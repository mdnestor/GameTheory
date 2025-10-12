
import GameTheory.GameTheory
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Topology.UnitInterval

/-

The public goods game can be characterized as:
- Every player picks a strategy from a lattice.
- Their preferences are monotone in their own strategy and antimonotone in others.
- The Nash equilibium is everyone's top.

-/

variable {I X Y: Type}

noncomputable def PublicGoodGame (I: Type) [Fintype I] (r: ℝ): UtilityGame I unitInterval Real := {
  play := fun π i => 1 - π i + r * (∑ j, (π j).val)
  prefer := fun x y => x ≤ y
}

example [Fintype I] [DecidableEq I] {r: ℝ} (hr: 0 ≤ r) (s1 s2: unitInterval) (hs: s1 ≤ s2): ∀ i π, (PublicGoodGame I r).toOutcomeGame.toGame.prefer i (update π i s2) (update π i s1) := by
  simp [PublicGoodGame]
  intro i π
  have: ∀ j, (if j = i then s1.val else π j) ≤ (if j = i then s2.val else π j) := by
    intro j
    by_cases hji: j = i <;> simp [hji]
    exact hs
  have: ∑ j, (if j = i then s1.val else π j) ≤ ∑ j,  (if j = i then s2.val else π j) := by
    exact Finset.sum_le_sum fun i a => this i
  have: (r * ∑ j, if j = i then s1.val else π j) ≤ (r * ∑ j, if j = i then s2.val else π j) := by
    exact mul_le_mul_of_nonneg_left this hr
  -- calc
  --    1 - s2 + (r * ∑ x, ↑(if x = i then s2 else π x))
  --      ≤ 1 - s1 + (r * ∑ x, ↑(if x = i then s2 else π x)) := by aesop?
  --    _ = 1 - s1 + (r * ∑ x, ↑(if x = i then s1 else π x)) := by exact?
  sorry
