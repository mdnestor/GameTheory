
import GameTheory
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sets
import Mathlib.Order.Minimal
import Mathlib.Tactic
set_option maxHeartbeats 1000000
-- A "social ordering" is any function that takes an indexed collections of orderings and produces a joint ordering.

namespace SocialChoice

-- class Rel {O: Type} (R: O → O → Prop): Prop where

def Vote (A: Type) {O: Type} (P: Set (Endorelation O)): Type :=
  (A → P) → P

variable {A O: Type} {P: Set (Endorelation O)}

variable {X I: Type}

-- Clearly the Pareto ordering is one such example.

def IsPareto (F: (I → Endorelation X) → Endorelation X): Prop :=
  ∀ π x y, (∀ i, π i x y) → F π x y

--def IsStrictPareto (c: SocialOrdering A O): Prop :=
 -- ∀ p, ∀ o1 o2, (∀ a, strict (p a) o1 o2) → strict (c p) o1 o2



-- An agent is called decisive over outcomes o1, o2 if whenever he prefers o1 ≤ o2, so does the social ordering.

def decisive (c: Rel.vote A O) (a: A) (o1 o2: O): Prop :=
  ∀ p, (p a).rel o1 o2 → (c p).rel o1 o2

-- A social ordering is called liberal if every individual is decisive over some outcomes.

def liberal (c: Rel.vote A O): Prop :=
  ∀ a, ∃ o1 o2, decisive c a o1 o2

-- An agent is called a 'dictator' if he is decisive over every pair of outcomes.

-- def dictator (c: SocialOrdering A O) (a: A): Prop :=
--   ∀ o1 o2, decisive c a o1 o2

-- def dictatorship (c: SocialOrdering A O): Prop :=
--   ∃ a, dictator c a

-- -- If there is a dictator and at least 2 outcomes, then he is unique.

-- theorem dictator_unique [DecidableEq A] (c: SocialOrdering A O) (a a': A) (h1: dictator c a) (h2: dictator c a') (h3: ∃ o1 o2: O, o1 ≠ o2): a = a' := by
--   sorry

-- -- Independent of irrelevant alternatives: if everyone orders o1, o2 the same then so does the social ordering.

variable {A O: Type} {P: Set (Endorelation O)}

def iia (F: PreferenceProfile I X → Endorelation X): Prop :=
  ∀ π1 π2 x y, (∀ i, π1 i x y ↔ π2 i x y) → (F π1 x y ↔ F π2 x y)

-- Arrow's impossibility theorem: a social ordering function cannot be simultaneously Pareto, dictator-free, and iia.


def coalition_decisive_over (F: PreferenceProfile I X → Endorelation X) (π: PreferenceProfile I X) (C: Set I) (x y: X): Prop :=
  (∀ i ∈ C, π i x y) → F π x y

def coalition_decisive (F: PreferenceProfile I X → Endorelation X) (π: PreferenceProfile I X) (C: Set I): Prop :=
  ∀ x y, coalition_decisive_over F π C x y

def coalition_weak_decisive_over (F: PreferenceProfile I X → Endorelation X) (π: PreferenceProfile I X) (C: Set I) (x y: X): Prop :=
  (∀ i ∈ C, π i x y) ∧ (∀ i ∉ C, π i y x) → F π x y

theorem coalition_weak_decisive_over_decisive_over {F: PreferenceProfile I X → Endorelation X} {π: PreferenceProfile I X} {C: Set I} {x y: X} (h: coalition_decisive_over F π C x y): coalition_weak_decisive_over F π C x y := by
  intro h1
  exact h h1.1

class Pref {O: Type} (R: O → O → Prop): Prop  where
  total: ∀ x y, R x y ∨ R y x
  trans: ∀ x y z, R x y → R y z → R x z

class StrictPref {O: Type} (R: O → O → Prop) extends Pref R where
  strict: ∀ x, ¬ R x x

variable [DecidableEq O] [∀ G: Set A, ∀ a, Decidable (a ∈ G)]

def Prefs (O: Type): Set (Endorelation O) :=
  {R | Pref R}

def transitive_closure (R: Endorelation O): Endorelation O :=
  fun o1 o2 => R o1 o2 ∨ ∃ o, R o1 o ∧ R o o2

open Relation

def TotalClosure (r : α → α → Prop) : α → α → Prop :=
  TransGen (fun x y => r x y ∨ ¬ r y x ∨ x = y)

lemma total_totalClosure (r : α → α → Prop) :
    Total (TotalClosure r) := by
  intro x y
  unfold TotalClosure
  by_cases h : r x y
  · left; exact TransGen.single (Or.inl h)
  · right; exact TransGen.single (Or.inr (Or.inl h))
lemma subset_totalClosure (r : α → α → Prop) :
    ∀ x y, r x y → TotalClosure r x y := by
  intro x y h
  unfold TotalClosure
  apply TransGen.single
  exact Or.inl h


theorem exists_condorcet_relation {π: PreferenceProfile I X} (h1: ∀ i, Pref (π i)) (C: Set I) {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z): ∃ π': PreferenceProfile I X, (∀ i, Pref (π' i)) ∧ (∀ i, π i x z ↔ π' i x z) ∧ (∀ i ∈ C, π' i x y ∧ π' i y z) ∧ (∀ i ∉ C, π' i y x ∧ π' i y z):= by
  sorry

theorem decisive_spread_forward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: PreferenceProfile I X → Endorelation X} (h2: ∀ π, (∀ i, Pref (π i)) → Pref (F π)) (h3: IsPareto F) (h4: iia F) {π: PreferenceProfile I X} (h5: ∀ i, Pref (π i)) {C: Set I} (h6: coalition_weak_decisive_over F π C x y): coalition_decisive_over F π C x z := by
  intro h7
  obtain ⟨π', h10, h11, h12, h13⟩ := exists_condorcet_relation h5 C hxy hxz hyz
  have: F π x y := by
    sorry
  have: F π' x y := by
    sorry
  have: F π' y z := by
    sorry
  have: F π' x z := by
    apply (h2 π' h10).trans
    repeat assumption
  rw [h4 π π' x z h11]
  exact this

theorem decisive_spread_backward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: PreferenceProfile I X → Endorelation X} (h2: ∀ π, (∀ i, Pref (π i)) → Pref (F π)) (h3: IsPareto F) (h4: iia F) {π: PreferenceProfile I X} (h5: ∀ i, Pref (π i)) {C: Set I} (h6: coalition_weak_decisive_over F π C x y): coalition_decisive_over F π C z y := by
  sorry

theorem decisive_symmetry {x y: X} (hxy: x ≠ y) (hz: ∃ z, x ≠ z ∧ y ≠ z) {F: PreferenceProfile I X → Endorelation X} (h2: ∀ π, (∀ i, Pref (π i)) → Pref (F π)) (h3: IsPareto F) (h4: iia F) {π: PreferenceProfile I X} (h5: ∀ i, Pref (π i)) {C: Set I} (h6: coalition_weak_decisive_over F π C x y): coalition_decisive_over F π C y x := by
  sorry


theorem decisive_coalition_contraction [Fintype A] [DecidableEq O] [∀ C: Set A, ∀ a, Decidable (a ∈ C)]
  {c: (A → StrictPrefs O) → StrictPrefs O} {C: Set A} (h1: coalition_decisive2 c C) (h2: 2 ≤ Fintype.card C) (h3: ∀ p, Total (c p).val) (hc4: ∀ p, Transitive (c p).val) (hc5: ∀ p: PreferenceProfile A O, ∀ a, Transitive (p a)): ∃ C' < C, coalition_decisive2 c C' := by
  have: ∃ C1 C2: Set A, Nonempty C1 ∧ Nonempty C2 ∧ Disjoint C1 C2 ∧ C1 ∪ C2 = C := by sorry
  obtain ⟨C1, C2, h3, h4, h5, h6⟩ := this
  let x: O := sorry
  let y: O := sorry
  let z: O := sorry
  have: x ≠ y := sorry
  have: x ≠ z := sorry
  have: y ≠ z := sorry
  have: Nonempty (A → StrictPrefs O) := by
    sorry

  let p: A → StrictPrefs O := Classical.ofNonempty

  let p': A → Endorelation O := fun a => fun o1 o2 =>
    if a ∈ C1 then
      (if (o1 = z ∧ o2 = y) ∨ (o1 = y ∧ o2 = x) then True else (p a).val o1 o2)
    else if a ∈ C2 then
      (if (o1 = y ∧ o2 = x) ∨  (o1 = x ∧ o2 = z) then True else (p a).val o1 o2)
    else
      (if (o1 = x ∧ o2 = z) ∨ (o1 = z ∧ o2 = y) then True else (p a).val o1 o2)
  have: ∀ a, StrictPref (p' a) := by
    intro a
    have:= (p a).prop.total
    have:= (p a).prop.trans
    constructor
    intro o
    aesop
    simp [Total]
    intro o1 o2
    --by_cases a ∈ C1 <;> by_cases a ∈ C2 <;> by_cases (o1 = z ∧ o2 = y) <;> by_cases (o1 = y ∧ o2 = x) <;> by_cases (o1 = x ∧ o2 = z)

    --by_cases o1 = x <;> by_cases o1 = y <;> by_cases o1 = z
    repeat simp_all [p, p']


    --aesop


  --have: ∀ a ∈ C, p a z x := by aesop
  have: ∀ a ∈ C, (p' a) y x := by
    intro a a_1
    subst h6
    simp_all only [nonempty_subtype, ne_eq, nonempty_fun, ite_self, implies_true, Fintype.card_ofFinset,
      Set.mem_union, x, y, z, p', p]

  have := h1 z x p
  by_cases h7: (c p).val z x
  have: coalition_weak_decisive_over2 c C1 z x := by
    intro p''
    intro ⟨h8, h9⟩

    have: ∀ a, (p'' a).val z x = p' a z x := by
      intro a
      simp_all
      by_cases h10: a ∈ C1
      aesop
      by_cases h10: a ∈ C2


  sorry

def exists_coalition_of_size [Fintype A] [∀ C: Set A, ∀ a, Decidable (a ∈ C)] (c: SocialOrdering A O) (n: Nat): Prop :=
  ∃ C, coalition_decisive c C ∧ Fintype.card C = n

theorem pareto_univ_decisive {c: SocialOrdering A O} (h: IsPareto c): coalition_decisive c Set.univ := by
  simp [coalition_decisive, coalition_decisive_over]
  exact fun o1 o2 p => h p o1 o2

theorem exists_minimal_decisive_coalition [Fintype A] [∀ C: Set A, ∀ a, Decidable (a ∈ C)] {c: SocialOrdering A O} (hc: IsPareto c): ∃ n, Minimal (exists_coalition_of_size c) n := by
   apply exists_minimal_of_wellFoundedLT
   exists Fintype.card A
   exists Set.univ
   constructor
   exact pareto_univ_decisive hc
   exact Fintype.card_setUniv

-- Cannot have an empty decisive coalition
theorem decisive_coalition_nonempty [Fintype A] [∀ C: Set A, ∀ a, Decidable (a ∈ C)] {c: SocialOrdering A O} (hc: IsPareto c) {C: Set A} (h1: coalition_decisive c C): C.Nonempty := by
  sorry

theorem decisive_coalition_minimal [Fintype A] [∀ C: Set A, ∀ a, Decidable (a ∈ C)] {c: SocialOrdering A O} (hc: IsPareto c): Minimal (exists_coalition_of_size c) 1 := by
  obtain ⟨n, hn⟩ := exists_minimal_decisive_coalition hc
  obtain ⟨C, hC1, hC2⟩ := hn.1
  have n_neq_zero: n ≠ 0 := by
    intro
    simp_all
    have := Set.subset_eq_empty hC2 rfl
    have := decisive_coalition_nonempty hc hC1
    simp_all
  have n_lt_two: n < 2 := by
    apply Classical.not_not.mp
    intro h
    simp at h
    rw [←hC2] at h
    obtain ⟨C', hC3, _⟩ := decisive_coalition_contraction hC1 h
    have hC4 := Set.card_lt_card hC3
    have := Minimal.le_of_le hn (by exists C')
    have := Nat.le_of_succ_le (Nat.lt_of_lt_of_eq hC4 hC2)
    simp_all [Nat.not_le_of_gt]
  have: n = 1 := by
    apply Nat.le_antisymm
    exact Nat.le_of_lt_succ n_lt_two
    exact Nat.one_le_iff_ne_zero.mpr n_neq_zero
  rw [←this]
  exact hn

theorem exists_dictatorship [Fintype A] [∀ C: Set A, ∀ a, Decidable (a ∈ C)] {c: SocialOrdering A O} (hc: IsPareto c) {C: Set A} (h1: coalition_decisive c C) (h2: 2 ≤ Fintype.card C): dictatorship c := by
  have := decisive_coalition_minimal hc
  obtain ⟨x, hx⟩ := this
  obtain ⟨C, hC1, hC2⟩ := x
  have: Nonempty C := by
    apply Fintype.card_pos_iff.mp
    exact Nat.lt_of_sub_eq_succ hC2
  have x: C := Classical.ofNonempty
  have: C = (Set.singleton x.val) := by sorry -- should follow quickly from `hC2 : Fintype.card ↑C = 1`
  rw [this] at hC1
  exists x
  intro o1 o2 p h
  apply hC1 o1 o2 p
  intro a ha
  rw [ha]
  exact h

-- also requires that |A| ≥ 3
theorem arrow {c: SocialOrdering A O} (h1: IsPareto c) (h2: ¬ dictatorship c) (h3: iia c): False :=
  sorry

-- A social choice function maps preference profiles to outcome sets.
-- It can still be interpreted as a social ordering, where o1 ≤ o2 in the social ordering whenever o1 ∈ S → o2 ∈ S where S is the chosen outcome set.

def SocialChoice (A O: Type): Type :=
  PreferenceProfile A O → Set O

def SocialChoice.toSocialOrdering {A O: Type} (c: SocialChoice A O): SocialOrdering A O :=
  fun p => fun o1 o2 => c p o1 → c p o2

-- If a social choice function is strictly Pareto, and everyone strictly prefers o1 < o2, then o1 ∉ S.

theorem social_choice_strict_pareto [Nonempty A] {c: SocialChoice A O} (h1: IsStrictPareto c.toSocialOrdering)
  (p: PreferenceProfile A O) (o1 o2: O) (h2: ∀ a, strict (p a) o1 o2): o1 ∉ c p := by
  intro
  have h3 := h1 p o1 o2
  simp_all [strict, SocialChoice.toSocialOrdering]
  have := h3.right.right
  contradiction
