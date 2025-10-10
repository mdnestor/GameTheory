
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sets

--import Mathlib.Tactic

import Mathlib.Order.Minimal
import Mathlib.Data.Set.Finite.Basic

namespace SocialChoice

variable {I X: Type}

class Pref {X: Type} (p: X → X → Prop): Prop where
  refl: ∀ x, p x x
  trans: ∀ x y z, p x y → p y z → p x z
  total: ∀ x y, p x y ∨ p y x

def Prefs (O: Type): Set (O → O → Prop) :=
  {R | Pref R}

instance: CoeFun (Prefs X) (fun _ => X → X → Prop) where
  coe p := p.val

def pareto (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ π x y, (∀ i, π i x y) → F π x y

def coalition_decisive_over (F: (I → Prefs X) → Prefs X) (C: Set I) (x y: X): Prop :=
  ∀ π, (∀ i ∈ C, π i x y) → F π x y

def coalition_decisive_over_refl (F: (I → Prefs X) → Prefs X) (C: Set I) (x: X): coalition_decisive_over F C x x := by
  intro π h
  exact (F π).property.refl x

def coalition_decisive (F: (I → Prefs X) → Prefs X) (C: Set I): Prop :=
  ∀ x y, coalition_decisive_over F C x y

def coalition_weak_decisive_over (F: (I → Prefs X) → Prefs X) (C: Set I) (x y: X): Prop :=
  ∀ π, (∀ i ∈ C, π i x y) ∧ (∀ i ∉ C, π i y x) → F π x y

def coalition_decisive_over_weak_decisive_over {F: (I → Prefs X) → Prefs X} {C: Set I} {x y: X} (h: coalition_decisive_over F C x y): coalition_weak_decisive_over F C x y := by
  intro π h1
  exact h π h1.left

theorem univ_coalition_decisive {F: (I → Prefs X) → Prefs X} (h: pareto F): coalition_decisive F Set.univ := by
  intro x y π h1
  exact h π x y fun i => h1 i trivial

def decisive (F: (I → Prefs X) → Prefs X) (i: I) (o1 o2: X): Prop :=
  ∀ π, π i o1 o2 → F π o1 o2

def dictator (F: (I → Prefs X) → Prefs X) (i: I): Prop :=
  ∀ o1 o2, decisive F i o1 o2

def dictatorship (F: (I → Prefs X) → Prefs X): Prop :=
  ∃ i, dictator F i

def iia (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ π1 π2 x y, (∀ i, π1 i x y ↔ π2 i x y) → (F π1 x y ↔ F π2 x y)

-- Given a profile π, and distinct x, y, z, can always find a modified profile π' such that
-- πi x z ↔ πi' x z
-- ∀ i ∈ A, πi x y
-- ∀ i ∈ Aᶜ, πi y x
-- ∀ i ∈ B, πi y z
-- ∀ i ∈ Bᶜ, πi z y
theorem exists_modified_vote (π: I → Prefs X) {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) (A: Set I) (B: Set I):
  ∃ π': I → Prefs X, (∀ i, π i x z ↔ π' i x z) ∧ (∀ i ∈ A, π' i x y) ∧ (∀ i ∉ A, π' i y x) ∧ (∀ i ∈ B, π' i y z) ∧ (∀ i ∉ B, π' i z y) := by
  sorry

theorem decisive_spread_forward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C x z := by
  intro π h1
  obtain ⟨π', h2, h3, h4⟩ := exists_modified_vote π hxy hxz hyz C Set.univ
  simp_all [hF2 π π' x z h2]
  apply (F π').property.trans _ y
  · apply h
    constructor
    · intro i hi
      exact h3 i hi
    · intro i hi
      exact h4.left i hi
  · apply hF π'
    intro i
    by_cases hi: i ∈ C
    · exact h4.right i
    · exact h4.right i

theorem decisive_spread_backward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C z y := by
  intro π h1
  have hzx: z ≠ x := by exact id (Ne.symm hxz)
  have hzy: z ≠ y := by exact id (Ne.symm hyz)
  obtain ⟨π', h2, h3, h4⟩ := exists_modified_vote π hzx hzy hxy Set.univ C
  simp_all [hF2 π π' z y h2]
  apply (F π').property.trans _ x
  · apply hF π'
    intro i
    by_cases hi: i ∈ C
    · exact (h3 i)
    · exact (h3 i)
  · apply h
    constructor
    · intro i hi
      exact h4.left i hi
    · intro i hi
      exact (h4.right i hi)

theorem decisive_spread_symmetric (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C y x := by
  obtain ⟨z, hxz, hyz⟩ := h0 x y
  have: coalition_decisive_over F C x z := by exact decisive_spread_forward hxy hxz hyz hF hF2 h
  have: coalition_weak_decisive_over F C x z := by exact coalition_decisive_over_weak_decisive_over this
  have: coalition_decisive_over F C y z := by exact decisive_spread_backward hxz hxy (id (Ne.symm hyz)) hF hF2 this
  have: coalition_weak_decisive_over F C y z := by exact coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_forward hyz (id (Ne.symm hxy)) (id (Ne.symm hxz)) hF hF2 this

theorem decisive_spread_strengthen (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C x y := by
  have: coalition_decisive_over F C y x := by exact decisive_spread_symmetric h0 hxy hF hF2 h
  have: coalition_weak_decisive_over F C y x := by exact coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_symmetric h0 (id (Ne.symm hxy)) hF hF2 this

theorem decisive_spread (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive F C := by
  intro s t
  by_cases h1: s = t
  subst h1
  exact coalition_decisive_over_refl F C s
  by_cases h2: x = s <;> by_cases h3: x = t <;> by_cases h4: y = s <;> by_cases h5: y = t <;> simp_all
  exact decisive_spread_strengthen h0 h1 hF hF2 h
  exact decisive_spread_forward hxy h1 h5 hF hF2 h
  subst h3 h4
  exact decisive_spread_symmetric h0 hxy hF hF2 h
  subst h3
  have := by exact decisive_spread_symmetric h0 hxy hF hF2 h
  have := by exact coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_backward h5 h4 h2 hF hF2 this
  subst h4
  have := by exact decisive_spread_symmetric h0 h2 hF hF2 h
  have := by exact coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_forward (fun a => h2 (id (Eq.symm a))) h1 h3 hF hF2 this
  exact decisive_spread_backward h3 h2 h4 hF hF2 h
  have := by exact decisive_spread_forward hxy h3 h5 hF hF2 h
  have := by exact coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_backward h3 h2 (fun a => h1 (id (Eq.symm a))) hF hF2 this

def exists_nonempty_coalition_of_size [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (F: (I → Prefs X) → Prefs X) (n: Nat): Prop :=
  ∃ C, C.Nonempty ∧ coalition_decisive F C ∧ Fintype.card C = n

theorem pareto_univ_decisive {F: (I → Prefs X) → Prefs X} (h: pareto F): coalition_decisive F Set.univ := by
  simp [coalition_decisive, coalition_decisive_over]
  exact fun o1 o2 p => h p o1 o2

theorem exists_minimal_decisive_coalition [Nonempty I] [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] {F: (I → Prefs X) → Prefs X} (h: pareto F): ∃ n, Minimal (exists_nonempty_coalition_of_size F) n := by
   apply exists_minimal_of_wellFoundedLT
   exists Fintype.card I
   exists Set.univ
   repeat' (apply And.intro)
   exact Set.nonempty_iff_univ_nonempty.mp (by assumption)
   exact pareto_univ_decisive h
   exact Fintype.card_setUniv

theorem decisive_coalition_contraction [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) {F: (I → Prefs X) → Prefs X} {C: Set I} (h1: coalition_decisive F C) (h2: 2 ≤ Fintype.card C) (hF2: pareto F) (hF3: iia F): ∃ C', C'.Nonempty ∧ C' < C ∧ coalition_decisive F C' := by
  -- C has at least 2 elements, so there exists nonempty partition
  have: ∃ C1: Set I, Nonempty C1 ∧ C1 < C := sorry
  obtain ⟨C1, hC11, hC12⟩ := this
  let C2 := C \ C1
  have hC2: Nonempty C2 := sorry -- obvious
  have: ∃ x y z: X, x ≠ y ∧ x ≠ z ∧ y ≠ z := sorry
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := this
  have: ∃ π: I → Prefs X, (∀ i ∈ C1, π i x y ∧ π i y z) ∧ (∀ i ∈ C2, π i z x ∧ π i x y) ∧ (∀ i ∉ C, π i y z ∧ π i z x) := sorry
  obtain ⟨π, h3, h4, h5⟩ := this
  have := (F π).property.total x z
  match this with
  | Or.inl h6 => {
    exists C1
    constructor
    exact Set.nonempty_coe_sort.mp hC11
    constructor
    simp_all only [Fintype.card_ofFinset, nonempty_subtype, Set.lt_eq_ssubset, ne_eq, true_or, C2]
    apply decisive_spread h0 hxz hF2 hF3
    intro π' ⟨h7, h8⟩
    have: ∃ π'': I → Prefs X, (∀ i, π' i x z ↔ π'' i x z) ∧ (∀ i ∈ C, π'' i x y) ∧ (∀ i, π'' i y z) := by sorry
    obtain ⟨π'', h9, h10, h11⟩ := exists_modified_vote π' hxy hxz hyz C Set.univ
    simp [hF3 π' π'' x z h9]
    apply h1
    intro i hi
    apply (π'' i).property.trans x y z
    exact h10 i hi
    exact h11.2.1 i (by trivial)
  }
  | Or.inr h6 => {
    exists C2
    constructor
    exact Set.nonempty_of_ssubset hC12
    constructor

    simp_all [C2]
    have: C ∩ C1 = C1 := by
      simp_all [subset_of_ssubset]
    rw [this]
    exact hC11
    simp_all only [Fintype.card_ofFinset, nonempty_subtype, Set.lt_eq_ssubset, ne_eq, C2]
    apply decisive_spread h0 hxz hF2 hF3
    intro π' ⟨h7, h8⟩
    have: ∃ π'': I → Prefs X, (∀ i, π' i x z ↔ π'' i x z) ∧ (∀ i ∈ C, π'' i x y) ∧ (∀ i, π'' i y z) := by sorry
    obtain ⟨π'', h9, h10, h11⟩ := this
    rw [hF3 π' π'' x z h9]
    apply h1
    intro i hi
    exact (π'' i).property.trans x y z (h10 i hi) (h11 i)
  }

theorem decisive_coalition_minimal [Nonempty I] [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) {F: (I → Prefs X) → Prefs X} (hF2: pareto F) (hF3: iia F): Minimal (exists_nonempty_coalition_of_size F) 1 := by
  obtain ⟨n, hn⟩ := exists_minimal_decisive_coalition hF2
  obtain ⟨C, hC0, hC1, hC2⟩ := hn.1
  have n_neq_zero: n ≠ 0 := by
    subst hC2
    simp_all
    exact hC0
  have n_lt_two: n < 2 := by
    apply Classical.not_not.mp
    intro h
    simp at h
    rw [←hC2] at h
    obtain ⟨C', hC3, hC4, hC5⟩ := decisive_coalition_contraction h0 hC1 h hF2 hF3
    have: Fintype.card C' < n := by sorry
    -- from C' ⊂ C get a strict card inequality
    have hlt_C' : Fintype.card C' < Fintype.card C :=
      Set.card_lt_card hC4
    have hlt : Fintype.card C' < n := by
      simpa [hC2] using hlt_C'

    have ⟨hPn, hMin⟩ := hn
    -- so applying hMin gives a contradiction
    --have hcontra := hMin (Fintype.card C') hlt h_exists
    -- should be easy


    --exact hn.2 (Fintype.card C') hC4 this

    --have hC4 := Set.card_lt_card hC3
    sorry
  have: n = 1 := by
    apply Nat.le_antisymm
    exact Nat.le_of_lt_succ n_lt_two
    exact Nat.one_le_iff_ne_zero.mpr n_neq_zero
  rw [←this]
  exact hn

theorem exists_dictatorship [Nonempty I] [Fintype I] (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) [∀ C: Set I, ∀ i, Decidable (i ∈ C)] {F: (I → Prefs X) → Prefs X} (h1: pareto F) (h2: iia F) {C: Set I} (h3: 2 ≤ Fintype.card C) (h4: coalition_decisive F C): dictatorship F := by
  have := decisive_coalition_minimal h0 h1 h2
  obtain ⟨x, hx⟩ := this
  obtain ⟨C, hC0, hC1, hC2⟩ := x
  have: Nonempty C := by
    apply Fintype.card_pos_iff.mp
    simp_all [Fintype.card_ofFinset, Nat.lt_add_one]
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
theorem singleton_pareto_dictator [Subsingleton I] {F: (I → Prefs X) → Prefs X} (h: pareto F) (i: I): dictator F i := by
   intro x y π hi
   apply h
   intro j
   rw [←Subsingleton.allEq i j]
   exact hi

theorem singleton_pareto_dictatorship [Subsingleton I] [Nonempty I] {F: (I → Prefs X) → Prefs X} (h: pareto F): dictatorship F := by
   exists Classical.ofNonempty
   apply singleton_pareto_dictator h

theorem arrow (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) [Fintype I] [Nonempty I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (F: (I → Prefs X) → Prefs X) (h1: pareto F) (h2: iia F): dictatorship F := by
  by_cases h: Fintype.card I ≤ 1
  have := Fintype.card_le_one_iff_subsingleton.mp h
  exact singleton_pareto_dictatorship h1
  simp [not_le] at h
  have: 2 ≤ Fintype.card I := by exact h
  apply exists_dictatorship (C := Set.univ) h0 h1 h2
  rw [Fintype.card_setUniv]
  exact h
  exact univ_coalition_decisive h1
