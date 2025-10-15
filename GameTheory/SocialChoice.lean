/-

Arrow's impossibility theorem.

Based on the decisive coalitions argument.

TODO: re parameterize existence lemmas.

-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Minimal

set_option linter.unusedVariables false

variable {I X: Type}

def strict (R: X → X → Prop): X → X → Prop :=
  fun x y => R x y ∧ ¬ R y x

theorem strict_transitive {R: X → X → Prop} (h: Transitive R): Transitive (strict R) := by
  intro x y z ⟨lexy, nleyx⟩ ⟨leyz, nlezy⟩
  have lexz := h lexy leyz
  have nlezx: ¬ R z x := by
    intro lezx
    exact nleyx (h leyz lezx)
  exact ⟨lexz, nlezx⟩

class Pref {X: Type} (R: X → X → Prop): Prop where
  reflexive: Reflexive R
  transitive: Transitive R
  total: Total R

def Prefs (X: Type): Set (X → X → Prop) :=
  {R | Pref R}

instance: CoeFun (Prefs X) (fun _ => X → X → Prop) where
  coe p := p.val

def pareto (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ π x y, (∀ i, strict (π i) x y) → strict (F π) x y

def coalition_decisive_over (F: (I → Prefs X) → Prefs X) (C: Set I) (x y: X): Prop :=
  ∀ π, (∀ i ∈ C, strict (π i) x y) → strict (F π) x y

def coalition_decisive (F: (I → Prefs X) → Prefs X) (C: Set I): Prop :=
  ∀ x y, coalition_decisive_over F C x y

def coalition_weak_decisive_over (F: (I → Prefs X) → Prefs X) (C: Set I) (x y: X): Prop :=
  ∀ π, (∀ i ∈ C, strict (π i) x y) ∧ (∀ i ∉ C, strict (π i) y x) → strict (F π) x y

def coalition_decisive_over_weak_decisive_over {F: (I → Prefs X) → Prefs X} {C: Set I} {x y: X} (h: coalition_decisive_over F C x y): coalition_weak_decisive_over F C x y := by
  intro π h1
  exact h π h1.left

theorem univ_coalition_decisive {F: (I → Prefs X) → Prefs X} (h: pareto F): coalition_decisive F Set.univ := by
  intro x y π h1
  exact h π x y fun i => h1 i trivial

def decisive (F: (I → Prefs X) → Prefs X) (i: I) (x y: X): Prop :=
  ∀ π, strict (π i) x y → strict (F π) x y

def dictator (F: (I → Prefs X) → Prefs X) (i: I): Prop :=
  ∀ x y, decisive F i x y

def dictatorship (F: (I → Prefs X) → Prefs X): Prop :=
  ∃ i, dictator F i

def iia (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ π1 π2 x y, (∀ i, π1 i x y ↔ π2 i x y) → (F π1 x y ↔ F π2 x y)

theorem iia_strict {F: (I → Prefs X) → Prefs X} (hF: iia F) {π π': I → Prefs X} {x z : X}
  (hxz: ∀ i, π i x z ↔ π' i x z) (hzx: ∀ i, π i z x ↔ π' i z x):
  strict (F π) x z ↔ strict (F π') x z := by
  have Hxz: (F π) x z ↔ (F π') x z := hF π π' x z hxz
  have Hzx: (F π) z x ↔ (F π') z x := hF π π' z x hzx
  simp [strict, Hxz, Hzx]

def rank_pref (r: X → Nat): Pref (fun a b => r a ≤ r b) := {
  reflexive := fun x => Nat.le_refl (r x)
  transitive := fun _ _ _ => Nat.le_trans
  total := fun x y => Nat.le_total (r x) (r y)
}

theorem modify_pref (p: Prefs X) (x y z : X) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (h : strict p x z):
  ∃ p' : Prefs X, (p x z ↔ p' x z) ∧ (p z x ↔ p' z x) ∧ strict p' x y ∧ strict p' y z := by
  classical
  let r: X → Nat := fun a => if a = x then 0 else if a = y then 1 else if a = z then 2 else 0
  let pref := rank_pref r
  exists ⟨fun a b => r a ≤ r b, rank_pref r⟩
  simp_all [r, strict, Ne.symm hxy, Ne.symm hyz, Ne.symm hxz]

theorem modify_pref' (p: Prefs X) (x y z : X) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z):
  ∃ p' : Prefs X, (p x z ↔ p' x z) ∧ (p z x ↔ p' z x) ∧ strict p' y x ∧ strict p' y z := by
  classical
  let p': X → X → Prop := fun a b => if a = y then
    True
  else if b = y then
    False
  else
    p a b
  have: Pref p' := {
    reflexive := by
      intro a
      by_cases a = y <;> simp_all [p']
      apply p.prop.reflexive
    transitive := by
      intro a b c h1 h2
      by_cases a = y <;> by_cases b = y <;> by_cases c = y <;> simp_all [p']
      exact p.prop.transitive h1 h2
    total := by
      intro a b
      by_cases a = y <;> by_cases b = y <;> simp_all [p']
      exact p.prop.total a b
  }
  use ⟨p', this⟩
  simp_all [p', strict]
  repeat' (apply And.intro)
  intro
  exact Ne.symm hyz
  exact Or.inl (Ne.symm hyz)
  exact Ne.symm hyz

theorem modify_pref'' (p: Prefs X) (x y z : X) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z):
  ∃ p' : Prefs X, (p x z ↔ p' x z) ∧ (p z x ↔ p' z x) ∧ strict p' x y ∧ strict p' z y := by
  classical
  let p': X → X → Prop := fun a b => if b = y then
    True
  else if a = y then
    False
  else
    p a b
  have: Pref p' := {
    reflexive := by
      intro a
      by_cases a = y <;> simp_all [p']
      apply p.prop.reflexive
    transitive := by
      intro a b c h1 h2
      by_cases a = y <;> by_cases b = y <;> by_cases c = y <;> simp_all [p']
      exact p.prop.transitive h1 h2
    total := by
      intro a b
      by_cases a = y <;> by_cases b = y <;> simp_all [p']
      exact p.prop.total a b
  }
  use ⟨p', this⟩
  simp_all [p', strict]
  repeat' (apply And.intro)
  exact Or.inl (Ne.symm hyz)
  intro
  exact Ne.symm hyz
  exact Ne.symm hyz

theorem exists_modified_profile
  (π : I → Prefs X)
  {x y z : X}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
  {C : Set I}
  (h : ∀ i ∈ C, strict (π i) x z) :
  ∃ π' : I → Prefs X, ∀ i,
    ((π i) x z ↔ (π' i) x z) ∧
    ((π i) z x ↔ (π' i) z x) ∧
    (i ∈ C → strict (π' i) x y ∧ strict (π' i) y z) ∧
    (i ∉ C → strict (π' i) y x ∧ strict (π' i) y z) := by
  classical
  use fun i => if hi: i ∈ C then
    (modify_pref (π i) x y z hxy hxz hyz (h i hi)).choose
  else
    (modify_pref' (π i) x y z hxy hxz hyz).choose
  intro i
  by_cases hi: i ∈ C
  simp [hi]
  exact (modify_pref (π i) x y z hxy hxz hyz (h i hi)).choose_spec
  simp [hi]
  exact (modify_pref' (π i) x y z hxy hxz hyz).choose_spec

theorem exists_modified_profile'
  (π : I → Prefs X)
  {x y z : X}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
  {C : Set I}
  (h : ∀ i ∈ C, strict (π i) x z) :
  ∃ π' : I → Prefs X, ∀ i,
    ((π i) x z ↔ (π' i) x z) ∧
    ((π i) z x ↔ (π' i) z x) ∧
    (i ∈ C → strict (π' i) x y ∧ strict (π' i) y z) ∧
    (i ∉ C → strict (π' i) x y ∧ strict (π' i) z y) := by
  classical
  use fun i => if hi: i ∈ C then
    (modify_pref (π i) x y z hxy hxz hyz (h i hi)).choose
  else
    (modify_pref'' (π i) x y z hxy hxz hyz).choose
  intro i
  by_cases hi: i ∈ C
  simp [hi]
  exact (modify_pref (π i) x y z hxy hxz hyz (h i hi)).choose_spec
  simp [hi]
  exact (modify_pref'' (π i) x y z hxy hxz hyz).choose_spec

theorem decisive_spread_forward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C x z := by
  intro π h1
  obtain ⟨π', hπ'⟩ := exists_modified_profile π hxy hxz hyz h1
  let h2 := fun i => (hπ' i).1
  let h3 := fun i => (hπ' i).2.1
  let h4 := fun i => (hπ' i).2.2.1
  let h5 := fun i => (hπ' i).2.2.2
  rw [iia_strict hF2 h2 h3]
  apply strict_transitive (F π').prop.transitive
  · apply h
    constructor
    · intro i hi
      exact (h4 i hi).left
    · intro i hi
      exact (h5 i hi).left
  · apply hF π'
    intro i
    by_cases hi: i ∈ C
    · exact (h4 i hi).right
    · exact (h5 i hi).right

theorem decisive_spread_backward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C z y := by
  intro π h1
  have hzx: z ≠ x := Ne.symm hxz
  have hzy: z ≠ y := Ne.symm hyz
  obtain ⟨π', hπ'⟩ := exists_modified_profile' π hzx hzy hxy h1
  let h2 := fun i => (hπ' i).1
  let h3 := fun i => (hπ' i).2.1
  let h4 := fun i => (hπ' i).2.2.1
  let h5 := fun i => (hπ' i).2.2.2
  rw [iia_strict hF2 h2 h3]
  apply strict_transitive (F π').prop.transitive
  · apply hF π'
    intro i
    by_cases hi: i ∈ C
    · exact (h4 i hi).left
    · exact (h5 i hi).left
  · apply h
    constructor
    · intro i hi
      exact (h4 i hi).right
    · intro i hi
      exact (h5 i hi).right

theorem decisive_spread_symmetric (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C y x := by
  obtain ⟨z, hxz, hyz⟩ := h0 x y
  have := decisive_spread_forward hxy hxz hyz hF hF2 h
  have := coalition_decisive_over_weak_decisive_over this
  have := decisive_spread_backward hxz hxy (Ne.symm hyz) hF hF2 this
  have := coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_forward hyz (Ne.symm hxy) (Ne.symm hxz) hF hF2 this

theorem decisive_spread_strengthen (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C x y := by
  have := decisive_spread_symmetric h0 hxy hF hF2 h
  have := coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_symmetric h0 (Ne.symm hxy) hF hF2 this

theorem coalition_decisive_over_refl (F: (I → Prefs X) → Prefs X) {C: Set I} (hC: Nonempty C) (x: X): coalition_decisive_over F C x x := by
  simp [coalition_decisive_over]
  intro π
  have i: C := Classical.ofNonempty
  intro h
  have := h i i.prop
  simp_all [strict]

theorem decisive_spread (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (hC: Nonempty C) (h: coalition_weak_decisive_over F C x y): coalition_decisive F C := by
  intro s t
  by_cases h1: s = t
  subst h1
  exact coalition_decisive_over_refl F hC s
  by_cases h2: x = s <;> by_cases h3: x = t <;> by_cases h4: y = s <;> by_cases h5: y = t <;> simp_all
  exact decisive_spread_strengthen h0 h1 hF hF2 h
  exact decisive_spread_forward hxy h1 h5 hF hF2 h
  subst h3 h4
  exact decisive_spread_symmetric h0 hxy hF hF2 h
  subst h3
  have := decisive_spread_symmetric h0 hxy hF hF2 h
  have := coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_backward h5 h4 h2 hF hF2 this
  subst h4
  have := decisive_spread_symmetric h0 h2 hF hF2 h
  have := coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_forward (fun a => h2 (Eq.symm a)) h1 h3 hF hF2 this
  exact decisive_spread_backward h3 h2 h4 hF hF2 h
  have := decisive_spread_forward hxy h3 h5 hF hF2 h
  have := coalition_decisive_over_weak_decisive_over this
  exact decisive_spread_backward h3 h2 (fun a => h1 (Eq.symm a)) hF hF2 this

def exists_nonempty_decisive_coalition_of_size [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (F: (I → Prefs X) → Prefs X) (n: Nat): Prop :=
  ∃ C, C.Nonempty ∧ coalition_decisive F C ∧ Fintype.card C = n

theorem pareto_univ_decisive {F: (I → Prefs X) → Prefs X} (h: pareto F): coalition_decisive F Set.univ := by
  simp [coalition_decisive, coalition_decisive_over]
  exact fun x y p => h p x y

theorem exists_minimal_decisive_coalition [Nonempty I] [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] {F: (I → Prefs X) → Prefs X} (h: pareto F): ∃ n, Minimal (exists_nonempty_decisive_coalition_of_size F) n := by
  classical
  apply exists_minimal_of_wellFoundedLT
  exists Fintype.card I
  exists Set.univ
  repeat' (apply And.intro)
  exact Set.nonempty_iff_univ_nonempty.mp (by assumption)
  exact pareto_univ_decisive h
  exact Fintype.card_setUniv

theorem decisive_coalition_contraction_lemma {I X : Type}
  [Fintype I] [Fintype X] --[(C : Set I) → (i : I) → Decidable (i ∈ C)]
  (h0 : ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z)
  {F : (I → ↑(Prefs X)) → ↑(Prefs X)}
  {C : Set I}
  (hF2 : pareto F)
  (hF3 : iia F)
  --{i : ↑C}
  {C1 : Set I}--:= {↑i})
  (hC11 : Nonempty ↑C1)
  (hC12 : C1 < C)
  {x y z : X}
  (hxz : x ≠ z)
  {π₀ : I → ↑(Prefs X)}
  (h3 : ∀ i ∈ C1, strict (π₀ i) x y ∧ strict (π₀ i) y z)
  (h4 : ∀ i ∈ C \ C1, strict (π₀ i) z x ∧ strict (π₀ i) x y)
  (h5 : ∀ i ∉ C, strict (π₀ i) y z ∧ strict (π₀ i) z x)
  (h6: strict (F π₀) x z):
  ∃ C', C'.Nonempty ∧ C' < C ∧ coalition_decisive F C' := by
  classical
  exists C1
  constructor
  exact Set.nonempty_coe_sort.mp hC11
  constructor
  simp_all [nonempty_subtype, Set.lt_eq_ssubset, ne_eq]
  apply decisive_spread h0 hxz hF2 hF3
  assumption
  intro π ⟨h7, h8⟩
  have h9: ∀ i ∈ C1, strict (π₀ i) x z ∧ strict (π i) x z := by
    intro i hi
    have := h7 i hi
    simp [h7 i hi, strict_transitive (π₀ i).prop.transitive (h3 i hi).left (h3 i hi).right]
  have h9': ∀ i ∈ C1, π₀ i x z ∧ π i x z := by
    intro i hi
    have := h9 i hi
    exact ⟨this.1.1, this.2.1⟩
  have h9'': ∀ i ∈ C1, ¬ π₀ i z x ∧ ¬ π i z x := by
    intro i hi
    have := h9 i hi
    exact ⟨this.1.2, this.2.2⟩
  have h10: ∀ i ∉ C1, strict (π₀ i) z x ∧ strict (π i) z x := by
    intro i hi
    by_cases hi1: i ∈ C
    constructor
    have: i ∈ C \ C1 := by
      exact Set.mem_diff_of_mem hi1 hi
    exact (h4 i this).left
    exact h8 i hi
    constructor
    exact (h5 i hi1).right
    simp_all
  have h10': ∀ i ∉ C1, π₀ i z x ∧ π i z x := by
    intro i hi
    have := h10 i hi
    exact ⟨this.1.1, this.2.1⟩
  have h10': ∀ i ∉ C1, ¬ π₀ i x z ∧ ¬ π i x z := by
    intro i hi
    have := h10 i hi
    exact ⟨this.1.2, this.2.2⟩
  have h11: ∀ i, π₀ i x z ↔ π i x z := by
    intro i; by_cases i ∈ C1
    repeat simp_all
  have h11': ∀ i, π₀ i z x ↔ π i z x := by
    intro i; by_cases i ∈ C1
    repeat simp_all
  have := iia_strict hF3 h11 h11'
  rw [←this]
  exact h6

theorem decisive_coalition_contraction [Fintype I] [Fintype X] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) {F: (I → Prefs X) → Prefs X} {C: Set I} (h1: coalition_decisive F C) (h2: 2 ≤ Fintype.card C) (hF2: pareto F) (hF3: iia F) (hX: Fintype.card X ≥ 3): ∃ C', C'.Nonempty ∧ C' < C ∧ coalition_decisive F C' := by
  -- C has at least 2 elements, so there exists nonempty partition
  classical
  have: 1 < Fintype.card C := by exact h2
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card this
  let C1: Set I := {i.val}
  have: j.val ∈ C := j.prop
  have: j.val ∉ C1 := by
    simp_all only [ne_eq, Fintype.card_ofFinset, ge_iff_le, Subtype.coe_prop, Set.mem_singleton_iff, C1]
    obtain ⟨val, property⟩ := i
    obtain ⟨val_1, property_1⟩ := j
    simp_all only [Subtype.mk.injEq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [not_true_eq_false]
  have C1_lt_C: C1 < C := by
    apply Set.ssubset_iff_subset_ne.mpr
    constructor
    simp_all only [ne_eq, Fintype.card_ofFinset, ge_iff_le, Subtype.coe_prop, Set.mem_singleton_iff,
      Set.singleton_subset_iff, C1]
    (expose_names; exact Ne.symm (ne_of_mem_of_not_mem' this_2 this))
  have: Nonempty C1 := by exact instNonemptyOfInhabited
  have: C1 < C := C1_lt_C
  have hC11: Nonempty C1 := by (expose_names; exact this_4)
  have hC12: C1 < C := by exact C1_lt_C
  let C2 := C \ C1
  have hC2: C2.Nonempty := by
    rename_i inst inst_1 inst_2 this_1 this_2 this_3 this_4
    simp_all [C1, C2]
    obtain ⟨val, property⟩ := i
    obtain ⟨val_1, property_1⟩ := j
    simp_all only [Subtype.mk.injEq]
    apply Exists.intro
    apply And.intro
    apply property_1
    simp_all only [Set.mem_singleton_iff, not_false_eq_true]
  have: Fintype.card X > 2 := by exact hX
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp this
  have: ∃ π₀: I → Prefs X, (∀ i ∈ C1, strict (π₀ i) x y ∧ strict (π₀ i) y z) ∧ (∀ i ∈ C2, strict (π₀ i) z x ∧ strict (π₀ i) x y) ∧ (∀ i ∉ C, strict (π₀ i) y z ∧ strict (π₀ i) z x) := by
    sorry
  obtain ⟨π₀, h3, h4, h5⟩ := this
  have := (F π₀).property.total x z
  have C1_sub_C: C1 ⊆ C := by exact subset_of_ssubset C1_lt_C
  have C2_sub_C : C2 ⊆ C := by
    rw [Set.diff_subset_iff]
    exact Set.subset_union_right
  have: strict (F π₀) x y := by
    apply h1
    intro i
    by_cases i ∈ C1
    aesop
    aesop

  by_cases h6: strict (F π₀) x z
  exact decisive_coalition_contraction_lemma h0 hF2 hF3 hC11 hC12 hxz h3 h4 h5 h6
  --simp [strict] at h6

  have: strict (F π₀) z y := by
    classical
    rcases this with ⟨hxy, n_yx⟩
    -- get (F π₀) z x from ¬ strict x z and totality
    have hzx : (F π₀) z x := by
      rcases (F π₀).property.total x z with hxz | hzx
      · have : ¬¬ (F π₀) z x := by
          intro hn; exact h6 ⟨hxz, hn⟩
        exact not_not.mp this
      · exact hzx
    -- build z ≽ y and rule out y ≽ z
    have pzy : (F π₀) z y := (F π₀).property.transitive hzx hxy
    have n_yz : ¬ (F π₀) y z := by
      intro hyz
      have hyx : (F π₀) y x := (F π₀).property.transitive hyz hzx
      exact n_yx hyx
    exact ⟨pzy, n_yz⟩

  exists C2
  constructor
  exact hC2
  constructor
  simp_all only [ne_eq, Fintype.card_ofFinset, ge_iff_le, Subtype.coe_prop, Set.mem_singleton_iff, Set.lt_eq_ssubset,
    nonempty_subtype, exists_eq, gt_iff_lt, forall_eq, Set.mem_diff, and_imp, Set.singleton_subset_iff,
    Set.diff_singleton_subset_iff, Set.insert_eq_of_mem, subset_refl, Set.diff_ssubset_left_iff,
    Set.inter_singleton_nonempty, C1, C2]

  simp_all [nonempty_subtype, Set.lt_eq_ssubset, ne_eq]
  have hzy: z ≠ y := by exact fun a => hyz (id (Eq.symm a))
  apply decisive_spread h0 hzy hF2 hF3
  simp_all only [Set.mem_singleton_iff, exists_eq, forall_eq, Set.mem_diff, and_imp, Set.singleton_subset_iff,
    Subtype.coe_prop, Set.diff_singleton_subset_iff, Set.insert_eq_of_mem, subset_refl, ne_eq, nonempty_subtype, C1,
    C2]
  obtain ⟨val, property⟩ := i
  obtain ⟨val_1, property_1⟩ := j
  obtain ⟨left, right⟩ := h3
  simp_all only [Subtype.mk.injEq]
  exact hC2

  intro π ⟨h7, h8⟩
  have h9: ∀ i ∈ C2, strict (π₀ i) z y ∧ strict (π i) z y := by
    intro i hi
    have := h7 i hi
    simp [h7 i hi]
    apply strict_transitive (π₀ i).prop.transitive
    exact (h4 i hi).left
    exact (h4 i hi).right

  have h9': ∀ i ∈ C2, π₀ i z y ∧ π i z y := by
    intro i hi
    have := h9 i hi
    exact ⟨this.1.1, this.2.1⟩
  have h9'': ∀ i ∈ C2, ¬ π₀ i y z ∧ ¬ π i y z := by
    intro i hi
    have := h9 i hi
    exact ⟨this.1.2, this.2.2⟩
  have h10: ∀ i ∉ C2, strict (π₀ i) y z ∧ strict (π i) y z := by
    intro i hi
    by_cases hi1: i ∈ C
    constructor
    have: i ∈ C \ C2 := by
      exact Set.mem_diff_of_mem hi1 hi
    have: i ∈ C1 := by simp_all only [Set.mem_singleton_iff, exists_eq, forall_eq, Set.mem_diff, and_imp,
      Set.singleton_subset_iff, Subtype.coe_prop, Set.diff_singleton_subset_iff, Set.insert_eq_of_mem, subset_refl,
      ne_eq, not_false_eq_true, and_self, implies_true, not_and, Decidable.not_not, true_and, sdiff_sdiff_right_self,
      Set.le_eq_subset, inf_of_le_right, C1, C2]
    exact (h3 i this).right
    exact h8 i hi
    constructor

    exact (h5 i hi1).left

    simp_all
  have h10': ∀ i ∉ C2, π₀ i y z ∧ π i y z := by
    intro i hi
    have := h10 i hi
    exact ⟨this.1.1, this.2.1⟩
  have h10': ∀ i ∉ C2, ¬ π₀ i z y ∧ ¬ π i z y := by
    intro i hi
    have := h10 i hi
    exact ⟨this.1.2, this.2.2⟩
  have h11: ∀ i, π₀ i y z ↔ π i y z := by
    intro i; by_cases i ∈ C2
    repeat simp_all
  have h11': ∀ i, π₀ i z y ↔ π i z y := by
    intro i; by_cases i ∈ C2
    repeat simp_all
  have := iia_strict hF3 h11' h11
  rw [←this]
  (expose_names; exact this_6)

theorem decisive_coalition_minimal [Nonempty I] [Fintype X] [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) {F: (I → Prefs X) → Prefs X} (hF2: pareto F) (hF3: iia F) (hX: Fintype.card X ≥ 3): Minimal (exists_nonempty_decisive_coalition_of_size F) 1 := by
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
    obtain ⟨C', hC3, hC4, hC5⟩ := decisive_coalition_contraction h0 hC1 h hF2 hF3 hX
    have hlt_C' : Fintype.card C' < Fintype.card C :=
      Set.card_lt_card hC4
    have hlt : Fintype.card C' < n := by
      simpa [hC2] using hlt_C'
    have ⟨hPn, hMin⟩ := hn
    have: (exists_nonempty_decisive_coalition_of_size F) (Fintype.card ↑C') := by
      exists C'
    have := Minimal.le_of_le hn this
    have h1: Fintype.card ↑C' + 1 ≤ n := by exact hlt
    have := Minimal.not_prop_of_lt hn hlt
    contradiction
  have: n = 1 := by
    apply Nat.le_antisymm
    exact Nat.le_of_lt_succ n_lt_two
    exact Nat.one_le_iff_ne_zero.mpr n_neq_zero
  rw [←this]
  exact hn

theorem exists_dictatorship [Nonempty I] [Fintype I] [Fintype X] (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) [∀ C: Set I, ∀ i, Decidable (i ∈ C)] {F: (I → Prefs X) → Prefs X} (h1: pareto F) (h2: iia F) {C: Set I} (h3: 2 ≤ Fintype.card C) (h4: coalition_decisive F C) (hX: Fintype.card X ≥ 3): dictatorship F := by
  have := decisive_coalition_minimal h0 h1 h2 hX
  obtain ⟨x, hx⟩ := this
  obtain ⟨C, hC0, hC1, hC2⟩ := x
  have: Nonempty C := by
    apply Fintype.card_pos_iff.mp
    simp_all [Fintype.card_ofFinset, Nat.lt_add_one]
  have x: C := Classical.ofNonempty
  have: C = (Set.singleton x.val) := by
    have: Fintype.card C ≤ 1 := by exact Nat.le_of_eq hC2
    have := Fintype.card_le_one_iff_subsingleton.mp this
    rw [Set.singleton]
    rename_i this_1 this_2
    simp_all only [ne_eq, Fintype.card_ofFinset, ge_iff_le, nonempty_subtype, le_refl, Set.subsingleton_coe,
      Set.setOf_eq_eq_singleton]
    obtain ⟨val, property⟩ := x
    obtain ⟨w, h⟩ := this_1
    simp_all only
    ext x : 1
    simp_all only [Set.mem_singleton_iff]
    apply Iff.intro
    · intro a
      apply this
      · simp_all only
      · simp_all only
    · intro a
      subst a
      simp_all only
  -- should follow quickly from `hC2 : Fintype.card ↑C = 1`
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

theorem arrow [Fintype X] [Fintype I] [Nonempty I]
  [∀ C: Set I, ∀ i, Decidable (i ∈ C)]
  (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z)
  (hX: Fintype.card X ≥ 3) -- oh wait h0 and hX equivalent..
  (F: (I → Prefs X) → Prefs X)
  (h1: pareto F) (h2: iia F): dictatorship F := by
  by_cases h: Fintype.card I ≤ 1
  have := Fintype.card_le_one_iff_subsingleton.mp h
  exact singleton_pareto_dictatorship h1
  simp [not_le] at h
  have: 2 ≤ Fintype.card I := by exact h
  apply exists_dictatorship (C := Set.univ) h0 h1 h2
  rw [Fintype.card_setUniv]
  exact h
  exact univ_coalition_decisive h1
  exact hX
