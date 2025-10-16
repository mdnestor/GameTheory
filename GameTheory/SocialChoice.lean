/-

Arrow's impossibility theorem.

Based on the decisive coalitions argument.

TODO:
- better factorization of existence lemmas
- maybe just refer to the coalitions as finsets
- perhaps redo tripartition stuff in terms of function to Fin 3?

-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Minimal
import Mathlib.Order.SetNotation

set_option linter.unusedVariables false

variable {I X: Type*}

class Pref {X: Type*} (R: X → X → Prop): Prop where
  reflexive: Reflexive R
  transitive: Transitive R
  total: Total R

def Prefs (X: Type*): Set (X → X → Prop) :=
  {R | Pref R}

instance: CoeFun (Prefs X) (fun _ => X → X → Prop) where
  coe p := p.val

def strict (R: X → X → Prop): X → X → Prop :=
  fun x y => R x y ∧ ¬ R y x

theorem strict_transitive {R: X → X → Prop} (h: Transitive R): Transitive (strict R) := by
  intro x y z ⟨lexy, nleyx⟩ ⟨leyz, nlezy⟩
  have lexz := h lexy leyz
  have nlezx: ¬ R z x := by
    intro lezx
    exact nleyx (h leyz lezx)
  exact ⟨lexz, nlezx⟩

def decisive_over (F: (I → Prefs X) → Prefs X) (C: Set I) (x y: X): Prop :=
  ∀ π, (∀ i ∈ C, strict (π i) x y) → strict (F π) x y

def decisive (F: (I → Prefs X) → Prefs X) (C: Set I): Prop :=
  ∀ x y, decisive_over F C x y

def dictator (F: (I → Prefs X) → Prefs X) (i: I): Prop :=
  decisive F (Set.singleton i)

def dictatorship (F: (I → Prefs X) → Prefs X): Prop :=
  ∃ i, dictator F i

def pareto (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ π x y, (∀ i, strict (π i) x y) → strict (F π) x y

theorem univ_decisive {F: (I → Prefs X) → Prefs X} (h: pareto F): decisive F Set.univ := by
  intro x y π h1
  exact h π x y fun i => h1 i trivial

theorem singleton_pareto_dictator [Subsingleton I] {F: (I → Prefs X) → Prefs X} (h: pareto F) (i: I): dictator F i := by
   intro x y π hi
   apply h
   intro j
   rw [←Subsingleton.allEq i j]
   exact hi i rfl

theorem singleton_pareto_dictatorship [Subsingleton I] [Nonempty I] {F: (I → Prefs X) → Prefs X} (h: pareto F): dictatorship F := by
   exists Classical.ofNonempty
   apply singleton_pareto_dictator h

def weak_decisive_over (F: (I → Prefs X) → Prefs X) (C: Set I) (x y: X): Prop :=
  ∀ π, (∀ i ∈ C, strict (π i) x y) ∧ (∀ i ∉ C, strict (π i) y x) → strict (F π) x y

theorem decisive_over_weak_decisive_over {F: (I → Prefs X) → Prefs X} {C: Set I} {x y: X} (h: decisive_over F C x y): weak_decisive_over F C x y := by
  intro π h1
  exact h π h1.left

def iia (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ π1 π2 x y, (∀ i, π1 i x y ↔ π2 i x y) → (F π1 x y ↔ F π2 x y)

theorem iia_strict {F: (I → Prefs X) → Prefs X} (hF: iia F) {π π': I → Prefs X} {x z : X}
  (hxz: ∀ i, π i x z ↔ π' i x z) (hzx: ∀ i, π i z x ↔ π' i z x):
  strict (F π) x z ↔ strict (F π') x z := by
  have Hxz: (F π) x z ↔ (F π') x z := hF π π' x z hxz
  have Hzx: (F π) z x ↔ (F π') z x := hF π π' z x hzx
  simp [strict, Hxz, Hzx]

def pullback {X Y: Type*} (f: X → Y) (R: Y → Y → Prop): X → X → Prop :=
  fun x y => R (f x) (f y)

theorem pullback_pref {X Y: Type*} {R: Y → Y → Prop} (h: Pref R) (f: X → Y): Pref (pullback f R) := {
  reflexive := fun x => h.reflexive (f x)
  transitive := fun _ _ _ h1 h2 => h.transitive h1 h2
  total := fun x y => h.total (f x) (f y)
}

def rank_pref (r: X → Nat): Pref (fun a b => r a ≤ r b) := {
  reflexive := fun x => Nat.le_refl (r x)
  transitive := fun _ _ _ => Nat.le_trans
  total := fun x y => Nat.le_total (r x) (r y)
}

def modify_relation_between [DecidableEq X] (R: X → X → Prop) (x y z : X): X → X → Prop :=
  let r: X → Nat := fun a => if a = x then 0 else if a = y then 1 else if a = z then 2 else 0
  pullback r (Nat.le)

def modify_relation_below [DecidableEq X] (R: X → X → Prop) (x y z : X): X → X → Prop :=
  fun a b => if a = y then True else if b = y then False else R a b

def modify_relation_above [DecidableEq X] (R: X → X → Prop) (x y z : X): X → X → Prop :=
  fun a b => if b = y then True else if a = y then False else R a b

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
  simp_all [p', strict, Ne.symm hyz]

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
  simp_all [p', strict, Ne.symm hyz]

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

theorem exists_acyclic_pref {x y z : X}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z):
  ∃ p: Prefs X, strict p x y ∧ strict p y z := by
  classical
  let r: X → Nat := fun a => if a = x then 0 else if a = y then 1 else if a = z then 2 else 0
  let pref := rank_pref r
  exists ⟨fun a b => r a ≤ r b, rank_pref r⟩
  simp_all [r, strict, Ne.symm hxy, Ne.symm hyz, Ne.symm hxz]

theorem exists_condorcet_profile
  {x y z : X}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
  (c: I → Fin 3):
  ∃ π : I → Prefs X, ∀ i,
    (c i = 0 → strict (π i) x y ∧ strict (π i) y z) ∧
    (c i = 1 → strict (π i) y z ∧ strict (π i) z x) ∧
    (c i = 2 → strict (π i) z x ∧ strict (π i) x y) := by
  classical
  use fun i => match c i with
  | 0 => (exists_acyclic_pref hxy hxz hyz).choose
  | 1 => (exists_acyclic_pref hyz (Ne.symm hxy) (Ne.symm hxz)).choose
  | 2 => (exists_acyclic_pref (Ne.symm hxz) (Ne.symm hyz) hxy).choose
  intro i
  match _: c i with
  | 0 => simp_all; exact (exists_acyclic_pref hxy hxz hyz).choose_spec
  | 1 => simp_all; exact (exists_acyclic_pref (hyz) (Ne.symm hxy) (Ne.symm hxz)).choose_spec
  | 2 => simp_all; exact (exists_acyclic_pref (Ne.symm hxz) (Ne.symm hyz) hxy).choose_spec

def tripartition {I: Type*} (A B C: Set I): Prop :=
  (A ∩ B = ∅) ∧ (A ∩ C = ∅) ∧ (B ∩ C = ∅) ∧ (A ∪ B ∪ C = Set.univ)

theorem tripartition_lemma {I: Type*} {A B C: Set I} (h: tripartition A B C):
  ∀ i: I, (
    i ∈ A ∪ B ∪ C ∧
    (i ∈ A ↔ (i ∉ B ∧ i ∉ C)) ∧
    (i ∈ B ↔ (i ∉ A ∧ i ∉ C)) ∧
    (i ∈ C ↔ (i ∉ A ∧ i ∉ B)))
 := by
  intro i
  by_cases hA: i ∈ A <;> by_cases hB: i ∈ B <;> by_cases hC: i ∈ C <;> simp_all [tripartition]
  have := Set.mem_inter hA hB; simp_all
  have := Set.mem_inter hA hB; simp_all
  have := Set.mem_inter hA hC; simp_all
  have := Set.mem_inter hB hC; simp_all
  have: i ∉ A ∪ B ∪ C := by
    intro h
    match h with
    | Or.inl h => match h with
      | Or.inl h => contradiction
      | Or.inr h => contradiction
    | Or.inr h => contradiction
  rw [h.2.2.2] at this
  exact this trivial

theorem exists_condorcet_profile'
  {x y z : X}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
  {A B C: Set I} (hAB: A ∩ B = ∅) (hAC: A ∩ C = ∅) (hBC: B ∩ C = ∅) (hABC: A ∪ B ∪ C = Set.univ):
  ∃ π : I → Prefs X, ∀ i,
    (i ∈ A → strict (π i) x y ∧ strict (π i) y z) ∧
    (i ∈ B → strict (π i) y z ∧ strict (π i) z x) ∧
    (i ∈ C → strict (π i) z x ∧ strict (π i) x y) := by
  classical
  let c: I → Fin 3 := fun i =>
    if i ∈ A then 0 else if i ∈ B then 1 else 2
  have: ∀ i, (i ∈ A ↔ c i = 0) ∧ (i ∈ B ↔ c i = 1) ∧ (i ∈ C ↔ c i = 2) := by
    intro i
    by_cases hA: i ∈ A <;> by_cases hB: i ∈ B <;> by_cases hC: i ∈ C <;> simp_all [c]
    have := Set.mem_inter hA hB; simp_all
    have := Set.mem_inter hA hB; simp_all
    have := Set.mem_inter hA hC; simp_all
    have := Set.mem_inter hB hC; simp_all
    have: i ∉ A ∪ B ∪ C := by
      intro h
      match h with
      | Or.inl h => match h with
        | Or.inl h => contradiction
        | Or.inr h => contradiction
      | Or.inr h => contradiction
    rw [hABC] at this
    exact this trivial
  obtain ⟨π, hπ⟩ := exists_condorcet_profile hxy hxz hyz c
  exists π
  simp_all

theorem decisive_spread_forward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: weak_decisive_over F C x y): decisive_over F C x z := by
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

theorem decisive_spread_backward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z)
  {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I}
  (h: weak_decisive_over F C x y): decisive_over F C z y := by
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

theorem decisive_spread_symmetric {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z)
  {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I}
  (h: weak_decisive_over F C x y): decisive_over F C y x := by
  have := decisive_spread_forward hxy hxz hyz hF hF2 h
  have := decisive_over_weak_decisive_over this
  have := decisive_spread_backward hxz hxy (Ne.symm hyz) hF hF2 this
  have := decisive_over_weak_decisive_over this
  exact decisive_spread_forward hyz (Ne.symm hxy) (Ne.symm hxz) hF hF2 this

theorem decisive_spread_strengthen {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z)
  {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I}
  (h: weak_decisive_over F C x y): decisive_over F C x y := by
  have := decisive_spread_symmetric hxy hxz hyz hF hF2 h
  have := decisive_over_weak_decisive_over this
  exact decisive_spread_symmetric (Ne.symm hxy) hyz hxz hF hF2 this

theorem decisive_over_refl (F: (I → Prefs X) → Prefs X) {C: Set I}
  (hC: Nonempty C) (x: X): decisive_over F C x x := by
  simp [decisive_over]
  intro π
  have i: C := Classical.ofNonempty
  intro h
  have := h i i.prop
  simp_all [strict]

theorem decisive_spread {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z)
  {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (hC: Nonempty C)
  (h: weak_decisive_over F C x y): decisive F C := by
  intro s t
  by_cases h1: s = t
  subst h1
  exact decisive_over_refl F hC s
  by_cases h2: x = s <;> by_cases h3: x = t <;> by_cases h4: y = s <;> by_cases h5: y = t <;> simp_all
  exact decisive_spread_strengthen h1 hxz hyz hF hF2 h
  exact decisive_spread_forward hxy h1 h5 hF hF2 h
  subst h3 h4
  exact decisive_spread_symmetric hxy hxz hyz hF hF2 h
  subst h3
  have := decisive_spread_symmetric hxy hxz hyz hF hF2 h
  have := decisive_over_weak_decisive_over this
  exact decisive_spread_backward h5 h4 h2 hF hF2 this
  subst h4
  have := decisive_spread_symmetric h2 h3 h1 hF hF2 h
  have := decisive_over_weak_decisive_over this
  exact decisive_spread_forward (fun a => h2 (Eq.symm a)) h1 h3 hF hF2 this
  exact decisive_spread_backward h3 h2 h4 hF hF2 h
  have := decisive_spread_forward hxy h3 h5 hF hF2 h
  have := decisive_over_weak_decisive_over this
  exact decisive_spread_backward h3 h2 (fun a => h1 (Eq.symm a)) hF hF2 this

def exists_nonempty_decisive_of_size [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)]
  (F: (I → Prefs X) → Prefs X) (n: Nat): Prop :=
  ∃ C, C.Nonempty ∧ decisive F C ∧ Fintype.card C = n

theorem pareto_univ_decisive {F: (I → Prefs X) → Prefs X} (h: pareto F): decisive F Set.univ := by
  simp [decisive, decisive_over]
  exact fun x y p => h p x y

theorem exists_minimal_decisive_coalition [Nonempty I] [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)]
  {F: (I → Prefs X) → Prefs X} (h: pareto F): ∃ n, Minimal (exists_nonempty_decisive_of_size F) n := by
  apply exists_minimal_of_wellFoundedLT
  exists Fintype.card I
  exists Set.univ
  repeat' (apply And.intro)
  exact Set.nonempty_iff_univ_nonempty.mp (by assumption)
  exact pareto_univ_decisive h
  exact Fintype.card_setUniv

theorem decisive_contraction_lemma {I X : Type*}
  {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z)
  {A B C: Set I} (hC11 : Set.Nonempty A) (hABC: tripartition A B C)
  {F: (I → Prefs X) → Prefs X} (hF2 : pareto F) (hF3 : iia F)
  {π₀ : I → Prefs X}
  (hA : ∀ i ∈ A, strict (π₀ i) x y ∧ strict (π₀ i) y z)
  (hB : ∀ i ∈ B, strict (π₀ i) y z ∧ strict (π₀ i) z x)
  (hC : ∀ i ∈ C, strict (π₀ i) z x ∧ strict (π₀ i) x y)
  (h6: strict (F π₀) x z):
  decisive F A := by
  apply decisive_spread hxz hxy (Ne.symm hyz) hF2 hF3
  exact Set.Nonempty.to_subtype hC11
  intro π ⟨h7, h8⟩
  have h9: ∀ i ∈ A, strict (π₀ i) x z ∧ strict (π i) x z := by
    intro i hi
    simp [h7 i hi, strict_transitive (π₀ i).prop.transitive (hA i hi).left (hA i hi).right]
  have h9': ∀ i ∈ A, π₀ i x z ∧ π i x z := by
    intro i hi
    have := h9 i hi
    exact ⟨this.1.1, this.2.1⟩
  have h9'': ∀ i ∈ A, ¬ π₀ i z x ∧ ¬ π i z x := by
    intro i hi
    have := h9 i hi
    exact ⟨this.1.2, this.2.2⟩
  have h10: ∀ i ∉ A, strict (π₀ i) z x ∧ strict (π i) z x := by
    intro i hi
    constructor
    by_cases hi1: i ∈ B
    exact (hB i hi1).right
    have: i ∈ C := by simp_all [(tripartition_lemma hABC i).2.2.2]
    exact (hC i this).left
    exact h8 i hi
  have h10': ∀ i ∉ A, π₀ i z x ∧ π i z x := by
    intro i hi
    have := h10 i hi
    exact ⟨this.1.1, this.2.1⟩
  have h10': ∀ i ∉ A, ¬ π₀ i x z ∧ ¬ π i x z := by
    intro i hi
    have := h10 i hi
    exact ⟨this.1.2, this.2.2⟩
  have h11: ∀ i, π₀ i x z ↔ π i x z := by
    intro i; by_cases i ∈ A
    repeat simp_all
  have h11': ∀ i, π₀ i z x ↔ π i z x := by
    intro i; by_cases i ∈ A
    repeat simp_all
  have := iia_strict hF3 h11 h11'
  rw [←this]
  exact h6

theorem decisive_contraction [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)]
  (h0: ∃ x y z: X, x ≠ y ∧ x ≠ z ∧ y ≠ z) {F: (I → Prefs X) → Prefs X} {C: Set I}
  (h1: decisive F C) (h2: 2 ≤ Fintype.card C) (hF2: pareto F) (hF3: iia F):
  ∃ A, A.Nonempty ∧ A < C ∧ decisive F A := by

  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card h2
  let A: Set I := {i.val}
  let B := C \ A

  have A_nonempty: Set.Nonempty A := by exists i
  have B_nonempty: Set.Nonempty B := by
    simp [A, B]
    exists j
    simp
    apply Ne.symm
    exact Subtype.coe_ne_coe.mpr hij

  have A_le_C: A ⊆ C := by simp_all [A, B]
  have A_lt_C: A < C := by
    constructor
    exact A_le_C
    simp_all [A, B]
    exists j
    rcases i
    rcases j
    simp_all [Iff.symm comm]

  -- show A, B, Cᶜ form a partition
  have tri: tripartition A Cᶜ B := by
    repeat' (apply And.intro)
    repeat simp_all [A, B]
    rw [Set.inter_comm]
    ext
    simp_all
    have: C = A ∪ B := by simp_all [A, B]
    have:  A ∪ Cᶜ ∪ B =  A ∪ B ∪ Cᶜ := by apply Set.union_right_comm
    simp_all [A]

  have tri': tripartition B A Cᶜ := by
    repeat' (apply And.intro)
    exact Set.diff_inter_self
    simp_all [A, B]
    rw [Set.inter_comm]
    exact tri.2.2.1
    repeat simp_all [A, B]

  -- Let x, y, z be distinct
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := h0

  -- Obtain the Condorcet profile
  obtain ⟨π₀, hπ₀⟩ := exists_condorcet_profile' hxy hxz hyz tri.1 tri.2.1 tri.2.2.1 tri.2.2.2
  let h3 := fun i => (hπ₀ i).1
  let h5 := fun i => (hπ₀ i).2.1
  let h4 := fun i => (hπ₀ i).2.2

  -- Case 1: if π₀ votes x < z then A is decisive
  by_cases h6: strict (F π₀) x z
  exists A
  simp_all
  exact decisive_contraction_lemma hxy hxz hyz A_nonempty tri hF2 hF3 h3 h5 h4 h6

  -- Case 2: if π₀ does not vote x < z then it votes z < y and B is decisive
  have: strict (F π₀) x y := by
    apply h1
    intro i
    by_cases i ∈ A <;> simp_all [A, B]
  have h6': strict (F π₀) z y := by
    rcases this with ⟨hxy, n_yx⟩
    have hzx : (F π₀) z x := by
      rcases (F π₀).property.total x z with hxz | hzx
      · have : ¬¬ (F π₀) z x := by
          intro hn; exact h6 ⟨hxz, hn⟩
        exact not_not.mp this
      · exact hzx
    have pzy : (F π₀) z y := (F π₀).property.transitive hzx hxy
    have n_yz : ¬ (F π₀) y z := by
      intro hyz
      have hyx : (F π₀) y x := (F π₀).property.transitive hyz hzx
      exact n_yx hyx
    exact ⟨pzy, n_yz⟩

  exists B
  simp_all [A, B]
  exact decisive_contraction_lemma (Ne.symm hxz) (Ne.symm hyz) hxy B_nonempty tri' hF2 hF3 h4 h3 h5 h6'

theorem decisive_minimal [Nonempty I] [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)]
  (h0: ∃ x y z: X, x ≠ y ∧ x ≠ z ∧ y ≠ z) {F: (I → Prefs X) → Prefs X}
  (hF2: pareto F) (hF3: iia F): Minimal (exists_nonempty_decisive_of_size F) 1 := by
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
    obtain ⟨C', hC3, hC4, hC5⟩ := decisive_contraction h0 hC1 h hF2 hF3
    have hlt_C': Fintype.card C' < Fintype.card C := Set.card_lt_card hC4
    have hlt: Fintype.card C' < n := Nat.lt_of_lt_of_eq hlt_C' hC2
    have: (exists_nonempty_decisive_of_size F) (Fintype.card ↑C') := by exists C'
    have := Minimal.not_prop_of_lt hn hlt
    contradiction
  have: n = 1 := by
    apply Nat.le_antisymm
    exact Nat.le_of_lt_succ n_lt_two
    exact Nat.one_le_iff_ne_zero.mpr n_neq_zero
  rw [←this]
  exact hn

theorem exists_dictatorship [Nonempty I] [Fintype I] (h0: ∃ x y z: X, x ≠ y ∧ x ≠ z ∧ y ≠ z)
  [∀ C: Set I, ∀ i, Decidable (i ∈ C)] {F: (I → Prefs X) → Prefs X} (h1: pareto F) (h2: iia F) {C: Set I} (h3: 2 ≤ Fintype.card C)
  (h4: decisive F C): dictatorship F := by
  obtain ⟨i, _⟩ := decisive_minimal h0 h1 h2
  obtain ⟨C, hC0, hC1, hC2⟩ := i
  have: Nonempty C := Set.Nonempty.to_subtype hC0
  have i: C := Classical.ofNonempty
  have: C = {i.val} := by
    have: Fintype.card C ≤ 1 := by exact Nat.le_of_eq hC2
    have := Fintype.card_le_one_iff_subsingleton.mp this
    simp_all
    rcases i
    (expose_names; exact (Set.Nonempty.subset_singleton_iff hC0).mp fun ⦃a⦄ a_1 => this a_1 property)
  rw [this] at hC1
  exists i

theorem arrow [Fintype I] [Nonempty I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)]
  (h0: ∃ x y z: X, x ≠ y ∧ x ≠ z ∧ y ≠ z) (F: (I → Prefs X) → Prefs X)
  (h1: pareto F) (h2: iia F): dictatorship F := by
  by_cases h: Fintype.card I ≤ 1
  have := Fintype.card_le_one_iff_subsingleton.mp h
  exact singleton_pareto_dictatorship h1
  simp [not_le] at h
  apply exists_dictatorship h0 h1 h2
  rw [Fintype.card_setUniv]
  exact h
  exact univ_decisive h1
