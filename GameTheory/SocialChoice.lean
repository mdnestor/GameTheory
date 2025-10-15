
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sets

import Mathlib.Order.Minimal
import Mathlib.Data.Set.Finite.Basic

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


/- strict decisive -/

-- I need to show strict is a pref?

def strict (p : Prefs X) (a b : X) : Prop := p a b ∧ ¬ p b a

def strict_pareto (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ π x y, (∀ i, strict (π i) x y) → strict (F π) x y


def coalition_strict_decisive_over (F: (I → Prefs X) → Prefs X) (C: Set I) (x y: X): Prop :=
  ∀ π, (∀ i ∈ C, strict (π i) x y) → strict (F π) x y

def coalition_strict_decisive (F: (I → Prefs X) → Prefs X) (C: Set I): Prop :=
  ∀ x y, coalition_strict_decisive_over F C x y

def coalition_weak_strict_decisive_over (F: (I → Prefs X) → Prefs X) (C: Set I) (x y: X): Prop :=
  ∀ π, (∀ i ∈ C, strict (π i) x y) ∧ (∀ i ∉ C, strict (π i) y x) → strict (F π) x y

def coalition_strict_decisive_over_weak_strict_decisive_over {F: (I → Prefs X) → Prefs X} {C: Set I} {x y: X} (h: coalition_strict_decisive_over F C x y): coalition_weak_strict_decisive_over F C x y := by
  intro π h1
  exact h π h1.left

theorem univ_coalition_strict_decisive {F: (I → Prefs X) → Prefs X} (h: strict_pareto F): coalition_strict_decisive F Set.univ := by
  intro x y π h1
  exact h π x y fun i => h1 i trivial

def decisive (F: (I → Prefs X) → Prefs X) (i: I) (x y: X): Prop :=
  ∀ π, π i x y → F π x y

def dictator (F: (I → Prefs X) → Prefs X) (i: I): Prop :=
  ∀ x y, decisive F i x y

def strict_decisive (F: (I → Prefs X) → Prefs X) (i: I) (x y: X): Prop :=
  ∀ π, strict (π i) x y → strict (F π) x y


def strict_dictator (F: (I → Prefs X) → Prefs X) (i: I): Prop :=
  ∀ x y, strict_decisive F i x y

def liberal (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ i, ∃ x y, decisive F i x y

def dictatorship (F: (I → Prefs X) → Prefs X): Prop :=
  ∃ i, dictator F i

def strict_dictatorship (F: (I → Prefs X) → Prefs X): Prop :=
  ∃ i, strict_dictator F i

def iia (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ π1 π2 x y, (∀ i, π1 i x y ↔ π2 i x y) → (F π1 x y ↔ F π2 x y)

def iia2 (F: (I → Prefs X) → Prefs X): Prop :=
  ∀ π1 π2 x y, (∀ i, (π1 i x y ↔ π2 i x y) ∧ (π1 i y x ↔ π2 i y x)) → (F π1 x y ↔ F π2 x y)

theorem iia_implies_iia2 {F: (I → Prefs X) → Prefs X} (h: iia F): iia2 F := by
  intro _ _ _ _ h1
  apply h
  intro i
  exact (h1 i).left

-- ∀ x z, π x z ∧ π x y ↔ π x z ∧ ¬ π x y
-- ∀ x z, π x z ∧ π y z ↔ π x z ∧ ¬ π y z

-- Given a profile π, and distinct x, y, z, can always find a modified profile π' such that
-- πi x z ↔ πi' x z
-- ∀ i ∈ A, πi x y
-- ∀ i ∈ Aᶜ, πi y x
-- ∀ i ∈ B, πi y z
-- ∀ i ∈ Bᶜ, πi z y
-- This needs an additional hypothesis about voters in a set...


lemma lex_trans {α : Type} [LinearOrder α] {R : X → X → Prop}
  (hR : Transitive R)
  {f : X → α} :
  Transitive (fun a b => f a < f b ∨ f a = f b ∧ R a b) := by
  intro a b c h₁ h₂
  rcases h₁ with (h₁ | ⟨rfl₁, Rab⟩)
  rcases h₂ with (h₂ | ⟨rfl₂, Rbc⟩)
  · exact Or.inl (lt_trans h₁ h₂)
  · exact Or.inl (lt_of_lt_of_eq h₁ rfl₂)
  ·
    simp_all only
    cases h₂ with
    | inl h => simp_all only [true_or]
    | inr h_1 =>
      simp_all only [lt_self_iff_false, true_and, false_or]
      obtain ⟨left, right⟩ := h_1
      apply hR
      · exact Rab
      · simp_all only--  Or.inl (lt_of_eq_of_lt rfl₁ h₂)

def rank_pref (r: X → Nat): Pref (fun a b => r a ≤ r b) := {
  refl := fun x => Nat.le_refl (r x)
  trans := fun _ _ _ => Nat.le_trans
  total := fun x y => Nat.le_total (r x) (r y)
}

-- theorem modify1
--   (p: Prefs X)
--   {x y z : X}
--   (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
--   (h : p x z):
--   ∃ p' : Prefs X, (p x z ↔ p' x z) ∧ p' x y ∧ p' y z := by
--   classical
--   let r: X → Nat := fun a => if a = x then 0 else if a = y then 1 else if a = z then 1 else 0
--   use ⟨fun a b => r a ≤ r b, rank_pref r⟩
--   simp [r]
--   constructor
--   exact h
--   repeat (split; repeat simp_all)

-- theorem modify2
--   (p: Prefs X)
--   {x y z : X}
--   (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z):
--   ∃ p' : Prefs X, (p x z ↔ p' x z) ∧ p' x y ∧ p' z y := by
--     classical
--   let r: X → Nat := fun a => if a = x then 0 else if a = y then 2 else if a = z then 1 else 0
--   use ⟨fun a b => r a ≤ r b, rank_pref r⟩
--   simp [r]
--   constructor
--   repeat (split; repeat simp_all)


theorem exists_modified_vote2
  (π : I → Prefs X)
  {x y z : X}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
  {C : Set I}
  (h : ∀ i ∈ C, π i x z) :
  ∃ π' : I → Prefs X,
    (∀ i, π i x z ↔ π' i x z) ∧
    (∀ i, π i z x ↔ π' i z x) ∧
    (∀ i ∈ C, π' i x y ∧ π' i y z) ∧
    (∀ i ∉ C, π' i y x ∧ π' i y z) := by
  sorry

theorem exists_modified_vote3
  (π : I → Prefs X)
  {x y z : X}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
  {C : Set I}
  (h : ∀ i ∈ C, strict (π i) x z) :
  ∃ π' : I → Prefs X,
    (∀ i, (π i) x z ↔ (π' i) x z) ∧
    (∀ i, (π i) z x ↔ (π' i) z x) ∧
    (∀ i ∈ C, strict (π' i) x y ∧ strict (π' i) y z) ∧
    (∀ i ∉ C, strict (π' i) y x ∧ strict (π' i) y z) := by
  sorry




-- theorem exists_modified_vote' (π: I → Prefs X) {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {C: Set I} (h: ∀ i ∈ C, π i x z):
--   ∃ π': I → Prefs X,
--   (∀ i, π i x z ↔ π' i x z) ∧
--   (∀ i ∈ C, π' i x y ∧ π' i y z) ∧
--   (∀ i ∉ C, π' i x y ∧ π' i z y) := by
--   classical
--   let π' := fun i => if hi: i ∈ C then
--     Classical.choose (modify1 (π i) hxy hxz hyz (h i hi))
--   else
--     Classical.choose (modify2 (π i) hxy hxz hyz)
--   use π'
--   constructor
--   intro i
--   by_cases hi: i ∈ C
--   have hm := modify1 (π i) hxy hxz hyz (h i hi)
--   have: π' i = Classical.choose hm := by exact dif_pos hi
--   rw [this]
--   have := Classical.choose_spec hm
--   repeat' (apply And.intro)
--   exact this.1
--   have hm := modify2 (π i) hxy hxz hyz
--   have: π' i = Classical.choose hm := by exact (Ne.dite_eq_right_iff fun h_1 a => hi h_1).mpr hi
--   rw [this]
--   have := Classical.choose_spec hm
--   exact this.1
--   intro i hi
--   have hm := modify1 (π i) hxy hxz hyz (h i hi)
--   have: π' i = Classical.choose hm := by exact dif_pos hi
--   rw [this]
--   have := Classical.choose_spec hm
--   exact this.2
--   intro i hi
--   have hm := modify2 (π i) hxy hxz hyz
--   have: π' i = Classical.choose hm := by exact (Ne.dite_eq_right_iff fun h_1 a => hi h_1).mpr hi
--   rw [this]
--   have := Classical.choose_spec hm
--   exact this.2

theorem decisive_spread_forward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C x z := by
  intro π h1
  obtain ⟨π', h2, h3, h4, h5⟩ := exists_modified_vote2 π hxy hxz hyz h1
  simp_all [hF2 π π' x z h2]
  apply (F π').property.trans _ y
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

-- theorem decisive_spread_backward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C z y := by
--   intro π h1
--   have hzx: z ≠ x := by exact id (Ne.symm hxz)
--   have hzy: z ≠ y := by exact id (Ne.symm hyz)
--   obtain ⟨π', h2, h3, h4⟩ := exists_modified_vote' π hzx hzy hxy h1
--   simp_all [hF2 π π' z y h2]
--   apply (F π').property.trans _ x
--   · apply hF π'
--     intro i
--     by_cases hi: i ∈ C
--     · exact (h3 i hi).left
--     · exact (h4 i hi).left
--   · apply h
--     constructor
--     · intro i hi
--       exact (h3 i hi).right
--     · intro i hi
--       exact (h4 i hi).right

-- theorem decisive_spread_symmetric (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C y x := by
--   obtain ⟨z, hxz, hyz⟩ := h0 x y
--   have: coalition_decisive_over F C x z := by exact decisive_spread_forward hxy hxz hyz hF hF2 h
--   have: coalition_weak_decisive_over F C x z := by exact coalition_decisive_over_weak_decisive_over this
--   have: coalition_decisive_over F C y z := by exact decisive_spread_backward hxz hxy (id (Ne.symm hyz)) hF hF2 this
--   have: coalition_weak_decisive_over F C y z := by exact coalition_decisive_over_weak_decisive_over this
--   exact decisive_spread_forward hyz (id (Ne.symm hxy)) (id (Ne.symm hxz)) hF hF2 this

-- theorem decisive_spread_strengthen (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive_over F C x y := by
--   have: coalition_decisive_over F C y x := by exact decisive_spread_symmetric h0 hxy hF hF2 h
--   have: coalition_weak_decisive_over F C y x := by exact coalition_decisive_over_weak_decisive_over this
--   exact decisive_spread_symmetric h0 (id (Ne.symm hxy)) hF hF2 this

-- theorem decisive_spread (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_decisive_over F C x y): coalition_decisive F C := by
--   intro s t
--   by_cases h1: s = t
--   subst h1
--   exact coalition_decisive_over_refl F C s
--   by_cases h2: x = s <;> by_cases h3: x = t <;> by_cases h4: y = s <;> by_cases h5: y = t <;> simp_all
--   exact decisive_spread_strengthen h0 h1 hF hF2 h
--   exact decisive_spread_forward hxy h1 h5 hF hF2 h
--   subst h3 h4
--   exact decisive_spread_symmetric h0 hxy hF hF2 h
--   subst h3
--   have := by exact decisive_spread_symmetric h0 hxy hF hF2 h
--   have := by exact coalition_decisive_over_weak_decisive_over this
--   exact decisive_spread_backward h5 h4 h2 hF hF2 this
--   subst h4
--   have := by exact decisive_spread_symmetric h0 h2 hF hF2 h
--   have := by exact coalition_decisive_over_weak_decisive_over this
--   exact decisive_spread_forward (fun a => h2 (id (Eq.symm a))) h1 h3 hF hF2 this
--   exact decisive_spread_backward h3 h2 h4 hF hF2 h
--   have := by exact decisive_spread_forward hxy h3 h5 hF hF2 h
--   have := by exact coalition_decisive_over_weak_decisive_over this
--   exact decisive_spread_backward h3 h2 (fun a => h1 (id (Eq.symm a))) hF hF2 this

lemma iia_strict
  {F : (I → Prefs X) → Prefs X} (hF2 : iia F)
  {π π' : I → Prefs X} {x z : X}
  (hxz : ∀ i, (π i) x z ↔ (π' i) x z)
  (hzx : ∀ i, (π i) z x ↔ (π' i) z x) :
  strict (F π) x z ↔ strict (F π') x z := by
  -- weak IIA on both directions
  have Hxz : (F π) x z ↔ (F π') x z := hF2 π π' x z hxz
  have Hzx : (F π) z x ↔ (F π') z x := hF2 π π' z x hzx
  -- unfold strict: p x z ∧ ¬ p z x
  simpa [strict, Hxz, Hzx]

theorem exists_modified_vote4
  (π : I → Prefs X)
  {x y z : X}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
  {C : Set I}
  (h : ∀ i ∈ C, π i x z) :
  ∃ π' : I → Prefs X,
    (∀ i, π i x z ↔ π' i x z) ∧
    (∀ i, π i z x ↔ π' i z x) ∧
    (∀ i ∈ C, π' i x y ∧ π' i y z) ∧
    (∀ i ∉ C, π' i y x ∧ π' i y z) := by
  sorry

lemma strict_trans_of_total_trans
  {r : Prefs X} :
  strict r x y → strict r y z → strict r x z :=
by
  rintro ⟨rxy, n_yx⟩ ⟨ryz, n_zy⟩
  have rxz : r x z := r.prop.trans _ _ _ rxy ryz
  have n_zx : ¬ r z x := by
    intro rzx
    have rzy : r z y := r.prop.trans _ _ _ rzx rxy
    exact n_zy rzy
  exact ⟨rxz, n_zx⟩

/-- Weak IIA on both directions transports a **strict** comparison. -/
lemma iia_strict2
  {F : (I → Prefs X) → Prefs X} (hF2 : iia F)
  {π π' : I → Prefs X} {x z : X}
  (hxz : ∀ i, (π i) x z ↔ (π' i) x z)
  (hzx : ∀ i, (π i) z x ↔ (π' i) z x) :
  strict (F π) x z ↔ strict (F π') x z :=
by
  have Hxz : (F π) x z ↔ (F π') x z := hF2 π π' x z hxz
  have Hzx : (F π) z x ↔ (F π') z x := hF2 π π' z x hzx
  simpa [strict, Hxz, Hzx]


theorem strict_decisive_spread_forward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: (I → Prefs X) → Prefs X} (hF: strict_pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_strict_decisive_over F C x y): coalition_strict_decisive_over F C x z := by
  intro π h1
  obtain ⟨π', h2, h3, h4, h5⟩ := exists_modified_vote3 π hxy hxz hyz h1
  rw [iia_strict2 hF2 h2 h3]
  apply strict_trans_of_total_trans-- (F π')--.property.trans _ y
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

theorem exists_modified_vote5
  (π : I → Prefs X)
  {x y z : X}
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
  {C : Set I}
  (h : ∀ i ∈ C, strict (π i) x z) :
  ∃ π' : I → Prefs X,
    (∀ i, (π i) x z ↔ (π' i) x z) ∧
    (∀ i, (π i) z x ↔ (π' i) z x) ∧
    (∀ i ∈ C, strict (π' i) x y ∧ strict (π' i) y z) ∧
    (∀ i ∉ C, strict (π' i) x y ∧ strict (π' i) z y) := by
  sorry

theorem strict_decisive_spread_backward {x y z: X} (hxy: x ≠ y) (hxz: x ≠ z) (hyz: y ≠ z) {F: (I → Prefs X) → Prefs X} (hF: strict_pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_strict_decisive_over F C x y): coalition_strict_decisive_over F C z y := by
  intro π h1
  have hzx: z ≠ x := by exact id (Ne.symm hxz)
  have hzy: z ≠ y := by exact id (Ne.symm hyz)
  obtain ⟨π', h2, h3, h4, h5⟩ := exists_modified_vote5 π hzx hzy hxy h1
  rw [iia_strict2 hF2 h2 h3]
  apply strict_trans_of_total_trans
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

theorem strict_decisive_spread_symmetric (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: strict_pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_strict_decisive_over F C x y): coalition_strict_decisive_over F C y x := by
  obtain ⟨z, hxz, hyz⟩ := h0 x y
  have: coalition_strict_decisive_over F C x z := by exact strict_decisive_spread_forward hxy hxz hyz hF hF2 h
  have: coalition_weak_strict_decisive_over F C x z := by exact coalition_strict_decisive_over_weak_strict_decisive_over this
  have: coalition_strict_decisive_over F C y z := by exact strict_decisive_spread_backward hxz hxy (id (Ne.symm hyz)) hF hF2 this
  have: coalition_weak_strict_decisive_over F C y z := by exact coalition_strict_decisive_over_weak_strict_decisive_over this
  exact strict_decisive_spread_forward hyz (id (Ne.symm hxy)) (id (Ne.symm hxz)) hF hF2 this

theorem strict_decisive_spread_strengthen (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: strict_pareto F) (hF2: iia F) {C: Set I} (h: coalition_weak_strict_decisive_over F C x y): coalition_strict_decisive_over F C x y := by
  have: coalition_strict_decisive_over F C y x := by exact strict_decisive_spread_symmetric h0 hxy hF hF2 h
  have: coalition_weak_strict_decisive_over F C y x := by exact coalition_strict_decisive_over_weak_strict_decisive_over this
  exact strict_decisive_spread_symmetric h0 (id (Ne.symm hxy)) hF hF2 this

theorem coalition_strict_decisive_over_refl (F: (I → Prefs X) → Prefs X) {C: Set I} (hC: Nonempty C) (x: X): coalition_strict_decisive_over F C x x := by
  simp [coalition_strict_decisive_over]
  intro π
  have i: C := Classical.ofNonempty
  intro h
  have := h i i.prop
  simp_all [strict]

theorem strict_decisive_spread (h0: ∀ x y: X, ∃ z, x ≠ z ∧ y ≠ z) {x y: X} (hxy: x ≠ y) {F: (I → Prefs X) → Prefs X} (hF: strict_pareto F) (hF2: iia F) {C: Set I} (hC: Nonempty C) (h: coalition_weak_strict_decisive_over F C x y): coalition_strict_decisive F C := by
  intro s t
  by_cases h1: s = t
  subst h1
  exact coalition_strict_decisive_over_refl F hC s
  by_cases h2: x = s <;> by_cases h3: x = t <;> by_cases h4: y = s <;> by_cases h5: y = t <;> simp_all
  exact strict_decisive_spread_strengthen h0 h1 hF hF2 h
  exact strict_decisive_spread_forward hxy h1 h5 hF hF2 h
  subst h3 h4
  exact strict_decisive_spread_symmetric h0 hxy hF hF2 h
  subst h3
  have := by exact strict_decisive_spread_symmetric h0 hxy hF hF2 h
  have := by exact coalition_strict_decisive_over_weak_strict_decisive_over this
  exact strict_decisive_spread_backward h5 h4 h2 hF hF2 this
  subst h4
  have := by exact strict_decisive_spread_symmetric h0 h2 hF hF2 h
  have := by exact coalition_strict_decisive_over_weak_strict_decisive_over this
  exact strict_decisive_spread_forward (fun a => h2 (id (Eq.symm a))) h1 h3 hF hF2 this
  exact strict_decisive_spread_backward h3 h2 h4 hF hF2 h
  have := by exact strict_decisive_spread_forward hxy h3 h5 hF hF2 h
  have := by exact coalition_strict_decisive_over_weak_strict_decisive_over this
  exact strict_decisive_spread_backward h3 h2 (fun a => h1 (id (Eq.symm a))) hF hF2 this

def exists_nonempty_coalition_of_size [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (F: (I → Prefs X) → Prefs X) (n: Nat): Prop :=
  ∃ C, C.Nonempty ∧ coalition_decisive F C ∧ Fintype.card C = n

def exists_nonempty_strict_decisive_coalition_of_size [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (F: (I → Prefs X) → Prefs X) (n: Nat): Prop :=
  ∃ C, C.Nonempty ∧ coalition_strict_decisive F C ∧ Fintype.card C = n

theorem pareto_univ_decisive {F: (I → Prefs X) → Prefs X} (h: pareto F): coalition_decisive F Set.univ := by
  simp [coalition_decisive, coalition_decisive_over]
  exact fun o1 o2 p => h p o1 o2

theorem strict_pareto_univ_strict_decisive {F: (I → Prefs X) → Prefs X} (h: strict_pareto F): coalition_strict_decisive F Set.univ := by
  simp [coalition_strict_decisive, coalition_strict_decisive_over]
  exact fun o1 o2 p => h p o1 o2

theorem exists_minimal_decisive_coalition [Nonempty I] [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] {F: (I → Prefs X) → Prefs X} (h: pareto F): ∃ n, Minimal (exists_nonempty_coalition_of_size F) n := by
   apply exists_minimal_of_wellFoundedLT
   exists Fintype.card I
   exists Set.univ
   repeat' (apply And.intro)
   exact Set.nonempty_iff_univ_nonempty.mp (by assumption)
   exact pareto_univ_decisive h
   exact Fintype.card_setUniv

theorem exists_minimal_strict_decisive_coalition [Nonempty I] [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] {F: (I → Prefs X) → Prefs X} (h: strict_pareto F): ∃ n, Minimal (exists_nonempty_strict_decisive_coalition_of_size F) n := by
  apply exists_minimal_of_wellFoundedLT
  exists Fintype.card I
  exists Set.univ
  repeat' (apply And.intro)
  exact Set.nonempty_iff_univ_nonempty.mp (by assumption)
  exact strict_pareto_univ_strict_decisive h
  exact Fintype.card_setUniv


theorem strict_decisive_coalition_contraction_lemma {I X : Type}
  [Fintype I] [Fintype X] --[(C : Set I) → (i : I) → Decidable (i ∈ C)]
  (h0 : ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z)
  {F : (I → ↑(Prefs X)) → ↑(Prefs X)}
  {C : Set I}
  (hF2 : strict_pareto F)
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
  ∃ C', C'.Nonempty ∧ C' < C ∧ coalition_strict_decisive F C' := by
  classical
  exists C1
  constructor
  exact Set.nonempty_coe_sort.mp hC11
  constructor
  simp_all [nonempty_subtype, Set.lt_eq_ssubset, ne_eq]
  apply strict_decisive_spread h0 hxz hF2 hF3
  assumption
  intro π ⟨h7, h8⟩
  have h9: ∀ i ∈ C1, strict (π₀ i) x z ∧ strict (π i) x z := by
    intro i hi
    have := h7 i hi
    simp [h7 i hi, strict_trans_of_total_trans (h3 i hi).left (h3 i hi).right]
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

theorem strict_decisive_coalition_contraction [Fintype I] [Fintype X] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) {F: (I → Prefs X) → Prefs X} {C: Set I} (h1: coalition_strict_decisive F C) (h2: 2 ≤ Fintype.card C) (hF2: strict_pareto F) (hF3: iia F) (hX: Fintype.card X ≥ 3): ∃ C', C'.Nonempty ∧ C' < C ∧ coalition_strict_decisive F C' := by
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
  exact strict_decisive_coalition_contraction_lemma h0 hF2 hF3 hC11 hC12 hxz h3 h4 h5 h6
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
    have pzy : (F π₀) z y := (F π₀).property.trans _ _ _ hzx hxy
    have n_yz : ¬ (F π₀) y z := by
      intro hyz
      have hyx : (F π₀) y x := (F π₀).property.trans _ _ _ hyz hzx
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
  apply strict_decisive_spread h0 hzy hF2 hF3
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
    apply strict_trans_of_total_trans
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


theorem strict_decisive_coalition_minimal [Nonempty I] [Fintype X] [Fintype I] [∀ C: Set I, ∀ i, Decidable (i ∈ C)] (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) {F: (I → Prefs X) → Prefs X} (hF2: strict_pareto F) (hF3: iia F) (hX: Fintype.card X ≥ 3): Minimal (exists_nonempty_strict_decisive_coalition_of_size F) 1 := by
  obtain ⟨n, hn⟩ := exists_minimal_strict_decisive_coalition hF2
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
    obtain ⟨C', hC3, hC4, hC5⟩ := strict_decisive_coalition_contraction h0 hC1 h hF2 hF3 hX
    have hlt_C' : Fintype.card C' < Fintype.card C :=
      Set.card_lt_card hC4
    have hlt : Fintype.card C' < n := by
      simpa [hC2] using hlt_C'
    have ⟨hPn, hMin⟩ := hn
    have: (exists_nonempty_strict_decisive_coalition_of_size F) (Fintype.card ↑C') := by
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

theorem exists_strict_dictatorship [Nonempty I] [Fintype I] [Fintype X] (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z) [∀ C: Set I, ∀ i, Decidable (i ∈ C)] {F: (I → Prefs X) → Prefs X} (h1: strict_pareto F) (h2: iia F) {C: Set I} (h3: 2 ≤ Fintype.card C) (h4: coalition_strict_decisive F C) (hX: Fintype.card X ≥ 3): strict_dictatorship F := by
  have := strict_decisive_coalition_minimal h0 h1 h2 hX
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
theorem singleton_strict_pareto_strict_dictator [Subsingleton I] {F: (I → Prefs X) → Prefs X} (h: strict_pareto F) (i: I): strict_dictator F i := by
   intro x y π hi
   apply h
   intro j
   rw [←Subsingleton.allEq i j]
   exact hi

theorem singleton_strict_pareto_strict_dictatorship [Subsingleton I] [Nonempty I] {F: (I → Prefs X) → Prefs X} (h: strict_pareto F): strict_dictatorship F := by
   exists Classical.ofNonempty
   apply singleton_strict_pareto_strict_dictator h

theorem arrow [Fintype X] [Fintype I] [Nonempty I]
  [∀ C: Set I, ∀ i, Decidable (i ∈ C)]
  (h0: ∀ (x y : X), ∃ z, x ≠ z ∧ y ≠ z)
  (hX: Fintype.card X ≥ 3) -- oh wait h0 and hX equivalent..
  (F: (I → Prefs X) → Prefs X)
  (h1: strict_pareto F) (h2: iia F): strict_dictatorship F := by
  by_cases h: Fintype.card I ≤ 1
  have := Fintype.card_le_one_iff_subsingleton.mp h
  exact singleton_strict_pareto_strict_dictatorship h1
  simp [not_le] at h
  have: 2 ≤ Fintype.card I := by exact h
  apply exists_strict_dictatorship (C := Set.univ) h0 h1 h2
  rw [Fintype.card_setUniv]
  exact h
  exact univ_coalition_strict_decisive h1
  exact hX
