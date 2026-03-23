/-

Open games (in the category of sets).

Reference: "Compositional Game Theory" by Ghani et al.
1. https://arxiv.org/pdf/1603.04641

I will mirror the notation in the reference,
but for simplicity I will not use lenses.

-/

import Mathlib.Data.Set.Basic
import GameTheory.StrategicGame

variable {X S Y R Z Q: Type*}

-- For convenience `1` will denote the unit type.

local instance: One Type := ⟨Unit⟩


-- Definition of an open game (X, S) → (Y, R).
structure OpenGame.{u} (X S Y R: Type*) where
  strat: Type u
  play: strat → X → Y
  coplay: strat → X → R → S
  best_response: X → (Y → R) → Rel strat

-- A (closed) normal-form game with player set I, strategy set S, and outcome set O can be represented as open game (1, 1) → (O, O).
def Game.toOpenGame {I S O: Type*} [DecidableEq I] (G: Game I S O): OpenGame 1 1 O O := {
  strat := I → S
  play := fun σ _ => G.play σ
  coplay := fun _ _ _ => ()
  best_response := fun _ _ => G.best_response_rel
}

-- Composition of open games.
def OpenGame.comp (G: OpenGame X S Y R) (H: OpenGame Y R Z Q): OpenGame X S Z Q := {
  strat := G.strat × H.strat
  play   := fun (σ, τ) x => H.play τ (G.play σ x)
  coplay := fun (σ, τ) x q => G.coplay σ x (H.coplay τ (G.play σ x) q)
  best_response := fun x k (σ, τ) (σ', τ') =>
    let k' := fun y => H.coplay τ y (k (H.play τ y))
    (G.best_response x k' σ σ') ∧ (H.best_response (G.play σ x) k τ τ')
}

-- The type of scalar open games.
def ScalarOpenGame.{u}: Type (u + 1) :=
  OpenGame 1 1 1 1

-- Given play and coplay functions, the "trivial" open game with singleton strategy profile set and always-true best strategy relation.
def TrivialOpenGame (play: X → Y) (coplay: X → R → S): OpenGame X S Y R := {
  strat := 1
  play := fun _ => play
  coplay := fun _ => coplay
  best_response := fun _ _ _ _ => True
}

-- On an arbitrary set X, the counit open game (X, X) → (1, 1).
-- Definition 8 in [1].
def Counit (X: Type*): OpenGame X X 1 1 :=
  TrivialOpenGame (fun _ => ()) (fun x _ => x)

-- Given a normal form game represented as an open game (1, 1) → (O, O),
-- we can compose it with the counit (O, O) → (1, 1) to get a scalar open game.
def Game.toScalarOpenGame {I S O: Type*} [DecidableEq I] (G: Game I S O): ScalarOpenGame :=
  OpenGame.comp (G.toOpenGame) (Counit O)

-- Definition 5 in [1].
def Selection (X Y R: Type*) (δ: (Y → R) → Set Y): OpenGame X 1 Y R := {
  strat := X → Y
  play := fun σ x => σ x
  coplay := fun _ _ _ => ()
  best_response := fun x k _ σ' => σ' x ∈ δ k
}

def argmax [LE R] (k: Y → R): Set Y :=
  {y | ∀ y₀, k y₀ ≤ k y}

-- Definition 4 in [1].
def Decision (X Y R: Type*) [LE R]: OpenGame X 1 Y R :=
  Selection X Y R argmax

-- Definition 7 in [1].
def Function (f: X → Y) (g: R → S): OpenGame X S Y R :=
  TrivialOpenGame f (fun _ => g)

def CovariantLift (f: X → Y): OpenGame X 1 Y 1 :=
  Function f id

def ContravariantLift (f: X → Y): OpenGame 1 Y 1 X :=
  Function id f






-- Binary product of open games.

def OpenGame.prod {X₁ X₂ S₁ S₂ Y₁ Y₂ R₁ R₂: Type*} (G₁: OpenGame X₁ S₁ Y₁ R₁) (G₂: OpenGame X₂ S₂ Y₂ R₂): OpenGame (X₁ × X₂) (S₁ × S₂) (Y₁ × Y₂) (R₁ × R₂) := {
  strat := G₁.strat × G₂.strat
  play := fun (σ₁, σ₂) (x₁, x₂) => (G₁.play σ₁ x₁, G₂.play σ₂ x₂)
  coplay := fun (σ₁, σ₂) (x₁, x₂) (r₁, r₂) => (G₁.coplay σ₁ x₁ r₁, G₂.coplay σ₂ x₂ r₂)
  best_response :=
    fun (x₁, x₂) k (σ₁, σ₂) (σ'₁, σ'₂) =>
    let k₁ := fun y₁ => (k (y₁, G₂.play σ₂ x₂)).1
    let k₂ := fun y₂ => (k (G₁.play σ₁ x₁, y₂)).2
    (G₁.best_response x₁ k₁ σ₁ σ'₁) ∧ (G₂.best_response x₂ k₂ σ₂ σ'₂)
}

-- Indexed product of open games.

def OpenGame.iProd {ι: Type*} [DecidableEq ι] {X S Y R: ι → Type*} (G: (i: ι) → OpenGame (X i) (S i) (Y i) (R i)):
  OpenGame ((i: ι) → X i) ((i: ι) → S i) ((i: ι) → Y i) ((i: ι) → R i) := {
  strat := (i: ι) → (G i).strat
  play := fun σ x i => (G i).play (σ i) (x i)
  coplay := fun σ x r i => (G i).coplay (σ i) (x i) (r i)
  best_response :=
    fun x k σ σ' =>
    let kᵢ: (i: ι) → (Y i → R i) := fun i => fun y =>
      let σᵢ := fun (j: ι) => if h: j = i then (Eq.ndrec (motive := fun i => Y i → Y j) id h y) else (G j).play (σ j) (x j)
      k σᵢ i
    ∀ i, (G i).best_response (x i) (kᵢ i) (σ i) (σ' i)
}

/-

Theorem 2:
Let X and R be sets and assume R has an ordering ≤.
Let I be a set of players and for each i let be a decision D_i: (1, 1) -> (X, R).
Let G = Π_i D_i be their monoidal product.
Let q: (I → X) → I → R be an arbitrary function.

Let B_G be the best response of G.
Then the relation B_G(-, q) is equal to the best response relation of the normal-form game with outcome function q.

TODO: this proof could be cleaner.

-/

theorem decision_product_simultaneous_move_game (I X R: Type*) [DecidableEq I] [LE R] (q: (I → X) → I → R):
  let G := OpenGame.iProd (fun _ => Decision 1 X R)
  let LHS := fun (σ σ': I → X) => G.best_response (fun _ => ()) q (fun i _ => σ i) (fun i _ => σ' i)
  let RHS := ({play := q, pref := LE.le}: UtilityGame I X R).toGame.best_response_rel
  LHS = RHS := by
  ext σ σ'
  constructor
  intro h
  repeat simp_all [
    OpenGame.iProd,
    Decision,
    Selection,
    argmax,
    UtilityGame.toGame,
    Game.best_response_rel,
    Game.best_response,
    RelTop,
    Game.pref_strat,
    Pullback
  ]




-- Equivalence of open games.

structure OpenGameEquiv (G₁ G₂: OpenGame X S Y R) where
  imap: Equiv G₁.strat G₂.strat
  play: ∀ σ x, G₁.play σ x = G₂.play (imap σ) x
  coplay: ∀ σ x r, G₁.coplay σ x r = G₂.coplay (imap σ) x r
  best_response: ∀ x k σ σ', G₁.best_response x k σ σ' ↔ G₂.best_response x k (imap σ) (imap σ')

def OpenGameEquiv.refl (G: OpenGame X S Y R): OpenGameEquiv G G := {
  imap := Equiv.refl G.strat
  play := by intros; rfl
  coplay := by intros; rfl
  best_response := by intros; rfl
}

def OpenGameEquiv.symm {G₁ G₂: OpenGame X S Y R} (i: OpenGameEquiv G₁ G₂): OpenGameEquiv G₂ G₁ := {
  imap := Equiv.symm i.imap
  play := by intros; rw [i.play, Equiv.symm]; simp
  coplay := by intros; rw [i.coplay, Equiv.symm]; simp
  best_response := by intros; rw [i.best_response, Equiv.symm]; simp
}

def OpenGameEquiv.trans {G₁ G₂ G₃: OpenGame X S Y R} (i₁: OpenGameEquiv G₁ G₂) (i₂: OpenGameEquiv G₂ G₃): OpenGameEquiv G₁ G₃ := {
  imap := Equiv.trans i₁.imap i₂.imap
  play := by intros; rw [i₁.play, i₂.play]; simp
  coplay := by intros; rw [i₁.coplay, i₂.coplay]; simp
  best_response := by intros; rw [i₁.best_response, i₂.best_response]; simp
}

def OpenGame.equiv_rel {X S Y R: Type*}: Rel (OpenGame X S Y R) :=
  fun G₁ G₂: OpenGame X S Y R => Nonempty (OpenGameEquiv G₁ G₂)

theorem OpenGameEquiv.is_equivalence (X S Y R: Type*): Equivalence (@OpenGame.equiv_rel X S Y R) := {
  refl := fun G => Nonempty.intro (OpenGameEquiv.refl G)
  symm := fun h => Nonempty.intro (OpenGameEquiv.symm (Nonempty.some h))
  trans := fun h₁ h₂ => Nonempty.intro (OpenGameEquiv.trans (Nonempty.some h₁) (Nonempty.some h₂))
}

theorem OpenGame.equiv_lift_comp (G G': OpenGame X S Y R) (H H': OpenGame Y R Z Q) (h₁: OpenGame.equiv_rel G G') (h₂: OpenGame.equiv_rel H H'):
  OpenGame.equiv_rel (OpenGame.comp G H) (OpenGame.comp G' H') := by
  sorry

theorem OpenGame.equiv_lift_prod (G₁ G₁': OpenGame X₁ S₁ Y₁ R₁) (G₂ G₂': OpenGame X₂ S₂ Y₂ R₂) (h₁: OpenGame.equiv_rel G₁ G₁') (h₂: OpenGame.equiv_rel G₂ G₂'):
  OpenGame.equiv_rel (OpenGame.prod G₁ G₂) (OpenGame.prod G₁' G₂') := by
  sorry

theorem OpenGame.equiv_lift_iProd {ι: Type*} [DecidableEq ι] {X S Y R: ι → Type*} (G G': (i: ι) → OpenGame (X i) (S i) (Y i) (R i)) (h: ∀ i, OpenGame.equiv_rel (G i) (G' i)):
  OpenGame.equiv_rel (OpenGame.iProd G) (OpenGame.iProd G') := by
  sorry
