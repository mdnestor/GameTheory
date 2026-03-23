
import Mathlib.Tactic.TypeStar

variable {I S X Y: Type*}

-- Relations and basic definitions.

def Rel (X: Type u): Type u :=
  X → X → Prop

def Refl (R: Rel X): Prop :=
  ∀ x, R x x

def Antisymm (R: Rel X): Prop :=
  ∀ x y, R x y → R y x → x = y

def RelTop (R: Rel X) (x: X): Prop :=
  ∀ z, R z x

def Strict (R: Rel X): Rel X :=
  fun x y => R x y ∧ ¬ R y x

def StrictRelTop (R: Rel X) (x: X): Prop :=
  ∀ z, z ≠ x → R z x

def Pullback (f: X → Y) (R: Rel Y): Rel X :=
  fun x₁ x₂ => R (f x₁) (f x₂)

/-

Since we are dealing with multiple relations on the same set,
this notation lets us write `x ≤[p] y` to means `x ≤ y` in the relation `p: Rel X`.
Similarly `x ≤[π i] y` means individual `i: I` prefers `x ≤ y` in the profile `π: I → Rel X`.

-/

notation:50 x:50 " ≤[" p "] " y:50 => p x y
notation:50 x:50 " <[" p "] " y:50 => p x y ∧ ¬ p y x


-- A 'preference profile' is a map `π: I → Rel X` where `I` is the set of individuals, `X` the set of outcomes.
-- The 'meet' of a preference profile is the 'consensus relation', i.e. the 'Pareto improvement' relation.

def Meet (π: I → Rel X): Rel X :=
  fun x y => ∀ i, x ≤[π i] y

-- An outcome `x` is Pareto efficient if no individual strictly prefers any alternative.

def ParetoEfficient (π: I → Rel X) (x: X): Prop :=
  ∀ y, ¬ (x <[Meet π] y)

-- If `x` is the top element in the consensus relation, it is Pareto efficient.

theorem RelTopParetoEfficient {π: I → Rel X} {x: X} (hx: RelTop (Meet π) x): ParetoEfficient π x := by
  intro; simp_all [RelTop]

-- A preference profile is called zero-sum if preferences are reversed between distinct players.

def ZeroSum (π: I → Rel X): Prop :=
  ∀ i j, i ≠ j → ∀ x y, x ≤[π i] y ↔ y ≤[π j] x

/-

Theorem: if a profile is zero-sum, there are ≥ 2 individuals, and every individual preference is reflexive and anti-symmetric,
then every outcome is Pareto efficient.

Proof:
- If x is not Pareto efficient, there exists strict Pareto improvement y.
- So any two distinct players i, j weakly prefer x ≤ y.
- By zero sum, since i weakly prefers x ≤ y then j weakly prefers y ≤ x.
- By reflexivity x = y, contradicting strict improvement.

-/

theorem ZeroSumParetoEfficient (h₀: ∀ i: I, ∃ j, i ≠ j) -- at least 2 players
  {π: I → Rel X} (h₁: ∀ i, Refl (π i))
  (h₂: ∀ i, Antisymm (π i))
  (h: ZeroSum π): ∀ x, ParetoEfficient π x := by
  intro x y h'
  simp [Meet] at h'
  obtain ⟨i, hi⟩ := h'.right
  obtain ⟨j, hj⟩ := h₀ i
  have hi' := h'.left i
  have hj' := h'.left j
  have := h _ _ hj
  rw [this] at hi'
  have: y = x := h₂ _ _ _ hi' hj'
  rw [this] at hi
  exact hi (h₁ _ x)



/-

Definition of a normal-form strategic game:
- `I` is the set of players
- `S` is the set of strategies (assumed to be shared for simplicity)
- `O` is the set of outcomes
- `play: (I → S) → O` maps strategy profiles to outcomes
- `pref: I → Rel O` gives each player's preference on outcomes.

-/

class Game (I S O: Type*) where
  play: (I → S) → O
  pref: I → Rel O

-- This instance lets us write `o₁ ≤[G i] o₂` to mean player i prefers o₁ ≤ o₂.

instance {I S O: Type*}: CoeFun (Game I S O) (fun _ => I → Rel O) where
  coe G := G.pref

-- A game is zero sum if the underlying preference profile is zero sum.

variable {I S O U: Type*}

def Game.zero_sum (G: Game I S O): Prop :=
  ZeroSum G.pref


-- Example: ranked choice voting as an example of an outcome game.
-- Both the strategy set and outcome set are ordering on `X`.

example (π: I → Rel X) (F: (I → Rel X) → Rel X): Game I (Rel X) (Rel X) := {
  play := F
  pref := fun i => fun r₁ r₂ => ∀ x y, x ≤[π i] y → x ≤[r₁] y → x ≤[r₂] y
}



/-

One more common definition of a game involves a utility score assigned to outcomes.
See https://en.wikipedia.org/wiki/Utility_representation_theorem

-/

class UtilityGame (I S U: Type*) where
  play: (I → S) → I → U
  pref: Rel U

-- Every utility game is an outcome game where the outcomes are utility assignments
-- and players prefer outcomes where they get higher utility.

def UtilityGame.toGame (G: UtilityGame I S U): Game I S (I → U) := {
  play := G.play
  pref := fun i => Pullback (fun u => u i) G.pref
}




-- The "update" of a function at a point. Requires decidable equality on I.
-- This is needed to define best response.

variable [DecidableEq I]

abbrev update (σ: I → S) (i₀: I) (s₀: S): I → S :=
  fun i => if i = i₀ then s₀ else σ i



/-

For a fixed strategy profile σ, each player has an induced preference relation on strategies,
i.e. what they would rather do assuming everyone else is fixed.

Namely, to compare two strategies s₁ and s₂, compare the outcome of playing them in the fixed profile σ.

-/

def Game.pref_strat (G: Game I S O) (σ: I → S) (i: I): Rel S :=
  fun s₁ s₂ =>
  let o₁ := G.play (update σ i s₁)
  let o₂ := G.play (update σ i s₂)
  G.pref i o₁ o₂



-- A strategy is called a player's 'best response' wrt. σ if no other strategy is better in that profile.

def Game.best_response (G: Game I S O) (σ: I → S) (i: I) (s: S): Prop :=
  RelTop (G.pref_strat σ i) s

def Game.best_response_rel (G: Game I S O): Rel (I → S) :=
  fun σ₁ σ₂ => ∀ i, G.best_response σ₁ i (σ₂ i)

-- σ is called a Nash equilibrium if everyone is playing a best response wrt. σ.

def Game.equilibrium (G: Game I S O) (σ: I → S): Prop :=
  ∀ i, G.best_response σ i (σ i)

-- σ is a Nash equilibrium if and only if it is a fixed point of the best response relation (trivial).

example (G: Game I S O) (σ: I → S): G.equilibrium σ ↔ G.best_response_rel σ σ := by
  rfl

/-

For a fixed player, a strategy s₁ 'dominates' another strategy s₀ if it's always preferable to play s₁ over s₀.
The strategy s₁ is called 'dominant' if it dominates all other strategies.

-/

def Game.dominates (G: Game I S O) (i: I): Rel S :=
  Meet (fun σ => G.pref_strat σ i)

def Game.dominant (G: Game I S O) (i: I) (s: S): Prop :=
  RelTop (G.dominates i) s

-- A strategy is dominant if and only if it is the best response in every situation.

theorem Game.dominant_iff_best_response (G: Game I S O) (i: I) (s: S): G.dominant i s ↔ ∀ σ, G.best_response σ i s := by
  exact forall_comm

-- If every player is playing a dominant strategy, it is a Nash equilibrium.

theorem Game.dominant_equilibrium {G: Game I S O} {σ: I → S} (h: ∀ i, G.dominant i (σ i)): G.equilibrium σ := by
  intro i s
  exact h i s σ



-- σ is called payoff dominant if it is Pareto superior to all Nash equilibria.

-- def Game.payoff_dominant {G: Game I S O} (σ: I → S): Prop :=
--   ∀ σ₀, G.equilibrium σ₀ → σ₀ ≤[Meet G.pref] σ



/-

Example: a (generalized) prisoner's dilemma.

Given a set of players `I` with a binary strategy {True, False} (whether to cooperate),
the prisoner's dilemma occurs when each player has the following preferences:

- Defecting is always preferable to not defecting.
- Otherwise, it's preferable that as many peers cooperate as possible.

The characteristic outcome of this scenario is that:

1. The Nash equilibrium is global defection, and yet,
2. This equilibrium is Pareto dominated by global cooperation.

-/

-- def PrisonerDilemma (I: Type): Game I Prop := {
--   pref := fun i π₁ π₂ => (π₁ i ∧ ¬ π₂ i) ∨ (∀ j, π₁ j → π₂ j)
-- }

-- def PrisonerDilemma' (G: Game I Prop): Prop :=
--   ∀ i, ∀ π₁ π₂, (π₁ i ∧ ¬ π₂ i) ∨ (∀ j, π₁ j → π₂ j) → π₁ ≤[G i] π₂

/-

The characteristic outcome of the prisoner's dilemma is that:
1. the Nash equilibrium is for all players to defect, but
2. this equilibrium is the worst for all players; namely EVERY other outcome is a Pareto improvement!

-/

-- -- First we can show that the best response for every player is not to cooperate.
-- def PDilemma_br {I: Type} [DecidableEq I] (π: I → Prop) (i: I): (PrisonerDilemma I).best_response π i False := by
--   intro p
--   by_cases p
--   repeat simp_all [PrisonerDilemma, Game.pref_strat, Pullback]

-- def PDilemma_br' {G: Game I Prop} (h: PrisonerDilemma' G) [DecidableEq I] (π: I → Prop) (i: I): G.best_response π i False := by
--   intro p
--   by_cases p
--   repeat simp_all [PrisonerDilemma', Game.pref_strat, Pullback]



-- example {I: Type} [DecidableEq I] {π: I → Prop}: (∀ i, ¬ π i) → (PrisonerDilemma I).equilibrium π := by
--   intro h i
--   by_cases hi : π i
--   · exact False.elim (h i hi)
--   · simpa [hi] using (PDilemma_br π i)

-- example {G: Game I Prop} (hG: PrisonerDilemma' G) [DecidableEq I] {π: I → Prop}: (∀ i, ¬ π i) → G.equilibrium π := by
--   intro h i
--   by_cases hi : π i
--   · exact False.elim (h i hi)
--   · simpa [hi] using (PDilemma_br' hG π i)


-- Global cooperation is a Pareto improvement over global defection.
-- example {I: Type}: Meet (PrisonerDilemma I).pref (fun _ => False) (fun _ => True) := by
--   intro i
--   right
--   intro j hj
--   exact True.intro

-- example {G: Game I Prop} (h: PrisonerDilemma' G): Meet G.pref (fun _ => False) (fun _ => True) := by
--   intro i
--   right
--   intro j hj
--   exact True.intro


-- Strict versions of the above.

def Game.pref_strat_strict (G: Game I S O) (σ: I → S): I → Rel S :=
  fun i => Strict (pref_strat G σ i)

def Game.best_response_strict (G: Game I S O) (σ: I → S) (i: I) (s: S): Prop :=
  StrictRelTop (pref_strat_strict G σ i) s

def Game.equilibrium_strict (G: Game I S O) (σ: I → S): Prop :=
  ∀ i, best_response_strict G σ i (σ i)

def Game.dominates_strict (G: Game I S O): I → Rel S :=
  fun i => Meet (fun σ => pref_strat_strict G σ i)

def Game.dominant_strict (G: Game I S O) (i: I) (s: S): Prop :=
  RelTop (dominates_strict G i) s

-- Strict best responses are unique.

theorem Game.strict_best_response_unique {G: Game I S O} {σ: I → S} {i: I} {s s': S} (h1: G.best_response_strict σ i s) (h2: G.best_response_strict σ i s'): s = s' := by
  apply Classical.not_not.mp
  intro h
  apply (h1 s' (Ne.symm h)).right
  apply (h2 s _).left
  exact h

-- In a Nash equilibrium, the strategy of each player is unique (holding all others fixed).

theorem Game.strict_equilibrium_strategy_unique {G: Game I S O} {σ: I → S} {i: I} {s: S}
  (h1: G.equilibrium_strict σ) (h2: G.equilibrium_strict (update σ i s)): σ i = s := by
  have hupdate : update (update σ i s) i = update σ i := by
    funext t
    funext j
    by_cases hj : j = i <;> simp [update, hj]
  have h2i := h2 i
  have h2' : G.best_response_strict σ i s := by
    intro z hz
    have hz' : z ≠ (update σ i s) i := by
      simpa [update] using hz
    have : Strict (G.pref_strat (update σ i s) i) z ((update σ i s) i) := h2i z hz'
    sorry -- simpa [Game.pref_strat_strict, Game.pref_strat, Pullback, update, hupdate] using this
  exact G.strict_best_response_unique (h1 i) h2'

-- If a strategy is strictly dominant, it is unique.

theorem Game.strict_dominant_unique [Nonempty S] {G: Game I S O} {i: I} {s s': S} (h1: G.dominant_strict i s) (h2: G.dominant_strict i s'): s = s' := by
  let σ: I → S := Classical.ofNonempty
  have := h1 s' σ
  have := h2 s σ
  simp_all [pref_strat_strict, Strict]
