
variable {I X Y: Type}

def Relation (X: Type u): Type u :=
  X → X → Prop

def reflexive (R: Relation X): Prop :=
  ∀ x, R x x

def antisymmetric (R: Relation X): Prop :=
  ∀ x y, R x y → R y x → x = y

def top (R: Relation X) (x: X): Prop :=
  ∀ x₀, R x₀ x

def strict (R: Relation X): Relation X :=
  fun x y => R x y ∧ ¬ R y x

def strict_top (R: Relation X) (x: X): Prop :=
  ∀ x₀, x ≠ x₀ → R x₀ x

/-

The meet of an indexed family of endorelations (aka preference profile)
is the agreement of all members.
In game theory terms this is the 'Pareto improvement' relation.

-/

@[simp]
def meet (π: I → Relation X): Relation X :=
  fun x y => ∀ i, π i x y

/-

Two important operations on endorelations:
- given a relation on Y and a function X → Y, pullback to a relation on X.
- given a relation on Y and a point x, pullback to a relation on X → Y.

-/

@[simp]
def pullback (R: Relation Y) (f: X → Y): Relation X :=
  fun x₁ x₂ => R (f x₁) (f x₂)

@[simp]
def pullback_eval (R: Relation Y) (x: X): Relation (X → Y) :=
  pullback R (fun f => f x)

-- An outcome is Pareto efficient wrt. a preference profile if it is not strictly Pareto dominated.

def pareto_efficient (π: I → Relation X) (x: X): Prop :=
  ∀ x₁, ¬ strict (meet π) x x₁

-- A preference profile is called 'zero-sum' if preferences are flipped between different players.

def zero_sum (π: I → Relation X): Prop :=
  ∀ i j x y, i ≠ j → (π i x y ↔ π j y x)

/-

In a zero-sum game with at least 2 players and all preferences reflexive and anti-symmetric,
every outcome is Pareto efficient.

Proof:
- If x is not Pareto efficient, there exists strict Pareto improvement x'.
- So any two distinct players i, j weakly prefer x ≤ x'.
- By zero sum, since i weakly prefers x ≤ x' then j weakly prefers x' ≤ x.
- By reflexivity x = x', contradicting strict improvement.

-/

theorem zero_sum_pareto_efficient {π: I → Relation X} (h1: zero_sum π) (h2: ∀ i, reflexive (π i)) (h3: ∀ i, antisymmetric (π i)) (h4: ∀ i: I, ∃ j, i ≠ j): ∀ x, pareto_efficient π x := by
  intro π π' h5
  simp_all [strict]
  rcases h5.2 with ⟨i, hi1⟩
  rcases h4 i with ⟨j, hj1⟩
  have hi2 := h5.1 i
  have hj2 := h5.1 j
  have hj3 := (h1 _ _ _ _ hj1).mp hi2
  have h6 := h3 _ _ _ hj2 hj3
  rw [h6] at hi1
  exact hi1 (h2 i π')

/-

First definition of a normal-form game based on the notion of utility, consisting of:

- a set of players,
- a set of strategies (assumed to be the same for all players),
- a set of possible 'utility' values,
- a 'play' function which maps strategy profiles to utility profiles, where
  - a 'strategy profile' is a choice of strategy for each player,
  - a 'utility profile' is an assignment of utilities to each player; and
- a preference relation on utility values, assumed to be shared by all players.

For example the utility could be a numerical value
and all players agree "more is better" (for themselves).

Note the 'play' function wraps what is usually called the 'payoff matrix'.

-/

variable {S U: Type}

class UtilityGame (I S U: Type) where
  play: (I → S) → (I → U)
  pref: Relation U

-- A generalization: instead of each player getting a utility,
-- the game has some 'outcome' and the players have a preference on outcomes.

class OutcomeGame (I S O: Type) where
  play: (I → S) → O
  pref: I → Relation O

-- Social choice as an example of an outcome game

example (pref: I → Relation X) (F: (I → Relation X) → Relation X):
  OutcomeGame I (Relation X) (Relation X) := {
  play := F
  pref := fun i p₁ p₂ => ∀ x y, pref i x y → p₁ x y → p₂ x y
}

-- Every utility game is an outcome game where the outcomes are utility assignments
-- and players prefer outcomes where they get higher utility.

@[simp]
def UtilityGame.toOutcomeGame (G: UtilityGame I S U): OutcomeGame I S (I → U) := {
  play := G.play
  pref := pullback_eval G.pref
}

-- One more further disillation: we don't need to explicitly reference the set of outcomes.
-- Instead, the players can have preferences directly on strategy profiles.

class Game (I S: Type) where
  pref: I → Relation (I → S)


-- This is actually an equivalent representation because we can treat the strategy profiles themselves as outcomes.
-- ie each player's preference on strategy profiles is the pullback along the play function.

@[simp]
def OutcomeGame.toGame (G: OutcomeGame I S X): Game I S := {
  pref := fun p => pullback (G.pref p) G.play
}

@[simp]
def UtilityGame.toGame (G: UtilityGame I S U): Game I S :=
  G.toOutcomeGame.toGame

@[simp]
def Game.toOutcomeGame (G: Game I S): OutcomeGame I S (I → S) := {
  play := id
  pref := G.pref
}

def zero_sum_game (G: Game I S): Prop :=
  zero_sum G.pref

-- Example: two-player zero-sum utility game.
example (S U: Type) [LE U] [Add U] [Zero U] (h1: ∀ u1 u2: U, u1 + u2 = u2 + u1) (h2: ∀ u1 u2 u1' u2': U, u1 + u2 = u1' + u2' → u1 ≤ u1' → u2' ≤ u2) (play: (Fin 2 → S) → (Fin 2 → U)) (h3: ∀ π, play π 0 + play π 1 = 0): zero_sum_game (UtilityGame.mk play LE.le).toOutcomeGame.toGame := by
  intro i j _ _
  match hij: (i, j) with
  | (0, 0) | (1, 1) => simp_all
  | (0, 1) | (1, 0) => simp_all; constructor <;> (
    intro h4
    apply h2
    repeat rw [h1, h3]
    exact h4
  )

-- Given a function f: X → Y and a pair (x0, y0) we can "update" f to take the value f(x0) = y0.
-- See https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Function/Basic.html#Function.update

variable [DecidableEq I]

@[simp]
def update (π: I → S) (i₀: I) (s₀: S): I → S :=
  fun i => if i = i₀ then s₀ else π i

-- For a fixed strategy profile, each player has an induced preference relation on strategies,
-- i.e. what they would rather do assuming everyone else is fixed.

@[simp]
def strategy_pref (G: Game I S) (π: I → S): I → Relation S :=
  fun i => pullback (G.pref i) (update π i)

-- Given a fixed strategy profile, a strategy is called a player's 'best response'
-- if no other strategy is better in that profile.

def best_response (G: Game I S) (π: I → S) (i: I) (s: S): Prop :=
  top (strategy_pref G π i) s

-- A Nash equilibrium is a profile in which every player is using their best response.
-- equivalently it is a top element in the induced Pareto relation on strategies.

def Game.nash_eq (G: Game I S) (π: I → S): Prop :=
  ∀ i, best_response G π i (π i)

-- For a fixed player, a strategy s 'dominates' another strategy s₀ if it's always preferable to play s over s₀.
-- The strategy s is called 'dominant' if it dominates all other strategies.

def dominates (G: Game I S) (i: I): Relation S :=
  meet (fun π => strategy_pref G π i)

def dominant (G: Game I S) (i: I) (s: S): Prop :=
  top (dominates G i) s

-- Some immediately obvious theorems:
-- A strategy is dominant iff. it is the best response to every profile (this is basically just by definition).

theorem dominant_iff_best_response (G: Game I S) (i: I) (s: S): dominant G i s ↔ ∀ π, best_response G π i s := by
  exact forall_comm

-- Any profile where every player is using a dominant strategy is a Nash equilibrium.

theorem dominant_equilibrium {G: Game I S} {π: I → S} (h: ∀ i, dominant G i (π i)): G.nash_eq π := by
  intro p s
  exact h p s π

def payoff_dominant {G: Game I S} (π: I → S): Prop :=
  ∀ π₀, G.nash_eq π₀ → meet G.pref π₀ π

example {G: Game I S}: Relation (I → S) :=
  meet G.pref


/-

Example: prisoner's dilemma.

It is a utility game with 2 players {0, 1}, 2 strategies {true, false} (defect or not),
and 4 possible scores/utilities (sometimes described as costs / negative utilities).
The Nash equilibrium is for both to defect.

-/

def PrisonerDilemma: UtilityGame (Fin 2) Bool (Fin 4) := {
  play := fun π => fun p => match (π 0, π 1) with
    | (false, false) => 2           -- neither defect
    | (true, true) => 1             -- both defect
    | (true, false) => match p with -- first defects
      | 0 => 3
      | 1 => 0
    | (false, true) => match p with -- second defects
      | 0 => 0
      | 1 => 3
  pref := LE.le
}

example: PrisonerDilemma.toGame.nash_eq (fun _ => true) := by
  intro p s
  rw [PrisonerDilemma]
  match p with
  | 0 => cases s <;> simp
  | 1 => cases s <;> simp


-- Given a preference, there is the associated "strict" preference, along with all the associated notions


def strict_strategy_pref (G: Game I S) (π: I → S) (p: I): Relation S :=
  strict (strategy_pref G π p)

def strict_best_response (G: Game I S) (π: I → S) (p: I) (s: S): Prop :=
  strict_top (strict_strategy_pref G π p) s

def strict_nash_equilibrium (G: Game I S) (π: I → S): Prop :=
  ∀ p, strict_best_response G π p (π p)

def strict_dominates (G: Game I S) (p: I): Relation S :=
  meet (fun π => strict_strategy_pref G π p)

def strict_dominant (G: Game I S) (p: I) (s: S): Prop :=
  top (strict_dominates G p) s

-- Strict best responses are unique.

theorem strict_best_response_unique {G: Game I S} {π: I → S} {p: I} {s s': S} (h1: strict_best_response G π p s) (h2: strict_best_response G π p s'): s = s' := by
  apply Classical.not_not.mp
  intro h
  apply (h1 s' h).right
  apply (h2 s _).left
  exact fun a => h (id (Eq.symm a))

-- In a Nash equilibrium, the strategy of each player is unique (holding all others fixed).

theorem strict_nash_equilibrium_strategy_unique {G: Game I S} {π: I → S} {p: I} {s: S}
  (h1: strict_nash_equilibrium G π) (h2: strict_nash_equilibrium G (update π p s)): π p = s := by
  have h1p := h1 p
  have h2p := h2 p
  apply strict_best_response_unique (h1 p)

  simp_all [strict_best_response]--
  sorry
  --, strict_strategy_pref]



-- If a strategy is strictly dominant, it is unique.

theorem strict_dominant_unique [Nonempty S] {G: Game I S} {p: I} {s s': S} (h1: strict_dominant G p s) (h2: strict_dominant G p s'): s = s' := by
  let π: I → S := Classical.ofNonempty
  have := h1 s' π
  have := h2 s π
  simp_all [strict_strategy_pref, strict]
