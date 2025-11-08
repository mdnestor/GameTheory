
variable {I X Y: Type}

-- Relations and basic definitions.

def Relation (X: Type u): Type u :=
  X → X → Prop

def Reflexive (R: Relation X): Prop :=
  ∀ x, R x x

def Antisymmetric (R: Relation X): Prop :=
  ∀ x y, R x y → R y x → x = y

def Top (R: Relation X) (x: X): Prop :=
  ∀ z, R z x

-- Given a relation R, the corresponding "strict" version.
def Strict (R: Relation X): Relation X :=
  fun x y => R x y ∧ ¬ R y x

def StrictTop (R: Relation X) (x: X): Prop :=
  ∀ z, z ≠ x → R z x

-- Given a function X → Y and a relation on Y, we can "pull back" to a relation on X.
def Pullback (f: X → Y) (R: Relation Y): Relation X :=
  fun x₁ x₂ => R (f x₁) (f x₂)

/-

Definition of a "preference profile": each player i ∈ I has a preference relation on X.

- The meet of a profile is the 'consensus relation', aka the 'Pareto improvement' relation.
- A profile π is Pareto efficient if ∄ some π' strictly preferred by the consensus.
- A preference profile is called 'zero-sum' if preferences are flipped between different players.

For notation we can use π for a preference profile and p for a particular preference.

-/

def Profile (I X: Type): Type :=
  I → Relation X

def Profile.meet (π: Profile I X): Relation X :=
  fun x y => ∀ i, π i x y

def Profile.pareto_efficient (π: Profile I X) (x: X): Prop :=
  ∀ y, ¬ Strict (meet π) x y

def Profile.zero_sum (π: Profile I X): Prop :=
  ∀ i j, i ≠ j → π i = flip (π j)

-- If x is a top element in the meet (consensus) relation then it is Pareto efficient.
theorem Profile.top_pareto_efficient {π: Profile I X} {x: X} (h: Top (meet π) x): pareto_efficient π x := by
  intro y
  simp [Strict]
  intro
  exact h y

/-

If a profile is zero-sum, there are ≥ 2 individuals, and every individual preference is reflexive and anti-symmetric,
then every outcome is Pareto efficient.

Proof:
- If x is not Pareto efficient, there exists strict Pareto improvement x'.
- So any two distinct players i, j weakly prefer x ≤ x'.
- By zero sum, since i weakly prefers x ≤ x' then j weakly prefers x' ≤ x.
- By reflexivity x = x', contradicting strict improvement.

-/

theorem Profile.zero_sum_pareto_efficient (h₀: ∀ i: I, ∃ j, i ≠ j) -- at least 2 players
  {π: Profile I X} (h₁: ∀ i, Reflexive (π i))
  (h₂: ∀ i, Antisymmetric (π i))
  (h: zero_sum π): ∀ x, pareto_efficient π x := by
  intro x x' h'
  simp [Strict, meet] at h'
  obtain ⟨i, hi⟩ := h'.right
  obtain ⟨j, hj⟩ := h₀ i
  have hi' := h'.left i
  have hj' := h'.left j
  have := h _ _ hj
  rw [this, flip] at hi'
  have: x' = x := h₂ _ _ _ hi' hj'
  rw [this] at hi
  exact hi (h₁ _ x)



/-

Definition of a "utility game" consisting of:

- a set I of players,
- a set S of strategies (assumed to be the same for all players),
- a set U of possible 'utilities' (typically U = ℝ),
- a 'play' function which maps strategy profiles to utility profiles,
- a preference relation on utility values, assumed to be shared by all players.

For example with U = ℝ, the shared utility preference is the standard order on ℝ.

Note the 'play' function is essentially the payoff matrix.

-/

variable {S U: Type}

class UtilityGame (I S U: Type) where
  play: (I → S) → I → U
  pref: Relation U

-- Definition of an "outcome game": instead of each player getting a utility,
-- there is a set of possible outcomes and each player has some preference on outcomes.

class OutcomeGame (I S O: Type) where
  play: (I → S) → O
  pref: Profile I O

-- Every utility game is an outcome game where the outcomes are utility assignments
-- and players prefer outcomes where they get higher utility.

def UtilityGame.toOutcomeGame (G: UtilityGame I S U): OutcomeGame I S (I → U) := {
  play := G.play
  pref := fun i => Pullback (fun u => u i) G.pref
}

-- Example: social choice as an example of an outcome game
example (π: Profile I X) (F: Profile (Profile I X) X): OutcomeGame I (Relation X) (Relation X) := {
  play := F
  pref := fun i => fun p₁ p₂ => ∀ x y, π i x y → p₁ x y → p₂ x y
}


-- General definition of a strategic game: we don't need to explicitly reference the set of outcomes.
-- Instead, the players can simply have preferences directly on strategy profiles.

class Game (I S: Type) where
  pref: Profile I (I → S)

-- This is actually an equivalent representation because we can treat the strategy profiles themselves as outcomes.
-- i.e. each player's preference on strategy profiles is the pullback along the play function.

def OutcomeGame.toGame (G: OutcomeGame I S X): Game I S := {
  pref := fun p => Pullback G.play (G.pref p)
}

def Game.toOutcomeGame (G: Game I S): OutcomeGame I S (I → S) := {
  play := id
  pref := G.pref
}

-- A game is zero sum if the underlying preference profile is zero sum.
def Game.zero_sum (G: Game I S): Prop :=
  Profile.zero_sum G.pref



-- The "update" of a function at a pair. Requires decidable equality on I.

variable [DecidableEq I]

abbrev update (σ: I → S) (i₀: I) (s₀: S): I → S :=
  fun i => if i = i₀ then s₀ else σ i

/-

For a fixed strategy profile σ, each player has an induced preference relation on strategies,
i.e. what they would rather do assuming everyone else is fixed.

A strategy is called a player's 'best response' wrt. σ if no other strategy is better in that profile.

σ is called a Nash equilibrium if everyone is playing a best response wrt. σ.

-/

def Game.strategy_pref (G: Game I S) (σ: I → S): Profile I S :=
  fun i => Pullback (update σ i) (G.pref i)

def Game.best_response (G: Game I S) (σ: I → S) (i: I) (s: S): Prop :=
  Top (G.strategy_pref σ i) s

def Game.nash_eq (G: Game I S) (σ: I → S): Prop :=
  ∀ i, G.best_response σ i (σ i)


/-

For a fixed player, a strategy s 'dominates' another strategy s₀ if it's always preferable to play s over s₀.
The strategy s is called 'dominant' if it dominates all other strategies.

A couple theorems:
- A strategy is dominant iff. it is the best response to every profile (this is basically just by definition).
- Any profile where every player is using a dominant strategy is a Nash equilibrium.

-/

def Game.dominates (G: Game I S): Profile I S :=
  fun i => Profile.meet (fun σ => G.strategy_pref σ i)

def Game.dominant (G: Game I S) (i: I) (s: S): Prop :=
  Top (G.dominates i) s

theorem Game.dominant_iff_best_response (G: Game I S) (i: I) (s: S): G.dominant i s ↔ ∀ σ, G.best_response σ i s := by
  exact forall_comm

theorem Game.dominant_equilibrium {G: Game I S} {σ: I → S} (h: ∀ i, G.dominant i (σ i)): G.nash_eq σ := by
  intro i s
  exact h i s σ



-- σ is called payoff dominant if it is Pareto superior to all Nash equilibria.

def Game.payoff_dominant {G: Game I S} (σ: I → S): Prop :=
  ∀ σ', G.nash_eq σ' → G.pref.meet σ' σ



/-

Example: prisoner's dilemma.

It is a utility game with 2 players {0, 1}, 2 strategies {true, false} (defect or not),
and 4 possible scores/utilities (sometimes described as costs / negative utilities).
The Nash equilibrium is for both to defect.

-/

def PrisonerDilemma: UtilityGame (Fin 2) Bool (Fin 4) := {
  play := fun σ => fun p => match (σ 0, σ 1) with
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

-- I have evidently committed some Lean sin. I think I need type class synthesis? TODO
example: PrisonerDilemma.toOutcomeGame.toGame.nash_eq (fun _ => true) := by
  intro p s
  simp_all [PrisonerDilemma, UtilityGame.toOutcomeGame, OutcomeGame.toGame, Game.strategy_pref, Pullback]
  match p with
  | 0 => cases s <;> simp
  | 1 => cases s <;> simp



-- Strict versions of the above.

def Game.strategy_pref_strict (G: Game I S) (σ: I → S): Profile I S :=
  fun i => Strict (strategy_pref G σ i)

def Game.best_response_strict (G: Game I S) (σ: I → S) (i: I) (s: S): Prop :=
  StrictTop (strategy_pref_strict G σ i) s

def Game.nash_eq_strict (G: Game I S) (σ: I → S): Prop :=
  ∀ i, best_response_strict G σ i (σ i)

def Game.dominates_strict (G: Game I S): Profile I S :=
  fun i => Profile.meet (fun σ => strategy_pref_strict G σ i)

def Game.dominant_strict (G: Game I S) (i: I) (s: S): Prop :=
  Top (dominates_strict G i) s

-- Strict best responses are unique.

theorem Game.strict_best_response_unique {G: Game I S} {σ: I → S} {i: I} {s s': S} (h1: G.best_response_strict σ i s) (h2: G.best_response_strict σ i s'): s = s' := by
  apply Classical.not_not.mp
  intro h
  apply (h1 s' (Ne.symm h)).right
  apply (h2 s _).left
  exact h

-- In a Nash equilibrium, the strategy of each player is unique (holding all others fixed).

theorem Game.strict_nash_equilibrium_strategy_unique {G: Game I S} {σ: I → S} {i: I} {s: S}
  (h1: G.nash_eq_strict σ) (h2: G.nash_eq_strict (update σ i s)): σ i = s := by
  sorry

-- If a strategy is strictly dominant, it is unique.

theorem Game.strict_dominant_unique [Nonempty S] {G: Game I S} {i: I} {s s': S} (h1: G.dominant_strict i s) (h2: G.dominant_strict i s'): s = s' := by
  let σ: I → S := Classical.ofNonempty
  have := h1 s' σ
  have := h2 s σ
  simp_all [strategy_pref_strict, Strict]
