A little game theory library written in Lean. Loosely based on Osborne and Rubinstein.

Currently there is no dependence on Mathlib, at the benefit of simplicity but at the cost of inability to touch the major theorems (like existence of a mixed Nash equilibrium).

Contains a proof of Arrow's impossibility theorem under GameTheory/SocialChoice.

### Code samples

Three versions of a normal form game:

```lean
class UtilityGame (P S U: Type) where
  play: (P → S) → (P → U)
  prefer: Endorelation U

class OutcomeGame (P S O: Type) where
  play: (P → S) → O
  prefer:  P → Endorelation O

class Game (P S: Type) where
  prefer: P → Endorelation (P → S)
```

Every utility game is a outcome game, every outcome game is a game.

```lean
example (G: UtilityGame P S U): OutcomeGame P S (P → U) := {
  play := G.play
  prefer := fun p => fun π0 π1 => G.prefer (π0 p) (π1 p)
}

example (G: OutcomeGame P S O): Game P S := {
  prefer := fun p => fun π0 π1 => G.prefer p (G.play π0) (G.play π1)
}
```

Prisoner's dilemma as a utility game:

```lean
def PrisonerDilemma: UtilityGame (Fin 2) Bool (Fin 4) := {
  play := fun π => fun p => match (π 0, π 1) with
    -- neither defect
    | (false, false) => match p with
      | 0 => 2
      | 1 => 2
    -- first defects
    | (true, false) => match p with
      | 0 => 3
      | 1 => 0
    -- second defects
    | (false, true) => match p with
      | 0 => 0
      | 1 => 3
    -- both defect
    | (true, true) => match p with
      | 0 => 1
      | 1 => 1
  prefer := fun u1 u2 => u1 ≤ u2
}

example: nash_equilibrium PrisonerDilemma.toGame (fun _ => true) := by
  intro p s
  rw [PrisonerDilemma, UtilityGame.toGame, UtilityGame.toOutcomeGame, OutcomeGame.toGame, prefer_strategy]
  simp [update]
  change Fin 2 at p
  change Bool at s
  match p with
  | 0 => cases s <;> simp
  | 1 => cases s <;> simp
```

Sequential games:

```lean
class SeqGame (P E A: Type) where
  move: (P → A) → E → E
  prefer: P → Endorelation (Nat → E)

class SeqUtilityGame (P E A U: Type) where
  move: (P → A) → E → E
  uvalue: E → P → U
  prefer: Endorelation U
```

Every sequential game is an outcome game (where the outcomes are state trajectories) and every sequential utility game (when paired with a utility sequence summation) is a utility game:

```lean
example (G: SeqGame P E A) (ε: E): OutcomeGame P (E → A) (Nat → E) := {
  play := fun π => G.run π ε
  prefer := G.prefer
}

example (G: SeqUtilityGame P E A U) (σ: (Nat → U) → U) (ε: E): UtilityGame P (E → A) U := {
  play := fun π =>
    let h := G.run π ε
    hvalue G σ h
  prefer := G.prefer
}
```
