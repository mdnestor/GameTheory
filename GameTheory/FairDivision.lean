
import GameTheory
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sets

set_option linter.unusedSectionVars false

/-

This file is about fair division problems (aka cake-cutting problems). https://en.wikipedia.org/wiki/Fair_division

First I define an "assignment problem" consisting of
- a set A of agents
- a set X of items/objects?
- each player has a preference on items.

An assignment is called 'envy-free' if no agent would prefer another's item.

As a special case you might have that each agent places a utility value on each item.

Next I define a "division problem" which assigns each element of a set C (the "cake") to each agent.
This is an assignment problem where the items are subsets of C.

-/

variable {A C P U X: Type}

class Assignment (A X: Type) where
  assign: A → X
  pref: A → Endorelation X

def envy_free {A X: Type} (A: Assignment A X): Prop :=
  ∀ i j, A.pref i (A.assign j) (A.assign i)


class UtilityAssignment (A X U: Type) where
  assign: A → X
  util: A → X → U
  pref: Endorelation U

def UtilityAssignment.toAssignment (A: UtilityAssignment P X U): Assignment P X := {
  assign := A.assign
  pref := fun p => fun x1 x2 => A.pref (A.util p x1) (A.util p x2)
}

-- A utility assignment is called equitable if all players assign equal utility to their assigned item.

def equitable (A: UtilityAssignment P X U): Prop :=
  ∀ i j, A.util i (A.assign i) = A.util j (A.assign j)

-- It is called a consensus if all players agree on the value of assigned items.

def consensus (A: UtilityAssignment P X U): Prop :=
  ∀ i j, A.util i (A.assign i) = A.util j (A.assign i)



class Division (A C: Type) where
  divide: C → A
  pref: A → Endorelation (Set C)

def Division.share {A C: Type} (D: Division A C) (a: A): Set C :=
  Set.preimage D.divide {a}

def Division.toAssignment (D: Division A C): Assignment A (Set C) := {
  assign := D.share
  pref := D.pref
}



class UtilityDivision (A C U: Type) where
  divide: C → A
  util: A → Set C → U
  pref: Endorelation U

def UtilityDivision.toDivision (D: UtilityDivision P C U): Division P C := {
  divide := D.divide
  pref := fun p => fun s1 s2 => D.pref (D.util p s1) (D.util p s2)
}

def UtilityDivision.toUtilityAssignment (D: UtilityDivision P C U): UtilityAssignment P (Set C) U := {
  assign := D.toDivision.share
  util := D.util
  pref := D.pref
}

-- We will call a utility division problem homogeneous
-- if the utility of a set only depends on its cardinality.

def homogeneous [Fintype C] [∀ S: Set C, ∀ x, Decidable (x ∈ S)] (D: UtilityDivision A C U): Prop :=
  ∀ a, ∀ s1 s2, D.pref (D.util a s1) (D.util a s2) ↔ Fintype.card s1 ≤ Fintype.card s2

-- A homogeneous division problem can only be equitable if the # of agents divides the # of items.

theorem homogeneous_nonequitable_if [Fintype A] [Fintype C] [∀ S: Set C, ∀ x, Decidable (x ∈ S)]
  (D: UtilityDivision A C U) (h: homogeneous D): equitable D.toUtilityAssignment →  Fintype.card A ∣ Fintype.card C := by
  sorry
