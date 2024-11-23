/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `rcases'`
* `constructor`
* `rintro`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  rintro ⟨p, q⟩
  exact p
  done

example : P ∧ Q → Q := by
  rintro ⟨p, q⟩
  exact q
  done

example : (P → Q → R) → P ∧ Q → R := by
  rintro pqr ⟨p, q⟩
  apply pqr
  exact p
  exact q
  done

example : P → Q → P ∧ Q := by
  intro p q
  constructor
  exact p
  exact q
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  rintro ⟨p, q⟩
  constructor
  exact q
  exact p
  done

example : P → P ∧ True := by
  intro p
  constructor
  exact p
  triv
  done

example : False → P ∧ False := by
  intro f
  constructor
  · exfalso
    exact f
  · exact f
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  rintro ⟨p, q⟩ ⟨q, r⟩
  constructor
  exact p
  exact r
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro pqr p q
  apply pqr
  constructor
  exact p
  exact q
  done
