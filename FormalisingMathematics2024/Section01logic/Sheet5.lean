/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`
* `apply Iff.intro`
-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro pq
  exact pq.symm
  --rw [pq]
  -- 通过重写策略，将P ↔ Q 转换为 Q ↔ P
  -- exact pq.symm
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  apply Iff.intro
  -- apply Iff.intro 用来拆分目标为两个方向的证明
  · intro pq
    exact pq.symm
  · intro qp
    exact qp.symm
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry
  done

example : P ∧ Q ↔ Q ∧ P := by
  sorry
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  sorry
  done

example : P ↔ P ∧ True := by
  sorry
  done

example : False ↔ P ∧ False := by
  sorry
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry
  done

example : ¬(P ↔ ¬P) := by
  sorry
  done
