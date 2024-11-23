/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `True` and `False`

We learn about the `True` and `False` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/


-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by
  triv
  done

example : True → True := by
  intro _
  triv
  done

example : False → True := by
  intro _
  triv
  done

example : False → False := by
  intro p
  exfalso
  exact p
  done

example : (True → False) → False := by
  intro p
  apply p
  triv
  done

example : False → P := by
  intro h
  exfalso
  exact h
  done

example : True → False → True → False → True → False := by
  intro t1 f2 t3 f4 t5
  exact f2
  done

example : P → (P → False) → False := by
  intro p pf
  apply pf
  exact p
  done

example : (P → False) → P → Q := by
  intro pf p
-- 因为 h1 : P → False 和 h2 : P 逻辑上是互相矛盾的，我们可以通过它们推导出 False，从而使用 exfalso。
  exfalso
  exact pf p
  done

example : (True → False) → P := by
  intro tf
-- 将当前的目标（证明 P）转化为证明 False
  exfalso
  apply tf
  triv
  done
