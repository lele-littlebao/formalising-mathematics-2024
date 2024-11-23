/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`
* `rfl`-- 一般用来证明等式
* `iff.rfl`-- exact iff.rfl 一般用来证明等价命题

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬P ↔ P → False := by
  change ¬ P ↔ ¬ P
  exact Iff.rfl
  done

example : ¬True → False := by
  intro ft
  change True → False at ft
  apply ft
  triv
  done

example : False → ¬True := by
  intro f
  exfalso
  exact f
  done

example : ¬False → True := by
  intro nf
  triv
  done

example : True → ¬False := by
  --change改写时直接改写目标
  intro t
  change False → False
  intro f
  exfalso
  exact f
  done

example : False → ¬P := by
  intro f
  exfalso
  exact f
  done

example : P → ¬P → False := by
  intro hp np
  exact np hp
  done

example : P → ¬¬P := by
  -- 注意逻辑上的矛盾
  intro hp
  -- 注意change的使用
  change ¬P → False
  -- 直接用¬P → False替换¬¬P
  intro np
  exact np hp
  done

example : (P → Q) → ¬Q → ¬P := by
  intro pq nq p
  apply pq at p
  exact nq p
  done

example : ¬¬False → False := by
  intro nnf
  by_contra nf
  exact nnf nf
  done

example : ¬¬P → P := by
  -- 反证法
  intro nnp
  by_contra np
  exact nnp np
  done

example : (¬Q → ¬P) → P → Q := by
  intro nqnp hp
  by_cases h:Q
  -- 假设Q为真
  · exact h
  -- 假设Q为假
  · apply nqnp at h
    -- nqnp假设更新为¬P
    -- 当前目标依然是 Q。
    -- Lean 并不会自动推断出可以利用矛盾 h : ¬P 和 hp : P 来完成证明，除非你明确指出这一点。
    -- exfalso 的作用：让目标从 Q 转变为 False。注意exalso的用途
    exfalso
    exact h hp
  done
