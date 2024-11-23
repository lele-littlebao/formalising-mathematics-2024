/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all of the tactics in Lean's maths library


/-!

# Logic in Lean, example sheet 1 : "implies" (`→`)

A *proposition* is a true-false statement, like `2+2=4` or `2+2=5`
or the Riemann hypothesis. In algebra we manipulate
numbers whilst not knowing what the numbers actually are; the trick is
that we call the numbers `x` and `y` and so on. In this sheet we
will learn how to manipulate propositions without saying what the
propositions are -- we'll just call them things like `P` and `Q`.

The purpose of these first few sheets is to teach you some very basic
*tactics*. In particular we will learn how to manipulate statements
such as "P implies Q", which is itself a true-false statement (e.g.
it is false when P is true and Q is false). In Lean we use the
notation `P → Q` for "P implies Q". You can get
this arrow by typing `\to` or `\r`. Mathematicians usually write the
implication arrow as 'P ⇒ Q'but Lean prefers a single arrow.
//

## The absolute basics

`P : Prop` means that `P` is a true-false statement. `h : P` means
that `h` is a proof that `P` is true. You can also regard `h` as the
hypothesis that `P` is true; logically these are the same. Stuff above
the `⊢` symbol is your assumptions. The statement to the right of it is
the goal. Your job is to prove the goal from the assumptions.

## Tactics you will need

To solve the levels on this sheet you will need to know how to use the
following three tactics:

* `intro`
--假设前提成立，现在在这个前提的基础上去证明结论(不管这个前提是什么)
* `exact`
--精确匹配目标
* `apply`
--应用假设
* `obtain`
--引入假设

You can read the descriptions of these tactics in Part C of the online course
notes here https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/tactics/tactics.html
In this course we'll be learning about 30 tactics in total; the goal of this
first logic section is to get you up to speed with ten very basic ones.

## Worked examples

Click around in the proofs to see the tactic state (on the right) change.
The tactic is implemented and the state changes just before the newline or semicolon (`;`).
I will use the following conventions: variables with capital
letters like `P`, `Q`, `R` denote propositions
(i.e. true/false statements) and variables whose names begin
with `h` like `h1` or `hP` are proofs or hypotheses.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)
--variable：声明全局变量
--prop：命题

-- Here are some examples of `intro`, `exact` and `apply` being used.
-- Assume that `P` and `Q` and `R` are all true. Deduce that `P` is true.
example (hP : P) (hQ : Q) (_ : R) : P := by
  -- note that `exact P` does *not* work. `P` is the proposition, `hP` is the proof.
  -- 假设p为真，则将这个假设命名为hp
  --p:=by 表示开始一个证明
  exact hP
  --exact tactic，用于精确匹配目标
  done

lemma a(hP : P) : P := by
  exact hP
  done

-- Same example: assume that `P` and `Q` and `R` are true, but this time
-- give the assumptions silly names. Deduce that `P` is true.
example (fish : P) (giraffe : Q) (dodecahedron : R) : P := by
-- `fish` is the name of the assumption that `P` is true (but `hP` is a better name)
  exact fish
-- fish 是假设的名称，可以随意命名
  done

-- Assume `Q` is true. Prove that `P → Q`.
example (hQ : Q) : P → Q := by
  -- The goal is of the form `X → Y` so we can use `intro`
  intro h
  -- now `h` is the hypothesis that `P` is true.
  -- Our goal is now the same as a hypothesis so we can use `exact`
  -- intro tactic，用于引入假设，每次引入最左边的假设
  exact hQ
  -- note `exact Q` doesn't work: `exact` takes the *term*, not the type.
  done

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q := by
  -- h : P → Q 表示假设h：P->Q
  -- `hP` says that `P` is true, and `h` says that `P` implies `Q`, so `apply h at hP` will change
  -- `hP` to a proof of `Q`.
  apply h at hP
  -- apply a at b 表示将假设a应用到目标b中;其中a必须是函数类型，b必须是一个已有的假设
  -- now `hP` is a proof of `Q` so that's exactly what we want.
  exact hP
  done

-- The `apply` tactic always needs a hypothesis of the form `P → Q`. But instead of applying
-- it to a hypothesis `h : P` (which changes the hypothesis to a proof of `Q`), you can instead
-- just use a bare `apply h` and it will apply it to the *goal*, changing it from `Q` to `P`.
-- Here we are "arguing backwards" -- if we know that P implies Q, then to prove Q it suffices to prove P.

-- Assume `P → Q` and `P` is true. Deduce `Q`.

example (h : P → Q) (hP : P) : Q :=by
  -- `h` says that `P` implies `Q`, so to prove `Q` (our goal) it suffices to prove `P`.
  apply h
  -- Our goal is now `⊢ P`.
    -- apply h 直接尝试将 h 应用到当前的证明目标，如果 h 的类型可以生成当前目标，则成功
  exact hP
  done
--


example (h : P → Q) (hP : P) : Q :=by
  obtain hQ := h hP
  -- obtain hQ := h hP 的意思是：使用 h hP 推导出 Q，并将结果命名为 hQ
  -- := 赋值
  exact hQ
  done
/-

## Examples for you to try

Delete the `sorry`s and replace them with tactic proofs using `intro`,
`exact` and `apply`, separating them with newlines or semicolons (`;`).

-/
/-- Every proposition implies itself. -/
example : P → P := by
  intro hP
  exact hP
  done

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`. If you think
about it, this means that to deduce `R` you will need to prove both `P`
and `Q`. In general to prove `P1 → P2 → P3 → ... Pn` you can assume
`P1`, `P2`,...,`P(n-1)` and then you have to prove `Pn`.

So the next level is asking you prove that `P → (Q → P)`.

-/
example : P → Q → P := by
  intro hP
  intro hQ
  exact hP
  done

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
This is called "Modus Ponens" by logicians. -/
example : P → (P → Q) → Q := by
  intro hp
  intro hpq
  exact hpq hp
  -- exact hpq hp 表示将 P → Q 的假设 hpq 应用到 P 的证明 hp 上，从而得到 Q 的证明。这是正确的顺序，
  --而 hp hpq 则是错误的顺序，因为 hp 不是一个函数。
  done

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
  so is `P → R`. -/
example : (P → Q) → (Q → R) → P → R := by
  sorry
  done

-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
-- two goals! Note that tactics operate on only the first goal.
example : (P → Q → R) → (P → Q) → P → R := by
  intros h1 h2 p    -- 引入三个假设
  apply h1          -- 应用第一个假设 h1: P → Q → R
  · exact p         -- 证明 P
  · apply h2        -- 应用第二个假设 h2: P → Q
    exact p         -- 证明 P
  done

/-

Here are some harder puzzles. They won't teach you anything new about
Lean, they're just trickier. If you're not into logic puzzles
and you feel like you understand `intro`, `exact` and `apply`
then you can just skip these and move onto the next sheet
in this section, where you'll learn some more tactics.

-/
variable (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro pr sq rt qr hs
  apply rt
  apply qr
  apply sq
  exact hs
  done

example : (P → Q) → ((P → Q) → P) → Q := by
  intro pq pqp
  apply pq
  apply pqp
  exact pq
  done

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro pqr qrp rpq
  apply qrp
  intro hq
  apply pqr
  intro hp
  exact hq
  done

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro qpp qr rp
  apply qpp
  intro hq
  apply rp
  apply qr
  exact hq
  done

example : (((P → Q) → Q) → Q) → P → Q := by
  intro pqqq hp
  apply pqqq
  intro hpq
  apply hpq
  exact hp
  done

example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  intro h1 h2 h3
  apply h1
  -- 现在需要证明 (P → Q → Q)
  · intro pqq pq
    apply pqq
    intro hq
    apply pq
    exact hp
  -- 现在需要证明 (P → Q)
  · exact pq
  -- 现在需要证明 (Q)
  · apply pq
    intro hp
    exact hp
  done
