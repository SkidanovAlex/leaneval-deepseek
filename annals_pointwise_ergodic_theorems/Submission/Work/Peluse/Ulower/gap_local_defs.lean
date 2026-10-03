/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.

# Vocabulary of the gap-regime localisation (`gap_local_block`)

This module fixes the two auxiliary objects on which the localisation of the gap-regime box-norm
hypothesis to a *balanced* block is phrased.

## The mathematical content

`F = iterDelta (s-2) sh (dualFn N P f₀ f₁)` is the function whose level-two box norm over the big
box is the hypothesis of the gap regime.  Windowing `f₀, f₁` to `symIcc Ns` around a point `a` and
looking at the localised dual function `G_a = dualFn N P (gapLocalise f₀ a Ns) (gapLocalise f₁ a Ns)`
gives, on the *interior* of the window, exactly the translate `G (· + a)` of the original dual
function: the auxiliary condition on the localised coordinate `w` is that all the values
`w - P y`, `w + y - P y` (`y ∈ [1,N]`) lie in `symIcc Ns`, and a sufficient condition (used here,
because it is an interval of a computable size) is `w ∈ symIcc (Ns - (polySup P N + N))`
(`gapGoodSet`).

The second object is the *reach* of the iterated difference: `iterDelta k sh F (w)` is a product of
values of `F` at the points `w + ζ`, `ζ ∈ reach k sh`; hence `iterDelta k sh` commutes with the
translation by `a` as soon as all those points lie in the interior.

## Contents

* `Work.Peluse.Ulower.reach` — the finite set of shifts read by `iterDelta k sh`;
* `Work.Peluse.Ulower.gapGoodSet` — the interior of the window `symIcc Ns` at which the localised
  dual function is the translate of the original one.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.gap_defs

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- **The reach of the iterated difference.**  `iterDelta k sh F (w)` is a product of values of `F`
at the points `w + ζ` with `ζ ∈ reach k sh`, and conversely every `ζ ∈ reach k sh` occurs as the
argument of some factor.  Recursively: the reach of `iterDelta 0` is `{0}`, and the reach of
`iterDelta (k+1) sh` is the reach of `iterDelta k (sh ∘ succ)` shifted by the two entries of `sh 0`,
because

`iterDelta (k+1) sh F w = iterDelta k sh' F (w + (sh 0).1) · conj (iterDelta k sh' F (w + (sh 0).2))`.

The arguments of the iterated difference distinguish `(h₁,h₁')` from `(h₂,h₂')` in exactly one
coordinate (that is the point of the "reach" terminology): the factor count is `2 ^ k`, but the
number of distinct shift *values* is at most `(k+1) ^ k` because a shift entry of the `i`-th level
can only be `(sh i).1` or `(sh i).2`. -/
def reach : (k : ℕ) → (Fin k → ℤ × ℤ) → Finset ℤ
  | 0, _ => {0}
  | (k + 1), sh =>
      ((reach k (fun i => sh i.succ)).image (fun ζ => ζ + (sh 0).1)) ∪
      ((reach k (fun i => sh i.succ)).image (fun ζ => ζ + (sh 0).2))

/-- **The interior of the localisation window.**  The set of localised coordinates `w` at which the
windowed dual function `dualFn N P (gapLocalise f₀ a Ns) (gapLocalise f₁ a Ns)` agrees with the
translate `dualFn N P f₀ f₁ (· + a)` of the original one: for `w ∈ symIcc (Ns - (polySup P N + N))`
every argument `w - P y`, `w + y - P y` (`1 ≤ y ≤ N`) has modulus at most `Ns`, so the truncation
indicators of `gapLocalise` are inactive.

The set is an interval of cardinality `2 (Ns - (polySup P N + N)) + 1`, so it is nonempty and of
comparable size to `symIcc Ns` as soon as `Ns` is at least a constant multiple of `polySup P N + N`
(which is `O(N ^ P.natDegree)`). -/
def gapGoodSet (P : Polynomial ℤ) (N Ns : ℕ) : Finset ℤ :=
  symIcc (Ns - (polySup P N + N))

end

end Work.Peluse.Ulower
