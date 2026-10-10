import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AsTwCoord
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `asCoord_asTwCoord`: the interpolation identity of the AS-twisted Klein coordinates

Let `W = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (asRoot g)` be a root of `Z⁵ - Z - g` and let
`x i = kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0` be the Klein coordinates of the Klein
point, normalised at the zeroth coordinate.  By definition (`Work.MotC5N3.asTwCoord`) the
Artin–Schreier twisted coordinates `y_j` are the coefficients of the Lagrange interpolation
polynomial through the Galois conjugate nodes `W + i`:

  `y_j = -∑_i x_i ((W + i)^{4-j} - δ_{j,0})`   (`δ` being `if j = 0 then 1 else 0`).

The present lemma is exactly the statement that this polynomial interpolates the values
`x k` at the nodes `W + k`:

  `asCoord W y k = ∑_j y_j (W + k)^j = x k`.

The reason: put `S(i,k) = ∑_j (W+i)^{4-j} (W+k)^j` (`j` ranging over `Fin 5`).  Then

* `S(k,k) = 5 (W+k)^4 = 0`, and
* for `i ≠ k` the telescoping identity `geom_sum₂_mul` gives
  `(W+i)^5 - (W+k)^5 = S(i,k) · ((W+i) - (W+k))`;  in characteristic `5` the Frobenius gives
  `(W+i)^5 = W^5 + i^5` and the elements `0,…,4 ∈ R` are fixed by `z ↦ z^5`, so the left hand
  side is `i - k ≠ 0`; cancelling gives `S(i,k) = 1`.

Consequently `S(i,k) - 1` is `-1` for `i = k` and `0` otherwise, and expanding the defining
sum gives `∑_j y_j (W+k)^j = -∑_i x_i (S(i,k) - 1) = x k`.

Note that nothing beyond characteristic-`5` algebra is used: neither the specific value of
`g` (the relation `W^5 - W = g` is not needed, only `(W+i)^5 = W^5 + i^5`), nor any property
of the Klein data `D` — the lemma is unconditional in `D`.

Formally, the identity is the expansion of the two `Fin 5` sums followed by `ring_nf` in
characteristic `5`; the numeral reductions modulo `5` are performed by `reduce_mod_char!`,
which needs the `CharP` instance to be a *local* hypothesis — whence the general auxiliary
lemma `Work.MotC5N3.asInterp` below, stated over an abstract field `R` of characteristic `5`.
-/

set_option autoImplicit false
-- `haveI` is exactly what is wanted here: `CharP (Work.MotC5N3.OmA K D) 5` must be an *instance* for the
-- instance-implicit argument of `asInterp`, and for the local search of `reduce_mod_char!`.
set_option linter.style.haveILetI false

namespace Work.MotC5N3
open Work.MotV5
noncomputable section

/-! ## The interpolation identity in characteristic `5` -/

/-- **Lagrange interpolation at the five nodes `w, w+1, …, w+4` in characteristic `5`.**

For any field `R` of characteristic `5`, any `w : R` and any `x : Fin 5 → R`, the numbers
`y_j = -∑_i x_i ((w+i)^{4-j} - δ_{j,0})` interpolate `x` at the nodes `w + k`:
`∑_j y_j (w+k)^j = x k`.

(For `R = Work.MotC5N3.OmA K D` and `x i = kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0` this is exactly
`Work.MotV5.asCoord_asTwCoord`, since `asTwCoord` is `y` by definition.) -/
theorem asInterp {R : Type*} [Field R] [CharP R 5] (w : R) (x : Fin 5 → R) (k : Fin 5) :
    (∑ j : Fin 5, (-∑ i : Fin 5,
        x i * ((w + ((i : ℕ) : R)) ^ (4 - (j : ℕ)) - (if (j : ℕ) = 0 then 1 else 0)))
      * (w + ((k : ℕ) : R)) ^ (j : ℕ)) = x k := by
  fin_cases k <;> simp [Fin.sum_univ_five] <;> ring_nf <;> reduce_mod_char! <;>
    ring_nf <;> reduce_mod_char!

/-! ## The characteristic of the Klein function field -/

/-- The function field `Work.MotC5N3.OmA K D = K(C)` of the Klein curve over `K = Work.MotC5N3.KbA K = 𝕜(t)‾` has
characteristic `5` whenever `𝕜` does.  (The `CharP` instance of `Work.MotC5N3.OmA K D` is not found by
typeclass search, because `Work.MotC5N3.OmA K D` is a `FractionRing` of a quotient of a polynomial ring over
`Work.MotC5N3.KbA K`; here it is deduced from the injectivity of the structure map of the `Work.MotC5N3.KbA K`-algebra
`Work.MotC5N3.OmA K D`.) -/
theorem charP_Om (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5] (D : Work.MotV.KleinData 𝕜) :
    CharP (Work.MotC5N3.OmA K D) 5 :=
  charP_of_injective_algebraMap (R := Work.MotC5N3.KbA K) (A := Work.MotC5N3.OmA K D)
    (fun (a b : Work.MotC5N3.KbA K) hab => by
      by_contra h
      have hne : a - b ≠ 0 := sub_ne_zero.mpr h
      have hz : algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (a - b) = 0 := by
        rw [map_sub, hab, sub_self]
      have h1 : (1 : Work.MotC5N3.OmA K D) = 0 := by
        have h2 := congrArg (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D))
          (mul_inv_cancel₀ hne)
        rw [map_mul, map_one, hz, zero_mul] at h2
        exact h2.symm
      exact one_ne_zero h1) 5

/-! ## The requested lemma -/

theorem asCoord_asTwCoord (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5] (D : Work.MotV.KleinData 𝕜)
    (g : K) (i : Fin 5) :
    Work.MotV.asCoord (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g))
        (Work.MotC5N3.asTwCoord D g) i
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
  haveI : CharP (Work.MotC5N3.OmA K D) 5 := charP_Om 𝕜 D
  have h := asInterp (R := Work.MotC5N3.OmA K D)
    (w := algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g))
    (x := fun i => Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
      / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) i
  simpa [Work.MotV.asCoord, Work.MotC5N3.asTwCoord] using h

end

end Work.MotC5N3