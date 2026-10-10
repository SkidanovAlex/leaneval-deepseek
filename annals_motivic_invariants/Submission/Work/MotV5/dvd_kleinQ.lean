import Mathlib
import Submission.Work.MotV5.WtDefs
import Submission.Work.MotV5.dvd_roots
import Submission.Work.MotV5.kleinP_shift
import Submission.Work.MotV5.eval_kleinQPoly
import Submission.Work.MotV5.asPolyF_root
import Submission.Work.MotV5.w_add_injective

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `dvd_kleinQ`: the Klein polynomial of an AS-twisted point

Let `F` be a field of characteristic `5`, `L` an `F`-algebra, `w ∈ L` with `w⁵ - w = g` (`g ∈ F`),
and `y : Fin 5 → F`.  Put `xᵢ = Σ_j y_j (w + i)^j`, i.e. `x = asCoord w y` is the tuple of Galois
coordinates (`σ : w ↦ w + 1`) of the polynomial `P = polyOf y` evaluated at the five roots
`w, w+1, …, w+4` of `T⁵ - T - g`.

The lemma says that if `x` lies on the Klein curve (`kleinP a b x k = 0` for all `k`), then
`T⁵ - T - g` divides the Klein polynomial `kleinQPoly a b P` of `P` over `F`.

The mathematical content: `kleinQPoly a b P` evaluated at `w + i` is `kleinP0` of the `i`-th cyclic
shift of `x`, and the Klein quadrics are permuted by the cyclic shift (`kleinP0` of the shift of `x`
by `i` is `kleinP (3i) x` in the index arithmetic of `Fin 5`), so `kleinQPoly a b P` vanishes at all
five distinct roots `w + i` of `T⁵ - T - g`; as `T⁵ - T - g` is monic of degree `5` and
`kleinQPoly a b P` has coefficients in `F`, the divisibility descends from `L[T]` to `F[T]`.
-/

set_option autoImplicit false

namespace Work.MotV5

open Polynomial

/-- The Artin–Schreier polynomial `T⁵ - T - g` is monic of degree five. -/
theorem asPolyF_natDegree {F : Type*} [CommRing F] [Nontrivial F] (g : F) :
    (asPolyF g).natDegree = 5 := by
  rw [asPolyF]
  compute_degree!

/-- The Klein polynomial commutes with the extension of scalars `F → L`. -/
theorem map_kleinQPoly {F L : Type*} [Field F] [Field L] [Algebra F L] (a b : F)
    (y : Fin 5 → F) :
    ((kleinQPoly a b (polyOf y)).map (algebraMap F L)) =
      kleinQPoly (algebraMap F L a) (algebraMap F L b)
        (polyOf (fun j => algebraMap F L (y j))) := by
  simp only [kleinQPoly, polyOf, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_neg, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_sum, Polynomial.map_X,
    Polynomial.map_comp, map_ofNat]
  norm_num

/-- **The root computation.**  If the AS Galois coordinates `xᵢ = P(w + i)` of `P = polyOf y` lie on
the Klein curve, then `kleinQPoly a b P` vanishes at `w + i` for every `i : Fin 5`.

Indeed `kleinQPoly a b P` evaluated at `w + i` is `kleinP0` of the cyclic shift of `x` by `i`, which
is `kleinP (3 * i) x` — one of the vanishing Pfaffians. -/
theorem eval_kleinQPoly_at_root {F L : Type*} [Field F] [Field L] [Algebra F L] [CharP F 5]
    (w : L) (a b : F) (y : Fin 5 → F)
    (heq : ∀ k, Work.MotK.kleinP (algebraMap F L a) (algebraMap F L b)
      (Work.MotV.asCoord w (fun j => algebraMap F L (y j))) k = 0) (i : Fin 5) :
    ((kleinQPoly a b (polyOf y)).map (algebraMap F L)).eval (w + ((i:ℕ):L)) = 0 := by
  haveI : CharP L 5 := charP_of_injective_algebraMap (algebraMap F L).injective 5
  -- `P` evaluated at `w + n` only depends on `n` mod `5`, and gives the Galois coordinate.
  have hPc : ∀ n : ℕ, (polyOf (fun j => algebraMap F L (y j))).eval (w + (n : L)) =
      Work.MotV.asCoord w (fun j => algebraMap F L (y j))
        ⟨n % 5, Nat.mod_lt n (by norm_num)⟩ := by
    intro n
    have hcast : ((n : ℕ) : L) = ((n % 5 : ℕ) : L) := by
      nth_rewrite 1 [← Nat.div_add_mod n 5]
      rw [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero L 5, zero_mul, zero_add]
    simp only [polyOf, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Work.MotV.asCoord]
    rw [hcast]
  rw [map_kleinQPoly]
  rw [eval_kleinQPoly]
  rw [show (fun j : Fin 5 => (polyOf (fun j => algebraMap F L (y j))).eval
        ((w + (i:ℕ)) + (j:ℕ))) =
      (fun j : Fin 5 => Work.MotV.asCoord w (fun j => algebraMap F L (y j)) (i + j)) from by
    funext j
    rw [show ((w + (i:ℕ)) + (j:ℕ) : L) = (w + (((i:ℕ) + (j:ℕ) : ℕ) : L)) by push_cast; ring]
    rw [hPc]
    rfl]
  rw [kleinP_shift]
  exact heq ((3 : Fin 5) * i)

theorem dvd_kleinQ {F L : Type*} [Field F] [Field L] [Algebra F L] [CharP F 5]
    (w : L) (g : F) (hw : w ^ 5 - w = algebraMap F L g) (a b : F) (y : Fin 5 → F)
    (heq : ∀ k, Work.MotK.kleinP (algebraMap F L a) (algebraMap F L b)
      (Work.MotV.asCoord w (fun j => algebraMap F L (y j))) k = 0) :
    asPolyF g ∣ kleinQPoly a b (polyOf y) := by
  refine dvd_roots (asPolyF g) (kleinQPoly a b (polyOf y)) w ?_ (asPolyF_natDegree g) ?_
    (w_add_injective (F := F) w) ?_
  · rw [asPolyF]
    monicity!
  · exact asPolyF_root w g hw
  · exact eval_kleinQPoly_at_root w a b y heq

end Work.MotV5
