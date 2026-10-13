/-
Copyright: work module for the Elgindi finite-time singularity project.

# A Leibniz + Cauchy–Schwarz bound for the angular operator `D_θ`

`Work.Elliptic.Dth1 f = sin(2θ) · f'` is (definitionally) the derivation
`Work.Spaces.Lop` acting on functions of `θ` alone, so its `m`-th iterate is
Leibniz:

  `Dth1Iter m (F·G) = ∑_{j ≤ m} C(m,j) · (Dth1Iter j F · Dth1Iter (m-j) G)`.

Applying Cauchy–Schwarz to the `m+1` terms then gives the pointwise estimate

  `(Dth1Iter m (F·G) θ)² ≤ (m+1) · ∑_{j ≤ m} C(m,j)² · ((Dth1Iter j F θ)² · (Dth1Iter (m-j) G θ)²)`

on the interval `(-1, π/2+1)` on which a `SmoothSlice` is smooth.

The Leibniz identity is the one-dimensional (`θ`-slice) instance of
`Work.Spaces.Lop_iter_mul_eqOn`, reused verbatim; the rest is Cauchy–Schwarz
(`sq_sum_le_card_mul_sum_sq`).
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- `Work.Elliptic.Dth1Iter` is the `n`-fold iterate of the derivation
`Work.Spaces.Lop` — the two operators are the same function `θ ↦ sin(2θ)·f'(θ)`. -/
private lemma Dth1Iter_eq_Lop_iter (n : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter n f = Work.Spaces.Lop^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Elliptic.Dth1Iter_succ, Function.iterate_succ_apply', ih]
      rfl

/-- The iterated Leibniz rule for `Work.Elliptic.Dth1Iter` at a point of the
smoothness interval: the `m`-th iterate applied to a pointwise product expands
into the binomial convolution. -/
private lemma Dth1Iter_mul_eq (m : ℕ) {F G : ℝ → ℝ} (hF : Work.Elliptic.SmoothSlice F)
    (hG : Work.Elliptic.SmoothSlice G) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    Work.Elliptic.Dth1Iter m (fun θ => F θ * G θ) θ =
      ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) *
          (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ) := by
  have hleib := Work.Spaces.Lop_iter_mul_eqOn F G (Set.Ioo (-1) (Real.pi / 2 + 1))
    isOpen_Ioo hF hG m hθ
  rw [Dth1Iter_eq_Lop_iter]
  refine hleib.trans ?_
  apply Finset.sum_congr rfl
  intro j _
  rw [← Dth1Iter_eq_Lop_iter j F, ← Dth1Iter_eq_Lop_iter (m - j) G]

/-- Pointwise `L²`-type bound for the iterate of `D_θ` on a product: the square of
`Dth1Iter m (F·G)` at `θ` is controlled by the Cauchy–Schwarz sum of the squares of
the Leibniz terms. -/
theorem Dth1Iter_mul_sq_le (m : ℕ) {F G : ℝ → ℝ}
    (hF : Work.Elliptic.SmoothSlice F) (hG : Work.Elliptic.SmoothSlice G)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    (Work.Elliptic.Dth1Iter m (fun θ => F θ * G θ) θ) ^ 2
      ≤ (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1),
          ((m.choose j : ℝ)) ^ 2 * ((Work.Elliptic.Dth1Iter j F θ) ^ 2
            * (Work.Elliptic.Dth1Iter (m - j) G θ) ^ 2) := by
  rw [Dth1Iter_mul_eq m hF hG hθ]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1))
    (f := fun j => (m.choose j : ℝ) *
      (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ))
  have hcard : (((Finset.range (m + 1)).card : ℕ) : ℝ) = (m + 1 : ℝ) := by
    rw [Finset.card_range]
    norm_num
  calc (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
          (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ)) ^ 2
      ≤ (((Finset.range (m + 1)).card : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) *
            (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ)) ^ 2 := hcs
    _ = (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) *
            (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ)) ^ 2 := by
          rw [hcard]
    _ = (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
            ((Work.Elliptic.Dth1Iter j F θ) ^ 2
              * (Work.Elliptic.Dth1Iter (m - j) G θ) ^ 2) := by
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring

end Work.FTS.EllipticEst.TT
