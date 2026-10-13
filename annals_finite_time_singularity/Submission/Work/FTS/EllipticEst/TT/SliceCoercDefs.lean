/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slicewise vocabulary for the angular coercivity `slice_coercive`

This module fixes the one-dimensional (`θ`-slice) vocabulary of the proof of

`Work.FTS.EllipticEst.TT.slice_coercive`,

the statement that the angular functional `Ptheta α m u` is dominated by the same functional
applied to `∂_θθu` and to `Lzero1 u`.

The proof route is *triangular* in the number of angular derivatives:

* `Hη u ≤ C Gη u` (the `i = 0` term is bounded by the second derivative alone, through
  Newton–Leibniz on `Iθ`);
* `Gγ α 1 u ≤ C (Gη u + Fη u)` (the first angular derivative, through the self-pairing identity
  `∫ Lzero1 u · u = ∫ (u')² + (1/2)∫ (u/cos θ)² - 6∫ u²`);
* `Gγ α i u ≤ K i (Gη u + Σ_{k ≤ i-2} Gγ α k (D2 u) + Σ_{k ≤ i-1} Gγ α k u)` for `i ≥ 2`
  (the identity `D_θ(D_θ u) = sin(2θ)²·u'' + 2cos(2θ)·D_θ u` plus the Leibniz rule of the
  derivation `D_θ`).

Assembling the triangle gives the theorem, since every quantity on the right hand side is a
summand of `Ptheta α m (∂_θθu)` or of `Ptheta α m (Lzero1 u)`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- `D2 u = u''`, the second derivative of the one-variable function `u`.  It is definitionally
the function whose `Ptheta` is the second summand of the statement of `slice_coercive`. -/
def D2 (u : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (fun t => deriv u t) θ

/-- `Gη u = ∫_θ (u'')² sin(2θ)^{-η}`, the `η`-weighted energy of the second derivative. -/
def Gη (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (D2 u θ) ^ 2 * sEta θ

/-- `Fη u = ∫_θ (Lzero1 u)² sin(2θ)^{-η}`, the `η`-weighted energy of `Lzero1 u`. -/
def Fη (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Lzero1 u θ) ^ 2 * sEta θ

/-- `Gγ α i u = ∫_θ (D_θ^i u)² sin(2θ)^{-γ}`, the `i`-th `γ`-weighted energy. -/
def Gγ (α : ℝ) (i : ℕ) (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter i u θ) ^ 2 * sGam α θ

/-- `Hη u = ∫_θ u² sin(2θ)^{-η}`, the `η`-weighted `L²` energy (the `i = 0` term of `Ptheta`). -/
def Hη (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * sEta θ

/-- `D2` is `Work.Elliptic.d2`. -/
theorem D2_eq_d2 (u : ℝ → ℝ) : D2 u = Work.Elliptic.d2 u := rfl

/-- `Ptheta` is the sum of its `i = 0` (`Hη`) and `i ≥ 1` (`Gγ`) pieces. -/
theorem Ptheta_eq (α : ℝ) (m : ℕ) (u : ℝ → ℝ) :
    Ptheta α m u = Hη u + ∑ i ∈ Finset.Icc 1 m, Gγ α i u := rfl

/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) > 0` on `(0, π/2)`. -/
theorem sin_two_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- `sEta θ ≥ 0` on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _

/-- `sGam α θ ≥ 0` on `Iθ`. -/
theorem sGam_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sGam α θ :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _

end Work.FTS.EllipticEst.TT
