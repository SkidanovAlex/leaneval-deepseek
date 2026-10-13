/-
# `Work.FTS.BSSwirl.vorticity_vorticity_eq` — the curl-curl identity on `ℝ³`

The vector identity

  `∇ × (∇ × Ψ) = ∇ (∇·Ψ) - ΔΨ`

for a smooth field `Ψ : ℝ³ → ℝ³`, in the exact form in which the `BSSwirl` area needs it
(item 7a of `FTS_PHYS_BRIDGE.md` §1, the weak form of the Biot–Savart law
`∇ × (BS ω) = ω`).  Here `∇ ×` is `FiniteTimeSingularity.vorticity`, `∇·` is
`FiniteTimeSingularity.div = trace (fderiv ℝ ·)`, `∇` is Mathlib's `gradient` and `Δ` is
Mathlib's `Laplacian.laplacian = ∑ᵢ ∂ᵢ∂ᵢ`.

## The proof

Write `B := fderiv ℝ (fderiv ℝ Ψ) x : ℝ³ →L[ℝ] ℝ³ →L[ℝ] ℝ³`, the (symmetric, by Clairaut)
second derivative of `Ψ` at `x`.  The three calculus inputs are

* `fderiv ℝ (∇ × Ψ) x v = ∑ i, e_i × (B v e_i)`  (`VortVV.fderiv_vorticity_apply`),
* `fderiv ℝ (∇·Ψ) x v = trace (B v)`  (`VortVV.fderiv_div_apply`),
* `Δ Ψ x = ∑ i, B e_i e_i`  (`VortVV.laplacian_apply_e`),

and one algebraic input, the BAC–CAB computation

* `∑ i, e_i × (∑ j, e_j × B e_i e_j)
     = (∑ k, (∑ i, ⟪e_i, B e_k e_i⟫) • e_k) - ∑ k, B e_k e_k`
  (`VortVV.curl_curl_algebra`), which uses the symmetry of `B` exactly once, in the
  identification of `∑ i (B e_i e_k)_i` with `∑ i (B e_k e_i)_i`.

Combining them gives the identity.  (The two remaining elementary inputs, the standard basis
expansion `w = ∑ i, ⟪e i, w⟫ • e i` and the trace formula `tr L = ∑ i, ⟪e i, L (e i)⟫`, are
proved here.)
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Trace
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.CrossAux
import Submission.Work.FTS.BSSwirl.VortVV.curl_curl_algebra
import Submission.Work.FTS.BSSwirl.VortVV.fderiv_vorticity_apply
import Submission.Work.FTS.BSSwirl.VortVV.fderiv_div_apply
import Submission.Work.FTS.BSSwirl.VortVV.laplacian_apply_e

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## Elementary identifications in the standard basis -/

/-- The standard basis vector `e i` of `ChallengeDeps` is the `i`-th vector of Mathlib's
standard orthonormal basis of `ℝ³`.  (Private: `Work.FTS.BSSwirl.laplacian_radial` already
contains a lemma of this name and statement, and the two modules must be importable together.) -/
private lemma basisFun_eq_e (i : Fin 3) : EuclideanSpace.basisFun (Fin 3) ℝ i = e i := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

/-- **The standard basis expansion of a vector of `ℝ³`**: `w = ∑ i, ⟪e i, w⟫ • e i`. -/
private lemma sum_inner_smul_e_eq (w : R3) : ∑ i : Fin 3, inner ℝ (e i) w • e i = w := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  simpa [OrthonormalBasis.repr_apply_apply, FiniteTimeSingularity.e] using h

/-- **The trace in the standard basis**: `tr L = ∑ i, ⟪e i, L (e i)⟫`. -/
private lemma trace_eq_sum_inner_e (L : R3 →L[ℝ] R3) :
    L.trace ℝ R3 = ∑ i : Fin 3, inner ℝ (e i) (L (e i)) := by
  rw [show L.trace ℝ R3 = ((L : R3 →ₗ[ℝ] R3)).trace ℝ R3 from rfl,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basisFun_eq_e]
  rfl

/-- **The gradient in the standard basis**: `∇f x = ∑ k, ∂ₖf(x) • e k`.  (A vector `w` equals
`∑ k, ⟪e k, w⟫ • e k`, and `⟪e k, ∇f x⟫ = ∂ₖf(x)`.) -/
private lemma gradient_eq_sum_e (f : R3 → ℝ) (x : R3) :
    gradient f x = ∑ k : Fin 3, fderiv ℝ f x (e k) • e k := by
  conv_lhs => rw [← sum_inner_smul_e_eq (gradient f x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_gradient_right]
  simp

/-! ## The curl-curl identity -/

theorem vorticity_vorticity_eq {Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (x : Work.FTS.BSSwirl.R3) :
    FiniteTimeSingularity.vorticity (FiniteTimeSingularity.vorticity Ψ) x
      = gradient (FiniteTimeSingularity.div Ψ) x - Laplacian.laplacian Ψ x := by
  -- the second derivative of `Ψ` at `x` is symmetric (Clairaut)
  have hsymm : ∀ u v : R3, fderiv ℝ (fderiv ℝ Ψ) x u v = fderiv ℝ (fderiv ℝ Ψ) x v u := by
    have h : ContDiffAt ℝ 2 Ψ x := (hΨ 2).contDiffAt
    exact h.isSymmSndFDerivAt (by simp)
  -- the left-hand side, in the standard basis
  have hcurl : vorticity (vorticity Ψ) x
      = ∑ i : Fin 3, crossR3 (e i)
          (∑ j : Fin 3, crossR3 (e j) (fderiv ℝ (fderiv ℝ Ψ) x (e i) (e j))) := by
    rw [vorticity_eq_sum_crossR3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [VortVV.fderiv_vorticity_apply Ψ hΨ x (e i)]
  -- the gradient of the divergence, in the standard basis
  have hgrad : gradient (div Ψ) x
      = ∑ k : Fin 3,
          (∑ i : Fin 3, inner ℝ (e i) (fderiv ℝ (fderiv ℝ Ψ) x (e k) (e i))) • e k := by
    rw [gradient_eq_sum_e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [VortVV.fderiv_div_apply Ψ hΨ x (e k), trace_eq_sum_inner_e]
  -- the Laplacian, in the standard basis
  have hlap : Laplacian.laplacian Ψ x
      = ∑ k : Fin 3, fderiv ℝ (fderiv ℝ Ψ) x (e k) (e k) := VortVV.laplacian_apply_e Ψ x
  rw [hcurl, hgrad, hlap, VortVV.curl_curl_algebra (fderiv ℝ (fderiv ℝ Ψ) x) hsymm]

end

end Work.FTS.BSSwirl
