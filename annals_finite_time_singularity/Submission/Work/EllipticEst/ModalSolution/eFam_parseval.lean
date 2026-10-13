/-
# `ModalSolution/eFam_parseval`: Parseval's identity for the angular Gegenbauer modes

`eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)` are the Dirichlet eigenfunctions of
`Work.Elliptic.Lzero` on `(0, π/2)` (`FTS/PhiStar/Gegenbauer/Defs.lean`), orthogonal for the
self-adjoint weight `cos θ dθ` (`eFam_orthogonal`) with norms
`∫_{Iθ} eFam m θ ^ 2 cos θ = ((2m+2)(2m+3))/(4m+5)` (`eFam_norm_fts`), and complete
(`eFam_complete`).  This file proves the corresponding Parseval identity: for an
a.e.-strongly-measurable slice `θ ↦ F z θ` with `∫_{Iθ} (F z)² cos θ < ∞`,

  `∑_{m ≤ N} (cmode m F z)² · ∫_{Iθ} eFam m θ ^ 2 cos θ  →  ∫_{Iθ} (F z)² cos θ`,

where `cmode m F z = ⟨F z, eFam m⟩_{cos θ dθ} / ‖eFam m‖²` is the `m`-th modal coefficient
(`FTS/PhiStar/Series/Defs.lean`) — the standard Hilbert-basis expansion in
`L²(Iθ, cos θ dθ) = L²(angMeasure)`.

## The proof

`eFamParsevalDefs.lean` realises `L²(Iθ, cos θ dθ)` as `Lp ℝ 2 angMeasure` and provides the
mode classes `eFamLp m`, the normalised classes `eFamE m = (√(eFamD m))⁻¹ • eFamLp m`
(`eFamD m = ∫_{Iθ} eM m² cos θ`, `eFamD_pos`), and the inner-product computations
`inner_toLp_eFamE`, `inner_eFamE_toLp`, `inner_toLp_toLp`.

* `eFamE_orthonormal_aux` makes `eFamE` an orthonormal family, and
  `eFamE_span_orthogonal_eq_bot_aux` makes it total — the `Lp` form of `eFam_complete`.  (Both
  are in `eFamParsevalAux.lean`; the same statements are also delivered by colleagues without
  the `_aux` suffix, under `eFamE_orthonormal`, `eFamE_span_orthogonal_eq_bot`.)  Hence
  `HilbertBasis.mkOfOrthogonalEqBot` produces a Hilbert basis and
  `HilbertBasis.hasSum_inner_mul_inner` gives, for `x = MemLp.toLp f hfm`,

    `HasSum (fun m => ⟪x, eFamE m⟫ · ⟪eFamE m, x⟫) ⟪x, x⟫`.

* Expanding the inner products reduces the `m`-th summand to `(cmode m F z)² · eFamD m`
  (`cmode_eq_setIntegral_aux` converts `cmode`'s interval integral into the set integral over
  `Iθ`), while `⟪x, x⟫ = ∫_{Iθ} (F z)² cos θ`.

* Finally `HasSum.tendsto_sum_nat`, composed with the shift `N ↦ N + 1`, turns the `HasSum`
  into the `Tendsto` of the partial sums `∑_{m < N+1}`.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigParsevalDefs
import Submission.Work.EllipticEst.ModalSolution.eFamBasisFts_FALSE
import Submission.Work.EllipticEst.ModalSolution.eFamParsevalDefs
import Submission.Work.EllipticEst.ModalSolution.eFamParsevalAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

local notation "Iθ" => Work.Spaces.Iθ
local notation "angMeasure" => Work.FTS.EllipticEst.LevelOneAsm.angMeasure

theorem eFam_parseval (F : ℝ → ℝ → ℝ) (z : ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
      Filter.atTop (nhds (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)) := by
  let f : ℝ → ℝ := fun θ => F z θ
  have hfm : MemLp f 2 angMeasure :=
    Work.FTS.EllipticEst.LevelOneAsm.memLp_of_hyps hmeas.aemeasurable hz
  have hb := HilbertBasis.hasSum_inner_mul_inner
    (HilbertBasis.mkOfOrthogonalEqBot (v := eFamE) eFamE_orthonormal_aux
      eFamE_span_orthogonal_eq_bot_aux)
    (MemLp.toLp f hfm) (MemLp.toLp f hfm)
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot] at hb
  -- the elementary arithmetic collapsing the two normalising square roots
  have harith : ∀ D A : ℝ, 0 < D →
      (Real.sqrt D)⁻¹ * A * ((Real.sqrt D)⁻¹ * A) = (A / D) ^ 2 * D := by
    intro D A hD
    have hsq : (Real.sqrt D)⁻¹ * (Real.sqrt D)⁻¹ = D⁻¹ := by
      rw [← mul_inv, ← sq, Real.sq_sqrt hD.le]
    rw [show (Real.sqrt D)⁻¹ * A * ((Real.sqrt D)⁻¹ * A)
          = ((Real.sqrt D)⁻¹ * (Real.sqrt D)⁻¹) * (A * A) from by ring, hsq]
    field_simp
  -- the `m`-th summand of the Hilbert-basis expansion is `(cmode m F z)² · eFamD m`
  have hterm : ∀ m : ℕ,
      inner ℝ (MemLp.toLp f hfm) (eFamE m) * inner ℝ (eFamE m) (MemLp.toLp f hfm)
        = (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * eFamD m := by
    intro m
    rw [inner_toLp_eFamE hfm m, inner_eFamE_toLp hfm m, cmode_eq_setIntegral_aux F z m]
    have hBA : (∫ θ in Iθ, eM m θ * f θ * Real.cos θ)
        = ∫ θ in Iθ, f θ * eM m θ * Real.cos θ :=
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hBA]
    exact harith (eFamD m) (∫ θ in Iθ, f θ * eM m θ * Real.cos θ) (eFamD_pos m)
  have hb' : HasSum (fun m => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * eFamD m)
      (∫ θ in Iθ, F z θ ^ 2 * Real.cos θ) := by
    have h1 := hb.congr_fun (fun m => (hterm m).symm)
    rw [Work.FTS.EllipticEst.LevelOneAsm.inner_toLp_toLp hfm hfm] at h1
    have hval : (∫ θ in Iθ, f θ * f θ * Real.cos θ)
        = ∫ θ in Iθ, F z θ ^ 2 * Real.cos θ := by
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      show f θ * f θ * Real.cos θ = F z θ ^ 2 * Real.cos θ
      rw [show f θ = F z θ from rfl]
      ring
    rwa [hval] at h1
  -- the partial sums are exactly those of the statement
  have htend := hb'.tendsto_sum_nat
  have hcomp := htend.comp (Filter.tendsto_add_atTop_nat 1)
  refine Tendsto.congr' ?_ hcomp
  refine Filter.Eventually.of_forall (fun N => ?_)
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [eFamD, eM]

end Work.EllipticEst.ModalSolution
