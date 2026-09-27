import Mathlib
import Submission.Work.EKLC6Core.lpMeas_le_eqLocus_compMeasurePreserving
import Submission.Work.EKLC6Core.eqLocus_compMeasurePreserving_le_lpMeas
import Submission.Work.EKLC6Core.birkhoffAverage_compMeasurePreserving_toLp
import Submission.Work.EKLC6Core.norm_sq_eq_integral_sq_Lp

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

/-- **Mean ergodic theorem (von Neumann) in `L²`.**  For a measure preserving self-map `T` of a
finite measure space and `f ∈ L²(μ)`, the Cesàro (Birkhoff) averages of `f` along the orbits of `T`
converge to the conditional expectation of `f` on the `T`-invariant σ-algebra, in `L²(μ)` (phrased
through the `L²`-squared integral).

Proof sketch.  Let `U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` be the Koopman operator
`Lp.compMeasurePreserving T hmp` (Mathlib gives only an `AddMonoidHom`; upgrade it to a linear map
using `(c • g) ∘ T = c • (g ∘ T)` a.e. and `Lp.coeFn_compMeasurePreserving`, then to a
`ContinuousLinearMap` of norm `≤ 1` via `Lp.norm_compMeasurePreserving`).
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection U _ (hf.toLp f)` gives convergence
of the Birkhoff averages of `U` to `((U).eqLocus 1).orthogonalProjectionOnto (hf.toLp f)`, and
`MeasureTheory.condExpL2` *is by definition* the orthogonal projection onto
`MeasureTheory.lpMeas ℝ ℝ (invariants T) 2 μ`.  So it remains to identify, as submodules of
`Lp ℝ 2 μ`, `U.eqLocus 1 = lpMeas ℝ ℝ (invariants T) 2 μ`:
`⊇` an `(invariants T)`-measurable `h` satisfies `h ∘ T = h` pointwise (for Borel `B`,
`h ⁻¹' B ∈ invariants T`); `⊆` if `g ∘ T =ᵐ[μ] g` then `g` agrees a.e. with an
`(invariants T)`-measurable function (put `N := {x | g (T x) ≠ g x}`,
`N' := ⋃ n, (T^[n]) ⁻¹' N`, `C := N'ᶜ`, `D := ⋂ n, (T^[n]) ⁻¹' C`: then `T ⁻¹' D = D` as
`T ⁻¹' C ⊇ C`, and `g · 1_D` works).
Finally `birkhoffAverage ℝ U id n (hf.toLp f) = MemLp.toLp (birkhoffAverage ℝ T f n) _` and
`‖h‖²_{L²} = ∫ h²` (`Lp.norm_def`). -/
theorem tendsto_birkhoffAverage_condExp {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (T : X → X) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : MeasureTheory.MemLp f 2 μ) :
    Filter.Tendsto (fun n : ℕ => ∫ x, (birkhoffAverage ℝ T f n x
        - MeasureTheory.condExp (MeasurableSpace.invariants T) μ f x)^2 ∂μ)
      Filter.atTop (nhds (0 : ℝ)) := by
  have hmle : MeasurableSpace.invariants T ≤ ‹MeasurableSpace X› :=
    MeasurableSpace.invariants_le T
  have : Fact (MeasurableSpace.invariants T ≤ ‹MeasurableSpace X›) := ⟨hmle⟩
  -- The Koopman operator of `T`, as a continuous linear map of norm `≤ 1`.
  let U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hmp).toContinuousLinearMap
  have hUcoe : ⇑U = ⇑(Lp.compMeasurePreserving T hmp) := rfl
  have hU1 : ‖U‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound U zero_le_one fun x => ?_
    rw [hUcoe, one_mul]
    exact (Lp.norm_compMeasurePreserving x hmp).le
  let u : Lp ℝ 2 μ := MemLp.toLp f hf
  -- The fixed point set of `U` is exactly the space of `(invariants T)`-measurable `L²` functions.
  have hK : U.eqLocus 1 = lpMeas ℝ ℝ (MeasurableSpace.invariants T) 2 μ := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · have h1 : U g = g := by
        simpa using (LinearMap.mem_eqLocus).mp hg
      rw [hUcoe] at h1
      exact eqLocus_compMeasurePreserving_le_lpMeas μ T hmp g h1
    · have h1 : Lp.compMeasurePreserving T hmp g = g :=
        lpMeas_le_eqLocus_compMeasurePreserving μ T hmp g hg
      show g ∈ U.eqLocus 1
      rw [LinearMap.mem_eqLocus]
      show U g = (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) g
      rw [hUcoe]
      simpa using h1
  -- `U.eqLocus 1` is a closed subspace, hence has an orthogonal projection.
  have hker : (U - 1).ker = U.eqLocus 1 := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_eqLocus]
    exact sub_eq_zero
  have : IsClosed ((U.eqLocus 1 : Submodule ℝ (Lp ℝ 2 μ)) : Set (Lp ℝ 2 μ)) := by
    rw [← hker]
    exact (U - 1).isClosed_ker
  -- von Neumann's mean ergodic theorem for the Koopman operator.
  have hlim := U.tendsto_birkhoffAverage_orthogonalProjection hU1 u
  -- The projection onto the fixed point set is the conditional expectation.
  have hcond : ((U.eqLocus 1).orthogonalProjectionOnto u : Lp ℝ 2 μ)
      =ᵐ[μ] condExp (MeasurableSpace.invariants T) μ f := by
    have hstar : (U.eqLocus 1).starProjection u
        = (lpMeas ℝ ℝ (MeasurableSpace.invariants T) 2 μ).starProjection u := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := U.eqLocus 1) ?_ ?_
      · rw [hK]
        exact Submodule.starProjection_apply_mem _ u
      · intro w hw
        rw [hK] at hw
        exact Submodule.starProjection_inner_eq_zero u w hw
    have hL : ((U.eqLocus 1).orthogonalProjectionOnto u : Lp ℝ 2 μ)
        = (condExpL2 ℝ ℝ hmle u : Lp ℝ 2 μ) := by
      rw [Submodule.coe_orthogonalProjectionOnto_apply, hstar]
      rfl
    rw [hL]
    exact MemLp.condExpL2_ae_eq_condExp hmle hf
  -- The Birkhoff averages along the Koopman operator are the Birkhoff averages along `T`.
  have hbirk : ∀ n : ℕ, ((birkhoffAverage ℝ (⇑U) id n u : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] fun x => birkhoffAverage ℝ T f n x := by
    intro n
    simpa [hUcoe] using birkhoffAverage_compMeasurePreserving_toLp μ T hmp f hf n
  -- The Birkhoff averages converge to that projection.
  have hlimnorm : Tendsto (fun n => ‖birkhoffAverage ℝ (⇑U) id n u
      - ((U.eqLocus 1).orthogonalProjectionOnto u : Lp ℝ 2 μ)‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hlim
  have hlimsq : Tendsto (fun n => ‖birkhoffAverage ℝ (⇑U) id n u
      - ((U.eqLocus 1).orthogonalProjectionOnto u : Lp ℝ 2 μ)‖ ^ 2) atTop (𝓝 0) := by
    simpa using hlimnorm.pow 2
  refine hlimsq.congr' (Eventually.of_forall fun n => ?_)
  rw [norm_sq_eq_integral_sq_Lp μ]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (birkhoffAverage ℝ (⇑U) id n u)
      ((U.eqLocus 1).orthogonalProjectionOnto u : Lp ℝ 2 μ), hbirk n, hcond] with x hx1 hx2 hx3
  rw [hx1, Pi.sub_apply, hx2, hx3]

end

end Work.EKLC6Core
