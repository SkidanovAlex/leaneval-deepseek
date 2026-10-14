import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.OffPlanes.offPlanes_ibp
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_mixed_mul_le_4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Weyl identity for the curl of the Lamb vector `u × ω`

`Work.FTS.PressureOn.weakCurl.weyl_cross`: for a velocity field `u` and its vorticity `ω`
(at a fixed time `t`, with `ω` compactly supported, continuous, differentiable off the two
coordinate planes `x 0 = 0`, `x 2 = 0` and with locally integrable derivative) and for a smooth
compactly supported field `A`,

  `∫ ⟪u × ω, curl A⟫ = ∫ ⟪curl (u × ω), A⟫`.

This is the integration by parts which shows that the pairing against the Lamb vector `u × ω` is
self-adjoint for the curl, i.e. that `∂ₜ curl u = curl ∂ₜ u` weakly (see `weakCurl_pair`).

## Route

* the pointwise Weyl identity `div (V × A) = ⟪curl V, A⟫ - ⟪V, curl A⟫` for `V := u × ω`
  (`CurlGrad.div_crossVec_eq`), which holds off the two planes;
* the divergence
  `div ((u × ω) × A) = div (⟪u,A⟫ • ω) - div (⟪ω,A⟫ • u)`, the triple product identity
  `(a × b) × c = (a·c) b - (b·c) a` together with the product rules `div_smul_eq`, whose integral
  vanishes by `Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes` once the integrability of
  the four summands is known: three of them are integrable by `integrable_mul_div` /
  `integrable_inner_gradient` (`div u = 0` kills the fourth), and the last one
  `⟪∇⟪ω,A⟫, u⟫` by `integrable_gradInner_rough_local` below.

(`hcurl` is part of the statement but the identity is a pure integration by parts for the field
`u × ω`; the hypothesis is not needed by this proof.)
-/

set_option maxHeartbeats 1600000

open MeasureTheory Set Topology Filter
open FiniteTimeSingularity
open scoped Topology

namespace Work.FTS.PressureOn.weakCurl

/-! ## Elementary helpers -/

theorem crossVec_crossVec_eq (a b c : R3) :
    crossVec (crossVec a b) c = inner ℝ a c • b - inner ℝ b c • a := by
  ext k
  fin_cases k <;>
    simp [crossVec, crossProduct, PiLp.inner_apply, WithLp.ofLp_toLp, Fin.sum_univ_three] <;> ring



theorem div_sub_eq_local (A B : R3 → R3) (x : R3) (hA : DifferentiableAt ℝ A x)
    (hB : DifferentiableAt ℝ B x) : div (fun y => A y - B y) x = div A x - div B x := by
  rw [div, div, div, fderiv_fun_sub hA hB]
  rw [show (↑(fderiv ℝ A x - fderiv ℝ B x) : R3 →ₗ[ℝ] R3)
        = (fderiv ℝ A x : R3 →ₗ[ℝ] R3) - (fderiv ℝ B x : R3 →ₗ[ℝ] R3) from rfl]
  rw [map_sub]

/-! ## Integrability of `⟪∇⟪ω,A⟫, u⟫` for a merely continuous `ω` -/

theorem integrable_gradInner_rough_local {ω A u : R3 → R3}
    (hωcont : Continuous ω) (hωcs : HasCompactSupport ω)
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt ω (fderiv ℝ ω x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    (hA : ∀ n : ℕ, ContDiff ℝ n A) (hAcs : HasCompactSupport A)
    (hu : ContDiff ℝ 1 u) :
    MeasureTheory.Integrable
      (fun x => inner ℝ (gradient (fun x => inner ℝ (ω x) (A x)) x) (u x)) := by
  have hAc1 : ContDiff ℝ 1 A := hA 1
  have hAd : ∀ x, HasFDerivAt A (fderiv ℝ A x) x :=
    fun x => (hAc1.differentiable_one x).hasFDerivAt
  have huc : Continuous u := hu.continuous
  have hae : (fun x : R3 => inner ℝ (gradient (fun x => inner ℝ (ω x) (A x)) x) (u x))
      =ᵐ[volume] fun x : R3 =>
        inner ℝ ((fderiv ℝ ω x) (u x)) (A x) + inner ℝ (ω x) ((fderiv ℝ A x) (u x)) := by
    filter_upwards [Work.FTS.PressureOn.ae_coord_ne_zero] with x hx
    rw [inner_gradient_left,
      fderiv_inner_apply ℝ (hωdiff x hx.1 hx.2).differentiableAt (hAd x).differentiableAt (u x)]
    ring
  refine (Integrable.add ?_ ?_).congr hae.symm
  · obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ tsupport A, ‖u x‖ ≤ C := by
      have hb : Bornology.IsBounded ((fun x : R3 => ‖u x‖) '' tsupport A) :=
        (hAcs.isCompact.image (f := fun x : R3 => ‖u x‖) huc.norm).isBounded
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
      refine ⟨C, fun x hx => ?_⟩
      have h1 : ‖‖u x‖‖ ≤ C := hC (‖u x‖) (Set.mem_image_of_mem (fun x : R3 => ‖u x‖) hx)
      simpa using h1
    set M : ℝ := |C| + 1 with hMdef
    have hM : ∀ x ∈ tsupport A, ‖u x‖ ≤ M := fun x hx => by
      rw [hMdef]; linarith [hC x hx, le_abs_self C]
    have hMpos : 0 ≤ M := by rw [hMdef]; positivity
    have hbase : MeasureTheory.Integrable (fun x : R3 => ‖A x‖ * ‖fderiv ℝ ω x‖) := by
      have h := hωint.integrable_smul_left_of_hasCompactSupport hAc1.continuous.norm hAcs.norm
      refine h.norm.congr ?_
      filter_upwards with x
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (hbase.const_mul M).mono' ?_ ?_
    · have hY : AEStronglyMeasurable (fun x : R3 => fderiv ℝ ω x) :=
        hωint.aestronglyMeasurable
      have hX1 : AEStronglyMeasurable (fun x : R3 => (u x, A x)) :=
        huc.aestronglyMeasurable.prodMk hAc1.continuous.aestronglyMeasurable
      have hX : AEStronglyMeasurable
          (fun x : R3 => (fderiv ℝ ω x, (u x, A x))) :=
        hY.prodMk hX1
      have hΦ : Continuous (fun p : (R3 →L[ℝ] R3) × (R3 × R3) =>
          inner ℝ (p.1 p.2.1) (p.2.2)) :=
        Continuous.inner
          (continuous_fst.clm_apply (continuous_fst.comp continuous_snd))
          (continuous_snd.comp continuous_snd)
      exact hΦ.comp_aestronglyMeasurable hX
    · filter_upwards with x
      by_cases hx : x ∈ tsupport A
      · calc ‖inner ℝ ((fderiv ℝ ω x) (u x)) (A x)‖
            ≤ ‖(fderiv ℝ ω x) (u x)‖ * ‖A x‖ := norm_inner_le_norm _ _
          _ ≤ (‖fderiv ℝ ω x‖ * ‖u x‖) * ‖A x‖ := by
              gcongr
              exact ContinuousLinearMap.le_opNorm _ _
          _ ≤ (‖fderiv ℝ ω x‖ * M) * ‖A x‖ := by
              gcongr
              exact hM x hx
          _ = M * (‖A x‖ * ‖fderiv ℝ ω x‖) := by ring
      · have hA0 : A x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hA0, inner_zero_right, norm_zero]
        exact mul_nonneg hMpos (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact Continuous.inner hωcont ((hAc1.continuous_fderiv_apply one_ne_zero).comp
        (continuous_id.prodMk huc))
    · refine hωcs.mono' ?_
      intro x hx
      rw [Function.mem_support] at hx
      exact subset_tsupport _ (by
        rw [Function.mem_support]
        intro hω0
        exact hx (by rw [hω0, inner_zero_left]))

/-! ## The main theorem -/

theorem weyl_cross {u ω : R3 → ℝ → R3} {t : ℝ} {A : R3 → R3}
    (hA : ∀ n : ℕ, ContDiff ℝ n A) (hAcs : HasCompactSupport A)
    (hR : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hsnbhd : ∀ s ∈ Set.Ioo (t - 1) (t + 1), ContDiff ℝ 1 (u · s))
    (hcurl : ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x,
      FiniteTimeSingularity.vorticity (fun y => u y s) x = ω x s)
    (hdivu : ∀ s ∈ Set.Ioo (t - 1) (t + 1), FiniteTimeSingularity.div (u · s) = 0)
    (hωcont : Continuous (fun x => ω x t))
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt (fun x => ω x t) (fderiv ℝ (ω · t) x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ (ω · t) x)) :
    (∫ x, inner ℝ (crossVec (u x t) (ω x t)) (FiniteTimeSingularity.vorticity A x))
      = ∫ x, inner ℝ (FiniteTimeSingularity.vorticity (fun y => crossVec (u y t) (ω y t)) x)
          (A x) := by
  obtain ⟨R₀, hR₀0, hR₀bd⟩ := hR
  have htI : t ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hut : ContDiff ℝ 1 (fun x : R3 => u x t) := hsnbhd t htI
  have hutd : ∀ x, HasFDerivAt (fun y : R3 => u y t) (fderiv ℝ (fun y : R3 => u y t) x) x :=
    fun x => (hut.differentiable_one x).hasFDerivAt
  have hdivut : div (fun y : R3 => u y t) = 0 := hdivu t htI
  have hAc1 : ContDiff ℝ 1 A := hA 1
  have hAd : ∀ x, HasFDerivAt A (fderiv ℝ A x) x := fun x => (hAc1.differentiable_one x).hasFDerivAt
  -- compact support of the vorticity at time `t`
  have hωcs : HasCompactSupport (fun x : R3 => ω x t) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R₀) ?_
    intro x hx
    rw [Function.mem_support] at hx
    show dist x 0 ≤ R₀
    rw [dist_eq_norm, sub_zero]
    exact hR₀bd t htI x hx
  -- the fields
  set V : R3 → R3 := fun x => crossVec (u x t) (ω x t) with hVdef
  set W : R3 → R3 := fun x => crossVec (V x) (A x) with hWdef
  have hVd : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt V (fderiv ℝ V x) x := by
    intro x hx1 hx2
    have h := Work.FTS.BSSwirl.hasFDerivAt_crossR3 (V := fun y : R3 => u y t)
      (Ψ := fun y : R3 => ω y t) (hutd x) (hωdiff x hx1 hx2)
    have h2 : HasFDerivAt (fun y : R3 => Work.FTS.BSSwirl.crossR3 ((fun y : R3 => u y t) y)
        ((fun y : R3 => ω y t) y))
        (fderiv ℝ (fun y : R3 => Work.FTS.BSSwirl.crossR3 ((fun y : R3 => u y t) y)
          ((fun y : R3 => ω y t) y)) x) x := by
      rw [h.fderiv]; exact h
    rw [hVdef]
    exact h2
  have hVcont : Continuous V := by
    have h := Work.FTS.PressureOn.vorticityCross_isBoundedBilinearMap.continuous
    rw [hVdef]
    exact h.comp (hut.continuous.prodMk hωcont)
  have hVcs : HasCompactSupport V := by
    rw [hVdef]
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R₀) ?_
    intro x hx
    rw [Function.mem_support] at hx
    show dist x 0 ≤ R₀
    rw [dist_eq_norm, sub_zero]
    by_contra hlt
    push_neg at hlt
    have hω0 : ω x t = 0 := by
      by_contra hne
      exact absurd (hR₀bd t htI x hne) (not_le.mpr hlt)
    exact hx (by simp [hω0])
  have hWd : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt W (fderiv ℝ W x) x := by
    intro x hx1 hx2
    have h := Work.FTS.BSSwirl.hasFDerivAt_crossR3 (V := V) (Ψ := A) (hVd x hx1 hx2) (hAd x)
    have h2 : HasFDerivAt (fun y : R3 => Work.FTS.BSSwirl.crossR3 (V y) (A y))
        (fderiv ℝ (fun y : R3 => Work.FTS.BSSwirl.crossR3 (V y) (A y)) x) x := by
      rw [h.fderiv]; exact h
    rw [hWdef]
    exact h2
  have hWcont : Continuous W := by
    have h := Work.FTS.PressureOn.vorticityCross_isBoundedBilinearMap.continuous
    rw [hWdef]
    exact h.comp (hVcont.prodMk (hAc1.continuous))
  have hWcs : HasCompactSupport W := by
    rw [hWdef]
    refine hVcs.mono' ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro hV0
      exact hx (by simp [hV0]))
  -- the two scalar multipliers
  have hφ_cd : ContDiff ℝ 1 (fun x : R3 => inner ℝ (u x t) (A x)) := by
    have hw : ContDiff ℝ 1 (fun p : R3 × R3 => inner ℝ p.1 p.2) :=
      isBoundedBilinearMap_inner.contDiff
    exact hw.comp (hut.prodMk hAc1)
  have hφ_cs : HasCompactSupport (fun x : R3 => inner ℝ (u x t) (A x)) := by
    refine hAcs.mono' ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro hAx
      exact hx (by rw [hAx, inner_zero_right]))
  -- the a.e. identity for the divergence of `W`
  have hdivW_ae : (fun x : R3 => div W x) =ᵐ[volume]
      fun x : R3 =>
        (inner ℝ (u x t) (A x) * div (fun y : R3 => ω y t) x
          + inner ℝ (gradient (fun y : R3 => inner ℝ (u y t) (A y)) x) (ω x t))
        - (inner ℝ (ω x t) (A x) * div (fun y : R3 => u y t) x
          + inner ℝ (gradient (fun y : R3 => inner ℝ (ω y t) (A y)) x) (u x t)) := by
    filter_upwards [Work.FTS.PressureOn.ae_coord_ne_zero] with x hx
    have hx1 : x 0 ≠ 0 := hx.1
    have hx2 : x 2 ≠ 0 := hx.2
    -- the algebraic identity `W = ψ₁ • ω - ψ₂ • u`
    have hWeq : W = (fun y : R3 => inner ℝ (u y t) (A y)) • (fun z : R3 => ω z t)
        - (fun y : R3 => inner ℝ (ω y t) (A y)) • (fun z : R3 => u z t) := by
      rw [hWdef]
      funext y
      simp only [hVdef]
      rw [crossVec_crossVec_eq]
      rfl
    have hd1 : DifferentiableAt ℝ (fun y : R3 => inner ℝ (u y t) (A y)) x :=
      DifferentiableAt.inner ℝ (hutd x).differentiableAt (hAd x).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun y : R3 => inner ℝ (ω y t) (A y)) x :=
      DifferentiableAt.inner ℝ (hωdiff x hx1 hx2).differentiableAt (hAd x).differentiableAt
    have hd3 : DifferentiableAt ℝ (fun z : R3 => ω z t) x := (hωdiff x hx1 hx2).differentiableAt
    have hd4 : DifferentiableAt ℝ (fun z : R3 => u z t) x := (hutd x).differentiableAt
    have hP1 : DifferentiableAt ℝ ((fun y : R3 => inner ℝ (u y t) (A y)) •
        (fun z : R3 => ω z t)) x := hd1.smul hd3
    have hP2 : DifferentiableAt ℝ ((fun y : R3 => inner ℝ (ω y t) (A y)) •
        (fun z : R3 => u z t)) x := hd2.smul hd4
    -- the divergence of `W` splits
    have hpieces : div W x
        = div ((fun y : R3 => inner ℝ (u y t) (A y)) • (fun z : R3 => ω z t)) x
          - div ((fun y : R3 => inner ℝ (ω y t) (A y)) • (fun z : R3 => u z t)) x := by
      have hWeq' : W = (fun y : R3 =>
          ((fun y : R3 => inner ℝ (u y t) (A y)) • (fun z : R3 => ω z t)) y
            - ((fun y : R3 => inner ℝ (ω y t) (A y)) • (fun z : R3 => u z t)) y) :=
        funext fun y => congrFun hWeq y
      rw [hWeq', div_sub_eq_local _ _ x hP1 hP2]
    rw [hpieces,
      div_smul_eq (ψ := fun y : R3 => inner ℝ (u y t) (A y)) (ω := fun z : R3 => ω z t) hd1 hd3,
      div_smul_eq (ψ := fun y : R3 => inner ℝ (ω y t) (A y)) (ω := fun z : R3 => u z t) hd2 hd4]
  -- integrability of the two pieces
  have hIntP : MeasureTheory.Integrable (fun x : R3 =>
      inner ℝ (u x t) (A x) * div (fun y : R3 => ω y t) x
        + inner ℝ (gradient (fun y : R3 => inner ℝ (u y t) (A y)) x)
            (ω x t)) := by
    refine Integrable.add ?_ ?_
    · exact integrable_mul_div (ω := fun y : R3 => ω y t)
        (ψ := fun y : R3 => inner ℝ (u y t) (A y)) hωint hφ_cd hφ_cs
    · have h := integrable_inner_gradient (ω := fun y : R3 => ω y t)
        (ψ := fun y : R3 => inner ℝ (u y t) (A y)) hωcont hφ_cd hφ_cs
      refine h.congr ?_
      filter_upwards with x
      rw [real_inner_comm]
  have hIntQ : MeasureTheory.Integrable (fun x : R3 =>
      inner ℝ (ω x t) (A x) * div (fun y : R3 => u y t) x
        + inner ℝ (gradient (fun y : R3 => inner ℝ (ω y t) (A y)) x)
            (u x t)) := by
    have hQ : (fun x : R3 =>
        inner ℝ (ω x t) (A x) * div (fun y : R3 => u y t) x
          + inner ℝ (gradient (fun y : R3 => inner ℝ (ω y t) (A y)) x) (u x t))
        = fun x : R3 => inner ℝ (gradient (fun y : R3 => inner ℝ (ω y t) (A y)) x) (u x t) := by
      funext x
      simp only [congrFun hdivut x, Pi.zero_apply, mul_zero, zero_add]
    rw [hQ]
    exact integrable_gradInner_rough_local hωcont hωcs hωdiff hωint hA hAcs hut
  have hWint : MeasureTheory.Integrable (fun x : R3 => div W x) :=
    (hIntP.sub hIntQ).congr hdivW_ae.symm
  have hWzero : (∫ x : R3, div W x) = 0 :=
    Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes hWcont hWcs hWd hWint
  -- the pointwise Weyl identity
  have hIntVvA : MeasureTheory.Integrable (fun x : R3 => inner ℝ (V x) (vorticity A x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hVcont.inner (Work.FTS.BSSwirl.continuous_vorticity hAc1)
    · refine hVcs.mono' ?_
      intro x hx
      rw [Function.mem_support] at hx
      exact subset_tsupport _ (by
        rw [Function.mem_support]
        intro hV0
        exact hx (by simp [hV0]))
  have hWeyl : (fun x : R3 => inner ℝ (vorticity V x) (A x))
      =ᵐ[volume] fun x : R3 => inner ℝ (V x) (vorticity A x) + div W x := by
    filter_upwards [Work.FTS.PressureOn.ae_coord_ne_zero] with x hx
    have h := Work.FTS.PressureOn.CurlGrad.div_crossVec_eq (F := V) (G := A)
      (hVd x hx.1 hx.2) (hAd x)
    have hWd' : div W x = div (fun y : R3 => crossVec (V y) (A y)) x := by
      rw [hWdef]
    rw [hWd', h]
    ring
  have hmain : (∫ x : R3, inner ℝ (vorticity V x) (A x))
      = ∫ x : R3, inner ℝ (V x) (vorticity A x) := by
    rw [integral_congr_ae hWeyl]
    rw [integral_add hIntVvA hWint, hWzero, add_zero]
  simpa only [hVdef] using hmain.symm

end Work.FTS.PressureOn.weakCurl
