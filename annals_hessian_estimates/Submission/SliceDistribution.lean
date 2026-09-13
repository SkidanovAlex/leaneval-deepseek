/-
# The distributional inequality `L_e u ≥ 0` for a viscosity subsolution

Combining the slice theorem (`Submission.isViscSubsolution_slice_add`) with the mean value
property for viscosity subharmonic functions and the Fubini decomposition of `ℝ⁴` along the
splitting `ℝ⁴ = span(b 0) ⊕ span(b 1, b 2, b 3)`, we obtain: a continuous viscosity subsolution
`u` of `L_e = Δ - D_ee` on an open set `s` satisfies `L_e u ≥ 0` in the sense of distributions,
`∫ u · L_eφ ≥ 0` for every nonnegative test function `φ` supported in `s`.

This is the second half of the proof that the Hessian of a continuous `2`-convex function is a
Radon measure (Chaudhuri--Trudinger `[CT]` Theorem 2.4).
-/
import Mathlib
import Submission.ViscositySlice
import Submission.HyperplaneSubsolution
import Submission.Commons.Measure.Lebesgue.integral_euclideanSpace_fin_succ
import Submission.Commons.Analysis.Viscosity.ball_le_of_visc_subharmonic
import Submission.Commons.Analysis.Harmonic.integral_laplacian_nonneg_of_ball_meanValue_cs

open Metric MeasureTheory Filter Set Function
open scoped BigOperators RealInnerProductSpace InnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Expansion of a vector in value coordinates in the orthonormal basis. -/
theorem repr_symm_eq_sum (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (c : Fin 4 → ℝ) :
    b.repr.symm (WithLp.toLp 2 c) = ∑ i : Fin 4, c i • b i := by
  conv_lhs => rw [← b.sum_repr (b.repr.symm (WithLp.toLp 2 c))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- The linear combination `t • b 0 + ∑ j z j • b (j+1)`. -/
theorem cons_expand (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (t : ℝ) (z : ℝ³) :
    b.repr.symm (WithLp.toLp 2 (Fin.cons t (fun j : Fin 3 => z.ofLp j)))
      = t • b 0 + frameMap b z := by
  rw [repr_symm_eq_sum]
  rw [Fin.sum_univ_succ (f := fun i : Fin 4 =>
    (Fin.cons t (fun j : Fin 3 => z.ofLp j) : Fin 4 → ℝ) i • b i)]
  rw [Fin.cons_zero, frameMap_apply]
  simp only [Fin.cons_succ]

/-- The frame map is an isometry onto its image. -/
theorem norm_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z : ℝ³) :
    ‖frameMap b z‖ = ‖z‖ := by
  have h1 : frameMap b z
      = b.repr.symm (WithLp.toLp 2 (Fin.cons 0 (fun j : Fin 3 => z.ofLp j) : Fin 4 → ℝ)) := by
    rw [cons_expand b 0 z]
    simp
  rw [h1, LinearIsometryEquiv.norm_map]
  have h2 : ‖WithLp.toLp 2 (Fin.cons 0 (fun j : Fin 3 => z.ofLp j) : Fin 4 → ℝ)‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 4 => ℝ), PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ),
      Fin.sum_univ_succ (f := fun i : Fin 4 =>
        ‖(WithLp.toLp 2 (Fin.cons 0 (fun j : Fin 3 => z.ofLp j) : Fin 4 → ℝ)).ofLp i‖ ^ 2)]
    simp [Fin.cons_zero, Fin.cons_succ]
  nlinarith [h2, norm_nonneg (WithLp.toLp 2 (Fin.cons 0 (fun j : Fin 3 => z.ofLp j) : Fin 4 → ℝ)),
    norm_nonneg z]

/-- **Fubini decomposition along the splitting `ℝ⁴ = span(b 0) ⊕ span(b 1, b 2, b 3)`.** -/
theorem integral_frame_split (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (G : ℝ⁴ → ℝ)
    (hG : Integrable G volume) :
    ∫ y, G y = ∫ t : ℝ, ∫ z : ℝ³, G (t • b 0 + frameMap b z) := by
  have h1 : ∫ y, G y = ∫ x : ℝ⁴, G (b.repr.symm x) :=
    (b.measurePreserving_repr_symm.integral_comp
      (MeasurableEquiv.measurableEmbedding b.repr.symm.toMeasurableEquiv) G).symm
  have h2 : ∫ x : ℝ⁴, G (b.repr.symm x)
      = ∫ t : ℝ, ∫ w : ℝ³, G (b.repr.symm (WithLp.toLp 2 (Fin.cons t (fun j => w.ofLp j)))) :=
    Commons.Measure.Lebesgue.integral_euclideanSpace_fin_succ
      (fun x : ℝ⁴ => G (b.repr.symm x))
      ((b.measurePreserving_repr_symm.integrable_comp_emb
        (MeasurableEquiv.measurableEmbedding b.repr.symm.toMeasurableEquiv)).mpr hG)
  rw [h1, h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact congrArg G (cons_expand b t z)


/-- The slice domain `{z | c + frameMap b z ∈ s}` is open. -/
theorem isOpen_sliceSetAt (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) {s : Set ℝ⁴} (hs : IsOpen s)
    (c : ℝ⁴) : IsOpen (sliceSetAt b c s) := by
  have h : sliceSetAt b c s = (fun z : ℝ³ => c + frameMapCLM b z) ⁻¹' s := by
    ext z
    simp [sliceSetAt, frameMapCLM_apply]
  rw [h]
  exact hs.preimage (continuous_const.add (frameMapCLM b).continuous)

/-- The frame coordinates of a standard basis vector. -/
theorem frameMapCLM_single (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (i : Fin 3) :
    frameMapCLM b (EuclideanSpace.single i 1) = b (Fin.succ i) := by
  rw [frameMapCLM_apply, frameMap_apply]
  rw [Finset.sum_eq_single i]
  · simp [PiLp.single_apply]
  · intro j _ hj
    rw [PiLp.single_apply, if_neg hj, zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The second derivative of a function of the slice coordinates. -/
theorem fderiv_fderiv_comp_frameMap {φ : ℝ⁴ → ℝ} (hφ : ContDiff ℝ 2 φ) (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴)
    (c : ℝ⁴) (z : ℝ³) (u v : ℝ³) :
    (fderiv ℝ (fderiv ℝ (fun w : ℝ³ => φ (c + frameMap b w))) z) u v
      = (fderiv ℝ (fderiv ℝ φ) (c + frameMap b z)) (frameMapCLM b u) (frameMapCLM b v) := by
  have h := Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_comp_add_linear
    (frameMapCLM b) c φ hφ z u v
  have hfun : (fun w : ℝ³ => φ (c + frameMap b w))
      = (fun w : ℝ³ => φ (c + frameMapCLM b w)) := by
    funext w
    rw [frameMapCLM_apply]
  rw [hfun]
  exact h

/-- **`L_e u ≥ 0` in the sense of distributions.** -/
theorem hyperplane_laplacian_nonneg {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴)
    (hvis : ∀ φ : ℝ⁴ → ℝ, ContDiffOn ℝ 2 φ s → ∀ x ∈ s,
        (∀ᶠ y in 𝓝[s] x, u y - φ y ≤ u x - φ x) →
        0 ≤ ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
          (b (Fin.succ i)) (b (Fin.succ i))) :
    ∀ φ : ℝ⁴ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ s → 0 ≤ φ →
      0 ≤ ∫ x, u x * (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
        (b (Fin.succ i)) (b (Fin.succ i))) := by
  intro φ hφcd hφcs hφs hφnn
  have hφ2 : ContDiff ℝ 2 φ := hφcd.of_le (WithTop.coe_le_coe.mpr le_top)
  set Lf : ℝ⁴ → ℝ := fun x => ∑ i : Fin 3, (iteratedFDeriv ℝ 2 φ x)
    ![b (Fin.succ i), b (Fin.succ i)] with hLf
  have hLf_eq : ∀ x : ℝ⁴, Lf x = ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
      (b (Fin.succ i)) (b (Fin.succ i)) := by
    intro x
    rw [hLf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDeriv_two_apply]
    simp
  -- ## continuity of `Lf`
  have hcont2 : Continuous (iteratedFDeriv ℝ 2 φ) :=
    hφ2.continuous_iteratedFDeriv (m := 2) (by norm_num)
  have hLcont : Continuous Lf := by
    rw [hLf]
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ⁴) ℝ
      ![b (Fin.succ i), b (Fin.succ i)]).continuous).comp hcont2
  -- ## the support of `Lf` is contained in that of `φ`
  have hsuppL : tsupport Lf ⊆ tsupport φ := by
    refine closure_minimal ?_ (isClosed_tsupport φ)
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxc
    refine hx ?_
    have h0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxc
    have h1 : fderiv ℝ φ =ᶠ[𝓝 x] fderiv ℝ (fun _ : ℝ⁴ => (0 : ℝ)) := h0.fderiv
    have h2 : fderiv ℝ (fderiv ℝ φ) =ᶠ[𝓝 x] fderiv ℝ (fderiv ℝ (fun _ : ℝ⁴ => (0 : ℝ))) :=
      h1.fderiv
    have h3 : fderiv ℝ (fderiv ℝ φ) x = 0 := by
      rw [h2.eq_of_nhds]; simp
    rw [hLf]
    show (∑ i : Fin 3, (iteratedFDeriv ℝ 2 φ x) ![b (Fin.succ i), b (Fin.succ i)]) = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [iteratedFDeriv_two_apply, h3]
    simp
  -- ## integrability
  have hFint : Integrable (fun x => u x * Lf x) volume := by
    have hcontK : ContinuousOn (fun x => u x * Lf x) (tsupport φ) :=
      (hu.mono hφs).mul hLcont.continuousOn
    have hIntK : IntegrableOn (fun x => u x * Lf x) (tsupport φ) volume :=
      hcontK.integrableOn_compact hφcs
    have hzero : ∀ x ∉ tsupport φ, u x * Lf x = 0 := by
      intro x hx
      have : Lf x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsuppL hmem))
      rw [this, mul_zero]
    have h1 : (fun x => u x * Lf x) = (tsupport φ).indicator (fun x => u x * Lf x) := by
      funext x
      by_cases hx : x ∈ tsupport φ
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hzero x hx]
    rw [h1]
    exact (integrable_indicator_iff hφcs.measurableSet).mpr hIntK
  -- ## the identity on the slices
  have hkey : ∀ (c : ℝ⁴) (z : ℝ³),
      Lf (c + frameMap b z) = Laplacian.laplacian (fun w : ℝ³ => φ (c + frameMap b w)) z := by
    intro c z
    rw [hLf, laplacian_eq_sum_single]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDeriv_two_apply, ← frameMapCLM_single b i]
    exact (fderiv_fderiv_comp_frameMap hφ2 b c z
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)).symm
  -- ## each slice integral is nonnegative
  have hslice : ∀ t : ℝ, 0 ≤ ∫ z : ℝ³, u (t • b 0 + frameMap b z) * Lf (t • b 0 + frameMap b z) := by
    intro t
    set c : ℝ⁴ := t • b 0 with hc
    set ψ : ℝ³ → ℝ := fun z => φ (c + frameMap b z) with hψ
    have hslic : IsOpen (sliceSetAt b c s) := isOpen_sliceSetAt b hs c
    have hmap : Continuous (fun z : ℝ³ => c + frameMap b z) := by
      have h0 : Continuous (fun z : ℝ³ => c + frameMapCLM b z) :=
        continuous_const.add (frameMapCLM b).continuous
      simpa [frameMapCLM_apply] using h0
    have hwcont : ContinuousOn (fun z : ℝ³ => u (c + frameMap b z)) (sliceSetAt b c s) := by
      refine hu.comp hmap.continuousOn fun z hz => ?_
      simpa [sliceSetAt, frameMapCLM_apply] using hz
    have hwvis : ∀ χ : ℝ³ → ℝ, ContDiffOn ℝ 2 χ (sliceSetAt b c s) → ∀ z ∈ sliceSetAt b c s,
        (∀ᶠ w in 𝓝[sliceSetAt b c s] z, u (c + frameMap b w) - χ w ≤ u (c + frameMap b z) - χ z) →
        0 ≤ Laplacian.laplacian χ z :=
      fun χ hχ z hz hmax => isViscSubsolution_slice_add hs hu b c hvis χ hχ z hz hmax
    have hMVP : ∀ c₀ ∈ sliceSetAt b c s, ∀ R : ℝ, 0 < R → closedBall c₀ R ⊆ sliceSetAt b c s →
        u (c + frameMap b c₀) ≤ ⨍ y in ball c₀ R, u (c + frameMap b y) :=
      fun c₀ hc₀ R hR hsub =>
        Commons.Analysis.Viscosity.ball_le_of_visc_subharmonic (n := 3) (by norm_num)
          hslic hwcont hwvis hR hsub
    have hmapcd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ³ => c + frameMap b z) := by
      rw [show (fun z : ℝ³ => c + frameMap b z) = (fun z : ℝ³ => c + frameMapCLM b z) from by
        funext z; rw [frameMapCLM_apply]]
      exact contDiff_const.add (frameMapCLM b).contDiff
    have hψcd : ContDiff ℝ (⊤ : ℕ∞) ψ := hφcd.comp hmapcd
    have hψcs : HasCompactSupport ψ := by
      obtain ⟨R, hR⟩ := hφcs.isBounded.subset_closedBall 0
      have hsupp2 : support ψ ⊆ closedBall (0 : ℝ³) (R + ‖c‖) := by
        intro z hz
        rw [Function.mem_support] at hz
        rw [mem_closedBall, dist_eq_norm, sub_zero]
        by_contra hcon
        refine hz ?_
        rw [hψ]
        exact image_eq_zero_of_notMem_tsupport (fun hmem => by
          have hR' := hR hmem
          rw [mem_closedBall, dist_eq_norm, sub_zero] at hR'
          have h2 : ‖z‖ ≤ ‖c + frameMap b z‖ + ‖c‖ := by
            calc ‖z‖ = ‖frameMap b z‖ := (norm_frameMap b z).symm
              _ = ‖(c + frameMap b z) - c‖ := by rw [add_sub_cancel_left]
              _ ≤ ‖c + frameMap b z‖ + ‖c‖ := norm_sub_le _ _
          have h3 : R + ‖c‖ < ‖c + frameMap b z‖ + ‖c‖ := lt_of_lt_of_le (not_le.mp hcon) h2
          linarith)
      have hbdd : Bornology.IsBounded (tsupport ψ) :=
        (isBounded_closedBall (x := (0 : ℝ³)) (r := R + ‖c‖)).subset
          (closure_minimal hsupp2 isClosed_closedBall)
      rw [HasCompactSupport]
      exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hbdd⟩
    have hψs : tsupport ψ ⊆ sliceSetAt b c s := by
      have h1 : support ψ ⊆ (fun z : ℝ³ => c + frameMap b z) ⁻¹' tsupport φ := by
        intro z hz
        rw [Function.mem_support] at hz
        by_contra hmem
        exact hz (by rw [hψ]; exact image_eq_zero_of_notMem_tsupport hmem)
      have h2 : tsupport ψ ⊆ (fun z : ℝ³ => c + frameMap b z) ⁻¹' tsupport φ :=
        closure_minimal h1 ((isClosed_tsupport φ).preimage hmap)
      intro z hz
      exact hφs (h2 hz)
    have hψnn : 0 ≤ ψ := fun z => hφnn _
    have h := Commons.Analysis.Harmonic.integral_laplacian_nonneg_of_ball_meanValue_cs
      hslic hwcont hMVP ψ hψcd hψcs hψs hψnn
    rw [show (∫ z : ℝ³, u (c + frameMap b z) * Lf (c + frameMap b z))
        = ∫ z : ℝ³, u (c + frameMap b z) * Laplacian.laplacian ψ z from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show u (c + frameMap b z) * Lf (c + frameMap b z)
        = u (c + frameMap b z) * Laplacian.laplacian ψ z
      rw [hkey c z]]
    exact h
  -- ## assemble
  rw [show (∫ x : ℝ⁴, u x * (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
        (b (Fin.succ i)) (b (Fin.succ i)))) = ∫ x : ℝ⁴, u x * Lf x from by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show u x * (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x) (b (Fin.succ i)) (b (Fin.succ i)))
      = u x * Lf x
    rw [hLf_eq x]]
  rw [integral_frame_split b (fun x => u x * Lf x) hFint]
  exact integral_nonneg hslice


/-- **`L_e u ≥ 0` in the sense of distributions, for a continuous `2`-convex function.** -/
theorem hyperplane_laplacian_nonneg_of_twoConvex {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (h2 : IsTwoConvexOn u s) (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) :
    ∀ φ : ℝ⁴ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ s → 0 ≤ φ →
      0 ≤ ∫ x, u x * (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
        (b (Fin.succ i)) (b (Fin.succ i))) := by
  refine hyperplane_laplacian_nonneg hs hu b ?_
  intro φ hφ x hx hmax
  have h1 := isViscSubsolution_hyperplane hs h2 (b 0) (b.norm_eq_one 0) φ hφ x hx hmax
  change (fun M : ℝ⁴ →L[ℝ] ℝ⁴ =>
    -((LinearMap.trace ℝ ℝ⁴) M.toLinearMap - ⟪M (b 0), b 0⟫)) (HessOp φ s x) ≤ 0 at h1
  rw [neg_nonpos, sub_nonneg, LinearMap.trace_eq_sum_inner _ b, Fin.sum_univ_succ] at h1
  have hA : ⟪(HessOp φ s x) (b 0), b 0⟫_ℝ
      = ⟪b 0, (HessOp φ s x).toLinearMap (b 0)⟫_ℝ :=
    real_inner_comm (b 0) (HessOp φ s x (b 0))
  rw [hA] at h1
  have h2' : 0 ≤ ∑ i : Fin 3, ⟪HessOp φ s x (b (Fin.succ i)), b (Fin.succ i)⟫_ℝ := by
    have hsum : (∑ i : Fin 3, ⟪b (Fin.succ i), (HessOp φ s x).toLinearMap (b (Fin.succ i))⟫_ℝ)
        = ∑ i : Fin 3, ⟪HessOp φ s x (b (Fin.succ i)), b (Fin.succ i)⟫_ℝ :=
      Finset.sum_congr rfl fun i _ =>
        (real_inner_comm (b (Fin.succ i)) (HessOp φ s x (b (Fin.succ i)))).symm
    linarith [h1, hsum.le, hsum.ge]
  refine le_trans h2' ?_
  refine Finset.sum_le_sum fun i _ => ?_
  unfold HessOp
  rw [Commons.Analysis.Calculus.FDeriv.hessianWithin_apply_second_partial b hs hx hφ (Fin.succ i)
      (Fin.succ i), iteratedFDeriv_two_apply]
  simp


/-- The Laplacian in an orthonormal basis. -/
theorem laplacian_eq_sum_frame (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (ψ : ℝ⁴ → ℝ) (x : ℝ⁴) :
    Laplacian.laplacian ψ x = ∑ j : Fin 4, (fderiv ℝ (fderiv ℝ ψ) x) (b j) (b j) := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials b ψ x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  simp

/-- **`L_e u ≥ 0` in the sense of distributions, in the direction form.** -/
theorem hyperplane_laplacian_nonneg_e {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴)
    (hvis : ∀ φ : ℝ⁴ → ℝ, ContDiffOn ℝ 2 φ s → ∀ x ∈ s,
        (∀ᶠ y in 𝓝[s] x, u y - φ y ≤ u x - φ x) →
        0 ≤ ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
          (b (Fin.succ i)) (b (Fin.succ i)))
    (e : ℝ⁴) (he : b 0 = e) :
    ∀ φ : ℝ⁴ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ s → 0 ≤ φ →
      0 ≤ ∫ x, u x * (Laplacian.laplacian φ x - (fderiv ℝ (fderiv ℝ φ) x) e e) := by
  intro φ hφcd hφcs hφs hφnn
  have h := hyperplane_laplacian_nonneg hs hu b hvis φ hφcd hφcs hφs hφnn
  rw [show (fun x => u x * (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
        (b (Fin.succ i)) (b (Fin.succ i))))
      = (fun x => u x * (Laplacian.laplacian φ x - (fderiv ℝ (fderiv ℝ φ) x) e e)) from by
    funext x
    rw [laplacian_eq_sum_frame b φ x,
      Fin.sum_univ_succ (f := fun j : Fin 4 => (fderiv ℝ (fderiv ℝ φ) x) (b j) (b j)), he]
    ring] at h
  exact h

/-- **`L_e u ≥ 0` in the sense of distributions, for a continuous `2`-convex function.** -/
theorem hyperplane_laplacian_nonneg_of_twoConvex_e {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (h2 : IsTwoConvexOn u s) (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴)
    (e : ℝ⁴) (he : b 0 = e) :
    ∀ φ : ℝ⁴ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ s → 0 ≤ φ →
      0 ≤ ∫ x, u x * (Laplacian.laplacian φ x - (fderiv ℝ (fderiv ℝ φ) x) e e) := by
  have hone : ‖b 0‖ = 1 := b.norm_eq_one 0
  refine hyperplane_laplacian_nonneg_e hs hu b ?_ e he
  intro φ hφ x hx hmax
  have h1 := isViscSubsolution_hyperplane hs h2 (b 0) hone φ hφ x hx hmax
  change (fun M : ℝ⁴ →L[ℝ] ℝ⁴ =>
    -((LinearMap.trace ℝ ℝ⁴) M.toLinearMap - ⟪M (b 0), b 0⟫)) (HessOp φ s x) ≤ 0 at h1
  rw [neg_nonpos, sub_nonneg, LinearMap.trace_eq_sum_inner _ b, Fin.sum_univ_succ] at h1
  have hA : ⟪(HessOp φ s x) (b 0), b 0⟫_ℝ
      = ⟪b 0, (HessOp φ s x).toLinearMap (b 0)⟫_ℝ :=
    real_inner_comm (b 0) (HessOp φ s x (b 0))
  rw [hA] at h1
  have h2' : 0 ≤ ∑ i : Fin 3, ⟪HessOp φ s x (b (Fin.succ i)), b (Fin.succ i)⟫_ℝ := by
    have hsum : (∑ i : Fin 3, ⟪b (Fin.succ i), (HessOp φ s x).toLinearMap (b (Fin.succ i))⟫_ℝ)
        = ∑ i : Fin 3, ⟪HessOp φ s x (b (Fin.succ i)), b (Fin.succ i)⟫_ℝ :=
      Finset.sum_congr rfl fun i _ =>
        (real_inner_comm (b (Fin.succ i)) (HessOp φ s x (b (Fin.succ i)))).symm
    linarith [h1, hsum.le, hsum.ge]
  refine le_trans h2' ?_
  refine Finset.sum_le_sum fun i _ => ?_
  unfold HessOp
  rw [Commons.Analysis.Calculus.FDeriv.hessianWithin_apply_second_partial b hs hx hφ (Fin.succ i)
      (Fin.succ i), iteratedFDeriv_two_apply]
  simp

end Submission


