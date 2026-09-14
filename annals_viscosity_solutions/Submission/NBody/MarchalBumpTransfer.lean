import Submission.NBody.MarchalBump
import Submission.NBody.MarchalBumpGeometric
import Submission.NBody.MarchalDerivBound

/-!
# The transfer identity of the symmetric bump

The engine of the standard-variation argument (`Submission/ROADMAP.md`, SESSION 29): the real
action difference of the symmetric bump, expressed in the *rescaled* coordinates of the colliding
cluster.  Writing `q^λ(s) = λ^{-2/3}·(cmRel ∘ γ)(t₀ + λs)` for the blow-up of `γ` at the collision
time `t₀`, `d(s) = stdCoef δ T s · stdPertVec m k i₀ δ` for the standard variation and
`γ̃ = bumpCurve m k i₀ δ T λ t₀ γ` for the competitor, the action difference on the right window is

  `A(γ̃) - A(γ) = λ^{1/3}·( kinetic + cluster-potential difference of `q^λ` and `q^λ + d` )
                   + λ·( interaction-potential difference )`.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- The shifted curve `u ↦ γ (t₀ + u)`. -/
noncomputable def shiftCurve (γ : ℝ → EN E N) (t₀ : ℝ) : ℝ → EN E N := fun u => γ (t₀ + u)

@[simp] lemma shiftCurve_apply (γ : ℝ → EN E N) (t₀ u : ℝ) : shiftCurve γ t₀ u = γ (t₀ + u) := rfl

lemma deriv_shiftCurve (γ : ℝ → EN E N) (t₀ x : ℝ) :
    deriv (shiftCurve γ t₀) x = deriv γ (t₀ + x) :=
  deriv_comp_const_add γ t₀ x

/-- The rescaled curve attached to the right-hand side of the collision time. -/
noncomputable def bumpRescaled (m : Fin N → ℝ) (k : Finset (Fin N)) (γ : ℝ → EN E N)
    (t₀ lam : ℝ) : ℝ → EN E N := rescaledCentered m k (shiftCurve γ t₀) lam

/-- The standard perturbation, as a function of the rescaled time. -/
noncomputable def stdVarVec (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (δ : E) (T : ℝ) :
    ℝ → EN E N := fun s => stdCoef δ T s • stdPertVec m k i₀ δ

/-- Its almost-everywhere derivative. -/
noncomputable def stdVarVecDeriv (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (δ : E)
    (T : ℝ) : ℝ → EN E N :=
  fun s => if s ≤ T - ‖δ‖ then 0 else (-(‖δ‖)⁻¹) • stdPertVec m k i₀ δ

lemma stdVarVec_eq_stdPert (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (δ : E) (T : ℝ) :
    stdVarVec m k i₀ δ T = stdPert m k i₀ δ T := by
  funext s
  exact (stdPert_eq_smul_stdPertVec δ T s).symm

lemma deriv_stdVarVec_ae (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (δ : E) (T : ℝ)
    (hδ : δ ≠ 0) :
    (fun s : ℝ => deriv (stdVarVec m k i₀ δ T) s)
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)] (stdVarVecDeriv m k i₀ δ T) := by
  rw [stdVarVec_eq_stdPert]
  exact deriv_stdPert_ae δ T hδ

/-- The bump, evaluated at the shifted time `t₀ + lam s`: it is `lam^{2/3}` times the standard
variation. -/
lemma bumpPert_shift {δ : E} {lam T t₀ : ℝ} (hlam : 0 < lam) (u₀ : EN E N) {s : ℝ} (hs : 0 ≤ s) :
    bumpPert δ T lam t₀ u₀ (t₀ + lam * s) = lam ^ ((2:ℝ)/3) • (stdCoef δ T s • u₀) := by
  rw [bumpPert]
  have h1 : |t₀ + lam * s - t₀| = lam * s := by
    rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg hlam.le hs)]
  rw [h1, mul_div_cancel_left₀ s hlam.ne', smul_smul,
    mul_comm (stdCoef δ T s) (lam ^ ((2:ℝ)/3)), ← smul_smul]

/-- The competitor at the shifted time. -/
lemma bumpCurve_shift {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} {δ : E}
    {lam T t₀ : ℝ} (hlam : 0 < lam) {γ : ℝ → EN E N} {s : ℝ} (hs : 0 ≤ s) :
    bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)
      = γ (t₀ + lam * s) + lam ^ ((2:ℝ)/3) • stdVarVec m k i₀ δ T s := by
  rw [bumpCurve, bumpPert_shift hlam (stdPertVec m k i₀ δ) hs, stdVarVec]

/-- The derivative of the shifted curve. -/
lemma deriv_shift_mul (γ : ℝ → EN E N) (t₀ lam x : ℝ) :
    deriv (fun s : ℝ => γ (t₀ + lam * s)) x = lam • deriv γ (t₀ + lam * x) := by
  rw [deriv_comp_mul_left lam (fun u : ℝ => γ (t₀ + u)) x, deriv_comp_const_add]

end Submission.NBody

namespace Submission.NBody

open Commons.MeasureTheory.Integral

lemma lipschitzWith_stdVarVec {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} {δ : E}
    (hδ : δ ≠ 0) (T : ℝ) :
    LipschitzWith (⟨(‖δ‖)⁻¹ * ‖stdPertVec m k i₀ δ‖, by positivity⟩ : NNReal)
      (stdVarVec m k i₀ δ T) := by
  have hd : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  have h2 : LipschitzWith (⟨(‖δ‖)⁻¹, inv_nonneg.mpr (norm_nonneg δ)⟩ : NNReal) (stdCoef δ T) :=
    lipschitzWith_stdCoef hδ T
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 : stdVarVec m k i₀ δ T x - stdVarVec m k i₀ δ T y
      = (stdCoef δ T x - stdCoef δ T y) • stdPertVec m k i₀ δ := by
    rw [stdVarVec, stdVarVec, ← sub_smul]
  have h3 : dist (stdCoef δ T x) (stdCoef δ T y)
      ≤ (↑(⟨(‖δ‖)⁻¹, inv_nonneg.mpr (norm_nonneg δ)⟩ : NNReal) : ℝ) * dist x y :=
    h2.dist_le_mul x y
  rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs]
  have h4 : dist (stdCoef δ T x) (stdCoef δ T y) = |stdCoef δ T x - stdCoef δ T y| := by
    rw [Real.dist_eq]
  rw [← h4]
  push_cast
  calc |stdCoef δ T x - stdCoef δ T y| * ‖stdPertVec m k i₀ δ‖
      ≤ ((‖δ‖)⁻¹ * dist x y) * ‖stdPertVec m k i₀ δ‖ :=
        mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ = ((‖δ‖)⁻¹ * ‖stdPertVec m k i₀ δ‖) * dist x y := by ring

end Submission.NBody

namespace Submission.NBody

/-- **The almost-everywhere derivative of the bumped curve, in shifted coordinates.** -/
lemma deriv_shift_bump_ae {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} {δ : E}
    {lam T t₀ : ℝ} {γ : ℝ → EN E N} (hlam : 0 < lam) (hT : 0 < T) (hδ : δ ≠ 0)
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T)) :
    (fun s : ℝ => deriv (fun u : ℝ => bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * u)) s)
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)]
    (fun s : ℝ => lam • deriv γ (t₀ + lam * s)
      + lam ^ ((2:ℝ)/3) • stdVarVecDeriv m k i₀ δ T s) := by
  have hcomp : AbsolutelyContinuousOnInterval (fun u : ℝ => γ (t₀ + lam * u)) 0 T := by
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ) (a := t₀) (b := t₀ + lam * T) (c := lam) (d := t₀) hlam.ne' hac
    have h1 : (fun t : ℝ => γ (lam * t + t₀)) = (fun u : ℝ => γ (t₀ + lam * u)) := by
      funext t; rw [add_comm]
    rw [h1, sub_self, zero_div, add_sub_cancel_left, mul_div_cancel_left₀ T hlam.ne'] at h
    exact h
  have hAae : ∀ᵐ s ∂volume.restrict (Set.Ioc (0:ℝ) T),
      DifferentiableAt ℝ (fun u : ℝ => γ (t₀ + lam * u)) s := by
    have h1 := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector
      hcomp
    filter_upwards [MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self h1,
      MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s h1s hs
    exact h1s (by rw [Set.uIcc_of_le hT.le]; exact Set.Ioc_subset_Icc_self hs)
  have hBae : ∀ᵐ s ∂volume.restrict (Set.Ioc (0:ℝ) T),
      DifferentiableAt ℝ (stdVarVec m k i₀ δ T) s :=
    MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self
      (lipschitzWith_stdVarVec hδ T).ae_differentiableAt
  have hpt : ∀ s ∈ Set.Ioc (0:ℝ) T,
      deriv (fun u : ℝ => bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * u)) s
        = deriv (fun u : ℝ =>
            γ (t₀ + lam * u) + lam ^ ((2:ℝ)/3) • stdVarVec m k i₀ δ T u) s := by
    intro s hs
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hs.1] with u hu
    exact bumpCurve_shift hlam hu.le
  filter_upwards [hAae, hBae, MeasureTheory.ae_restrict_mem measurableSet_Ioc,
    deriv_stdVarVec_ae m k i₀ δ T hδ] with s hA hB hs hdv
  rw [hpt s hs]
  have hB2 : DifferentiableAt ℝ
      (fun u : ℝ => lam ^ ((2:ℝ)/3) • stdVarVec m k i₀ δ T u) s :=
    hB.const_smul (lam ^ ((2:ℝ)/3))
  have h1 : deriv (fun u : ℝ => γ (t₀ + lam * u) + lam ^ ((2:ℝ)/3) • stdVarVec m k i₀ δ T u) s
      = deriv (fun u : ℝ => γ (t₀ + lam * u)) s
        + deriv (fun u : ℝ => lam ^ ((2:ℝ)/3) • stdVarVec m k i₀ δ T u) s :=
    deriv_add hA hB2
  rw [h1, deriv_shift_mul]
  have hBderiv : deriv (fun u : ℝ => lam ^ ((2:ℝ)/3) • stdVarVec m k i₀ δ T u) s
      = lam ^ ((2:ℝ)/3) • stdVarVecDeriv m k i₀ δ T s := by
    rw [show (fun u : ℝ => lam ^ ((2:ℝ)/3) • stdVarVec m k i₀ δ T u)
        = lam ^ ((2:ℝ)/3) • (stdVarVec m k i₀ δ T) from rfl]
    rw [deriv_const_smul _ hB, hdv]
  rw [hBderiv]

end Submission.NBody

namespace Submission.NBody

lemma clusterCM_add (m : Fin N → ℝ) (k : Finset (Fin N)) (x y : EN E N) :
    clusterCM m k (x + y) = clusterCM m k x + clusterCM m k y := by
  simp only [clusterCM, PiLp.add_apply, smul_add, Finset.sum_add_distrib]

lemma clusterCM_smul (m : Fin N → ℝ) (k : Finset (Fin N)) (c : ℝ) (x : EN E N) :
    clusterCM m k (c • x) = c • clusterCM m k x := by
  have hsum : (∑ i ∈ k, m i • ((c • x : EN E N) i)) = c • ∑ i ∈ k, m i • x i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.smul_apply, smul_comm]
  rw [clusterCM, hsum, clusterCM, smul_comm]

lemma cmRel_add (m : Fin N → ℝ) (k : Finset (Fin N)) (x y : EN E N) :
    cmRel m k (x + y) = cmRel m k x + cmRel m k y := by
  refine PiLp.ext fun i => ?_
  by_cases hi : i ∈ k
  · simp only [PiLp.add_apply, cmRel_apply_of_mem hi, clusterCM_add]
    abel
  · rw [PiLp.add_apply, cmRel_apply_of_notMem hi, cmRel_apply_of_notMem hi,
      cmRel_apply_of_notMem hi, add_zero]

lemma cmRel_smul (m : Fin N → ℝ) (k : Finset (Fin N)) (c : ℝ) (x : EN E N) :
    cmRel m k (c • x) = c • cmRel m k x := by
  refine PiLp.ext fun i => ?_
  by_cases hi : i ∈ k
  · simp only [PiLp.smul_apply, cmRel_apply_of_mem hi, clusterCM_smul]
    rw [smul_sub]
  · rw [PiLp.smul_apply, cmRel_apply_of_notMem hi, cmRel_apply_of_notMem hi, smul_zero]

lemma clusterCM_stdPertVec {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) (v : E) : clusterCM m k (stdPertVec m k i₀ v) = 0 := by
  rw [clusterCM, stdPertVec_centred hm hi₀ v, smul_zero]

lemma cmRel_stdVarVec {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) (δ : E) (T : ℝ) (s : ℝ) :
    cmRel m k (stdVarVec m k i₀ δ T s) = stdVarVec m k i₀ δ T s := by
  rw [stdVarVec, cmRel_smul]
  congr 1
  refine PiLp.ext fun i => ?_
  by_cases hi : i ∈ k
  · rw [cmRel_apply_of_mem hi, clusterCM_stdPertVec hm hi₀, sub_zero]
  · rw [cmRel_apply_of_notMem hi, stdPertVec_apply_of_notMem hi]

lemma cmRel_bumpCurve_shift {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) {δ : E} {lam T t₀ : ℝ} (hlam : 0 < lam) {γ : ℝ → EN E N} {s : ℝ}
    (hs : 0 ≤ s) :
    cmRel m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
      = cmRel m k (γ (t₀ + lam * s)) + lam ^ ((2:ℝ)/3) • stdVarVec m k i₀ δ T s := by
  rw [bumpCurve_shift hlam hs, cmRel_add, cmRel_smul, cmRel_stdVarVec hm hi₀]

lemma bumpRescaled_shift {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) {δ : E} {lam T t₀ : ℝ} (hlam : 0 < lam) {γ : ℝ → EN E N} {s : ℝ} (hs : 0 ≤ s) :
    lam ^ (-(2:ℝ)/3) • cmRel m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
      = bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s := by
  rw [bumpCurve_shift hlam hs, cmRel_add, cmRel_smul, cmRel_stdVarVec hm hi₀, smul_add,
    smul_smul, ← Real.rpow_add hlam, show (-(2:ℝ)/3) + ((2:ℝ)/3) = 0 by norm_num,
    Real.rpow_zero, one_smul]
  congr 1
  rw [bumpRescaled, rescaledCentered, shiftCurve, mul_comm]

end Submission.NBody

namespace Submission.NBody

/-- The cluster potential of a configuration is `λ^{-2/3}` times the cluster potential of the
rescaled centred configuration. -/
lemma clusterPotential_scaled {m : Fin N → ℝ} {k : Finset (Fin N)} {lam : ℝ} (hlam : 0 < lam)
    {x : EN E N} :
    clusterPotential m k x
      = lam ^ (-(2:ℝ)/3) * clusterPotential m k (lam ^ (-(2:ℝ)/3) • cmRel m k x) := by
  have hc : (0:ℝ) < lam ^ (-(2:ℝ)/3) := Real.rpow_pos_of_pos hlam _
  have hinv : (lam ^ (-(2:ℝ)/3))⁻¹ = lam ^ ((2:ℝ)/3) := by
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg hlam.le, inv_inv]
  rw [clusterPotential_smul, clusterPotential_cmRel, abs_of_pos hc, hinv, ← mul_assoc,
    ← Real.rpow_add hlam, show (-(2:ℝ)/3) + ((2:ℝ)/3) = 0 by norm_num, Real.rpow_zero, one_mul]

/-- The rescaled centred configuration of the bumped curve at the shifted time. -/
lemma bumpRescaled_apply {m : Fin N → ℝ} {k : Finset (Fin N)} {γ : ℝ → EN E N} {t₀ lam s : ℝ} :
    bumpRescaled m k γ t₀ lam s
      = lam ^ (-(2:ℝ)/3) • cmRel m k (γ (t₀ + lam * s)) := by
  rw [bumpRescaled, rescaledCentered, shiftCurve, mul_comm]

end Submission.NBody

namespace Submission.NBody

/-- `cmRel m k` as a linear map. -/
noncomputable def cmRelLM (m : Fin N → ℝ) (k : Finset (Fin N)) : EN E N →ₗ[ℝ] EN E N where
  toFun := cmRel m k
  map_add' x y := cmRel_add m k x y
  map_smul' c x := cmRel_smul m k c x

/-- `cmRel m k` as a continuous linear map (the space is finite-dimensional). -/
noncomputable def cmRelL (m : Fin N → ℝ) (k : Finset (Fin N)) : EN E N →L[ℝ] EN E N :=
  (cmRelLM m k).toContinuousLinearMap

lemma cmRelL_apply (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    cmRelL m k x = cmRel m k x := rfl

/-- The chain rule for `cmRel`. -/
lemma hasDerivAt_cmRel_comp {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {t : ℝ}
    {v : EN E N} (h : HasDerivAt x v t) :
    HasDerivAt (fun u : ℝ => cmRel m k (x u)) (cmRel m k v) t := by
  have hL := (cmRelL m k).hasFDerivAt.comp_hasDerivAt t h
  rw [cmRelL_apply] at hL
  exact hL

end Submission.NBody

namespace Submission.NBody

lemma absolutelyContinuousOnInterval_shift_mul {γ : ℝ → EN E N} {t₀ lam T : ℝ} (hlam : 0 < lam)
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T)) :
    AbsolutelyContinuousOnInterval (fun s : ℝ => γ (t₀ + lam * s)) 0 T := by
  have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
    (f := γ) (a := t₀) (b := t₀ + lam * T) (c := lam) (d := t₀) hlam.ne' hac
  have h1 : (fun t : ℝ => γ (lam * t + t₀)) = (fun u : ℝ => γ (t₀ + lam * u)) := by
    funext t; rw [add_comm]
  rw [h1, sub_self, zero_div, add_sub_cancel_left, mul_div_cancel_left₀ T hlam.ne'] at h
  exact h

lemma ae_differentiableAt_shift_mul {γ : ℝ → EN E N} {t₀ lam T : ℝ} (hlam : 0 < lam)
    (hT : 0 < T) (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T)) :
    ∀ᵐ s ∂volume.restrict (Set.Ioc (0:ℝ) T),
      DifferentiableAt ℝ (fun u : ℝ => γ (t₀ + lam * u)) s := by
  have h1 := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector
    (absolutelyContinuousOnInterval_shift_mul hlam hac)
  filter_upwards [MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self h1,
    MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s h1s hs
  exact h1s (by rw [Set.uIcc_of_le hT.le]; exact Set.Ioc_subset_Icc_self hs)

/-- **The derivative of the rescaled curve**, almost everywhere. -/
lemma deriv_bumpRescaled_ae {m : Fin N → ℝ} {k : Finset (Fin N)} {γ : ℝ → EN E N}
    {t₀ lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T)) :
    (fun s : ℝ => deriv (bumpRescaled m k γ t₀ lam) s)
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)]
    (fun s : ℝ => lam ^ ((1:ℝ)/3) • cmRel m k (deriv γ (t₀ + lam * s))) := by
  filter_upwards [ae_differentiableAt_shift_mul hlam hT hac] with s hA
  have hdA : HasDerivAt (fun u : ℝ => γ (t₀ + lam * u))
      (deriv (fun u : ℝ => γ (t₀ + lam * u)) s) s := hasDerivAt_deriv_iff.mpr hA
  have hcomp' : HasDerivAt (fun u : ℝ => cmRel m k (γ (t₀ + lam * u)))
      (cmRel m k (deriv (fun u : ℝ => γ (t₀ + lam * u)) s)) s :=
    hasDerivAt_cmRel_comp hdA
  have hderiv : deriv (fun u : ℝ => cmRel m k (γ (t₀ + lam * u))) s
      = cmRel m k (deriv (fun u : ℝ => γ (t₀ + lam * u)) s) := hcomp'.deriv
  have heqfun : bumpRescaled m k γ t₀ lam
      = fun u : ℝ => lam ^ (-(2:ℝ)/3) • cmRel m k (γ (t₀ + lam * u)) := by
    funext u; rw [bumpRescaled_apply, mul_comm]
  have hscal : lam ^ (-(2:ℝ)/3) * lam = lam ^ ((1:ℝ)/3) := by
    have h1 : lam ^ (-(2:ℝ)/3) * lam ^ (1:ℝ) = lam ^ ((1:ℝ)/3) := by
      rw [← Real.rpow_add hlam]; norm_num
    rwa [Real.rpow_one] at h1
  have hd1 : deriv (fun u : ℝ => lam ^ (-(2:ℝ)/3) • cmRel m k (γ (t₀ + lam * u))) s
      = lam ^ (-(2:ℝ)/3) • deriv (fun u : ℝ => cmRel m k (γ (t₀ + lam * u))) s := by
    rw [show (fun u : ℝ => lam ^ (-(2:ℝ)/3) • cmRel m k (γ (t₀ + lam * u)))
        = lam ^ (-(2:ℝ)/3) • (fun u : ℝ => cmRel m k (γ (t₀ + lam * u))) from rfl]
    rw [deriv_const_smul _ hcomp'.differentiableAt]
  rw [heqfun, hd1, hderiv, deriv_shift_mul, cmRel_smul, smul_smul, hscal]

end Submission.NBody

namespace Submission.NBody

/-- A vector supported in `k` and centred can be moved to either side of the mass inner product. -/
lemma massInner_cmRel_left {m : Fin N → ℝ} {k : Finset (Fin N)} {v w : EN E N}
    (hw : ∑ j ∈ k, m j • w j = 0) (hwsupp : ∀ j, j ∉ k → w j = 0) :
    massInner m (cmRel m k v) w = massInner m v w := by
  rw [massInner_cmRel_eq' m k v w]
  have hsupp : massInner m v w = ∑ i ∈ k, m i * ⟪v i, w i⟫_ℝ := by
    rw [massInner]
    exact (Finset.sum_subset (Finset.subset_univ k) (fun i _ hi => by
      rw [hwsupp i hi]; simp)).symm
  rw [hsupp, Finset.sum_congr rfl (fun i _ => by rw [inner_sub_left, mul_sub]),
    Finset.sum_sub_distrib]
  have hC : (∑ i ∈ k, m i * ⟪clusterCM m k v, w i⟫_ℝ)
      = ⟪clusterCM m k v, ∑ i ∈ k, m i • w i⟫_ℝ := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_right]
  rw [hC, hw, inner_zero_right, sub_zero]

/-- `stdPertVec` is supported inside `k`. -/
lemma stdPertVec_supp {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} (v : E) :
    ∀ j, j ∉ k → stdPertVec m k i₀ v j = 0 :=
  fun j hj => stdPertVec_apply_of_notMem hj v

/-- `stdVarVecDeriv` is of the form "constant times `stdPertVec`". -/
lemma massInner_stdVarVecDeriv {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) (δ : E) (T : ℝ) (s : ℝ) (v : EN E N) :
    massInner m v (stdVarVecDeriv m k i₀ δ T s)
      = massInner m (cmRel m k v) (stdVarVecDeriv m k i₀ δ T s) := by
  have hcent : ∀ c : ℝ, ∑ j ∈ k, m j • (c • (stdPertVec m k i₀ δ) j) = 0 := by
    intro c
    rw [Finset.sum_congr rfl (fun j _ => by rw [smul_comm]), ← Finset.smul_sum,
      stdPertVec_centred hm hi₀, smul_zero]
  simp only [stdVarVecDeriv]
  by_cases h : s ≤ T - ‖δ‖
  · rw [if_pos h, massInner, massInner]
    simp
  · rw [if_neg h]
    have hsupp : ∀ j, j ∉ k → ((-(‖δ‖)⁻¹) • stdPertVec m k i₀ δ : EN E N) j = 0 := by
      intro j hj; rw [PiLp.smul_apply, stdPertVec_apply_of_notMem hj, smul_zero]
    exact (massInner_cmRel_left (hcent _) hsupp).symm

end Submission.NBody

namespace Submission.NBody

/-- The derivative of the bumped curve at the shifted time. -/
lemma deriv_bumpCurve_shift_ae {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} {δ : E}
    {lam T t₀ : ℝ} {γ : ℝ → EN E N} (hlam : 0 < lam) (hT : 0 < T) (hδ : δ ≠ 0)
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T)) :
    (fun s : ℝ => deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)]
    (fun s : ℝ => deriv γ (t₀ + lam * s)
      + lam ^ (-(1:ℝ)/3) • deriv (stdVarVec m k i₀ δ T) s) := by
  have h1 := deriv_shift_bump_ae (m := m) (k := k) (i₀ := i₀) (δ := δ) hlam hT hδ hac
  filter_upwards [h1, deriv_stdVarVec_ae m k i₀ δ T hδ] with s hs hdv
  have h2 : deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s)
      = lam⁻¹ • deriv (fun u : ℝ => bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * u)) s := by
    have h3 : deriv (fun u : ℝ => bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * u)) s
        = lam • deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s) :=
      deriv_shift_mul (bumpCurve m k i₀ δ T lam t₀ γ) t₀ lam s
    rw [h3, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  rw [h2, hs, smul_add, smul_smul, smul_smul,
    show lam⁻¹ * lam = 1 by field_simp, show lam⁻¹ * lam ^ ((2:ℝ)/3) = lam ^ (-(1:ℝ)/3) by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hlam]; norm_num,
    one_smul, hdv]

/-- The potential part of the action difference. -/
lemma bump_potential_diff {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) {δ : E} {lam T t₀ : ℝ} (hlam : 0 < lam) {γ : ℝ → EN E N} {s : ℝ}
    (hs : 0 ≤ s) :
    U m (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)) - U m (γ (t₀ + lam * s))
      = lam ^ (-(2:ℝ)/3) *
          (clusterPotential m k (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)
            - clusterPotential m k (bumpRescaled m k γ t₀ lam s))
        + (clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
            - clusterPotentialRest m k (γ (t₀ + lam * s))) := by
  rw [U_eq_clusterPotential_add_rest m k
      (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)),
    U_eq_clusterPotential_add_rest m k (γ (t₀ + lam * s))]
  have h1 : clusterPotential m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
      = lam ^ (-(2:ℝ)/3) *
          clusterPotential m k (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s) := by
    rw [clusterPotential_scaled hlam, bumpRescaled_shift hm hi₀ hlam hs]
  have h2 : clusterPotential m k (γ (t₀ + lam * s))
      = lam ^ (-(2:ℝ)/3) * clusterPotential m k (bumpRescaled m k γ t₀ lam s) := by
    rw [clusterPotential_scaled hlam, bumpRescaled_apply]
  rw [h1, h2]
  ring

end Submission.NBody

namespace Submission.NBody

/-- The kinetic part of the action difference of the symmetric bump. -/
lemma bump_kinetic_diff_ae {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} {lam T t₀ : ℝ} {γ : ℝ → EN E N} (hlam : 0 < lam)
    (hT : 0 < T) (hδ : δ ≠ 0) (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T)) :
    (fun s : ℝ => (1 / 2) * (‖deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s)‖_[m] ^ 2
                      - ‖deriv γ (t₀ + lam * s)‖_[m] ^ 2))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)]
    (fun s : ℝ => lam ^ (-(2:ℝ)/3) *
        (massInner m (deriv (bumpRescaled m k γ t₀ lam) s) (deriv (stdVarVec m k i₀ δ T) s)
          + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)) := by
  have hmnn : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hcube : lam ^ (-(1:ℝ)/3) * lam ^ (-(1:ℝ)/3) = lam ^ (-(2:ℝ)/3) := by
    rw [← Real.rpow_add hlam]; norm_num
  have hsquare : (lam ^ (-(1:ℝ)/3)) ^ 2 = lam ^ (-(2:ℝ)/3) := by rw [sq, hcube]
  filter_upwards [deriv_bumpCurve_shift_ae (m := m) (k := k) (i₀ := i₀) (δ := δ) hlam hT hδ hac,
    deriv_bumpRescaled_ae (m := m) (k := k) hlam hT hac,
    deriv_stdVarVec_ae m k i₀ δ T hδ] with s hbv hq hd
  set v : EN E N := deriv γ (t₀ + lam * s) with hv
  set a : EN E N := deriv (stdVarVec m k i₀ δ T) s with ha
  have haeq : a = stdVarVecDeriv m k i₀ δ T s := hd
  have hmass : massInner m v a = massInner m (cmRel m k v) a := by
    rw [haeq]
    exact massInner_stdVarVecDeriv hm hi₀ δ T s v
  have hcm : massInner m (cmRel m k v) a
      = lam ^ (-(1:ℝ)/3) * massInner m (deriv (bumpRescaled m k γ t₀ lam) s) a := by
    have hone : lam ^ (-(1:ℝ)/3) * lam ^ ((1:ℝ)/3) = 1 := by
      rw [← Real.rpow_add hlam]; norm_num
    rw [hq, massInner_smul_left hmnn, ← mul_assoc, hone, one_mul]
  have hmass' : massInner m v a
      = lam ^ (-(1:ℝ)/3) * massInner m (deriv (bumpRescaled m k γ t₀ lam) s) a := by
    rw [hmass, hcm]
  have hpol : ‖v + lam ^ (-(1:ℝ)/3) • a‖_[m] ^ 2
      = ‖v‖_[m] ^ 2 + 2 * (lam ^ (-(1:ℝ)/3)) * massInner m v a
        + (lam ^ (-(1:ℝ)/3)) ^ 2 * ‖a‖_[m] ^ 2 :=
    weightedNorm_add_smul_sq hmnn v a (lam ^ (-(1:ℝ)/3))
  have hkey : lam ^ (-(1:ℝ)/3)
        * (lam ^ (-(1:ℝ)/3) * massInner m (deriv (bumpRescaled m k γ t₀ lam) s) a)
      = lam ^ (-(2:ℝ)/3) * massInner m (deriv (bumpRescaled m k γ t₀ lam) s) a := by
    rw [← mul_assoc, hcube]
  rw [hbv, hpol, hmass', hsquare]
  nlinarith [hkey]

end Submission.NBody

namespace Submission.NBody

lemma weightedNorm_sq_eq_sum {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v : EN E N) :
    ‖v‖_[m] ^ 2 = ∑ i, m i * ‖v i‖ ^ 2 := by
  rw [weightedNorm_eq_norm_massScale hm, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [massScale_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hm i)]

lemma lagR_eq {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (h : ℝ) (x v : EN E N) :
    lagR m h x v = (1 / 2) * ‖v‖_[m] ^ 2 + U m x + h := by
  rw [lagR, weightedNorm_sq_eq_sum hm]

/-- **The Lagrangian difference of the symmetric bump, in rescaled coordinates.** -/
theorem bump_lagR_diff_ae {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ h : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    {γ : ℝ → EN E N} (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T)) :
    (fun s : ℝ =>
        lagR m h (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
              (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
        - lagR m h (γ (t₀ + lam * s)) (deriv γ (t₀ + lam * s)))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)]
    (fun s : ℝ =>
        lam ^ (-(2:ℝ)/3) *
          (massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
              (deriv (stdVarVec m k i₀ δ T) s)
            + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
            + (clusterPotential m k
                  (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)
                - clusterPotential m k (bumpRescaled m k γ t₀ lam s)))
        + (clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
            - clusterPotentialRest m k (γ (t₀ + lam * s)))) := by
  filter_upwards [bump_kinetic_diff_ae hm hi₀ hlam hT hδ hac,
    MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hkin hs
  rw [lagR_eq (fun i => (hm i).le), lagR_eq (fun i => (hm i).le)]
  have hsplit : (1 / 2) * ‖deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s)‖_[m] ^ 2
        + U m (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)) + h
        - ((1 / 2) * ‖deriv γ (t₀ + lam * s)‖_[m] ^ 2 + U m (γ (t₀ + lam * s)) + h)
      = (1 / 2) * (‖deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s)‖_[m] ^ 2
            - ‖deriv γ (t₀ + lam * s)‖_[m] ^ 2)
        + (U m (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)) - U m (γ (t₀ + lam * s))) := by
    ring
  rw [hsplit, hkin, bump_potential_diff hm hi₀ hlam hs.1.le]
  ring

end Submission.NBody

namespace Submission.NBody

/-- **The transfer identity**: the real action difference of the symmetric bump on the right
window equals `λ^{1/3}` times the rescaled (kinetic + cluster potential) difference, plus `λ` times
the interaction-potential difference. -/
theorem bump_real_action_eq {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ h : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    {γ : ℝ → EN E N} (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    (h1 : IntervalIntegrable (fun s : ℝ => massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
      (deriv (stdVarVec m k i₀ δ T) s)) volume (0:ℝ) T)
    (h2 : IntervalIntegrable (fun s : ℝ => ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2) volume 0 T)
    (h3 : IntervalIntegrable (fun s : ℝ => clusterPotential m k
      (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)) volume 0 T)
    (h4 : IntervalIntegrable (fun s : ℝ => clusterPotential m k
      (bumpRescaled m k γ t₀ lam s)) volume 0 T)
    (h5 : IntervalIntegrable (fun s : ℝ => clusterPotentialRest m k
      (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))) volume 0 T)
    (h6 : IntervalIntegrable (fun s : ℝ => clusterPotentialRest m k
      (γ (t₀ + lam * s))) volume 0 T) :
    ∫ t in t₀..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
          - lagR m h (γ t) (deriv γ t))
      = lam ^ ((1:ℝ)/3) *
          ((∫ s in (0:ℝ)..T, massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
              (deriv (stdVarVec m k i₀ δ T) s))
           + (1 / 2) * (∫ s in (0:ℝ)..T, ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
           + ((∫ s in (0:ℝ)..T, clusterPotential m k
                (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s))
              - (∫ s in (0:ℝ)..T, clusterPotential m k (bumpRescaled m k γ t₀ lam s))))
        + lam * ((∫ s in (0:ℝ)..T, clusterPotentialRest m k
                (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)))
            - (∫ s in (0:ℝ)..T, clusterPotentialRest m k (γ (t₀ + lam * s)))) := by
  have hthird : lam * lam ^ (-(2:ℝ)/3) = lam ^ ((1:ℝ)/3) := by
    have h1 : lam ^ (1:ℝ) * lam ^ (-(2:ℝ)/3) = lam ^ ((1:ℝ)/3) := by
      rw [← Real.rpow_add hlam]; norm_num
    rwa [Real.rpow_one] at h1
  have hkey : ∫ t in t₀..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
          - lagR m h (γ t) (deriv γ t))
      = lam * ∫ s in (0:ℝ)..T,
          (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
              (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
            - lagR m h (γ (t₀ + lam * s)) (deriv γ (t₀ + lam * s))) := by
    set F : ℝ → ℝ := fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
          - lagR m h (γ t) (deriv γ t) with hF
    have hmul := intervalIntegral.integral_comp_mul_add (a := (0:ℝ)) (b := T) F hlam.ne' t₀
    rw [mul_zero, zero_add, add_comm (lam * T) t₀, smul_eq_mul] at hmul
    have hcongr : (∫ x in (0:ℝ)..T, F (lam * x + t₀))
        = ∫ s in (0:ℝ)..T, F (t₀ + lam * s) := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [add_comm]
    rw [hcongr, hF] at hmul
    rw [hmul, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
  rw [hkey]
  have hcongr : ∫ s in (0:ℝ)..T,
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
          - lagR m h (γ (t₀ + lam * s)) (deriv γ (t₀ + lam * s)))
      = ∫ s in (0:ℝ)..T,
        (lam ^ (-(2:ℝ)/3) *
          (massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
              (deriv (stdVarVec m k i₀ δ T) s)
            + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
            + (clusterPotential m k
                  (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)
                - clusterPotential m k (bumpRescaled m k γ t₀ lam s)))
        + (clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
            - clusterPotentialRest m k (γ (t₀ + lam * s)))) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hT.le]
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp
      (bump_lagR_diff_ae (h := h) hm hi₀ hδ hlam hT hac)
  rw [hcongr]
  have hsum : IntervalIntegrable (fun s : ℝ =>
      massInner m (deriv (bumpRescaled m k γ t₀ lam) s) (deriv (stdVarVec m k i₀ δ T) s)
      + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
      + (clusterPotential m k (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)
          - clusterPotential m k (bumpRescaled m k γ t₀ lam s))) volume (0:ℝ) T :=
    (h1.add (h2.const_mul (1 / 2))).add (h3.sub h4)
  rw [intervalIntegral.integral_add (hsum.const_mul (lam ^ (-(2:ℝ)/3))) (h5.sub h6),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (h1.add (h2.const_mul (1 / 2))) (h3.sub h4),
    intervalIntegral.integral_add h1 (h2.const_mul (1 / 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub h3 h4,
    intervalIntegral.integral_sub h5 h6, mul_add]
  rw [show lam ^ ((1:ℝ)/3) = lam * lam ^ (-(2:ℝ)/3) from hthird.symm]
  ring

end Submission.NBody


namespace Submission.NBody

/-- **The transfer identity, difference form.**  Same as `bump_real_action_eq`, but the two
integrability hypotheses for the interaction potential are replaced by the single hypothesis that
the *difference* is interval integrable, and the corresponding term on the right is the integral of
that difference.  This is the form needed in the multi-class situation, where the interaction
potential itself is not bounded (other clusters collide at the same time) but its variation under
the bump is. -/
theorem bump_real_action_eq_diff {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ h : ℝ} (hlam : 0 < lam)
    (hT : 0 < T)
    {γ : ℝ → EN E N} (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    (h1 : IntervalIntegrable (fun s : ℝ => massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
      (deriv (stdVarVec m k i₀ δ T) s)) volume (0:ℝ) T)
    (h2 : IntervalIntegrable (fun s : ℝ => ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2) volume 0 T)
    (h3 : IntervalIntegrable (fun s : ℝ => clusterPotential m k
      (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)) volume 0 T)
    (h4 : IntervalIntegrable (fun s : ℝ => clusterPotential m k
      (bumpRescaled m k γ t₀ lam s)) volume 0 T)
    (h56 : IntervalIntegrable (fun s : ℝ => clusterPotentialRest m k
      (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
        - clusterPotentialRest m k (γ (t₀ + lam * s))) volume 0 T) :
    ∫ t in t₀..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
          - lagR m h (γ t) (deriv γ t))
      = lam ^ ((1:ℝ)/3) *
          ((∫ s in (0:ℝ)..T, massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
              (deriv (stdVarVec m k i₀ δ T) s))
           + (1 / 2) * (∫ s in (0:ℝ)..T, ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
           + ((∫ s in (0:ℝ)..T, clusterPotential m k
                (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s))
              - (∫ s in (0:ℝ)..T, clusterPotential m k (bumpRescaled m k γ t₀ lam s))))
        + lam * (∫ s in (0:ℝ)..T, (clusterPotentialRest m k
                (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
            - clusterPotentialRest m k (γ (t₀ + lam * s)))) := by
  have hthird : lam * lam ^ (-(2:ℝ)/3) = lam ^ ((1:ℝ)/3) := by
    have h1 : lam ^ (1:ℝ) * lam ^ (-(2:ℝ)/3) = lam ^ ((1:ℝ)/3) := by
      rw [← Real.rpow_add hlam]; norm_num
    rwa [Real.rpow_one] at h1
  have hkey : ∫ t in t₀..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
          - lagR m h (γ t) (deriv γ t))
      = lam * ∫ s in (0:ℝ)..T,
          (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
              (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
            - lagR m h (γ (t₀ + lam * s)) (deriv γ (t₀ + lam * s))) := by
    set F : ℝ → ℝ := fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
          - lagR m h (γ t) (deriv γ t) with hF
    have hmul := intervalIntegral.integral_comp_mul_add (a := (0:ℝ)) (b := T) F hlam.ne' t₀
    rw [mul_zero, zero_add, add_comm (lam * T) t₀, smul_eq_mul] at hmul
    have hcongr : (∫ x in (0:ℝ)..T, F (lam * x + t₀))
        = ∫ s in (0:ℝ)..T, F (t₀ + lam * s) := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [add_comm]
    rw [hcongr, hF] at hmul
    rw [hmul, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
  rw [hkey]
  have hcongr : ∫ s in (0:ℝ)..T,
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
          - lagR m h (γ (t₀ + lam * s)) (deriv γ (t₀ + lam * s)))
      = ∫ s in (0:ℝ)..T,
        (lam ^ (-(2:ℝ)/3) *
          (massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
              (deriv (stdVarVec m k i₀ δ T) s)
            + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
            + (clusterPotential m k
                  (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)
                - clusterPotential m k (bumpRescaled m k γ t₀ lam s)))
        + (clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
            - clusterPotentialRest m k (γ (t₀ + lam * s)))) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hT.le]
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp
      (bump_lagR_diff_ae (h := h) hm hi₀ hδ hlam hT hac)
  rw [hcongr]
  have hsum : IntervalIntegrable (fun s : ℝ =>
      massInner m (deriv (bumpRescaled m k γ t₀ lam) s) (deriv (stdVarVec m k i₀ δ T) s)
      + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
      + (clusterPotential m k (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)
          - clusterPotential m k (bumpRescaled m k γ t₀ lam s))) volume (0:ℝ) T :=
    (h1.add (h2.const_mul (1 / 2))).add (h3.sub h4)
  rw [intervalIntegral.integral_add (hsum.const_mul (lam ^ (-(2:ℝ)/3))) h56,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (h1.add (h2.const_mul (1 / 2))) (h3.sub h4),
    intervalIntegral.integral_add h1 (h2.const_mul (1 / 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub h3 h4, mul_add]
  rw [show lam ^ ((1:ℝ)/3) = lam * lam ^ (-(2:ℝ)/3) from hthird.symm]
  ring

end Submission.NBody
