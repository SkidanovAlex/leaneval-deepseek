import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BSKinetic.Decomp.ShiftDefs
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.chiSmall_kinFT_decay`

**Scale-sharp Fourier decay of the `dℓ`-scale cosine-`M`-th-power cutoff `chiSmall M`.**

The target is: for all `N, M` with `N + 1 ≤ M` there is a constant `C ≥ 0` such that for every
`0 < ρ ≤ 1`, every shift `u` and every frequency `k`,

    ‖kinFT (χ_M(ρ⁻¹· − u)) k‖ ≤ C ρ³ (1 + ρ‖k‖)^{-N} ,

where `kinFT f k = ∫ e^{−i⟪k,z⟫} f(z) dz` (`Submission.BoseGases.kinFT`) and
`χ_M = chiSmall M = (ζζζ)^M/√∫(ζζζ)^{2M}` is the corpus's cosine-`M`-th-power bump
(`Submission.Work.ChiSmall`), whose support is the unit cube and which is `C^{M−1}` because `ζ^M`
kills the derivative jumps of the cosine profile at the box faces to order `M − 1`.

This is the `ℓ`-free (`chiScale ≡ 1`) counterpart of the sibling
`Work.BoseFixB1S.win.chiSmallB_kinFT_decay`; the single localisation factor is absent, so the
profile in the rescaled variable is just `χ_M` itself.

## Route

1. **`C^N` of `χ_M`** for `N + 1 ≤ M` (`Work.BoseFixB1S.win.contDiff_chiSmallC`) — this is exactly
   where the hypothesis `N + 1 ≤ M` is used.
2. **Uniform derivative bounds** `‖D^j χ_M‖ ≤ chiSmallCBound N M` for `j ≤ N`, and support in the
   closed unit ball, give the two `L¹` bounds `∫‖χ_M‖ ≤ A` and `∫‖D^N χ_M‖ ≤ A` with
   `A = chiSmallCBound N M · vol(ball 1)`.
3. **Fourier decay** of the profile: `‖𝓕 χ_M ξ‖ ≤ 2^N A (1+‖ξ‖)^{-N}`
   (`Work.BoseFixB1S.oneBodyB1.norm_fourier_le_of_integral_iteratedFDeriv`, `N`-fold integration
   by parts); converting `kinFT` to `𝓕` at the frequency `(2π)⁻¹ • q` costs the fixed factor
   `(2π)^N` (`one_add_le_two_pi_mul_inv_smul`).  The case `N = 0` is the bare `L¹` bound.
4. **Rescaling**: the dilation identity `kinFT (· ↦ g(c⁻¹· − u)) p = c³ e^{−i⟪c·p,u⟫} kinFT g (c·p)`
   (`Work.BoseFixB1S.win.kinFT_inv_smul_sub_norm_le`) turns the statement into
   `ρ³ ‖kinFT χ_M (ρ • k)‖` and the decay estimate at `q = ρ • k`.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Real Topology ContDiff BigOperators FourierTransform RealInnerProductSpace

namespace Work.BoseFixB1B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## 1. A support/volume bound for integrals of norms -/

/-- **Support-volume bound.**  If `f` is supported in the closed ball of radius `R` and is
bounded by `B` there, then `∫ ‖f‖ ≤ B · vol(closedBall 0 R)`.  (Copy of the private helper of
`Work.BoseFixB1S.win.chiSmallB_kinFT_decay`, which is not exported.) -/
private lemma integral_norm_le_of_support_closedBall {F : Type*} [NormedAddCommGroup F]
    (f : ℝ³ → F) (R B : ℝ)
    (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) (hb : ∀ z, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∫ z, ‖f z‖ ≤ B * volume.real (Metric.closedBall (0 : ℝ³) R) := by
  have hzero : ∀ z ∉ Metric.closedBall (0 : ℝ³) R, ‖f z‖ = 0 := by
    intro z hz
    have hz' : ¬ ‖z‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    have hfz : f z = 0 := by
      by_contra h
      exact hz' (hsupp z h)
    rw [hfz, norm_zero]
  have hfin : volume (Metric.closedBall (0 : ℝ³) R) < ⊤ :=
    (isCompact_closedBall (0 : ℝ³) R).measure_lt_top
  have h1 : ‖∫ z in Metric.closedBall (0 : ℝ³) R, ‖f z‖‖
      ≤ B * volume.real (Metric.closedBall (0 : ℝ³) R) := by
    refine norm_setIntegral_le_of_norm_le_const hfin (fun z hz => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hb z (by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz)
  have hnn : 0 ≤ ∫ z in Metric.closedBall (0 : ℝ³) R, ‖f z‖ :=
    setIntegral_nonneg measurableSet_closedBall (fun z _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnn] at h1
  calc ∫ z, ‖f z‖ = ∫ z in Metric.closedBall (0 : ℝ³) R, ‖f z‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ B * volume.real (Metric.closedBall (0 : ℝ³) R) := h1

/-! ## 2. Fourier decay of the profile `χ_M` (no dilation, no shift) -/

/-- The `L¹` constant of the profile: `chiSmallCBound N M · vol(ball 1)`, bounding both `∫‖χ_M‖`
and `∫‖D^N χ_M‖`. -/
noncomputable def chiSmallCL1 (N M : ℕ) (hNM : N + 1 ≤ M) : ℝ :=
  Work.BoseFixB1S.win.chiSmallCBound N M hNM *
    volume.real (Metric.closedBall (0 : ℝ³) 1)

lemma chiSmallCL1_nonneg (N M : ℕ) (hNM : N + 1 ≤ M) : 0 ≤ chiSmallCL1 N M hNM :=
  mul_nonneg (Work.BoseFixB1S.win.chiSmallCBound_nonneg N M hNM) measureReal_nonneg

/-- The support containment of `chiSmallC M` in the closed unit ball. -/
lemma chiSmallC_support_le_one {M : ℕ} (hM : 1 ≤ M) {z : ℝ³}
    (hz : Work.BoseFixB1S.win.chiSmallC M z ≠ 0) : ‖z‖ ≤ 1 :=
  Work.BoseFixB1S.win.chiSmall_support_norm_le hM
    (fun h => hz (by simp [Work.BoseFixB1S.win.chiSmallC, h]))

/-- `∫ ‖χ_M‖ ≤ chiSmallCL1 N M hNM`. -/
lemma integral_norm_chiSmallC_le (N M : ℕ) (hNM : N + 1 ≤ M) :
    ∫ z : ℝ³, ‖Work.BoseFixB1S.win.chiSmallC M z‖ ≤ chiSmallCL1 N M hNM := by
  have hM1 : 1 ≤ M := by omega
  have hbd : ∀ z : ℝ³, ‖z‖ ≤ 1 →
      ‖Work.BoseFixB1S.win.chiSmallC M z‖ ≤ Work.BoseFixB1S.win.chiSmallCBound N M hNM := by
    intro z _
    simpa using (Work.BoseFixB1S.win.norm_iteratedFDeriv_chiSmallC_le N M hNM 0 (by omega) z)
  exact integral_norm_le_of_support_closedBall _ 1 _ (fun z hz => chiSmallC_support_le_one hM1 hz)
    hbd

/-- `∫ ‖D^N χ_M‖ ≤ chiSmallCL1 N M hNM`. -/
lemma integral_norm_iteratedFDeriv_chiSmallC_le (N M : ℕ) (hNM : N + 1 ≤ M) :
    ∫ z : ℝ³, ‖iteratedFDeriv ℝ N (Work.BoseFixB1S.win.chiSmallC M) z‖
      ≤ chiSmallCL1 N M hNM := by
  have hM1 : 1 ≤ M := by omega
  have hsup' : ∀ z : ℝ³, iteratedFDeriv ℝ N (Work.BoseFixB1S.win.chiSmallC M) z ≠ 0 →
      ‖z‖ ≤ 1 := by
    intro z hz
    have hmem : z ∈ tsupport (Work.BoseFixB1S.win.chiSmallC M) :=
      support_iteratedFDeriv_subset (𝕜 := ℝ) N (Function.mem_support.mpr hz)
    have hsub : tsupport (Work.BoseFixB1S.win.chiSmallC M) ⊆ Metric.closedBall (0 : ℝ³) 1 :=
      closure_minimal (fun y hy => by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact chiSmallC_support_le_one hM1 (Function.mem_support.mp hy)) isClosed_closedBall
    have h := hsub hmem
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  have hbd : ∀ z : ℝ³, ‖z‖ ≤ 1 →
      ‖iteratedFDeriv ℝ N (Work.BoseFixB1S.win.chiSmallC M) z‖
        ≤ Work.BoseFixB1S.win.chiSmallCBound N M hNM :=
    fun z _ => Work.BoseFixB1S.win.norm_iteratedFDeriv_chiSmallC_le N M hNM N le_rfl z
  exact integral_norm_le_of_support_closedBall _ 1 _ hsup' hbd

/-- The `N = 0` decay: the bare `L¹` bound for `kinFT χ_M`. -/
lemma chiSmallC_kinFT_decay_zero (M : ℕ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ³,
      ‖kinFT (Work.BoseFixB1S.win.chiSmallC M) q‖ ≤ C / (1 + ‖q‖) ^ 0 := by
  have hNM : 0 + 1 ≤ M := by omega
  refine ⟨chiSmallCL1 0 M hNM, chiSmallCL1_nonneg 0 M hNM, fun q => ?_⟩
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, pow_zero, div_one]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm (𝕜 := ℝ) Real.fourierChar volume
    (innerₗ ℝ³) (Work.BoseFixB1S.win.chiSmallC M) ((2 * Real.pi)⁻¹ • q)).trans
    (integral_norm_chiSmallC_le 0 M hNM)

/-- **Fourier decay of `χ_M`**: `‖kinFT χ_M q‖ ≤ C (1 + ‖q‖)^{-N}` for `N + 1 ≤ M`. -/
lemma chiSmallC_kinFT_decay_aux (N M : ℕ) (hNM : N + 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ³,
      ‖kinFT (Work.BoseFixB1S.win.chiSmallC M) q‖ ≤ C / (1 + ‖q‖) ^ N := by
  have hM1 : 1 ≤ M := by omega
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    exact chiSmallC_kinFT_decay_zero M hM1
  · refine ⟨2 ^ N * chiSmallCL1 N M hNM * (2 * Real.pi) ^ N, ?_, fun q => ?_⟩
    · exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) N) (chiSmallCL1_nonneg N M hNM))
        (pow_nonneg (by positivity) N)
    · have hdec := Work.BoseFixB1S.oneBodyB1.norm_fourier_le_of_integral_iteratedFDeriv N hNpos
        (Work.BoseFixB1S.win.chiSmallC M) (chiSmallCL1 N M hNM) (chiSmallCL1_nonneg N M hNM)
        (Work.BoseFixB1S.win.contDiff_chiSmallC N M hNM)
        (Work.BoseFixB1S.win.chiSmallC_hasCompactSupport hM1)
        (integral_norm_chiSmallC_le N M hNM)
        (integral_norm_iteratedFDeriv_chiSmallC_le N M hNM) ((2 * Real.pi)⁻¹ • q)
      rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
      refine hdec.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc 2 ^ N * chiSmallCL1 N M hNM * (1 + ‖q‖) ^ N
          ≤ 2 ^ N * chiSmallCL1 N M hNM *
              ((2 * Real.pi) ^ N * (1 + ‖((2 * Real.pi)⁻¹ : ℝ) • q‖) ^ N) :=
            mul_le_mul_of_nonneg_left (Work.BoseFixB1S.win.one_add_le_two_pi_mul_inv_smul N q)
              (mul_nonneg (pow_nonneg (by norm_num) N) (chiSmallCL1_nonneg N M hNM))
        _ = 2 ^ N * chiSmallCL1 N M hNM * (2 * Real.pi) ^ N *
              (1 + ‖((2 * Real.pi)⁻¹ : ℝ) • q‖) ^ N := by ring

/-! ## 3. The target -/

theorem chiSmall_kinFT_decay (N M : ℕ) (hNM : N + 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (u k : EuclideanSpace ℝ (Fin 3)),
      ‖Submission.BoseGases.kinFT
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            ((Submission.BoseGases.chiSmall M ((ρ⁻¹ : ℝ) • z - u) : ℝ) : ℂ)) k‖
        ≤ C * ρ ^ 3 / (1 + ρ * ‖k‖) ^ N := by
  obtain ⟨C, hC0, hC⟩ := chiSmallC_kinFT_decay_aux N M hNM
  refine ⟨C, hC0, fun ρ hρ _ u k => ?_⟩
  have hfun : (fun z : ℝ³ => ((chiSmall M ((ρ⁻¹ : ℝ) • z - u) : ℝ) : ℂ))
      = fun z : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (ρ⁻¹ • z - u) := by
    funext z
    rfl
  rw [hfun]
  refine (Work.BoseFixB1S.win.kinFT_inv_smul_sub_norm_le (Work.BoseFixB1S.win.chiSmallC M)
    hρ u k).trans ?_
  have hb := hC (ρ • k)
  have hnorm : ‖ρ • k‖ = ρ * ‖k‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  calc ρ ^ 3 * ‖kinFT (Work.BoseFixB1S.win.chiSmallC M) (ρ • k)‖
      ≤ ρ ^ 3 * (C / (1 + ‖ρ • k‖) ^ N) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hρ.le 3)
    _ = C * ρ ^ 3 / (1 + ρ * ‖k‖) ^ N := by
        rw [hnorm]
        ring

end Work.BoseFixB1B
