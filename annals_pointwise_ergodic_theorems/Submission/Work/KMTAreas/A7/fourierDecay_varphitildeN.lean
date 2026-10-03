import Mathlib
import Submission.Work.KMTAreas.A7.cw_etaCut_decay

namespace Work.KMTAreas.A7

open MeasureTheory

/-- The fixed cutoff `η = kmtEta` is smooth to every order (it is the complexification of the
`ContDiffBump` `kmtBump`). -/
lemma contDiff_kmtEta_top : ContDiff ℝ (⊤ : ℕ∞) Work.KMTContract.kmtEta :=
  (ContinuousLinearMap.contDiff (n := (⊤ : ℕ∞)) (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)).comp
    (ContDiffBump.contDiff Work.KMTContract.kmtBump (n := ⊤))

/-- **A rescaling of the cutoff is `C²`.**  `ξ ↦ η (a ξ)` is a composition of the smooth `η`
with the linear map `ξ ↦ a ξ`. -/
lemma contDiff_smul_kmtEta (a : ℝ) :
    ContDiff ℝ 2 (fun ξ : ℝ => Work.KMTContract.kmtEta (a * ξ)) :=
  (contDiff_kmtEta_top.comp (contDiff_const.mul contDiff_id)).of_le
    (WithTop.coe_le_coe.mpr le_top)

/-- **A rescaling of the cutoff has compact support.**  For `a > 0` the rescaling `ξ ↦ η (a ξ)`
vanishes for `|ξ| > 1/a`, because `η` vanishes for `|x| ≥ 1`; its support is therefore contained
in the closed ball of radius `a⁻¹`, which is compact. -/
lemma hasCompactSupport_smul_kmtEta {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (fun ξ : ℝ => Work.KMTContract.kmtEta (a * ξ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) a⁻¹) ?_
  intro ξ hξ
  rw [Function.mem_support] at hξ
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h
  rw [not_le] at h
  have h1 : 1 < a * |ξ| := by
    have := mul_lt_mul_of_pos_left h ha
    rwa [mul_inv_cancel₀ (ne_of_gt ha)] at this
  have h2 : 1 ≤ |a * ξ| := by
    rw [abs_mul, abs_of_pos ha]; linarith
  exact hξ (Work.KMTContract.kmtEta_zero h2)

/-- **`φ̃_N` is `C²`.**  Both branches of `varphitildeN` are rescalings `ξ ↦ η (a ξ)` (with
`a > 0`, or a difference of two of them), and `η` is smooth. -/
lemma contDiff_varphitildeN (d N k : ℕ) :
    ContDiff ℝ 2 (Work.KMTAreas.A7.varphitildeN d N k) := by
  unfold Work.KMTAreas.A7.varphitildeN
  split_ifs with hk
  · exact contDiff_smul_kmtEta _
  · exact (contDiff_smul_kmtEta _).sub (contDiff_smul_kmtEta _)

/-- **`φ̃_N` has compact support.**  Each rescaling `ξ ↦ η (a ξ)` (with `a > 0`) is supported in
`[-a⁻¹, a⁻¹]`, and the difference of two compactly supported functions is compactly supported. -/
lemma hasCompactSupport_varphitildeN (d N k : ℕ) :
    HasCompactSupport (Work.KMTAreas.A7.varphitildeN d N k) := by
  unfold Work.KMTAreas.A7.varphitildeN
  split_ifs with hk
  · exact hasCompactSupport_smul_kmtEta (Real.rpow_pos_of_pos (by norm_num) _)
  · exact (hasCompactSupport_smul_kmtEta (Real.rpow_pos_of_pos (by norm_num) _)).sub
      (hasCompactSupport_smul_kmtEta (Real.rpow_pos_of_pos (by norm_num) _))

/-- The Fourier transform of the rescaled KMT bump `φ̃_N` decays like `|x|^{-2}`.  `varphitildeN d N k`
is, for `k = 0`, the single rescaling `ξ ↦ η (2^{d·logN N} ξ)` and otherwise the difference of the
two rescalings `ξ ↦ η (2^{d(logN N - k)} ξ) - η (2^{d(logN N - k)+1} ξ)` of the smooth compactly
supported cutoff `η = Work.KMTContract.kmtEta`.  Each rescaling is `C²` with compact support
(`ContDiff.comp` of `ContDiffBump.contDiff` with `ξ ↦ a * ξ`; support inside `[-1/a, 1/a]` via
`Work.KMTContract.kmtEta_zero`), so `Work.KMTAreas.A7.FourierDecayExplicit` (exactly the same
pattern as the already-proved `Work.KMTAreas.A7.cw_etaCut_decay`, using
`Work.KMTAreas.A7.cw_eq_fourierTransform`) gives the bound; the difference case follows from
linearity of the integral for integrable functions (each summand is continuous with compact
support).  An explicit constant `4 * max (∫ ‖g‖) (∫ ‖iteratedDeriv 2 g‖) + 1` for `g` the whole
`varphitildeN d N k` works directly in the `k ≠ 0` case too if one proves `ContDiff ℝ 2` and
`HasCompactSupport` for the difference. -/
theorem fourierDecay_varphitildeN (d N k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖FourierTransform.fourier (Work.KMTAreas.A7.varphitildeN d N k) x‖ ≤ C / (1 + |x|) ^ 2 := by
  have hcd : ContDiff ℝ 2 (Work.KMTAreas.A7.varphitildeN d N k) :=
    contDiff_varphitildeN d N k
  have hcs : HasCompactSupport (Work.KMTAreas.A7.varphitildeN d N k) :=
    hasCompactSupport_varphitildeN d N k
  refine ⟨4 * max (∫ y, ‖Work.KMTAreas.A7.varphitildeN d N k y‖)
      (∫ y, ‖iteratedDeriv 2 (Work.KMTAreas.A7.varphitildeN d N k) y‖) + 1, ?_, ?_⟩
  · have hA : 0 ≤ ∫ y, ‖Work.KMTAreas.A7.varphitildeN d N k y‖ :=
      integral_nonneg (fun y => norm_nonneg _)
    have hm : 0 ≤ max (∫ y, ‖Work.KMTAreas.A7.varphitildeN d N k y‖)
        (∫ y, ‖iteratedDeriv 2 (Work.KMTAreas.A7.varphitildeN d N k) y‖) :=
      le_max_of_le_left hA
    linarith
  · intro x
    exact FourierDecayExplicit hcd hcs x

end Work.KMTAreas.A7
