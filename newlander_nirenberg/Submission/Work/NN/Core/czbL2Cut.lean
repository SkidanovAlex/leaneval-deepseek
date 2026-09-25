/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The radial cut-off used to localise the energy identity

`cutC R` is the smooth radial cut-off `z ↦ cutProfile (nrmSq z / R²)` viewed in `ℂ`.  It equals
`1` on the Euclidean ball of radius `R/√2` and vanishes off the Euclidean ball of radius `R`.
Its Wirtinger derivatives are supported in the Euclidean shell `R/√2 ≤ eucNorm ≤ R` and are
bounded by `K / R`; this file collects those elementary facts.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmKerEpsAux
import Submission.Work.CR.Flat.Cauchy.bmCz.czAux
import Submission.Work.CR.Flat.Cauchy.bmCz.czDifferenceEstimate
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.NN.Core.czbL2_integral_radial_dCoord

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-- The smooth radial cut-off profile: `1` on `(-∞,1/2]` and `0` on `[1,∞)` (as a function of
`nrmSq z / R²`). -/
noncomputable def cutRe {n : ℕ} (R : ℝ) (z : Fin n → ℂ) : ℝ :=
  Work.CR.Flat.Cauchy.cutProfile (Work.CR.Flat.Cauchy.nrmSq z / R ^ 2)

/-- The complexified radial cut-off `z ↦ cutProfile (nrmSq z / R²)`. -/
noncomputable def cutC {n : ℕ} (R : ℝ) (z : Fin n → ℂ) : ℂ :=
  (cutRe (n := n) R z : ℂ)

@[simp] lemma cutC_apply {n : ℕ} (R : ℝ) (z : Fin n → ℂ) :
    cutC R z = (cutRe (n := n) R z : ℂ) := rfl

lemma cutRe_nonneg {n : ℕ} (R : ℝ) (z : Fin n → ℂ) : 0 ≤ cutRe (n := n) R z :=
  cutProfile_nonneg _

lemma cutRe_le_one {n : ℕ} (R : ℝ) (z : Fin n → ℂ) : cutRe (n := n) R z ≤ 1 :=
  cutProfile_le_one _

lemma cutRe_eq_one {n : ℕ} {R : ℝ} {z : Fin n → ℂ} (h : 2 * nrmSq z ≤ R ^ 2) :
    cutRe (n := n) R z = 1 := by
  refine cutProfile_of_two_mul_le_one ?_
  have hR2 : (0:ℝ) ≤ R ^ 2 := sq_nonneg R
  rw [show 2 * (nrmSq z / R ^ 2) = (2 * nrmSq z) / R ^ 2 by ring]
  rcases eq_or_lt_of_le hR2 with h0 | hpos
  · rw [← h0, div_zero]; norm_num
  · rw [div_le_one hpos]; linarith

lemma cutRe_eq_zero {n : ℕ} {R : ℝ} (hR : 0 < R) {z : Fin n → ℂ} (h : R ^ 2 ≤ nrmSq z) :
    cutRe (n := n) R z = 0 := by
  refine cutProfile_of_one_le ?_
  rw [one_le_div (pow_pos hR 2)]
  exact h

/-- The complexified cut-off is `1` on the Euclidean ball of radius `R/√2`. -/
lemma cutC_eq_one {n : ℕ} {R : ℝ} {z : Fin n → ℂ} (h : 2 * (eucNorm z) ^ 2 ≤ R ^ 2) :
    cutC R z = 1 := by
  rw [cutC, cutRe_eq_one (by rwa [nrmSq_eq_eucNorm_sq])]
  exact Complex.ofReal_one

/-- The complexified cut-off vanishes off the Euclidean ball of radius `R`. -/
lemma cutC_eq_zero {n : ℕ} {R : ℝ} (hR : 0 < R) {z : Fin n → ℂ} (h : R ^ 2 ≤ nrmSq z) :
    cutC R z = 0 := by
  rw [cutC, cutRe_eq_zero hR h]
  exact Complex.ofReal_zero

lemma contDiff_cutRe {n : ℕ} (R : ℝ) :
    ContDiff ℝ 1 (fun z : Fin n → ℂ => cutRe (n := n) R z) := by
  have hden : ContDiff ℝ 1 (fun z : Fin n → ℂ => nrmSq z / R ^ 2) :=
    Work.NN.Core.contDiff_one_nrmSq.div_const _
  exact contDiff_cutProfile.comp hden

lemma contDiff_cutC {n : ℕ} (R : ℝ) : ContDiff ℝ 1 (cutC (n := n) R) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_cutRe R)

lemma hasCompactSupport_cutC {n : ℕ} {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutC (n := n) R) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall (0 : Fin n → ℂ) R) (isCompact_closedBall _ _) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hne : cutRe (n := n) R z ≠ 0 := by
    intro h; exact hz (by rw [cutC, h]; simp)
  have hlt : nrmSq z < R ^ 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hne (cutRe_eq_zero hR hcon)
  rw [nrmSq_eq_eucNorm_sq] at hlt
  have := pi_norm_le_eucNorm z
  nlinarith [eucNorm_nonneg z, sq_nonneg (eucNorm z)]

/-! ## Derivatives of the cut-off -/

lemma deriv_cutProfile_eq_zero_of_lt_half {t : ℝ} (ht : t < 1 / 2) :
    deriv Work.CR.Flat.Cauchy.cutProfile t = 0 := by
  have hnb : {s : ℝ | s < 1 / 2} ∈ nhds t :=
    (isOpen_lt continuous_id continuous_const).mem_nhds ht
  have hev : Work.CR.Flat.Cauchy.cutProfile =ᶠ[nhds t] (fun _ => (1:ℝ)) := by
    filter_upwards [hnb] with s hs
    exact cutProfile_of_two_mul_le_one (by linarith)
  rw [hev.deriv_eq]; simp

lemma deriv_cutProfile_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Work.CR.Flat.Cauchy.cutProfile t = 0 := by
  have hnb : {s : ℝ | 1 < s} ∈ nhds t :=
    (isOpen_lt continuous_const continuous_id).mem_nhds ht
  have hev : Work.CR.Flat.Cauchy.cutProfile =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
    filter_upwards [hnb] with s hs
    exact cutProfile_of_one_le (le_of_lt hs)
  rw [hev.deriv_eq]; simp

lemma hasCompactSupport_deriv_cutProfile :
    HasCompactSupport (deriv Work.CR.Flat.Cauchy.cutProfile) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (1/2 : ℝ) 1) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  rw [Set.mem_Icc]
  by_contra h
  rw [not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact ht (deriv_cutProfile_eq_zero_of_lt_half h)
  · exact ht (deriv_cutProfile_eq_zero_of_one_lt h)

lemma exists_bound_deriv_cutProfile :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv Work.CR.Flat.Cauchy.cutProfile t| ≤ K := by
  have hcont : Continuous (deriv Work.CR.Flat.Cauchy.cutProfile) :=
    contDiff_cutProfile.continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hasCompactSupport_deriv_cutProfile
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have := hC t
  rw [Real.norm_eq_abs] at this
  exact le_trans this (le_max_left _ _)

/-- The `(1,0)`-derivative of the complexified cut-off. -/
lemma dCoord_cutC {n : ℕ} (R : ℝ) (j : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (cutC (n := n) R) z
      = ((deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2 : ℝ) : ℂ)
          * star (z j) := by
  have hd : HasDerivAt (fun t : ℝ => Work.CR.Flat.Cauchy.cutProfile (t / R ^ 2))
      (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2) (nrmSq z) := by
    have h1 : HasDerivAt (fun t : ℝ => t / R ^ 2) (1 / R ^ 2) (nrmSq z) :=
      (hasDerivAt_id (nrmSq z)).div_const _
    have h2 : HasDerivAt Work.CR.Flat.Cauchy.cutProfile
        (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) (nrmSq z / R ^ 2) :=
      (contDiff_cutProfile.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have h3 := h2.comp (nrmSq z) h1
    rwa [show deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) * (1 / R ^ 2)
        = deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2 by ring] at h3
  have h := Work.CR.Flat.Cauchy.bmCz.dCoord_comp_nrmSq (n := n) j
    (Φ := fun t : ℝ => Work.CR.Flat.Cauchy.cutProfile (t / R ^ 2))
    (Φ' := deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2) hd
  exact h

/-- The `(0,1)`-derivative of the complexified cut-off. -/
lemma dbarCoord_cutC {n : ℕ} (R : ℝ) (j : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord j (cutC (n := n) R) z
      = ((deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2 : ℝ) : ℂ)
          * z j := by
  have hd : HasDerivAt (fun t : ℝ => Work.CR.Flat.Cauchy.cutProfile (t / R ^ 2))
      (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2) (nrmSq z) := by
    have h1 : HasDerivAt (fun t : ℝ => t / R ^ 2) (1 / R ^ 2) (nrmSq z) :=
      (hasDerivAt_id (nrmSq z)).div_const _
    have h2 : HasDerivAt Work.CR.Flat.Cauchy.cutProfile
        (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) (nrmSq z / R ^ 2) :=
      (contDiff_cutProfile.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have h3 := h2.comp (nrmSq z) h1
    rwa [show deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) * (1 / R ^ 2)
        = deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2 by ring] at h3
  have h := Work.CR.Flat.Cauchy.dbarCoord_comp_nrmSq (n := n) j
    (Φ := fun t : ℝ => Work.CR.Flat.Cauchy.cutProfile (t / R ^ 2))
    (Φ' := deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2) hd
  exact h

/-- The squared modulus of the `(1,0)`-gradient of the cut-off, in closed form. -/
lemma sum_normSq_dCoord_cutC {n : ℕ} {R : ℝ} (z : Fin n → ℂ) :
    ∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2
      = (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) ^ 2 / R ^ 4 * nrmSq z := by
  have hpow : ∀ j : Fin n, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2
      = ((deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) ^ 2 / R ^ 4) * ‖z j‖ ^ 2 := by
    intro j
    rw [dCoord_cutC, norm_mul]
    rw [show ‖((deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2 : ℝ) : ℂ)‖
        = |deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)| / R ^ 2 by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div]; norm_num]
    rw [norm_star, mul_pow, div_pow, sq_abs]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hpow j), ← Finset.mul_sum]
  congr 1

/-- The squared modulus of the `(0,1)`-gradient of the cut-off, in closed form. -/
lemma sum_normSq_dbarCoord_cutC {n : ℕ} {R : ℝ} (z : Fin n → ℂ) :
    ∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2
      = (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) ^ 2 / R ^ 4 * nrmSq z := by
  have hpow : ∀ j : Fin n, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2
      = ((deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) ^ 2 / R ^ 4) * ‖z j‖ ^ 2 := by
    intro j
    rw [dbarCoord_cutC, norm_mul]
    rw [show ‖((deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) / R ^ 2 : ℝ) : ℂ)‖
        = |deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)| / R ^ 2 by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div]; norm_num]
    rw [mul_pow, div_pow, sq_abs]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hpow j), ← Finset.mul_sum]
  congr 1

/-- A uniform bound for the squared modulus of the `(1,0)`-gradient of the cut-off. -/
lemma exists_bound_sum_normSq_dCoord_cutC :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ} (R : ℝ) (z : Fin n → ℂ), 0 < R →
      ∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2 ≤ K / R ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_deriv_cutProfile
  refine ⟨K ^ 2, by positivity, ?_⟩
  intro n R z hR
  rw [sum_normSq_dCoord_cutC z]
  have hR2 : (0:ℝ) < R ^ 2 := pow_pos hR 2
  have hR4 : (0:ℝ) < R ^ 4 := by positivity
  by_cases hle : nrmSq z ≤ R ^ 2
  · have hg : (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) ^ 2 ≤ K ^ 2 := by
      have h := hK (nrmSq z / R ^ 2)
      rw [abs_le] at h
      nlinarith [h.1, h.2]
    rw [div_mul_eq_mul_div]
    calc (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) ^ 2 * nrmSq z / R ^ 4
        ≤ K ^ 2 * R ^ 2 / R ^ 4 := by
          apply div_le_div_of_nonneg_right _ hR4.le
          exact mul_le_mul hg hle (nrmSq_nonneg z) (by positivity)
      _ = K ^ 2 / R ^ 2 := by field_simp
  · have hz : deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) = 0 :=
      deriv_cutProfile_eq_zero_of_one_lt (by rw [one_lt_div hR2]; push_neg at hle; exact hle)
    rw [hz, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, zero_mul]
    positivity

/-- A uniform bound for the squared modulus of the `(0,1)`-gradient of the cut-off. -/
lemma exists_bound_sum_normSq_dbarCoord_cutC :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ} (R : ℝ) (z : Fin n → ℂ), 0 < R →
      ∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2 ≤ K / R ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_deriv_cutProfile
  refine ⟨K ^ 2, by positivity, ?_⟩
  intro n R z hR
  rw [sum_normSq_dbarCoord_cutC z]
  have hR2 : (0:ℝ) < R ^ 2 := pow_pos hR 2
  have hR4 : (0:ℝ) < R ^ 4 := by positivity
  by_cases hle : nrmSq z ≤ R ^ 2
  · have hg : (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) ^ 2 ≤ K ^ 2 := by
      have h := hK (nrmSq z / R ^ 2)
      rw [abs_le] at h
      nlinarith [h.1, h.2]
    rw [div_mul_eq_mul_div]
    calc (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) ^ 2 * nrmSq z / R ^ 4
        ≤ K ^ 2 * R ^ 2 / R ^ 4 := by
          apply div_le_div_of_nonneg_right _ hR4.le
          exact mul_le_mul hg hle (nrmSq_nonneg z) (by positivity)
      _ = K ^ 2 / R ^ 2 := by field_simp
  · have hz : deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2) = 0 :=
      deriv_cutProfile_eq_zero_of_one_lt (by rw [one_lt_div hR2]; push_neg at hle; exact hle)
    rw [hz, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, zero_mul]
    positivity

/-! ## Two support helpers -/

lemma eventuallyEq_zero_of_notMem_tsupport {α E : Type*} [TopologicalSpace α] [Zero E]
    {g : α → E} {z : α} (hz : z ∉ tsupport g) : g =ᶠ[nhds z] 0 := by
  have h : (tsupport g)ᶜ ∈ nhds z :=
    (isClosed_closure : IsClosed (tsupport g)).isOpen_compl.mem_nhds hz
  filter_upwards [h] with w hw
  by_contra hw0
  exact hw (subset_tsupport g (Function.mem_support.mpr hw0))

lemma HasCompactSupport.of_forall_notMem_tsupport {α E F : Type*} [TopologicalSpace α] [R1Space α]
    [Zero E] [Zero F] {f : α → E} {g : α → F} (hg : HasCompactSupport g)
    (h : ∀ z, z ∉ tsupport g → f z = 0) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact hg (fun z hz => by
    by_contra hc
    exact hz (h z hc))


end Work.NN.Core
