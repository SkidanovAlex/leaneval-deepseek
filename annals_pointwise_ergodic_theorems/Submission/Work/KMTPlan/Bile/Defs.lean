/-
# The band-limited lift: definitions

Foundations of the finite-model `bile-2` transfer: the KMT cutoff, its Fourier transform `Psi`,
and the scaled bump `bileChi R` together with its periodisation `bileTheta R`.
-/
import Mathlib
import Submission.Work.KMTContract.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open MeasureTheory
open scoped FourierTransform SchwartzMap BigOperators

namespace Work.KMTPlan.Bile

open Work.Analysis.IonescuWainger

/-! ## The cutoff and its Fourier transform -/

lemma kmtEta_contDiff : ContDiff ℝ (⊤ : ℕ∞) Work.KMTContract.kmtEta := by
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  exact h2.comp (ContDiffBump.contDiff Work.KMTContract.kmtBump (n := ⊤))

lemma kmtEta_compact : HasCompactSupport Work.KMTContract.kmtEta := by
  refine HasCompactSupport.intro (K := Set.Icc (-1:ℝ) 1) isCompact_Icc (fun x hx => ?_)
  have hx' : 1 ≤ |x| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · exact le_trans (by linarith : (1:ℝ) ≤ -x) (neg_le_abs x)
    · exact le_trans h.le (le_abs_self x)
  exact Work.KMTContract.kmtEta_zero hx'

noncomputable def etaS : 𝓢(ℝ, ℂ) := kmtEta_compact.toSchwartzMap kmtEta_contDiff

lemma etaS_coe : (etaS : ℝ → ℂ) = Work.KMTContract.kmtEta := rfl

noncomputable def PsiS : 𝓢(ℝ, ℂ) := FourierTransform.fourier etaS
noncomputable def Psi : ℝ → ℂ := ⇑PsiS

lemma Psi_apply (t : ℝ) : Psi t = 𝓕 Work.KMTContract.kmtEta t := by
  rw [Psi, ← etaS_coe]
  exact congrFun (SchwartzMap.fourier_coe etaS) t

lemma Psi_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (1 + |t|) ^ k * ‖Psi t‖ ≤ C := by
  refine ⟨2 ^ k * max ((Finset.Iic ((k, 0) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℂ m.1 m.2) PsiS) 0 + 1, by positivity, fun t => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0))
    (k := k) (n := 0) le_rfl le_rfl PsiS t
  simp only [norm_iteratedFDeriv_zero] at h
  rw [Real.norm_eq_abs] at h
  refine le_trans h ?_
  have h2 : (2:ℝ)^k * ((Finset.Iic ((k, 0) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℂ m.1 m.2) PsiS) ≤
      2 ^ k * max ((Finset.Iic ((k, 0) : ℕ × ℕ)).sup
        (fun m => SchwartzMap.seminorm ℂ m.1 m.2) PsiS) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  linarith

lemma Psi_fderiv_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (1 + |t|) ^ k * ‖fderiv ℝ Psi t‖ ≤ C := by
  refine ⟨2 ^ k * max ((Finset.Iic ((k, 1) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℂ m.1 m.2) PsiS) 0 + 1, by positivity, fun t => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 1))
    (k := k) (n := 1) le_rfl le_rfl PsiS t
  rw [norm_iteratedFDeriv_one] at h
  rw [Real.norm_eq_abs] at h
  refine le_trans h ?_
  have h2 : (2:ℝ)^k * ((Finset.Iic ((k, 1) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℂ m.1 m.2) PsiS) ≤
      2 ^ k * max ((Finset.Iic ((k, 1) : ℕ × ℕ)).sup
        (fun m => SchwartzMap.seminorm ℂ m.1 m.2) PsiS) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  linarith

lemma Psi_zero_eq : Psi 0 = ∫ x, Work.KMTContract.kmtEta x := by
  rw [Psi_apply]
  have h := Real.fourier_real_eq (f := Work.KMTContract.kmtEta) (w := 0)
  rw [h]
  simp

lemma integral_kmtBump_pos : 0 < ∫ x : ℝ, ((Work.KMTContract.kmtBump : ℝ → ℝ) x) := by
  have hsupp : Function.support (Work.KMTContract.kmtBump : ℝ → ℝ) = Metric.ball (0:ℝ) 1 :=
    ContDiffBump.support_eq _
  have hμ : 0 < volume (Function.support (Work.KMTContract.kmtBump : ℝ → ℝ)) := by
    rw [hsupp, Real.volume_ball]; simp
  have hcont : Continuous (Work.KMTContract.kmtBump : ℝ → ℝ) := ContDiffBump.continuous _
  have hint : Integrable (Work.KMTContract.kmtBump : ℝ → ℝ) :=
    hcont.integrable_of_hasCompactSupport (ContDiffBump.hasCompactSupport _)
  exact (integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => ContDiffBump.nonneg Work.KMTContract.kmtBump))
    hint).mpr hμ

lemma Psi_zero_ne : Psi 0 ≠ 0 := by
  rw [Psi_zero_eq]
  have h : (∫ x, Work.KMTContract.kmtEta x)
      = ((∫ x, (Work.KMTContract.kmtBump : ℝ → ℝ) x : ℝ) : ℂ) := by
    simp only [Work.KMTContract.kmtEta]
    exact integral_ofReal
  rw [h]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt integral_kmtBump_pos

/-! ## The scaled bump and its periodisation -/

noncomputable def bileChi (R : ℝ) : ℝ → ℂ := fun x => (R : ℂ) * Work.KMTContract.kmtEta (R * x)

lemma bileChi_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (bileChi R) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => R * x) := contDiff_const.mul contDiff_id
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (R : ℂ) * z) := contDiff_const.mul contDiff_id
  exact h2.comp (kmtEta_contDiff.comp h1)

lemma bileChi_eq_zero {R : ℝ} {x : ℝ} (hx : 1 ≤ |R * x|) : bileChi R x = 0 := by
  simp only [bileChi, Work.KMTContract.kmtEta_zero hx, mul_zero]

lemma bileChi_summable (R : ℝ) (hR : 0 < R) (x : ℝ) :
    Summable fun j : ℤ => bileChi R (x + j) := by
  refine summable_of_ne_finset_zero
    (s := Finset.Icc (-(⌈|x| + 1/R⌉₊ : ℤ)) (⌈|x| + 1/R⌉₊ : ℤ)) ?_
  intro j hj
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
  have hceil : |x| + 1/R ≤ ((⌈|x| + 1/R⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hjabs : ((⌈|x| + 1/R⌉₊ : ℕ) : ℝ) < |(j:ℝ)| := by
    rcases hj with h | h
    · have h1 : ((⌈|x| + 1/R⌉₊ : ℤ)) < -j := by omega
      have h2 : (((⌈|x| + 1/R⌉₊ : ℤ)) : ℝ) < -(j:ℝ) := by exact_mod_cast h1
      have h3 : (((⌈|x| + 1/R⌉₊ : ℤ)) : ℝ) = ((⌈|x| + 1/R⌉₊ : ℕ) : ℝ) := by push_cast; ring
      rw [h3] at h2
      exact lt_of_lt_of_le h2 (neg_le_abs _)
    · have h1 : ((⌈|x| + 1/R⌉₊ : ℤ)) < j := by omega
      have h2 : (((⌈|x| + 1/R⌉₊ : ℤ)) : ℝ) < (j:ℝ) := by exact_mod_cast h1
      have h3 : (((⌈|x| + 1/R⌉₊ : ℤ)) : ℝ) = ((⌈|x| + 1/R⌉₊ : ℕ) : ℝ) := by push_cast; ring
      rw [h3] at h2
      exact lt_of_lt_of_le h2 (le_abs_self _)
  have hxj : 1/R < |x + (j:ℝ)| := by
    have h3 : |(j:ℝ)| ≤ |x + (j:ℝ)| + |x| := by
      calc |(j:ℝ)| = |(x + (j:ℝ)) - x| := by ring_nf
        _ ≤ |x + (j:ℝ)| + |x| := abs_sub _ _
    linarith
  have : 1 ≤ |R * (x + (j:ℝ))| := by
    rw [abs_mul, abs_of_pos hR]
    have h6 : R * (1/R) < R * |x + (j:ℝ)| := mul_lt_mul_of_pos_left hxj hR
    rw [mul_one_div, div_self (ne_of_gt hR)] at h6
    exact le_of_lt h6
  exact bileChi_eq_zero this

noncomputable def bileTheta (R : ℝ) : Work.Analysis.IonescuWainger.Circle → ℂ :=
  periodize (bileChi R)

lemma bileChi_mem_arc (R : ℝ) (hR : 0 < R) {x : ℝ} (hx : bileChi R x ≠ 0) {k : ℤ}
    (hk : (1:ℝ) / R ≤ (2:ℝ)^k) : x ∈ realArc k := by
  have hne : Work.KMTContract.kmtEta (R * x) ≠ 0 := by
    intro h; exact hx (by simp [bileChi, h])
  have hlt : |R * x| < 1 := by
    by_contra hcon
    exact hne (Work.KMTContract.kmtEta_zero (le_of_not_gt hcon))
  rw [abs_mul, abs_of_pos hR] at hlt
  have hxabs : |x| < 1/R := (lt_div_iff₀ hR).mpr (by linarith [hlt])
  rw [realArc, Set.mem_Icc]
  have h2 : |x| ≤ (2:ℝ)^k := le_of_lt (lt_of_lt_of_le hxabs hk)
  exact ⟨by linarith [neg_le_abs x], le_trans (le_abs_self x) h2⟩

end Work.KMTPlan.Bile
