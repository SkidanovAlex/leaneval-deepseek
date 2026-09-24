import Mathlib
import Submission.Commons.Analysis.Calculus.exists_schwartzMap_eq_of_contDiff_hasCompactSupport
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled
import Submission.Commons.NumberTheory.DirichletPolynomial.weighted_window_reflection

open Finset Real Filter
open scoped BigOperators Topology

set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.DirichletPolynomial

noncomputable section

def prW (N : ℕ) : ℝ := Real.sqrt (N : ℝ)

def prChi (N : ℕ) (y : ℝ) : ℝ :=
  Real.smoothTransition (((y - (N : ℝ)) / prW N) + 1) *
    Real.smoothTransition ((((2 * N : ℝ) - y) / prW N) + 1)

def prRho (N : ℕ) (y : ℝ) : ℝ :=
  (N : ℝ) / 4 + (y - (N : ℝ) / 4) * Real.smoothTransition ((4 * y - (N : ℝ)) / (N : ℝ))

def prG (N : ℕ) (τ : ℝ) (y : ℝ) : ℂ :=
  (((Real.sqrt (prRho N y) : ℝ) : ℂ))⁻¹ * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log (prRho N y) : ℂ))) *
    (prChi N y : ℂ)

lemma prW_pos {N : ℕ} (hN : 1 ≤ N) : 0 < prW N := by
  rw [prW]; exact Real.sqrt_pos.mpr (by exact_mod_cast hN)

lemma prW_nonneg (N : ℕ) : 0 ≤ prW N := Real.sqrt_nonneg _

lemma prChi_nonneg (N : ℕ) (y : ℝ) : 0 ≤ prChi N y := by
  unfold prChi; exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma prChi_le_one (N : ℕ) (y : ℝ) : prChi N y ≤ 1 := by
  unfold prChi
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

lemma prChi_eq_one {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (h1 : (N : ℝ) ≤ y) (h2 : y ≤ 2 * N) :
    prChi N y = 1 := by
  have hW : 0 < prW N := prW_pos hN
  unfold prChi
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · have : 0 ≤ (2 * (N : ℝ) - y) / prW N := div_nonneg (by linarith) (le_of_lt hW)
    linarith
  · have : 0 ≤ (y - (N : ℝ)) / prW N := div_nonneg (by linarith) (le_of_lt hW)
    linarith

lemma prChi_eq_zero_of_le {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (h : y ≤ (N : ℝ) - prW N) :
    prChi N y = 0 := by
  have hW : 0 < prW N := prW_pos hN
  unfold prChi
  rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
  have : (y - (N : ℝ)) / prW N ≤ -1 := by
    rw [div_le_iff₀ hW]; linarith
  linarith

lemma prChi_eq_zero_of_ge {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (h : (2 * N : ℝ) + prW N ≤ y) :
    prChi N y = 0 := by
  have hW : 0 < prW N := prW_pos hN
  unfold prChi
  rw [mul_eq_zero]
  right
  rw [Real.smoothTransition.zero_of_nonpos]
  have : ((2 * N : ℝ) - y) / prW N ≤ -1 := by
    rw [div_le_iff₀ hW]; linarith
  linarith

lemma prChi_contDiff (N : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prChi N) := by
  unfold prChi
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp (((contDiff_id.sub contDiff_const).div_const _).add contDiff_const)
  · exact Real.smoothTransition.contDiff.comp (((contDiff_const.sub contDiff_id).div_const _).add contDiff_const)

lemma prChi_hasCompactSupport (N : ℕ) (hN : 1 ≤ N) : HasCompactSupport (prChi N) := by
  refine HasCompactSupport.intro (K := Set.Icc ((N : ℝ) - prW N) ((2 * N : ℝ) + prW N))
    (isCompact_Icc) (fun x hx => ?_)
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact prChi_eq_zero_of_le hN (le_of_lt hx)
  · exact prChi_eq_zero_of_ge hN (le_of_lt hx)

/-- `prRho N y ≥ N/4`. -/
lemma prRho_ge {N : ℕ} (y : ℝ) : (N : ℝ) / 4 ≤ prRho N y := by
  unfold prRho
  by_cases h : y ≤ (N : ℝ) / 4
  · have hs : Real.smoothTransition ((4 * y - (N : ℝ)) / (N : ℝ)) = 0 := by
      rw [Real.smoothTransition.zero_of_nonpos]
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · simp [h0]
      · have hNpos : (0:ℝ) < N := by exact_mod_cast h0
        rw [div_nonpos_iff]
        exact Or.inr ⟨by linarith, le_of_lt hNpos⟩
    rw [hs, mul_zero, add_zero]
  · have h0 : 0 ≤ (y - (N : ℝ) / 4) := by push_neg at h; linarith
    have h1 : 0 ≤ Real.smoothTransition ((4 * y - (N : ℝ)) / (N : ℝ)) := Real.smoothTransition.nonneg _
    have := mul_nonneg h0 h1
    linarith

lemma prRho_eq_self {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : (N : ℝ) / 2 ≤ y) : prRho N y = y := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hs : Real.smoothTransition ((4 * y - (N : ℝ)) / (N : ℝ)) = 1 := by
    rw [Real.smoothTransition.one_of_one_le]
    rw [le_div_iff₀ hNpos]; linarith
  unfold prRho
  rw [hs]
  ring

lemma prRho_contDiff (N : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prRho N) := by
  unfold prRho
  apply ContDiff.add contDiff_const
  apply ContDiff.mul (contDiff_id.sub contDiff_const)
  exact Real.smoothTransition.contDiff.comp (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const _)

lemma prRho_pos {N : ℕ} (hN : 1 ≤ N) (y : ℝ) : 0 < prRho N y := by
  have h2 : (0:ℝ) < (N:ℝ)/4 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    linarith
  exact lt_of_lt_of_le h2 (prRho_ge (N := N) y)

lemma prRho_ne_zero {N : ℕ} (hN : 1 ≤ N) (y : ℝ) : prRho N y ≠ 0 :=
  ne_of_gt (prRho_pos hN y)

lemma prG_contDiff (N : ℕ) (τ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prG N τ) := by
  rcases eq_or_ne N 0 with h0 | h0
  · subst h0
    have : prG 0 τ = fun _ => 0 := by
      funext y; unfold prG prRho; simp
    rw [this]; exact contDiff_const
  · have hN1 : 1 ≤ N := by omega
    have hne : ∀ y, prRho N y ≠ 0 := prRho_ne_zero hN1
    unfold prG
    refine ContDiff.mul (ContDiff.mul ?_ ?_) ?_
    · rw [contDiff_iff_contDiffAt]
      intro x
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : ℝ => ((Real.sqrt (prRho N y) : ℝ) : ℂ)) x :=
        (Complex.ofRealCLM.contDiff.contDiffAt).comp x
          ((prRho_contDiff N).contDiffAt.sqrt (hne x))
      exact h1.inv (by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact ne_of_gt (Real.sqrt_pos.mpr (prRho_pos hN1 x)))
    · apply Complex.contDiff_exp.comp
      rw [contDiff_iff_contDiffAt]
      intro x
      refine ContDiffAt.mul contDiffAt_const ?_
      refine ContDiffAt.mul contDiffAt_const ?_
      exact (Complex.ofRealCLM.contDiff.contDiffAt).comp x
        ((Real.contDiffAt_log.mpr (hne x)).comp x (prRho_contDiff N).contDiffAt)
    · rw [contDiff_iff_contDiffAt]
      intro x
      exact (Complex.ofRealCLM.contDiff.contDiffAt).comp x (prChi_contDiff N).contDiffAt

/-- On the support of `prChi`, the clamp is the identity. -/
lemma prG_eq_of_mem {N : ℕ} (hN : 4 ≤ N) (τ : ℝ) {y : ℝ}
    (hy : (N : ℝ) - prW N ≤ y) :
    prG N τ y = (((Real.sqrt y : ℝ) : ℂ))⁻¹ * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log y : ℂ))) *
      (prChi N y : ℂ) := by
  have hN1 : 1 ≤ N := by omega
  have hy2 : (N : ℝ) / 2 ≤ y := by
    have hW : prW N ≤ (N : ℝ) / 2 := by
      rw [prW]
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have h4 : (4:ℝ) ≤ N := by exact_mod_cast hN
        nlinarith
    linarith
  unfold prG
  rw [prRho_eq_self hN1 hy2]

lemma prG_support {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    Function.support (prG N τ) ⊆ Set.Icc ((N : ℝ) - prW N) ((2 * N : ℝ) + prW N) := by
  intro y hy
  simp only [Function.mem_support] at hy
  by_contra hc
  simp only [Set.mem_Icc, not_and_or, not_le] at hc
  rcases hc with hc | hc
  · have h1 : prChi N y = 0 := prChi_eq_zero_of_le hN (le_of_lt hc)
    unfold prG at hy
    rw [h1] at hy
    simp at hy
  · have h1 : prChi N y = 0 := prChi_eq_zero_of_ge hN (le_of_lt hc)
    unfold prG at hy
    rw [h1] at hy
    simp at hy

lemma prG_hasCompactSupport (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) : HasCompactSupport (prG N τ) :=
  HasCompactSupport.intro (K := Set.Icc ((N : ℝ) - prW N) ((2 * N : ℝ) + prW N))
    isCompact_Icc (fun x hx => by
      by_contra h
      exact hx (prG_support hN τ h))

private lemma fourier_schwartz_eq (F : SchwartzMap ℝ ℂ) (n : ℤ) :
    (FourierTransform.fourier F) n =
      ∫ y : ℝ, F y * Complex.exp (-(2 * Real.pi * Complex.I) * ((n : ℝ) * y)) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

theorem pr_poisson (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) :
    (∑' n : ℤ, prG N τ (n : ℝ)) =
      ∑' m : ℤ, (∫ y : ℝ, prG N τ y * Complex.exp (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y))) := by
  obtain ⟨F, hF⟩ := Commons.Analysis.Calculus.exists_schwartzMap_eq_of_contDiff_hasCompactSupport
    (prG_contDiff N τ) (prG_hasCompactSupport N hN τ)
  have key := SchwartzMap.tsum_eq_tsum_fourier F 0
  simp only [zero_add] at key
  rw [show (∑' n : ℤ, F (n : ℝ)) = ∑' n : ℤ, prG N τ (n : ℝ) from tsum_congr fun n => hF _] at key
  rw [key]
  refine tsum_congr fun m => ?_
  rw [fourier_schwartz_eq]
  have hf0 : (fourier m) (↑(0 : ℝ) : AddCircle (1 : ℝ)) = 1 := by
    rw [fourier_apply]; simp
  rw [hf0, mul_one]
  congr 1
  funext y
  rw [hF]

/-- The complex power `n^{iτ}` rewritten as an exponential of the phase. -/
lemma cpow_I_mul_eq_exp (n : ℕ) (hn : 1 ≤ n) (τ : ℝ) :
    (n : ℂ) ^ (Complex.I * (τ : ℂ)) =
      Complex.exp (Complex.I * (((τ * Real.log (n : ℝ)) : ℝ) : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this.ne'
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_log (show (0:ℝ) ≤ (n:ℝ) by exact_mod_cast (Nat.zero_le n))).symm
  rw [hlog]
  congr 1
  push_cast
  ring

/-- On `[N,2N]`, `prG` reproduces the summand of the reflected Dirichlet sum. -/
lemma prG_nat_eq {N : ℕ} (hN : 4 ≤ N) (τ : ℝ) {n : ℕ} (hn : N ≤ n) (hn2 : n ≤ 2 * N) :
    prG N τ (n : ℝ) =
      (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ) := by
  have hN1 : 1 ≤ N := by omega
  have hW : prW N ≤ (N : ℝ) := by
    have h4 : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have hs : (0:ℝ) ≤ prW N := prW_nonneg N
    have hsq : (prW N)^2 = (N:ℝ) := by rw [prW, Real.sq_sqrt (by positivity)]
    nlinarith [hs, hsq, h4]
  have hn1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmem : (N : ℝ) - prW N ≤ (n : ℝ) := le_trans (sub_le_self _ (prW_nonneg N)) hn1
  have e1 : prG N τ (n : ℝ) =
      (((Real.sqrt (n : ℝ)) : ℂ))⁻¹ *
        Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (n : ℝ)) : ℂ))) := by
    rw [prG_eq_of_mem hN τ hmem, prChi_eq_one hN1 hn1 (by exact_mod_cast hn2),
      Complex.ofReal_one, mul_one]
  have e2 : (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((τ * Real.log (n : ℝ)) : ℝ) : ℂ)) :=
    cpow_I_mul_eq_exp n (by omega) τ
  have e3 : Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (n : ℝ)) : ℂ))) =
      Complex.exp (Complex.I * (((τ * Real.log (n : ℝ)) : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [e1, e2, e3, div_eq_mul_inv]
  ring

/-- `prW N ≤ N` for `N ≥ 1`. -/
lemma prW_le_self {N : ℕ} (hN : 1 ≤ N) : prW N ≤ (N : ℝ) := by
  have h4 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs : (0:ℝ) ≤ prW N := prW_nonneg N
  have hsq : (prW N)^2 = (N:ℝ) := by rw [prW, Real.sq_sqrt (by positivity)]
  nlinarith [hs, hsq, h4]

/-- The `tsum` of `prG` is the finite sum over the integers in its support. -/
lemma prG_tsum_eq_sum {N : ℕ} (hN : 4 ≤ N) (τ : ℝ) :
    (∑' n : ℤ, prG N τ (n : ℝ)) =
      ∑ n ∈ Finset.Icc (⌈(N : ℝ) - prW N⌉) (⌊(2 * N : ℝ) + prW N⌋),
        prG N τ (n : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  refine tsum_eq_sum (s := Finset.Icc (⌈(N : ℝ) - prW N⌉) (⌊(2 * N : ℝ) + prW N⌋))
    (fun n hn => ?_)
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  have hzero : prChi N (n : ℝ) = 0 := by
    rcases hn with hn | hn
    · apply prChi_eq_zero_of_le (N := N) hN1
      have h := (Int.lt_ceil (z := n) (a := (N : ℝ) - prW N)).mp hn
      exact le_of_lt h
    · apply prChi_eq_zero_of_ge (N := N) hN1
      have h := (Int.floor_lt (z := n) (a := (2 * N : ℝ) + prW N)).mp hn
      exact le_of_lt h
  unfold prG
  rw [hzero]
  simp

/-- The integers inside `[N,2N]`. -/
def prInd (N : ℕ) : Finset ℤ := Finset.Icc (N : ℤ) (2 * (N : ℤ))

/-- The integers inside the support of the window. -/
def prSup (N : ℕ) : Finset ℤ := Finset.Icc (⌈(N : ℝ) - prW N⌉) (⌊(2 * N : ℝ) + prW N⌋)

lemma prG_tsum_eq_sum' {N : ℕ} (hN : 4 ≤ N) (τ : ℝ) :
    (∑' n : ℤ, prG N τ (n : ℝ)) = ∑ n ∈ prSup N, prG N τ (n : ℝ) := by
  have h := prG_tsum_eq_sum hN τ
  unfold prSup
  exact h

lemma prInd_subset_prSup {N : ℕ} (hN : 4 ≤ N) : prInd N ⊆ prSup N := by
  intro n hn
  unfold prInd at hn
  rw [Finset.mem_Icc] at hn
  unfold prSup
  rw [Finset.mem_Icc]
  constructor
  · have hn1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    exact (Int.ceil_le).mpr (by linarith [prW_nonneg N])
  · have hn2 : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn.2
    exact (Int.le_floor).mpr (by linarith [prW_nonneg N])

lemma norm_prG_le {N : ℕ} (hN : 1 ≤ N) (τ y : ℝ) : ‖prG N τ y‖ ≤ 2 / Real.sqrt N := by
  have hpos : (0:ℝ) < prRho N y := prRho_pos hN y
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have h1 : ‖(((Real.sqrt (prRho N y) : ℝ)) : ℂ)⁻¹‖ = (Real.sqrt (prRho N y))⁻¹ := by
    rw [norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : ‖Complex.exp (Complex.I * ((τ : ℂ) * (Real.log (prRho N y) : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have h3 : ‖((prChi N y : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_of_nonneg (prChi_nonneg N y)]
    exact prChi_le_one N y
  have key : ‖prG N τ y‖ ≤ (Real.sqrt (prRho N y))⁻¹ := by
    calc ‖prG N τ y‖ = (Real.sqrt (prRho N y))⁻¹ * ‖((prChi N y : ℝ) : ℂ)‖ := by
          unfold prG; rw [norm_mul, norm_mul, h1, h2]; ring
      _ ≤ (Real.sqrt (prRho N y))⁻¹ * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (Real.sqrt (prRho N y))⁻¹ := mul_one _
  refine le_trans key ?_
  have h4 : (N:ℝ)/4 ≤ prRho N y := prRho_ge (N := N) y
  have h5 : Real.sqrt ((N:ℝ)/4) ≤ Real.sqrt (prRho N y) := Real.sqrt_le_sqrt h4
  have h6 : Real.sqrt ((N:ℝ)/4) = Real.sqrt N / 2 := by
    rw [show (N:ℝ)/4 = (N:ℝ) * (1/4) by ring, Real.sqrt_mul (by positivity)]
    rw [show Real.sqrt (1/4:ℝ) = 1/2 by
      rw [show (1/4:ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  have h7 : (0:ℝ) < Real.sqrt (prRho N y) := Real.sqrt_pos.mpr hpos
  rw [h6] at h5
  have h5' : Real.sqrt N / 2 ≤ Real.sqrt (prRho N y) := h5
  have h8 : (Real.sqrt (prRho N y))⁻¹ ≤ 2 / Real.sqrt N := by
    have h9 : (Real.sqrt N / 2)⁻¹ = 2 / Real.sqrt N := by rw [inv_div]
    rw [← h9]
    exact (inv_le_inv₀ h7 (by positivity)).mpr h5'
  exact h8

lemma extra_bound {N : ℕ} (hN : 4 ≤ N) (τ : ℝ) :
    ‖∑ n ∈ prSup N \ prInd N, prG N τ (n : ℝ)‖ ≤ 6 := by
  have hN1 : 1 ≤ N := by omega
  set G1 : Finset ℤ := Finset.Icc (⌈(N : ℝ) - prW N⌉) ((N : ℤ) - 1) with hG1
  set G2 : Finset ℤ := Finset.Icc ((2 * (N : ℤ)) + 1) (⌊(2 * N : ℝ) + prW N⌋) with hG2
  have hsub : prSup N \ prInd N ⊆ G1 ∪ G2 := by
    intro n hn
    simp only [prSup, prInd, Finset.mem_sdiff, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    push Not at h3
    simp only [Finset.mem_union, hG1, hG2, Finset.mem_Icc]
    rcases lt_or_ge n (N : ℤ) with h | h
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr ⟨by omega, h2⟩
  have hdisj : Disjoint G1 G2 := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    rw [hG1, Finset.mem_Icc] at h1
    rw [hG2, Finset.mem_Icc] at h2
    omega
  have hc1 : ((G1.card : ℕ) : ℝ) ≤ prW N := by
    rw [hG1, Int.card_Icc]
    have h2 : (0:ℤ) ≤ (N : ℤ) - ⌈(N : ℝ) - prW N⌉ := by
      rw [sub_nonneg]
      exact (Int.ceil_le).mpr (by push_cast; linarith [prW_nonneg N])
    rw [show (N : ℤ) - 1 + 1 = (N : ℤ) by ring]
    rw [show (((((N : ℤ) - ⌈(N : ℝ) - prW N⌉).toNat : ℕ) : ℝ) =
        ((((N : ℤ) - ⌈(N : ℝ) - prW N⌉).toNat : ℤ) : ℝ)) by push_cast; ring]
    rw [Int.toNat_of_nonneg h2]
    push_cast
    have h4 := Int.le_ceil ((N : ℝ) - prW N)
    linarith
  have hc2 : ((G2.card : ℕ) : ℝ) ≤ prW N := by
    rw [hG2, Int.card_Icc]
    have h2 : (0:ℤ) ≤ ⌊(2 * N : ℝ) + prW N⌋ - 2 * (N : ℤ) := by
      rw [sub_nonneg]
      exact (Int.le_floor).mpr (by push_cast; linarith [prW_nonneg N])
    rw [show ⌊(2 * (N : ℝ) + prW N)⌋ + 1 - (2 * (N : ℤ) + 1) =
        ⌊(2 * N : ℝ) + prW N⌋ - 2 * (N : ℤ) by ring]
    rw [show (((⌊(2 * N : ℝ) + prW N⌋ - 2 * (N : ℤ)).toNat : ℕ) : ℝ) =
        (((⌊(2 * N : ℝ) + prW N⌋ - 2 * (N : ℤ)).toNat : ℤ) : ℝ) by push_cast; ring]
    rw [Int.toNat_of_nonneg h2]
    push_cast
    have h4 := Int.floor_le ((2 * N : ℝ) + prW N)
    linarith
  have hb1 : ∑ n ∈ G1, ‖prG N τ (n : ℝ)‖ ≤ prW N * (2 / Real.sqrt N) := by
    calc ∑ n ∈ G1, ‖prG N τ (n : ℝ)‖ ≤ ∑ n ∈ G1, (2 / Real.sqrt N) :=
          Finset.sum_le_sum (fun n _ => norm_prG_le hN1 τ _)
      _ = ((G1.card : ℕ) : ℝ) * (2 / Real.sqrt N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ prW N * (2 / Real.sqrt N) := mul_le_mul_of_nonneg_right hc1 (by positivity)
  have hb2 : ∑ n ∈ G2, ‖prG N τ (n : ℝ)‖ ≤ prW N * (2 / Real.sqrt N) := by
    calc ∑ n ∈ G2, ‖prG N τ (n : ℝ)‖ ≤ ∑ n ∈ G2, (2 / Real.sqrt N) :=
          Finset.sum_le_sum (fun n _ => norm_prG_le hN1 τ _)
      _ = ((G2.card : ℕ) : ℝ) * (2 / Real.sqrt N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ prW N * (2 / Real.sqrt N) := mul_le_mul_of_nonneg_right hc2 (by positivity)
  have hfin : prW N * (2 / Real.sqrt N) = 2 := by
    rw [prW, div_eq_mul_inv]
    have h : Real.sqrt (N:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  calc ‖∑ n ∈ prSup N \ prInd N, prG N τ (n : ℝ)‖
      ≤ ∑ n ∈ prSup N \ prInd N, ‖prG N τ (n : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ G1 ∪ G2, ‖prG N τ (n : ℝ)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ = ∑ n ∈ G1, ‖prG N τ (n : ℝ)‖ + ∑ n ∈ G2, ‖prG N τ (n : ℝ)‖ := Finset.sum_union hdisj
    _ ≤ prW N * (2 / Real.sqrt N) + prW N * (2 / Real.sqrt N) := add_le_add hb1 hb2
    _ = 4 := by rw [hfin]; norm_num
    _ ≤ 6 := by norm_num

def prA (N : ℕ) (y : ℝ) : ℝ := (1/prW N) * y + (1 - (N:ℝ)/prW N)
def prB (N : ℕ) (y : ℝ) : ℝ := (-(1/prW N)) * y + ((2*N:ℝ)/prW N + 1)
lemma prA_eq (N : ℕ) (y : ℝ) : prA N y = ((y - (N:ℝ))/prW N) + 1 := by
  unfold prA; field_simp; ring
lemma prB_eq (N : ℕ) (y : ℝ) : prB N y = (((2*N:ℝ) - y)/prW N) + 1 := by
  unfold prB; field_simp; ring

lemma prChi_eq_AB (N : ℕ) :
    prChi N = (fun y : ℝ => Real.smoothTransition (prA N y)) *
      (fun y : ℝ => Real.smoothTransition (prB N y)) := by
  funext y
  rw [Pi.mul_apply, prChi, prA_eq, prB_eq]

lemma deriv_eq_zero_of_eventually_const {f : ℝ → ℝ} {c x : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => c) : deriv f x = 0 := by
  rw [h.deriv_eq]
  simp [deriv_const]

lemma exists_bound_deriv_smoothTransition :
    ∃ K : ℝ, 0 < K ∧ (∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K) ∧
      (∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) := by
  have hle1 : ((1:ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have hle2 : ((2:ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have hc1 : Continuous (iteratedDeriv 1 Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).continuous_iteratedDeriv 1 hle1
  have hc2 : Continuous (iteratedDeriv 2 Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).continuous_iteratedDeriv 2 hle2
  obtain ⟨K1, hK1⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc 0 1) hc1.continuousOn
  obtain ⟨K2, hK2⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc 0 1) hc2.continuousOn
  have hK1nn : 0 ≤ K1 := le_trans (norm_nonneg _) (hK1 0 ⟨le_rfl, zero_le_one⟩)
  have hK2nn : 0 ≤ K2 := le_trans (norm_nonneg _) (hK2 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨max K1 K2 + 1, by linarith [le_max_left K1 K2, le_max_right K1 K2], ?_, ?_⟩
  · intro x
    by_cases h : x < 0
    · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds h] with y hy
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [deriv_eq_zero_of_eventually_const hev, abs_zero]
      linarith [le_max_left K1 K2, le_max_right K1 K2]
    · push Not at h
      by_cases h2 : x ≤ 1
      · have hb : |deriv Real.smoothTransition x| ≤ K1 := by
          simpa only [Real.norm_eq_abs, iteratedDeriv_one] using hK1 x ⟨h, h2⟩
        linarith [le_max_left K1 K2]
      · push Not at h2
        have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
          filter_upwards [isOpen_Ioi.mem_nhds h2] with y hy
          exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
        rw [deriv_eq_zero_of_eventually_const hev, abs_zero]
        linarith [le_max_left K1 K2, le_max_right K1 K2]
  · intro x
    have h2eq : iteratedDeriv 2 Real.smoothTransition = deriv (deriv Real.smoothTransition) := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    by_cases h : x < 0
    · have hz : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds h] with y hy
        exact deriv_eq_zero_of_eventually_const (show Real.smoothTransition =ᶠ[𝓝 y] fun _ => (0:ℝ) from by
          filter_upwards [isOpen_Iio.mem_nhds hy] with z hz'
          exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz'))
      rw [deriv_eq_zero_of_eventually_const hz, abs_zero]
      linarith [le_max_left K1 K2, le_max_right K1 K2]
    · push Not at h
      by_cases h2 : x ≤ 1
      · have hb : |deriv (deriv Real.smoothTransition) x| ≤ K2 := by
          simpa only [Real.norm_eq_abs, h2eq] using hK2 x ⟨h, h2⟩
        linarith [le_max_right K1 K2]
      · push Not at h2
        have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
          filter_upwards [isOpen_Ioi.mem_nhds h2] with y hy
          exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
        have hz : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
          filter_upwards [isOpen_Ioi.mem_nhds h2] with y hy
          exact deriv_eq_zero_of_eventually_const (show Real.smoothTransition =ᶠ[𝓝 y] fun _ => (1:ℝ) from by
            filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz'
            exact Real.smoothTransition.one_of_one_le (le_of_lt hz'))
        rw [deriv_eq_zero_of_eventually_const hz, abs_zero]
        linarith [le_max_left K1 K2, le_max_right K1 K2]

lemma hasDerivAt_affine (c d x : ℝ) : HasDerivAt (fun y : ℝ => c * y + d) c x := by
  simpa using ((hasDerivAt_id x).const_mul c).add_const d

lemma hasDerivAt_smoothTransition_affine (c d y : ℝ) :
    HasDerivAt (fun x : ℝ => Real.smoothTransition (c * x + d))
      (deriv Real.smoothTransition (c * y + d) * c) y := by
  have hcomp : (fun x : ℝ => Real.smoothTransition (c * x + d)) =
      Real.smoothTransition ∘ (fun x : ℝ => c * x + d) := by funext x; rfl
  rw [hcomp]
  have hσ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (c * y + d)) (c * y + d) :=
    (Real.smoothTransition.contDiff.differentiable_one.differentiableAt).hasDerivAt
  exact hσ.comp y (hasDerivAt_affine c d y)

lemma hasDerivAt_deriv_smoothTransition_affine (c d y : ℝ) :
    HasDerivAt (fun x : ℝ => deriv Real.smoothTransition (c * x + d))
      (deriv (deriv Real.smoothTransition) (c * y + d) * c) y := by
  have hcomp : (fun x : ℝ => deriv Real.smoothTransition (c * x + d)) =
      deriv Real.smoothTransition ∘ (fun x : ℝ => c * x + d) := by funext x; rfl
  rw [hcomp]
  have h2 : ContDiff ℝ 1 (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (2:ℕ∞))).deriv'
  have hσ : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) (c * y + d)) (c * y + d) :=
    h2.differentiable_one.differentiableAt.hasDerivAt
  exact hσ.comp y (hasDerivAt_affine c d y)

lemma deriv_smoothTransition_affine_eq (c d y : ℝ) :
    deriv (fun x : ℝ => Real.smoothTransition (c * x + d)) y =
      deriv Real.smoothTransition (c * y + d) * c :=
  (hasDerivAt_smoothTransition_affine c d y).deriv

lemma iteratedDeriv_two_smoothTransition_affine (c d y : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.smoothTransition (c * x + d)) y =
      deriv (deriv Real.smoothTransition) (c * y + d) * c * c := by
  have h1 : iteratedDeriv 2 (fun x : ℝ => Real.smoothTransition (c * x + d)) =
      deriv (deriv (fun x : ℝ => Real.smoothTransition (c * x + d))) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h1]
  have hfun : deriv (fun x : ℝ => Real.smoothTransition (c * x + d)) =
      fun x : ℝ => deriv Real.smoothTransition (c * x + d) * c :=
    funext fun x => deriv_smoothTransition_affine_eq c d x
  rw [hfun]
  have hd := (hasDerivAt_deriv_smoothTransition_affine c d y).mul_const c
  exact hd.deriv

lemma deriv_prChi (N : ℕ) (y : ℝ) :
    deriv (prChi N) y =
      deriv Real.smoothTransition (prA N y) * (1/prW N) * Real.smoothTransition (prB N y)
        + Real.smoothTransition (prA N y) * (deriv Real.smoothTransition (prB N y) * (-(1/prW N))) := by
  have h1 : HasDerivAt (fun x : ℝ => Real.smoothTransition (prA N x))
      (deriv Real.smoothTransition (prA N y) * (1/prW N)) y :=
    hasDerivAt_smoothTransition_affine (1/prW N) (1 - (N:ℝ)/prW N) y
  have h2 : HasDerivAt (fun x : ℝ => Real.smoothTransition (prB N x))
      (deriv Real.smoothTransition (prB N y) * (-(1/prW N))) y :=
    hasDerivAt_smoothTransition_affine (-(1/prW N)) ((2*N:ℝ)/prW N + 1) y
  have h3 : HasDerivAt ((fun x : ℝ => Real.smoothTransition (prA N x)) *
      (fun x : ℝ => Real.smoothTransition (prB N x)))
      (deriv Real.smoothTransition (prA N y) * (1/prW N) * Real.smoothTransition (prB N y)
        + Real.smoothTransition (prA N y) * (deriv Real.smoothTransition (prB N y) * (-(1/prW N)))) y :=
    h1.mul h2
  have heq : ((fun x : ℝ => Real.smoothTransition (prA N x)) *
      (fun x : ℝ => Real.smoothTransition (prB N x))) = prChi N := prChi_eq_AB N |>.symm
  rw [heq] at h3
  exact h3.deriv

lemma deriv_prChi_eq (N : ℕ) :
    deriv (prChi N) = fun y : ℝ =>
      deriv Real.smoothTransition (prA N y) * (1/prW N) * Real.smoothTransition (prB N y)
        + Real.smoothTransition (prA N y) * (deriv Real.smoothTransition (prB N y) * (-(1/prW N))) :=
  funext fun y => deriv_prChi N y

lemma deriv_prA (N : ℕ) (y : ℝ) :
    deriv (fun x : ℝ => Real.smoothTransition (prA N x)) y =
      deriv Real.smoothTransition (prA N y) * (1/prW N) := by
  simpa only [prA] using deriv_smoothTransition_affine_eq (1/prW N) (1 - (N:ℝ)/prW N) y

lemma deriv_prB (N : ℕ) (y : ℝ) :
    deriv (fun x : ℝ => Real.smoothTransition (prB N x)) y =
      deriv Real.smoothTransition (prB N y) * (-(1/prW N)) := by
  simpa only [prB] using deriv_smoothTransition_affine_eq (-(1/prW N)) ((2*N:ℝ)/prW N + 1) y

lemma iteratedDeriv_two_prA (N : ℕ) (y : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.smoothTransition (prA N x)) y =
      deriv (deriv Real.smoothTransition) (prA N y) * (1/prW N) * (1/prW N) := by
  simpa only [prA] using iteratedDeriv_two_smoothTransition_affine (1/prW N) (1 - (N:ℝ)/prW N) y

lemma iteratedDeriv_two_prB (N : ℕ) (y : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.smoothTransition (prB N x)) y =
      deriv (deriv Real.smoothTransition) (prB N y) * (-(1/prW N)) * (-(1/prW N)) := by
  simpa only [prB] using iteratedDeriv_two_smoothTransition_affine (-(1/prW N)) ((2*N:ℝ)/prW N + 1) y

lemma iteratedDeriv_two_prChi (N : ℕ) (y : ℝ) :
    iteratedDeriv 2 (prChi N) y =
      deriv (deriv Real.smoothTransition) (prA N y) * (1/prW N) * (1/prW N) * Real.smoothTransition (prB N y)
      + 2 * (deriv Real.smoothTransition (prA N y) * (1/prW N) *
          (deriv Real.smoothTransition (prB N y) * (-(1/prW N))))
      + Real.smoothTransition (prA N y) *
          (deriv (deriv Real.smoothTransition) (prB N y) * (-(1/prW N)) * (-(1/prW N))) := by
  have hAcd : ContDiffAt ℝ 2 (fun x : ℝ => Real.smoothTransition (prA N x)) y := by
    have hσ : ContDiffAt ℝ 2 Real.smoothTransition (prA N y) :=
      (Real.smoothTransition.contDiff (n := (2:ℕ∞))).contDiffAt
    have ha : ContDiffAt ℝ 2 (fun x : ℝ => (1/prW N) * x + (1 - (N:ℝ)/prW N)) y := by fun_prop
    exact hσ.comp y ha
  have hBcd : ContDiffAt ℝ 2 (fun x : ℝ => Real.smoothTransition (prB N x)) y := by
    have hσ : ContDiffAt ℝ 2 Real.smoothTransition (prB N y) :=
      (Real.smoothTransition.contDiff (n := (2:ℕ∞))).contDiffAt
    have ha : ContDiffAt ℝ 2 (fun x : ℝ => (-(1/prW N)) * x + ((2*N:ℝ)/prW N + 1)) y := by fun_prop
    exact hσ.comp y ha
  rw [prChi_eq_AB]
  rw [iteratedDeriv_mul hAcd hBcd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.choose, Nat.reduceSub, iteratedDeriv_zero, iteratedDeriv_one]
  rw [iteratedDeriv_two_prA N y, iteratedDeriv_two_prB N y, deriv_prA N y, deriv_prB N y]
  ring

lemma prChi_deriv_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (y : ℝ),
      |deriv (prChi N) y| ≤ K / prW N ∧
      |deriv (deriv (prChi N)) y| ≤ K / (prW N * prW N) := by
  obtain ⟨Ks, hKs, hK1, hK2⟩ := exists_bound_deriv_smoothTransition
  refine ⟨2*Ks + 2*Ks^2 + 1, by positivity, ?_⟩
  intro N hN y
  have hWpos : 0 < prW N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hKsnn : 0 ≤ Ks := le_trans (abs_nonneg _) (hK1 0)
  have hσb : |Real.smoothTransition (prB N y)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hσa : |Real.smoothTransition (prA N y)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hw1 : |(1:ℝ)/prW N| = 1/prW N := abs_of_pos (by positivity)
  have hwnn : (0:ℝ) ≤ 1/prW N := le_of_lt (by positivity)
  have hd1 := hK1 (prA N y)
  have hd2 := hK1 (prB N y)
  have hd3 := hK2 (prA N y)
  have hd4 := hK2 (prB N y)
  constructor
  · have hb : |deriv (prChi N) y| ≤ 2 * (Ks * (1/prW N)) := by
      rw [deriv_prChi]
      have e1 : |deriv Real.smoothTransition (prA N y) * (1/prW N) * Real.smoothTransition (prB N y)|
          ≤ Ks * (1/prW N) := by
        have habs : |deriv Real.smoothTransition (prA N y) * (1/prW N) * Real.smoothTransition (prB N y)|
            = |deriv Real.smoothTransition (prA N y)| * (1/prW N) * |Real.smoothTransition (prB N y)| := by
          simp only [abs_mul, hw1]
        rw [habs]
        calc |deriv Real.smoothTransition (prA N y)| * (1/prW N) * |Real.smoothTransition (prB N y)|
            ≤ Ks * (1/prW N) * 1 :=
              mul_le_mul (mul_le_mul hd1 le_rfl hwnn (le_trans (abs_nonneg _) hd1)) hσb
                (abs_nonneg _) (mul_nonneg hKsnn hwnn)
          _ = Ks * (1/prW N) := by ring
      have e2 : |Real.smoothTransition (prA N y) * (deriv Real.smoothTransition (prB N y) * (-(1/prW N)))|
          ≤ Ks * (1/prW N) := by
        have habs : |Real.smoothTransition (prA N y) * (deriv Real.smoothTransition (prB N y) * (-(1/prW N)))|
            = |Real.smoothTransition (prA N y)| * (|deriv Real.smoothTransition (prB N y)| * (1/prW N)) := by
          simp only [abs_mul, abs_neg, hw1]
        rw [habs]
        calc |Real.smoothTransition (prA N y)| * (|deriv Real.smoothTransition (prB N y)| * (1/prW N))
            ≤ 1 * (Ks * (1/prW N)) :=
              mul_le_mul hσa (mul_le_mul hd2 le_rfl hwnn (le_trans (abs_nonneg _) hd2))
                (mul_nonneg (abs_nonneg _) hwnn) (by norm_num)
          _ = Ks * (1/prW N) := by ring
      calc |deriv Real.smoothTransition (prA N y) * (1/prW N) * Real.smoothTransition (prB N y) +
            Real.smoothTransition (prA N y) * (deriv Real.smoothTransition (prB N y) * (-(1/prW N)))|
          ≤ Ks * (1/prW N) + Ks * (1/prW N) := le_trans (abs_add_le _ _) (add_le_add e1 e2)
        _ = 2 * (Ks * (1/prW N)) := by ring
    refine le_trans hb ?_
    rw [div_eq_mul_inv]
    have h2 : 2 * Ks ≤ 2 * Ks + 2 * Ks ^ 2 + 1 := by nlinarith
    calc 2 * (Ks * (1/prW N)) = (2 * Ks) * (1/prW N) := by ring
      _ ≤ (2 * Ks + 2 * Ks ^ 2 + 1) * (1/prW N) := mul_le_mul_of_nonneg_right h2 hwnn
      _ = (2 * Ks + 2 * Ks ^ 2 + 1) / prW N := by rw [div_eq_mul_inv]; ring
  · have hb : |deriv (deriv (prChi N)) y| ≤ (2*Ks + 2*Ks^2) * ((1/prW N) * (1/prW N)) := by
      rw [show deriv (deriv (prChi N)) y = iteratedDeriv 2 (prChi N) y from by
        rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]]
      rw [iteratedDeriv_two_prChi]
      have e1 : |deriv (deriv Real.smoothTransition) (prA N y) * (1/prW N) * (1/prW N) * Real.smoothTransition (prB N y)|
          ≤ Ks * ((1/prW N) * (1/prW N)) := by
        have habs : |deriv (deriv Real.smoothTransition) (prA N y) * (1/prW N) * (1/prW N) * Real.smoothTransition (prB N y)|
            = |deriv (deriv Real.smoothTransition) (prA N y)| * (1/prW N) * (1/prW N) * |Real.smoothTransition (prB N y)| := by
          simp only [abs_mul, hw1]
        rw [habs]
        calc |deriv (deriv Real.smoothTransition) (prA N y)| * (1/prW N) * (1/prW N) * |Real.smoothTransition (prB N y)|
            ≤ Ks * (1/prW N) * (1/prW N) * 1 :=
              mul_le_mul (mul_le_mul (mul_le_mul hd3 le_rfl hwnn (le_trans (abs_nonneg _) hd3))
                le_rfl hwnn (mul_nonneg (le_trans (abs_nonneg _) hd3) hwnn)) hσb (abs_nonneg _)
                (by positivity)
          _ = Ks * ((1/prW N) * (1/prW N)) := by ring
      have e2 : |2 * (deriv Real.smoothTransition (prA N y) * (1/prW N) *
            (deriv Real.smoothTransition (prB N y) * (-(1/prW N))))|
          ≤ 2 * ((Ks * (1/prW N)) * (Ks * (1/prW N))) := by
        have habs : |2 * (deriv Real.smoothTransition (prA N y) * (1/prW N) *
            (deriv Real.smoothTransition (prB N y) * (-(1/prW N))))|
            = 2 * (|deriv Real.smoothTransition (prA N y)| * (1/prW N) *
                (|deriv Real.smoothTransition (prB N y)| * (1/prW N))) := by
          simp only [abs_mul, abs_neg, hw1, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        rw [habs]
        have ha : |deriv Real.smoothTransition (prA N y)| * (1/prW N) ≤ Ks * (1/prW N) :=
          mul_le_mul_of_nonneg_right hd1 hwnn
        have hb2 : |deriv Real.smoothTransition (prB N y)| * (1/prW N) ≤ Ks * (1/prW N) :=
          mul_le_mul_of_nonneg_right hd2 hwnn
        calc 2 * (|deriv Real.smoothTransition (prA N y)| * (1/prW N) *
              (|deriv Real.smoothTransition (prB N y)| * (1/prW N)))
            ≤ 2 * ((Ks * (1/prW N)) * (Ks * (1/prW N))) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul ha hb2 (mul_nonneg (abs_nonneg _) hwnn) (mul_nonneg hKsnn hwnn)
          _ = 2 * ((Ks * (1/prW N)) * (Ks * (1/prW N))) := rfl
      have e3 : |Real.smoothTransition (prA N y) *
            (deriv (deriv Real.smoothTransition) (prB N y) * (-(1/prW N)) * (-(1/prW N)))|
          ≤ 1 * (Ks * ((1/prW N) * (1/prW N))) := by
        have habs : |Real.smoothTransition (prA N y) *
            (deriv (deriv Real.smoothTransition) (prB N y) * (-(1/prW N)) * (-(1/prW N)))|
            = |Real.smoothTransition (prA N y)| * (|deriv (deriv Real.smoothTransition) (prB N y)| *
                (1/prW N) * (1/prW N)) := by
          simp only [abs_mul, abs_neg, hw1]
        rw [habs]
        calc |Real.smoothTransition (prA N y)| * (|deriv (deriv Real.smoothTransition) (prB N y)| *
              (1/prW N) * (1/prW N))
            ≤ 1 * (Ks * (1/prW N) * (1/prW N)) :=
              mul_le_mul hσa (mul_le_mul (mul_le_mul hd4 le_rfl hwnn (le_trans (abs_nonneg _) hd4))
                le_rfl hwnn (mul_nonneg (le_trans (abs_nonneg _) hd4) hwnn)) (by positivity) (by norm_num)
          _ = 1 * (Ks * ((1/prW N) * (1/prW N))) := by ring
      calc |deriv (deriv Real.smoothTransition) (prA N y) * (1/prW N) * (1/prW N) * Real.smoothTransition (prB N y) +
            2 * (deriv Real.smoothTransition (prA N y) * (1/prW N) *
              (deriv Real.smoothTransition (prB N y) * (-(1/prW N)))) +
            Real.smoothTransition (prA N y) *
              (deriv (deriv Real.smoothTransition) (prB N y) * (-(1/prW N)) * (-(1/prW N)))|
          ≤ Ks * ((1/prW N) * (1/prW N)) + 2 * ((Ks * (1/prW N)) * (Ks * (1/prW N)))
            + 1 * (Ks * ((1/prW N) * (1/prW N))) :=
            le_trans (abs_add_le _ _) (add_le_add (le_trans (abs_add_le _ _) (add_le_add e1 e2)) e3)
        _ = (2*Ks + 2*Ks^2) * ((1/prW N) * (1/prW N)) := by ring
    have h1 : (2*Ks + 2*Ks^2) * ((1/prW N) * (1/prW N))
        ≤ (2*Ks + 2*Ks^2 + 1) * ((1/prW N) * (1/prW N)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    have h2 : ((1:ℝ)/prW N) * (1/prW N) = 1/(prW N * prW N) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    rw [h2] at h1
    have h3 : (2 * Ks + 2 * Ks ^ 2 + 1) * (1 / (prW N * prW N)) =
        (2 * Ks + 2 * Ks ^ 2 + 1) / (prW N * prW N) := by
      rw [div_eq_mul_inv]; ring
    rw [h3] at h1
    have hb' : |deriv (deriv (prChi N)) y| ≤ (2*Ks + 2*Ks^2) * (1/(prW N * prW N)) := by
      rw [← h2]; exact hb
    exact le_trans hb' h1


/-- The `m`-th Fourier integral of `prG`. -/
def prHat (N : ℕ) (τ : ℝ) (m : ℤ) : ℂ :=
  ∫ y : ℝ, prG N τ y * Complex.exp (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y))

lemma prHat_eq_integral (N : ℕ) (hN : 4 ≤ N) (τ : ℝ) (m : ℤ) :
    prHat N τ m =
      ∫ y : ℝ, (((Real.sqrt y)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log y : ℂ))) *
        (prChi N y : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y)) := by
  unfold prHat
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  by_cases hy : prChi N y = 0
  · rw [show prG N τ y = 0 from by unfold prG; rw [hy]; simp, hy]
    simp
  · have hmem : (N:ℝ) - prW N ≤ y := by
      by_contra hc
      push Not at hc
      exact hy (prChi_eq_zero_of_le (by omega) (le_of_lt hc))
    rw [prG_eq_of_mem hN τ hmem, Complex.ofReal_inv]

lemma prHat_tsum_eq (N : ℕ) (hN : 4 ≤ N) (τ : ℝ) :
    (∑' m : ℤ, prHat N τ m) =
      ∑' m : ℤ, (∫ y : ℝ, (((Real.sqrt y)⁻¹ : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((τ : ℂ) * (Real.log y : ℂ))) * (prChi N y : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y))) :=
  tsum_congr fun m => prHat_eq_integral N hN τ m

/-- The integer block `[N,2N]` reindexed. -/
lemma sum_prInd_eq (N : ℕ) (hN : 4 ≤ N) (τ : ℝ) :
    ∑ n ∈ prInd N, prG N τ (n : ℝ) =
      ∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ) := by
  have hN1 : 1 ≤ N := by omega
  have h1 : ∑ n ∈ prInd N, prG N τ (n : ℝ) = ∑ n ∈ Finset.Icc N (2 * N), prG N τ (n : ℝ) := by
    refine Finset.sum_bij (fun (n : ℤ) _ => n.toNat) ?_ ?_ ?_ ?_
    · intro n hn
      rw [prInd, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      constructor <;> omega
    · intro n1 hn1 n2 hn2 h
      simp only [prInd, Finset.mem_Icc] at hn1 hn2
      have h3 : (0:ℤ) ≤ n1 := by omega
      have h4 : (0:ℤ) ≤ n2 := by omega
      have h5 : ((n1.toNat : ℕ) : ℤ) = n1 := Int.toNat_of_nonneg h3
      have h6 : ((n2.toNat : ℕ) : ℤ) = n2 := Int.toNat_of_nonneg h4
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      refine ⟨(n : ℤ), ?_, ?_⟩
      · simp only [prInd, Finset.mem_Icc]
        constructor <;> omega
      · simp
    · intro n hn
      simp only [prInd, Finset.mem_Icc] at hn
      have h3 : (0:ℤ) ≤ n := by omega
      have h5 : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg h3
      have h6 : ((n : ℝ)) = ((n.toNat : ℕ) : ℝ) := by exact_mod_cast h5.symm
      rw [h6]
  rw [h1]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  exact prG_nat_eq hN τ hn.1 hn.2

/-- **The requested pointwise reflection bound (van der Corput form).** -/
theorem pointwise_reflection_vdc :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (τ : ℝ), (N : ℝ) ≤ τ →
      ‖∑ n ∈ Finset.Icc N (2 * N),
          (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
      ≤ C * (1 + Real.log (2 + τ)) ^ 4 *
        (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                  (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
              (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ ^ 2) := by
  obtain ⟨C0, hC0pos, hCore⟩ := Commons.NumberTheory.DirichletPolynomial.weighted_window_reflection
  obtain ⟨Kd, hKdpos, hKdb⟩ := prChi_deriv_bounds
  refine ⟨2 * (C0 * (1 + Kd) + 6) ^ 2 + 16, by positivity, ?_⟩
  intro N hN τ hNτ
  by_cases hN4 : 4 ≤ N
  · -- ### main case `4 ≤ N`
    have hτ1 : (1:ℝ) ≤ τ := le_trans (by exact_mod_cast hN) hNτ
    have hlog1 : (1:ℝ) ≤ 1 + Real.log (2 + τ) := by
      have : (0:ℝ) ≤ Real.log (2 + τ) := Real.log_nonneg (by linarith)
      linarith
    have hD1 : (1:ℝ) ≤ 1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                  (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
              (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ := by
      have : (0:ℝ) ≤ ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                  (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
              (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ := norm_nonneg _
      linarith
    -- the analytic core bound
    have hχd : ContDiff ℝ 3 (prChi N) := (prChi_contDiff N).of_le (WithTop.coe_le_coe.mpr le_top)
    have hχ0 : ∀ y : ℝ, 0 ≤ prChi N y ∧ prChi N y ≤ 1 :=
      fun y => ⟨prChi_nonneg N y, prChi_le_one N y⟩
    have hχ1 : ∀ y : ℝ, (N : ℝ) ≤ y → y ≤ 2 * N → prChi N y = 1 :=
      fun y h1 h2 => prChi_eq_one hN h1 h2
    have hχz : ∀ y : ℝ, y ≤ (N : ℝ) - Real.sqrt (N : ℝ) ∨
        (2 * N : ℝ) + Real.sqrt (N : ℝ) ≤ y → prChi N y = 0 := by
      intro y hy
      rcases hy with hy | hy
      · exact prChi_eq_zero_of_le hN (by rwa [prW])
      · exact prChi_eq_zero_of_ge hN (by rwa [prW])
    have hbd1 : ∀ y : ℝ, |deriv (prChi N) y| ≤ Kd / Real.sqrt (N : ℝ) :=
      fun y => (hKdb N hN y).1
    have hbd2 : ∀ y : ℝ, |deriv (deriv (prChi N)) y| ≤
        Kd / (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) :=
      fun y => (hKdb N hN y).2
    have hcore := hCore N hN4 τ hNτ (prChi N) Kd hKdpos hχd hχ0 hχ1 hχz hbd1 hbd2
    -- the Poisson representation
    have hPoisson : (∑' n : ℤ, prG N τ (n : ℝ)) = ∑' m : ℤ, prHat N τ m := pr_poisson N hN τ
    have htsum : (∑' m : ℤ, prHat N τ m) =
        ∑' m : ℤ, (∫ y : ℝ, (((Real.sqrt y)⁻¹ : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((τ : ℂ) * (Real.log y : ℂ))) * (prChi N y : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y))) := prHat_tsum_eq N hN4 τ
    have hcore' : ‖∑' m : ℤ, prHat N τ m‖ ≤
        C0 * (1 + Kd) * (1 + Real.log (2 + τ)) *
          (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖) := by
      rw [htsum]
      exact hcore
    -- the block identity
    have hsub := prInd_subset_prSup hN4
    have hsdiff := Finset.sum_sdiff (f := fun n : ℤ => prG N τ (n : ℝ)) hsub
    have hpInd : (∑ n ∈ prSup N, prG N τ (n : ℝ)) =
        ∑ n ∈ prSup N \ prInd N, prG N τ (n : ℝ) + ∑ n ∈ prInd N, prG N τ (n : ℝ) := hsdiff.symm
    have hpSup : (∑ n ∈ prSup N, prG N τ (n : ℝ)) = ∑' m : ℤ, prHat N τ m := by
      rw [← prG_tsum_eq_sum' hN4 τ, hPoisson]
    have hS : (∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)) =
        (∑' m : ℤ, prHat N τ m) - ∑ n ∈ prSup N \ prInd N, prG N τ (n : ℝ) := by
      rw [← sum_prInd_eq N hN4 τ]
      rw [show (∑' m : ℤ, prHat N τ m) - ∑ n ∈ prSup N \ prInd N, prG N τ (n : ℝ) =
          ∑ n ∈ prInd N, prG N τ (n : ℝ) from by
        rw [hpSup] at hpInd
        rw [hpInd]
        ring]
    have hnormS : ‖∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ≤
        C0 * (1 + Kd) * (1 + Real.log (2 + τ)) *
          (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖) + 6 := by
      rw [hS]
      refine le_trans (norm_sub_le _ _) (add_le_add hcore' (extra_bound hN4 τ))
    have hb : ‖∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ≤
        (C0 * (1 + Kd) + 6) * (1 + Real.log (2 + τ)) *
          (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖) := by
      refine le_trans hnormS ?_
      have hX : (1:ℝ) ≤ (1 + Real.log (2 + τ)) *
          (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖) := by
        have h1 := hlog1
        have h2 := hD1
        nlinarith [mul_le_mul h1 h2 (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ 1 + Real.log (2 + τ))]
      have hAnn : (0:ℝ) ≤ C0 * (1 + Kd) := by positivity
      nlinarith [hX, hAnn]
    -- square
    have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hDnn : (0:ℝ) ≤ 1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ := by
      have := norm_nonneg (∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ))
      linarith
    have hsq : ((C0 * (1 + Kd) + 6) * (1 + Real.log (2 + τ)) *
          (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖)) ^ 2
        ≤ (2 * (C0 * (1 + Kd) + 6) ^ 2 + 16) * (1 + Real.log (2 + τ)) ^ 4 *
          (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ ^ 2) := by
      have hstep1 : (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖) ^ 2
          ≤ 2 * (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ ^ 2) := by
        nlinarith [hDnn, sq_nonneg (‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ - 1)]
      have hstep2 : (1 + Real.log (2 + τ)) ^ 2 ≤ (1 + Real.log (2 + τ)) ^ 4 := by
        have h : (1:ℝ) ≤ (1 + Real.log (2 + τ)) ^ 2 := by
          simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hlog1 2
        calc (1 + Real.log (2 + τ)) ^ 2 = (1 + Real.log (2 + τ)) ^ 2 * 1 := by ring
          _ ≤ (1 + Real.log (2 + τ)) ^ 2 * (1 + Real.log (2 + τ)) ^ 2 :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = (1 + Real.log (2 + τ)) ^ 4 := by ring
      have hA : (0:ℝ) ≤ (C0 * (1 + Kd) + 6) ^ 2 := sq_nonneg _
      calc ((C0 * (1 + Kd) + 6) * (1 + Real.log (2 + τ)) *
            (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖)) ^ 2
          = (C0 * (1 + Kd) + 6) ^ 2 * (1 + Real.log (2 + τ)) ^ 2 *
            (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖) ^ 2 := by ring
        _ ≤ (C0 * (1 + Kd) + 6) ^ 2 * (1 + Real.log (2 + τ)) ^ 4 *
            (2 * (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ ^ 2)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hstep2 hA
            · exact hstep1
            · positivity
            · positivity
        _ = 2 * (C0 * (1 + Kd) + 6) ^ 2 * (1 + Real.log (2 + τ)) ^ 4 *
            (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ ^ 2) := by ring
        _ ≤ (2 * (C0 * (1 + Kd) + 6) ^ 2 + 16) * (1 + Real.log (2 + τ)) ^ 4 *
            (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_right
              · nlinarith [hA]
              · positivity
            · positivity
    exact le_trans hb2 hsq
  · -- ### small case `N ≤ 3`
    push Not at hN4
    have hbound : ‖∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ≤ 4 := by
      calc ‖∑ n ∈ Finset.Icc N (2 * N),
            (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖
          ≤ ∑ n ∈ Finset.Icc N (2 * N),
              ‖(n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Icc N (2 * N), (1:ℝ) := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_Icc] at hn
            have hn1 : (1:ℕ) ≤ n := le_trans hN hn.1
            have hnorm : ‖(n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ≤ 1 := by
              rw [norm_div]
              have hnum : ‖(n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ))‖ = 1 := by
                rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp]
                rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn1)]
                simp
              have hden : ‖((Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ = Real.sqrt (n : ℝ) :=
                Complex.norm_of_nonneg (Real.sqrt_nonneg _)
              rw [hnum, hden, one_div]
              exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by exact_mod_cast hn1))
            exact hnorm
        _ = ((Finset.Icc N (2 * N)).card : ℝ) := by simp
        _ ≤ 4 := by
            rw [Nat.card_Icc]
            have : 2 * N + 1 - N ≤ 4 := by omega
            exact_mod_cast this
    have hsq : ‖∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2 ≤ 16 := by
      have := norm_nonneg (∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ))
      nlinarith [hbound]
    refine le_trans hsq ?_
    have h1 : (1:ℝ) ≤ (1 + Real.log (2 + τ)) ^ 4 := by
      have h2 : (1:ℝ) ≤ 1 + Real.log (2 + τ) := by
        have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
        have : (0:ℝ) ≤ Real.log (2 + τ) := Real.log_nonneg (by linarith)
        linarith
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h2 4
    have h2 : (1:ℝ) ≤ 1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                  (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
              (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ ^ 2 := by
      have := sq_nonneg ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                  (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
              (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖
      linarith
    have hC : (16:ℝ) ≤ 2 * (C0 * (1 + Kd) + 6) ^ 2 + 16 := by
      nlinarith [sq_nonneg (C0 * (1 + Kd) + 6)]
    calc (16:ℝ) ≤ (2 * (C0 * (1 + Kd) + 6) ^ 2 + 16) * 1 * 1 := by
          nlinarith [sq_nonneg (C0 * (1 + Kd) + 6)]
      _ ≤ (2 * (C0 * (1 + Kd) + 6) ^ 2 + 16) * (1 + Real.log (2 + τ)) ^ 4 *
          (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖ ^ 2) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h1 (by positivity)
        · exact h2
        · positivity
        · positivity

end

end Commons.NumberTheory.DirichletPolynomial
