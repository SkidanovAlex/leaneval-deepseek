/-
# Quantitative bounds for the modulated Ionescu--Wainger bump `φ_{N,t}`

The KMT bump of §6--§8 is `φ_N(ξ) = η(2^{Log N - k}ξ) - η(2^{Log N-k+1}ξ)` (and `η(2^{Log N}ξ)` at
the bottom scale `k = 0`), a *difference of rescalings* of the fixed cutoff `η`; its modulation is
`φ_{N,t}(ξ) = φ_N(ξ)·e(Ntξ)`, `e(x) = exp(2πix)`.

This file records the elementary facts that the analytic chapters need about `φ_{N,t}`, with
constants **uniform in `t ∈ [1/2,1]`** (this is what makes it possible to integrate in `t`
afterwards):

* `φ_{N,t}` vanishes off the ball of radius `2^{k - Log N} + 1`, independently of `t`
  (`varphiN_support`, `varphiNt_support`);
* `φ_{N,t} : ℝ → ℂ` is `C^2` with compact support (`contDiff_varphiNt`,
  `hasCompactSupport_varphiNt`), hence integrable, as are its first two derivatives
  (`integrable_iteratedDeriv_varphiN`, `integrable_iteratedDeriv_varphiNt`);
* the second derivative of the modulated bump is bounded pointwise by the second derivative of the
  unmodulated bump plus the `(2πN)`-multiples of its first derivative and of the bump itself
  (`norm_iteratedDeriv_two_varphiNt_le`), the price of the modulation.

The main theorem `varphiNt_bounds` packages this as: there are `R, S` (depending on `N,k` but not
on `t`) with `0 ≤ S` such that for all `t ∈ [1/2,1]` the bump `φ_{N,t}` vanishes off `[-R,R]`,
is `C^2` with compact support, and both `∫‖φ_{N,t}‖` and `∫‖(φ_{N,t})''‖` are bounded by `S`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The support of the bumps -/

/-- Elementary arithmetic of the support bound: if `2^{L-k}|ξ| < 1` then `|ξ| ≤ 2^{k-L}`. -/
lemma abs_le_of_rpow_mul_lt_one {L : ℝ} {k : ℕ} {ξ : ℝ}
    (h : (2 : ℝ) ^ (L - (k : ℝ)) * |ξ| < 1) : |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - L) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (L - (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h4 : (2 : ℝ) ^ (L - (k : ℝ)) * |ξ| <
      (2 : ℝ) ^ (L - (k : ℝ)) * ((2 : ℝ) ^ (L - (k : ℝ)))⁻¹ := by
    rwa [mul_inv_cancel₀ (ne_of_gt hp)]
  have h5 : |ξ| < ((2 : ℝ) ^ (L - (k : ℝ)))⁻¹ := lt_of_mul_lt_mul_left h4 (le_of_lt hp)
  have h6 : ((2 : ℝ) ^ (L - (k : ℝ)))⁻¹ = (2 : ℝ) ^ ((k : ℝ) - L) := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [h6] at h5
  exact le_of_lt h5

/-- If `η(2^{L-k}ξ) ≠ 0` for the cutoff `η`, then `|ξ| ≤ 2^{k-L}`. -/
lemma abs_le_of_eta_rpow_ne_zero {L : ℝ} {k : ℕ} {ξ : ℝ}
    (h : Work.KMTContract.kmtEta ((2 : ℝ) ^ (L - (k : ℝ)) * ξ) ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - L) := by
  have hlt : ¬ (1 ≤ |(2 : ℝ) ^ (L - (k : ℝ)) * ξ|) :=
    fun hc => h (Work.KMTContract.kmtEta_zero hc)
  have h3 : |(2 : ℝ) ^ (L - (k : ℝ)) * ξ| < 1 := lt_of_not_ge hlt
  have hp : (0 : ℝ) < (2 : ℝ) ^ (L - (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  rw [abs_mul, abs_of_pos hp] at h3
  exact abs_le_of_rpow_mul_lt_one h3

/-- **The support of the KMT bump** `φ_N`: it is supported in `[-2^{k-Log N}, 2^{k-Log N}]`,
at every scale `k` (including the bottom scale `k = 0`). -/
lemma varphiN_support (N k : ℕ) :
    ∀ ξ : ℝ, varphiN N k ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
  intro ξ hξ
  by_cases hk : k = 0
  · subst hk
    simp only [varphiN, if_true] at hξ
    exact abs_le_of_eta_rpow_ne_zero (L := (Work.Analysis.EndVar.logN N : ℝ)) (k := 0)
      (by simpa using hξ)
  · simp only [varphiN, if_neg hk] at hξ
    have hmain : Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * ξ) ≠ 0 ∨
        Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) * ξ) ≠ 0 := by
      by_contra h
      push Not at h
      exact hξ (by rw [h.1, h.2, sub_zero])
    rcases hmain with h | h
    · exact abs_le_of_eta_rpow_ne_zero h
    · have hlt : ¬ (1 ≤ |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) * ξ|) :=
        fun hc => h (Work.KMTContract.kmtEta_zero hc)
      have h3 : |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) * ξ| < 1 :=
        lt_of_not_ge hlt
      have hp : (0 : ℝ) < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) :=
        Real.rpow_pos_of_pos (by norm_num) _
      rw [abs_mul, abs_of_pos hp] at h3
      have hbase : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) ≤
          (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)
      have h2 : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * |ξ| < 1 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbase (abs_nonneg ξ)) h3
      exact abs_le_of_rpow_mul_lt_one h2

/-- The modulation `e(Ntξ)` never vanishes, so the support of `φ_{N,t}` is that of `φ_N`. -/
lemma varphiNt_support (N k : ℕ) (t : ℝ) :
    ∀ ξ : ℝ, varphiNt N k t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
  intro ξ hξ
  refine varphiN_support N k ξ ?_
  intro h
  exact hξ (by simp only [varphiNt, h, zero_mul])

/-! ## Smoothness of `η` and of the bumps -/

@[fun_prop]
lemma contDiff_ofReal_aux (n : ℕ) : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff (n := n)

/-- The cutoff `η` is smooth. -/
lemma contDiff_kmtEta (n : ℕ) : ContDiff ℝ n (fun x : ℝ => Work.KMTContract.kmtEta x) := by
  have h1 : ContDiff ℝ n ((Work.KMTContract.kmtBump : ℝ → ℝ)) := ContDiffBump.contDiff _
  have h2 : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) := contDiff_ofReal_aux n
  have h3 := h2.comp h1
  simpa [Function.comp_def, Work.KMTContract.kmtEta] using h3

/-- The bump `φ_N` is `C^2`. -/
lemma contDiff_varphiN (N k : ℕ) : ContDiff ℝ 2 (varphiN N k) := by
  unfold varphiN
  split
  · exact (contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)
  · exact ((contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)).sub
      ((contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id))

/-- The exponential `e(c·)` has modulus one. -/
lemma norm_ee (y : ℝ) : ‖ee y‖ = 1 := by
  simp only [ee, Complex.norm_exp]
  rw [show (2 * ↑Real.pi * Complex.I * ↑y).re = 0 by simp, Real.exp_zero]

/-- The norm of the frequency `2πi c`. -/
lemma norm_A (c : ℝ) : ‖(2 * ↑Real.pi * Complex.I * ↑c)‖ = 2 * Real.pi * |c| := by
  rw [norm_mul, norm_mul, norm_mul]
  simp [Complex.norm_I, Real.pi_pos.le]

/-- The derivative of the real parameter on `ℂ`. -/
lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt (fun ξ : ℝ => (ξ : ℂ)) 1 x := by
  simpa using (hasDerivAt_id x).ofReal_comp

lemma ee_const_mul_eq (c ξ : ℝ) :
    ee (c * ξ) = Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ)) := by
  simp only [ee]
  push_cast
  ring_nf

lemma hasDerivAt_ee_const_mul (c x : ℝ) :
    HasDerivAt (fun ξ : ℝ => ee (c * ξ)) ((2 * ↑Real.pi * Complex.I * ↑c) * ee (c * x)) x := by
  have hinner : HasDerivAt (fun ξ : ℝ => (2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ))
      (2 * ↑Real.pi * Complex.I * ↑c) x := by
    simpa using ((hasDerivAt_ofReal x).const_mul (2 * ↑Real.pi * Complex.I * ↑c))
  have key := hinner.cexp
  have hfun : (fun ξ : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ))) =
      (fun ξ : ℝ => ee (c * ξ)) := funext fun ξ => (ee_const_mul_eq c ξ).symm
  rw [hfun] at key
  have hval : (2 * ↑Real.pi * Complex.I * ↑c) * ee (c * x) =
      Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (x : ℂ)) * (2 * ↑Real.pi * Complex.I * ↑c) := by
    rw [ee_const_mul_eq c x]; ring
  rw [hval]
  exact key

lemma deriv_ee_const_mul (c x : ℝ) :
    deriv (fun ξ : ℝ => ee (c * ξ)) x = (2 * ↑Real.pi * Complex.I * ↑c) * ee (c * x) :=
  (hasDerivAt_ee_const_mul c x).deriv

/-- The modulated exponential is `C^n` for every `n`. -/
lemma contDiff_ee_const_mul (n : ℕ) (c : ℝ) : ContDiff ℝ n (fun ξ : ℝ => ee (c * ξ)) := by
  unfold ee
  fun_prop

lemma iteratedDeriv_two_ee_const_mul (c x : ℝ) :
    iteratedDeriv 2 (fun ξ : ℝ => ee (c * ξ)) x =
      (2 * ↑Real.pi * Complex.I * ↑c) ^ 2 * ee (c * x) := by
  have h1 : deriv (fun ξ : ℝ => ee (c * ξ)) =
      fun ξ => (2 * ↑Real.pi * Complex.I * ↑c) * ee (c * ξ) :=
    funext fun ξ => deriv_ee_const_mul c ξ
  have h2 : deriv (fun ξ : ℝ => (2 * ↑Real.pi * Complex.I * ↑c) * ee (c * ξ)) x =
      (2 * ↑Real.pi * Complex.I * ↑c) * deriv (fun ξ : ℝ => ee (c * ξ)) x := by
    rw [deriv_const_mul _ (hasDerivAt_ee_const_mul c x).differentiableAt]
  have h3 : deriv (fun ξ : ℝ => ee (c * ξ)) x = (2 * ↑Real.pi * Complex.I * ↑c) * ee (c * x) :=
    deriv_ee_const_mul c x
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h1]
  rw [h2]
  rw [h3]
  ring

/-- The bump `φ_{N,t}` is `C^2`. -/
lemma contDiff_varphiNt (N k : ℕ) (t : ℝ) : ContDiff ℝ 2 (varphiNt N k t) := by
  unfold varphiNt
  exact (contDiff_varphiN N k).mul (contDiff_ee_const_mul 2 ((N : ℝ) * t))

/-! ## Compact support -/

/-- The bump `φ_N` has compact support. -/
lemma hasCompactSupport_varphiN (N k : ℕ) : HasCompactSupport (varphiN N k) := by
  refine HasCompactSupport.of_support_subset_isCompact (K :=
    Set.Icc (-((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))
      ((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) isCompact_Icc ?_
  intro x hx
  exact abs_le.mp (varphiN_support N k x hx)

/-- The modulated bump `φ_{N,t}` has compact support, uniformly in `t`. -/
lemma hasCompactSupport_varphiNt (N k : ℕ) (t : ℝ) : HasCompactSupport (varphiNt N k t) := by
  refine HasCompactSupport.of_support_subset_isCompact (K :=
    Set.Icc (-((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))
      ((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) isCompact_Icc ?_
  intro x hx
  exact abs_le.mp (varphiNt_support N k t x hx)

/-! ## Integrability -/

lemma integrable_varphiN (N k : ℕ) : Integrable (varphiN N k) :=
  (contDiff_varphiN N k).continuous.integrable_of_hasCompactSupport (hasCompactSupport_varphiN N k)

lemma integrable_varphiNt (N k : ℕ) (t : ℝ) : Integrable (varphiNt N k t) :=
  (contDiff_varphiNt N k t).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_varphiNt N k t)

lemma hcs_iteratedDeriv_varphiN (N k m : ℕ) (hm : m ≤ 2) :
    HasCompactSupport (iteratedDeriv m (varphiN N k)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hasCompactSupport_varphiN N k
  · rw [iteratedDeriv_one]; exact (hasCompactSupport_varphiN N k).deriv
  · rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hasCompactSupport_varphiN N k).deriv).deriv

lemma hcs_iteratedDeriv_varphiNt (N k m : ℕ) (hm : m ≤ 2) (t : ℝ) :
    HasCompactSupport (iteratedDeriv m (varphiNt N k t)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hasCompactSupport_varphiNt N k t
  · rw [iteratedDeriv_one]; exact (hasCompactSupport_varphiNt N k t).deriv
  · rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hasCompactSupport_varphiNt N k t).deriv).deriv

lemma integrable_iteratedDeriv_varphiN (N k m : ℕ) (hm : m ≤ 2) :
    Integrable (fun y => ‖iteratedDeriv m (varphiN N k) y‖) := by
  have hcont : Continuous (iteratedDeriv m (varphiN N k)) :=
    (contDiff_varphiN N k).continuous_iteratedDeriv m (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport (hcs_iteratedDeriv_varphiN N k m hm)).norm

lemma integrable_iteratedDeriv_varphiNt (N k m : ℕ) (hm : m ≤ 2) (t : ℝ) :
    Integrable (fun y => ‖iteratedDeriv m (varphiNt N k t) y‖) := by
  have hcont : Continuous (iteratedDeriv m (varphiNt N k t)) :=
    (contDiff_varphiNt N k t).continuous_iteratedDeriv m (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport (hcs_iteratedDeriv_varphiNt N k m hm t)).norm

/-! ## The pointwise bound for the second derivative of the modulated bump -/

/-- The product rule at order two (Leibniz). -/
lemma iteratedDeriv_two_mul (u v : ℝ → ℂ) (x : ℝ) (hu : ContDiffAt ℝ 2 u x)
    (hv : ContDiffAt ℝ 2 v x) :
    iteratedDeriv 2 (u * v) x =
      iteratedDeriv 2 u x * v x + 2 * (iteratedDeriv 1 u x * iteratedDeriv 1 v x)
        + u x * iteratedDeriv 2 v x := by
  rw [iteratedDeriv_mul hu hv]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.choose_self, iteratedDeriv_zero, Nat.sub_zero, Nat.reduceSub]
  ring

/-- **The price of the modulation**: the second derivative of `u · e(c·)` is controlled by the
second derivative of `u`, the `2π|c|`-multiple of its first derivative, and the `(2π|c|)^2`-multiple
of `u` itself. -/
lemma norm_iteratedDeriv_two_mul_ee_le (u : ℝ → ℂ) (c : ℝ) (hu : ContDiff ℝ 2 u) (x : ℝ) :
    ‖iteratedDeriv 2 (u * fun ξ : ℝ => ee (c * ξ)) x‖ ≤
      ‖iteratedDeriv 2 u x‖ + 2 * (2 * Real.pi * |c|) * ‖iteratedDeriv 1 u x‖
        + (2 * Real.pi * |c|) ^ 2 * ‖u x‖ := by
  have hv : ContDiffAt ℝ 2 (fun ξ : ℝ => ee (c * ξ)) x := (contDiff_ee_const_mul 2 c).contDiffAt
  rw [iteratedDeriv_two_mul u (fun ξ : ℝ => ee (c * ξ)) x hu.contDiffAt hv]
  have e1 : iteratedDeriv 1 (fun ξ : ℝ => ee (c * ξ)) x =
      (2 * ↑Real.pi * Complex.I * ↑c) * ee (c * x) := by
    rw [iteratedDeriv_one]; exact deriv_ee_const_mul c x
  have e2 : iteratedDeriv 2 (fun ξ : ℝ => ee (c * ξ)) x =
      (2 * ↑Real.pi * Complex.I * ↑c) ^ 2 * ee (c * x) := iteratedDeriv_two_ee_const_mul c x
  have hP1 : ‖iteratedDeriv 2 u x * (fun ξ : ℝ => ee (c * ξ)) x‖ = ‖iteratedDeriv 2 u x‖ := by
    rw [norm_mul, norm_ee, mul_one]
  have hP2 : ‖(2 : ℂ) * (iteratedDeriv 1 u x * iteratedDeriv 1 (fun ξ : ℝ => ee (c * ξ)) x)‖ =
      2 * (2 * Real.pi * |c|) * ‖iteratedDeriv 1 u x‖ := by
    rw [e1, norm_mul, norm_mul, norm_mul, norm_A, norm_ee, Complex.norm_ofNat]
    ring
  have hP3 : ‖u x * iteratedDeriv 2 (fun ξ : ℝ => ee (c * ξ)) x‖ =
      (2 * Real.pi * |c|) ^ 2 * ‖u x‖ := by
    rw [e2, norm_mul, norm_mul, norm_pow, norm_A, norm_ee, mul_one]
    ring
  refine le_trans (le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)) (le_of_eq ?_)
  rw [hP1, hP2, hP3]

/-- The same bound, with the modulation frequency `Nt` replaced by `N`, valid for `t ∈ [1/2,1]`. -/
lemma norm_iteratedDeriv_two_varphiNt_le (N k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
    (y : ℝ) :
    ‖iteratedDeriv 2 (fun ξ : ℝ => varphiN N k ξ * ee (((N : ℝ) * t) * ξ)) y‖ ≤
      ‖iteratedDeriv 2 (varphiN N k) y‖ + (2 * (2 * Real.pi * (N : ℝ))) *
          ‖iteratedDeriv 1 (varphiN N k) y‖
        + (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiN N k y‖ := by
  have hb := norm_iteratedDeriv_two_mul_ee_le (varphiN N k) ((N : ℝ) * t) (contDiff_varphiN N k) y
  have htabs : |t| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
  have hc : |(N : ℝ) * t| ≤ (N : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg N) htabs
  refine le_trans hb ?_
  have h1 : 2 * (2 * Real.pi * |(N : ℝ) * t|) * ‖iteratedDeriv 1 (varphiN N k) y‖ ≤
      2 * (2 * Real.pi * (N : ℝ)) * ‖iteratedDeriv 1 (varphiN N k) y‖ := by
    gcongr
  have h2 : (2 * Real.pi * |(N : ℝ) * t|) ^ 2 * ‖varphiN N k y‖ ≤
      (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiN N k y‖ := by
    gcongr
  linarith

/-! ## The main statement -/

theorem varphiNt_bounds (N k : ℕ) :
    ∃ R S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      (∀ y : ℝ, R ≤ |y| → Work.KMTAreas.A7.varphiNt N k t y = 0) ∧
      ContDiff ℝ 2 (fun ξ => Work.KMTAreas.A7.varphiNt N k t ξ) ∧
      HasCompactSupport (fun ξ => Work.KMTAreas.A7.varphiNt N k t ξ) ∧
      (∫ y, ‖Work.KMTAreas.A7.varphiNt N k t y‖) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => Work.KMTAreas.A7.varphiNt N k t ξ) y‖) ≤ S := by
  set R : ℝ := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) + 1 with hR
  set A : ℝ := ∫ y, ‖varphiN N k y‖ with hA
  set B : ℝ := ∫ y, ‖iteratedDeriv 1 (varphiN N k) y‖ with hB
  set C : ℝ := ∫ y, ‖iteratedDeriv 2 (varphiN N k) y‖ with hC
  set S : ℝ := A + 2 * (2 * Real.pi * (N : ℝ)) * B + (2 * Real.pi * (N : ℝ)) ^ 2 * A + C + 1
    with hS
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun y => norm_nonneg _)
  have hC0 : 0 ≤ C := by rw [hC]; exact integral_nonneg (fun y => norm_nonneg _)
  have h1 : 0 ≤ 2 * (2 * Real.pi * (N : ℝ)) * B :=
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hB0
  have h2 : 0 ≤ (2 * Real.pi * (N : ℝ)) ^ 2 * A := mul_nonneg (by positivity) hA0
  refine ⟨R, S, ?_, ?_⟩
  · linarith
  · intro t ht
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      by_contra hne
      have hb := varphiNt_support N k t y hne
      rw [hR] at hy
      linarith
    · exact contDiff_varphiNt N k t
    · exact hasCompactSupport_varphiNt N k t
    · have hcongr : (fun y => ‖varphiNt N k t y‖) = fun y => ‖varphiN N k y‖ := by
        funext y
        rw [varphiNt, norm_mul, norm_ee, mul_one]
      rw [hcongr, ← hA, hS]
      linarith
    · have hpt : ∀ y, ‖iteratedDeriv 2 (fun ξ => varphiNt N k t ξ) y‖ ≤
            ‖iteratedDeriv 2 (varphiN N k) y‖ +
              (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (varphiN N k) y‖ +
              (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiN N k y‖ := by
        intro y
        have h := norm_iteratedDeriv_two_varphiNt_le N k t ht y
        simpa only [varphiNt] using h
      have hI1 : Integrable (fun y => ‖iteratedDeriv 2 (varphiN N k) y‖) :=
        integrable_iteratedDeriv_varphiN N k 2 le_rfl
      have hI2 : Integrable (fun y => (2 * (2 * Real.pi * (N : ℝ))) *
          ‖iteratedDeriv 1 (varphiN N k) y‖) :=
        (integrable_iteratedDeriv_varphiN N k 1 (by norm_num)).const_mul _
      have hI3 : Integrable (fun y => (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiN N k y‖) := by
        simpa using ((integrable_varphiN N k).norm).const_mul ((2 * Real.pi * (N : ℝ)) ^ 2)
      have hI12 : Integrable (fun y => ‖iteratedDeriv 2 (varphiN N k) y‖ +
          (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (varphiN N k) y‖) := hI1.add hI2
      have hLint : Integrable (fun y => ‖iteratedDeriv 2 (fun ξ => varphiNt N k t ξ) y‖) :=
        integrable_iteratedDeriv_varphiNt N k 2 le_rfl t
      have hmono := integral_mono hLint ((hI1.add hI2).add hI3) hpt
      have heq : (∫ y, (‖iteratedDeriv 2 (varphiN N k) y‖ +
              (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (varphiN N k) y‖ +
              (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiN N k y‖))
          = C + (2 * (2 * Real.pi * (N : ℝ))) * B + (2 * Real.pi * (N : ℝ)) ^ 2 * A := by
        rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul,
          integral_const_mul, ← hA, ← hB, ← hC]
      have hfinal : (∫ y, ‖iteratedDeriv 2 (fun ξ => varphiNt N k t ξ) y‖) ≤
          C + (2 * (2 * Real.pi * (N : ℝ))) * B + (2 * Real.pi * (N : ℝ)) ^ 2 * A :=
        le_trans hmono (le_of_eq heq)
      rw [hS]
      linarith

end Work.KMTAreas.A7
