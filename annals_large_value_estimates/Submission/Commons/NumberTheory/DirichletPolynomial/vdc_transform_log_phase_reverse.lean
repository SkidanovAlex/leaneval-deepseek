import Mathlib
import Submission.Commons.Analysis.Calculus.iteratedDeriv_smoothTransition_scale_bound
import Submission.Commons.Analysis.Fourier.poisson_log_phase
import Submission.Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay
import Submission.Commons.Analysis.StationaryPhase.log_phase_prim_left_general
import Submission.Commons.Analysis.StationaryPhase.log_phase_stationary_phase
import Submission.Commons.Analysis.StationaryPhase.log_phase_half_line_left
import Submission.Commons.Analysis.Log.log_two_add_le
import Submission.Commons.Analysis.StationaryPhase.log_phase_prim_right_general
import Submission.Commons.Analysis.Oscillatory.first_derivative_test_ibp
import Submission.Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_hasDerivAt_deriv_ge_mono
import Submission.Commons.Analysis.Oscillatory.norm_integral_exp_two_ibp
import Submission.Commons.Analysis.Summation.abel_prefix_bound
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test
import Submission.Commons.Analysis.Harmonic.sum_inv_sub_le
import Submission.Commons.Analysis.Harmonic.sum_inv_sq_sub_le

open Complex MeasureTheory Real Finset
open scoped Real BigOperators Topology FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Commons.NumberTheory.DirichletPolynomial

noncomputable section

variable {d : ℝ}

/-!
# The van der Corput transform error (`vdc_transform_error`)

Target:
`∃ C > 0, ∀ N ≥ 1, ∀ t ≥ 1,`
`‖Σ_{N≤n≤2N} n^{it} − (t/2π)^{1+it} · F(t) · Σ_{⌈t/4πN⌉≤k≤⌊t/2πN⌋} k^{-1-it}‖`
`    ≤ C·(N/√t + log(Nt) + 1)`,
where `F(t) = ∫_{1/2}^{6} exp(i t (log y − y)) dy`.

The proof follows the standard Poisson-summation/stationary-phase route:
with the smooth weight `vw` (= 1 on `[N,2N]`, supported in `[N−1/2, 2N+1]`),

* `Σ_{n∈[N,2N]} n^{it} = Σ_{n∈ℤ} vw(n) n^{it} = Σ_{k∈ℤ} I_k`,
  `I_k = ∫ vw(x) e^{iθ_k(x)} dx`, `θ_k(x) = t log x − 2πkx` (commons `poisson_log_phase`);
* for `k` in the dual range (`x_k = t/(2πk) ∈ [N,2N]`) the integral `I_k` is
  `x_k^{1+it} ∫_{A_k}^{B_k} vw(x_k y) e^{iφ(y)} dy` with `φ(y) = t(log y − y)`; the
  stationary phase point `y = 1` lies in `[A_k,B_k] = [(N−1/2)/x_k, (2N+1)/x_k]`, so
  `I_k − x_k^{1+it}F` is small;
* outside the dual range the stationary point is (at worst) near the boundary, and the
  integrals are small by the first-order test (van der Corput) or cancel in `k` (strips).
-/

/-! ## 1. The smooth weight `vw` -/

/-- Smooth weight with transition width `d` (`d > 0`): `= 1` on `[N,2N]`, `= 0` on `(-∞,N-d]`
and on `[2N+d,∞)`.  Taking `d` small makes the transition regions narrow. -/
def vw (d : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x - ((N : ℝ) - d)) / d)
    * (1 - Real.smoothTransition ((x - 2 * (N : ℝ)) / d))

lemma vw_contDiff (d : ℝ) (N : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vw d N) := by
  unfold vw; fun_prop

lemma vw_eq_one {d : ℝ} (hd : 0 < d) {N : ℕ} {x : ℝ} (h1 : (N : ℝ) ≤ x)
    (h2 : x ≤ 2 * (N : ℝ)) : vw d N x = 1 := by
  unfold vw
  have ha : (1 : ℝ) ≤ (x - ((N : ℝ) - d)) / d := by
    rw [le_div_iff₀ hd]; linarith
  have hc : (x - 2 * (N : ℝ)) / d ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  rw [Real.smoothTransition.one_of_one_le ha, Real.smoothTransition.zero_of_nonpos hc]
  ring

lemma vw_eq_zero_of_le {d : ℝ} (hd : 0 < d) {N : ℕ} {x : ℝ} (h : x ≤ (N : ℝ) - d) :
    vw d N x = 0 := by
  unfold vw
  have ha : (x - ((N : ℝ) - d)) / d ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  rw [Real.smoothTransition.zero_of_nonpos ha]
  ring

lemma vw_eq_zero_of_ge {d : ℝ} (hd : 0 < d) {N : ℕ} {x : ℝ} (h : 2 * (N : ℝ) + d ≤ x) :
    vw d N x = 0 := by
  unfold vw
  have hc : (1 : ℝ) ≤ (x - 2 * (N : ℝ)) / d := by
    rw [le_div_iff₀ hd]; linarith
  rw [Real.smoothTransition.one_of_one_le hc]
  ring

lemma vw_half_zero {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (h : x ≤ 1/2) : vw d N x = 0 := by
  refine vw_eq_zero_of_le hd ?_
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

lemma vw_hasCompactSupport {d : ℝ} (hd : 0 < d) (N : ℕ) : HasCompactSupport (vw d N) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (N : ℝ) - d) (b := 2 * (N : ℝ) + d)) ?_
  intro x hx
  rw [Set.mem_Icc] at hx
  rw [not_and_or] at hx
  rcases hx with hx | hx
  · refine vw_eq_zero_of_le hd ?_
    have := not_le.mp hx
    linarith
  · refine vw_eq_zero_of_ge hd ?_
    have := not_le.mp hx
    linarith

lemma vw_nonneg (d : ℝ) (N : ℕ) (x : ℝ) : 0 ≤ vw d N x := by
  unfold vw
  have h : 0 ≤ 1 - Real.smoothTransition ((x - 2 * (N : ℝ)) / d) := by
    have := Real.smoothTransition.le_one ((x - 2 * (N : ℝ)) / d); linarith
  exact mul_nonneg (Real.smoothTransition.nonneg _) h

lemma vw_le_one (d : ℝ) (N : ℕ) (x : ℝ) : vw d N x ≤ 1 := by
  unfold vw
  have h1 : Real.smoothTransition ((x - ((N : ℝ) - d)) / d) ≤ 1 :=
    Real.smoothTransition.le_one _
  have h2 : 1 - Real.smoothTransition ((x - 2 * (N : ℝ)) / d) ≤ 1 := by
    have := Real.smoothTransition.nonneg ((x - 2 * (N : ℝ)) / d); linarith
  have h3 : 0 ≤ 1 - Real.smoothTransition ((x - 2 * (N : ℝ)) / d) := by
    have := Real.smoothTransition.le_one ((x - 2 * (N : ℝ)) / d); linarith
  calc Real.smoothTransition ((x - ((N : ℝ) - d)) / d)
        * (1 - Real.smoothTransition ((x - 2 * (N : ℝ)) / d))
      ≤ 1 * 1 := mul_le_mul h1 h2 h3 (by norm_num)
    _ = 1 := by ring

lemma vw_nat_eq_one {d : ℝ} (hd : 0 < d) {N : ℕ} {n : ℕ} (h1 : N ≤ n) (h2 : n ≤ 2 * N) :
    vw d N (n : ℝ) = 1 :=
  vw_eq_one hd (by exact_mod_cast h1) (by exact_mod_cast h2)

lemma vw_nat_eq_zero_of_lt {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2) {N : ℕ} {n : ℕ} (h : n < N) :
    vw d N (n : ℝ) = 0 := by
  refine vw_eq_zero_of_le hd ?_
  have h1 : n + 1 ≤ N := h
  have : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h1
  linarith

lemma vw_nat_eq_zero_of_gt {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2) {N : ℕ} {n : ℕ}
    (h : 2 * N < n) : vw d N (n : ℝ) = 0 := by
  refine vw_eq_zero_of_ge hd ?_
  have h1 : 2 * N + 1 ≤ n := h
  have : (2 : ℝ) * (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
  linarith

/-! ## 2. The Poisson integrals and the target quantities -/

/-- The `k`-th Poisson integral `∫ vw(x) exp (i (t log x − 2π k x)) dx`. -/
noncomputable def vdcI (d : ℝ) (N : ℕ) (t : ℝ) (k : ℤ) : ℂ :=
  ∫ x : ℝ, (vw d N x : ℂ)
    * Complex.exp (Complex.I * (((t * Real.log x - 2 * Real.pi * (k : ℝ) * x : ℝ)) : ℂ))

/-- The Dirichlet sum `Σ_{N ≤ n ≤ 2N} n^{it}`. -/
noncomputable def vdcS (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (t : ℂ))

/-- The Fourier window `F(t) = ∫_{1/2}^{6} exp (i t (log y − y)) dy`. -/
noncomputable def vdcF (t : ℝ) : ℂ :=
  ∫ y in (1 / 2 : ℝ)..6, Complex.exp (Complex.I * (((t * (Real.log y - y) : ℝ)) : ℂ))

/-- The dual sum `Σ_{⌈t/4πN⌉ ≤ k ≤ ⌊t/2πN⌋} k^{-1-it}`. -/
noncomputable def vdcD (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (Nat.ceil (t / (4 * Real.pi * (N : ℝ))))
      (Nat.floor (t / (2 * Real.pi * (N : ℝ)))),
    (k : ℂ) ^ (-(Complex.I * (t : ℂ))) / (k : ℂ)

/-- The main term of the van der Corput transform. -/
noncomputable def vdcMain (N : ℕ) (t : ℝ) : ℂ :=
  ((t / (2 * Real.pi) : ℝ) : ℂ) ^ ((1 : ℂ) + Complex.I * (t : ℂ)) * vdcF t * vdcD N t

/-- The stationary point `x_k = t/(2πk)`. -/
noncomputable def vdcX (t : ℝ) (k : ℕ) : ℝ := t / (2 * Real.pi * (k : ℝ))

lemma vdcX_pos {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) : 0 < vdcX t k := by
  unfold vdcX; positivity

/-! ### The Poisson step -/

lemma vw_int_zero_of_notMem {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) {n : ℤ}
    (hn : n < (N : ℤ) ∨ (2 * N : ℤ) < n) : vw d N (n : ℝ) = 0 := by
  rcases hn with hn | hn
  · rcases lt_or_ge n 0 with h | h
    · exact vw_half_zero hd hd1 hN (by
        have : (n : ℝ) < 0 := by exact_mod_cast h
        linarith)
    · have h' : n.toNat < N := by
        have : n < (N : ℤ) := hn
        omega
      have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg h)
      rw [← hcast]
      exact vw_nat_eq_zero_of_lt hd hd1 h'
  · have h' : 2 * N < n.toNat := by
      have : (2 * N : ℤ) < n := hn
      omega
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ n))
    rw [← hcast]
    exact vw_nat_eq_zero_of_gt hd hd1 h'

lemma cpow_I_mul_eq_exp_log {t : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (Complex.I * (t : ℂ))
      = Complex.exp (Complex.I * (((t * Real.log n : ℝ)) : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : ((Real.log n : ℝ) : ℂ) = Complex.log (n : ℂ) :=
    Complex.ofReal_log (by positivity)
  rw [← hlog]
  congr 1
  push_cast
  ring

/-- Reindex a sum over `{N, …, 2N} ⊂ ℤ` as a sum over `{N, …, 2N} ⊂ ℕ`. -/
lemma sum_Icc_int_eq_sum_Icc_nat (N : ℕ) (g : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc (N : ℤ) (2 * (N : ℤ)), g n.toNat)
      = ∑ m ∈ Finset.Icc N (2 * N), g m := by
  refine Finset.sum_bij' (fun (n : ℤ) _ => n.toNat) (fun (m : ℕ) _ => (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    omega
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ n)]
  · intro m hm
    simp
  · intro n hn
    simp

/-- **Poisson summation for the smoothed Dirichlet sum:**
`Σ_{N≤n≤2N} n^{it} = Σ_{k∈ℤ} I_k`. -/
theorem vdc_poisson (N : ℕ) (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) :
    vdcS N t = ∑' k : ℤ, vdcI d N t k := by
  have hpos : ∀ x : ℝ, x ≤ 1 / 2 → vw d N x = 0 := fun x hx => vw_half_zero hd hd1 hN hx
  have key := Commons.Analysis.Fourier.poisson_log_phase (g := vw d N) (vw_contDiff d N)
    (vw_hasCompactSupport hd N) hpos t
  have h1 : (∑' n : ℤ, (vw d N (n : ℝ) : ℂ)
        * Complex.exp (Complex.I * (((t * Real.log (n : ℝ) : ℝ)) : ℂ)))
      = ∑' k : ℤ, vdcI d N t k := by
    rw [key]
    rfl
  rw [← h1]
  rw [tsum_eq_sum (s := Finset.Icc (N : ℤ) (2 * (N : ℤ)))
    (f := fun n : ℤ => (vw d N (n : ℝ) : ℂ)
      * Complex.exp (Complex.I * (((t * Real.log (n : ℝ) : ℝ)) : ℂ)))]
  · rw [vdcS, ← sum_Icc_int_eq_sum_Icc_nat N]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℤ) ≤ n := by omega
    have hNn : N ≤ n.toNat := by omega
    have h2n : n.toNat ≤ 2 * N := by omega
    have hn1 : 1 ≤ n.toNat := by omega
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hn0)
    rw [← hcast, vw_nat_eq_one hd hNn h2n, cpow_I_mul_eq_exp_log hn1, hcast]
    simp
  · intro b hb
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hb
    rw [vw_int_zero_of_notMem hd hd1 hN (by
      rcases hb with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h))]
    exact zero_mul _

/-! ## 3. Summability of the Poisson series

The Fourier transform of a smooth compactly supported function decays faster than any power, and
`vdcI d N t k` is the Fourier transform of `x ↦ vw d N x · x^{it}` (made globally smooth by a surrogate
for the identity).  Hence `Σ_k I_k` is absolutely summable. -/

/-- Globally smooth positive surrogate for the identity: `= x` for `x ≥ 1/2`, `= 1` for `x ≤ 0`. -/
noncomputable def vdcSm (x : ℝ) : ℝ :=
  x * Real.smoothTransition (2 * x) + (1 - Real.smoothTransition (2 * x))

lemma vdcSm_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) vdcSm := by
  unfold vdcSm; fun_prop

lemma vdcSm_eq_one_of_nonpos {x : ℝ} (h : x ≤ 0) : vdcSm x = 1 := by
  unfold vdcSm
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

lemma vdcSm_eq_self {x : ℝ} (h : 1 / 2 ≤ x) : vdcSm x = x := by
  unfold vdcSm
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

lemma vdcSm_pos (x : ℝ) : 0 < vdcSm x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [vdcSm_eq_one_of_nonpos hx]; norm_num
  · rcases le_or_gt (1/2) x with h1 | h1
    · rw [vdcSm_eq_self h1]; linarith
    · have hs1 : Real.smoothTransition (2 * x) < 1 :=
        Real.smoothTransition.lt_one_of_lt_one (by linarith)
      have hlt : Real.smoothTransition (2 * x) * (1 - x) < 1 := by
        have h1x : 0 < 1 - x := by
          have := Real.smoothTransition.nonneg (2 * x); linarith
        calc Real.smoothTransition (2 * x) * (1 - x) < 1 * (1 - x) :=
              mul_lt_mul_of_pos_right hs1 h1x
          _ < 1 := by linarith
      have : vdcSm x = 1 - Real.smoothTransition (2 * x) * (1 - x) := by
        unfold vdcSm; ring
      rw [this]; linarith

/-- The smooth compactly supported function with `𝓕 (vdcFourier d N t) k = vdcI d N t k`. -/
noncomputable def vdcFourier (d : ℝ) (N : ℕ) (t : ℝ) : ℝ → ℂ := fun x =>
  (vw d N x : ℂ) * Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (vdcSm x) : ℝ) : ℂ)))

lemma vdcFourier_contDiff (N : ℕ) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vdcFourier d N t) := by
  have hlog : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Real.log (vdcSm x)) :=
    vdcSm_contDiff.log (fun x => ne_of_gt (vdcSm_pos x))
  have hlogC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => ((Real.log (vdcSm x) : ℝ) : ℂ)) := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (⇑Complex.ofRealCLM ∘ fun x => Real.log (vdcSm x))
    exact Complex.ofRealCLM.contDiff.comp hlog
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => ((t : ℂ) * ((Real.log (vdcSm x) : ℝ) : ℂ))) :=
    contDiff_const.mul hlogC
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (vdcSm x) : ℝ) : ℂ)))) := by
    refine Complex.contDiff_exp.comp ?_
    exact contDiff_const.mul h1
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ((vw d N x : ℝ) : ℂ)) := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Complex.ofRealCLM ∘ vw d N)
    exact Complex.ofRealCLM.contDiff.comp (vw_contDiff d N)
  exact h3.mul h2

lemma vdcFourier_hasCompactSupport (N : ℕ) (hd : 0 < d) (t : ℝ) :
    HasCompactSupport (vdcFourier d N t) := by
  have h1 : HasCompactSupport (fun x : ℝ => ((vw d N x : ℝ) : ℂ)) :=
    (vw_hasCompactSupport hd N).comp_left Complex.ofReal_zero
  exact h1.mul_right

lemma fourier_vdcFourier (N : ℕ) (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) (k : ℤ) :
    𝓕 (vdcFourier d N t) k = vdcI d N t k := by
  rw [Real.fourier_eq']
  rw [vdcI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, Real.inner_apply, vdcFourier]
  by_cases hvw : vw d N x = 0
  · rw [hvw]
    simp only [Complex.ofReal_zero, zero_mul, mul_zero]
  · have hx : (1 / 2 : ℝ) < x := by
      by_contra hcon
      push Not at hcon
      exact hvw (vw_half_zero hd hd1 hN hcon)
    rw [vdcSm_eq_self (le_of_lt hx)]
    have hexp : Complex.exp (↑(-2 * Real.pi * (x * ↑k)) * Complex.I)
          * Complex.exp (Complex.I * ((t : ℂ) * ↑(Real.log x)))
        = Complex.exp (Complex.I * ↑(t * Real.log x - 2 * Real.pi * ↑k * x)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc Complex.exp (↑(-2 * Real.pi * (x * ↑k)) * Complex.I)
          * (↑(vw d N x) * Complex.exp (Complex.I * ((t : ℂ) * ↑(Real.log x))))
        = ↑(vw d N x) * (Complex.exp (↑(-2 * Real.pi * (x * ↑k)) * Complex.I)
            * Complex.exp (Complex.I * ((t : ℂ) * ↑(Real.log x)))) := by ring
      _ = ↑(vw d N x) * Complex.exp (Complex.I * ↑(t * Real.log x - 2 * Real.pi * ↑k * x)) := by
            rw [hexp]

/-- **Absolute summability of the Poisson series.** -/
lemma summable_vdcI (N : ℕ) (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) :
    Summable (fun k : ℤ => vdcI d N t k) := by
  obtain ⟨C, _hC0, hC⟩ :=
    Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay 2
      (vdcFourier_contDiff (d := d) N t) (vdcFourier_hasCompactSupport N hd t)
  have hnat : Summable (fun n : ℕ => C / ((n : ℤ) : ℝ) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)
    have := h.mul_left C
    refine this.congr fun n => ?_
    push_cast
    ring
  have hg : Summable (fun k : ℤ => C / (k : ℝ) ^ 2) := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · simpa using hnat
    · have := hnat
      refine this.congr fun n => ?_
      push_cast
      ring
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton (0 : ℤ)) ?_
  intro k hk
  by_contra hk0
  refine hk ?_
  have hk' : (k : ℝ) ≠ 0 := by
    intro h
    exact hk0 (by exact_mod_cast h)
  rw [← fourier_vdcFourier N hd hd1 hN t k]
  calc ‖𝓕 (vdcFourier d N t) (k : ℝ)‖ ≤ C / |(k : ℝ)| ^ 2 := hC (k : ℝ) hk'
    _ = C / (k : ℝ) ^ 2 := by rw [sq_abs]

/-! ## 4. Rewriting the main term -/

lemma ofReal_cpow_exp {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x : ℝ) : ℂ) ^ s = Complex.exp (((Real.log x : ℝ) : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hx), Complex.ofReal_log hx.le]

/-- The cpow identity splitting `(t/(2πk))^{1+it}` into the product
`(t/(2π))^{1+it} · k^{-1-it}`. -/
lemma cpow_div_mul {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) :
    ((t / (2 * Real.pi * (k : ℝ)) : ℝ) : ℂ) ^ ((1 : ℂ) + Complex.I * (t : ℂ))
      = ((t / (2 * Real.pi) : ℝ) : ℂ) ^ ((1 : ℂ) + Complex.I * (t : ℂ))
        * ((k : ℂ) ^ (-(Complex.I * (t : ℂ))) * (k : ℂ)⁻¹) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hk0)
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hA : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht h2π
  have hAB : (0 : ℝ) < t / (2 * Real.pi * (k : ℝ)) := by positivity
  have hlog : Real.log (t / (2 * Real.pi * (k : ℝ)))
      = Real.log (t / (2 * Real.pi)) - Real.log (k : ℝ) := by
    rw [show t / (2 * Real.pi * (k : ℝ)) = (t / (2 * Real.pi)) * ((k : ℝ))⁻¹ by ring]
    rw [Real.log_mul (ne_of_gt hA) (inv_ne_zero (ne_of_gt hk0)), Real.log_inv]
    ring
  have hkpow : (k : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = Complex.exp (-(Complex.I * (t : ℂ)) * ((Real.log (k:ℝ) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hkC, ← Complex.ofReal_natCast, Complex.ofReal_log hk0.le,
      mul_comm]
  have hkexp : (k : ℂ)⁻¹ = Complex.exp (-((Real.log (k : ℝ) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    rw [show (((k : ℝ))⁻¹) = Real.exp (-(Real.log (k : ℝ))) by
        rw [Real.exp_neg, Real.exp_log hk0]]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [ofReal_cpow_exp (s := (1 : ℂ) + Complex.I * (t : ℂ)) hAB,
      ofReal_cpow_exp (s := (1 : ℂ) + Complex.I * (t : ℂ)) hA, hkpow, hkexp,
      ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast [hlog]
  ring

/-- The main term is the sum of the stationary-phase values over the dual range. -/
theorem vdcMain_eq (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t) :
    vdcMain N t = ∑ k ∈ Finset.Icc (Nat.ceil (t / (4 * Real.pi * (N : ℝ))))
        (Nat.floor (t / (2 * Real.pi * (N : ℝ)))),
      ((vdcX t k : ℝ) : ℂ) ^ ((1 : ℂ) + Complex.I * (t : ℂ)) * vdcF t := by
  rw [vdcMain, vdcD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := by
    rw [Finset.mem_Icc] at hk
    have : 0 < Nat.ceil (t / (4 * Real.pi * (N : ℝ))) := by
      rw [Nat.ceil_pos]; positivity
    omega
  rw [vdcX, cpow_div_mul ht hk1]
  ring

/-! ## 5. Two general analytic tools -/

/-- **Change of variables `x = c·y`** for a function supported in `[a,b]` (with `f = 0` outside). -/
lemma integral_eq_const_mul_integral_comp_mul (f : ℝ → ℂ) {c : ℝ} (hc : 0 < c)
    {a b : ℝ} (hab : a ≤ b) (hsupp : ∀ x : ℝ, x ∉ Set.Icc a b → f x = 0) :
    ∫ x : ℝ, f x = c * ∫ y : ℝ, f (c * y) := by
  have hca : a / c ≤ b / c := div_le_div_of_nonneg_right hab hc.le
  have h1 : (∫ x : ℝ, f x) = ∫ x in a..b, f x := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
      intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h2 : (∫ y : ℝ, f (c * y)) = ∫ y in (a / c)..(b / c), f (c * y) := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_,
      intervalIntegral.integral_of_le hca, MeasureTheory.integral_Icc_eq_integral_Ioc]
    intro y hy
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    refine hsupp _ ?_
    simp only [Set.mem_Icc, not_and_or, not_le]
    rcases hy with h | h
    · refine Or.inl ?_
      have h' : y * c < a := by rwa [lt_div_iff₀ hc] at h
      rwa [mul_comm] at h'
    · refine Or.inr ?_
      have h' : b < y * c := by rwa [div_lt_iff₀ hc] at h
      rwa [mul_comm] at h'
  rw [h1, h2]
  have hbnd : (∫ x in a..b, f x) = ∫ x in c * (a / c)..c * (b / c), f x := by
    congr 1 <;> field_simp
  rw [hbnd, ← intervalIntegral.smul_integral_comp_mul_left f c (a := a / c) (b := b / c),
    Complex.real_smul]

/-- **Integration by parts against a primitive bound**: if `∫_a^y exp (i φ)` is bounded by `P` on
`[a,b]` and `W` is `C¹` there, then `∫_a^b W exp (i φ)` is bounded by
`P * (‖W b‖ + ∫_a^b ‖W'‖)`. -/
theorem norm_integral_mul_exp_le_of_primitive_bound {φ : ℝ → ℝ} {W : ℝ → ℂ} {a b P : ℝ}
    (hab : a ≤ b) (hP0 : 0 ≤ P)
    (hφ : ContDiff ℝ 1 φ) (hW : ContDiff ℝ 1 W)
    (hP : ∀ y ∈ Set.Icc a b, ‖∫ s in a..y, Complex.exp (Complex.I * (φ s : ℂ))‖ ≤ P) :
    ‖∫ s in a..b, W s * Complex.exp (Complex.I * (φ s : ℂ))‖
      ≤ P * (‖W b‖ + ∫ s in a..b, ‖deriv W s‖) := by
  set E : ℝ → ℂ := fun y => Complex.exp (Complex.I * (φ y : ℂ)) with hE
  have hEcont : Continuous E := by
    rw [hE]
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hφ.continuous))
  set Prim : ℝ → ℂ := fun y => ∫ s in a..y, E s with hPrim
  have hPrim_deriv : ∀ y ∈ Set.uIcc a b, HasDerivAt Prim (E y) y := by
    intro y hy
    exact intervalIntegral.integral_hasDerivAt_right (hEcont.intervalIntegrable a y)
      (hEcont.stronglyMeasurableAtFilter volume (nhds y)) hEcont.continuousAt
  have hWderiv : ∀ y ∈ Set.uIcc a b, HasDerivAt W (deriv W y) y := fun y _ =>
    (hW.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hW'cont : Continuous (deriv W) := hW.continuous_deriv (by norm_num)
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := W) (v := Prim) (u' := deriv W) (v' := E)
    hWderiv hPrim_deriv (hW'cont.intervalIntegrable a b) (hEcont.intervalIntegrable a b)
  have hzero : Prim a = 0 := by simp [hPrim]
  have hPrim_cont : Continuous Prim := intervalIntegral.continuous_primitive
    (fun a b => hEcont.intervalIntegrable a b) a
  have hnorm : ‖∫ s in a..b, W s * E s‖ ≤ ‖W b‖ * P + P * ∫ s in a..b, ‖deriv W s‖ := by
    rw [hIBP, hzero, mul_zero, sub_zero]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h2 : ‖∫ s in a..b, deriv W s * Prim s‖ ≤ P * ∫ s in a..b, ‖deriv W s‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
      rw [← intervalIntegral.integral_const_mul (a := a) (b := b) P (fun s => ‖deriv W s‖)]
      have hc1 : Continuous (fun s : ℝ => ‖deriv W s * Prim s‖) :=
        Continuous.norm (f := fun s : ℝ => deriv W s * Prim s) (hW'cont.mul hPrim_cont)
      have hc2 : Continuous (fun s : ℝ => P * ‖deriv W s‖) :=
        hW'cont.norm.const_mul P
      refine intervalIntegral.integral_mono_on hab (hc1.intervalIntegrable a b)
        (hc2.intervalIntegrable a b) ?_
      intro s hs
      rw [norm_mul, mul_comm (‖deriv W s‖) (‖Prim s‖)]
      exact mul_le_mul_of_nonneg_right (hP s hs) (norm_nonneg (deriv W s))
    have h3 : ‖Prim b‖ * ‖W b‖ ≤ P * ‖W b‖ :=
      mul_le_mul_of_nonneg_right (hP b (Set.right_mem_Icc.mpr hab)) (norm_nonneg _)
    linarith [h2, h3]
  have hfin : ‖W b‖ * P + P * (∫ s in a..b, ‖deriv W s‖)
      = P * (‖W b‖ + ∫ s in a..b, ‖deriv W s‖) := by ring
  simpa [hE] using hnorm.trans (le_of_eq hfin)

/-! ## 6. Fresnel-scale bounds for the log-phase integral -/

/-- The log-phase integrand `exp (i t (log s − s))`. -/
noncomputable def vdcPhase (t s : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))

lemma continuousOn_vdcPhase (t : ℝ) : ContinuousOn (vdcPhase t) (Set.Icc 1 6) := by
  unfold vdcPhase
  refine Complex.continuous_exp.comp_continuousOn ?_
  refine ContinuousOn.mul continuousOn_const ?_
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  refine ContinuousOn.mul continuousOn_const ?_
  exact (Real.continuousOn_log.mono (fun x hx => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hx.1])).sub continuousOn_id

/-- **Fresnel-scale bound to the right of the stationary point**: for `t ≥ 2` and
`1 ≤ z ≤ q ≤ 6` the log-phase integral over `[z,q]` is `O(1/√t)`; split at `1 + 1/√t` and use
the primitive bound `log_phase_prim_right_general` on the far piece. -/
lemma vdc_half_line_right_145 (t z q : ℝ) (ht : 2 ≤ t) (hz : 1 ≤ z) (hzq : z ≤ q)
    (hq : q ≤ 6) : ‖∫ s in z..q, vdcPhase t s‖ ≤ 145 / Real.sqrt t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have htδ : t * (1 / Real.sqrt t) = Real.sqrt t := by
    rw [mul_one_div, div_eq_iff (ne_of_gt hsqrt), ← sq, Real.sq_sqrt (le_of_lt ht0)]
  have hcont : ContinuousOn (vdcPhase t) (Set.Icc 1 6) := continuousOn_vdcPhase t
  have hbdd : ∀ s : ℝ, ‖vdcPhase t s‖ ≤ 1 := by
    intro s
    rw [vdcPhase, mul_comm]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  rcases le_or_gt (1 + 1 / Real.sqrt t) z with h1 | h1
  · have hz1 : 1 < z := by
      have : (0:ℝ) < 1 / Real.sqrt t := by positivity
      linarith
    have hprim : ‖∫ s in z..q, vdcPhase t s‖
        ≤ min (q - z) (24 * q / (t * (z - 1))) :=
      Commons.Analysis.StationaryPhase.log_phase_prim_right_general t z q (by linarith) hz1 hzq hq
    have hden : t * (1 / Real.sqrt t) ≤ t * (z - 1) :=
      mul_le_mul_of_nonneg_left (by linarith [sub_le_sub_right h1 1] : (1:ℝ)/Real.sqrt t ≤ z - 1)
        (le_of_lt ht0)
    have hbound : 24 * q / (t * (z - 1)) ≤ 144 / Real.sqrt t := by
      calc 24 * q / (t * (z - 1)) ≤ 144 / (t * (1 / Real.sqrt t)) := by
            apply div_le_div₀ (by positivity) (by linarith) (by positivity) hden
        _ = 144 / Real.sqrt t := by rw [htδ]
    calc ‖∫ s in z..q, vdcPhase t s‖ ≤ 24 * q / (t * (z - 1)) :=
          le_trans hprim (min_le_right _ _)
      _ ≤ 144 / Real.sqrt t := hbound
      _ ≤ 145 / Real.sqrt t := by
          rw [div_le_div_iff₀ hsqrt hsqrt]; linarith
  · have hzδ : z < 1 + 1 / Real.sqrt t := h1
    by_cases h2 : 1 + 1 / Real.sqrt t ≤ q
    · have hI1 : IntervalIntegrable (vdcPhase t) volume z (1 + 1 / Real.sqrt t) :=
        ((hcont.mono (by
          intro x hx
          rw [Set.uIcc_of_le (by linarith : z ≤ 1 + 1 / Real.sqrt t)] at hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)).intervalIntegrable)
      have hI2 : IntervalIntegrable (vdcPhase t) volume (1 + 1 / Real.sqrt t) q :=
        ((hcont.mono (by
          intro x hx
          rw [Set.uIcc_of_le h2] at hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)).intervalIntegrable)
      have hsplit : (∫ s in z..q, vdcPhase t s)
          = (∫ s in z..(1 + 1 / Real.sqrt t), vdcPhase t s)
            + (∫ s in (1 + 1 / Real.sqrt t)..q, vdcPhase t s) :=
        (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hA : ‖∫ s in z..(1 + 1 / Real.sqrt t), vdcPhase t s‖ ≤ 1 / Real.sqrt t := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := z) (b := 1 + 1 / Real.sqrt t) (C := (1:ℝ))
          (fun s _ => hbdd s)
        rw [abs_of_pos (by linarith : (0:ℝ) < 1 + 1 / Real.sqrt t - z), one_mul] at h
        linarith [h, hz]
      have hB : ‖∫ s in (1 + 1 / Real.sqrt t)..q, vdcPhase t s‖ ≤ 144 / Real.sqrt t := by
        have hprim := Commons.Analysis.StationaryPhase.log_phase_prim_right_general t
          (1 + 1 / Real.sqrt t) q (by linarith) (by linarith) h2 hq
        refine le_trans (le_trans hprim (min_le_right _ _)) ?_
        have hq' : 24 * q ≤ 144 := by linarith
        have hden : (0:ℝ) < t * (1 / Real.sqrt t) := by positivity
        calc 24 * q / (t * ((1 + 1 / Real.sqrt t) - 1)) = 24 * q / (t * (1 / Real.sqrt t)) := by
              rw [add_sub_cancel_left]
          _ ≤ 144 / (t * (1 / Real.sqrt t)) := div_le_div_of_nonneg_right hq' (le_of_lt hden)
          _ = 144 / Real.sqrt t := by rw [htδ]
      refine le_trans (add_le_add hA hB) ?_
      rw [← add_div]
      gcongr <;> norm_num
    · have hzq' : q ≤ 1 + 1 / Real.sqrt t := le_of_lt (not_le.mp h2)
      have hA : ‖∫ s in z..q, vdcPhase t s‖ ≤ 1 / Real.sqrt t := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := z) (b := q) (C := (1:ℝ)) (fun s _ => hbdd s)
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ q - z), one_mul] at h
        linarith
      refine le_trans hA ?_
      rw [div_le_div_iff₀ hsqrt hsqrt]
      linarith

lemma vdc_half_line_right :
    ∃ C : ℝ, 0 < C ∧ ∀ (t z q : ℝ), 2 ≤ t → 1 ≤ z → z ≤ q → q ≤ 6 →
      ‖∫ s in z..q, vdcPhase t s‖ ≤ C / Real.sqrt t :=
  ⟨145, by norm_num, fun t z q ht hz hzq hq => vdc_half_line_right_145 t z q ht hz hzq hq⟩



/-! ## The support of `vw` and the phase primitive -/

/-- The left endpoint of the support of `vw d N`. -/
noncomputable def vdcA (d : ℝ) (N : ℕ) : ℝ := (N:ℝ) - d

lemma vdcA_pos {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) :
    0 < vdcA d N := by
  rw [vdcA]
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  linarith

lemma vdcA_le {d : ℝ} (hd : 0 ≤ d) (N : ℕ) : vdcA d N ≤ 2*(N:ℝ) + 1 := by
  rw [vdcA]
  have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  linarith

lemma vw_eq_zero_of_le_A {d : ℝ} (hd : 0 < d) {N : ℕ} {x : ℝ} (h : x ≤ vdcA d N) :
    vw d N x = 0 := by
  rw [vdcA] at h
  exact vw_eq_zero_of_le hd (by linarith)

lemma vw_vdcA_eq_zero {d : ℝ} (hd : 0 < d) (N : ℕ) : vw d N (vdcA d N) = 0 :=
  vw_eq_zero_of_le_A hd le_rfl

lemma vw_vdcA_eq_N {d : ℝ} (hd : 0 < d) (N : ℕ) : vw d N (vdcA d N) = 0 :=
  vw_eq_zero_of_le_A hd le_rfl

lemma vw_eq_zero_of_ge_B {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2) {N : ℕ} {x : ℝ}
    (h : 2*(N:ℝ) + 1 ≤ x) : vw d N x = 0 :=
  vw_eq_zero_of_ge hd (by linarith)

/-! ### A globally smooth surrogate for the log-phase

The phase `x ↦ t log x − 2π k x` of the Poisson integral is not smooth at `0`, so the
commons' first/second-order oscillatory-integral tests cannot be applied to it directly
(they require a globally `C²` phase).  `vdcTheta t k` replaces `log x` by the globally
smooth positive surrogate `log (vdcSm x)`, which agrees with `log x` on `[1/2,∞)` — and
the support of `deriv (vw d N)` lies in `[N−d, 2N+1]` with `N−d ≥ 1/2`. -/

/-- Globally smooth surrogate for the phase `x ↦ t log x − 2π k x`; it agrees with it on `[1/2,∞)`
(where `vdcSm` is the identity). -/
noncomputable def vdcTheta (t k : ℝ) (x : ℝ) : ℝ :=
  t * Real.log (vdcSm x) - 2 * Real.pi * k * x

lemma vdcTheta_contDiff (t k : ℝ) : ContDiff ℝ 2 (vdcTheta t k) := by
  unfold vdcTheta
  have h1 : ContDiff ℝ 2 (fun x : ℝ => Real.log (vdcSm x)) :=
    (vdcSm_contDiff.log (fun x => ne_of_gt (vdcSm_pos x))).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have h2 : ContDiff ℝ 2 (fun x : ℝ => 2 * Real.pi * k * x) := by fun_prop
  exact (contDiff_const.mul h1).sub h2

lemma vdcTheta_eq {t k x : ℝ} (hx : 1/2 ≤ x) :
    vdcTheta t k x = t * Real.log x - 2 * Real.pi * k * x := by
  rw [vdcTheta, vdcSm_eq_self hx]

lemma deriv_vdcTheta {t k x : ℝ} (hx : 1/2 < x) :
    deriv (vdcTheta t k) x = t / x - 2 * Real.pi * k := by
  have hev : vdcSm =ᶠ[𝓝 x] id := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hy' : (1:ℝ)/2 < y := hy
    exact vdcSm_eq_self (le_of_lt hy')
  have h1 : vdcTheta t k =ᶠ[𝓝 x] (fun y => t * Real.log y - 2 * Real.pi * k * y) := by
    filter_upwards [hev] with y hy
    rw [vdcTheta, hy]; rfl
  rw [h1.deriv_eq]
  have hd : HasDerivAt (fun y : ℝ => t * Real.log y - 2 * Real.pi * k * y)
      (t / x - 2 * Real.pi * k) x := by
    have h1 : HasDerivAt (fun y : ℝ => t * Real.log y) (t / x) x := by
      have := (Real.hasDerivAt_log (ne_of_gt (by linarith : (0:ℝ) < x))).const_mul t
      rw [div_eq_mul_inv]
      exact this
    have h2 : HasDerivAt (fun y : ℝ => 2 * Real.pi * k * y) (2 * Real.pi * k) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * k)
    exact h1.sub h2
  exact hd.deriv

lemma vdcTheta_antitone {t k : ℝ} (ht : 0 ≤ t) {a : ℝ} (ha : 1/2 < a) :
    AntitoneOn (deriv (vdcTheta t k)) (Set.Ici a) := by
  have hderiv : ∀ x : ℝ, a ≤ x → deriv (vdcTheta t k) x = t / x - 2 * Real.pi * k :=
    fun x hx => deriv_vdcTheta (by linarith)
  have hmono : AntitoneOn (fun x : ℝ => t / x - 2 * Real.pi * k) (Set.Ici a) := by
    intro x hx y hy hxy
    have hxa : a ≤ x := hx
    have hx0 : 0 < x := by linarith
    have h1 : (1:ℝ)/y ≤ 1/x := one_div_le_one_div_of_le hx0 hxy
    have h2 : t * (1/y) ≤ t * (1/x) := mul_le_mul_of_nonneg_left h1 ht
    have e1 : t / y - 2 * Real.pi * k = t * (1/y) - 2 * Real.pi * k := by ring
    have e2 : t / x - 2 * Real.pi * k = t * (1/x) - 2 * Real.pi * k := by ring
    change t / y - 2 * Real.pi * k ≤ t / x - 2 * Real.pi * k
    rw [e1, e2]; linarith
  intro x hx y hy hxy
  have hxa : a ≤ x := hx
  have hya : a ≤ y := hy
  have h := hmono hx hy hxy
  rw [hderiv x hxa, hderiv y hya]
  simpa using h

/-- The primitive `Φ(y) = ∫_{1/2}^{y} e^{i t (log s - s)}` of the log-phase. -/
noncomputable def vdcPrim (t y : ℝ) : ℂ := ∫ s in (1/2 : ℝ)..y, vdcPhase t s

/-- The tail primitive `Ψ(y) = ∫_y^6 e^{i t (log s - s)}`. -/
noncomputable def vdcTail (t y : ℝ) : ℂ := ∫ s in y..6, vdcPhase t s

lemma continuousOn_vdcPhase_Ioi (t : ℝ) : ContinuousOn (vdcPhase t) (Set.Ioi 0) := by
  unfold vdcPhase
  refine Complex.continuous_exp.comp_continuousOn ?_
  refine continuousOn_const.mul ?_
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  refine continuousOn_const.mul ?_
  exact (Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)).sub continuousOn_id

lemma intervalIntegrable_vdcPhase (t : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (vdcPhase t) volume a b := by
  refine ((continuousOn_vdcPhase_Ioi t).mono ?_).intervalIntegrable
  intro x hx
  rw [Set.mem_uIcc] at hx
  rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact lt_of_lt_of_le ha h1
  · exact lt_of_lt_of_le hb h1

lemma vdcPrim_half (t : ℝ) : vdcPrim t (1/2) = 0 := by simp [vdcPrim]

lemma vdcPrim_six (t : ℝ) : vdcPrim t 6 = vdcF t := by rfl

lemma vdcPrim_sub_eq {t p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    vdcPrim t q - vdcPrim t p = ∫ s in p..q, vdcPhase t s := by
  unfold vdcPrim
  exact intervalIntegral.integral_interval_sub_left (a := (1/2:ℝ)) (b := q) (c := p)
    (intervalIntegrable_vdcPhase t (by norm_num) hq)
    (intervalIntegrable_vdcPhase t (by norm_num) hp)

lemma vdcPrim_add_tail {t y : ℝ} (hy : 0 < y) : vdcPrim t y + vdcTail t y = vdcF t := by
  have h1 : vdcPrim t y + vdcTail t y = vdcPrim t 6 := by
    unfold vdcPrim vdcTail
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_vdcPhase t (by norm_num) hy)
      (intervalIntegrable_vdcPhase t hy (by norm_num))
  rwa [vdcPrim_six] at h1

/-! ### Bounds for the primitives -/

/-- Fresnel bound for `Φ` on `[1/4,6]`, given a left-half-line Fresnel constant `C1`. -/
lemma norm_vdcPrim_le_window (C1 : ℝ)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t)
    {t y : ℝ} (ht : 2 ≤ t) (hy1 : 1/4 ≤ y) (hy2 : y ≤ 6) :
    ‖vdcPrim t y‖ ≤ (C1 + 145)/Real.sqrt t := by
  have ht0 : (0:ℝ) < t := by linarith
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hHLR : ∀ (z q : ℝ), 1 ≤ z → z ≤ q → q ≤ 6 →
      ‖∫ s in z..q, vdcPhase t s‖ ≤ 145/Real.sqrt t :=
    fun z q hz hzq hq => vdc_half_line_right_145 t z q ht hz hzq hq
  rcases le_or_gt 1 y with h | h
  · have hsub : vdcPrim t y - vdcPrim t 1 = ∫ s in (1:ℝ)..y, vdcPhase t s :=
      vdcPrim_sub_eq (by norm_num) (by linarith)
    have h2 : ‖∫ s in (1:ℝ)..y, vdcPhase t s‖ ≤ 145/Real.sqrt t := by
      rcases eq_or_lt_of_le h with he | hl
      · subst he; rw [intervalIntegral.integral_same, norm_zero]; positivity
      · exact hHLR 1 y le_rfl h (by linarith)
    have h1 : ‖vdcPrim t 1‖ ≤ C1/Real.sqrt t := by
      have hh := hC1 t (1/2) 1 ht (by norm_num) (by norm_num) (by norm_num)
      simpa [vdcPrim, vdcPhase] using hh
    have heq : vdcPrim t y = (vdcPrim t y - vdcPrim t 1) + vdcPrim t 1 := by ring
    rw [heq, hsub]
    refine le_trans (norm_add_le _ _) ?_
    rw [add_div]
    linarith [h1, h2]
  · rcases le_or_gt (1/2) y with h2 | h2
    · have hh := hC1 t (1/2) y ht (by norm_num) h2 (le_of_lt h)
      have hb : ‖vdcPrim t y‖ ≤ C1/Real.sqrt t := by simpa [vdcPrim, vdcPhase] using hh
      refine le_trans hb ?_
      rw [div_le_div_iff₀ hs hs]; linarith
    · have hthis : vdcPrim t y = -∫ s in y..(1/2), vdcPhase t s := by
        rw [vdcPrim, intervalIntegral.integral_symm (a := y) (b := (1/2))]
      have hh := hC1 t y (1/2) ht hy1 (le_of_lt h2) (by norm_num)
      have hb : ‖vdcPrim t y‖ ≤ C1/Real.sqrt t := by
        rw [hthis, norm_neg]; simpa [vdcPhase] using hh
      refine le_trans hb ?_
      rw [div_le_div_iff₀ hs hs]; linarith

/-- Harmonic bound for `Φ` to the left of the stationary point. -/
lemma norm_vdcPrim_le_harm {t y : ℝ} (ht : 1 ≤ t) (hy1 : 1/8 ≤ y) (hy2 : y < 1) :
    ‖vdcPrim t y‖ ≤ 48 / (t * (1 - y)) := by
  have ht0 : (0:ℝ) < t := by linarith
  rcases le_or_gt (1/2) y with h | h
  · have hb := Commons.Analysis.StationaryPhase.log_phase_prim_left_general t (1/2) y ht
      (by norm_num) h hy2
    have hb' : ‖vdcPrim t y‖ ≤ min (y - 1/2) (24 / (t * (1 - y))) := by
      simpa [vdcPrim, vdcPhase] using hb
    have h24 : ‖vdcPrim t y‖ ≤ 24 / (t * (1 - y)) := hb'.trans (min_le_right _ _)
    refine le_trans h24 ?_
    gcongr
    norm_num
  · have hthis : vdcPrim t y = -∫ s in y..(1/2), vdcPhase t s := by
      rw [vdcPrim, intervalIntegral.integral_symm (a := y) (b := (1/2))]
    have hb := Commons.Analysis.StationaryPhase.log_phase_prim_left_general t y (1/2) ht hy1
      (le_of_lt h) (by norm_num)
    have hb' : ‖∫ s in y..(1/2), vdcPhase t s‖ ≤ min ((1/2) - y) (24 / (t * (1 - 1/2))) := by
      simpa [vdcPhase] using hb
    have h24 : ‖vdcPrim t y‖ ≤ 48 / t := by
      rw [hthis, norm_neg]
      have hb2 : (24:ℝ)/(t*(1-1/2)) = 48/t := by
        field_simp
        ring
      rw [hb2] at hb'
      exact hb'.trans (min_le_right _ _)
    refine le_trans h24 ?_
    rw [div_le_div_iff₀ ht0 (by positivity)]
    nlinarith [ht0, hy2, h]

/-- Fresnel bound for `Ψ` on `[1,6]`. -/
lemma norm_vdcTail_le_window {t y : ℝ} (ht : 2 ≤ t) (hy1 : 1 ≤ y) (hy2 : y ≤ 6) :
    ‖vdcTail t y‖ ≤ 145 / Real.sqrt t :=
  vdc_half_line_right_145 t y 6 ht hy1 hy2 (by norm_num)

/-- Harmonic bound for `Ψ` to the right of the stationary point. -/
lemma norm_vdcTail_le_harm {t y : ℝ} (ht : 1 ≤ t) (hy1 : 1 < y) (hy2 : y ≤ 6) :
    ‖vdcTail t y‖ ≤ 144 / (t * (y - 1)) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hb := Commons.Analysis.StationaryPhase.log_phase_prim_right_general t y 6 ht hy1 hy2
    (by norm_num)
  have h1 : ‖vdcTail t y‖ ≤ 24 * 6 / (t * (y - 1)) := by
    have hb' : ‖vdcTail t y‖ ≤ min (6 - y) (24 * 6 / (t * (y - 1))) := by
      simpa [vdcTail, vdcPhase] using hb
    exact hb'.trans (min_le_right _ _)
  refine le_trans h1 ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [ht0, hy1]


/-! ### The change of variables `x = x_k y` -/

lemma vdcX_mul (N : ℕ) (t : ℝ) {k : ℕ} (hk : 1 ≤ k) : 2 * Real.pi * (k:ℝ) * vdcX t k = t := by
  have hk0 : ((k:ℝ)) ≠ 0 := by
    have : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
    positivity
  rw [vdcX]
  field_simp

lemma vdcX_pos' {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) : 0 < vdcX t k := vdcX_pos ht hk

/-- `x^{it} = exp (i t log x)` for real `x > 0`. -/
lemma ofReal_cpow_I_mul {x t : ℝ} (hx : 0 < x) :
    ((x:ℝ):ℂ) ^ (Complex.I*(t:ℂ)) = Complex.exp (Complex.I * ((t * Real.log x : ℝ) : ℂ)) := by
  rw [ofReal_cpow_exp hx]
  congr 1
  push_cast
  ring

/-- The `k`-th Poisson integral, after the substitution `x = x_k y`. -/
lemma vdcI_eq_cpow_mul (N : ℕ) (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) {k : ℕ}
    (hk : 1 ≤ k) (ht : 0 < t) :
    vdcI d N t (k:ℤ) = ((vdcX t k : ℝ) : ℂ) ^ ((1:ℂ) + Complex.I * (t:ℂ))
      * ∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y := by
  set x : ℝ := vdcX t k with hxdef
  have hx0 : 0 < x := vdcX_pos ht hk
  have hxk : 2 * Real.pi * (k:ℝ) * x = t := by
    rw [hxdef]; exact vdcX_mul N t hk
  set f : ℝ → ℂ := fun z => (vw d N z : ℂ) *
    Complex.exp (Complex.I * (((t * Real.log z - 2*Real.pi*(k:ℝ)*z : ℝ)) : ℂ)) with hfdef
  have hsupp : ∀ z : ℝ, z ∉ Set.Icc (vdcA d N) (2*(N:ℝ)+1) → f z = 0 := by
    intro z hz
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hz
    have hv : vw d N z = 0 := by
      rcases hz with h | h
      · exact vw_eq_zero_of_le_A hd (le_of_lt h)
      · exact vw_eq_zero_of_ge_B hd hd1 (le_of_lt h)
    simp [hfdef, hv]
  have hA : vdcA d N ≤ 2*(N:ℝ)+1 := vdcA_le (le_of_lt hd) N
  have hstep1 : (∫ z : ℝ, f z) = x * ∫ y : ℝ, f (x*y) :=
    integral_eq_const_mul_integral_comp_mul (f := f) hx0 hA hsupp
  have hlogx : ((x:ℝ):ℂ) = Complex.exp (((Real.log x : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log hx0]
  have hxpow : ((x:ℝ):ℂ) ^ (Complex.I*(t:ℂ))
      = Complex.exp (Complex.I * ((t * Real.log x : ℝ) : ℂ)) := by
    rw [ofReal_cpow_exp hx0]
    congr 1
    push_cast
    ring
  have hpt : ∀ y : ℝ, f (x*y) = (((x:ℝ):ℂ) ^ (Complex.I*(t:ℂ))) *
      ((vw d N (x*y) : ℂ) * vdcPhase t y) := by
    intro y
    rcases le_or_gt y 0 with hy | hy
    · have hxy : x*y ≤ vdcA d N := by
        have h1 : x*y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0.le hy
        linarith [vdcA_pos hd hd1 hN]
      rw [hfdef]
      simp only [vw_eq_zero_of_le_A hd hxy, Complex.ofReal_zero, zero_mul, mul_zero]
    · have hlog : Real.log (x*y) = Real.log x + Real.log y := Real.log_mul (ne_of_gt hx0) (ne_of_gt hy)
      have h2π : 2*Real.pi*(k:ℝ)*(x*y) = t*y := by rw [← hxk]; ring
      have hA' : (t * Real.log (x*y) - 2*Real.pi*(k:ℝ)*(x*y) : ℝ)
          = (t * Real.log x) + (t * Real.log y - t * y) := by
        rw [hlog, h2π]; ring
      have hrearr : Complex.exp (Complex.I * ((t * Real.log x : ℝ) : ℂ)) *
            (↑(vw d N (x*y)) * Complex.exp (Complex.I * ((t * (Real.log y - y) : ℝ) : ℂ)))
          = ↑(vw d N (x*y)) * (Complex.exp (Complex.I * ((t * Real.log x : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((t * (Real.log y - y) : ℝ) : ℂ))) := by ring
      have hX : Complex.I * ((t * Real.log x : ℝ) : ℂ) + Complex.I * ((t * (Real.log y - y) : ℝ) : ℂ)
          = Complex.I * (((t * Real.log x) + (t * Real.log y - t * y) : ℝ) : ℂ) := by
        push_cast; ring
      simp only [hfdef]
      rw [hA', ofReal_cpow_I_mul hx0, vdcPhase, hrearr, ← Complex.exp_add, hX]

  have hstep2 : (∫ y : ℝ, f (x*y))
      = (((x:ℝ):ℂ) ^ (Complex.I*(t:ℂ))) * ∫ y : ℝ, (vw d N (x*y) : ℂ) * vdcPhase t y := by
    rw [show (∫ y : ℝ, f (x*y)) = ∫ y : ℝ, (((x:ℝ):ℂ) ^ (Complex.I*(t:ℂ))) *
        ((vw d N (x*y) : ℂ) * vdcPhase t y) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_const_mul]
  have hLHS : vdcI d N t (k:ℤ) = ∫ z : ℝ, f z := by
    rw [vdcI, hfdef]
    apply integral_congr_ae
    filter_upwards with z
    simp only [Int.cast_natCast]
  rw [hLHS, hstep1, hstep2]
  have hcpow : ((x:ℝ):ℂ) * ((x:ℝ):ℂ)^(Complex.I*(t:ℂ)) = ((x:ℝ):ℂ)^((1:ℂ) + Complex.I*(t:ℂ)) := by
    rw [ofReal_cpow_exp hx0, ofReal_cpow_exp hx0]
    rw [hlogx, ← Complex.exp_add]
    congr 1
    ring
  rw [← hcpow, mul_assoc]


/-! ### Integrals over `ℝ` of functions supported in `[a,b]` -/

lemma integral_eq_intervalIntegral_of_support {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ y : ℝ, y ∉ Set.Icc a b → f y = 0) : ∫ y : ℝ, f y = ∫ y in a..b, f y := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Real-valued version of `integral_eq_intervalIntegral_of_support`. -/
lemma integral_eq_intervalIntegral_of_support_real {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ y : ℝ, y ∉ Set.Icc a b → f y = 0) : ∫ y : ℝ, f y = ∫ y in a..b, f y := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Derivative of `y ↦ vw d N (x*y)`. -/
lemma vw_comp_deriv (N : ℕ) (x y : ℝ) :
    deriv (fun y : ℝ => vw d N (x*y)) y = deriv (vw d N) (x*y) * x := by
  have h1 : HasDerivAt (fun y : ℝ => x*y) x y := by
    simpa using (hasDerivAt_id y).const_mul x
  have h2 : HasDerivAt (vw d N) (deriv (vw d N) (x*y)) (x*y) :=
    ((vw_contDiff d N).differentiable (by norm_num) (x*y)).hasDerivAt
  exact (h2.comp y h1).deriv

/-- The derivative of `vw` vanishes in the middle of the plateau and outside the support. -/
lemma deriv_vw_eq_zero_plateau {N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) {u : ℝ} (h1 : (N:ℝ) < u)
    (h2 : u < 2*(N:ℝ)) : deriv (vw d N) u = 0 := by
  have hev : vw d N =ᶠ[𝓝 u] (fun _ => (1:ℝ)) := by
    filter_upwards [Ioi_mem_nhds h1, Iio_mem_nhds h2] with z hz1 hz2
    exact vw_eq_one hd (le_of_lt hz1) (le_of_lt hz2)
  rw [hev.deriv_eq]
  simp

lemma deriv_vw_zero_of_lt_A {N : ℕ} (hd : 0 < d) {u : ℝ} (h : u < vdcA d N) :
    deriv (vw d N) u = 0 := by
  have hev : vw d N =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds h] with z hz
    exact vw_eq_zero_of_le_A hd (le_of_lt hz)
  rw [hev.deriv_eq]; simp

/-- The derivative of `vw d N` vanishes beyond the right end `2N+d` of its support. -/
lemma deriv_vw_zero_of_gt_B {d : ℝ} {N : ℕ} (hd : 0 < d) {u : ℝ}
    (h : 2*(N:ℝ) + d < u) : deriv (vw d N) u = 0 := by
  have hev : vw d N =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds h] with z hz
    exact vw_eq_zero_of_ge hd (le_of_lt hz)
  rw [hev.deriv_eq]; simp

lemma deriv_vw_eq_zero_right {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) {u : ℝ}
    (h : 2*(N:ℝ) + 1 < u) : deriv (vw d N) u = 0 := by
  have hev : vw d N =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds h] with z hz
    exact vw_eq_zero_of_ge_B hd hd1 (le_of_lt hz)
  rw [hev.deriv_eq]; simp

/-- **Integration by parts** for `J(x) = ∫ vw d N (x y) e^{iφ(y)} dy`. -/
lemma vdc_ibp {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) {t x : ℝ} (hx : 0 < x) :
    ∫ y : ℝ, (vw d N (x*y) : ℂ) * vdcPhase t y
      = -x * ∫ y : ℝ, (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * vdcPrim t y := by
  set a : ℝ := vdcA d N / x with hadef
  set b : ℝ := (2*(N:ℝ)+1)/x with hbdef
  have ha : 0 < a := by rw [hadef]; exact div_pos (vdcA_pos hd hd1 hN) hx
  have hb : 0 < b := by rw [hbdef]; exact div_pos (by positivity) hx
  have hab : a ≤ b := by
    rw [hadef, hbdef]
    exact div_le_div_of_nonneg_right (vdcA_le (le_of_lt hd) N) hx.le
  have hxa : x * a = vdcA d N := by rw [hadef]; field_simp
  have hxb : x * b = 2*(N:ℝ)+1 := by rw [hbdef]; field_simp
  have hs1 : ∀ y : ℝ, y ∉ Set.Icc a b → (vw d N (x*y) : ℂ) * vdcPhase t y = 0 := by
    intro y hy
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    have hv : vw d N (x*y) = 0 := by
      rcases hy with h | h
      · refine vw_eq_zero_of_le_A hd ?_
        have h' : x*y < vdcA d N := by rw [← hxa]; exact mul_lt_mul_of_pos_left h hx
        linarith
      · refine vw_eq_zero_of_ge_B hd hd1 ?_
        have h' : 2*(N:ℝ)+1 < x*y := by rw [← hxb]; exact mul_lt_mul_of_pos_left h hx
        linarith
    rw [hv, Complex.ofReal_zero, zero_mul]
  have hs2 : ∀ y : ℝ, y ∉ Set.Icc a b → (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * vdcPrim t y = 0 := by
    intro y hy
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    have hv : deriv (vw d N) (x*y) = 0 := by
      rcases hy with h | h
      · exact deriv_vw_zero_of_lt_A hd (by rw [← hxa]; exact mul_lt_mul_of_pos_left h hx)
      · exact deriv_vw_eq_zero_right hd hd1 (by rw [← hxb]; exact mul_lt_mul_of_pos_left h hx)
    rw [hv, Complex.ofReal_zero, zero_mul]
  rw [integral_eq_intervalIntegral_of_support hab hs1,
      integral_eq_intervalIntegral_of_support hab hs2]
  have hderiv1 : ∀ y ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => (vw d N (x*y) : ℂ)) ((((deriv (vw d N)) (x*y) : ℝ) : ℂ) * x) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => x*y) x y := by
      simpa using (hasDerivAt_id y).const_mul x
    have h2 : HasDerivAt (vw d N) (deriv (vw d N) (x*y)) (x*y) :=
      ((vw_contDiff d N).differentiable (by norm_num) (x*y)).hasDerivAt
    have h3 : HasDerivAt (fun y : ℝ => vw d N (x*y)) (deriv (vw d N) (x*y) * x) y := h2.comp y h1
    have h4 := h3.ofReal_comp
    have h5 : (((deriv (vw d N) (x*y) * x : ℝ)) : ℂ) = ((((deriv (vw d N)) (x*y) : ℝ) : ℂ)) * x := by
      push_cast; ring
    rwa [h5] at h4
  have hderiv2 : ∀ y ∈ Set.uIcc a b, HasDerivAt (vdcPrim t) (vdcPhase t y) y := by
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hcont : ContinuousAt (vdcPhase t) y :=
      (continuousOn_vdcPhase_Ioi t).continuousAt (isOpen_Ioi.mem_nhds hy0)
    exact intervalIntegral.integral_hasDerivAt_right (a := (1/2:ℝ)) (b := y)
      ((continuousOn_vdcPhase_Ioi t).mono (by
        intro z hz
        rw [Set.mem_uIcc] at hz
        rcases hz with ⟨hz1, _⟩ | ⟨hz1, _⟩
        · exact (lt_of_lt_of_le (by norm_num) hz1)
        · exact (lt_of_lt_of_le hy0 hz1))).intervalIntegrable
      (ContinuousAt.stronglyMeasurableAtFilter (f := vdcPhase t) isOpen_Ioi
        (fun z hz => (continuousOn_vdcPhase_Ioi t).continuousAt (isOpen_Ioi.mem_nhds hz)) y hy0)
      hcont
  have hu'int : IntervalIntegrable (fun y : ℝ => (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * x)
      volume a b := by
    have h1 : Continuous (fun y : ℝ => deriv (vw d N) (x*y)) :=
      ((vw_contDiff d N).continuous_deriv (by norm_num)).comp (continuous_const.mul continuous_id)
    exact ((Complex.continuous_ofReal.comp h1).mul continuous_const).continuousOn.intervalIntegrable
  have hv'int : IntervalIntegrable (vdcPhase t) volume a b := intervalIntegrable_vdcPhase t ha hb
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b)
    (u := fun y : ℝ => (vw d N (x*y) : ℂ)) (v := fun y : ℝ => vdcPrim t y)
    (u' := fun y : ℝ => (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * x) (v' := fun y : ℝ => vdcPhase t y)
    hderiv1 hderiv2 hu'int hv'int
  have hb0 : (vw d N (x*b) : ℂ) = 0 := by rw [hxb, vw_eq_zero_of_ge_B hd hd1 le_rfl]; simp
  have ha0 : (vw d N (x*a) : ℂ) = 0 := by rw [hxa, vw_vdcA_eq_zero hd N]; simp
  rw [hibp, hb0, ha0, zero_mul, zero_mul, sub_zero, zero_sub]
  have hcongr : (∫ y in a..b, (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * x * vdcPrim t y)
      = x * ∫ y in a..b, (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * vdcPrim t y := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun y _ => by ring)
  rw [hcongr]
  ring

/-- The change of variables `u = x y` in the primitive integral. -/
lemma vdc_ibp_subst {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) {t x : ℝ} (hx : 0 < x) :
    x * ∫ y : ℝ, (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * vdcPrim t y
      = ∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x) := by
  have hsupp : ∀ u : ℝ, u ∉ Set.Icc (vdcA d N) (2*(N:ℝ)+1) →
      (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x) = 0 := by
    intro u hu
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    have hv : deriv (vw d N) u = 0 := by
      rcases hu with h | h
      · exact deriv_vw_zero_of_lt_A hd (N := N) h
      · exact deriv_vw_eq_zero_right hd hd1 h
    rw [hv, Complex.ofReal_zero, zero_mul]
  have h := integral_eq_const_mul_integral_comp_mul
    (f := fun u : ℝ => (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)) hx (vdcA_le (le_of_lt hd) N) hsupp
  rw [h]
  have hfun : (fun y : ℝ => (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * vdcPrim t (x*y/x))
      = fun y : ℝ => (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * vdcPrim t y := by
    funext y
    have : x*y/x = y := by field_simp
    rw [this]
  rw [hfun]


/-! ### Total variation of the weight on its two transition intervals -/

lemma vw_eq_prod_of_le {d : ℝ} (hd : 0 < d) {N : ℕ} {u : ℝ} (hu : u ≤ 2*(N:ℝ)) :
    vw d N u = Real.smoothTransition ((u - ((N:ℝ) - d))/d) := by
  rw [vw, show (1 - Real.smoothTransition ((u - 2*(N:ℝ))/d)) = 1 by
    rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)]; ring]
  ring

lemma deriv_vw_nonneg_left {d : ℝ} (hd : 0 < d) {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (h1 : vdcA d N ≤ u) (h2 : u ≤ (N:ℝ)) : 0 ≤ deriv (vw d N) u := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  set A : ℝ → ℝ := fun x => Real.smoothTransition ((x - ((N:ℝ) - d))/d) with hA
  have hu2 : u < 2*(N:ℝ) := by linarith
  have hev : vw d N =ᶠ[𝓝 u] A := by
    filter_upwards [Iio_mem_nhds hu2] with x hx
    rw [hA]
    exact vw_eq_prod_of_le hd (le_of_lt hx)
  rw [hev.deriv_eq]
  have hm : Monotone A := by
    intro x y hxy
    rw [hA]
    exact Real.smoothTransition.monotone (by
      rw [div_le_div_iff_of_pos_right hd]; linarith)
  exact Monotone.deriv_nonneg hm

lemma deriv_vw_nonpos_right {d : ℝ} (hd : 0 < d) {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (h1 : 2*(N:ℝ) ≤ u) : deriv (vw d N) u ≤ 0 := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  by_cases h2 : u ≤ 2*(N:ℝ) + d
  · set R : ℝ → ℝ := fun x => Real.smoothTransition ((x - 2*(N:ℝ))/d) with hR
    have huN : (N:ℝ) < u := by linarith only [hN1, h1]
    have hev : vw d N =ᶠ[𝓝 u] (fun x => 1 - R x) := by
      filter_upwards [Ioi_mem_nhds huN] with x hx
      have hx' : (N:ℝ) < x := hx
      rw [vw, hR]
      have hx1 : (1:ℝ) ≤ (x - ((N:ℝ) - d))/d := by
        rw [le_div_iff₀ hd]; linarith
      rw [Real.smoothTransition.one_of_one_le hx1]; ring
    have hgoal : deriv (vw d N) u = - deriv R u := by
      rw [hev.deriv_eq]
      change deriv ((fun _ : ℝ => (1:ℝ)) - R) u = - deriv R u
      rw [deriv_sub (differentiableAt_const (c := (1:ℝ))) (by fun_prop)]
      simp
    rw [hgoal]
    have hd0 : 0 ≤ deriv R u := by
      have hm : Monotone R := by
        intro x y hxy
        rw [hR]
        exact Real.smoothTransition.monotone (by
          rw [div_le_div_iff_of_pos_right hd]; linarith)
      exact Monotone.deriv_nonneg hm
    linarith
  · have hev : vw d N =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
      filter_upwards [Ioi_mem_nhds (by linarith : 2*(N:ℝ) + d < u)] with x hx
      exact vw_eq_zero_of_ge hd (le_of_lt hx)
    rw [hev.deriv_eq]; simp

lemma integral_abs_deriv_vw_left {d : ℝ} (hd : 0 < d) {N : ℕ} (hN : 1 ≤ N) :
    ∫ u in (vdcA d N)..(N:ℝ), |deriv (vw d N) u| = 1 := by
  have hAN : vdcA d N ≤ (N:ℝ) := by rw [vdcA]; linarith
  have hcongr : ∫ u in (vdcA d N)..(N:ℝ), |deriv (vw d N) u|
      = ∫ u in (vdcA d N)..(N:ℝ), deriv (vw d N) u :=
    intervalIntegral.integral_congr (fun u hu => by
      rw [Set.uIcc_of_le hAN] at hu
      exact abs_of_nonneg (deriv_vw_nonneg_left hd hN hu.1 hu.2))
  rw [hcongr, intervalIntegral.integral_deriv_eq_sub (f := vw d N) (a := vdcA d N) (b := (N:ℝ))]
  · rw [vw_nat_eq_one hd (n := N) le_rfl (by omega), vw_vdcA_eq_zero hd N]; norm_num
  · intro x _
    exact ((vw_contDiff d N).differentiable (by norm_num) x).hasDerivAt.differentiableAt
  · exact ((vw_contDiff d N).continuous_deriv (by norm_num)).intervalIntegrable _ _

lemma integral_abs_deriv_vw_right {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) :
    ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), |deriv (vw d N) u| = 1 := by
  have hcongr : ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), |deriv (vw d N) u|
      = ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (- deriv (vw d N) u) :=
    intervalIntegral.integral_congr (fun u hu => by
      rw [Set.uIcc_of_le (by linarith : 2*(N:ℝ) ≤ 2*(N:ℝ)+1)] at hu
      exact abs_of_nonpos (deriv_vw_nonpos_right hd hN hu.1))
  rw [hcongr, intervalIntegral.integral_neg,
      intervalIntegral.integral_deriv_eq_sub (f := vw d N) (a := 2*(N:ℝ)) (b := 2*(N:ℝ)+1)]
  · have h2N : vw d N (2*(N:ℝ)) = 1 := by
      have h := vw_nat_eq_one hd (N := N) (n := 2*N) (by omega) le_rfl
      simpa using h
    rw [vw_eq_zero_of_ge_B hd hd1 le_rfl, h2N]; norm_num
  · intro x _
    exact ((vw_contDiff d N).differentiable (by norm_num) x).hasDerivAt.differentiableAt
  · exact ((vw_contDiff d N).continuous_deriv (by norm_num)).intervalIntegrable _ _



lemma continuousAt_vdcPrim {t y : ℝ} (hy : 0 < y) : ContinuousAt (vdcPrim t) y := by
  have hcont : ContinuousAt (vdcPhase t) y :=
    (continuousOn_vdcPhase_Ioi t).continuousAt (isOpen_Ioi.mem_nhds hy)
  have hint : IntervalIntegrable (vdcPhase t) volume (1/2) y := by
    refine ((continuousOn_vdcPhase_Ioi t).mono ?_).intervalIntegrable
    intro z hz
    rw [Set.mem_uIcc] at hz
    rcases hz with ⟨hz1, _⟩ | ⟨hz1, _⟩
    · exact lt_of_lt_of_le (by norm_num) hz1
    · exact lt_of_lt_of_le hy hz1
  have hsm : StronglyMeasurableAtFilter (vdcPhase t) (𝓝 y) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (f := vdcPhase t) isOpen_Ioi
      (fun z hz => (continuousOn_vdcPhase_Ioi t).continuousAt (isOpen_Ioi.mem_nhds hz)) y hy
  have h := intervalIntegral.integral_hasDerivAt_right (a := (1/2:ℝ)) (b := y) hint hsm hcont
  exact h.continuousAt

lemma continuousOn_vdcPrim (t : ℝ) : ContinuousOn (vdcPrim t) (Set.Ioi 0) :=
  fun y hy => (continuousAt_vdcPrim hy).continuousWithinAt

lemma continuousOn_vdcTail (t : ℝ) : ContinuousOn (vdcTail t) (Set.Ioi 0) := by
  refine ContinuousOn.congr (f := fun y : ℝ => vdcF t - vdcPrim t y) ?_ ?_
  · exact continuousOn_const.sub (continuousOn_vdcPrim t)
  · intro y hy
    exact eq_sub_of_add_eq (by rw [add_comm]; exact vdcPrim_add_tail hy)



lemma vdcA_le' {N : ℕ} {d : ℝ} (hd : 0 < d) (hN : 1 ≤ N) : vdcA d N ≤ (N:ℝ) := by
  rw [vdcA]; linarith

lemma vdc_mid_integral {N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ u in (N:ℝ)..(2*(N:ℝ)), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x) = 0 := by
  have hsubset : {u : ℝ | ¬(u ∈ Set.uIoc (N:ℝ) (2*(N:ℝ)) →
        (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x) = 0)} ⊆ {2*(N:ℝ)} := by
    intro u hu
    rw [Set.mem_setOf_eq, Classical.not_imp] at hu
    obtain ⟨hu1, hu2⟩ := hu
    rw [Set.uIoc_of_le (by linarith : (N:ℝ) ≤ 2*(N:ℝ))] at hu1
    obtain ⟨hu1a, hu1b⟩ := hu1
    by_contra hne
    simp only [Set.mem_singleton_iff] at hne ⊢
    apply hu2
    have hlt : u < 2*(N:ℝ) := lt_of_le_of_ne hu1b hne
    rw [deriv_vw_eq_zero_plateau hd hN hu1a hlt]
    simp
  have key : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.uIoc (N:ℝ) (2*(N:ℝ)) →
      (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x) = 0 := by
    rw [MeasureTheory.ae_iff]
    exact measure_mono_null hsubset (measure_singleton _)
  rw [intervalIntegral.integral_congr_ae key, intervalIntegral.integral_zero]

lemma vdc_right_integral {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) {x : ℝ}
    (hx : 0 < x) :
    ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)
      = - vdcF t - ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcTail t (u/x) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have h2Npos : (0:ℝ) < 2*(N:ℝ) := by linarith
  have hpos : ∀ u ∈ Set.Icc (2*(N:ℝ)) (2*(N:ℝ)+1), 0 < u/x := fun u hu =>
    div_pos (lt_of_lt_of_le h2Npos hu.1) hx
  have hGcont : Continuous (fun u : ℝ => (((deriv (vw d N)) u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((vw_contDiff d N).continuous_deriv (by norm_num))
  have hPcont : ContinuousOn (fun u : ℝ => vdcPrim t (u/x)) (Set.Icc (2*(N:ℝ)) (2*(N:ℝ)+1)) :=
    (continuousOn_vdcPrim t).comp (continuous_id.div_const x).continuousOn (by
      intro u hu; rw [Set.mem_Ioi]; exact hpos u hu)
  have hQcont : ContinuousOn (fun u : ℝ => vdcTail t (u/x)) (Set.Icc (2*(N:ℝ)) (2*(N:ℝ)+1)) :=
    (continuousOn_vdcTail t).comp (continuous_id.div_const x).continuousOn (by
      intro u hu; rw [Set.mem_Ioi]; exact hpos u hu)
  have hA2 : IntervalIntegrable (fun u : ℝ => (((deriv (vw d N)) u : ℝ) : ℂ) * vdcF t)
      volume (2*(N:ℝ)) (2*(N:ℝ)+1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by linarith : 2*(N:ℝ) ≤ 2*(N:ℝ)+1)]
    exact hGcont.continuousOn.mul continuousOn_const
  have hA3 : IntervalIntegrable (fun u : ℝ => (((deriv (vw d N)) u : ℝ) : ℂ) * vdcTail t (u/x))
      volume (2*(N:ℝ)) (2*(N:ℝ)+1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by linarith : 2*(N:ℝ) ≤ 2*(N:ℝ)+1)]
    exact hGcont.continuousOn.mul hQcont
  have hderivint : ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) = -1 := by
    rw [show (∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ))
        = ((∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), deriv (vw d N) u : ℝ) : ℂ) from by
      rw [← intervalIntegral.integral_ofReal]]
    rw [intervalIntegral.integral_deriv_eq_sub (f := vw d N) (a := 2*(N:ℝ)) (b := 2*(N:ℝ)+1)]
    · rw [vw_eq_zero_of_ge_B hd hd1 le_rfl]
      have h2N : vw d N (2*(N:ℝ)) = 1 := by
        have h := vw_nat_eq_one hd (N := N) (n := 2*N) (by omega) le_rfl
        simpa using h
      rw [h2N]; norm_num
    · intro y _
      exact ((vw_contDiff d N).differentiable (by norm_num) y).hasDerivAt.differentiableAt
    · exact ((vw_contDiff d N).continuous_deriv (by norm_num)).intervalIntegrable _ _
  have hstep1 : ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)
      = ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1),
          (((deriv (vw d N)) u : ℝ) : ℂ) * (vdcF t - vdcTail t (u/x)) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by linarith : 2*(N:ℝ) ≤ 2*(N:ℝ)+1)] at hu
    have hpt : vdcPrim t (u/x) + vdcTail t (u/x) = vdcF t := vdcPrim_add_tail (hpos u hu)
    rw [eq_sub_of_add_eq hpt]
  rw [hstep1]
  have hstep2 : ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1),
        (((deriv (vw d N)) u : ℝ) : ℂ) * (vdcF t - vdcTail t (u/x))
      = (∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ)) * vdcF t
        - ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcTail t (u/x) := by
    rw [show (∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1),
          (((deriv (vw d N)) u : ℝ) : ℂ) * (vdcF t - vdcTail t (u/x)))
        = ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcF t
            - (((deriv (vw d N)) u : ℝ) : ℂ) * vdcTail t (u/x) from
      intervalIntegral.integral_congr (fun u _ => by ring)]
    rw [intervalIntegral.integral_sub hA2 hA3, intervalIntegral.integral_mul_const]
  rw [hstep2, hderivint]
  ring


/-- **The deviation identity**: `J(x) - F = -∫_A^N vw' Φ(·/x) + ∫_{2N}^{2N+1} vw' Ψ(·/x)`. -/
lemma vdc_star {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) {x : ℝ}
    (hx : 0 < x) :
    (∫ y : ℝ, (vw d N (x*y) : ℂ) * vdcPhase t y) - vdcF t
      = - (∫ u in (vdcA d N)..(N:ℝ), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x))
        + (∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcTail t (u/x)) := by
  have hJ : ∫ y : ℝ, (vw d N (x*y) : ℂ) * vdcPhase t y
      = - ∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x) := by
    rw [vdc_ibp hd hd1 hN (t := t) (x := x) hx]
    rw [show (-x * ∫ y : ℝ, (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * vdcPrim t y)
        = -(x * ∫ y : ℝ, (((deriv (vw d N)) (x*y) : ℝ) : ℂ) * vdcPrim t y) from by ring,
      vdc_ibp_subst hd hd1 hN (t := t) (x := x) hx]
  have hsupp : ∀ u : ℝ, u ∉ Set.Icc (vdcA d N) (2*(N:ℝ)+1) →
      (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x) = 0 := by
    intro u hu
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    have hv : deriv (vw d N) u = 0 := by
      rcases hu with h | h
      · exact deriv_vw_zero_of_lt_A hd h
      · exact deriv_vw_eq_zero_right hd hd1 h
    rw [hv]; simp
  have hGcont : Continuous (fun u : ℝ => (((deriv (vw d N)) u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((vw_contDiff d N).continuous_deriv (by norm_num))
  have hcont : ContinuousOn (fun u : ℝ => (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x))
      (Set.Icc (vdcA d N) (2*(N:ℝ)+1)) := by
    refine hGcont.continuousOn.mul ?_
    refine (continuousOn_vdcPrim t).comp (continuous_id.div_const x).continuousOn ?_
    intro u hu
    rw [Set.mem_Ioi]
    exact div_pos (lt_of_lt_of_le (vdcA_pos hd hd1 hN) hu.1) hx
  have hint : ∀ a b : ℝ, vdcA d N ≤ a → a ≤ b → b ≤ 2*(N:ℝ)+1 →
      IntervalIntegrable (fun u : ℝ => (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)) volume a b := by
    intro a b ha hab hb
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hcont.mono (by
      intro u hu
      exact ⟨le_trans ha hu.1, le_trans hu.2 hb⟩)
  have h1 : ∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)
      = ∫ u in (vdcA d N)..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x) :=
    integral_eq_intervalIntegral_of_support (vdcA_le (le_of_lt hd) N) hsupp
  have hsplit : ∫ u in (vdcA d N)..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)
      = (∫ u in (vdcA d N)..(N:ℝ), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x))
        + (∫ u in (N:ℝ)..(2*(N:ℝ)), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x))
        + (∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)) := by
    have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hA2N : vdcA d N ≤ 2*(N:ℝ) := le_trans (vdcA_le' hd hN) (by linarith)
    have hN2N : (N:ℝ) ≤ 2*(N:ℝ) := by linarith
    have h2N1 : 2*(N:ℝ) ≤ 2*(N:ℝ)+1 := by linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hint (vdcA d N) (2*(N:ℝ)) le_rfl hA2N (by linarith))
          (hint (2*(N:ℝ)) (2*(N:ℝ)+1) hA2N h2N1 le_rfl),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hint (vdcA d N) (N:ℝ) le_rfl (vdcA_le' hd hN) (by linarith))
          (hint (N:ℝ) (2*(N:ℝ)) (vdcA_le' hd hN) hN2N (by linarith))]
  have hJval : ∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)
      = (∫ u in (vdcA d N)..(N:ℝ), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x))
        - vdcF t
        - (∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcTail t (u/x)) := by
    rw [h1, hsplit, vdc_mid_integral hd hN t hx, vdc_right_integral hd hd1 hN t hx]
    ring
  have habs : ∀ P Q F : ℂ, -(P - F - Q) - F = -P + Q := by intro P Q F; ring
  rw [hJ, hJval]
  exact habs _ _ _


/-- **Per-`k` deviation bound**: if the primitive `Φ` is bounded by `P` on `[A,N]` and the tail
primitive `Ψ` is bounded by `Q` on `[2N,2N+1]` (as functions of `u`, at `u/x`), then
`|J(x) - F| ≤ P + Q`. -/
lemma vdc_deviation_le {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) {x : ℝ}
    (hx : 0 < x) {P Q : ℝ}
    (hP : ∀ u ∈ Set.Icc (vdcA d N) (N:ℝ), ‖vdcPrim t (u/x)‖ ≤ P)
    (hQ : ∀ u ∈ Set.Icc (2*(N:ℝ)) (2*(N:ℝ)+1), ‖vdcTail t (u/x)‖ ≤ Q) :
    ‖(∫ y : ℝ, (vw d N (x*y) : ℂ) * vdcPhase t y) - vdcF t‖ ≤ P + Q := by
  have hAN : vdcA d N ≤ (N:ℝ) := vdcA_le' hd hN
  have h2N : (2:ℝ)*(N:ℝ) ≤ 2*(N:ℝ)+1 := by linarith
  have hPint : IntervalIntegrable (fun u : ℝ => ‖(((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)‖)
      volume (vdcA d N) (N:ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.norm ?_
    rw [Set.uIcc_of_le hAN]
    refine ContinuousOn.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp_continuousOn
        (((vw_contDiff d N).continuous_deriv (by norm_num)).continuousOn)
    · refine (continuousOn_vdcPrim t).comp (continuous_id.div_const x).continuousOn ?_
      intro u hu
      rw [Set.mem_Ioi]
      exact div_pos (lt_of_lt_of_le (vdcA_pos hd hd1 hN) hu.1) hx
  have hQint : IntervalIntegrable (fun u : ℝ => ‖(((deriv (vw d N)) u : ℝ) : ℂ) * vdcTail t (u/x)‖)
      volume (2*(N:ℝ)) (2*(N:ℝ)+1) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.norm ?_
    rw [Set.uIcc_of_le h2N]
    refine ContinuousOn.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp_continuousOn
        (((vw_contDiff d N).continuous_deriv (by norm_num)).continuousOn)
    · refine (continuousOn_vdcTail t).comp (continuous_id.div_const x).continuousOn ?_
      intro u hu
      rw [Set.mem_Ioi]
      have h2Npos : (0:ℝ) < 2*(N:ℝ) := by
        have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
        linarith
      exact div_pos (lt_of_lt_of_le h2Npos hu.1) hx
  have habsint1 : IntervalIntegrable (fun u : ℝ => |deriv (vw d N) u| * P) volume (vdcA d N) (N:ℝ) :=
    (((vw_contDiff d N).continuous_deriv (by norm_num)).abs.intervalIntegrable _ _).mul_const P
  have habsint2 : IntervalIntegrable (fun u : ℝ => |deriv (vw d N) u| * Q)
      volume (2*(N:ℝ)) (2*(N:ℝ)+1) :=
    (((vw_contDiff d N).continuous_deriv (by norm_num)).abs.intervalIntegrable _ _).mul_const Q
  rw [vdc_star hd hd1 hN t hx]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · rw [norm_neg]
    calc ‖∫ u in (vdcA d N)..(N:ℝ), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)‖
        ≤ ∫ u in (vdcA d N)..(N:ℝ), ‖(((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/x)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hAN
      _ ≤ ∫ u in (vdcA d N)..(N:ℝ), |deriv (vw d N) u| * P := by
          refine intervalIntegral.integral_mono_on hAN hPint habsint1 ?_
          intro u hu
          rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
          exact mul_le_mul_of_nonneg_left (hP u hu) (abs_nonneg _)
      _ = P * (∫ u in (vdcA d N)..(N:ℝ), |deriv (vw d N) u|) := by
          rw [intervalIntegral.integral_mul_const]; ring
      _ = P := by rw [integral_abs_deriv_vw_left hd hN, mul_one]
  · calc ‖∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), (((deriv (vw d N)) u : ℝ) : ℂ) * vdcTail t (u/x)‖
        ≤ ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), ‖(((deriv (vw d N)) u : ℝ) : ℂ) * vdcTail t (u/x)‖ :=
          intervalIntegral.norm_integral_le_integral_norm h2N
      _ ≤ ∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), |deriv (vw d N) u| * Q := by
          refine intervalIntegral.integral_mono_on h2N hQint habsint2 ?_
          intro u hu
          rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
          exact mul_le_mul_of_nonneg_left (hQ u hu) (abs_nonneg _)
      _ = Q * (∫ u in (2*(N:ℝ))..(2*(N:ℝ)+1), |deriv (vw d N) u|) := by
          rw [intervalIntegral.integral_mul_const]; ring
      _ = Q := by rw [integral_abs_deriv_vw_right hd hd1 hN, mul_one]



/-- In the dual range `N ≤ x ≤ 2N` the deviation of `J(x)` from `F` is `O(1/√t)`. -/
lemma vdc_deviation_dual {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) {x : ℝ}
    (hx : 0 < x) (hxN : (N:ℝ) ≤ x) (hx2N : x ≤ 2*(N:ℝ)) (ht : 2 ≤ t) (C1 : ℝ)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t) :
    ‖(∫ y : ℝ, (vw d N (x*y) : ℂ) * vdcPhase t y) - vdcF t‖
      ≤ (C1 + 145)/Real.sqrt t + 145/Real.sqrt t := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  refine vdc_deviation_le hd hd1 hN t hx ?_ ?_
  · intro u hu
    have hy1 : (1/4:ℝ) ≤ u/x := by
      rw [le_div_iff₀ hx]
      have hA : (N:ℝ)/2 ≤ vdcA d N := by
        rw [vdcA]
        have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
        linarith
      have hx4 : x/4 ≤ (N:ℝ)/2 := by linarith
      linarith [hu.1]
    have hy2 : u/x ≤ 6 := by
      rw [div_le_iff₀ hx]
      nlinarith [hu.2, hxN]
    exact norm_vdcPrim_le_window C1 hC1 ht hy1 hy2
  · intro u hu
    have hy1 : (1:ℝ) ≤ u/x := by
      rw [le_div_iff₀ hx]
      linarith [hu.1, hx2N, hxN]
    have hy2 : u/x ≤ 6 := by
      rw [div_le_iff₀ hx]
      nlinarith [hu.2, hxN]
    exact norm_vdcTail_le_window ht hy1 hy2



/-- `‖x^{1+it}‖ = x` for real `x > 0`. -/
lemma norm_cpow_one_add_I_mul {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖((x:ℝ):ℂ) ^ ((1:ℂ) + Complex.I * (t:ℂ))‖ = x := by
  rw [ofReal_cpow_exp hx]
  rw [Complex.norm_exp]
  have hre : (((Real.log x : ℝ) : ℂ) * ((1:ℂ) + Complex.I * (t:ℂ))).re = Real.log x := by
    simp
  rw [hre, Real.exp_log hx]

/-- The deviation bound with both a Fresnel and a harmonic alternative for each piece. -/
lemma vdc_deviation_le_min {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) {x : ℝ}
    (hx : 0 < x) {P₁ P₂ Q₁ Q₂ : ℝ}
    (hP₁ : ∀ u ∈ Set.Icc (vdcA d N) (N:ℝ), ‖vdcPrim t (u/x)‖ ≤ P₁)
    (hP₂ : ∀ u ∈ Set.Icc (vdcA d N) (N:ℝ), ‖vdcPrim t (u/x)‖ ≤ P₂)
    (hQ₁ : ∀ u ∈ Set.Icc (2*(N:ℝ)) (2*(N:ℝ)+1), ‖vdcTail t (u/x)‖ ≤ Q₁)
    (hQ₂ : ∀ u ∈ Set.Icc (2*(N:ℝ)) (2*(N:ℝ)+1), ‖vdcTail t (u/x)‖ ≤ Q₂) :
    ‖(∫ y : ℝ, (vw d N (x*y) : ℂ) * vdcPhase t y) - vdcF t‖ ≤ min P₁ P₂ + min Q₁ Q₂ := by
  have h₁ := vdc_deviation_le hd hd1 hN t hx hP₁ hQ₁
  have h₂ := vdc_deviation_le hd hd1 hN t hx hP₁ hQ₂
  have h₃ := vdc_deviation_le hd hd1 hN t hx hP₂ hQ₁
  have h₄ := vdc_deviation_le hd hd1 hN t hx hP₂ hQ₂
  rcases min_choice P₁ P₂ with hP | hP <;> rcases min_choice Q₁ Q₂ with hQ | hQ
  · rw [hP, hQ]; exact h₁
  · rw [hP, hQ]; exact h₂
  · rw [hP, hQ]; exact h₃
  · rw [hP, hQ]; exact h₄

/-- **Refined dual-range deviation bound**: for `N ≤ x ≤ 2N` (with `x` strictly between `N`
and `2N`) the deviation of `J(x)` from `F` is bounded by the sum of the two minima. -/
lemma vdc_deviation_dual_refined {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ)
    {x : ℝ} (hx : 0 < x) (hxN : (N:ℝ) < x) (hx2N : x < 2*(N:ℝ)) (ht : 2 ≤ t) (C1 : ℝ)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t) :
    ‖(∫ y : ℝ, (vw d N (x*y) : ℂ) * vdcPhase t y) - vdcF t‖
      ≤ min ((C1 + 145)/Real.sqrt t) (48*x/(t*(x - N)))
        + min (145/Real.sqrt t) (144*x/(t*(2*(N:ℝ) - x))) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have ht0 : (0:ℝ) < t := by linarith
  have hAn : (1:ℝ)/4 ≤ vdcA d N / x := by
    rw [le_div_iff₀ hx]
    have hA : (N:ℝ)/2 ≤ vdcA d N := by
      rw [vdcA]; linarith
    linarith [hx2N]
  refine vdc_deviation_le_min hd hd1 hN t hx ?_ ?_ ?_ ?_
  · -- Fresnel bound for Φ
    intro u hu
    have hy1 : (1/4:ℝ) ≤ u/x := le_trans hAn (div_le_div_of_nonneg_right hu.1 hx.le)
    have hy2 : u/x ≤ 6 := by
      rw [div_le_iff₀ hx]; nlinarith [hu.2, hxN, hx]
    exact norm_vdcPrim_le_window C1 hC1 ht hy1 hy2
  · -- harmonic bound for Φ
    intro u hu
    have hxu : u ≤ (N:ℝ) := hu.2
    have hxupos : 0 < x - u := by linarith
    have hxNpos : 0 < x - (N:ℝ) := by linarith
    have hy1 : (1/8:ℝ) ≤ u/x := by
      rw [le_div_iff₀ hx]
      have hA : x/8 ≤ vdcA d N := by
        have hA' : (N:ℝ)/2 ≤ vdcA d N := by
          rw [vdcA]; linarith
        linarith [hx2N]
      linarith [hu.1]
    have hy2 : u/x < 1 := by
      rw [div_lt_iff₀ hx]; linarith [hu.2, hxN]
    have hb := norm_vdcPrim_le_harm (by linarith : (1:ℝ) ≤ t) hy1 hy2
    have heq : (1:ℝ) - u/x = (x - u)/x := by field_simp
    calc ‖vdcPrim t (u/x)‖ ≤ 48 / (t * (1 - u/x)) := hb
      _ = 48*x/(t*(x - u)) := by
          rw [heq]; field_simp
      _ ≤ 48*x/(t*(x - (N:ℝ))) := by
          have h1 : t*(x - (N:ℝ)) ≤ t*(x - u) := mul_le_mul_of_nonneg_left (by linarith) ht0.le
          have h2 : 0 < t*(x - (N:ℝ)) := by positivity
          have h3 : 1/(t*(x - u)) ≤ 1/(t*(x - (N:ℝ))) := one_div_le_one_div_of_le h2 h1
          calc 48*x/(t*(x - u)) = 48*x * (1/(t*(x - u))) := by ring
            _ ≤ 48*x * (1/(t*(x - (N:ℝ)))) := mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = 48*x/(t*(x - (N:ℝ))) := by ring
  · -- Fresnel bound for Ψ
    intro u hu
    have hy1 : (1:ℝ) ≤ u/x := by
      rw [le_div_iff₀ hx]; linarith [hu.1, hx2N]
    have hy2 : u/x ≤ 6 := by
      rw [div_le_iff₀ hx]; linarith [hu.2, hxN, hN1]
    exact norm_vdcTail_le_window ht hy1 hy2
  · -- harmonic bound for Ψ
    intro u hu
    have hu2N : 2*(N:ℝ) ≤ u := hu.1
    have hu1pos : 0 < u - x := by linarith [hu2N, hx2N]
    have h2Nxpos : 0 < 2*(N:ℝ) - x := by linarith [hx2N]
    have hy1 : 1 < u/x := by
      rw [lt_div_iff₀ hx]; linarith [hu2N, hx2N]
    have hy2 : u/x ≤ 6 := by
      rw [div_le_iff₀ hx]; linarith [hu.2, hxN, hN1]
    have hb := norm_vdcTail_le_harm (by linarith : (1:ℝ) ≤ t) hy1 hy2
    have heq : u/x - 1 = (u - x)/x := by field_simp
    calc ‖vdcTail t (u/x)‖ ≤ 144 / (t * (u/x - 1)) := hb
      _ = 144*x/(t*(u - x)) := by
          rw [heq]; field_simp
      _ ≤ 144*x/(t*(2*(N:ℝ) - x)) := by
          have h1 : t*(2*(N:ℝ) - x) ≤ t*(u - x) := mul_le_mul_of_nonneg_left (by linarith) ht0.le
          have h2 : 0 < t*(2*(N:ℝ) - x) := by positivity
          have h3 : 1/(t*(u - x)) ≤ 1/(t*(2*(N:ℝ) - x)) := one_div_le_one_div_of_le h2 h1
          calc 144*x/(t*(u - x)) = 144*x * (1/(t*(u - x))) := by ring
            _ ≤ 144*x * (1/(t*(2*(N:ℝ) - x))) := mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = 144*x/(t*(2*(N:ℝ) - x)) := by ring


/-- Harmonic bound: `Σ_{k=a}^{b} 1/k ≤ 1/a + log(1 + b/a)`. -/
lemma sum_Icc_inv_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, 1/(k:ℝ) ≤ 1/(a:ℝ) + Real.log (1 + (b:ℝ)/(a:ℝ)) := by
  let emb : ℕ ↪ ℤ := ⟨fun k => (k:ℤ), fun x y hxy => Int.ofNat.inj hxy⟩
  have hemb : ∀ k : ℕ, ((emb k : ℤ) : ℝ) = (k:ℝ) := by
    intro k
    change (((k:ℤ) : ℝ)) = ((k:ℕ) : ℝ)
    exact Int.cast_natCast k
  have hT : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hU : (0:ℝ) ≤ (b:ℝ) := Nat.cast_nonneg b
  have key := Commons.Analysis.Harmonic.sum_inv_sub_le (s := (Finset.Icc a b).map emb)
    (x := 0) (T := (a:ℝ)) (U := (b:ℝ)) hT hU ?_ ?_
  · rw [Finset.sum_map] at key
    simp only [hemb, sub_zero] at key
    exact key
  · intro k hk
    rw [Finset.mem_map] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    rw [Finset.mem_Icc] at hm
    rw [hemb, sub_zero]
    exact_mod_cast hm.1
  · intro k hk
    rw [Finset.mem_map] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    rw [Finset.mem_Icc] at hm
    rw [hemb, sub_zero]
    exact_mod_cast hm.2

/-- Harmonic bound: `Σ_{k=A}^{M} 1/(K−k) ≤ 1/δ + log(1 + (K−A)/δ)` when `K − k ≥ δ` on the range. -/
lemma sum_Icc_inv_K_sub_le {K δ : ℝ} (hδ : 0 < δ) {A M : ℕ} (hAM : A ≤ M)
    (hδK : δ ≤ K - (M:ℝ)) :
    ∑ k ∈ Finset.Icc A M, 1/(K - (k:ℝ)) ≤ 1/δ + Real.log (1 + (K - (A:ℝ))/δ) := by
  let emb : ℕ ↪ ℤ := ⟨fun k => (-(k:ℤ)), fun x y hxy => by
    have h : ((-(x:ℤ) : ℤ) : ℝ) = ((-(y:ℤ) : ℤ) : ℝ) := by exact_mod_cast hxy
    simp at h
    omega⟩
  have hemb : ∀ k : ℕ, ((emb k : ℤ) : ℝ) = -(k:ℝ) := by
    intro k
    change (((-(k:ℤ)) : ℤ) : ℝ) = -((k:ℕ) : ℝ)
    push_cast
    ring
  have hUA : (0:ℝ) ≤ K - (A:ℝ) := by
    have hMA : (A:ℝ) ≤ (M:ℝ) := by exact_mod_cast hAM
    linarith
  have key := Commons.Analysis.Harmonic.sum_inv_sub_le (s := (Finset.Icc A M).map emb)
    (x := -K) (T := δ) (U := K - (A:ℝ)) hδ hUA ?_ ?_
  · rw [Finset.sum_map] at key
    have hcongr : ∀ k : ℕ, (1:ℝ)/(((emb k : ℤ) : ℝ) - (-K)) = 1/(K - (k:ℝ)) := by
      intro k
      rw [hemb]; ring
    simp only [hcongr] at key
    exact key
  · intro k hk
    rw [Finset.mem_map] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    rw [Finset.mem_Icc] at hm
    rw [hemb]
    have : (m:ℝ) ≤ (M:ℝ) := by exact_mod_cast hm.2
    linarith
  · intro k hk
    rw [Finset.mem_map] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    rw [Finset.mem_Icc] at hm
    rw [hemb]
    have : (A:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
    linarith

/-- `x_k = t/(2πk)` lies in `[N,2N]` for `k` in the dual range. -/
lemma vdcX_mem_dual {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) {k : ℕ}
    (hk : k ∈ Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ)))) (Nat.floor (t/(2*Real.pi*(N:ℝ))))) :
    (N:ℝ) ≤ vdcX t k ∧ vdcX t k ≤ 2*(N:ℝ) := by
  rw [Finset.mem_Icc] at hk
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have h1 : (0:ℝ) < (Nat.ceil (t/(4*Real.pi*(N:ℝ))) : ℝ) := by
      rw [Nat.cast_pos, Nat.ceil_pos]; positivity
    have h2 : (Nat.ceil (t/(4*Real.pi*(N:ℝ))) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
    linarith
  have hden : (0:ℝ) < 2*Real.pi*(k:ℝ) := by positivity
  have hle : ((k:ℝ)) ≤ t/(2*Real.pi*(N:ℝ)) := by
    have h1 : (k:ℝ) ≤ (Nat.floor (t/(2*Real.pi*(N:ℝ))) : ℝ) := by exact_mod_cast hk.2
    have h2 : ((Nat.floor (t/(2*Real.pi*(N:ℝ))) : ℕ) : ℝ) ≤ t/(2*Real.pi*(N:ℝ)) :=
      Nat.floor_le (by positivity)
    linarith
  have hceil : t/(4*Real.pi*(N:ℝ)) ≤ (k:ℝ) := by
    have h1 : (Nat.ceil (t/(4*Real.pi*(N:ℝ))) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
    have h2 : t/(4*Real.pi*(N:ℝ)) ≤ (Nat.ceil (t/(4*Real.pi*(N:ℝ))) : ℝ) := Nat.le_ceil _
    linarith
  constructor
  · rw [vdcX, le_div_iff₀ hden]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(N:ℝ))] at hle
    nlinarith [hle, hπ, hkpos, hN1]
  · rw [vdcX, div_le_iff₀ hden]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4*Real.pi*(N:ℝ))] at hceil
    nlinarith [hceil, hπ, hkpos, hN1]

/-- Telescoping sum over `Icc a b`. -/
lemma sum_Icc_telescope (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, (f k - f (k-1)) = f b - f (a-1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Icc_succ_top (by omega : a ≤ b + 1)]
      rw [ih]
      have hb1 : b + 1 - 1 = b := by omega
      rw [hb1]
      ring

/-- Tight harmonic bound: `Σ_{k=a}^{b} 1/k ≤ log(b/(a−1))` for `2 ≤ a ≤ b`. -/
lemma sum_Icc_inv_le_log {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, 1/(k:ℝ) ≤ Real.log ((b:ℝ)/((a:ℝ) - 1)) := by
  have ha1 : 1 ≤ a := by omega
  have hstep : ∀ k ∈ Finset.Icc a b, 1/(k:ℝ) ≤ Real.log ((k:ℝ)/((k:ℝ) - 1)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk2 : (2:ℝ) ≤ (k:ℝ) := by
      have : 2 ≤ k := le_trans ha hk.1
      exact_mod_cast this
    have hkpos : (0:ℝ) < (k:ℝ) := by linarith
    have hx : (0:ℝ) < (k:ℝ)/((k:ℝ) - 1) := by
      apply div_pos hkpos; linarith
    have h := Real.one_sub_inv_le_log_of_pos hx
    rw [inv_div] at h
    have heq : (1:ℝ) - ((k:ℝ) - 1)/(k:ℝ) = 1/(k:ℝ) := by
      field_simp
      ring
    linarith [h, heq]
  have hker : ∀ k ∈ Finset.Icc a b,
      Real.log ((k:ℝ)/((k:ℝ) - 1)) = Real.log (k:ℝ) - Real.log ((k-1:ℕ):ℝ) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := le_trans ha1 hk.1
    have hk2 : (2:ℝ) ≤ (k:ℝ) := by
      have : 2 ≤ k := le_trans ha hk.1
      exact_mod_cast this
    have hcast : ((k-1:ℕ):ℝ) = (k:ℝ) - 1 := by
      rw [Nat.cast_sub hk1]; norm_num
    rw [hcast, Real.log_div (ne_of_gt (by linarith : (0:ℝ) < (k:ℝ)))
      (ne_of_gt (by linarith : (0:ℝ) < (k:ℝ) - 1))]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hconv : ∑ k ∈ Finset.Icc a b, Real.log ((k:ℝ)/((k:ℝ) - 1))
      = ∑ k ∈ Finset.Icc a b, (Real.log (k:ℝ) - Real.log ((k-1:ℕ):ℝ)) :=
    Finset.sum_congr rfl (fun k hk => hker k hk)
  rw [hconv, sum_Icc_telescope (fun k : ℕ => Real.log (k:ℝ)) hab]
  have ha' : ((a-1:ℕ):ℝ) = (a:ℝ) - 1 := by
    rw [Nat.cast_sub ha1]; norm_num
  rw [ha']
  have hbpos : (0:ℝ) < (b:ℝ) := by
    have : 0 < b := by omega
    exact_mod_cast this
  have hapos : (0:ℝ) < (a:ℝ) - 1 := by
    have : (1:ℝ) < (a:ℝ) := by exact_mod_cast ha
    linarith
  rw [← Real.log_div (ne_of_gt hbpos) (ne_of_gt hapos)]



/-- The "endpoint" part of the dual range (`x_k = N` or `x_k = 2N`) has at most two elements. -/
lemma dual_range_bad_card {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    (((Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ)))) (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
      (fun k => ¬ ((N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ)))).card) ≤ 2 := by
  classical
  set A : ℕ := Nat.ceil (t/(4*Real.pi*(N:ℝ))) with hA
  set K : ℕ := Nat.floor (t/(2*Real.pi*(N:ℝ))) with hK
  have hsub : (Finset.Icc A K).filter (fun k => ¬ ((N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ)))
      ⊆ ({A, K} : Finset ℕ) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, hk3⟩ := hk
    have hdual := vdcX_mem_dual hN ht (k := k) (by rw [Finset.mem_Icc]; exact ⟨hk1, hk2⟩)
    have hk1' : 1 ≤ k := by
      have : 0 < Nat.ceil (t/(4*Real.pi*(N:ℝ))) := by
        rw [Nat.ceil_pos]; positivity
      omega
    rw [not_and_or, not_lt, not_lt] at hk3
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hk3 with h3 | h3
    · -- `x_k ≤ N`
      right
      have hxk : vdcX t k = (N:ℝ) := le_antisymm h3 hdual.1
      have h1 : 2*Real.pi*(k:ℝ)*vdcX t k = t := vdcX_mul N t hk1'
      rw [hxk] at h1
      have hkN : (k:ℝ) = t/(2*Real.pi*(N:ℝ)) := by
        rw [← h1]; field_simp
      rw [hK, ← hkN, Nat.floor_natCast]
    · -- `2N ≤ x_k`
      left
      have hxk : vdcX t k = 2*(N:ℝ) := le_antisymm hdual.2 h3
      have h1 : 2*Real.pi*(k:ℝ)*vdcX t k = t := vdcX_mul N t hk1'
      rw [hxk] at h1
      have hkA : (k:ℝ) = t/(4*Real.pi*(N:ℝ)) := by
        rw [← h1]; field_simp; ring
      rw [hA, ← hkA, Nat.ceil_natCast]
  calc ((Finset.Icc A K).filter (fun k => ¬ ((N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ)))).card
      ≤ ({A, K} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 2 := by
      have h1 := Finset.card_insert_le A ({K} : Finset ℕ)
      simp only [Finset.card_singleton] at h1
      simpa using h1

/-- The endpoint part of the dual range contributes `O(N/√t)`. -/
lemma dual_range_bad_sum_le {N : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) {t : ℝ}
    (ht : 2 ≤ t) (C1 : ℝ)
    (hC1nn : 0 ≤ C1)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t) :
    ∑ k ∈ ((Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ)))) (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
        (fun k => ¬ ((N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ)))),
        (vdcX t k) * ‖(∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y) - vdcF t‖
      ≤ 2 * (2*(N:ℝ) * ((C1 + 290)/Real.sqrt t)) := by
  classical
  have ht0 : (0:ℝ) < t := by linarith
  have hcard := dual_range_bad_card (N := N) hN ht0
  have hterm : ∀ k ∈ ((Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
        (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
        (fun k => ¬ ((N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ)))),
        (vdcX t k) * ‖(∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y) - vdcF t‖
      ≤ 2*(N:ℝ) * ((C1 + 290)/Real.sqrt t) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, _⟩ := hk
    have hdual := vdcX_mem_dual hN ht0 (k := k) (by rw [Finset.mem_Icc]; exact ⟨hk1, hk2⟩)
    have hk1' : 1 ≤ k := by
      have : 0 < Nat.ceil (t/(4*Real.pi*(N:ℝ))) := by
        rw [Nat.ceil_pos]; positivity
      omega
    have hx0 : 0 < vdcX t k := vdcX_pos ht0 hk1'
    have hdev := vdc_deviation_dual hd hd1 hN t hx0 hdual.1 hdual.2 ht C1 hC1
    have hconst : (C1+145)/Real.sqrt t + 145/Real.sqrt t = (C1 + 290)/Real.sqrt t := by
      rw [← add_div]; ring_nf
    rw [hconst] at hdev
    have h2N0 : (0:ℝ) ≤ 2*(N:ℝ) := by positivity
    exact mul_le_mul hdual.2 hdev (norm_nonneg _) h2N0
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((((Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
        (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
        (fun k => ¬ ((N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ)))).card : ℕ) : ℝ) ≤ 2 := by
    exact_mod_cast hcard
  have hpos : (0:ℝ) ≤ 2*(N:ℝ) * ((C1 + 290)/Real.sqrt t) := by positivity
  nlinarith [hc, hpos]



/-- **Harmonic-mean bound for a minimum**: `min a b ≤ 2ab/(a+b)` for `a, b ≥ 0`. -/
lemma min_le_two_mul_mul_div_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ≤ 2*(a*b)/(a+b) := by
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ a + b) with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    rw [ha0, hb0, min_self, mul_zero, mul_zero, zero_div]
  · rcases le_total a b with hab | hab
    · rw [min_eq_left hab, le_div_iff₀ h]
      nlinarith
    · rw [min_eq_right hab, le_div_iff₀ h]
      nlinarith

/-- General form of the harmonic bound `Σ_{k∈S} 1/(K−k)`, for an arbitrary set of naturals. -/
lemma sum_inv_K_sub_le {K δ : ℝ} (hδ : 0 < δ) {A : ℕ} {S : Finset ℕ} (hAK : (A:ℝ) ≤ K)
    (hlo : ∀ k ∈ S, δ ≤ K - (k:ℝ)) (hhi : ∀ k ∈ S, (A:ℝ) ≤ (k:ℝ)) :
    ∑ k ∈ S, 1/(K - (k:ℝ)) ≤ 1/δ + Real.log (1 + (K - (A:ℝ))/δ) := by
  let emb : ℕ ↪ ℤ := ⟨fun k => (-(k:ℤ)), fun x y hxy => by
    have h : ((-(x:ℤ) : ℤ) : ℝ) = ((-(y:ℤ) : ℤ) : ℝ) := by exact_mod_cast hxy
    simp at h
    omega⟩
  have hemb : ∀ k : ℕ, ((emb k : ℤ) : ℝ) = -(k:ℝ) := by
    intro k
    change (((-(k:ℤ)) : ℤ) : ℝ) = -((k:ℕ) : ℝ)
    push_cast
    ring
  have hUA : (0:ℝ) ≤ K - (A:ℝ) := by linarith
  have key := Commons.Analysis.Harmonic.sum_inv_sub_le (s := S.map emb)
    (x := -K) (T := δ) (U := K - (A:ℝ)) hδ hUA ?_ ?_
  · rw [Finset.sum_map] at key
    have hcongr : ∀ k : ℕ, (1:ℝ)/(((emb k : ℤ) : ℝ) - (-K)) = 1/(K - (k:ℝ)) := by
      intro k
      rw [hemb]; ring
    simp only [hcongr] at key
    exact key
  · intro k hk
    rw [Finset.mem_map] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    rw [hemb]
    linarith [hlo m hm]
  · intro k hk
    rw [Finset.mem_map] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    rw [hemb]
    linarith [hhi m hm]



/-! ## 7. The target: the reverse van der Corput transform -/

/-- The van der Corput model coefficient `κ = (t/2π)^{1+it}·F(t)`, `|κ| = √(t/2π)`. -/
noncomputable def kappa (t : ℝ) : ℂ :=
  ((t/(2*Real.pi) : ℝ) : ℂ) ^ ((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t

theorem vdcD_norm_le (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : (N:ℝ) ≤ t) :
    ‖vdcD N t‖ ≤ 1 + 8 * Real.pi := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have htpos : (0:ℝ) < t := lt_of_lt_of_le hNpos ht
  set a : ℕ := Nat.ceil (t/(4*Real.pi*N)) with ha
  set b : ℕ := Nat.floor (t/(2*Real.pi*N)) with hb
  have ha_ge : t / (4 * Real.pi * (N : ℝ)) ≤ (a : ℝ) := Nat.le_ceil _
  have h4πN : 0 < 4 * Real.pi * (N : ℝ) := by positivity
  have ha1 : 1 ≤ a := by
    rw [ha, Nat.one_le_iff_ne_zero, ne_eq, Nat.ceil_eq_zero]
    push Not
    positivity
  have hapos : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha1
  have hD : ‖vdcD N t‖ ≤ ∑ k ∈ Finset.Icc a b, (1:ℝ)/k := by
    rw [vdcD]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun k hk => ?_))
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := le_trans ha1 hk.1
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
    have hkne : (k:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hkpos)
    have heq : ‖(k:ℂ)^(-(Complex.I*(t:ℂ)))/(k:ℂ)‖ = (1:ℝ)/k := by
      rw [norm_div, Complex.norm_natCast, Complex.norm_cpow_of_ne_zero hkne]
      have hre : (-(Complex.I*(t:ℂ))).re = 0 := by simp
      have harg : (k:ℂ).arg = 0 := by
        rw [← Complex.ofReal_natCast]
        exact Complex.arg_ofReal_of_nonneg (by positivity)
      rw [hre, Real.rpow_zero, harg, zero_mul, Real.exp_zero]
      simp
    rw [heq]
  have hterm : ∀ k ∈ Finset.Icc a b, (1:ℝ)/k ≤ (1/(a:ℝ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact one_div_le_one_div_of_le hapos (by exact_mod_cast hk.1)
  have hcard : ((Finset.Icc a b).card : ℝ) ≤ t/(4*Real.pi*(N:ℝ)) + 1 := by
    rw [Nat.card_Icc]
    by_cases hab : a ≤ b + 1
    · rw [Nat.cast_sub hab]; push_cast
      have hb' : (b:ℝ) ≤ t/(2*Real.pi*(N:ℝ)) := Nat.floor_le (by positivity)
      have hrel : t / (2*Real.pi*(N:ℝ)) = 2 * (t / (4 * Real.pi * (N : ℝ))) := by
        field_simp; ring
      linarith
    · push Not at hab
      have hzero : b + 1 - a = 0 := Nat.sub_eq_zero_of_le (le_of_lt hab)
      rw [hzero]
      simp only [Nat.cast_zero]
      have : (0 : ℝ) ≤ t / (4 * Real.pi * (N : ℝ)) := by positivity
      linarith
  have hsum : ∑ k ∈ Finset.Icc a b, (1:ℝ)/k ≤ 1 + 8*Real.pi := by
    have h1 : ∑ k ∈ Finset.Icc a b, (1:ℝ)/k ≤ (1/(a:ℝ)) * ((Finset.Icc a b).card : ℝ) := by
      calc ∑ k ∈ Finset.Icc a b, (1:ℝ)/k ≤ ∑ _k ∈ Finset.Icc a b, (1/(a:ℝ)) :=
            Finset.sum_le_sum hterm
        _ = ((Finset.Icc a b).card : ℝ) * (1/(a:ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = (1/(a:ℝ)) * ((Finset.Icc a b).card : ℝ) := by ring
    have h2 : (1/(a:ℝ)) ≤ 4*Real.pi*(N:ℝ)/t := by
      have h3 : (1/(a:ℝ)) ≤ 1/(t/(4*Real.pi*(N:ℝ))) :=
        one_div_le_one_div_of_le (by positivity) ha_ge
      have h4 : 1/(t/(4*Real.pi*(N:ℝ))) = 4*Real.pi*(N:ℝ)/t := by field_simp
      linarith [h3, le_of_eq h4]
    have h5 : 0 ≤ ((Finset.Icc a b).card : ℝ) := by positivity
    calc ∑ k ∈ Finset.Icc a b, (1:ℝ)/k ≤ (1/(a:ℝ)) * ((Finset.Icc a b).card : ℝ) := h1
      _ ≤ (4*Real.pi*(N:ℝ)/t) * (t/(4*Real.pi*(N:ℝ)) + 1) :=
          mul_le_mul h2 hcard h5 (by positivity)
      _ = 1 + 4*Real.pi*(N:ℝ)/t := by field_simp
      _ ≤ 1 + 4*Real.pi := by
          have h6 : 4*Real.pi*(N:ℝ)/t ≤ 4*Real.pi := by
            rw [div_le_iff₀ htpos]; nlinarith [ht, Real.pi_pos, hNpos]
          linarith
      _ ≤ 1 + 8*Real.pi := by linarith [Real.pi_pos]
  linarith [hD, hsum]



/-- **Far-right tail**: if the stationary point `x_k = t/(2πk)` lies strictly beyond the support
`[N−d, 2N+d]` of `vw d N`, the first-order test on the smooth surrogate phase `vdcTheta` gives
`‖I_k‖ ≤ 8/λ`, `λ = t/(2N+d) − 2πk`. -/
theorem vdcI_far_right {d : ℝ} {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hd2 : (1:ℝ)/2 < (N:ℝ) - d) (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k)
    (hxk : 2*(N:ℝ) + d < vdcX t k) :
    ‖vdcI d N t (k:ℤ)‖ ≤ 8 / (t/(2*(N:ℝ)+d) - 2*Real.pi*(k:ℝ)) := by
  set a : ℝ := (N:ℝ) - d with hadef
  set b : ℝ := 2*(N:ℝ) + d with hbdef
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have ha12 : (1:ℝ)/2 < a := by rw [hadef]; exact hd2
  have hb0 : (0:ℝ) < b := by rw [hbdef]; positivity
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have h2pik : (0:ℝ) < 2*Real.pi*(k:ℝ) := by positivity
  have hxk' : (2*(N:ℝ)+d) * (2*Real.pi*(k:ℝ)) < t := by
    rw [vdcX] at hxk
    rw [lt_div_iff₀ h2pik] at hxk
    linarith [hxk]
  have hlampos : 0 < t/b - 2*Real.pi*(k:ℝ) := by
    rw [hbdef, sub_pos, lt_div_iff₀ (by positivity : (0:ℝ) < 2*(N:ℝ)+d)]
    linarith [hxk']
  have hlam2 : 2*Real.pi*((k:ℤ):ℝ) ≤ t/b := by
    rw [hbdef, le_div_iff₀ (by positivity : (0:ℝ) < 2*(N:ℝ)+d)]
    push_cast
    linarith [hxk']
  -- restrict to the support and replace the phase by the smooth surrogate
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc a b →
      (vw d N x : ℂ) * Complex.exp (Complex.I *
        (((t*Real.log x - 2*Real.pi*(((k:ℤ):ℝ))*x : ℝ)) : ℂ)) = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have hv : vw d N x = 0 := by
      rcases hx with h | h
      · refine vw_eq_zero_of_le hd ?_
        have : x < a := h
        rw [hadef] at this; linarith
      · refine vw_eq_zero_of_ge hd ?_
        have : b < x := h
        rw [hbdef] at this; linarith
    rw [hv]; simp
  have hI : vdcI d N t (k:ℤ) = ∫ x in a..b,
      ((vw d N x : ℝ) : ℂ) * Complex.exp (Complex.I * ((vdcTheta t ((k:ℤ):ℝ) x : ℝ) : ℂ)) := by
    rw [vdcI]
    rw [integral_eq_intervalIntegral_of_support hab hsupp]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : (1:ℝ)/2 ≤ x := le_of_lt (lt_of_lt_of_le ha12 hx.1)
    rw [vdcTheta_eq hx1]
  rw [hI]
  -- the first-order test
  have hbound : ∀ x ∈ Set.Icc a b, (t/b - 2*Real.pi*((k:ℤ):ℝ)) ≤
      |deriv (vdcTheta t ((k:ℤ):ℝ)) x| := by
    intro x hx
    have hx1 : (1:ℝ)/2 < x := lt_of_lt_of_le ha12 hx.1
    have hx0 : 0 < x := by linarith
    have h1 : t/b ≤ t/x := by
      rw [div_le_div_iff₀ hb0 hx0]
      nlinarith [hx.2, ht]
    have h3 : 0 ≤ t/x - 2*Real.pi*((k:ℤ):ℝ) := by
      rw [sub_nonneg]; linarith [h1, hlam2]
    rw [deriv_vdcTheta hx1, abs_of_nonneg h3]
    linarith
  have hmono : MonotoneOn (deriv (vdcTheta t ((k:ℤ):ℝ))) (Set.Icc a b) ∨
      AntitoneOn (deriv (vdcTheta t ((k:ℤ):ℝ))) (Set.Icc a b) :=
    Or.inr ((vdcTheta_antitone (le_of_lt ht) ha12).mono Set.Icc_subset_Ici_self)
  have hgc : ContinuousOn (vw d N) (Set.Icc a b) :=
    (vw_contDiff d N).continuous.continuousOn
  have hgd : ContinuousOn (deriv (vw d N)) (Set.Icc a b) :=
    ((vw_contDiff d N).continuous_deriv (by norm_num)).continuousOn
  have hg : ∀ x ∈ Set.Ioo a b, HasDerivAt (vw d N) (deriv (vw d N) x) x :=
    fun x _ => ((vw_contDiff d N).differentiable (by norm_num) x).hasDerivAt
  have hkey := Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_hasDerivAt_deriv_ge_mono
    hab hlampos (vdcTheta_contDiff t ((k:ℤ):ℝ)) hmono hbound hgc hgd hg
  -- boundary term
  have hva : |vw d N a| = 0 := by
    rw [hadef]
    rw [show vw d N ((N:ℝ) - d) = 0 from vw_vdcA_eq_zero hd N, abs_zero]
  -- variation
  have hvar : ∫ x in a..b, |deriv (vw d N) x| ≤ 2 := by
    have hcont : Continuous (fun x : ℝ => |deriv (vw d N) x|) :=
      ((vw_contDiff d N).continuous_deriv (by norm_num)).abs
    have hsplit : ∫ x in a..b, |deriv (vw d N) x|
        = (∫ x in a..(N:ℝ), |deriv (vw d N) x|)
          + (∫ x in (N:ℝ)..b, |deriv (vw d N) x|) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable a (N:ℝ)) (hcont.intervalIntegrable (N:ℝ) b)]
    rw [hsplit]
    have hleft : ∫ x in a..(N:ℝ), |deriv (vw d N) x| = 1 := by
      rw [hadef]; exact integral_abs_deriv_vw_left hd hN
    have hright : ∫ x in (N:ℝ)..b, |deriv (vw d N) x| ≤ 1 := by
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (N:ℝ) b →
          |deriv (vw d N) x| = - deriv (vw d N) x := by
        filter_upwards with x hx
        rw [Set.uIoc_of_le (by rw [hbdef]; linarith : (N:ℝ) ≤ b)] at hx
        by_cases h2 : 2*(N:ℝ) ≤ x
        · exact abs_of_nonpos (deriv_vw_nonpos_right hd hN h2)
        · push Not at h2
          have hlt : (N:ℝ) < x := hx.1
          rw [deriv_vw_eq_zero_plateau hd hN hlt h2, abs_zero, neg_zero]
      rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_neg,
        intervalIntegral.integral_deriv_eq_sub (f := vw d N) (a := (N:ℝ)) (b := b)]
      · have hb0' : vw d N b = 0 := by rw [hbdef]; exact vw_eq_zero_of_ge hd le_rfl
        have hN1 : vw d N (N:ℝ) = 1 := vw_eq_one hd le_rfl (by linarith)
        rw [hb0', hN1]; norm_num
      · intro x _
        exact ((vw_contDiff d N).differentiable (by norm_num) x).hasDerivAt.differentiableAt
      · exact ((vw_contDiff d N).continuous_deriv (by norm_num)).intervalIntegrable _ _
    linarith
  calc ‖∫ x in a..b, ((vw d N x : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((vdcTheta t ((k:ℤ):ℝ) x : ℝ) : ℂ))‖
      ≤ 4 * (|vw d N a| + ∫ x in a..b, |deriv (vw d N) x|) /
          (t/b - 2*Real.pi*((k:ℤ):ℝ)) := hkey
    _ ≤ 4 * (0 + 2) / (t/b - 2*Real.pi*((k:ℤ):ℝ)) := by
        rw [hva]
        gcongr
    _ = 8 / (t/b - 2*Real.pi*((k:ℤ):ℝ)) := by ring

/-- **Far-left tail**: if the stationary point `x_k = t/(2πk)` lies strictly before the support
`[N−d, 2N+d]` of `vw d N`, the first-order test on the smooth surrogate phase gives
`‖I_k‖ ≤ 8/λ`, `λ = 2πk − t/(N−d)`. -/
theorem vdcI_far_left {d : ℝ} {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hd2 : (1:ℝ)/2 < (N:ℝ) - d) (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k)
    (hxk : vdcX t k < (N:ℝ) - d) :
    ‖vdcI d N t (k:ℤ)‖ ≤ 8 / (2*Real.pi*((k:ℤ):ℝ) - t/((N:ℝ)-d)) := by
  set a : ℝ := (N:ℝ) - d with hadef
  set b : ℝ := 2*(N:ℝ) + d with hbdef
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have ha12 : (1:ℝ)/2 < a := by rw [hadef]; exact hd2
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by rw [hbdef]; positivity
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have h2pik : (0:ℝ) < 2*Real.pi*((k:ℤ):ℝ) := by positivity
  have hkcast : ((k:ℤ):ℝ) = (k:ℝ) := by push_cast; ring
  have hxk' : t < (2*Real.pi*((k:ℤ):ℝ)) * a := by
    rw [vdcX] at hxk
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(k:ℝ))] at hxk
    rw [hkcast]
    linarith [hxk]
  have hlampos : 0 < 2*Real.pi*((k:ℤ):ℝ) - t/a := by
    rw [sub_pos, div_lt_iff₀ ha0]
    linarith [hxk']
  -- restrict to the support and replace the phase by the smooth surrogate
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc a b →
      (vw d N x : ℂ) * Complex.exp (Complex.I *
        (((t*Real.log x - 2*Real.pi*(((k:ℤ):ℝ))*x : ℝ)) : ℂ)) = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have hv : vw d N x = 0 := by
      rcases hx with h | h
      · refine vw_eq_zero_of_le hd ?_
        have : x < a := h
        rw [hadef] at this; linarith
      · refine vw_eq_zero_of_ge hd ?_
        have : b < x := h
        rw [hbdef] at this; linarith
    rw [hv]; simp
  have hI : vdcI d N t (k:ℤ) = ∫ x in a..b,
      ((vw d N x : ℝ) : ℂ) * Complex.exp (Complex.I * ((vdcTheta t ((k:ℤ):ℝ) x : ℝ) : ℂ)) := by
    rw [vdcI]
    rw [integral_eq_intervalIntegral_of_support hab hsupp]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : (1:ℝ)/2 ≤ x := le_of_lt (lt_of_lt_of_le ha12 hx.1)
    rw [vdcTheta_eq hx1]
  rw [hI]
  -- the first-order test
  have hbound : ∀ x ∈ Set.Icc a b, (2*Real.pi*((k:ℤ):ℝ) - t/a) ≤
      |deriv (vdcTheta t ((k:ℤ):ℝ)) x| := by
    intro x hx
    have hx1 : (1:ℝ)/2 < x := lt_of_lt_of_le ha12 hx.1
    have hx0 : 0 < x := by linarith
    have h1 : t/x ≤ t/a := by
      rw [div_le_div_iff₀ hx0 ha0]
      nlinarith [hx.1, ht]
    have ht_a : t/a ≤ 2*Real.pi*((k:ℤ):ℝ) := by
      rw [div_le_iff₀ ha0]
      linarith [hxk']
    have h3 : t/x - 2*Real.pi*((k:ℤ):ℝ) ≤ 0 := by linarith [h1, ht_a]
    rw [deriv_vdcTheta hx1, abs_of_nonpos h3]
    linarith
  have hmono : MonotoneOn (deriv (vdcTheta t ((k:ℤ):ℝ))) (Set.Icc a b) ∨
      AntitoneOn (deriv (vdcTheta t ((k:ℤ):ℝ))) (Set.Icc a b) :=
    Or.inr ((vdcTheta_antitone (le_of_lt ht) ha12).mono Set.Icc_subset_Ici_self)
  have hgc : ContinuousOn (vw d N) (Set.Icc a b) :=
    (vw_contDiff d N).continuous.continuousOn
  have hgd : ContinuousOn (deriv (vw d N)) (Set.Icc a b) :=
    ((vw_contDiff d N).continuous_deriv (by norm_num)).continuousOn
  have hg : ∀ x ∈ Set.Ioo a b, HasDerivAt (vw d N) (deriv (vw d N) x) x :=
    fun x _ => ((vw_contDiff d N).differentiable (by norm_num) x).hasDerivAt
  have hkey := Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_hasDerivAt_deriv_ge_mono
    hab hlampos (vdcTheta_contDiff t ((k:ℤ):ℝ)) hmono hbound hgc hgd hg
  have hva : |vw d N a| = 0 := by
    rw [hadef]
    rw [show vw d N ((N:ℝ) - d) = 0 from vw_vdcA_eq_zero hd N, abs_zero]
  have hvar : ∫ x in a..b, |deriv (vw d N) x| ≤ 2 := by
    have hcont : Continuous (fun x : ℝ => |deriv (vw d N) x|) :=
      ((vw_contDiff d N).continuous_deriv (by norm_num)).abs
    have hsplit : ∫ x in a..b, |deriv (vw d N) x|
        = (∫ x in a..(N:ℝ), |deriv (vw d N) x|)
          + (∫ x in (N:ℝ)..b, |deriv (vw d N) x|) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable a (N:ℝ)) (hcont.intervalIntegrable (N:ℝ) b)]
    rw [hsplit]
    have hleft : ∫ x in a..(N:ℝ), |deriv (vw d N) x| = 1 := by
      rw [hadef]; exact integral_abs_deriv_vw_left hd hN
    have hright : ∫ x in (N:ℝ)..b, |deriv (vw d N) x| ≤ 1 := by
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (N:ℝ) b →
          |deriv (vw d N) x| = - deriv (vw d N) x := by
        filter_upwards with x hx
        rw [Set.uIoc_of_le (by rw [hbdef]; linarith : (N:ℝ) ≤ b)] at hx
        by_cases h2 : 2*(N:ℝ) ≤ x
        · exact abs_of_nonpos (deriv_vw_nonpos_right hd hN h2)
        · push Not at h2
          have hlt : (N:ℝ) < x := hx.1
          rw [deriv_vw_eq_zero_plateau hd hN hlt h2, abs_zero, neg_zero]
      rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_neg,
        intervalIntegral.integral_deriv_eq_sub (f := vw d N) (a := (N:ℝ)) (b := b)]
      · have hb0' : vw d N b = 0 := by rw [hbdef]; exact vw_eq_zero_of_ge hd le_rfl
        have hN1 : vw d N (N:ℝ) = 1 := vw_eq_one hd le_rfl (by linarith)
        rw [hb0', hN1]; norm_num
      · intro x _
        exact ((vw_contDiff d N).differentiable (by norm_num) x).hasDerivAt.differentiableAt
      · exact ((vw_contDiff d N).continuous_deriv (by norm_num)).intervalIntegrable _ _
    linarith
  calc ‖∫ x in a..b, ((vw d N x : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((vdcTheta t ((k:ℤ):ℝ) x : ℝ) : ℂ))‖
      ≤ 4 * (|vw d N a| + ∫ x in a..b, |deriv (vw d N) x|) /
          (2*Real.pi*((k:ℤ):ℝ) - t/a) := hkey
    _ ≤ 4 * (0 + 2) / (2*Real.pi*((k:ℤ):ℝ) - t/a) := by
        rw [hva]
        gcongr
    _ = 8 / (2*Real.pi*((k:ℤ):ℝ) - t/a) := by ring

lemma vdcTheta_contDiff3 (t k : ℝ) : ContDiff ℝ 3 (vdcTheta t k) := by
  unfold vdcTheta
  have h1 : ContDiff ℝ 3 (fun x : ℝ => Real.log (vdcSm x)) :=
    (vdcSm_contDiff.log (fun x => ne_of_gt (vdcSm_pos x))).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have h2 : ContDiff ℝ 3 (fun x : ℝ => 2 * Real.pi * k * x) := by fun_prop
  exact (contDiff_const.mul h1).sub h2

/-- The surrogate phase has the same first three derivatives as `t log x − 2πkx` above `1/2`. -/
lemma deriv2_vdcTheta {t k x : ℝ} (hx : 1/2 < x) :
    deriv (deriv (vdcTheta t k)) x = -t/x^2 := by
  have hev : deriv (vdcTheta t k) =ᶠ[𝓝 x] (fun y : ℝ => t/y - 2*Real.pi*k) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact deriv_vdcTheta hy
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun y : ℝ => t/y - 2*Real.pi*k) (-t/x^2) x := by
    have h1 : HasDerivAt (fun y : ℝ => t/y) (-t/x^2) x := by
      have h2 := (hasDerivAt_inv (ne_of_gt (by linarith : (0:ℝ) < x))).const_mul t
      have h3 : -t * x⁻¹ ^ 2 = -t/x^2 := by ring
      simpa [div_eq_mul_inv, h3] using h2
    simpa using h1.sub_const (2*Real.pi*k)
  exact hd.deriv

lemma deriv3_vdcTheta {t k x : ℝ} (hx : 1/2 < x) :
    iteratedDeriv 3 (vdcTheta t k) x = 2*t/x^3 := by
  have h3eq : iteratedDeriv 3 (vdcTheta t k) = deriv (deriv (deriv (vdcTheta t k))) := by
    rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h3eq]
  have hev : deriv (deriv (vdcTheta t k)) =ᶠ[𝓝 x] (fun y : ℝ => -t/y^2) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact deriv2_vdcTheta hy
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun y : ℝ => -t/y^2) (2*t/x^3) x := by
    have hx0 : x ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < x)
    have h1 : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have h2 := h1.inv (pow_ne_zero 2 hx0)
    have h3 : HasDerivAt (fun y : ℝ => (y^2)⁻¹) (-(2*x)/(x^2)^2) x := h2
    have h4 : HasDerivAt (fun y : ℝ => -t * (y^2)⁻¹) (-t * (-(2*x)/(x^2)^2)) x :=
      h3.const_mul (-t)
    have h5 : -t * (-(2*x)/(x^2)^2) = 2*t/x^3 := by
      field_simp
    rw [h5] at h4
    have hfun : (fun y : ℝ => -t * (y^2)⁻¹) = fun y : ℝ => -t/y^2 := by
      funext y; ring
    rwa [hfun] at h4
  exact hd.deriv

/-- Total variation of `vw d N` over its support is at most `2`. -/
lemma integral_abs_deriv_vw_support {N : ℕ} (hN : 1 ≤ N) {d : ℝ} (hd : 0 < d) :
    ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |deriv (vw d N) x| ≤ 2 := by
  have hcont : Continuous (fun x : ℝ => |deriv (vw d N) x|) :=
    ((vw_contDiff d N).continuous_deriv (by norm_num)).abs
  have hsplit : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |deriv (vw d N) x|
      = (∫ x in ((N:ℝ)-d)..(N:ℝ), |deriv (vw d N) x|)
        + (∫ x in (N:ℝ)..(2*(N:ℝ)+d), |deriv (vw d N) x|) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  rw [hsplit]
  have hleft : ∫ x in ((N:ℝ)-d)..(N:ℝ), |deriv (vw d N) x| = 1 := by
    simpa only [vdcA] using integral_abs_deriv_vw_left hd hN
  have hright : ∫ x in (N:ℝ)..(2*(N:ℝ)+d), |deriv (vw d N) x| ≤ 1 := by
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (N:ℝ) (2*(N:ℝ)+d) →
        |deriv (vw d N) x| = - deriv (vw d N) x := by
      filter_upwards with x hx
      rw [Set.uIoc_of_le (by linarith : (N:ℝ) ≤ 2*(N:ℝ)+d)] at hx
      by_cases h2 : 2*(N:ℝ) ≤ x
      · exact abs_of_nonpos (deriv_vw_nonpos_right hd hN h2)
      · push Not at h2
        rw [deriv_vw_eq_zero_plateau hd hN hx.1 h2, abs_zero, neg_zero]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_neg,
      intervalIntegral.integral_deriv_eq_sub (f := vw d N) (a := (N:ℝ)) (b := 2*(N:ℝ)+d)]
    · have hb0 : vw d N (2*(N:ℝ)+d) = 0 := vw_eq_zero_of_ge hd le_rfl
      have hN1 : vw d N (N:ℝ) = 1 := vw_eq_one hd le_rfl (by linarith)
      rw [hb0, hN1]; norm_num
    · intro x _
      exact ((vw_contDiff d N).differentiable (by norm_num) x).hasDerivAt.differentiableAt
    · exact ((vw_contDiff d N).continuous_deriv (by norm_num)).intervalIntegrable _ _
  linarith

/-- **Non-positive indices `k ≤ 0`**: the phase `x ↦ t log x − 2πkx` is strictly increasing on the
support with `|θ'| ≥ m = t/(2N+d) + 2π|k|`, so the second-order test gives a bound decaying in
`|k|` (`M = t/(N−d)²`, `M₃ = 2t/(N−d)³`), with the three `L¹`-norms of `vw d N` entering as
`K0, K1, K2`. -/
theorem vdcI_nonpos {d : ℝ} {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hd2 : (1:ℝ)/2 < (N:ℝ) - d) (ht : 0 < t) {k : ℤ} (hk : k ≤ 0)
    {K0 K1 K2 : ℝ}
    (hK0 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |vw d N x| ≤ K0)
    (hK1 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |deriv (vw d N) x| ≤ K1)
    (hK2 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |deriv (deriv (vw d N)) x| ≤ K2) :
    ‖vdcI d N t k‖ ≤ 8 * (K2
        + K1 * (t / ((N:ℝ)-d)^2) / (t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|)
        + K0 * (2*t / ((N:ℝ)-d)^3) / (t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|)
        + K0 * (t / ((N:ℝ)-d)^2)^2 / (t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|)^2)
      / (t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|)^2 := by
  set a : ℝ := (N:ℝ) - d with hadef
  set b : ℝ := 2*(N:ℝ) + d with hbdef
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have ha12 : (1:ℝ)/2 < a := by rw [hadef]; exact hd2
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by rw [hbdef]; positivity
  have ht0 : (0:ℝ) < t := ht
  set m : ℝ := t/b + 2*Real.pi*|(k:ℝ)| with hmdef
  set M : ℝ := t / a^2 with hMdef
  set M3 : ℝ := 2*t / a^3 with hM3def
  have hmpos : 0 < m := by rw [hmdef]; positivity
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hM30 : 0 ≤ M3 := by rw [hM3def]; positivity
  -- reduce to the support with the surrogate phase
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc a b →
      (vw d N x : ℂ) * Complex.exp (Complex.I *
        (((t*Real.log x - 2*Real.pi*((k:ℝ))*x : ℝ)) : ℂ)) = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have hv : vw d N x = 0 := by
      rcases hx with h | h
      · refine vw_eq_zero_of_le hd ?_
        have : x < a := h
        rw [hadef] at this; linarith
      · refine vw_eq_zero_of_ge hd ?_
        have : b < x := h
        rw [hbdef] at this; linarith
    rw [hv]; simp
  have hI : vdcI d N t k = ∫ x in a..b,
      ((vw d N x : ℝ) : ℂ) * Complex.exp (Complex.I * ((vdcTheta t (k:ℝ) x : ℝ) : ℂ)) := by
    rw [vdcI]
    rw [integral_eq_intervalIntegral_of_support hab hsupp]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : (1:ℝ)/2 ≤ x := le_of_lt (lt_of_lt_of_le ha12 hx.1)
    rw [vdcTheta_eq hx1]
  rw [hI]
  have hgs : ∀ x : ℝ, x ∉ Set.Ioo a b → vw d N x = 0 := by
    intro x hx
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hx
    rcases hx with hx | hx
    · refine vw_eq_zero_of_le hd ?_
      have h : x ≤ a := hx
      rw [hadef] at h
      exact h
    · refine vw_eq_zero_of_ge hd ?_
      have h : b ≤ x := hx
      rw [hbdef] at h
      exact h
  have hgN : ContDiff ℝ 2 (vw d N) :=
    (vw_contDiff d N).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hmono : AntitoneOn (deriv (vdcTheta t (k:ℝ))) (Set.Icc a b) :=
    (vdcTheta_antitone ht.le ha12).mono Set.Icc_subset_Ici_self
  have hbdd : ∀ x ∈ Set.Icc a b, m ≤ |deriv (vdcTheta t (k:ℝ)) x| := by
    intro x hx
    have hx12 : (1:ℝ)/2 < x := lt_of_lt_of_le ha12 hx.1
    have hx0 : 0 < x := by linarith
    rw [deriv_vdcTheta hx12]
    have h1 : t/b ≤ t/x := by
      rw [div_le_div_iff₀ hb0 hx0]
      nlinarith [hx.2, ht0]
    have hkabs : ((-(k:ℝ)) = |(k:ℝ)|) := by
      rw [abs_of_nonpos]; exact_mod_cast hk
    have h3 : t / x - 2*Real.pi*(k:ℝ) = t/x + 2*Real.pi*(-(k:ℝ)) := by ring
    rw [h3, hkabs, abs_of_nonneg (by positivity : (0:ℝ) ≤ t/x + 2*Real.pi*|(k:ℝ)|)]
    rw [hmdef]; linarith
  have h2b : ∀ x ∈ Set.Icc a b, |deriv (deriv (vdcTheta t (k:ℝ))) x| ≤ M := by
    intro x hx
    have hx12 : (1:ℝ)/2 < x := lt_of_lt_of_le ha12 hx.1
    have hx0 : 0 < x := by linarith
    rw [deriv2_vdcTheta hx12, abs_div, abs_neg, abs_of_nonneg ht0.le, abs_of_pos (pow_pos hx0 2)]
    rw [hMdef, div_le_div_iff₀ (pow_pos hx0 2) (pow_pos ha0 2)]
    have h1 : a^2 ≤ x^2 := by
      apply pow_le_pow_left₀ (le_of_lt ha0) hx.1
    exact mul_le_mul_of_nonneg_left (by linarith) ht0.le
  have h3b : ∀ x ∈ Set.Icc a b, |iteratedDeriv 3 (vdcTheta t (k:ℝ)) x| ≤ M3 := by
    intro x hx
    have hx12 : (1:ℝ)/2 < x := lt_of_lt_of_le ha12 hx.1
    have hx0 : 0 < x := by linarith
    rw [deriv3_vdcTheta hx12, hM3def]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*t), abs_of_pos (pow_pos hx0 3)]
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos ha0 3)
    exact pow_le_pow_left₀ (le_of_lt ha0) hx.1 3
  have hIBP := Commons.Analysis.Oscillatory.norm_integral_exp_two_ibp
    (m := m) (M := M) (M3 := M3) hab hmpos (vdcTheta_contDiff3 t (k:ℝ)) (Or.inr hmono)
    hbdd h2b h3b hgN hgs
  have hkey : 8 * ((∫ x in a..b, |deriv (deriv (vw d N)) x|)
        + (∫ x in a..b, |deriv (vw d N) x|) * M / m
        + (∫ x in a..b, |vw d N x|) * M3 / m
        + (∫ x in a..b, |vw d N x|) * M^2 / m^2) / m^2
      ≤ 8 * (K2 + K1 * M / m + K0 * M3 / m + K0 * M^2 / m^2) / m^2 := by
    gcongr
  refine le_trans hIBP ?_
  rw [hmdef, hMdef, hM3def] at hkey ⊢
  refine le_trans hkey (le_of_eq ?_)
  ring

/-- **Far-left second-order companion**: for `k ≥ 1` with `x_k < N−d` the phase is strictly
decreasing on the support with `|θ'| ≥ m = 2πk − t/(N−d)`, so the second-order test gives a bound
decaying like `m⁻²` (this is the second member of the `min` used in the far-left summation). -/
theorem vdcI_far_left_sq {d : ℝ} {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hd2 : (1:ℝ)/2 < (N:ℝ) - d) (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k)
    (hxk : vdcX t k < (N:ℝ) - d) {K0 K1 K2 : ℝ}
    (hK0 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |vw d N x| ≤ K0)
    (hK1 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |deriv (vw d N) x| ≤ K1)
    (hK2 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |deriv (deriv (vw d N)) x| ≤ K2) :
    ‖vdcI d N t (k:ℤ)‖ ≤ 8 * (K2
        + K1 * (t / ((N:ℝ)-d)^2) / (2*Real.pi*((k:ℤ):ℝ) - t/((N:ℝ)-d))
        + K0 * (2*t / ((N:ℝ)-d)^3) / (2*Real.pi*((k:ℤ):ℝ) - t/((N:ℝ)-d))
        + K0 * (t / ((N:ℝ)-d)^2)^2 / (2*Real.pi*((k:ℤ):ℝ) - t/((N:ℝ)-d))^2)
      / (2*Real.pi*((k:ℤ):ℝ) - t/((N:ℝ)-d))^2 := by
  set a : ℝ := (N:ℝ) - d with hadef
  set b : ℝ := 2*(N:ℝ) + d with hbdef
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have ha12 : (1:ℝ)/2 < a := by rw [hadef]; exact hd2
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by rw [hbdef]; positivity
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hkcast : ((k:ℤ):ℝ) = (k:ℝ) := by push_cast; ring
  have h2pik : (0:ℝ) < 2*Real.pi*((k:ℤ):ℝ) := by positivity
  have hxk' : t < (2*Real.pi*((k:ℤ):ℝ)) * a := by
    rw [vdcX] at hxk
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(k:ℝ))] at hxk
    rw [hkcast]
    nlinarith [hxk]
  set m : ℝ := 2*Real.pi*((k:ℤ):ℝ) - t/a with hmdef
  set M : ℝ := t / a^2 with hMdef
  set M3 : ℝ := 2*t / a^3 with hM3def
  have hmpos : 0 < m := by
    rw [hmdef, sub_pos, div_lt_iff₀ ha0]
    linarith [hxk']
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hM30 : 0 ≤ M3 := by rw [hM3def]; positivity
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc a b →
      (vw d N x : ℂ) * Complex.exp (Complex.I *
        (((t*Real.log x - 2*Real.pi*(((k:ℤ):ℝ))*x : ℝ)) : ℂ)) = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have hv : vw d N x = 0 := by
      rcases hx with h | h
      · refine vw_eq_zero_of_le hd ?_
        have : x < a := h
        rw [hadef] at this; linarith
      · refine vw_eq_zero_of_ge hd ?_
        have : b < x := h
        rw [hbdef] at this; linarith
    rw [hv]; simp
  have hI : vdcI d N t (k:ℤ) = ∫ x in a..b,
      ((vw d N x : ℝ) : ℂ) * Complex.exp (Complex.I * ((vdcTheta t ((k:ℤ):ℝ) x : ℝ) : ℂ)) := by
    rw [vdcI]
    rw [integral_eq_intervalIntegral_of_support hab hsupp]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : (1:ℝ)/2 ≤ x := le_of_lt (lt_of_lt_of_le ha12 hx.1)
    rw [vdcTheta_eq hx1]
  rw [hI]
  have hgs : ∀ x : ℝ, x ∉ Set.Ioo a b → vw d N x = 0 := by
    intro x hx
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hx
    rcases hx with hx | hx
    · refine vw_eq_zero_of_le hd ?_
      have h : x ≤ a := hx
      rw [hadef] at h
      exact h
    · refine vw_eq_zero_of_ge hd ?_
      have h : b ≤ x := hx
      rw [hbdef] at h
      exact h
  have hgN : ContDiff ℝ 2 (vw d N) :=
    (vw_contDiff d N).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hmono : AntitoneOn (deriv (vdcTheta t ((k:ℤ):ℝ))) (Set.Icc a b) :=
    (vdcTheta_antitone ht.le ha12).mono Set.Icc_subset_Ici_self
  have hbdd : ∀ x ∈ Set.Icc a b, m ≤ |deriv (vdcTheta t ((k:ℤ):ℝ)) x| := by
    intro x hx
    have hx12 : (1:ℝ)/2 < x := lt_of_lt_of_le ha12 hx.1
    have hx0 : 0 < x := by linarith
    rw [deriv_vdcTheta hx12]
    have h1 : t/x ≤ t/a := by
      rw [div_le_div_iff₀ hx0 ha0]
      nlinarith [hx.1, ht]
    have h3 : t/x - 2*Real.pi*((k:ℤ):ℝ) ≤ 0 := by
      have ht_a : t/a ≤ 2*Real.pi*((k:ℤ):ℝ) := by
        rw [div_le_iff₀ ha0]
        linarith [hxk']
      linarith
    rw [abs_of_nonpos h3]
    rw [hmdef]
    linarith
  have h2b : ∀ x ∈ Set.Icc a b, |deriv (deriv (vdcTheta t ((k:ℤ):ℝ))) x| ≤ M := by
    intro x hx
    have hx12 : (1:ℝ)/2 < x := lt_of_lt_of_le ha12 hx.1
    have hx0 : 0 < x := by linarith
    rw [deriv2_vdcTheta hx12, abs_div, abs_neg, abs_of_nonneg ht.le, abs_of_pos (pow_pos hx0 2)]
    rw [hMdef, div_le_div_iff₀ (pow_pos hx0 2) (pow_pos ha0 2)]
    have h1 : a^2 ≤ x^2 := pow_le_pow_left₀ (le_of_lt ha0) hx.1 2
    exact mul_le_mul_of_nonneg_left (by linarith) ht.le
  have h3b : ∀ x ∈ Set.Icc a b, |iteratedDeriv 3 (vdcTheta t ((k:ℤ):ℝ)) x| ≤ M3 := by
    intro x hx
    have hx12 : (1:ℝ)/2 < x := lt_of_lt_of_le ha12 hx.1
    have hx0 : 0 < x := by linarith
    rw [deriv3_vdcTheta hx12, hM3def]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*t), abs_of_pos (pow_pos hx0 3)]
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos ha0 3)
    exact pow_le_pow_left₀ (le_of_lt ha0) hx.1 3
  have hIBP := Commons.Analysis.Oscillatory.norm_integral_exp_two_ibp
    (m := m) (M := M) (M3 := M3) hab hmpos (vdcTheta_contDiff3 t ((k:ℤ):ℝ)) (Or.inr hmono)
    hbdd h2b h3b hgN hgs
  have hkey : 8 * ((∫ x in a..b, |deriv (deriv (vw d N)) x|)
        + (∫ x in a..b, |deriv (vw d N) x|) * M / m
        + (∫ x in a..b, |vw d N x|) * M3 / m
        + (∫ x in a..b, |vw d N x|) * M^2 / m^2) / m^2
      ≤ 8 * (K2 + K1 * M / m + K0 * M3 / m + K0 * M^2 / m^2) / m^2 := by
    gcongr
  refine le_trans hIBP ?_
  rw [hmdef, hMdef, hM3def] at hkey ⊢
  refine le_trans hkey (le_of_eq ?_)
  ring

/-- **Telescoping second-moment bound**: `Σ_{j=J+1}^{n} 1/j² ≤ 1/J` for `J ≥ 1`. -/
lemma sum_Icc_inv_sq_le {J n : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Icc (J+1) n, 1/((j:ℝ)^2) ≤ 1/(J:ℝ) := by
  rcases le_or_gt (J+1) n with h | h
  · have hterm : ∀ j ∈ Finset.Icc (J+1) n,
        1/((j:ℝ)^2) ≤ (-1/(j:ℝ)) - (-1/((j-1:ℕ):ℝ)) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hj2 : 2 ≤ j := by omega
      have hj1 : 1 ≤ j := by omega
      have hjpos : (0:ℝ) < (j:ℝ) := by
        have : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj2
        linarith
      have hjm1 : (0:ℝ) < (j:ℝ) - 1 := by
        have : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj2
        linarith
      have hcast : ((j-1:ℕ):ℝ) = (j:ℝ) - 1 := by
        rw [Nat.cast_sub hj1]; norm_num
      rw [hcast]
      have hgoal : -1/(j:ℝ) - -1/((j:ℝ)-1) = 1/((j:ℝ)-1) - 1/(j:ℝ) := by ring
      rw [hgoal]
      have h1 : (1:ℝ)/((j:ℝ)-1) - 1/(j:ℝ) = 1/(((j:ℝ)-1)*(j:ℝ)) := by
        rw [div_sub_div 1 1 (ne_of_gt hjm1) (ne_of_gt hjpos)]
        norm_num
      have h2 : (1:ℝ)/((j:ℝ)^2) ≤ 1/(((j:ℝ)-1)*(j:ℝ)) := by
        rw [div_le_div_iff₀ (pow_pos hjpos 2) (by positivity : (0:ℝ) < ((j:ℝ)-1)*(j:ℝ))]
        nlinarith
      rw [h1]
      exact h2
    calc ∑ j ∈ Finset.Icc (J+1) n, 1/((j:ℝ)^2)
        ≤ ∑ j ∈ Finset.Icc (J+1) n, ((-1/(j:ℝ)) - (-1/((j-1:ℕ):ℝ))) :=
          Finset.sum_le_sum hterm
      _ = (-1/(n:ℝ)) - (-1/(J:ℝ)) := by
          have := sum_Icc_telescope (fun j : ℕ => -1/(j:ℝ)) h
          simpa [Nat.add_sub_cancel] using this
      _ = 1/(J:ℝ) - 1/(n:ℝ) := by ring
      _ ≤ 1/(J:ℝ) := sub_le_self _ (div_nonneg zero_le_one (Nat.cast_nonneg n))
  · have hempty : Finset.Icc (J+1) n = ∅ := Finset.Icc_eq_empty_iff.mpr (by omega)
    rw [hempty, Finset.sum_empty]
    exact div_nonneg zero_le_one (Nat.cast_nonneg J)

/-- **Shift reindexing**: `Σ_{j=1}^{n} 1/(j+C) = Σ_{j=C+1}^{C+n} 1/j`. -/
lemma sum_Icc_shift_inv {C n : ℕ} :
    ∑ j ∈ Finset.Icc (C+1) (C+n), (1:ℝ)/(j:ℝ)
      = ∑ j ∈ Finset.Icc 1 n, (1:ℝ)/((j:ℝ) + (C:ℝ)) := by
  refine Finset.sum_bij' (fun j _ => j - C) (fun j _ => j + C) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact Nat.sub_add_cancel (by omega)
  · intro j hj
    exact Nat.add_sub_cancel j C
  · intro j hj
    rw [Finset.mem_Icc] at hj
    have hcast : (((j - C) : ℕ) : ℝ) = (j:ℝ) - (C:ℝ) :=
      Nat.cast_sub (by omega : C ≤ j)
    rw [hcast, sub_add_cancel]

/-- **Head/tail split for a minimum**: `Σ_{j≤n} min(A/j, B/j²) = O(A·log(1 + B/A))`, uniformly in
`n`.  Split the index range at `J := max 1 ⌈B/A⌉`: below `J` use `min ≤ A/j`, above `J` use
`min ≤ B/j² ≤ B·(1/j²)` together with the telescoping `Σ_{j>J} 1/j² ≤ 1/J ≤ A/B`. -/
lemma sum_min_div_sq_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, min (A/(j:ℝ)) (B/((j:ℝ)^2)) ≤ A * (3 + Real.log (2 + B/A)) := by
  set J : ℕ := max 1 ⌈B/A⌉₊ with hJ
  have hJ1 : 1 ≤ J := le_max_left _ _
  have hJBA : B/A ≤ (J:ℝ) := by
    have h1 : (⌈B/A⌉₊ : ℝ) ≤ (J:ℝ) := by
      rw [hJ]; push_cast; exact le_max_right _ _
    exact le_trans (Nat.le_ceil (B/A)) h1
  have hJbound : (J:ℝ) ≤ 1 + B/A := by
    have h1 : (J:ℝ) = max 1 (⌈B/A⌉₊ : ℝ) := by rw [hJ]; push_cast; rfl
    rw [h1]
    refine max_le ?_ ?_
    · have : (0:ℝ) < B/A := div_pos hB hA
      linarith
    · have := Nat.ceil_lt_add_one (le_of_lt (div_pos hB hA))
      linarith
  have hsplit : ∑ j ∈ Finset.Icc 1 n, min (A/(j:ℝ)) (B/((j:ℝ)^2))
      = (∑ j ∈ (Finset.Icc 1 n).filter (fun j => j ≤ J), min (A/(j:ℝ)) (B/((j:ℝ)^2)))
        + ∑ j ∈ (Finset.Icc 1 n).filter (fun j => ¬ j ≤ J), min (A/(j:ℝ)) (B/((j:ℝ)^2)) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun j => j ≤ J) _).symm
  rw [hsplit]
  have hhead : ∑ j ∈ (Finset.Icc 1 n).filter (fun j => j ≤ J), min (A/(j:ℝ)) (B/((j:ℝ)^2))
      ≤ A * (1 + Real.log (1 + (J:ℝ))) := by
    have hsub : (Finset.Icc 1 n).filter (fun j => j ≤ J) ⊆ Finset.Icc 1 J := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      rw [Finset.mem_Icc]
      exact ⟨hj.1.1, hj.2⟩
    calc ∑ j ∈ (Finset.Icc 1 n).filter (fun j => j ≤ J), min (A/(j:ℝ)) (B/((j:ℝ)^2))
        ≤ ∑ j ∈ Finset.Icc 1 J, min (A/(j:ℝ)) (B/((j:ℝ)^2)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => le_min (by positivity) (by positivity))
      _ ≤ ∑ j ∈ Finset.Icc 1 J, A/(j:ℝ) :=
          Finset.sum_le_sum (fun j _ => min_le_left _ _)
      _ = A * ∑ j ∈ Finset.Icc 1 J, 1/(j:ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ A * (1 + Real.log (1 + (J:ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hA.le
          simpa using sum_Icc_inv_le (a := 1) (b := J) (by omega) (by omega)
  have htail : ∑ j ∈ (Finset.Icc 1 n).filter (fun j => ¬ j ≤ J), min (A/(j:ℝ)) (B/((j:ℝ)^2)) ≤ A := by
    have hsub : (Finset.Icc 1 n).filter (fun j => ¬ j ≤ J) ⊆ Finset.Icc (J+1) n := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc, not_le] at hj
      rw [Finset.mem_Icc]
      exact ⟨hj.2, hj.1.2⟩
    calc ∑ j ∈ (Finset.Icc 1 n).filter (fun j => ¬ j ≤ J), min (A/(j:ℝ)) (B/((j:ℝ)^2))
        ≤ ∑ j ∈ Finset.Icc (J+1) n, min (A/(j:ℝ)) (B/((j:ℝ)^2)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => le_min (by positivity) (by positivity))
      _ ≤ ∑ j ∈ Finset.Icc (J+1) n, B/((j:ℝ)^2) :=
          Finset.sum_le_sum (fun j _ => min_le_right _ _)
      _ = B * ∑ j ∈ Finset.Icc (J+1) n, 1/((j:ℝ)^2) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ B * (1/(J:ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le hJ1) hB.le
      _ ≤ A := by
          have hJpos : (0:ℝ) < (J:ℝ) := by exact_mod_cast hJ1
          have hBJ : B / (J:ℝ) ≤ A := by
            rw [div_le_iff₀ hJpos]
            have := (div_le_iff₀ hA).mp hJBA
            linarith
          calc B * (1/(J:ℝ)) = B/(J:ℝ) := by ring
            _ ≤ A := hBJ
  have hlog : Real.log (1 + (J:ℝ)) ≤ Real.log (2 + B/A) := by
    refine Real.log_le_log (by positivity) ?_
    linarith
  nlinarith [hhead, htail, hlog, hA, mul_le_mul_of_nonneg_left hlog hA.le]

/-- **Universal Fresnel bound**: whenever the stationary point `x_k` satisfies `(2N+d)/6 ≤ x_k` and
`x_k ≤ 4(N−d)` (so that `u/x_k ∈ [1/4,6]` on the support), the Poisson integral is at most
`2(C1+145)·x_k/√t`. -/
theorem vdcI_le_fresnel {d : ℝ} {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hd2 : (1:ℝ)/2 < (N:ℝ) - d) (ht : 2 ≤ t) {C1 : ℝ} (hC1nn : 0 ≤ C1)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t)
    {k : ℕ} (hk : 1 ≤ k)
    (hb6 : (2*(N:ℝ)+d)/6 ≤ vdcX t k) (h4a : vdcX t k ≤ 4*((N:ℝ)-d)) :
    ‖vdcI d N t (k:ℤ)‖ ≤ 2 * (C1 + 145) * (vdcX t k) / Real.sqrt t := by
  have ht0 : (0:ℝ) < t := by linarith
  have hspos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hx0 : 0 < vdcX t k := vdcX_pos ht0 hk
  have hK : (0:ℝ) ≤ (C1 + 145)/Real.sqrt t := div_nonneg (by linarith) hspos.le
  set a : ℝ := (N:ℝ) - d with hadef
  set b : ℝ := 2*(N:ℝ) + d with hbdef
  have ha0 : (0:ℝ) < a := by rw [hadef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have hb6' : b ≤ 6 * vdcX t k := by rw [hbdef]; linarith [hb6]
  have h4a' : vdcX t k ≤ 4 * a := by rw [hadef]; exact h4a
  -- rewrite the auxiliary integral `J`
  have h1 := vdc_ibp hd hd1 hN (t := t) (x := vdcX t k) hx0
  have h2 := vdc_ibp_subst hd hd1 hN (t := t) (x := vdcX t k) hx0
  have hJeq : (∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y)
      = - ∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k)) := by
    calc (∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y)
        = -vdcX t k * ∫ y : ℝ,
            (((deriv (vw d N)) (vdcX t k * y) : ℝ) : ℂ) * vdcPrim t y := h1
      _ = -(vdcX t k * ∫ y : ℝ,
            (((deriv (vw d N)) (vdcX t k * y) : ℝ) : ℂ) * vdcPrim t y) := by ring
      _ = - ∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k)) := by rw [h2]
  have hcont : Continuous (fun u : ℝ => |deriv (vw d N) u|) :=
    ((vw_contDiff d N).continuous_deriv (by norm_num)).abs
  have hsupp : ∀ u : ℝ, u ∉ Set.Icc a b →
      (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k)) = 0 := by
    intro u hu
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    have hv : deriv (vw d N) u = 0 := by
      rcases hu with h | h
      · refine deriv_vw_zero_of_lt_A hd ?_
        exact h
      · refine deriv_vw_zero_of_gt_B hd ?_
        have h' : b < u := h
        rw [hbdef] at h'
        exact h'
    rw [hv, Complex.ofReal_zero, zero_mul]
  have hpt : ∀ u ∈ Set.Icc a b, ‖vdcPrim t (u/(vdcX t k))‖ ≤ (C1 + 145)/Real.sqrt t := by
    intro u hu
    refine norm_vdcPrim_le_window C1 hC1 ht ?_ ?_
    · rw [le_div_iff₀ hx0]
      nlinarith [hu.1, h4a', ha0]
    · rw [div_le_iff₀ hx0]
      linarith [hu.2, hb6']
  have hJbound : ‖∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖
      ≤ 2 * (C1 + 145) / Real.sqrt t := by
    calc ‖∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖
        ≤ ∫ u : ℝ, ‖(((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ u in a..b, ‖(((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖ :=
          integral_eq_intervalIntegral_of_support_real hab
            (fun u hu => by rw [hsupp u hu, norm_zero])
      _ ≤ ∫ u in a..b, |deriv (vw d N) u| * ((C1 + 145)/Real.sqrt t) := by
          refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
          · refine ContinuousOn.intervalIntegrable ?_
            refine ContinuousOn.norm ?_
            refine ContinuousOn.mul ?_ ?_
            · exact Complex.continuous_ofReal.comp_continuousOn
                (((vw_contDiff d N).continuous_deriv (by norm_num)).continuousOn)
            · refine (continuousOn_vdcPrim t).comp (continuous_id.div_const _).continuousOn ?_
              intro u hu
              rw [Set.mem_Ioi]
              rw [Set.uIcc_of_le hab] at hu
              exact div_pos (lt_of_lt_of_le ha0 hu.1) hx0
          · exact (hcont.mul continuous_const).intervalIntegrable _ _
          · intro u hu
            rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]
            exact mul_le_mul_of_nonneg_left (hpt u hu) (abs_nonneg _)
      _ = ((C1 + 145)/Real.sqrt t) * ∫ u in a..b, |deriv (vw d N) u| := by
          rw [intervalIntegral.integral_mul_const, mul_comm]
      _ ≤ ((C1 + 145)/Real.sqrt t) * 2 :=
          mul_le_mul_of_nonneg_left (integral_abs_deriv_vw_support hN hd) hK
      _ = 2 * (C1 + 145) / Real.sqrt t := by ring
  calc ‖vdcI d N t (k:ℤ)‖
      = ‖((vdcX t k : ℝ) : ℂ)^((1:ℂ)+Complex.I*(t:ℂ))
          * (∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y)‖ := by
        rw [vdcI_eq_cpow_mul N hd hd1 hN t hk ht0]
    _ = vdcX t k * ‖∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y‖ := by
        rw [norm_mul, norm_cpow_one_add_I_mul hx0 t]
    _ = vdcX t k * ‖∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖ := by
        rw [hJeq, norm_neg]
    _ ≤ vdcX t k * (2 * (C1 + 145) / Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hJbound (le_of_lt hx0)
    _ = 2 * (C1 + 145) * (vdcX t k) / Real.sqrt t := by ring

/-- **Shift reindexing, general function**: `Σ_{k=J₀+1}^{n} f k = Σ_{j=1}^{n-J₀} f (J₀+j)`. -/
lemma sum_Icc_shift_eq {J₀ n : ℕ} (h : J₀ ≤ n) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc (J₀+1) n, f k = ∑ j ∈ Finset.Icc 1 (n - J₀), f (J₀ + j) := by
  refine Finset.sum_bij' (fun k _ => k - J₀) (fun j _ => J₀ + j) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    omega
  · intro k hk
    exact Nat.add_sub_cancel_left J₀ k
  · intro k hk
    rw [Finset.mem_Icc] at hk
    congr 1
    omega

/-- Reindex a sum over `{a,…,b} ⊂ ℤ` (`a,b : ℕ`) as a sum over `{a,…,b} ⊂ ℕ`. -/
lemma sum_Icc_int_eq_sum_Icc_nat' (a b : ℕ) (g : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc (a : ℤ) (b : ℤ), g n.toNat)
      = ∑ m ∈ Finset.Icc a b, g m := by
  refine Finset.sum_bij' (fun (n : ℤ) _ => n.toNat) (fun (m : ℕ) _ => (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    omega
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ n)]
  · intro m hm
    simp
  · intro n hn
    simp

/-- **Poisson split**: `vdcS` is the sum of the Poisson integrals over the dual range
`{k : ⌈t/4πN⌉ ≤ k ≤ ⌊t/2πN⌋} ⊂ ℤ` plus the complementary series. -/
theorem vdc_poisson_split {d : ℝ} (N : ℕ) (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N) (t : ℝ) :
    vdcS N t = (∑ k ∈ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
          ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ), vdcI d N t k)
      + ∑' k : {k : ℤ // k ∉ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
          ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)}, vdcI d N t (k : ℤ) := by
  rw [vdc_poisson N hd hd1 hN t]
  exact (summable_vdcI N hd hd1 hN t).sum_add_tsum_compl.symm

/-- **The trivial regime `t ≤ 100`**: crude bounds
(`‖vdcS‖ ≤ N+1`, `‖vdcF‖ ≤ 11/2`, `‖vdcD‖ ≤ 1+8π`) suffice, since `√t ≤ 10`
makes the right-hand side at least `10^6·N + 10^7`. -/
theorem vdc_trivial_regime (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (htN : (N:ℝ) ≤ t) (ht : t ≤ 100) :
    ‖vdcS N t - vdcMain N t‖ ≤ (10000000:ℝ) * ((N:ℝ)/Real.sqrt t
      + Real.log ((N:ℝ)*t) + 1) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have ht1 : (1:ℝ) ≤ t := le_trans hN1 htN
  have ht0 : (0:ℝ) < t := by linarith
  have hS : ‖vdcS N t‖ ≤ (N:ℝ) + 1 := by
    have hterm : ∀ n ∈ Finset.Icc N (2*N), ‖(n:ℂ)^(Complex.I*(t:ℂ))‖ = 1 := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [cpow_I_mul_eq_exp_log (t := t) (n := n) (le_trans hN hn.1)]
      exact Complex.norm_exp_I_mul_ofReal (t * Real.log n)
    rw [vdcS]
    calc ‖∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(t:ℂ))‖
        ≤ ∑ n ∈ Finset.Icc N (2*N), ‖(n:ℂ)^(Complex.I*(t:ℂ))‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc N (2*N), (1:ℝ) := Finset.sum_congr rfl hterm
      _ = ((Finset.Icc N (2*N)).card : ℝ) := by rw [Finset.sum_const]; simp
      _ = (N:ℝ) + 1 := by
          rw [Nat.card_Icc]
          have h : 2*N + 1 - N = N + 1 := by omega
          rw [h]; push_cast; ring
  have hF : ‖vdcF t‖ ≤ 11/2 := by
    rw [vdcF]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y : ℝ => Complex.exp (Complex.I * ((t*(Real.log y - y):ℝ):ℂ)))
      (a := (1/2:ℝ)) (b := 6) (C := 1) (fun y _ => le_of_eq (Complex.norm_exp_I_mul_ofReal _))
    rw [one_mul] at h
    have habs : |(6:ℝ) - 1/2| = 11/2 := by norm_num
    rwa [habs] at h
  have hD : ‖vdcD N t‖ ≤ 1 + 8*Real.pi := vdcD_norm_le N hN t htN
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hMain : ‖vdcMain N t‖ ≤ 100 * (11/2) * (1 + 8*Real.pi) := by
    have hcp : ‖((t/(2*Real.pi):ℝ):ℂ)^((1:ℂ)+Complex.I*(t:ℂ))‖ = t/(2*Real.pi) :=
      norm_cpow_one_add_I_mul (div_pos ht0 (by positivity)) t
    rw [vdcMain, norm_mul, norm_mul, hcp]
    have htpi : t/(2*Real.pi) ≤ 100 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three, ht]
    have hF0 : 0 ≤ ‖vdcF t‖ := norm_nonneg _
    have hD0 : 0 ≤ ‖vdcD N t‖ := norm_nonneg _
    have h1 : t/(2*Real.pi) * ‖vdcF t‖ ≤ 100 * (11/2) :=
      mul_le_mul htpi hF hF0 (by norm_num)
    exact mul_le_mul h1 hD hD0 (by positivity)
  have hconst : 100 * (11/2) * (1 + 8*Real.pi) ≤ 550000 := by nlinarith [hpi4, Real.pi_pos]
  have hsqrt10 : Real.sqrt t ≤ 10 := by
    calc Real.sqrt t ≤ Real.sqrt 100 := Real.sqrt_le_sqrt ht
      _ = 10 := by norm_num
  have hN10 : (N:ℝ)/10 ≤ (N:ℝ)/Real.sqrt t := by
    have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have h1 : 1/Real.sqrt t ≥ 1/10 := one_div_le_one_div_of_le hspos hsqrt10
    calc (N:ℝ)/10 = (N:ℝ) * (1/10) := by ring
      _ ≤ (N:ℝ) * (1/Real.sqrt t) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (N:ℝ)/Real.sqrt t := by ring
  have hlog : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := Real.log_nonneg (by nlinarith)
  have hrhs : (10000000:ℝ) * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1)
      ≥ (10000000:ℝ) * ((N:ℝ)/10 + 1) := by
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*t) + 1 := by linarith
    nlinarith [hN10]
  have htri : ‖vdcS N t - vdcMain N t‖ ≤ ((N:ℝ) + 1) + 100 * (11/2) * (1 + 8*Real.pi) :=
    le_trans (norm_sub_le _ _) (add_le_add hS hMain)
  nlinarith [htri, hconst, hrhs, hN1]


/-- Elementary algebraic identity used in the reduction. -/
lemma sqrt_div_model_smul {t : ℝ} (ht : 0 < t) (A Y : ℝ) (hA : 0 < A) :
    Real.sqrt t * (Y / (A * (t/(2*Real.pi)))) = (2*Real.pi/(A*Real.sqrt t)) * Y := by
  have hπ : (0:ℝ) < 2*Real.pi := by positivity
  field_simp
  rw [Real.sq_sqrt (le_of_lt ht)]
  ring

set_option maxHeartbeats 1600000

/-! ## Ancillary bounds for the complement series (sessions 6-7) -/



/-- Harmonic-mean normalisation: substituting `x = N·K/k` into
`x·(2ξ B x/(x−N))/(ξ + B x/(x−N))`. -/
lemma vdc_min_harm_subst {N Kr k t ξ : ℝ} (hk : 0 < k) (hN : 0 < N) (ht : 0 < t) (hξ : 0 < ξ)
    (hKk : Kr ≠ k) :
    (N*Kr/k) * ((2*(ξ*(48*(N*Kr/k)/(t*((N*Kr/k) - N)))))/(ξ + 48*(N*Kr/k)/(t*((N*Kr/k) - N))))
      = 2*ξ*(48/t)*N*Kr^2/(k*(ξ*(Kr-k) + (48/t)*Kr)) := by
  have hx : (N*Kr/k) - N = N*(Kr-k)/k := by field_simp
  have hxne : (N*Kr/k) - N ≠ 0 := by
    rw [hx]
    exact div_ne_zero (mul_ne_zero (ne_of_gt hN) (sub_ne_zero.mpr hKk)) (ne_of_gt hk)
  rw [hx]
  field_simp
  try ring

/-- The `1/k ≤ 2/K` reduction step. -/
lemma vdc_min_harm_le {N Kr k t ξ : ℝ} (hk : 0 < k) (hN : 0 < N) (ht : 0 < t) (hξ : 0 < ξ)
    (hKr : 0 < Kr) (hkKr : k ≤ Kr) (h2k : Kr ≤ 2*k) :
    2*ξ*(48/t)*N*Kr^2/(k*(ξ*(Kr-k) + (48/t)*Kr))
      ≤ 4*ξ*(48/t)*N*Kr/(ξ*(Kr-k) + (48/t)*Kr) := by
  have hBpos : (0:ℝ) < 48/t := by positivity
  have hDpos : 0 < ξ*(Kr-k) + (48/t)*Kr := by
    have h1 : 0 ≤ Kr - k := by linarith
    have h3 : 0 ≤ ξ*(Kr-k) := mul_nonneg (le_of_lt hξ) h1
    have h2 : 0 < (48/t)*Kr := mul_pos hBpos hKr
    linarith
  have hden1 : 0 < k*(ξ*(Kr-k) + (48/t)*Kr) := mul_pos hk hDpos
  rw [div_le_div_iff₀ hden1 hDpos]
  have hfac : 4*ξ*(48/t)*N*Kr*(k*(ξ*(Kr-k) + (48/t)*Kr)) - 2*ξ*(48/t)*N*Kr^2*(ξ*(Kr-k) + (48/t)*Kr)
      = 2*ξ*(48/t)*N*Kr*(ξ*(Kr-k) + (48/t)*Kr)*(2*k - Kr) := by ring
  have hprod : 0 ≤ 2*ξ*(48/t)*N*Kr*(ξ*(Kr-k) + (48/t)*Kr)*(2*k - Kr) := by
    have h1 : 0 ≤ 2*(k:ℝ) - Kr := by linarith
    have h2 : 0 ≤ 2*ξ*(48/t)*N*Kr*(ξ*(Kr-k) + (48/t)*Kr) := by
      have h3 : 0 ≤ ξ*(Kr-k) + (48/t)*Kr := le_of_lt hDpos
      have h4 : 0 ≤ 2*ξ*(48/t)*N*Kr := by positivity
      exact mul_nonneg h4 h3
    exact mul_nonneg h2 h1
  linarith [hfac, hprod]

/-- Factoring `ξ` out of the denominator. -/
lemma vdc_coef_factor {N Kr k t ξ : ℝ} (hξ : ξ ≠ 0) :
    4*ξ*(48/t)*N*Kr/(ξ*(Kr-k) + (48/t)*Kr)
      = 4*(48/t)*N*Kr/((Kr-k) + (48/t)*Kr/ξ) := by
  field_simp
  try ring

/-- **Φ-half of the interior dual-range sum.**  The harmonic-mean reduction of
`Σ_k x_k·min ((C1+145)/√t) (48 x_k/(t(x_k - N)))` over the strict interior of the dual range. -/
lemma phi_min_sum_bound (C1 : ℝ) (hC1nn : 0 ≤ C1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ), 2 ≤ t →
      ∑ k ∈ ((Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ)))) (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
          (fun k => (N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ))),
          (vdcX t k) * min ((C1+145)/Real.sqrt t) (48*(vdcX t k)/(t*(vdcX t k - (N:ℝ))))
        ≤ C * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) := by
  refine ⟨100*(C1+146) + 10000, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ C1 + 146 := by linarith
    linarith
  · intro N hN t ht
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hN0 : (0:ℝ) < (N:ℝ) := by linarith
    have ht0 : (0:ℝ) < t := by linarith
    have ht1 : (1:ℝ) ≤ t := by linarith
    have hs : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have hC145 : (0:ℝ) < C1 + 145 := by linarith
    have hlogpos : (0:ℝ) < Real.log ((N:ℝ)*t) := Real.log_pos (by nlinarith)
    set Kr : ℝ := t/(2*Real.pi*(N:ℝ)) with hKr
    set Cc : ℝ := 24*Real.sqrt t/(Real.pi*(N:ℝ)*(C1+145)) with hCc
    have hCcpos : (0:ℝ) < Cc := by rw [hCc]; positivity
    have hCcne : Cc ≠ 0 := ne_of_gt hCcpos
    have hKrpos : (0:ℝ) < Kr := by rw [hKr]; positivity
    set A : ℕ := Nat.ceil (t/(4*Real.pi*(N:ℝ))) with hA
    set K : ℕ := Nat.floor (t/(2*Real.pi*(N:ℝ))) with hK
    set S : Finset ℕ := (Finset.Icc A K).filter (fun k => (N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ))
      with hS
    have hKle : (K:ℝ) ≤ Kr := by rw [hK, hKr]; exact Nat.floor_le (by positivity)
    by_cases hSe : S = ∅
    · rw [hSe, Finset.sum_empty]
      refine mul_nonneg (by linarith) ?_
      have h1 : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t := by positivity
      have h2 : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := le_of_lt hlogpos
      linarith
    · obtain ⟨k0, hk0⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
      have hA_le_Kr : (A:ℝ) ≤ Kr := by
        rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk0
        have h1 : (A:ℝ) ≤ (k0:ℝ) := by exact_mod_cast hk0.1.1
        have h2 : (k0:ℝ) ≤ (K:ℝ) := by exact_mod_cast hk0.1.2
        linarith
      have hAK : (A:ℝ) ≤ Kr + Cc := by linarith
      have hCcval : Cc = (48/t)*Kr/((C1+145)/Real.sqrt t) := by
        rw [hCc, hKr]
        field_simp
        try ring_nf
        try (rw [Real.sq_sqrt (le_of_lt ht0)])
        try (rw [Real.sqrt_sq (Real.sqrt_nonneg t)])
        try ring
      have hkey : ∀ k ∈ S, (vdcX t k) * min ((C1+145)/Real.sqrt t)
            (48*(vdcX t k)/(t*(vdcX t k - (N:ℝ))))
          ≤ 4*(48/t)*(N:ℝ)*Kr/((Kr - (k:ℝ)) + Cc) := by
        intro k hk
        rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk
        obtain ⟨⟨hkA, hkK⟩, hkx⟩ := hk
        have hk1 : 1 ≤ k := by
          have hc : 0 < Nat.ceil (t/(4*Real.pi*(N:ℝ))) := by rw [Nat.ceil_pos]; positivity
          omega
        have hk0r : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
        have hxk : 0 < vdcX t k := vdcX_pos ht0 hk1
        have hxu : 0 < vdcX t k - (N:ℝ) := by linarith [hkx.1, hkx.2, hxk]
        have hxKr : vdcX t k = (N:ℝ)*Kr/(k:ℝ) := by rw [vdcX, hKr]; field_simp
        have hkKr : (k:ℝ) ≤ Kr := by
          have h1 : (k:ℝ) ≤ (K:ℝ) := by exact_mod_cast hkK
          linarith
        have h2kKr : Kr ≤ 2*(k:ℝ) := by
          have h1 : (k:ℝ) ≥ (A:ℝ) := by exact_mod_cast hkA
          have h2 : Kr/2 ≤ (A:ℝ) := by
            have h3 : t/(4*Real.pi*(N:ℝ)) = Kr/2 := by rw [hKr]; ring
            rw [hA, h3]
            exact Nat.le_ceil _
          linarith
        have hKk : Kr ≠ (k:ℝ) := by
          intro hcon
          have h1 : (N:ℝ)*(Kr/(k:ℝ)) = vdcX t k := by rw [hxKr]; ring
          have h2 : (N:ℝ)*(1:ℝ) < (N:ℝ)*(Kr/(k:ℝ)) := by
            rw [h1]; simpa using hkx.1
          have h3 : (1:ℝ) < Kr/(k:ℝ) := lt_of_mul_lt_mul_left h2 (le_of_lt hN0)
          have h4 : (1:ℝ) * (k:ℝ) < Kr/(k:ℝ) * (k:ℝ) := mul_lt_mul_of_pos_right h3 hk0r
          rw [div_mul_cancel₀ _ (ne_of_gt hk0r), one_mul] at h4
          linarith
        have hmin := min_le_two_mul_mul_div_add
          (by positivity : (0:ℝ) ≤ (C1+145)/Real.sqrt t)
          (by positivity : (0:ℝ) ≤ 48*(vdcX t k)/(t*(vdcX t k - (N:ℝ))))
        have hstep1 : (vdcX t k) * min ((C1+145)/Real.sqrt t)
              (48*(vdcX t k)/(t*(vdcX t k - (N:ℝ))))
            ≤ (vdcX t k) * (2*(((C1+145)/Real.sqrt t)*(48*(vdcX t k)/(t*(vdcX t k - (N:ℝ)))))/
                (((C1+145)/Real.sqrt t) + 48*(vdcX t k)/(t*(vdcX t k - (N:ℝ))))) :=
          mul_le_mul_of_nonneg_left hmin (le_of_lt hxk)
        have hstep2 : (vdcX t k) * ((2*(((C1+145)/Real.sqrt t)*(48*(vdcX t k)/(t*(vdcX t k - (N:ℝ))))))/
                (((C1+145)/Real.sqrt t) + 48*(vdcX t k)/(t*(vdcX t k - (N:ℝ)))))
            ≤ 4*(48/t)*(N:ℝ)*Kr/((Kr - (k:ℝ)) + Cc) := by
          rw [hxKr]
          calc (N*Kr/k) * ((2*(((C1+145)/Real.sqrt t)*(48*(N*Kr/k)/(t*((N*Kr/k) - (N:ℝ))))))/
                (((C1+145)/Real.sqrt t) + 48*(N*Kr/k)/(t*((N*Kr/k) - (N:ℝ)))))
              = 2*((C1+145)/Real.sqrt t)*(48/t)*N*Kr^2/
                  (k*(((C1+145)/Real.sqrt t)*(Kr-k) + (48/t)*Kr)) :=
                vdc_min_harm_subst hk0r hN0 ht0 (div_pos hC145 hs) hKk
            _ ≤ 4*((C1+145)/Real.sqrt t)*(48/t)*N*Kr/
                  (((C1+145)/Real.sqrt t)*(Kr-k) + (48/t)*Kr) :=
                vdc_min_harm_le hk0r hN0 ht0 (div_pos hC145 hs) hKrpos hkKr h2kKr
            _ = 4*(48/t)*(N:ℝ)*Kr/((Kr - (k:ℝ)) + Cc) := by
                rw [hCcval]
                exact vdc_coef_factor (t := t) (N := (N:ℝ)) (Kr := Kr) (k := (k:ℝ))
                  (ne_of_gt (div_pos hC145 hs))
        exact le_trans hstep1 hstep2
      have hstep : ∑ k ∈ S, (vdcX t k) * min ((C1+145)/Real.sqrt t)
            (48*(vdcX t k)/(t*(vdcX t k - (N:ℝ))))
          ≤ ∑ k ∈ S, 4*(48/t)*(N:ℝ)*Kr/((Kr - (k:ℝ)) + Cc) := Finset.sum_le_sum hkey
      have hsum : ∑ k ∈ S, 1/((Kr + Cc) - (k:ℝ))
          ≤ 1/Cc + Real.log (1 + ((Kr + Cc) - (A:ℝ))/Cc) := by
        refine sum_inv_K_sub_le hCcpos hAK ?_ ?_
        · intro k hk
          rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk
          have h1 : (k:ℝ) ≤ (K:ℝ) := by exact_mod_cast hk.1.2
          linarith
        · intro k hk
          rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk
          exact_mod_cast hk.1.1
      have hcongr : ∑ k ∈ S, 4*(48/t)*(N:ℝ)*Kr/((Kr - (k:ℝ)) + Cc)
          = 4*(48/t)*(N:ℝ)*Kr * ∑ k ∈ S, 1/((Kr + Cc) - (k:ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring_nf
      have hKrCc : Kr/Cc = (C1+145)*Real.sqrt t/48 := by
        rw [hCc, hKr]
        field_simp
        try ring_nf
        try (rw [Real.sq_sqrt (le_of_lt ht0)])
        try (rw [Real.sqrt_sq (Real.sqrt_nonneg t)])
        try ring
      have hlog1 : Real.log (1 + ((Kr + Cc) - (A:ℝ))/Cc)
          ≤ Real.log t + Real.log (C1+147) := by
        have h1 : 1 + ((Kr + Cc) - (A:ℝ))/Cc ≤ (C1+147)*Real.sqrt t := by
          have h2 : ((Kr + Cc) - (A:ℝ))/Cc ≤ (Kr + Cc)/Cc := by
            refine div_le_div_of_nonneg_right ?_ (le_of_lt hCcpos)
            linarith [(Nat.cast_nonneg A : (0:ℝ) ≤ (A:ℝ))]
          have h3 : (Kr + Cc)/Cc = 1 + Kr/Cc := by
            rw [add_div, div_self hCcne]
            exact add_comm _ _
          have h5 : (3:ℝ) + Kr/Cc ≤ (C1+147)*Real.sqrt t := by
            rw [hKrCc]
            have h6 : (1:ℝ) ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1
            have h7 : (0:ℝ) ≤ (C1+145)/48 := by linarith
            nlinarith [h6, h7]
          linarith [h2, h3, h5]
        refine le_trans (Real.log_le_log (by positivity) h1) ?_
        rw [Real.log_mul (by positivity) (by positivity)]
        have h7 : Real.log (Real.sqrt t) ≤ Real.log t := by
          refine Real.log_le_log (by positivity) ?_
          have h8 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht0)
          nlinarith [hs, h8]
        linarith
      have hfin1 : 4*(48/t)*(N:ℝ)*Kr/Cc = 4*(N:ℝ)*(C1+145)/Real.sqrt t := by
        rw [hCc, hKr]
        field_simp
        try ring_nf
        try (rw [Real.sq_sqrt (le_of_lt ht0)])
        try (rw [Real.sqrt_sq (Real.sqrt_nonneg t)])
        try ring
      have hfin3 : 4*(48/t)*(N:ℝ)*Kr = 96/Real.pi := by
        rw [hKr]
        field_simp
        ring
      have hsum2 : ∑ k ∈ S, 4*(48/t)*(N:ℝ)*Kr/((Kr - (k:ℝ)) + Cc)
          ≤ 4*(N:ℝ)*(C1+145)/Real.sqrt t + 96/Real.pi*(Real.log t + Real.log (C1+147)) := by
        refine le_trans (le_of_eq hcongr) ?_
        have h1 := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4*(48/t)*(N:ℝ)*Kr)
        rw [mul_add, mul_one_div, hfin1] at h1
        have h2 : 4*(48/t)*(N:ℝ)*Kr*Real.log (1 + ((Kr + Cc) - (A:ℝ))/Cc)
            ≤ 96/Real.pi*(Real.log t + Real.log (C1+147)) := by
          rw [hfin3]
          exact mul_le_mul_of_nonneg_left hlog1 (by positivity)
        linarith [h1, h2]
      have hA' : 4*(N:ℝ)*(C1+145)/Real.sqrt t
          ≤ (100*(C1+146) + 10000)*((N:ℝ)/Real.sqrt t) := by
        have heq : 4*(N:ℝ)*(C1+145)/Real.sqrt t = (4*(C1+145))*((N:ℝ)/Real.sqrt t) := by ring
        rw [heq]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith
      have hBL : 96/Real.pi*(Real.log t + Real.log (C1+147))
          ≤ (100*(C1+146) + 10000)*(Real.log ((N:ℝ)*t) + 1) := by
        have hlogt : Real.log t ≤ Real.log ((N:ℝ)*t) := by
          refine Real.log_le_log (by linarith) ?_
          nlinarith [hN1]
        have hlogC : Real.log (C1+147) ≤ C1 + 147 := by
          have h9 := Real.log_le_sub_one_of_pos (show (0:ℝ) < C1+147 by linarith)
          linarith
        have hpi3 : Real.pi > 3 := Real.pi_gt_three
        have hLnn : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := le_of_lt hlogpos
        have h96' : 96/Real.pi ≤ 32 := by
          rw [div_le_iff₀ Real.pi_pos]
          linarith
        have h96 : 96/Real.pi ≤ 100*(C1+146) + 10000 := by linarith
        have hC148 : 96/Real.pi*(C1+147) ≤ 100*(C1+146) + 10000 := by
          have h99 : 96/Real.pi*(C1+147) ≤ 32*(C1+147) :=
            mul_le_mul_of_nonneg_right h96' (by linarith)
          linarith
        have ha : 96/Real.pi*Real.log t
            ≤ (100*(C1+146) + 10000)*Real.log ((N:ℝ)*t) :=
          mul_le_mul h96 hlogt (Real.log_nonneg ht1) (by positivity)
        have hb : 96/Real.pi*Real.log (C1+147) ≤ 100*(C1+146) + 10000 :=
          le_trans (mul_le_mul_of_nonneg_left hlogC (by positivity)) hC148
        linarith [ha, hb]
      calc ∑ k ∈ S, (vdcX t k) * min ((C1+145)/Real.sqrt t)
            (48*(vdcX t k)/(t*(vdcX t k - (N:ℝ))))
          ≤ ∑ k ∈ S, 4*(48/t)*(N:ℝ)*Kr/((Kr - (k:ℝ)) + Cc) := hstep
        _ ≤ 4*(N:ℝ)*(C1+145)/Real.sqrt t + 96/Real.pi*(Real.log t + Real.log (C1+147)) := hsum2
        _ ≤ (100*(C1+146) + 10000)*((N:ℝ)/Real.sqrt t)
              + (100*(C1+146) + 10000)*(Real.log ((N:ℝ)*t) + 1) := add_le_add hA' hBL
        _ = (100*(C1+146) + 10000)*((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) := by ring


/-- Harmonic-mean normalisation for the `Ψ`-half (substituting `x = N·K/k`,
so that `2N − x = N(2k−K)/k`). -/
lemma vdc_psi_harm_subst {N Kr k t η : ℝ} (hk : 0 < k) (hN : 0 < N) (ht : 0 < t) (hη : 0 < η)
    (hKr : 0 < Kr) (hk2 : Kr < 2*k) :
    (N*Kr/k) * ((2*(η*(144*(N*Kr/k)/(t*(2*N - N*Kr/k)))))/(η + 144*(N*Kr/k)/(t*(2*N - N*Kr/k))))
      = 2*η*(144/t)*N*Kr^2/(k*(η*(2*k - Kr) + (144/t)*Kr)) := by
  have h2k : 0 < 2*k - Kr := by linarith
  have hv : 2*N - N*Kr/k = N*(2*k - Kr)/k := by field_simp
  have hZ : 144*(N*Kr/k)/(t*(2*N - N*Kr/k)) = 144*Kr/(t*(2*k - Kr)) := by
    rw [hv]
    field_simp
    try ring
  rw [hZ]
  have hDne : t*(2*k - Kr) ≠ 0 := by
    refine mul_ne_zero (ne_of_gt ht) ?_
    linarith
  have h2kne : 2*k - Kr ≠ 0 := ne_of_gt h2k
  have h2kne' : k*2 - Kr ≠ 0 := by
    intro h; exact h2kne (by linarith)
  have hZpos : 0 < 144*Kr/(t*(2*k - Kr)) := by positivity
  have hZne : 144*Kr/(t*(2*k - Kr)) ≠ 0 := ne_of_gt hZpos
  have hsumne : η + 144*Kr/(t*(2*k - Kr)) ≠ 0 := by positivity
  field_simp
  try ring
  try (rw [inv_inj]; field_simp; try ring)

/-- The `1/k ≤ 2/K` reduction for the `Ψ`-half. -/
lemma vdc_psi_harm_le {N Kr k t η : ℝ} (hk : 0 < k) (hN : 0 < N) (ht : 0 < t) (hη : 0 < η)
    (hKr : 0 < Kr) (h2k : Kr ≤ 2*k) :
    2*η*(144/t)*N*Kr^2/(k*(η*(2*k - Kr) + (144/t)*Kr))
      ≤ 4*(144/t)*N*Kr/(2*k - Kr + (144/t)*Kr/η) := by
  have hBpos : (0:ℝ) < 144/t := by positivity
  have hDpos : 0 < η*(2*k - Kr) + (144/t)*Kr := by
    have h1 : 0 ≤ 2*k - Kr := by linarith
    have h3 : 0 ≤ η*(2*k - Kr) := mul_nonneg (le_of_lt hη) h1
    have h2 : 0 < (144/t)*Kr := mul_pos hBpos hKr
    linarith
  have hden1 : 0 < k*(η*(2*k - Kr) + (144/t)*Kr) := mul_pos hk hDpos
  have hmid : 2*η*(144/t)*N*Kr^2/(k*(η*(2*k - Kr) + (144/t)*Kr))
      ≤ 4*η*(144/t)*N*Kr/(η*(2*k - Kr) + (144/t)*Kr) := by
    rw [div_le_div_iff₀ hden1 hDpos]
    have hfac : 4*η*(144/t)*N*Kr*(k*(η*(2*k - Kr) + (144/t)*Kr)) - 2*η*(144/t)*N*Kr^2*(η*(2*k - Kr) + (144/t)*Kr)
        = 2*η*(144/t)*N*Kr*(η*(2*k - Kr) + (144/t)*Kr)*(2*k - Kr) := by ring
    have hprod : 0 ≤ 2*η*(144/t)*N*Kr*(η*(2*k - Kr) + (144/t)*Kr)*(2*k - Kr) := by
      have h1 : 0 ≤ 2*(k:ℝ) - Kr := by linarith
      have h2 : 0 ≤ 2*η*(144/t)*N*Kr*(η*(2*k - Kr) + (144/t)*Kr) := by
        have h3 : 0 ≤ η*(2*k - Kr) + (144/t)*Kr := le_of_lt hDpos
        have h4 : 0 ≤ 2*η*(144/t)*N*Kr := by positivity
        exact mul_nonneg h4 h3
      exact mul_nonneg h2 h1
    linarith [hfac, hprod]
  refine le_trans hmid (le_of_eq ?_)
  have hηne : η ≠ 0 := ne_of_gt hη
  have hden2 : 0 < η*(2*k - Kr) + (144/t)*Kr := hDpos
  have hden3 : 0 < 2*k - Kr + (144/t)*Kr/η := by
    have h1 : 0 ≤ 2*k - Kr := by linarith
    have h2 : 0 < (144/t)*Kr/η := by positivity
    linarith
  field_simp
  try ring

/-- Harmonic bound for a sum reindexed by `2(k−A)`: `Σ_{A≤k≤K} 1/(2(k−A)+c) ≤ 2/c + log(2+2U/c)`. -/
lemma sum_inv_two_mul_le {c U : ℝ} (hc : 0 < c) (hU0 : 0 ≤ U) {A K : ℕ}
    (hU : (K:ℝ) - (A:ℝ) ≤ U) :
    ∑ k ∈ Finset.Icc A K, 1/(2*((k:ℝ) - (A:ℝ)) + c) ≤ 2/c + Real.log (2 + 2*U/c) := by
  have hc2 : 0 < c/2 := by linarith
  let emb : ℕ ↪ ℤ := ⟨fun k => (k:ℤ) - (A:ℤ), by
    intro x y hxy
    change (x:ℤ) - (A:ℤ) = (y:ℤ) - (A:ℤ) at hxy
    have h3 : (x:ℤ) = (y:ℤ) := by omega
    exact_mod_cast h3⟩
  have hemb : ∀ k : ℕ, ((emb k : ℤ) : ℝ) = (k:ℝ) - (A:ℝ) := by
    intro k
    change (((k:ℤ) - (A:ℤ) : ℤ) : ℝ) = (k:ℝ) - (A:ℝ)
    push_cast
    ring
  have key := Commons.Analysis.Harmonic.sum_inv_sub_le (s := (Finset.Icc A K).map emb)
    (x := -(c/2)) (T := c/2) (U := U + c/2) hc2 (by linarith) ?_ ?_
  · rw [Finset.sum_map] at key
    have key2 : ∑ k ∈ Finset.Icc A K, 1/((k:ℝ) - (A:ℝ) + c/2)
        ≤ 1/(c/2) + Real.log (1 + (U + c/2)/(c/2)) := by
      refine le_trans (le_of_eq ?_) key
      exact Finset.sum_congr rfl (fun k _ => by rw [hemb k]; ring_nf)
    have hcongr2 : ∑ k ∈ Finset.Icc A K, 1/(2*((k:ℝ) - (A:ℝ)) + c)
        = (1/2) * ∑ k ∈ Finset.Icc A K, 1/((k:ℝ) - (A:ℝ) + c/2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      field_simp
      try ring
    have h1 : 1/(c/2) = 2/c := by field_simp
    have h2 : 1 + (U + c/2)/(c/2) = 2 + 2*U/c := by
      field_simp
      ring
    calc ∑ k ∈ Finset.Icc A K, 1/(2*((k:ℝ) - (A:ℝ)) + c)
        = (1/2) * ∑ k ∈ Finset.Icc A K, 1/((k:ℝ) - (A:ℝ) + c/2) := hcongr2
      _ ≤ (1/2) * (1/(c/2) + Real.log (1 + (U + c/2)/(c/2))) :=
            mul_le_mul_of_nonneg_left key2 (by norm_num)
      _ = 1/c + (1/2)*Real.log (2 + 2*U/c) := by rw [h1, h2]; ring
      _ ≤ 2/c + Real.log (2 + 2*U/c) := by
          have h3 : (0:ℝ) ≤ Real.log (2 + 2*U/c) := by
            refine Real.log_nonneg ?_
            have h4 : (0:ℝ) ≤ 2*U/c := by positivity
            linarith
          have h8 : 1/c ≤ 2/c := div_le_div_of_nonneg_right (by norm_num) (le_of_lt hc)
          linarith
  · intro l hl
    rw [Finset.mem_map] at hl
    obtain ⟨k, hk, rfl⟩ := hl
    rw [hemb k]
    rw [Finset.mem_Icc] at hk
    have h1 : (A:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
    linarith
  · intro l hl
    rw [Finset.mem_map] at hl
    obtain ⟨k, hk, rfl⟩ := hl
    rw [hemb k]
    rw [Finset.mem_Icc] at hk
    have h1 : (k:ℝ) ≤ (K:ℝ) := by exact_mod_cast hk.2
    linarith


/-- **Ψ-half of the interior dual-range sum**: `Σ_k x_k·min (145/√t) (144 x_k/(t(2N−x_k)))`. -/
lemma psi_min_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ), 2 ≤ t →
      ∑ k ∈ ((Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ)))) (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
          (fun k => (N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ))),
          (vdcX t k) * min (145/Real.sqrt t) (144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k)))
        ≤ C * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro N hN t ht
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hN0 : (0:ℝ) < (N:ℝ) := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have ht1 : (1:ℝ) ≤ t := by linarith
  have hs : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hlogpos : (0:ℝ) < Real.log ((N:ℝ)*t) := Real.log_pos (by nlinarith)
  set Kr : ℝ := t/(2*Real.pi*(N:ℝ)) with hKr
  have hKrpos : (0:ℝ) < Kr := by rw [hKr]; positivity
  set c : ℝ := 144*Kr/(145*Real.sqrt t) with hcdef
  have hcpos : (0:ℝ) < c := by rw [hcdef]; positivity
  set A : ℕ := Nat.ceil (t/(4*Real.pi*(N:ℝ))) with hA
  set K : ℕ := Nat.floor (t/(2*Real.pi*(N:ℝ))) with hK
  set S : Finset ℕ := (Finset.Icc A K).filter (fun k => (N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ))
    with hS
  have hKle : (K:ℝ) ≤ Kr := by rw [hK, hKr]; exact Nat.floor_le (by positivity)
  have hAceil : Kr/2 ≤ (A:ℝ) := by
    have h : t/(4*Real.pi*(N:ℝ)) = Kr/2 := by rw [hKr]; ring
    rw [hA, h]
    exact Nat.le_ceil _
  by_cases hSe : S = ∅
  · rw [hSe, Finset.sum_empty]
    refine mul_nonneg (by norm_num) ?_
    have h1 : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t := by positivity
    have h2 : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := le_of_lt hlogpos
    linarith
  · obtain ⟨k0, hk0⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
    have hA_le_K : (A:ℝ) ≤ (K:ℝ) := by
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk0
      exact_mod_cast hk0.1.1.trans hk0.1.2
    have hkey : ∀ k ∈ S, (vdcX t k) * min (145/Real.sqrt t)
          (144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k)))
        ≤ 4*(144/t)*(N:ℝ)*Kr/(2*(k:ℝ) - Kr + c) := by
      intro k hk
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hkA, hkK⟩, hkx⟩ := hk
      have hk1 : 1 ≤ k := by
        have hc : 0 < Nat.ceil (t/(4*Real.pi*(N:ℝ))) := by rw [Nat.ceil_pos]; positivity
        omega
      have hk0r : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
      have hxk : 0 < vdcX t k := vdcX_pos ht0 hk1
      have hxKr : vdcX t k = (N:ℝ)*Kr/(k:ℝ) := by rw [vdcX, hKr]; field_simp
      have hk2 : Kr < 2*(k:ℝ) := by
        have h1 : (N:ℝ)*(Kr/(k:ℝ)) = vdcX t k := by rw [hxKr]; ring
        have h2 : (N:ℝ)*(Kr/(k:ℝ)) < (N:ℝ)*2 := by
          rw [h1]; simpa [mul_comm] using hkx.2
        have h3 : Kr/(k:ℝ) < 2 := lt_of_mul_lt_mul_left h2 (le_of_lt hN0)
        have h4 : Kr/(k:ℝ) * (k:ℝ) < 2 * (k:ℝ) := mul_lt_mul_of_pos_right h3 hk0r
        rw [div_mul_cancel₀ _ (ne_of_gt hk0r)] at h4
        linarith
      have h2A : Kr ≤ 2*(A:ℝ) := by linarith
      have hzc : 2*(k:ℝ) - Kr + c > 0 := by
        have h1 : 0 ≤ 2*(k:ℝ) - Kr := by linarith
        linarith
      have hfp : 0 ≤ 144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k)) := by
        have : 0 < 2*(N:ℝ) - vdcX t k := by linarith [hkx.2]
        positivity
      have hmin := min_le_two_mul_mul_div_add
        (by positivity : (0:ℝ) ≤ 145/Real.sqrt t) hfp
      have hstep1 : (vdcX t k) * min (145/Real.sqrt t)
            (144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k)))
          ≤ (vdcX t k) * ((2*((145/Real.sqrt t)*(144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k)))))/
              ((145/Real.sqrt t) + 144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k)))) :=
        mul_le_mul_of_nonneg_left hmin (le_of_lt hxk)
      have hstep2 : (vdcX t k) * ((2*((145/Real.sqrt t)*(144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k)))))/
              ((145/Real.sqrt t) + 144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k))))
          ≤ 4*(144/t)*(N:ℝ)*Kr/(2*(k:ℝ) - Kr + c) := by
        rw [hxKr]
        calc (N*Kr/k) * ((2*((145/Real.sqrt t)*(144*(N*Kr/k)/(t*(2*(N:ℝ) - N*Kr/k)))))/
              ((145/Real.sqrt t) + 144*(N*Kr/k)/(t*(2*(N:ℝ) - N*Kr/k))))
            = 2*(145/Real.sqrt t)*(144/t)*N*Kr^2/
                (k*((145/Real.sqrt t)*(2*k - Kr) + (144/t)*Kr)) :=
              vdc_psi_harm_subst hk0r hN0 ht0 (by positivity) hKrpos hk2
          _ ≤ 4*(144/t)*N*Kr/(2*k - Kr + (144/t)*Kr/(145/Real.sqrt t)) :=
              vdc_psi_harm_le hk0r hN0 ht0 (by positivity) hKrpos (le_of_lt hk2)
          _ = 4*(144/t)*(N:ℝ)*Kr/(2*(k:ℝ) - Kr + c) := by
              have hcc : (144/t)*Kr/(145/Real.sqrt t) = c := by
                rw [hcdef]
                field_simp
                try ring_nf
                try (rw [Real.sq_sqrt (le_of_lt ht0)])
                try ring
              rw [hcc]
      exact le_trans hstep1 hstep2
    have hstep : ∑ k ∈ S, (vdcX t k) * min (145/Real.sqrt t)
          (144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k)))
        ≤ ∑ k ∈ S, 4*(144/t)*(N:ℝ)*Kr/(2*(k:ℝ) - Kr + c) := Finset.sum_le_sum hkey
    have hsub : S ⊆ Finset.Icc A K := by
      intro k hk
      rw [hS, Finset.mem_filter] at hk
      exact hk.1
    have hnon : ∀ k ∈ Finset.Icc A K, k ∉ S → 0 ≤ 4*(144/t)*(N:ℝ)*Kr/(2*(k:ℝ) - Kr + c) := by
      intro k hk1 hk2
      rw [Finset.mem_Icc] at hk1
      have h2k : Kr ≤ 2*(k:ℝ) := by
        have h1 : (A:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1.1
        linarith
      have h1 : 0 < 2*(k:ℝ) - Kr + c := by linarith
      positivity
    have hsum1 : ∑ k ∈ S, 1/(2*(k:ℝ) - Kr + c) ≤ ∑ k ∈ Finset.Icc A K, 1/(2*((k:ℝ) - (A:ℝ)) + c) := by
      have h1 : ∑ k ∈ S, 1/(2*(k:ℝ) - Kr + c) ≤ ∑ k ∈ S, 1/(2*((k:ℝ) - (A:ℝ)) + c) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk
        have h1 : (A:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1.1
        have hpos : 0 < 2*((k:ℝ) - (A:ℝ)) + c := by
          have h2 : Kr ≤ 2*(A:ℝ) := by linarith
          linarith
        refine one_div_le_one_div_of_le hpos ?_
        have h2 : Kr ≤ 2*(A:ℝ) := by linarith
        linarith
      refine le_trans h1 ?_
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [hS, Finset.mem_filter] at hk
        exact hk.1
      · intro k hk1 hk2
        have h1 : 2*((k:ℝ) - (A:ℝ)) + c > 0 := by
          rw [Finset.mem_Icc] at hk1
          have h2 : (A:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1.1
          linarith
        positivity
    have hsum2 : ∑ k ∈ Finset.Icc A K, 1/(2*((k:ℝ) - (A:ℝ)) + c)
        ≤ 2/c + Real.log (2 + 2*((K:ℝ) - (A:ℝ))/c) := by
      refine sum_inv_two_mul_le hcpos ?_ (le_refl _)
      linarith
    have hcongr : ∑ k ∈ S, 4*(144/t)*(N:ℝ)*Kr/(2*(k:ℝ) - Kr + c)
        = 4*(144/t)*(N:ℝ)*Kr * ∑ k ∈ S, 1/(2*(k:ℝ) - Kr + c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring_nf
    have hKrA : 2*((K:ℝ) - (A:ℝ))/c ≤ 145*Real.sqrt t/144 := by
      have h1 : (K:ℝ) - (A:ℝ) ≤ Kr/2 := by linarith
      rw [div_le_iff₀ hcpos, hcdef]
      field_simp
      try ring_nf
      have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht0)
      nlinarith [h1, hsq, hs]
    have hlog : Real.log (2 + 2*((K:ℝ) - (A:ℝ))/c) ≤ Real.log t + Real.log 146 := by
      have h1 : 2 + 2*((K:ℝ) - (A:ℝ))/c ≤ 146*Real.sqrt t := by
        have h2 : 2*((K:ℝ) - (A:ℝ))/c ≤ 145*Real.sqrt t/144 := hKrA
        have h3 : (1:ℝ) ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1
        nlinarith [h2, h3]
      have h0 : (0:ℝ) < 2 + 2*((K:ℝ) - (A:ℝ))/c := by positivity
      refine le_trans (Real.log_le_log h0 h1) ?_
      rw [Real.log_mul (by norm_num) (ne_of_gt hs)]
      have h3 : Real.log (Real.sqrt t) ≤ Real.log t := by
        refine Real.log_le_log hs ?_
        have h4 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht0)
        nlinarith [hs, h4]
      linarith
    have hbound : ∑ k ∈ S, 4*(144/t)*(N:ℝ)*Kr/(2*(k:ℝ) - Kr + c)
        ≤ 1160*((N:ℝ)/Real.sqrt t) + (288/Real.pi)*(Real.log t + Real.log 146) := by
      have h1 : ∑ k ∈ S, 1/(2*(k:ℝ) - Kr + c) ≤ 2/c + (Real.log t + Real.log 146) := by
        refine le_trans hsum1 (le_trans hsum2 ?_)
        linarith [hlog]
      have h4 : 4*(144/t)*(N:ℝ)*Kr*(2/c) = 1160*((N:ℝ)/Real.sqrt t) := by
        rw [hcdef, hKr]
        field_simp
        try ring_nf
        try (rw [Real.sq_sqrt (le_of_lt ht0)])
        try ring
      have h5 : 4*(144/t)*(N:ℝ)*Kr = 288/Real.pi := by
        rw [hKr]
        field_simp
        ring
      calc ∑ k ∈ S, 4*(144/t)*(N:ℝ)*Kr/(2*(k:ℝ) - Kr + c)
          = 4*(144/t)*(N:ℝ)*Kr * ∑ k ∈ S, 1/(2*(k:ℝ) - Kr + c) := hcongr
        _ ≤ 4*(144/t)*(N:ℝ)*Kr * (2/c + (Real.log t + Real.log 146)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1160*((N:ℝ)/Real.sqrt t) + (288/Real.pi)*(Real.log t + Real.log 146) := by
            rw [mul_add, h4, h5]
    have hfin1 : 1160*((N:ℝ)/Real.sqrt t) ≤ 100000*((N:ℝ)/Real.sqrt t) := by
      refine mul_le_mul_of_nonneg_right (by norm_num) ?_
      positivity
    have hfin2 : (288/Real.pi)*(Real.log t + Real.log 146)
        ≤ 100000*(Real.log ((N:ℝ)*t) + 1) := by
      have hlogt : Real.log t ≤ Real.log ((N:ℝ)*t) :=
        Real.log_le_log ht0 (by nlinarith [hN1])
      have hlog146 : Real.log 146 ≤ 200 := by
        have h9 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 146)
        linarith
      have h3 : 288/Real.pi ≤ 100 := by
        rw [div_le_iff₀ Real.pi_pos]
        nlinarith [Real.pi_gt_three]
      have hLnn : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := le_of_lt hlogpos
      have h4 : (0:ℝ) ≤ Real.log t + Real.log 146 := by
        have h5 : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht1
        have h52 : (0:ℝ) ≤ Real.log 146 := Real.log_nonneg (by norm_num)
        linarith
      have h6 : (288/Real.pi)*(Real.log t + Real.log 146) ≤ 100*(200 + Real.log ((N:ℝ)*t)) :=
        mul_le_mul h3 (by linarith) h4 (by norm_num)
      have h7 : (100:ℝ)*(200 + Real.log ((N:ℝ)*t)) ≤ 100000*(Real.log ((N:ℝ)*t) + 1) := by
        linarith [hLnn]
      linarith [h6, h7]
    have hexp : (100000:ℝ)*((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1)
        = 100000*((N:ℝ)/Real.sqrt t) + 100000*(Real.log ((N:ℝ)*t) + 1) := by ring
    rw [hexp]
    linarith [hstep, hbound, hfin1, hfin2]



/-- **Interior sum over the dual range** (with the weight parameter `d`):
`Σ_{k∈D}‖vdcI k − x_k^{1+it}F‖ = O(N/√t + log(Nt) + 1)`. -/
lemma dual_interior_sum_bound
    (C1 : ℝ) (hC1nn : 0 ≤ C1) (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℝ), 0 < d → d ≤ 1/2 → ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ), 2 ≤ t →
      ∑ k ∈ Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ)))) (Nat.floor (t/(2*Real.pi*(N:ℝ)))),
          ‖vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t‖
        ≤ C * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) := by
  obtain ⟨Cφ, hCφpos, hCφ⟩ := phi_min_sum_bound C1 hC1nn
  obtain ⟨Cψ, hCψpos, hCψ⟩ := psi_min_sum_bound
  refine ⟨Cφ + Cψ + 4*(C1+290), by linarith, ?_⟩
  intro d hd hd1 N hN t ht
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have ht0 : (0:ℝ) < t := by linarith
  have hlogpos : (0:ℝ) ≤ Real.log ((N:ℝ)*t) :=
    le_of_lt (Real.log_pos (by nlinarith))
  have hsq : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t := by positivity
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
      (Nat.floor (t/(2*Real.pi*(N:ℝ)))))
      (fun k => (N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ))
      (fun k => ‖vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t‖)
  have hA : (∑ k ∈ (Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
        (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
        (fun k => (N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ)),
          ‖vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t‖)
      ≤ (Cφ + Cψ) * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) := by
    have hterm : ∀ k ∈ ((Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
          (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
          (fun k => (N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ))),
        ‖vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t‖
          ≤ (vdcX t k) * min ((C1+145)/Real.sqrt t) (48*(vdcX t k)/(t*(vdcX t k - (N:ℝ))))
            + (vdcX t k) * min (145/Real.sqrt t) (144*(vdcX t k)/(t*(2*(N:ℝ) - vdcX t k))) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hkA, hkK⟩, hkx⟩ := hk
      have hk1 : 1 ≤ k := by
        have hc : 0 < Nat.ceil (t/(4*Real.pi*(N:ℝ))) := by rw [Nat.ceil_pos]; positivity
        omega
      have hxk : 0 < vdcX t k := vdcX_pos ht0 hk1
      have hvdc : vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t
          = (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) *
              ((∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y) - vdcF t) := by
        rw [vdcI_eq_cpow_mul N hd hd1 hN t hk1 ht0]
        ring
      rw [hvdc, norm_mul, norm_cpow_one_add_I_mul hxk t]
      have hdev := vdc_deviation_dual_refined hd hd1 hN t hxk hkx.1 hkx.2 ht C1 hC1
      have hstep := mul_le_mul_of_nonneg_left hdev (le_of_lt hxk)
      rw [mul_add] at hstep
      exact hstep
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib]
    have h1 := hCφ N hN t ht
    have h2 := hCψ N hN t ht
    have h3 : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1 := by linarith
    nlinarith [h1, h2, h3, hCφpos, hCψpos]
  have hB : (∑ k ∈ (Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
        (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
        (fun k => ¬ ((N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ))),
          ‖vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t‖)
      ≤ 4*(C1+290) * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) := by
    have hterm2 : ∀ k ∈ ((Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
          (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
          (fun k => ¬ ((N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ)))),
        ‖vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t‖
          ≤ (vdcX t k) * ‖(∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y) - vdcF t‖ := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hkA, hkK⟩, _⟩ := hk
      have hk1 : 1 ≤ k := by
        have hc : 0 < Nat.ceil (t/(4*Real.pi*(N:ℝ))) := by rw [Nat.ceil_pos]; positivity
        omega
      have hxk : 0 < vdcX t k := vdcX_pos ht0 hk1
      have hvdc : vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t
          = (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) *
              ((∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y) - vdcF t) := by
        rw [vdcI_eq_cpow_mul N hd hd1 hN t hk1 ht0]
        ring
      rw [hvdc, norm_mul, norm_cpow_one_add_I_mul hxk t]
    refine le_trans (Finset.sum_le_sum hterm2) ?_
    have h4 := dual_range_bad_sum_le hd hd1 hN ht C1 hC1nn hC1
    refine le_trans h4 ?_
    have h6 : (0:ℝ) < (C1+290)/Real.sqrt t := by positivity
    have h7 : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t := hsq
    have h8 : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := hlogpos
    have h10 : 4*(N:ℝ)*((C1 + 290)/Real.sqrt t) = 4*(C1+290)*((N:ℝ)/Real.sqrt t) := by ring
    have h11 : 2 * (2*(N:ℝ) * ((C1 + 290)/Real.sqrt t)) = 4*(N:ℝ)*((C1 + 290)/Real.sqrt t) := by
      ring
    rw [h11, h10]
    have h12 : (0:ℝ) ≤ 4*(C1+290)*(Real.log ((N:ℝ)*t) + 1) := by positivity
    nlinarith [h7, h8, h12]
  calc (∑ k ∈ Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ)))) (Nat.floor (t/(2*Real.pi*(N:ℝ)))),
          ‖vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t‖)
      = (∑ k ∈ (Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
            (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
            (fun k => (N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ)),
          ‖vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t‖)
        + (∑ k ∈ (Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
            (Nat.floor (t/(2*Real.pi*(N:ℝ))))).filter
            (fun k => ¬ ((N:ℝ) < vdcX t k ∧ vdcX t k < 2*(N:ℝ))),
          ‖vdcI d N t (k:ℤ) - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t‖)
        := hsplit.symm
    _ ≤ (Cφ + Cψ) * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1)
          + 4*(C1+290) * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) := add_le_add hA hB
    _ = (Cφ + Cψ + 4*(C1+290)) * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) := by ring


/-- **Finset form of `sum_min_div_sq_le`**: the same bound for an arbitrary finite set of
positive integers. -/
lemma sum_min_inv_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {F : Finset ℕ}
    (hF : ∀ j ∈ F, 1 ≤ j) :
    ∑ j ∈ F, min (A/(j:ℝ)) (B/((j:ℝ)^2)) ≤ A * (3 + Real.log (2 + B/A)) := by
  have hsub : F ⊆ Finset.Icc 1 (F.sum id) := by
    intro j hj
    rw [Finset.mem_Icc]
    exact ⟨hF j hj, Finset.single_le_sum (fun i _ => Nat.zero_le i) hj⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _ => le_min (by positivity) (by positivity))) ?_
  exact sum_min_div_sq_le hA hB _

/-- Extended Fresnel window for `Φ` on `[1/8,6]`. -/
lemma norm_vdcPrim_le_window8 (C1 : ℝ)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t)
    {t y : ℝ} (ht : 2 ≤ t) (hy1 : 1/8 ≤ y) (hy2 : y ≤ 6) :
    ‖vdcPrim t y‖ ≤ (C1 + 170)/Real.sqrt t := by
  have ht0 : (0:ℝ) < t := by linarith
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsp2 : Real.sqrt 2 ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rcases le_or_gt (1/4 : ℝ) y with h | h
  · have hw := norm_vdcPrim_le_window C1 hC1 ht h hy2
    refine le_trans hw (div_le_div_of_nonneg_right (by linarith) hs.le)
  · have hsub : vdcPrim t (1/4) - vdcPrim t y = ∫ s in y..(1/4), vdcPhase t s :=
      vdcPrim_sub_eq (t := t) (p := y) (q := (1:ℝ)/4) (by linarith) (by norm_num)
    have hA : ‖vdcPrim t (1/4) - vdcPrim t y‖ ≤ 32/t := by
      rw [hsub]
      have hh := Commons.Analysis.StationaryPhase.log_phase_prim_left_general t y (1/4)
        (by linarith) (by linarith) (le_of_lt h) (by norm_num)
      have hh' : ‖∫ s in y..(1/4), vdcPhase t s‖ ≤
          min ((1:ℝ)/4 - y) (24/(t*(1 - 1/4))) := by
        simpa [vdcPhase] using hh
      refine le_trans (hh'.trans (min_le_right _ _)) (le_of_eq ?_)
      rw [show t*(1 - (1:ℝ)/4) = 3*t/4 by ring]
      rw [show (24:ℝ)/(3*t/4) = 32/t by field_simp; ring]
    have hw : ‖vdcPrim t (1/4)‖ ≤ (C1 + 145)/Real.sqrt t :=
      norm_vdcPrim_le_window C1 hC1 ht le_rfl (by norm_num)
    have h320 : (32:ℝ)/t ≤ 25/Real.sqrt t := by
      rw [div_le_div_iff₀ ht0 hs]
      have h2 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht0)
      have h4 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [hs, h2, hsp2, hs2, h4]
    have heq : vdcPrim t y = vdcPrim t (1/4) - (vdcPrim t (1/4) - vdcPrim t y) := by ring
    rw [heq]
    refine le_trans (norm_sub_le _ _) ?_
    have hfin : (25:ℝ)/Real.sqrt t + (C1 + 145)/Real.sqrt t = (C1 + 170)/Real.sqrt t := by
      rw [← add_div]; ring
    linarith [hA, hw, h320, hfin]

/-- **Wide Fresnel bound**: `(2N+d)/6 ≤ x_k` and `x_k ≤ 8(N−d)` suffice. -/
theorem vdcI_le_fresnel_wide {d : ℝ} {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hd2 : (1:ℝ)/2 < (N:ℝ) - d) (ht : 2 ≤ t) {C1 : ℝ} (hC1nn : 0 ≤ C1)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t)
    {k : ℕ} (hk : 1 ≤ k)
    (hb6 : (2*(N:ℝ)+d)/6 ≤ vdcX t k) (h8a : vdcX t k ≤ 8*((N:ℝ)-d)) :
    ‖vdcI d N t (k:ℤ)‖ ≤ 2 * (C1 + 170) * (vdcX t k) / Real.sqrt t := by
  have ht0 : (0:ℝ) < t := by linarith
  have hspos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hx0 : 0 < vdcX t k := vdcX_pos ht0 hk
  have hK : (0:ℝ) ≤ (C1 + 170)/Real.sqrt t := div_nonneg (by linarith) hspos.le
  set a : ℝ := (N:ℝ) - d with hadef
  set b : ℝ := 2*(N:ℝ) + d with hbdef
  have ha0 : (0:ℝ) < a := by rw [hadef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have hb6' : b ≤ 6 * vdcX t k := by rw [hbdef]; linarith [hb6]
  have h4a' : vdcX t k ≤ 8 * a := by rw [hadef]; exact h8a
  have h1 := vdc_ibp hd hd1 hN (t := t) (x := vdcX t k) hx0
  have h2 := vdc_ibp_subst hd hd1 hN (t := t) (x := vdcX t k) hx0
  have hJeq : (∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y)
      = - ∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k)) := by
    calc (∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y)
        = -vdcX t k * ∫ y : ℝ,
            (((deriv (vw d N)) (vdcX t k * y) : ℝ) : ℂ) * vdcPrim t y := h1
      _ = -(vdcX t k * ∫ y : ℝ,
            (((deriv (vw d N)) (vdcX t k * y) : ℝ) : ℂ) * vdcPrim t y) := by ring
      _ = - ∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k)) := by rw [h2]
  have hcont : Continuous (fun u : ℝ => |deriv (vw d N) u|) :=
    ((vw_contDiff d N).continuous_deriv (by norm_num)).abs
  have hsupp : ∀ u : ℝ, u ∉ Set.Icc a b →
      (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k)) = 0 := by
    intro u hu
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    have hv : deriv (vw d N) u = 0 := by
      rcases hu with h | h
      · refine deriv_vw_zero_of_lt_A hd ?_
        exact h
      · refine deriv_vw_zero_of_gt_B hd ?_
        have h' : b < u := h
        rw [hbdef] at h'
        exact h'
    rw [hv, Complex.ofReal_zero, zero_mul]
  have hpt : ∀ u ∈ Set.Icc a b, ‖vdcPrim t (u/(vdcX t k))‖ ≤ (C1 + 170)/Real.sqrt t := by
    intro u hu
    refine norm_vdcPrim_le_window8 C1 hC1 ht ?_ ?_
    · rw [le_div_iff₀ hx0]
      nlinarith [hu.1, h4a', ha0]
    · rw [div_le_iff₀ hx0]
      linarith [hu.2, hb6']
  have hJbound : ‖∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖
      ≤ 2 * (C1 + 170) / Real.sqrt t := by
    calc ‖∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖
        ≤ ∫ u : ℝ, ‖(((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ u in a..b, ‖(((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖ :=
          integral_eq_intervalIntegral_of_support_real hab
            (fun u hu => by rw [hsupp u hu, norm_zero])
      _ ≤ ∫ u in a..b, |deriv (vw d N) u| * ((C1 + 170)/Real.sqrt t) := by
          refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
          · refine ContinuousOn.intervalIntegrable ?_
            refine ContinuousOn.norm ?_
            refine ContinuousOn.mul ?_ ?_
            · exact Complex.continuous_ofReal.comp_continuousOn
                (((vw_contDiff d N).continuous_deriv (by norm_num)).continuousOn)
            · refine (continuousOn_vdcPrim t).comp (continuous_id.div_const _).continuousOn ?_
              intro u hu
              rw [Set.mem_Ioi]
              rw [Set.uIcc_of_le hab] at hu
              exact div_pos (lt_of_lt_of_le ha0 hu.1) hx0
          · exact (hcont.mul continuous_const).intervalIntegrable _ _
          · intro u hu
            rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]
            exact mul_le_mul_of_nonneg_left (hpt u hu) (abs_nonneg _)
      _ = ((C1 + 170)/Real.sqrt t) * ∫ u in a..b, |deriv (vw d N) u| := by
          rw [intervalIntegral.integral_mul_const, mul_comm]
      _ ≤ ((C1 + 170)/Real.sqrt t) * 2 :=
          mul_le_mul_of_nonneg_left (integral_abs_deriv_vw_support hN hd) hK
      _ = 2 * (C1 + 170) / Real.sqrt t := by ring
  calc ‖vdcI d N t (k:ℤ)‖
      = ‖((vdcX t k : ℝ) : ℂ)^((1:ℂ)+Complex.I*(t:ℂ))
          * (∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y)‖ := by
        rw [vdcI_eq_cpow_mul N hd hd1 hN t hk ht0]
    _ = vdcX t k * ‖∫ y : ℝ, (vw d N (vdcX t k * y) : ℂ) * vdcPhase t y‖ := by
        rw [norm_mul, norm_cpow_one_add_I_mul hx0 t]
    _ = vdcX t k * ‖∫ u : ℝ, (((deriv (vw d N)) u : ℝ) : ℂ) * vdcPrim t (u/(vdcX t k))‖ := by
        rw [hJeq, norm_neg]
    _ ≤ vdcX t k * (2 * (C1 + 170) / Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hJbound (le_of_lt hx0)
    _ = 2 * (C1 + 170) * (vdcX t k) / Real.sqrt t := by ring

/-- **First-order bound for non-positive indices** `k ≤ 0`: the phase `θ_k` is strictly increasing
on the support with `|θ'| ≥ t/(2N+d) + 2π|k|`. -/
theorem vdcI_nonpos_lin {d : ℝ} {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hd2 : (1:ℝ)/2 < (N:ℝ) - d) (ht : 0 < t) {k : ℤ} (hk : k ≤ 0) :
    ‖vdcI d N t k‖ ≤ 8 / (t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|) := by
  set a : ℝ := (N:ℝ) - d with hadef
  set b : ℝ := 2*(N:ℝ) + d with hbdef
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have ha12 : (1:ℝ)/2 < a := by rw [hadef]; exact hd2
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by rw [hbdef]; positivity
  set m : ℝ := t/b + 2*Real.pi*|(k:ℝ)| with hmdef
  have hmpos : 0 < m := by rw [hmdef]; positivity
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc a b →
      (vw d N x : ℂ) * Complex.exp (Complex.I *
        (((t*Real.log x - 2*Real.pi*((k:ℝ))*x : ℝ)) : ℂ)) = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have hv : vw d N x = 0 := by
      rcases hx with h | h
      · refine vw_eq_zero_of_le hd ?_
        have : x < a := h
        rw [hadef] at this; linarith
      · refine vw_eq_zero_of_ge hd ?_
        have : b < x := h
        rw [hbdef] at this; linarith
    rw [hv]; simp
  have hI : vdcI d N t k = ∫ x in a..b,
      ((vw d N x : ℝ) : ℂ) * Complex.exp (Complex.I * ((vdcTheta t (k:ℝ) x : ℝ) : ℂ)) := by
    rw [vdcI]
    rw [integral_eq_intervalIntegral_of_support hab hsupp]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : (1:ℝ)/2 ≤ x := le_of_lt (lt_of_lt_of_le ha12 hx.1)
    rw [vdcTheta_eq hx1]
  rw [hI]
  have hbound : ∀ x ∈ Set.Icc a b, m ≤ |deriv (vdcTheta t (k:ℝ)) x| := by
    intro x hx
    have hx1 : (1:ℝ)/2 < x := lt_of_lt_of_le ha12 hx.1
    have hx0 : 0 < x := by linarith
    rw [deriv_vdcTheta hx1]
    have h1 : t/b ≤ t/x := by
      rw [div_le_div_iff₀ hb0 hx0]
      nlinarith [hx.2, ht]
    have hkabs : ((-(k:ℝ)) = |(k:ℝ)|) := by
      rw [abs_of_nonpos]; exact_mod_cast hk
    have h3 : t / x - 2*Real.pi*(k:ℝ) = t/x + 2*Real.pi*(-(k:ℝ)) := by ring
    rw [h3, hkabs, abs_of_nonneg (by positivity : (0:ℝ) ≤ t/x + 2*Real.pi*|(k:ℝ)|)]
    rw [hmdef]; linarith
  have hmono : MonotoneOn (deriv (vdcTheta t ((k:ℤ):ℝ))) (Set.Icc a b) ∨
      AntitoneOn (deriv (vdcTheta t ((k:ℤ):ℝ))) (Set.Icc a b) :=
    Or.inr ((vdcTheta_antitone (le_of_lt ht) ha12).mono Set.Icc_subset_Ici_self)
  have hgc : ContinuousOn (vw d N) (Set.Icc a b) :=
    (vw_contDiff d N).continuous.continuousOn
  have hgd : ContinuousOn (deriv (vw d N)) (Set.Icc a b) :=
    ((vw_contDiff d N).continuous_deriv (by norm_num)).continuousOn
  have hg : ∀ x ∈ Set.Ioo a b, HasDerivAt (vw d N) (deriv (vw d N) x) x :=
    fun x _ => ((vw_contDiff d N).differentiable (by norm_num) x).hasDerivAt
  have hkey := Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_hasDerivAt_deriv_ge_mono
    hab hmpos (vdcTheta_contDiff t (k:ℝ)) hmono hbound hgc hgd hg
  have hva : |vw d N a| = 0 := by
    rw [hadef]
    rw [show vw d N ((N:ℝ) - d) = 0 from vw_vdcA_eq_zero hd N, abs_zero]
  have hvar : ∫ x in a..b, |deriv (vw d N) x| ≤ 2 := by
    have hcont : Continuous (fun x : ℝ => |deriv (vw d N) x|) :=
      ((vw_contDiff d N).continuous_deriv (by norm_num)).abs
    have hsplit : ∫ x in a..b, |deriv (vw d N) x|
        = (∫ x in a..(N:ℝ), |deriv (vw d N) x|)
          + (∫ x in (N:ℝ)..b, |deriv (vw d N) x|) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable a (N:ℝ)) (hcont.intervalIntegrable (N:ℝ) b)]
    rw [hsplit]
    have hleft : ∫ x in a..(N:ℝ), |deriv (vw d N) x| = 1 := by
      rw [hadef]; exact integral_abs_deriv_vw_left hd hN
    have hright : ∫ x in (N:ℝ)..b, |deriv (vw d N) x| ≤ 1 := by
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (N:ℝ) b →
          |deriv (vw d N) x| = - deriv (vw d N) x := by
        filter_upwards with x hx
        rw [Set.uIoc_of_le (by rw [hbdef]; linarith : (N:ℝ) ≤ b)] at hx
        by_cases h2 : 2*(N:ℝ) ≤ x
        · exact abs_of_nonpos (deriv_vw_nonpos_right hd hN h2)
        · push Not at h2
          have hlt : (N:ℝ) < x := hx.1
          rw [deriv_vw_eq_zero_plateau hd hN hlt h2, abs_zero, neg_zero]
      rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_neg,
        intervalIntegral.integral_deriv_eq_sub (f := vw d N) (a := (N:ℝ)) (b := b)]
      · have hb0' : vw d N b = 0 := by rw [hbdef]; exact vw_eq_zero_of_ge hd le_rfl
        have hN1 : vw d N (N:ℝ) = 1 := vw_eq_one hd le_rfl (by linarith)
        rw [hb0', hN1]; norm_num
      · intro x _
        exact ((vw_contDiff d N).differentiable (by norm_num) x).hasDerivAt.differentiableAt
      · exact ((vw_contDiff d N).continuous_deriv (by norm_num)).intervalIntegrable _ _
    linarith
  calc ‖∫ x in a..b, ((vw d N x : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((vdcTheta t (k:ℝ) x : ℝ) : ℂ))‖
      ≤ 4 * (|vw d N a| + ∫ x in a..b, |deriv (vw d N) x|) / m := hkey
    _ ≤ 4 * (0 + 2) / m := by rw [hva]; gcongr
    _ = 8 / m := by ring


/-! ### The total mass of `|vw''|` -/

/-- The mass of `|smoothTransition''|` on `[0,1]`. -/
noncomputable def vwM2 : ℝ := ∫ y in (0:ℝ)..1, |iteratedDeriv 2 Real.smoothTransition y|

lemma vwM2_nonneg : 0 ≤ vwM2 := by
  rw [vwM2]
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)

lemma continuous_iteratedDeriv2_vw {d : ℝ} (N : ℕ) :
    Continuous (iteratedDeriv 2 (vw d N)) := by
  have h : vw d N = fun x : ℝ => Real.smoothTransition ((x - ((N:ℝ) - d))/d)
      * (1 - Real.smoothTransition ((x - 2*(N:ℝ))/d)) := by
    funext y; rfl
  rw [h]
  fun_prop

/-- Second derivative of an affine rescaling of `smoothTransition` (translation form):
`(d/dx)² st((x−b)/d) = d⁻² st''((x−b)/d)`. -/
lemma iteratedDeriv2_st_affine {d b : ℝ} (hd : d ≠ 0) (x : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.smoothTransition ((x - b)/d)) x
      = (1/d)^2 * iteratedDeriv 2 Real.smoothTransition ((x - b)/d) := by
  have hfun : (fun x : ℝ => Real.smoothTransition ((x - b)/d))
      = (fun z : ℝ => (fun w : ℝ => Real.smoothTransition ((1/d) * w)) (z - b)) := by
    funext y
    congr 1
    ring
  rw [hfun, iteratedDeriv_comp_sub_const 2 (fun w : ℝ => Real.smoothTransition ((1/d) * w)) b]
  rw [iteratedDeriv_comp_const_mul (n := 2) Real.smoothTransition.contDiff (1/d)]
  congr 1
  ring

/-- On `(-∞, 2N]` the weight `vw` coincides with the left transition factor. -/
lemma vw_eq_st_left {d : ℝ} (hd : 0 < d) (N : ℕ) {x : ℝ} (hx : x ≤ 2*(N:ℝ)) :
    vw d N x = Real.smoothTransition ((x - ((N:ℝ) - d))/d) := by
  unfold vw
  have h0 : (x - 2*(N:ℝ))/d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  rw [Real.smoothTransition.zero_of_nonpos h0]
  ring

/-- On `[N, ∞)` the weight `vw` coincides with the right transition factor. -/
lemma vw_eq_st_right {d : ℝ} (hd : 0 < d) (N : ℕ) {x : ℝ} (hx : (N:ℝ) ≤ x) :
    vw d N x = 1 - Real.smoothTransition ((x - 2*(N:ℝ))/d) := by
  unfold vw
  have h1 : (1:ℝ) ≤ (x - ((N:ℝ) - d))/d := by
    rw [le_div_iff₀ hd]; linarith
  rw [Real.smoothTransition.one_of_one_le h1]
  ring

/-- **Total mass of `|vw''|`**: `∫|vw''| ≤ (2M₂+1)/d`. -/
lemma integral_abs_iteratedDeriv2_vw_le {d : ℝ} {N : ℕ} (hN : 1 ≤ N) (hd : 0 < d) :
    ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |iteratedDeriv 2 (vw d N) x|
      ≤ (2*vwM2 + 1)/d := by
  have hdne : d ≠ 0 := ne_of_gt hd
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have h2N : (N:ℝ) ≤ 2*(N:ℝ) := by linarith
  have hNlt : (N:ℝ) < 2*(N:ℝ) := by linarith
  set A : ℝ → ℝ := fun x => Real.smoothTransition ((x - ((N:ℝ) - d))/d) with hA
  set B : ℝ → ℝ := fun x => 1 - Real.smoothTransition ((x - 2*(N:ℝ))/d) with hB
  have hBder : ∀ x : ℝ, iteratedDeriv 2 B x
      = -((1/d)^2 * iteratedDeriv 2 Real.smoothTransition ((x - 2*(N:ℝ))/d)) := by
    intro x
    rw [hB, iteratedDeriv_const_sub (n := 2) (by norm_num) (1:ℝ), iteratedDeriv_neg,
      iteratedDeriv2_st_affine hdne x]
  have hsub1 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |iteratedDeriv 2 (vw d N) x|
      = (∫ x in ((N:ℝ)-d)..(N:ℝ), |iteratedDeriv 2 (vw d N) x|)
        + (∫ x in (N:ℝ)..(2*(N:ℝ)), |iteratedDeriv 2 (vw d N) x|)
        + (∫ x in (2*(N:ℝ))..(2*(N:ℝ)+d), |iteratedDeriv 2 (vw d N) x|) := by
    have hcont : Continuous (fun x : ℝ => |iteratedDeriv 2 (vw d N) x|) :=
      (continuous_iteratedDeriv2_vw (d := d) N).abs
    have hI : ∀ p q : ℝ, IntervalIntegrable (fun x : ℝ => |iteratedDeriv 2 (vw d N) x|)
        volume p q := fun p q => hcont.intervalIntegrable p q
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI ((N:ℝ)-d) (2*(N:ℝ)))
        (hI (2*(N:ℝ)) (2*(N:ℝ)+d)),
      ← intervalIntegral.integral_add_adjacent_intervals (hI ((N:ℝ)-d) (N:ℝ))
        (hI (N:ℝ) (2*(N:ℝ)))]
  rw [hsub1]
  have hfin : (1/d)^2 * (d * vwM2) = vwM2/d := by
    field_simp
  -- left piece
  have hleft : ∫ x in ((N:ℝ)-d)..(N:ℝ), |iteratedDeriv 2 (vw d N) x| ≤ vwM2/d := by
    have hopen : IsOpen (Set.Iio (2*(N:ℝ))) := isOpen_Iio
    have heq : Set.EqOn (vw d N) A (Set.Iio (2*(N:ℝ))) :=
      fun x hx => vw_eq_st_left hd N hx.le
    have hder := heq.iteratedDeriv_of_isOpen hopen 2
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc ((N:ℝ)-d) (N:ℝ) →
        |iteratedDeriv 2 (vw d N) x|
          = (1/d)^2 * |iteratedDeriv 2 Real.smoothTransition ((x - ((N:ℝ)-d))/d)| := by
      apply Filter.Eventually.of_forall
      intro x hx
      rw [Set.uIoc_of_le (by linarith : (N:ℝ)-d ≤ (N:ℝ))] at hx
      have hx2 : x < 2*(N:ℝ) := by linarith [hx.2, hNlt]
      rw [hder (Set.mem_Iio.mpr hx2), hA]
      rw [iteratedDeriv2_st_affine hdne x, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (1/d)^2)]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul]
    have hsub : ∫ x in ((N:ℝ)-d)..(N:ℝ),
        |iteratedDeriv 2 Real.smoothTransition ((x - ((N:ℝ)-d))/d)| = d * vwM2 := by
      have hf : ∀ x ∈ Set.uIcc ((N:ℝ)-d) (N:ℝ),
          HasDerivAt (fun x : ℝ => (x - ((N:ℝ)-d))/d) (1/d) x := by
        intro x _
        have h := (((hasDerivAt_id x).sub_const ((N:ℝ)-d))).div_const d
        simpa using h
      have hg : Continuous (fun y : ℝ => |iteratedDeriv 2 Real.smoothTransition y|) := by
        apply Continuous.abs
        fun_prop
      have key := intervalIntegral.integral_comp_mul_deriv hf continuousOn_const hg
      have h0 : (((N:ℝ) - d) - ((N:ℝ)-d))/d = 0 := by ring
      have h1 : ((N:ℝ) - ((N:ℝ)-d))/d = 1 := by
        rw [div_eq_one_iff_eq hdne]; ring
      rw [h0, h1] at key
      simp only [Function.comp_apply] at key
      rw [intervalIntegral.integral_mul_const] at key
      calc ∫ x in ((N:ℝ)-d)..(N:ℝ),
            |iteratedDeriv 2 Real.smoothTransition ((x - ((N:ℝ)-d))/d)|
          = (∫ x in ((N:ℝ)-d)..(N:ℝ),
              |iteratedDeriv 2 Real.smoothTransition ((x - ((N:ℝ)-d))/d)|) * (1/d) * d := by
              field_simp
              try ring
        _ = (∫ y in (0:ℝ)..1, |iteratedDeriv 2 Real.smoothTransition y|) * d := by rw [key]
        _ = d * vwM2 := by
              have hv : vwM2 = ∫ y in (0:ℝ)..1, |iteratedDeriv 2 Real.smoothTransition y| := rfl
              rw [hv]; ring
    rw [hsub, hfin]
  -- middle piece
  have hmid : ∫ x in (N:ℝ)..(2*(N:ℝ)), |iteratedDeriv 2 (vw d N) x| ≤ 0 := by
    have hopen : IsOpen (Set.Ioi (N:ℝ)) := isOpen_Ioi
    have heq : Set.EqOn (vw d N) B (Set.Ioi (N:ℝ)) := fun x hx => vw_eq_st_right hd N hx.le
    have hder := heq.iteratedDeriv_of_isOpen hopen 2
    have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (2:ℝ)*(N:ℝ) := by
      rw [MeasureTheory.ae_iff]
      simpa using (measure_singleton ((2:ℝ)*(N:ℝ)))
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (N:ℝ) (2*(N:ℝ)) →
        |iteratedDeriv 2 (vw d N) x| = 0 := by
      filter_upwards [hnull] with x hxne hxmem
      rw [Set.uIoc_of_le h2N] at hxmem
      have hx2 : x < 2*(N:ℝ) := lt_of_le_of_ne hxmem.2 hxne
      have hxN : (N:ℝ) < x := hxmem.1
      have hB0 : iteratedDeriv 2 B x = 0 := by
        rw [hBder x]
        have hneg : (x - 2*(N:ℝ))/d < 0 := div_neg_of_neg_of_pos (by linarith) hd
        rw [Commons.Analysis.Calculus.iteratedDeriv_succ_smoothTransition_eq_zero_of_neg 1 hneg]
        ring
      rw [hder (Set.mem_Ioi.mpr hxN), hB0, abs_zero]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_zero]
  -- right piece
  have hright : ∫ x in (2*(N:ℝ))..(2*(N:ℝ)+d), |iteratedDeriv 2 (vw d N) x| ≤ vwM2/d := by
    have hopen : IsOpen (Set.Ioi (N:ℝ)) := isOpen_Ioi
    have heq : Set.EqOn (vw d N) B (Set.Ioi (N:ℝ)) := fun x hx => vw_eq_st_right hd N hx.le
    have hder := heq.iteratedDeriv_of_isOpen hopen 2
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (2*(N:ℝ)) (2*(N:ℝ)+d) →
        |iteratedDeriv 2 (vw d N) x|
          = (1/d)^2 * |iteratedDeriv 2 Real.smoothTransition ((x - 2*(N:ℝ))/d)| := by
      apply Filter.Eventually.of_forall
      intro x hx
      rw [Set.uIoc_of_le (by linarith : 2*(N:ℝ) ≤ 2*(N:ℝ)+d)] at hx
      have hxN : (N:ℝ) < x := by linarith [hx.1, hNlt]
      rw [hder (Set.mem_Ioi.mpr hxN), hBder x, abs_neg, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (1/d)^2)]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul]
    have hsub : ∫ x in (2*(N:ℝ))..(2*(N:ℝ)+d),
        |iteratedDeriv 2 Real.smoothTransition ((x - 2*(N:ℝ))/d)| = d * vwM2 := by
      have hf : ∀ x ∈ Set.uIcc (2*(N:ℝ)) (2*(N:ℝ)+d),
          HasDerivAt (fun x : ℝ => (x - 2*(N:ℝ))/d) (1/d) x := by
        intro x _
        have h := (((hasDerivAt_id x).sub_const (2*(N:ℝ)))).div_const d
        simpa using h
      have hg : Continuous (fun y : ℝ => |iteratedDeriv 2 Real.smoothTransition y|) := by
        apply Continuous.abs
        fun_prop
      have key := intervalIntegral.integral_comp_mul_deriv hf continuousOn_const hg
      have key := intervalIntegral.integral_comp_mul_deriv hf continuousOn_const hg
      have h0 : (2*(N:ℝ) - 2*(N:ℝ))/d = 0 := by ring
      have h1 : (2*(N:ℝ)+d - 2*(N:ℝ))/d = 1 := by
        rw [div_eq_one_iff_eq hdne]; ring
      rw [h0, h1] at key
      simp only [Function.comp_apply] at key
      rw [intervalIntegral.integral_mul_const] at key
      calc ∫ x in (2*(N:ℝ))..(2*(N:ℝ)+d),
            |iteratedDeriv 2 Real.smoothTransition ((x - 2*(N:ℝ))/d)|
          = (∫ x in (2*(N:ℝ))..(2*(N:ℝ)+d),
              |iteratedDeriv 2 Real.smoothTransition ((x - 2*(N:ℝ))/d)|) * (1/d) * d := by
              field_simp
              try ring
        _ = (∫ y in (0:ℝ)..1, |iteratedDeriv 2 Real.smoothTransition y|) * d := by rw [key]
        _ = d * vwM2 := by
              have hv : vwM2 = ∫ y in (0:ℝ)..1, |iteratedDeriv 2 Real.smoothTransition y| := rfl
              rw [hv]; ring
    rw [hsub, hfin]
  have hsum : (∫ x in ((N:ℝ)-d)..(N:ℝ), |iteratedDeriv 2 (vw d N) x|)
      + (∫ x in (N:ℝ)..(2*(N:ℝ)), |iteratedDeriv 2 (vw d N) x|)
      + (∫ x in (2*(N:ℝ))..(2*(N:ℝ)+d), |iteratedDeriv 2 (vw d N) x|)
      ≤ vwM2/d + vwM2/d := by linarith [hleft, hmid, hright]
  refine le_trans hsum ?_
  rw [← add_div, div_le_div_iff₀ hd hd]
  nlinarith [vwM2_nonneg]


/-! ### Reindexing and elementary summation tools -/

/-- `ℕ ≃ {k : ℤ // k ≤ 0}`. -/
def equivNatIicZero : ℕ ≃ {k : ℤ // k ≤ 0} where
  toFun n := ⟨-(n:ℤ), by simp⟩
  invFun k := (-k.1).toNat
  left_inv n := by
    show ((-(-(n:ℤ))).toNat) = n
    simp
  right_inv k := by
    refine Subtype.ext ?_
    show -((((-k.1).toNat : ℤ))) = k.1
    rw [Int.toNat_of_nonneg (by have := k.2; omega : (0:ℤ) ≤ -k.1)]
    exact neg_neg _

/-- `ℕ ≃ {k : ℤ // J ≤ k}`. -/
def equivNatIci (J : ℤ) : ℕ ≃ {k : ℤ // J ≤ k} where
  toFun n := ⟨J + n, by simp⟩
  invFun k := (k.1 - J).toNat
  left_inv n := by
    show ((J + (n:ℤ) - J).toNat) = n
    simp
  right_inv k := by
    refine Subtype.ext ?_
    show J + (((k.1 - J).toNat : ℤ)) = k.1
    rw [Int.toNat_of_nonneg (by have := k.2; omega : (0:ℤ) ≤ k.1 - J)]
    ring_nf

lemma tsum_Iic_zero_eq (f : ℤ → ℝ) :
    ∑' k : {k : ℤ // k ≤ 0}, f k.1 = ∑' n : ℕ, f (-(n:ℤ)) := by
  have h := Equiv.tsum_eq equivNatIicZero (fun k : {k : ℤ // k ≤ 0} => f k.1)
  rw [← h]
  exact tsum_congr (fun n => by simp [equivNatIicZero])

lemma tsum_Ici_eq (J : ℤ) (f : ℤ → ℝ) :
    ∑' k : {k : ℤ // J ≤ k}, f k.1 = ∑' n : ℕ, f (J + n) := by
  have h := Equiv.tsum_eq (equivNatIci J) (fun k : {k : ℤ // J ≤ k} => f k.1)
  rw [← h]
  exact tsum_congr (fun n => by simp [equivNatIci])

/-- Reindexing `Σ_{k∈Icc 1 m} 1/(m+1−k) = Σ_{j∈Icc 1 m} 1/j`. -/
lemma sum_Icc_inv_rev {m : ℕ} :
    ∑ k ∈ Finset.Icc 1 m, (1:ℝ)/((m+1-k : ℕ) : ℝ) = ∑ j ∈ Finset.Icc 1 m, 1/(j:ℝ) := by
  refine Finset.sum_bij (fun k _ => m + 1 - k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro k₁ hk₁ k₂ hk₂ h
    rw [Finset.mem_Icc] at hk₁ hk₂
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨m + 1 - j, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · omega
  · intro k hk
    rfl

/-- The tsum form of the `min`-summation bound. -/
lemma tsum_shift_min_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∑' j : ℕ, min (A/(((j+1 : ℕ):ℝ))) (B/((((j+1 : ℕ):ℝ))^2))
      ≤ A * (3 + Real.log (2 + B/A)) := by
  refine Real.tsum_le_of_sum_le (fun j => le_min (by positivity) (by positivity)) (fun F => ?_)
  have hinj : Set.InjOn (fun j : ℕ => j + 1) (F : Set ℕ) := by
    intro a _ b _ h; simpa using h
  rw [← Finset.sum_image (g := fun j : ℕ => j + 1)
    (f := fun i : ℕ => min (A/(i:ℝ)) (B/((i:ℝ)^2))) hinj]
  refine sum_min_inv_le hA hB (fun i hi => ?_)
  rw [Finset.mem_image] at hi
  obtain ⟨j, _, rfl⟩ := hi
  omega

/-- Mass of `vw` on its support. -/
lemma int_abs_vw_le {d : ℝ} {N : ℕ} (hN : 1 ≤ N) (hd : 0 < d) (hd1 : d ≤ 1/2) :
    ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |vw d N x| ≤ 2*(N:ℝ) := by
  have hab : (N:ℝ) - d ≤ 2*(N:ℝ) + d := by
    have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    linarith
  have hcont : Continuous (fun x : ℝ => |vw d N x|) := (vw_contDiff d N).continuous.abs
  have h1 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |vw d N x| ≤ ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), (1:ℝ) := by
    refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
    · exact hcont.intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
    · intro x _
      exact abs_le.mpr ⟨by linarith [vw_nonneg d N x], vw_le_one d N x⟩
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1
  have h2 : 2*(N:ℝ) + d - ((N:ℝ) - d) = (N:ℝ) + 2*d := by ring
  rw [h2] at h1
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  linarith


/-! ### The complement series bound -/

/-- Second-order constant for the far tails. -/
noncomputable def vdcKc (d : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (2*vwM2+1)/d + 2*(t/((N:ℝ)-d)^2)/(t/(2*(N:ℝ)+d))
    + (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(t/(2*(N:ℝ)+d))
    + (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(t/(2*(N:ℝ)+d))^2

lemma vdcKc_pos {d : ℝ} {N : ℕ} {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N)
    (ht : 0 < t) :
    0 < vdcKc d N t := by
  rw [vdcKc]
  have h1 : 0 < (2*vwM2+1)/d := div_pos (by linarith [vwM2_nonneg]) hd
  have h4 : 0 < (N:ℝ) - d := by
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have h3 : 0 < t/(2*(N:ℝ)+d) := by positivity
  have h2 : 0 ≤ 2*(t/((N:ℝ)-d)^2)/(t/(2*(N:ℝ)+d)) := div_nonneg (by positivity) h3.le
  have h5 : 0 ≤ (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(t/(2*(N:ℝ)+d)) := div_nonneg (by positivity) h3.le
  have h6 : 0 ≤ (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(t/(2*(N:ℝ)+d))^2 :=
    div_nonneg (by positivity) (by positivity)
  linarith

lemma vdcKc_nonneg {d : ℝ} {N : ℕ} {t : ℝ} (hd : 0 < d) (hN : 1 ≤ N) (ht : 0 < t)
    (hd1 : d ≤ 1/2) :
    0 ≤ vdcKc d N t := by
  rw [vdcKc]
  have h1 : (0:ℝ) ≤ (2*vwM2+1)/d := div_nonneg (by linarith [vwM2_nonneg]) hd.le
  have h2 : (0:ℝ) < (N:ℝ) - d := by
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have h3 : (0:ℝ) < t/(2*(N:ℝ)+d) := by positivity
  have h4 : (0:ℝ) ≤ t/((N:ℝ)-d)^2 := by positivity
  have h5 : (0:ℝ) ≤ (t/((N:ℝ)-d)^2)^2 := by positivity
  have h6 : (0:ℝ) ≤ 2*t/((N:ℝ)-d)^3 := by positivity
  have h7 : (0:ℝ) ≤ (2:ℝ)*(N:ℝ) := by positivity
  have h8 : (0:ℝ) ≤ 2*(t/((N:ℝ)-d)^2)/(t/(2*(N:ℝ)+d)) := div_nonneg (by positivity) h3.le
  have h9 : (0:ℝ) ≤ (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(t/(2*(N:ℝ)+d)) :=
    div_nonneg (by positivity) h3.le
  have h10 : (0:ℝ) ≤ (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(t/(2*(N:ℝ)+d))^2 :=
    div_nonneg (by positivity) (by positivity)
  linarith


/-- Pointwise first-order bound for `k ≤ 0` in the form used by the summation. -/
lemma vdcI_nonpos_pt {d : ℝ} {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hd2 : (1:ℝ)/2 < (N:ℝ) - d) (ht : 0 < t) {k : ℤ} (hk : k ≤ 0) :
    ‖vdcI d N t k‖ ≤ 8/(t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|) :=
  vdcI_nonpos_lin hN hd hd1 hd2 ht hk


lemma iteratedDeriv2_vw_eq (d : ℝ) (N : ℕ) :
    iteratedDeriv 2 (vw d N) = deriv (deriv (vw d N)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- Pointwise `min` bound for `k ≤ 0`. -/
lemma vdcI_nonpos_min_pt {d : ℝ} {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 100 ≤ t) (hd : 0 < d)
    (hd1 : d ≤ 1/2) (hd2 : (1:ℝ)/2 < (N:ℝ) - d) :
    ∀ (k : ℤ), k ≤ 0 → ‖vdcI d N t k‖
      ≤ min (8/(t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|))
            (8*vdcKc d N t/(t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|)^2) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hK0 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |vw d N x| ≤ 2*(N:ℝ) :=
    int_abs_vw_le hN hd hd1
  have hK1 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |deriv (vw d N) x| ≤ 2 :=
    integral_abs_deriv_vw_support hN hd
  have hK2 : ∫ x in ((N:ℝ)-d)..(2*(N:ℝ)+d), |deriv (deriv (vw d N)) x|
      ≤ (2*vwM2+1)/d := by
    rw [← iteratedDeriv2_vw_eq]
    exact integral_abs_iteratedDeriv2_vw_le hN hd
  intro k hk
  have hbh : (0:ℝ) < t/(2*(N:ℝ)+d) := by positivity
  have h2pi : (0:ℝ) ≤ 2*Real.pi*|(k:ℝ)| := by positivity
  have hle : t/(2*(N:ℝ)+d) ≤ t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)| := by linarith
  refine le_min ?_ ?_
  · exact vdcI_nonpos_lin hN hd hd1 hd2 ht0 hk
  · have h := vdcI_nonpos hN hd hd1 hd2 ht0 hk hK0 hK1 hK2
    have hmm : (0:ℝ) < t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)| := by linarith
    have hMv : (0:ℝ) ≤ t/((N:ℝ)-d)^2 := by positivity
    have hM3v : (0:ℝ) ≤ 2*t/((N:ℝ)-d)^3 := by positivity
    have hK0p : (0:ℝ) ≤ (2:ℝ)*(N:ℝ) := by positivity
    have hmm2 : (t/(2*(N:ℝ)+d))^2 ≤ (t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|)^2 :=
      pow_le_pow_left₀ hbh.le hle 2
    have hA : 2*(t/((N:ℝ)-d)^2)/(t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|)
        ≤ 2*(t/((N:ℝ)-d)^2)/(t/(2*(N:ℝ)+d)) := by
      rw [div_le_div_iff₀ hmm hbh]
      linarith [mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ 2*(t/((N:ℝ)-d)^2))]
    have hB : (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|)
        ≤ (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(t/(2*(N:ℝ)+d)) := by
      rw [div_le_div_iff₀ hmm hbh]
      linarith [mul_le_mul_of_nonneg_left hle
        (by positivity : (0:ℝ) ≤ (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3))]
    have hC : (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(t/(2*(N:ℝ)+d) + 2*Real.pi*|(k:ℝ)|)^2
        ≤ (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(t/(2*(N:ℝ)+d))^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [mul_le_mul_of_nonneg_left hmm2
        (by positivity : (0:ℝ) ≤ (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2)]
    refine le_trans h ?_
    rw [vdcKc]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    linarith [hA, hB, hC]

/-- **Finset bound for the `k ≤ 0` part of the complement.** -/
lemma finset_nonpos_le {d : ℝ} {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 100 ≤ t) (hd : 0 < d)
    (hd1 : d ≤ 1/2) (hd2 : (1:ℝ)/2 < (N:ℝ) - d)
    {F : Finset ℤ} (hF : ∀ k ∈ F, k ≤ 0) :
    ∑ k ∈ F, ‖vdcI d N t k‖
      ≤ 20*(N:ℝ)/t + (4/Real.pi)*(3 + Real.log (2 + vdcKc d N t/(2*Real.pi))) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hKc0 : 0 ≤ vdcKc d N t := vdcKc_nonneg hd hN ht0 hd1
  have hbh : (0:ℝ) < t/(2*(N:ℝ)+d) := by positivity
  have hpt := vdcI_nonpos_min_pt hN ht hd hd1 hd2
  set G : ℕ → ℝ := fun i => min (8/(t/(2*(N:ℝ)+d) + 2*Real.pi*(i:ℝ)))
      (8*vdcKc d N t/(t/(2*(N:ℝ)+d) + 2*Real.pi*(i:ℝ))^2) with hG
  have hstep1 : ∑ k ∈ F, ‖vdcI d N t k‖ ≤ ∑ k ∈ F, G ((-k).toNat) := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hk0 := hF k hk
    have hcast : (((-k).toNat : ℕ) : ℝ) = (-(k:ℝ)) := by
      have h1 : (((-k).toNat : ℤ)) = -k := Int.toNat_of_nonneg (by omega)
      calc (((-k).toNat : ℕ) : ℝ) = (((-k).toNat : ℤ) : ℝ) := by push_cast; ring
        _ = ((-k : ℤ) : ℝ) := by rw [h1]
        _ = -(k:ℝ) := by push_cast; ring
    have habs : |(k:ℝ)| = (-(k:ℝ)) := abs_of_nonpos (by exact_mod_cast hk0)
    rw [hG]
    simp only
    rw [hcast]
    have hh := hpt k hk0
    rw [habs] at hh
    exact hh
  have hinj : Set.InjOn (fun k : ℤ => (-k).toNat) (F : Set ℤ) := by
    intro a ha b hb h
    have h1 : (((-a).toNat : ℤ)) = (((-b).toNat : ℤ)) := by exact_mod_cast h
    rw [Int.toNat_of_nonneg (by have := hF a ha; omega : (0:ℤ) ≤ -a),
      Int.toNat_of_nonneg (by have := hF b hb; omega : (0:ℤ) ≤ -b)] at h1
    omega
  have hstep2 : ∑ k ∈ F, G ((-k).toNat) = ∑ i ∈ F.image (fun k : ℤ => (-k).toNat), G i :=
    (Finset.sum_image (f := G) (g := fun k : ℤ => (-k).toNat) hinj).symm
  rw [hstep2] at hstep1
  set F' : Finset ℕ := F.image (fun k : ℤ => (-k).toNat) with hF'
  have hsplit := Finset.sum_filter_add_sum_filter_not F' (fun i => i = 0) G
  have hzero : ∑ i ∈ F'.filter (fun i => i = 0), G i ≤ 20*(N:ℝ)/t := by
    have hsub : F'.filter (fun i => i = 0) ⊆ ({0} : Finset ℕ) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      simp [hi.2]
    have hle : ∑ i ∈ F'.filter (fun i => i = 0), G i ≤ ∑ i ∈ ({0} : Finset ℕ), G i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => le_min (by positivity) (by positivity))
    refine le_trans hle ?_
    simp only [Finset.sum_singleton]
    rw [hG]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    refine le_trans (min_le_left _ _) ?_
    have heq : 8/(t/(2*(N:ℝ)+d)) = 8*(2*(N:ℝ)+d)/t := by field_simp
    rw [heq, div_le_div_iff₀ ht0 ht0]
    have hbv : 2*(N:ℝ)+d ≤ 5*(N:ℝ)/2 := by linarith
    nlinarith [hbv, hN1]
  have hpos : ∑ i ∈ F'.filter (fun i => ¬ i = 0), G i
      ≤ (4/Real.pi)*(3 + Real.log (2 + vdcKc d N t/(2*Real.pi))) := by
    have hsub : F'.filter (fun i => ¬ i = 0) ⊆ Finset.Icc 1 (F'.sum id) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_Icc]
      refine ⟨by omega, Finset.single_le_sum (fun j _ => Nat.zero_le j) hi.1⟩
    have h1 : ∑ i ∈ F'.filter (fun i => ¬ i = 0), G i
        ≤ ∑ i ∈ F'.filter (fun i => ¬ i = 0),
            min (4/Real.pi/(i:ℝ)) (2*vdcKc d N t/Real.pi^2/((i:ℝ)^2)) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      rw [Finset.mem_filter] at hi
      have hi1 : 1 ≤ i := by omega
      have hip : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi1
      rw [hG]
      simp only
      refine le_min ?_ ?_
      · refine le_trans (min_le_left _ _) ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : (4/Real.pi)*(2*Real.pi*(i:ℝ)) = 8*(i:ℝ) := by field_simp; ring
        have h2 : (0:ℝ) ≤ (4/Real.pi)*(t/(2*(N:ℝ)+d)) := by positivity
        rw [mul_add]
        linarith [h1, h2]
      · refine le_trans (min_le_right _ _) ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hmm : (0:ℝ) < t/(2*(N:ℝ)+d) + 2*Real.pi*(i:ℝ) := by positivity
        have hsq : (2*Real.pi*(i:ℝ))^2 ≤ (t/(2*(N:ℝ)+d) + 2*Real.pi*(i:ℝ))^2 := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [hbh.le]
        have h1 : (2*vdcKc d N t/Real.pi^2)*(2*Real.pi*(i:ℝ))^2 = 8*vdcKc d N t*(i:ℝ)^2 := by
          field_simp
          ring
        have h2 : (0:ℝ) ≤ 2*vdcKc d N t/Real.pi^2 := by positivity
        linarith [mul_le_mul_of_nonneg_left hsq h2]
    refine le_trans h1 ?_
    have h2 : ∑ i ∈ F'.filter (fun i => ¬ i = 0),
        min (4/Real.pi/(i:ℝ)) (2*vdcKc d N t/Real.pi^2/((i:ℝ)^2))
        ≤ ∑ i ∈ Finset.Icc 1 (F'.sum id),
            min (4/Real.pi/(i:ℝ)) (2*vdcKc d N t/Real.pi^2/((i:ℝ)^2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => le_min (by positivity) (by positivity))
    refine le_trans h2 (le_trans (sum_min_inv_le (A := 4/Real.pi) (B := 2*vdcKc d N t/Real.pi^2)
      (by positivity) (by have := vdcKc_pos hd hd1 hN ht0; positivity)
      (fun i hi => (Finset.mem_Icc.mp hi).1)) ?_)
    have hBA : (2*vdcKc d N t/Real.pi^2)/(4/Real.pi) = vdcKc d N t/(2*Real.pi) := by
      field_simp
      ring
    rw [hBA]
  linarith [hsplit, hzero, hpos]


/-- The second-order constant for the far-left tail. -/
noncomputable def vdcKcf (d : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (2*vwM2+1)/d + (t/((N:ℝ)-d)^2)/Real.pi
    + (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(2*Real.pi)
    + (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(2*Real.pi)^2

lemma vdcKcf_nonneg {d : ℝ} {N : ℕ} {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N)
    (ht : 0 < t) :
    0 ≤ vdcKcf d N t := by
  have h4 : 0 < (N:ℝ) - d := by
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  rw [vdcKcf]
  have h1 : 0 ≤ (2*vwM2+1)/d := div_nonneg (by linarith [vwM2_nonneg]) hd.le
  have h2 : 0 < t/((N:ℝ)-d)^2 := by positivity
  have h3 : 0 < 2*(N:ℝ) := by positivity
  have h5 : 0 < 2*Real.pi := by positivity
  have h6 : 0 < (2*Real.pi)^2 := by positivity
  positivity


set_option maxHeartbeats 6400000

/-! ## Left-tail and right-strip sums for the complement series (session 8) -/

/-- Strict positivity of the far-left constant `vdcKcf`. -/
lemma vdcKcf_pos {d : ℝ} {N : ℕ} {t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2) (hN : 1 ≤ N)
    (ht : 0 < t) : 0 < vdcKcf d N t := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have h4 : 0 < (N:ℝ) - d := by linarith
  have h1 : 0 ≤ vwM2 := vwM2_nonneg
  rw [vdcKcf]
  have h5 : 0 < 2*(N:ℝ) := by positivity
  have h6 : 0 < 2*Real.pi := by positivity
  have h7 : 0 < (2*Real.pi)^2 := by positivity
  have h8 : 0 < t/((N:ℝ)-d)^2 := by positivity
  have h9 : 0 < 2*t/((N:ℝ)-d)^3 := by positivity
  have h10 : 0 < (t/((N:ℝ)-d)^2)^2 := by positivity
  positivity

lemma vdcIntToNatCast (j : ℤ) (h : 0 ≤ j) : (((j.toNat : ℕ)) : ℝ) = (j:ℝ) := by
  have h1 : (((j.toNat : ℕ)) : ℤ) = j := Int.toNat_of_nonneg h
  exact_mod_cast congrArg (fun z : ℤ => (z:ℝ)) h1

/-- **Finset bound for the far-right part of the complement** `1 ≤ k < A`. -/

lemma finset_right_le {d : ℝ} {N : ℕ} {t : ℝ} {C1 : ℝ} {A : ℕ} (hN : 1 ≤ N) (ht : 100 ≤ t)
    (hd : 0 < d) (hd1 : d ≤ 1/2) (hd0 : d ≤ 1/4) (hd2 : (1:ℝ)/2 < (N:ℝ) - d)
    (htd : t*d ≤ (N:ℝ)^2/32)
    (hC1nn : 0 ≤ C1)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t)
    (hA2 : (A:ℝ) ≤ t/(4*Real.pi*(N:ℝ)) + 1)
    (hA3 : (A:ℝ) - 1 < t/(4*Real.pi*(N:ℝ)))
    {F : Finset ℤ} (hF : ∀ k ∈ F, 1 ≤ k ∧ k < (A:ℤ)) :
    ∑ k ∈ F, ‖vdcI d N t k‖ ≤ 100*(C1+170)*(N:ℝ)/Real.sqrt t
      + (4/Real.pi)*(1 + Real.log (2 + t/(2*Real.pi*(2*(N:ℝ)+d)))) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hsp : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hbv0 : (0:ℝ) < 2*(N:ℝ)+d := by positivity
  have hav0 : (0:ℝ) < (N:ℝ)-d := by linarith
  have hK2r0 : (0:ℝ) < t/(2*Real.pi*(2*(N:ℝ)+d)) := by positivity
  set K2r : ℝ := t/(2*Real.pi*(2*(N:ℝ)+d)) with hK2r
  set m2 : ℕ := Nat.floor K2r with hm2
  have hm2le : (m2:ℝ) ≤ K2r := by rw [hm2]; exact Nat.floor_le hK2r0.le
  have hm2lt : K2r < (m2:ℝ) + 1 := by rw [hm2]; exact Nat.lt_floor_add_one K2r
  have hAm : (A:ℝ) - (m2:ℝ) < 3 := by
    have h1 : t/(4*Real.pi*(N:ℝ)) - K2r ≤ 1/(256*Real.pi) := by
      rw [hK2r]
      have hkey : t/(4*Real.pi*(N:ℝ)) - t/(2*Real.pi*(2*(N:ℝ)+d))
          = t*d/(4*Real.pi*(N:ℝ)*(2*(N:ℝ)+d)) := by field_simp; ring
      rw [hkey, div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 := mul_le_mul_of_nonneg_left htd (by positivity : (0:ℝ) ≤ 256*Real.pi)
      have h3 : (256*Real.pi)*(((N:ℝ)^2)/32) ≤ (4*Real.pi*(N:ℝ))*(2*(N:ℝ)) := by
        nlinarith [Real.pi_pos, hN1]
      have h4 : (4*Real.pi*(N:ℝ))*(2*(N:ℝ)) ≤ (4*Real.pi*(N:ℝ))*(2*(N:ℝ)+d) := by
        have h0 : (0:ℝ) ≤ 4*Real.pi*(N:ℝ) := by positivity
        have h1 : (0:ℝ) ≤ d := hd.le
        nlinarith [mul_nonneg h0 h1, h0, h1, Real.pi_pos, hN1]
      have h5 : (t*d)*(256*Real.pi) = (256*Real.pi)*(t*d) := by ring
      have h6 : 1*(4*Real.pi*(N:ℝ)*(2*(N:ℝ)+d)) = (4*Real.pi*(N:ℝ))*(2*(N:ℝ)+d) := by ring
      rw [h5, h6]
      linarith [h2, h3, h4]
    have hp1 : (1:ℝ)/(256*Real.pi) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    linarith [hA2, h1, hm2le, hm2lt, hp1]
  have hxk : ∀ k ∈ F, (2:ℝ)*(N:ℝ) < vdcX t k.toNat := by
    intro k hk
    obtain ⟨hk1, hkA⟩ := hF k hk
    have hk1' : 1 ≤ k.toNat := by omega
    have hkcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
    have hkc : (k:ℝ) = ((k.toNat : ℕ) : ℝ) := by exact_mod_cast hkcast.symm
    have hklt : (k.toNat : ℝ) < t/(4*Real.pi*(N:ℝ)) := by
      have h1 : (k:ℝ) ≤ (A:ℝ) - 1 := by
        have h : (k:ℤ) ≤ (A:ℤ) - 1 := by omega
        exact_mod_cast h
      rw [hkc] at h1
      linarith [hA3]
    rw [vdcX]
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*((k.toNat:ℕ):ℝ))]
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4*Real.pi*(N:ℝ))] at hklt
    nlinarith [hklt, Real.pi_pos, hN1]
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun k => k ≤ (m2:ℤ) - 1)
    (fun k => ‖vdcI d N t k‖)
  -- harmonic part
  have hharm : ∑ k ∈ F.filter (fun k => k ≤ (m2:ℤ) - 1), ‖vdcI d N t k‖
      ≤ (4/Real.pi)*(1 + Real.log (2 + K2r)) := by
    have hpt : ∀ k ∈ F.filter (fun k => k ≤ (m2:ℤ) - 1),
        ‖vdcI d N t k‖ ≤ (4/Real.pi)/((m2:ℝ) - (k:ℝ)) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨hkF, hkle⟩ := hk
      have hk1 : 1 ≤ k.toNat := by have := (hF k hkF).1; omega
      have hkcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
      have hkR : (k:ℝ) ≤ (m2:ℝ) - 1 := by
        have h : (k:ℝ) ≤ ((m2:ℤ):ℝ) - 1 := by exact_mod_cast hkle
        push_cast at h
        linarith
      have hkK2 : (k:ℝ) < K2r := by linarith [hkR, hm2le]
      have hcastk : ((k.toNat:ℕ):ℝ) = (k:ℝ) := by
        have h : ((k.toNat:ℕ):ℤ) = k := hkcast
        exact_mod_cast congrArg (fun z : ℤ => (z:ℝ)) h
      have hfar := vdcI_far_right hN hd hd1 hd2 ht0 (k := k.toNat) hk1 (by
        rw [vdcX, lt_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*((k.toNat:ℕ):ℝ))]
        rw [hcastk]
        have hK2 : (k:ℝ) < K2r := hkK2
        have hK2t : K2r*(2*Real.pi*(2*(N:ℝ)+d)) = t := by rw [hK2r]; field_simp
        have hpos : (0:ℝ) < 2*Real.pi*(2*(N:ℝ)+d) := by positivity
        nlinarith [hK2, hK2t, hpos, hbv0, Real.pi_pos])
      rw [hkcast, hcastk] at hfar
      refine le_trans hfar ?_
      have hkey : t/(2*(N:ℝ)+d) - 2*Real.pi*(k:ℝ) = 2*Real.pi*(K2r - (k:ℝ)) := by
        rw [hK2r]; field_simp; try ring
      rw [hkey]
      have hden1 : (0:ℝ) < 2*Real.pi*(K2r - (k:ℝ)) := by
        have : (0:ℝ) < K2r - (k:ℝ) := by linarith
        positivity
      have hden2 : (0:ℝ) < ((m2:ℝ)-(k:ℝ)) := by
        have hkl : ((k:ℝ)) ≤ (m2:ℝ) - 1 := by
          have h : ((k:ℤ)) ≤ ((m2:ℤ)) - 1 := hkle
          have h' : ((k:ℤ):ℝ) ≤ (((m2:ℤ)):ℝ) - 1 := by exact_mod_cast h
          push_cast at h'
          linarith
        linarith
      rw [div_le_div_iff₀ hden1 hden2]
      have hpi : (0:ℝ) < Real.pi := Real.pi_pos
      have hid : (4/Real.pi)*(2*Real.pi*(K2r - (k:ℝ))) = 8*(K2r - (k:ℝ)) := by
        field_simp
        try ring
      nlinarith [hm2le, hid, hpi]
    calc ∑ k ∈ F.filter (fun k => k ≤ (m2:ℤ) - 1), ‖vdcI d N t k‖
        ≤ ∑ k ∈ F.filter (fun k => k ≤ (m2:ℤ) - 1), (4/Real.pi)/((m2:ℝ) - (k:ℝ)) :=
          Finset.sum_le_sum hpt
      _ = ∑ j ∈ (F.filter (fun k => k ≤ (m2:ℤ) - 1)).image (fun k => ((m2:ℤ) - k : ℤ)),
            (4/Real.pi)/(j:ℝ) := by
          rw [Finset.sum_image]
          · refine Finset.sum_congr rfl (fun k hk => ?_)
            rw [Finset.mem_filter] at hk
            have h : (((m2:ℤ) - k : ℤ) : ℝ) = (m2:ℝ) - (k:ℝ) := by push_cast; ring
            rw [h]
          · intro a _ b _ h; linarith [h]
      _ = (4/Real.pi) * ∑ j ∈ (F.filter (fun k => k ≤ (m2:ℤ) - 1)).image
              (fun k => ((m2:ℤ) - k : ℤ)), (1:ℝ)/(j:ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ (4/Real.pi) * ∑ j ∈ Finset.Icc (1:ℤ) (m2:ℤ), (1:ℝ)/(j:ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun j hj _ => by
              rw [one_div]
              exact inv_nonneg.mpr (by
                have h := (Finset.mem_Icc.mp hj).1
                exact_mod_cast (by omega : (0:ℤ) ≤ j)))
          intro j hj
          rw [Finset.mem_image] at hj
          obtain ⟨k, hk, rfl⟩ := hj
          rw [Finset.mem_filter] at hk
          rw [Finset.mem_Icc]
          exact ⟨by omega, by have := (hF k hk.1).1; omega⟩
      _ = (4/Real.pi) * ∑ n ∈ Finset.Icc 1 m2, (1:ℝ)/(n:ℝ) := by
          congr 1
          refine Finset.sum_bij (fun j _ => j.toNat) ?_ ?_ ?_ ?_
          · intro j hj
            rw [Finset.mem_Icc] at hj ⊢
            omega
          · intro j1 h1 j2 h2 hh
            rw [Finset.mem_Icc] at h1 h2
            omega
          · intro n hn
            rw [Finset.mem_Icc] at hn
            refine ⟨(n:ℤ), ?_, ?_⟩
            · rw [Finset.mem_Icc]; omega
            · exact Int.toNat_natCast n
          · intro j hj
            rw [Finset.mem_Icc] at hj
            rw [vdcIntToNatCast j (by omega)]
      _ ≤ (4/Real.pi) * (1 + Real.log (2 + K2r)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rcases Nat.eq_zero_or_pos m2 with h0 | h0
          · have hempty : Finset.Icc 1 m2 = ∅ := by rw [h0]; simp
            rw [hempty, Finset.sum_empty]
            have : (0:ℝ) ≤ Real.log (2 + K2r) := Real.log_nonneg (by linarith [hK2r0])
            linarith
          · have h1 := sum_Icc_inv_le (a := 1) (b := m2) le_rfl h0
            have h2 : (1:ℝ)/(1:ℝ) + Real.log (1 + (m2:ℝ)/(1:ℝ)) ≤ 1 + Real.log (2 + K2r) := by
              rw [one_div, div_one]
              have h3 : (1:ℝ) + (m2:ℝ) ≤ 2 + K2r := by linarith [hm2le]
              have h4 : Real.log (1 + (m2:ℝ)) ≤ Real.log (2 + K2r) :=
                Real.log_le_log (by positivity) h3
              linarith
            linarith [h1, h2]
  -- Fresnel part
  have hfres : ∑ k ∈ F.filter (fun k => ¬ k ≤ (m2:ℤ) - 1), ‖vdcI d N t k‖
      ≤ 100*(C1+170)*(N:ℝ)/Real.sqrt t := by
    have hcard : (F.filter (fun k => ¬ k ≤ (m2:ℤ) - 1)).card ≤ 2 := by
      have hsub : F.filter (fun k => ¬ k ≤ (m2:ℤ) - 1) ⊆ Finset.Icc (m2:ℤ) ((A:ℤ) - 1) := by
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [Finset.mem_Icc]
        exact ⟨by omega, by have := (hF k hk.1).2; omega⟩
      refine le_trans (Finset.card_le_card hsub) ?_
      rw [Int.card_Icc]
      have h1 : ((A:ℤ) - 1 + 1 - (m2:ℤ)) = ((A:ℤ) - (m2:ℤ)) := by ring
      rw [h1]
      have h3 : ((A:ℤ) - (m2:ℤ) : ℝ) < 3 := by push_cast; exact hAm
      have h4 : (A:ℤ) - (m2:ℤ) < 3 := by exact_mod_cast h3
      have h5 : ((A:ℤ) - (m2:ℤ)).toNat ≤ 2 := by omega
      exact h5
    have hpt : ∀ k ∈ F.filter (fun k => ¬ k ≤ (m2:ℤ) - 1),
        ‖vdcI d N t k‖ ≤ 2*(C1+170)*(8*((N:ℝ)-d))/Real.sqrt t := by
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨hkF, hkle⟩ := hk
      have hk1 : 1 ≤ k.toNat := by have := (hF k hkF).1; omega
      have hkcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
      have hkR : (m2:ℝ) ≤ (k:ℝ) := by
        have h : ((m2:ℤ):ℝ) ≤ (k:ℝ) := by
          have : (m2:ℤ) ≤ k := by omega
          exact_mod_cast this
        push_cast at h
        linarith
      have hkv : vdcI d N t k = vdcI d N t (k.toNat : ℤ) := by rw [hkcast]
      rw [hkv]
      have hb6v : (2*(N:ℝ)+d)/6 ≤ vdcX t k.toNat := by

        rw [vdcX]
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*((k.toNat:ℕ):ℝ))]
        have hx := hxk k hkF
        rw [vdcX] at hx
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*((k.toNat:ℕ):ℝ))] at hx
        have hb : (0:ℝ) < 2*(N:ℝ)+d := hbv0
        have hpi : (0:ℝ) < Real.pi := Real.pi_pos
        nlinarith [hx, hb, hpi]
      -- NOTE (WIP): `x_{k.toNat} ≤ 8(N−d)`.  Proof sketch: with `K2r = t/(2π(2N+d))`,
      -- `x = t/(2πk) = (2N+d)·K2r/k`, `k ≥ max(⌊K2r⌋,1)`.  If `⌊K2r⌋ = 0` then `K2r < 1`
      -- and `x < 2N+d`; if `⌊K2r⌋ ≥ 1` then `x < (2N+d)(⌊K2r⌋+1)/⌊K2r⌋ ≤ 2(2N+d)`.
      -- In both cases `x < 2(2N+d) ≤ 8(N−d)` (using `d ≤ 1/4`, `N ≥ 1`).
      have hx8 : vdcX t k.toNat ≤ 8*((N:ℝ)-d) := by
        have hcastk : ((k.toNat:ℕ):ℝ) = (k:ℝ) := vdcIntToNatCast k (by omega)
        have hK2t : K2r*(2*Real.pi*(2*(N:ℝ)+d)) = t := by rw [hK2r]; field_simp
        have hbv4 : 2*(N:ℝ)+d ≤ 8*((N:ℝ)-d) := by linarith [hN1, hd0]
        have hk1R : (1:ℝ) ≤ (k:ℝ) := by
          rw [← hcastk]
          exact_mod_cast hk1
        rw [vdcX, div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*((k.toNat:ℕ):ℝ)), hcastk]
        have h3 : (0:ℝ) < 2*Real.pi*(k:ℝ) := mul_pos (by positivity) (by linarith [hk1R])
        have hkm : ((m2:ℕ):ℝ) ≤ (k:ℝ) := hkR
        by_cases hm2 : m2 = 0
        · have hK21 : K2r < 1 := by
            have h := hm2lt
            rw [hm2] at h
            push_cast at h
            linarith
          have hxbd : t/(2*Real.pi*(k:ℝ)) < (2*(N:ℝ)+d) := by
            rw [div_lt_iff₀ h3]
            nlinarith [hK2t, hK21, hk1R, hbv0, Real.pi_pos]
          have : t ≤ 2*Real.pi*(k:ℝ)*(2*(N:ℝ)+d) := by
            rw [div_lt_iff₀ h3] at hxbd
            linarith
          nlinarith [this, hbv4, h3]
        · have hm2R : (1:ℝ) ≤ (m2:ℝ) := by
            have : 0 < m2 := Nat.pos_of_ne_zero hm2
            exact_mod_cast this
          have hxbd : t/(2*Real.pi*(k:ℝ)) < 2*(2*(N:ℝ)+d) := by
            rw [div_lt_iff₀ h3]
            nlinarith [hK2t, hm2lt, hkm, hm2R, hbv0, Real.pi_pos,
              mul_pos (by linarith : (0:ℝ) < (m2:ℝ)) h3]
          have : t ≤ 2*Real.pi*(k:ℝ)*(2*(2*(N:ℝ)+d)) := by
            rw [div_lt_iff₀ h3] at hxbd
            linarith
          nlinarith [this, hbv4, h3]
      have hres := vdcI_le_fresnel_wide (d := d) (N := N) (t := t) (C1 := C1) hN hd hd1 hd2
        (by linarith) hC1nn hC1 hk1 hb6v hx8
      refine le_trans hres ?_
      gcongr
    refine le_trans (Finset.sum_le_sum hpt) ?_
    have h2 : ((F.filter (fun k => ¬ k ≤ (m2:ℤ) - 1)).card : ℝ) ≤ 2 := by exact_mod_cast hcard
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc0 : (0:ℝ) ≤ 2*(C1+170)*(8*((N:ℝ)-d))/Real.sqrt t := by positivity
    have hN2 : 8*((N:ℝ)-d) ≤ 8*(N:ℝ) := by linarith [hd]
    have hfin : 2 * (2*(C1+170)*(8*((N:ℝ)-d))/Real.sqrt t) ≤ 100*(C1+170)*(N:ℝ)/Real.sqrt t := by
      have heq : 2 * (2*(C1+170)*(8*((N:ℝ)-d))/Real.sqrt t)
          = (32*(C1+170)*((N:ℝ)-d))/Real.sqrt t := by ring
      rw [heq, div_le_div_iff₀ hsp hsp]
      have hC : (0:ℝ) ≤ C1+170 := by linarith
      have hN1' : (1:ℝ) ≤ (N:ℝ) := hN1
      have h1 : (32:ℝ)*((N:ℝ)-d) ≤ 100*(N:ℝ) := by linarith [hN2, hN1']
      have h2 : (0:ℝ) ≤ (C1+170)*Real.sqrt t := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    linarith [mul_le_mul_of_nonneg_right h2 hc0, hfin]
  linarith [hsplit, hharm, hfres]



/-- Pointwise bound for the exceptional far-left index `k = ⌊K1r⌋ + 1`
(`K1r = t/(2π(N−d))`): either the Fresnel bound applies, or the first-order bound does and
the ratio `(j1+1)/K1r` is bounded away from 1. -/

lemma far_left_exc_le {d : ℝ} {N : ℕ} {t : ℝ} {C1 : ℝ} (hN : 1 ≤ N) (ht : 100 ≤ t)
    (hd : 0 < d) (hd1 : d ≤ 1/2) (hd0 : d ≤ 1/4) (hd2 : (1:ℝ)/2 < (N:ℝ) - d)
    (hC1nn : 0 ≤ C1)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t)
    (j1 : ℕ) (hj1 : ((j1:ℕ):ℝ) ≤ t/(2*Real.pi*((N:ℝ)-d)))
    (hj1u : t/(2*Real.pi*((N:ℝ)-d)) < ((j1:ℕ):ℝ) + 1) :
    ‖vdcI d N t ((j1+1 : ℕ):ℤ)‖ ≤ 2*(C1+170)*(N:ℝ)/Real.sqrt t + 40*(N:ℝ)/t := by
  have ht0 : (0:ℝ) < t := by linarith
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hsp : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hav0 : (0:ℝ) < (N:ℝ) - d := by linarith
  have havN : (N:ℝ) - d ≤ (N:ℝ) := by linarith
  set av : ℝ := (N:ℝ) - d with hav
  set K1r : ℝ := t/(2*Real.pi*av) with hK1r
  have hK1r0 : 0 < K1r := by rw [hK1r]; positivity
  have hcastj : ((j1:ℕ):ℝ) ≤ K1r := by rw [hK1r]; exact hj1
  have hkj : K1r < (((j1+1:ℕ)):ℝ) := by
    have h := hj1u
    rw [hK1r] at h
    push_cast
    linarith [h]
  have hkj0 : (0:ℝ) < (((j1+1:ℕ)):ℝ) := by positivity
  have hK1rt : av*(2*Real.pi*K1r) = t := by rw [hK1r]; field_simp
  have hk1 : 1 ≤ j1 + 1 := le_add_left le_rfl
  have hC : (0:ℝ) ≤ C1+170 := by linarith
  by_cases hbig : (2*(N:ℝ)+d)/6 ≤ vdcX t (j1+1)
  · have h8a : vdcX t (j1+1) ≤ 8*av := by
      rw [vdcX, div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(((j1+1:ℕ)):ℝ))]
      have havpi : (0:ℝ) < av*(2*Real.pi) := mul_pos hav0 (by positivity)
      nlinarith [hK1rt, mul_lt_mul_of_pos_left hkj havpi, hav0, Real.pi_pos]
    rw [hav] at h8a
    have hres := vdcI_le_fresnel_wide (d := d) (N := N) (t := t) (C1 := C1) hN hd hd1 hd2
      (show (2:ℝ) ≤ t by linarith) hC1nn hC1 (k := j1+1) hk1 hbig h8a
    refine le_trans hres ?_
    have hkN : vdcX t (j1+1) ≤ (N:ℝ) := by
      rw [vdcX, div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(((j1+1:ℕ)):ℝ))]
      have havpi : (0:ℝ) < av*(2*Real.pi) := mul_pos hav0 (by positivity)
      nlinarith [hK1rt, mul_lt_mul_of_pos_left hkj havpi, hav0, havN, Real.pi_pos, hN1]
    have h1 : 2*(C1+170)*(vdcX t (j1+1))/Real.sqrt t
        ≤ 2*(C1+170)*(N:ℝ)/Real.sqrt t := by
      apply div_le_div_of_nonneg_right _ hsp.le
      exact mul_le_mul_of_nonneg_left hkN (by linarith : (0:ℝ) ≤ 2*(C1+170))
    have h2 : (0:ℝ) ≤ 40*(N:ℝ)/t := by positivity
    linarith [h1, h2]
  · push Not at hbig
    have hfar := vdcI_far_left hN hd hd1 hd2 ht0 (k := j1+1) hk1 (by
      rw [vdcX, div_lt_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(((j1+1:ℕ)):ℝ))]
      nlinarith [hK1rt, hkj, hav0, Real.pi_pos])
    refine le_trans hfar ?_
    have hstep : K1r/5 < (((j1+1:ℕ)):ℝ) - K1r := by
      have hxeq : vdcX t (j1+1) = av*K1r/(((j1+1:ℕ)):ℝ) := by
        rw [vdcX, hK1r]; field_simp; try ring
      have h1 : (av*K1r)*6 < (2*(N:ℝ)+d)*(((j1+1:ℕ)):ℝ) := by
        rw [hxeq, div_lt_div_iff₀ hkj0 (by norm_num : (0:ℝ) < 6)] at hbig
        linarith [hbig]
      have hb5 : 2*(N:ℝ)+d ≤ 5*av := by rw [hav]; linarith [hN1, hd0]
      nlinarith [h1, hb5, hav0, hK1r0]
    have hden : 2*Real.pi*((((j1+1:ℕ)):ℤ):ℝ) - t/av
        = 2*Real.pi*((((j1+1:ℕ)):ℝ) - K1r) := by
      rw [hK1r]; push_cast; field_simp; try ring
    rw [hav] at hden
    rw [hden]
    have hpos : 0 < 2*Real.pi*((((j1+1:ℕ)):ℝ) - K1r) := by
      have : (0:ℝ) < (((j1+1:ℕ)):ℝ) - K1r := by linarith [hkj]
      positivity
    have hgoal : 8/(2*Real.pi*((((j1+1:ℕ)):ℝ) - K1r)) ≤ 40*(N:ℝ)/t := by
      rw [div_le_div_iff₀ hpos ht0]
      have h2 : 2*Real.pi*(K1r/5) < 2*Real.pi*((((j1+1:ℕ)):ℝ) - K1r) := by
        nlinarith [hstep, Real.pi_pos]
      have h3 : 2*Real.pi*(K1r/5) = t/(5*av) := by rw [hK1r]; field_simp; try ring
      have h4 : (8:ℝ)*t ≤ (40*(N:ℝ))*(t/(5*av)) := by
        rw [show (40*(N:ℝ))*(t/(5*av)) = 8*(N:ℝ)*t/av by field_simp; try ring]
        rw [le_div_iff₀ hav0]
        nlinarith [havN, ht0, hN1]
      nlinarith [h2, h3, h4, hpos, ht0]
    have h2 : (0:ℝ) ≤ 2*(C1+170)*(N:ℝ)/Real.sqrt t := by positivity
    linarith [hgoal, h2]



/-- Second-order far-left bound in the normalised form `vdcKcf/m²`. -/

lemma vdcI_far_left_sq' {d : ℝ} {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hd2 : (1:ℝ)/2 < (N:ℝ) - d) (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k)
    (hxk : vdcX t k < (N:ℝ) - d) (m : ℝ) (hm : 1 ≤ m)
    (hlam : 2*Real.pi*(k:ℝ) - t/((N:ℝ)-d) ≥ 2*Real.pi*m) :
    ‖vdcI d N t (k:ℤ)‖ ≤ vdcKcf d N t / m^2 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi2 : (4:ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hm0 : (0:ℝ) < m := by linarith
  set A : ℝ := (2*vwM2+1)/d with hAdef
  set Mu : ℝ := t/((N:ℝ)-d)^2 with hMudef
  set Mu3 : ℝ := 2*t/((N:ℝ)-d)^3 with hMu3def
  set N2 : ℝ := 2*(N:ℝ) with hN2def
  set lam : ℝ := 2*Real.pi*((k:ℤ):ℝ) - t/((N:ℝ)-d) with hlamdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact div_nonneg (by linarith [vwM2_nonneg]) hd.le
  have hMu0 : 0 ≤ Mu := by rw [hMudef]; positivity
  have hMu30 : 0 ≤ Mu3 := by rw [hMu3def]; positivity
  have hN20 : 0 ≤ N2 := by rw [hN2def]; positivity
  have hlam' : 2*Real.pi*m ≤ lam := by
    rw [hlamdef]
    have hb : 2*Real.pi*((k:ℤ):ℝ) = 2*Real.pi*(k:ℝ) := by push_cast; ring
    rw [hb]; exact hlam
  have h0lam : (0:ℝ) ≤ 2*Real.pi*m := by positivity
  have hlam0 : (0:ℝ) < lam := by nlinarith [hlam', hm0, hpi]
  -- monotone power bounds
  have hp2 : (2*Real.pi*m)^2 ≤ lam^2 := pow_le_pow_left₀ h0lam hlam' 2
  have hp3 : (2*Real.pi*m)^3 ≤ lam^3 := pow_le_pow_left₀ h0lam hlam' 3
  have hp4 : (2*Real.pi*m)^4 ≤ lam^4 := pow_le_pow_left₀ h0lam hlam' 4
  have hm2 : (1:ℝ) ≤ m^2 := by nlinarith [hm]
  have hm3 : (1:ℝ) ≤ m^3 := by nlinarith [hm]
  have hm4 : (1:ℝ) ≤ m^4 := by nlinarith [hm]
  -- the four base inequalities
  have hb1 : 8*m^2 ≤ lam^2 := by nlinarith [hp2, hpi2, hm2]
  have hpm : (2:ℝ) ≤ Real.pi^2*m := by nlinarith [hpi2, hm]
  have hpm4 : (4:ℝ) ≤ Real.pi^2*m^2 := by nlinarith [hpi2, hm2]
  have hb2 : 16*Real.pi*m^2 ≤ lam^3 := by
    have h : 16*Real.pi*m^2 ≤ (2*Real.pi*m)^3 := by nlinarith [hpm, hpi, hm0]
    linarith [h, hp3]
  have hb4 : 32*Real.pi^2*m^2 ≤ lam^4 := by
    have h : 32*Real.pi^2*m^2 ≤ (2*Real.pi*m)^4 := by nlinarith [hpm4, hpi, hm0]
    linarith [h, hp4]
  -- the analytic bound
  have hsq := vdcI_far_left_sq (K0 := N2) (K1 := 2) (K2 := A) hN hd hd1 hd2 ht hk hxk
    (by rw [hN2def]; exact int_abs_vw_le hN hd hd1)
    (integral_abs_deriv_vw_support hN hd)
    (by rw [hAdef, ← iteratedDeriv2_vw_eq]; exact integral_abs_iteratedDeriv2_vw_le hN hd)
  have hsq' : ‖vdcI d N t (k:ℤ)‖
      ≤ 8*(A + 2*Mu/lam + N2*Mu3/lam + N2*Mu^2/lam^2)/lam^2 := by
    rw [hAdef, hMudef, hMu3def, hN2def, hlamdef]
    exact hsq
  refine le_trans hsq' ?_
  -- split the LHS
  have hsplitL : 8*(A + 2*Mu/lam + N2*Mu3/lam + N2*Mu^2/lam^2)/lam^2
      = 8*A/lam^2 + 16*Mu/lam^3 + 8*(N2*Mu3)/lam^3 + 8*(N2*Mu^2)/lam^4 := by
    field_simp
    ring_nf
  rw [hsplitL]
  -- split the RHS
  rw [vdcKcf, ← hAdef, ← hMudef, ← hMu3def, ← hN2def]
  rw [add_div, add_div, add_div]
  -- four termwise inequalities
  have t1 : 8*A/lam^2 ≤ A/m^2 := by
    have hbase : 8/lam^2 ≤ 1/m^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simpa using hb1
    calc 8*A/lam^2 = A*(8/lam^2) := by ring
      _ ≤ A*(1/m^2) := mul_le_mul_of_nonneg_left hbase hA0
      _ = A/m^2 := by ring
  have t2 : 16*Mu/lam^3 ≤ (Mu/Real.pi)/m^2 := by
    have hbase : 16/lam^3 ≤ (1/Real.pi)/m^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h := mul_le_mul_of_nonneg_left hb2 (by positivity : (0:ℝ) ≤ 1/Real.pi)
      have heq : (1/Real.pi)*(16*Real.pi*m^2) = 16*m^2 := by field_simp; try ring
      rwa [heq] at h
    calc 16*Mu/lam^3 = Mu*(16/lam^3) := by ring
      _ ≤ Mu*((1/Real.pi)/m^2) := mul_le_mul_of_nonneg_left hbase hMu0
      _ = (Mu/Real.pi)/m^2 := by ring
  have t3 : 8*(N2*Mu3)/lam^3 ≤ ((N2*Mu3)/(2*Real.pi))/m^2 := by
    have hbase : 8/lam^3 ≤ (1/(2*Real.pi))/m^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h := mul_le_mul_of_nonneg_left hb2 (by positivity : (0:ℝ) ≤ 1/(2*Real.pi))
      have heq : (1/(2*Real.pi))*(16*Real.pi*m^2) = 8*m^2 := by field_simp; try ring
      rwa [heq] at h
    calc 8*(N2*Mu3)/lam^3 = (N2*Mu3)*(8/lam^3) := by ring
      _ ≤ (N2*Mu3)*((1/(2*Real.pi))/m^2) :=
          mul_le_mul_of_nonneg_left hbase (mul_nonneg hN20 hMu30)
      _ = ((N2*Mu3)/(2*Real.pi))/m^2 := by ring
  have t4 : 8*(N2*Mu^2)/lam^4 ≤ ((N2*Mu^2)/(2*Real.pi)^2)/m^2 := by
    have hbase : 8/lam^4 ≤ (1/(2*Real.pi)^2)/m^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h := mul_le_mul_of_nonneg_left hb4 (by positivity : (0:ℝ) ≤ 1/(2*Real.pi)^2)
      have heq : (1/(2*Real.pi)^2)*(32*Real.pi^2*m^2) = 8*m^2 := by field_simp; try ring
      rwa [heq] at h
    calc 8*(N2*Mu^2)/lam^4 = (N2*Mu^2)*(8/lam^4) := by ring
      _ ≤ (N2*Mu^2)*((1/(2*Real.pi)^2)/m^2) :=
          mul_le_mul_of_nonneg_left hbase (mul_nonneg hN20 (pow_nonneg hMu0 2))
      _ = ((N2*Mu^2)/(2*Real.pi)^2)/m^2 := by ring
  linarith [t1, t2, t3, t4]

/-- **Shifted `min`-summation bound over a `Finset ℤ`.** -/
lemma sum_min_shift_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {F : Finset ℤ} {c : ℤ}
    (hF : ∀ k ∈ F, c < k) :
    ∑ k ∈ F, min (A/(((k - c : ℤ) : ℝ))) (B/((((k - c : ℤ) : ℝ))^2))
      ≤ A * (3 + Real.log (2 + B/A)) := by
  have hcongr : ∀ k ∈ F, min (A/(((k - c : ℤ) : ℝ))) (B/((((k - c : ℤ) : ℝ))^2))
      = min (A/((((k - c).toNat : ℕ) : ℝ))) (B/(((((k - c).toNat : ℕ) : ℝ))^2)) := by
    intro k hk
    have h0 : 0 ≤ k - c := by have := hF k hk; omega
    rw [vdcIntToNatCast (k - c) h0]
  rw [Finset.sum_congr rfl hcongr]
  have hinj : Set.InjOn (fun k : ℤ => (k - c).toNat) (F : Set ℤ) := by
    intro a ha b hb hab
    simp only at hab
    have ha0 : 0 ≤ a - c := by have := hF a ha; omega
    have hb0 : 0 ≤ b - c := by have := hF b hb; omega
    have h1 : ((a - c).toNat : ℤ) = a - c := Int.toNat_of_nonneg ha0
    have h2 : ((b - c).toNat : ℤ) = b - c := Int.toNat_of_nonneg hb0
    have hmid : (a - c : ℤ) = (b - c : ℤ) := by
      rw [← h1, ← h2]
      exact congrArg (fun n : ℕ => (n : ℤ)) hab
    omega
  rw [← Finset.sum_image (f := fun i : ℕ => min (A/(i:ℝ)) (B/((i:ℝ)^2)))
        (g := fun k : ℤ => (k - c).toNat) hinj]
  refine sum_min_inv_le hA hB (fun j hj => ?_)
  rw [Finset.mem_image] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  have h0 : 0 ≤ k - c := by have := hF k hk; omega
  have h1 : ((k - c).toNat : ℤ) = k - c := Int.toNat_of_nonneg h0
  have h2 : (1:ℤ) ≤ k - c := by have := hF k hk; omega
  have h3 : (1:ℤ) ≤ ((k - c).toNat : ℤ) := by rw [h1]; exact h2
  omega



/-- **Finset bound for the far-left part of the complement** `K < k`. -/
lemma finset_left_le {d : ℝ} {N : ℕ} {t : ℝ} {C1 : ℝ} {K : ℕ} (hN : 1 ≤ N) (ht : 100 ≤ t)
    (hd : 0 < d) (hd1 : d ≤ 1/2) (hd0 : d ≤ 1/4) (hd2 : (1:ℝ)/2 < (N:ℝ) - d)
    (htd : t*d ≤ (N:ℝ)^2/32)
    (hC1nn : 0 ≤ C1)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t)
    (hK2 : (K:ℝ) ≤ t/(2*Real.pi*(N:ℝ)))
    (hK3 : t/(2*Real.pi*(N:ℝ)) < (K:ℝ) + 1)
    {F : Finset ℤ} (hF : ∀ k ∈ F, (K:ℤ) < k) :
    ∑ k ∈ F, ‖vdcI d N t k‖ ≤ 8*(C1+170)*(N:ℝ)/Real.sqrt t
      + (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi))) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hN0 : (0:ℝ) < (N:ℝ) := by linarith
  have hsp : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hC2 : (0:ℝ) ≤ C1+170 := by linarith
  set K1r : ℝ := t/(2*Real.pi*((N:ℝ)-d)) with hK1r
  set j1 : ℕ := Nat.floor K1r with hj1
  have hav0 : (0:ℝ) < (N:ℝ) - d := by linarith
  have hK1r0 : (0:ℝ) < K1r := by rw [hK1r]; positivity
  have hj1le : (j1:ℝ) ≤ K1r := by rw [hj1]; exact Nat.floor_le hK1r0.le
  have hj1lt : K1r < (j1:ℝ) + 1 := by rw [hj1]; exact Nat.lt_floor_add_one K1r
  have hK1rt : ((N:ℝ)-d)*(2*Real.pi*K1r) = t := by rw [hK1r]; field_simp; try ring
  have hK1req : t/((N:ℝ)-d) = 2*Real.pi*K1r := by
    rw [div_eq_iff hav0.ne']; linarith [hK1rt]
  have hav_eq : (N:ℝ)-d = t/(2*Real.pi*K1r) := by
    rw [eq_div_iff (ne_of_gt (by positivity : (0:ℝ) < 2*Real.pi*K1r))]; linarith [hK1rt]
  have hK1rK : K1r < (K:ℝ) + 2 := by
    have h2 : K1r - t/(2*Real.pi*(N:ℝ)) = t*d/(2*Real.pi*((N:ℝ)-d)*(N:ℝ)) := by
      rw [hK1r]; field_simp; try ring
    have h3 : t*d/(2*Real.pi*((N:ℝ)-d)*(N:ℝ)) < 1 := by
      have h1 : (16:ℝ)*(t*d) ≤ ((N:ℝ)-d)*(N:ℝ) := by nlinarith [htd, hN1, hd0]
      have h4 : t*d/(2*Real.pi*((N:ℝ)-d)*(N:ℝ)) ≤ 1/(32*Real.pi) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h1, Real.pi_pos]
      have h5 : (1:ℝ)/(32*Real.pi) < 1 := by
        rw [div_lt_one (by positivity : (0:ℝ) < 32*Real.pi)]
        nlinarith [Real.pi_gt_three]
      linarith [h4, h5]
    linarith
  have hj1K : (j1:ℤ) ≤ (K:ℤ) + 1 := by
    have h : (j1:ℝ) < (K:ℝ) + 2 := lt_of_le_of_lt hj1le hK1rK
    have h' : (j1:ℤ) < (K:ℤ) + 2 := by exact_mod_cast h
    omega
  -- region 3: k <= j1+1 (Fresnel / exceptional)
  have h3bound : ∑ k ∈ F.filter (fun k => k ≤ (j1:ℤ)+1), ‖vdcI d N t k‖
      ≤ 2*(2*(C1+170)*(N:ℝ)/Real.sqrt t + 40*(N:ℝ)/t) := by
    have hpt : ∀ k ∈ F.filter (fun k => k ≤ (j1:ℤ)+1),
        ‖vdcI d N t k‖ ≤ 2*(C1+170)*(N:ℝ)/Real.sqrt t + 40*(N:ℝ)/t := by
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨hkF, hkc⟩ := hk
      have hKk : (K:ℤ) < k := hF k hkF
      have hk0 : (0:ℤ) ≤ k := by omega
      have hk1 : 1 ≤ k.toNat := by omega
      have hcst : ((k.toNat : ℕ) : ℝ) = (k:ℝ) := vdcIntToNatCast k hk0
      have hkpos : (0:ℝ) < (k:ℝ) := by
        have h : (1:ℝ) ≤ ((k.toNat:ℕ):ℝ) := by exact_mod_cast hk1
        rw [← hcst]; linarith
      have hxkc : vdcX t k.toNat = t/(2*Real.pi*((k:ℝ))) := by rw [vdcX, hcst]
      by_cases hkle : k ≤ (j1:ℤ)
      · have hxav : ((N:ℝ)-d) ≤ vdcX t k.toNat := by
          rw [hxkc, le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(k:ℝ))]
          have hkK1r : (k:ℝ) ≤ K1r :=
            le_trans (by exact_mod_cast hkle : (k:ℝ) ≤ (j1:ℝ)) hj1le
          have hstep : 2*Real.pi*(k:ℝ) ≤ 2*Real.pi*K1r :=
            mul_le_mul_of_nonneg_left hkK1r (by positivity)
          have hstep2 : ((N:ℝ)-d)*(2*Real.pi*(k:ℝ)) ≤ ((N:ℝ)-d)*(2*Real.pi*K1r) :=
            mul_le_mul_of_nonneg_left hstep hav0.le
          linarith [hstep2, hK1rt]
        have hb6 : (2*(N:ℝ)+d)/6 ≤ vdcX t k.toNat := by
          have hc : (2*(N:ℝ)+d)/6 ≤ (N:ℝ)-d := by linarith [hN1, hd0]
          linarith
        have hxN : vdcX t k.toNat ≤ (N:ℝ) := by
          rw [hxkc, div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(k:ℝ))]
          have hkk : t/(2*Real.pi*(N:ℝ)) < (k:ℝ) :=
            lt_of_lt_of_le hK3 (by exact_mod_cast (by omega : (K:ℤ)+1 ≤ k))
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(N:ℝ))] at hkk
          nlinarith [hkk, Real.pi_pos]
        have h8a : vdcX t k.toNat ≤ 8*((N:ℝ)-d) := by
          have hc : (N:ℝ) ≤ 8*((N:ℝ)-d) := by linarith [hN1, hd0]
          linarith
        have hres := vdcI_le_fresnel_wide (d := d) (N := N) (t := t) (C1 := C1) hN hd hd1 hd2
          (by linarith : (2:ℝ) ≤ t) hC1nn hC1 (k := k.toNat) hk1 hb6 h8a
        have hcc : (((k.toNat : ℕ)) : ℤ) = k := Int.toNat_of_nonneg hk0
        rw [hcc] at hres
        refine le_trans hres ?_
        have h1 : 2*(C1+170)*vdcX t k.toNat/Real.sqrt t
            ≤ 2*(C1+170)*(N:ℝ)/Real.sqrt t := by
          apply div_le_div_of_nonneg_right _ hsp.le
          exact mul_le_mul_of_nonneg_left hxN (by linarith : (0:ℝ) ≤ 2*(C1+170))
        linarith [h1, show (0:ℝ) ≤ 40*(N:ℝ)/t by positivity]
      · have hkeq : k = (j1:ℤ)+1 := by omega
        rw [hkeq]
        have hres := far_left_exc_le (d := d) (N := N) (t := t) (C1 := C1) hN ht hd hd1 hd0
          hd2 hC1nn hC1 j1 hj1le hj1lt
        have hcast : (((j1+1 : ℕ)) : ℤ) = (j1:ℤ)+1 := by push_cast; ring
        rw [hcast] at hres
        exact hres
    calc ∑ k ∈ F.filter (fun k => k ≤ (j1:ℤ)+1), ‖vdcI d N t k‖
        ≤ (F.filter (fun k => k ≤ (j1:ℤ)+1)).card •
            (2*(C1+170)*(N:ℝ)/Real.sqrt t + 40*(N:ℝ)/t) :=
          Finset.sum_le_card_nsmul _ _ _ hpt
      _ ≤ 2 * (2*(C1+170)*(N:ℝ)/Real.sqrt t + 40*(N:ℝ)/t) := by
          have hcard : (F.filter (fun k => k ≤ (j1:ℤ)+1)).card ≤ 2 := by
            have hsub : F.filter (fun k => k ≤ (j1:ℤ)+1) ⊆ Finset.Icc ((K:ℤ)+1) ((j1:ℤ)+1) := by
              intro k hk
              rw [Finset.mem_filter] at hk
              rw [Finset.mem_Icc]
              exact ⟨by have := hF k hk.1; omega, hk.2⟩
            refine le_trans (Finset.card_le_card hsub) ?_
            rw [Int.card_Icc]
            rw [show (((j1:ℤ) + 1) + 1 - ((K:ℤ) + 1)) = ((j1:ℤ) + 1 - (K:ℤ)) by ring]
            exact Int.toNat_le.mpr (by omega)
          have hc : ((F.filter (fun k => k ≤ (j1:ℤ)+1)).card : ℝ) ≤ 2 := by exact_mod_cast hcard
          have hX := mul_le_mul_of_nonneg_right hc
            (by positivity : (0:ℝ) ≤ 2*(C1+170)*(N:ℝ)/Real.sqrt t + 40*(N:ℝ)/t)
          simpa only [nsmul_eq_mul] using hX
  -- region 4: j1+1 < k (far left)
  have h4bound : ∑ k ∈ F.filter (fun k => (j1:ℤ)+1 < k), ‖vdcI d N t k‖
      ≤ (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi))) := by
    have hpt : ∀ k ∈ F.filter (fun k => (j1:ℤ)+1 < k),
        ‖vdcI d N t k‖ ≤ min ((4/Real.pi)/((((k - ((j1:ℤ)+1) : ℤ)):ℝ)))
            (vdcKcf d N t/(((((k - ((j1:ℤ)+1) : ℤ)):ℝ))^2)) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨hkF, hkc⟩ := hk
      have hKk : (K:ℤ) < k := hF k hkF
      have hk0 : (0:ℤ) ≤ k := by omega
      have hk1 : 1 ≤ k.toNat := by omega
      have hcst : ((k.toNat : ℕ) : ℝ) = (k:ℝ) := vdcIntToNatCast k hk0
      have hcc : (((k.toNat : ℕ)) : ℤ) = k := Int.toNat_of_nonneg hk0
      have hkpos : (0:ℝ) < (k:ℝ) := by
        have h : (1:ℝ) ≤ ((k.toNat:ℕ):ℝ) := by exact_mod_cast hk1
        rw [← hcst]; linarith
      have hK1r_lt_k : K1r < (k:ℝ) := by
        have h1 : ((((j1:ℤ)+1 : ℤ) : ℝ)) < (k:ℝ) := by exact_mod_cast hkc
        have h2 : K1r < ((((j1:ℤ)+1 : ℤ) : ℝ)) := by push_cast; linarith [hj1lt]
        linarith
      have hxav : vdcX t k.toNat < (N:ℝ)-d := by
        rw [vdcX, hcst, hav_eq]
        rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(k:ℝ))
              (by positivity : (0:ℝ) < 2*Real.pi*K1r)]
        have hstep : 2*Real.pi*K1r < 2*Real.pi*(k:ℝ) :=
          mul_lt_mul_of_pos_left hK1r_lt_k (by positivity)
        nlinarith [mul_lt_mul_of_pos_left hstep ht0]
      have hm : (1:ℝ) ≤ (((k - ((j1:ℤ)+1) : ℤ)):ℝ) := by
        have h1 : (1:ℤ) ≤ k - ((j1:ℤ)+1) := by omega
        exact_mod_cast h1
      have hc1K1r : K1r ≤ ((((j1:ℤ)+1 : ℤ) : ℝ)) := by push_cast; linarith [hj1lt]
      have hle : ((((k-((j1:ℤ)+1):ℤ)):ℝ)) ≤ (k:ℝ) - K1r := by
        have hcc2 : (((k-((j1:ℤ)+1):ℤ)):ℝ) = (k:ℝ) - ((((j1:ℤ)+1 : ℤ) : ℝ)) := by
          push_cast; ring
        rw [hcc2]; linarith
      have hlam_nice : 2*Real.pi*(k:ℝ) - 2*Real.pi*K1r
          ≥ 2*Real.pi*((((k-((j1:ℤ)+1):ℤ)):ℝ)) := by
        have hstep : 2*Real.pi*((((k-((j1:ℤ)+1):ℤ)):ℝ)) ≤ 2*Real.pi*((k:ℝ) - K1r) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        have h3 : 2*Real.pi*((k:ℝ) - K1r) = 2*Real.pi*(k:ℝ) - 2*Real.pi*K1r := by ring
        linarith [hstep, h3]
      have hlam2 : 2*Real.pi*((k.toNat:ℕ):ℝ) - t/((N:ℝ)-d)
          ≥ 2*Real.pi*((((k-((j1:ℤ)+1):ℤ)):ℝ)) := by
        rw [hcst, hK1req]; exact hlam_nice
      have hfar := vdcI_far_left hN hd hd1 hd2 ht0 (k := k.toNat) hk1 hxav
      rw [hcc, hK1req] at hfar
      have hsq := vdcI_far_left_sq' hN hd hd1 hd2 ht0 (k := k.toNat) hk1 hxav
          (((k - ((j1:ℤ)+1) : ℤ)):ℝ) hm hlam2
      rw [hcc] at hsq
      have h1 : ‖vdcI d N t k‖ ≤ (4/Real.pi)/((((k - ((j1:ℤ)+1) : ℤ)):ℝ)) := by
        refine le_trans hfar ?_
        have hEpos : (0:ℝ) < (((k - ((j1:ℤ)+1) : ℤ)):ℝ) := by linarith
        have hkey : (4/Real.pi)/((((k - ((j1:ℤ)+1) : ℤ)):ℝ))
            = 8/(2*Real.pi*((((k - ((j1:ℤ)+1) : ℤ)):ℝ))) := by
          field_simp
          try ring
        rw [hkey]
        refine div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8)
          (by positivity : (0:ℝ) < 2*Real.pi*((((k - ((j1:ℤ)+1) : ℤ)):ℝ))) ?_
        exact hlam_nice
      exact le_min h1 hsq
    calc ∑ k ∈ F.filter (fun k => (j1:ℤ)+1 < k), ‖vdcI d N t k‖
        ≤ ∑ k ∈ F.filter (fun k => (j1:ℤ)+1 < k),
            min ((4/Real.pi)/((((k - ((j1:ℤ)+1) : ℤ)):ℝ)))
              (vdcKcf d N t/(((((k - ((j1:ℤ)+1) : ℤ)):ℝ))^2)) :=
          Finset.sum_le_sum hpt
      _ ≤ (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi))) :=
          sum_min_shift_le (A := 4/Real.pi) (B := vdcKcf d N t)
            (F := F.filter (fun k => (j1:ℤ)+1 < k)) (c := (j1:ℤ)+1)
            (by positivity) (vdcKcf_pos hd hd1 hN ht0)
            (fun k hk => by rw [Finset.mem_filter] at hk; exact hk.2)
  have hsplit : ∑ k ∈ F, ‖vdcI d N t k‖
      = ∑ k ∈ F.filter (fun k => k ≤ (j1:ℤ)+1), ‖vdcI d N t k‖
        + ∑ k ∈ F.filter (fun k => (j1:ℤ)+1 < k), ‖vdcI d N t k‖ := by
    have h1 := Finset.sum_filter_add_sum_filter_not F (fun k => k ≤ (j1:ℤ)+1)
      (fun k => ‖vdcI d N t k‖)
    have heq : F.filter (fun k => ¬ k ≤ (j1:ℤ)+1) = F.filter (fun k => (j1:ℤ)+1 < k) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · intro h; exact ⟨h.1, not_le.mp h.2⟩
      · intro h; exact ⟨h.1, not_le.mpr h.2⟩
    rw [heq] at h1
    exact h1.symm
  have hsqrt10 : (10:ℝ) ≤ Real.sqrt t :=
    (Real.le_sqrt (by norm_num) ht0.le).mpr (by nlinarith)
  have hdrift : 40*(N:ℝ)/t ≤ 2*(C1+170)*(N:ℝ)/Real.sqrt t := by
    rw [div_le_div_iff₀ ht0 hsp]
    have h20 : (20:ℝ) ≤ (C1+170)*Real.sqrt t := by
      have h1 : (20:ℝ) ≤ (C1+170)*10 := by linarith [hC2]
      exact le_trans h1 (mul_le_mul_of_nonneg_left hsqrt10 hC2)
    have h2 : (40:ℝ)*Real.sqrt t ≤ 2*(C1+170)*t := by
      nlinarith [h20, Real.sq_sqrt ht0.le]
    have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ (N:ℝ))
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h3
  have htotal : 2*(2*(C1+170)*(N:ℝ)/Real.sqrt t + 40*(N:ℝ)/t)
      ≤ 8*(C1+170)*(N:ℝ)/Real.sqrt t := by
    have hmono : 4*((C1+170)*(N:ℝ)/Real.sqrt t) + 80*(N:ℝ)/t
        ≤ 4*((C1+170)*(N:ℝ)/Real.sqrt t) + 4*((C1+170)*(N:ℝ)/Real.sqrt t) := by
      have h := mul_le_mul_of_nonneg_left hdrift (by norm_num : (0:ℝ) ≤ 2)
      rw [show (2:ℝ)*(40*(N:ℝ)/t) = 80*(N:ℝ)/t by ring] at h
      rw [show (2:ℝ)*(2*(C1+170)*(N:ℝ)/Real.sqrt t)
          = 4*((C1+170)*(N:ℝ)/Real.sqrt t) by ring] at h
      linarith [h]
    rw [show 2*(2*(C1+170)*(N:ℝ)/Real.sqrt t + 40*(N:ℝ)/t)
        = 4*((C1+170)*(N:ℝ)/Real.sqrt t) + 80*(N:ℝ)/t by ring]
    rw [show 8*(C1+170)*(N:ℝ)/Real.sqrt t
        = 4*((C1+170)*(N:ℝ)/Real.sqrt t) + 4*((C1+170)*(N:ℝ)/Real.sqrt t) by ring]
    exact hmono
  rw [hsplit]
  linarith [h3bound, h4bound, htotal]


/-- **Logarithmic comparison.**  If `0 ≤ X ≤ K·Y²` with `K, Y ≥ 1` then
`log (2+X) ≤ (log (2+K) + 2)·(log Y + 1)`. -/
lemma log_two_add_le_sq' {X Y K : ℝ} (hK : 1 ≤ K) (hX : 0 ≤ X) (hY : 1 ≤ Y)
    (hXY : X ≤ K * Y^2) :
    Real.log (2 + X) ≤ (Real.log (2 + K) + 2) * (Real.log Y + 1) := by
  have hY0 : (0:ℝ) < Y := by linarith
  have hY1 : (1:ℝ) ≤ Y^2 := by nlinarith
  have h2K : (0:ℝ) < 2 + K := by linarith
  have hbound : 2 + X ≤ (2 + K) * Y^2 := by nlinarith [hXY, hY1, hK]
  have hlogK : (0:ℝ) ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  have hlogY : (0:ℝ) ≤ Real.log Y := Real.log_nonneg hY
  have h1 : Real.log (2 + X) ≤ Real.log ((2 + K) * Y^2) :=
    Real.log_le_log (by linarith) hbound
  have h2 : Real.log ((2 + K) * Y^2) = Real.log (2 + K) + 2 * Real.log Y := by
    rw [Real.log_mul (ne_of_gt h2K) (by positivity)]
    rw [Real.log_pow]
    norm_num
  rw [h2] at h1
  nlinarith [h1, hlogK, hlogY]

/-- **Bound on `vdcKc` in terms of `N·t`.** -/
lemma vdcKc_le {d : ℝ} {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 1 ≤ t) (hNt : (N:ℝ) ≤ t)
    (hd : 0 < d) (hd4 : d ≤ 1/4) (hdinv : 1/d ≤ 4 + 32*t/(N:ℝ)^2) :
    vdcKc d N t ≤ (40*(2*vwM2+1) + 200) * (((N:ℝ)*t)^2) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have ht0 : (0:ℝ) < t := by linarith
  have hN0 : (0:ℝ) < (N:ℝ) := by linarith
  have hc : (0:ℝ) ≤ 2*vwM2+1 := by linarith [vwM2_nonneg]
  have ha : (3:ℝ)/4 ≤ (N:ℝ) - d := by linarith
  have ha0 : (0:ℝ) < (N:ℝ) - d := by linarith
  have hb : 2*(N:ℝ) + d ≤ 3*(N:ℝ) := by linarith
  have hb0 : (0:ℝ) < 2*(N:ℝ) + d := by positivity
  have heta : (1:ℝ) ≤ (N:ℝ)*t := by
    have h : (0:ℝ) ≤ ((N:ℝ) - 1)*(t - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h, hN1, ht0]
  have M2 : (1:ℝ) ≤ ((N:ℝ)*t)^2 := by nlinarith [heta]
  have hNM : (N:ℝ) ≤ ((N:ℝ)*t)^2 := by nlinarith [heta, hN1]
  have hN2M : (N:ℝ)^2 ≤ ((N:ℝ)*t)^2 := by nlinarith [heta, hN1]
  have htM : t ≤ ((N:ℝ)*t)^2 := by nlinarith [heta, ht0, hN1]
  have hN3M : (N:ℝ)^3 ≤ ((N:ℝ)*t)^2 := by
    have h1 : (N:ℝ) ≤ t^2 := by nlinarith [hNt, ht0]
    have h2 : (N:ℝ)*(N:ℝ)^2 ≤ t^2*(N:ℝ)^2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ (N:ℝ)^2)
    nlinarith [h2]
  have ha2 : ((3:ℝ)/4)^2 ≤ ((N:ℝ)-d)^2 := pow_le_pow_left₀ (by norm_num) ha 2
  have ha3 : ((3:ℝ)/4)^3 ≤ ((N:ℝ)-d)^3 := pow_le_pow_left₀ (by norm_num) ha 3
  have ha4 : ((3:ℝ)/4)^4 ≤ ((N:ℝ)-d)^4 := pow_le_pow_left₀ (by norm_num) ha 4
  have hA2 : 32*t/(N:ℝ)^2 ≤ 32*((N:ℝ)*t)^2 := by
    have htdiv : t/(N:ℝ)^2 ≤ t := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (N:ℝ)^2)]
      nlinarith [ht0, hN1]
    have h := mul_le_mul_of_nonneg_left htdiv (by norm_num : (0:ℝ) ≤ 32)
    have e1 : (32:ℝ)*(t/(N:ℝ)^2) = 32*t/(N:ℝ)^2 := by ring
    rw [e1] at h
    have h' : 32*t ≤ 32*((N:ℝ)*t)^2 := by linarith [htM]
    linarith [h, h']
  -- term A
  have hA : (2*vwM2+1)/d ≤ 36*(2*vwM2+1)*((N:ℝ)*t)^2 := by
    have h1 : (2*vwM2+1)/d ≤ (2*vwM2+1)*(4 + 32*t/(N:ℝ)^2) := by
      have h := mul_le_mul_of_nonneg_left hdinv hc
      have h1 : (2*vwM2+1)*(1/d) = (2*vwM2+1)/d := by ring
      rwa [h1] at h
    have h41 : (4:ℝ) ≤ 4*((N:ℝ)*t)^2 := by linarith [M2]
    have h4 : 4 + 32*t/(N:ℝ)^2 ≤ 36*((N:ℝ)*t)^2 := by linarith [h41, hA2]
    calc (2*vwM2+1)/d ≤ (2*vwM2+1)*(4 + 32*t/(N:ℝ)^2) := h1
      _ ≤ (2*vwM2+1)*(36*((N:ℝ)*t)^2) := mul_le_mul_of_nonneg_left h4 hc
      _ = 36*(2*vwM2+1)*((N:ℝ)*t)^2 := by ring
  -- term B
  have hB : 2*(t/((N:ℝ)-d)^2)/(t/(2*(N:ℝ)+d)) ≤ 12*((N:ℝ)*t)^2 := by
    have h1 : 2*(t/((N:ℝ)-d)^2)/(t/(2*(N:ℝ)+d))
        = 2*(2*(N:ℝ)+d)/(((N:ℝ)-d)^2) := by
      field_simp; try ring
    rw [h1]
    have h2 : 2*(2*(N:ℝ)+d)/(((N:ℝ)-d)^2) ≤ 2*3*(N:ℝ)/((3:ℝ)/4)^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [ha2, hb, ha0, hb0, hN1]
    have h3 : 2*3*(N:ℝ)/((3:ℝ)/4)^2 = (32/3)*(N:ℝ) := by field_simp; ring
    rw [h3] at h2
    have h4 : (32/3)*(N:ℝ) ≤ 12*((N:ℝ)*t)^2 := by nlinarith [hNM]
    linarith [h2, h4]
  -- term C
  have hC : (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(t/(2*(N:ℝ)+d)) ≤ 30*((N:ℝ)*t)^2 := by
    have h1 : (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(t/(2*(N:ℝ)+d))
        = 4*(N:ℝ)*(2*(N:ℝ)+d)/(((N:ℝ)-d)^3) := by
      field_simp; try ring
    rw [h1]
    have hb3 : (2*(N:ℝ)+d)^3 ≤ (3*(N:ℝ))^3 := pow_le_pow_left₀ hb0.le hb 3
    have h2 : 4*(N:ℝ)*(2*(N:ℝ)+d)/(((N:ℝ)-d)^3) ≤ 4*(N:ℝ)*3*(N:ℝ)/((3:ℝ)/4)^3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 4*(N:ℝ)*(2*(N:ℝ)+d)*(((3:ℝ)/4)^3)
          ≤ 4*(N:ℝ)*(3*(N:ℝ))*(((3:ℝ)/4)^3) := by
        have hc1 : (0:ℝ) ≤ 4*(N:ℝ)*(((3:ℝ)/4)^3) := by positivity
        nlinarith [hb, hc1]
      have h2 : 4*(N:ℝ)*(3*(N:ℝ))*(((3:ℝ)/4)^3)
          ≤ 4*(N:ℝ)*(3*(N:ℝ))*(((N:ℝ)-d)^3) :=
        mul_le_mul_of_nonneg_left ha3 (by positivity)
      linarith [h1, h2]
    have h3 : 4*(N:ℝ)*3*(N:ℝ)/((3:ℝ)/4)^3 = (256/9)*((N:ℝ)^2) := by field_simp; ring
    rw [h3] at h2
    have h4 : (256/9)*((N:ℝ)^2) ≤ 30*((N:ℝ)*t)^2 := by nlinarith [hN2M]
    linarith [h2, h4]
  -- term D
  have hD : (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(t/(2*(N:ℝ)+d))^2
      ≤ 60*((N:ℝ)*t)^2 := by
    have h1 : (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(t/(2*(N:ℝ)+d))^2
        = 2*(N:ℝ)*((2*(N:ℝ)+d))^2/(((N:ℝ)-d)^4) := by
      field_simp; try ring
    rw [h1]
    have hb2 : (2*(N:ℝ)+d)^2 ≤ (3*(N:ℝ))^2 := pow_le_pow_left₀ hb0.le hb 2
    have h2 : 2*(N:ℝ)*((2*(N:ℝ)+d))^2/(((N:ℝ)-d)^4)
        ≤ 2*(N:ℝ)*(3*(N:ℝ))^2/(((3:ℝ)/4)^4) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 2*(N:ℝ)*(2*(N:ℝ)+d)^2*(((3:ℝ)/4)^4)
          ≤ 2*(N:ℝ)*(3*(N:ℝ))^2*(((3:ℝ)/4)^4) := by
        have hc1 : (0:ℝ) ≤ 2*(N:ℝ)*(((3:ℝ)/4)^4) := by positivity
        have h := mul_le_mul_of_nonneg_left hb2 hc1
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h
      have h2 : 2*(N:ℝ)*(3*(N:ℝ))^2*(((3:ℝ)/4)^4)
          ≤ 2*(N:ℝ)*(3*(N:ℝ))^2*(((N:ℝ)-d)^4) :=
        mul_le_mul_of_nonneg_left ha4 (by positivity)
      linarith [h1, h2]
    have h3 : 2*(N:ℝ)*(3*(N:ℝ))^2/(((3:ℝ)/4)^4) = (512/9)*((N:ℝ)^3) := by
      field_simp; ring
    rw [h3] at h2
    have h4 : (512/9)*((N:ℝ)^3) ≤ 60*((N:ℝ)*t)^2 := by nlinarith [hN3M]
    linarith [h2, h4]
  rw [vdcKc]
  have hK : (40*(2*vwM2+1) + 200) * (((N:ℝ)*t)^2)
      = 40*(2*vwM2+1)*(((N:ℝ)*t)^2) + 200*(((N:ℝ)*t)^2) := by ring
  rw [hK]
  nlinarith [hA, hB, hC, hD, hc, M2]

/-- **Bound on `vdcKcf` in terms of `N·t`.** -/
lemma vdcKcf_le {d : ℝ} {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 1 ≤ t) (hNt : (N:ℝ) ≤ t)
    (hd : 0 < d) (hd4 : d ≤ 1/4) (hdinv : 1/d ≤ 4 + 32*t/(N:ℝ)^2) :
    vdcKcf d N t ≤ (40*(2*vwM2+1) + 200) * (((N:ℝ)*t)^2) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have ht0 : (0:ℝ) < t := by linarith
  have hN0 : (0:ℝ) < (N:ℝ) := by linarith
  have hc : (0:ℝ) ≤ 2*vwM2+1 := by linarith [vwM2_nonneg]
  have ha : (3:ℝ)/4 ≤ (N:ℝ) - d := by linarith
  have ha0 : (0:ℝ) < (N:ℝ) - d := by linarith
  have hb : 2*(N:ℝ) + d ≤ 3*(N:ℝ) := by linarith
  have hb0 : (0:ℝ) < 2*(N:ℝ) + d := by positivity
  have heta : (1:ℝ) ≤ (N:ℝ)*t := by
    have h : (0:ℝ) ≤ ((N:ℝ) - 1)*(t - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h, hN1, ht0]
  have M2 : (1:ℝ) ≤ ((N:ℝ)*t)^2 := by nlinarith [heta]
  have hNM : (N:ℝ) ≤ ((N:ℝ)*t)^2 := by nlinarith [heta, hN1]
  have hN2M : (N:ℝ)^2 ≤ ((N:ℝ)*t)^2 := by nlinarith [heta, hN1]
  have htM : t ≤ ((N:ℝ)*t)^2 := by nlinarith [heta, ht0, hN1]
  have hN3M : (N:ℝ)^3 ≤ ((N:ℝ)*t)^2 := by
    have h1 : (N:ℝ) ≤ t^2 := by nlinarith [hNt, ht0]
    have h2 : (N:ℝ)*(N:ℝ)^2 ≤ t^2*(N:ℝ)^2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ (N:ℝ)^2)
    nlinarith [h2]
  have ha2 : ((3:ℝ)/4)^2 ≤ ((N:ℝ)-d)^2 := pow_le_pow_left₀ (by norm_num) ha 2
  have ha3 : ((3:ℝ)/4)^3 ≤ ((N:ℝ)-d)^3 := pow_le_pow_left₀ (by norm_num) ha 3
  have ha4 : ((3:ℝ)/4)^4 ≤ ((N:ℝ)-d)^4 := pow_le_pow_left₀ (by norm_num) ha 4
  -- term A (same as for vdcKc)
  have hA2 : 32*t/(N:ℝ)^2 ≤ 32*((N:ℝ)*t)^2 := by
    have htdiv : t/(N:ℝ)^2 ≤ t := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (N:ℝ)^2)]
      nlinarith [ht0, hN1]
    have h := mul_le_mul_of_nonneg_left htdiv (by norm_num : (0:ℝ) ≤ 32)
    have e1 : (32:ℝ)*(t/(N:ℝ)^2) = 32*t/(N:ℝ)^2 := by ring
    rw [e1] at h
    have h' : 32*t ≤ 32*((N:ℝ)*t)^2 := by linarith [htM]
    linarith [h, h']
  have hA : (2*vwM2+1)/d ≤ 36*(2*vwM2+1)*((N:ℝ)*t)^2 := by
    have h1 : (2*vwM2+1)/d ≤ (2*vwM2+1)*(4 + 32*t/(N:ℝ)^2) := by
      have h := mul_le_mul_of_nonneg_left hdinv hc
      have h1 : (2*vwM2+1)*(1/d) = (2*vwM2+1)/d := by ring
      rwa [h1] at h
    have h41 : (4:ℝ) ≤ 4*((N:ℝ)*t)^2 := by linarith [M2]
    have h4 : 4 + 32*t/(N:ℝ)^2 ≤ 36*((N:ℝ)*t)^2 := by linarith [h41, hA2]
    calc (2*vwM2+1)/d ≤ (2*vwM2+1)*(4 + 32*t/(N:ℝ)^2) := h1
      _ ≤ (2*vwM2+1)*(36*((N:ℝ)*t)^2) := mul_le_mul_of_nonneg_left h4 hc
      _ = 36*(2*vwM2+1)*((N:ℝ)*t)^2 := by ring
  -- term B'
  have hB : (t/((N:ℝ)-d)^2)/Real.pi ≤ ((N:ℝ)*t)^2 := by
    have h1 : t/((N:ℝ)-d)^2 ≤ 2*t := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ((N:ℝ)-d)^2)]
      nlinarith [ha2, ht0]
    have h2 : (t/((N:ℝ)-d)^2)/Real.pi ≤ t := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [h1, Real.pi_gt_three, ht0]
    linarith [h2, htM]
  -- term C'
  have hC : (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(2*Real.pi) ≤ 2*((N:ℝ)*t)^2 := by
    have h1 : 2*t/((N:ℝ)-d)^3 ≤ 2*t/((3:ℝ)/4)^3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [ha3, ht0]
    have h2 : 2*t/((3:ℝ)/4)^3 = (128/27)*t := by field_simp; ring
    rw [h2] at h1
    have h3 : (2*(N:ℝ))*(2*t/((N:ℝ)-d)^3)/(2*Real.pi)
        ≤ (2*(N:ℝ))*((128/27)*t)/(2*Real.pi) := by
      apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 2*Real.pi)
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : (2*(N:ℝ))*((128/27)*t)/(2*Real.pi) ≤ (2:ℝ)*((N:ℝ)*t) := by
      have e : (2*(N:ℝ))*((128/27)*t)/(2*Real.pi) = (128/(27*Real.pi))*((N:ℝ)*t) := by
        field_simp; try ring
      rw [e]
      have h5 : (128:ℝ)/(27*Real.pi) ≤ 2 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 27*Real.pi)]
        nlinarith [Real.pi_gt_three]
      exact mul_le_mul_of_nonneg_right h5 (by positivity)
    have h5 : (2:ℝ)*((N:ℝ)*t) ≤ 2*((N:ℝ)*t)^2 := by
      have h6 : (N:ℝ)*t ≤ ((N:ℝ)*t)^2 := by nlinarith [heta]
      linarith [h6]
    linarith [h3, h4, h5]
  -- term D'
  have hD : (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(2*Real.pi)^2 ≤ ((N:ℝ)*t)^2 := by
    have h1 : (t/((N:ℝ)-d)^2)^2 ≤ (t/((3:ℝ)/4)^2)^2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [ha2, ht0]
    have h2 : (t/((3:ℝ)/4)^2)^2 = (256/81)*(t^2) := by field_simp; ring
    rw [h2] at h1
    have h3 : (2*(N:ℝ))*(t/((N:ℝ)-d)^2)^2/(2*Real.pi)^2
        ≤ (2*(N:ℝ))*((256/81)*(t^2))/(2*Real.pi)^2 := by
      apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ (2*Real.pi)^2)
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : (2*(N:ℝ))*((256/81)*(t^2))/(2*Real.pi)^2 ≤ ((N:ℝ)*t)^2 := by
      have e : (2*(N:ℝ))*((256/81)*(t^2))/(2*Real.pi)^2
          = (512/(81*(2*Real.pi)^2))*((N:ℝ)*t^2) := by
        field_simp; try ring
      rw [e]
      have h5 : (512:ℝ)/(81*(2*Real.pi)^2) ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < 81*(2*Real.pi)^2)]
        nlinarith [Real.pi_gt_three]
      have h6 : (0:ℝ) ≤ (N:ℝ)*t^2 := by positivity
      have h7 : (N:ℝ)*t^2 ≤ ((N:ℝ)*t)^2 := by nlinarith [hNM]
      nlinarith [h5, h6, h7]
    linarith [h3, h4]
  rw [vdcKcf]
  have hK : (40*(2*vwM2+1) + 200) * (((N:ℝ)*t)^2)
      = 40*(2*vwM2+1)*(((N:ℝ)*t)^2) + 200*(((N:ℝ)*t)^2) := by ring
  rw [hK]
  nlinarith [hA, hB, hC, hD, hc, M2]


/-- **Finset-level bound for the complement of the dual range.** -/
theorem finset_compl_le {d : ℝ} {N : ℕ} {t : ℝ} {C1 : ℝ} (hN : 1 ≤ N) (ht : 100 ≤ t)
    (hd : 0 < d) (hd1 : d ≤ 1/2) (hd0 : d ≤ 1/4) (hd2 : (1:ℝ)/2 < (N:ℝ) - d)
    (htd : t*d ≤ (N:ℝ)^2/32)
    (hC1nn : 0 ≤ C1)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t)
    {F : Finset ℤ} (hF : ∀ k ∈ F, k ∉ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
        ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)) :
    ∑ k ∈ F, ‖vdcI d N t k‖ ≤ 100*(C1+170)*(N:ℝ)/Real.sqrt t + 8*(C1+170)*(N:ℝ)/Real.sqrt t
      + 20*(N:ℝ)/t
      + (4/Real.pi)*(1 + Real.log (2 + t/(2*Real.pi*(2*(N:ℝ)+d))))
      + (4/Real.pi)*(3 + Real.log (2 + vdcKc d N t/(2*Real.pi)))
      + (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi))) := by
  have ha0 : (0:ℝ) ≤ t/(4*Real.pi*(N:ℝ)) := by positivity
  have hb0 : (0:ℝ) ≤ t/(2*Real.pi*(N:ℝ)) := by positivity
  have hA2 : ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℝ) ≤ t/(4*Real.pi*(N:ℝ)) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one ha0)
  have hA3 : ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℝ) - 1 < t/(4*Real.pi*(N:ℝ)) := by
    have h := Nat.ceil_lt_add_one ha0; linarith
  have hK2 : ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℝ) ≤ t/(2*Real.pi*(N:ℝ)) :=
    Nat.floor_le hb0
  have hK3 : t/(2*Real.pi*(N:ℝ)) < ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  set A : ℤ := ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ) with hAdef
  set K : ℤ := ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ) with hKdef
  set F₁ : Finset ℤ := F.filter (fun k => k ≤ 0) with hF1
  set F₂ : Finset ℤ := F.filter (fun k => 1 ≤ k ∧ k < A) with hF2
  set F₃ : Finset ℤ := F.filter (fun k => K < k) with hF3
  have hB : (F.filter (fun k => ¬ k ≤ 0)).filter (fun k => k < A) = F₂ := by
    rw [hF2]
    ext k
    simp only [Finset.mem_filter]
    constructor
    · intro h; exact ⟨h.1.1, by omega, h.2⟩
    · intro h; exact ⟨⟨h.1, by omega⟩, h.2.2⟩
  have hC : ((F.filter (fun k => ¬ k ≤ 0)).filter (fun k => ¬ k < A)) ⊆ F₃ := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_filter] at hk
    obtain ⟨⟨hkF, hk0⟩, hkA⟩ := hk
    rw [hF3, Finset.mem_filter]
    refine ⟨hkF, ?_⟩
    have hkI : ¬ (A ≤ k ∧ k ≤ K) := by
      intro hcon
      exact hF k hkF (by rwa [Finset.mem_Icc])
    rcases not_and_or.mp hkI with h | h
    · omega
    · omega
  have hgoal : ∑ k ∈ F, ‖vdcI d N t k‖
      ≤ ∑ k ∈ F₁, ‖vdcI d N t k‖ + ∑ k ∈ F₂, ‖vdcI d N t k‖
        + ∑ k ∈ F₃, ‖vdcI d N t k‖ := by
    have h1 : ∑ k ∈ F, ‖vdcI d N t k‖
        = ∑ k ∈ F₁, ‖vdcI d N t k‖ + ∑ k ∈ F.filter (fun k => ¬ k ≤ 0), ‖vdcI d N t k‖ := by
      rw [hF1]
      exact (Finset.sum_filter_add_sum_filter_not F (fun k => k ≤ 0) _).symm
    have h2 : ∑ k ∈ F.filter (fun k => ¬ k ≤ 0), ‖vdcI d N t k‖
        = ∑ k ∈ F₂, ‖vdcI d N t k‖
          + ∑ k ∈ (F.filter (fun k => ¬ k ≤ 0)).filter (fun k => ¬ k < A),
              ‖vdcI d N t k‖ := by
      rw [← hB]
      exact (Finset.sum_filter_add_sum_filter_not _ (fun k => k < A) _).symm
    have h3 : ∑ k ∈ (F.filter (fun k => ¬ k ≤ 0)).filter (fun k => ¬ k < A),
        ‖vdcI d N t k‖ ≤ ∑ k ∈ F₃, ‖vdcI d N t k‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hC (fun k _ _ => norm_nonneg _)
    linarith [h1, h2, h3]
  have b1 := finset_nonpos_le (d := d) (N := N) (t := t) hN ht hd hd1 hd2 (F := F₁) (fun k hk => by
    rw [hF1, Finset.mem_filter] at hk; exact hk.2)
  have b2 := finset_right_le (d := d) (N := N) (t := t) hN ht hd hd1 hd0 hd2 htd hC1nn hC1
    (A := Nat.ceil (t/(4*Real.pi*(N:ℝ)))) hA2 hA3 (F := F₂) (fun k hk => by
    rw [hF2, Finset.mem_filter] at hk
    exact ⟨hk.2.1, hk.2.2⟩)
  have b3 := finset_left_le (d := d) (N := N) (t := t) hN ht hd hd1 hd0 hd2 htd hC1nn hC1
    (K := Nat.floor (t/(2*Real.pi*(N:ℝ)))) hK2 hK3 (F := F₃) (fun k hk => by
    rw [hF3, Finset.mem_filter] at hk
    exact hk.2)
  linarith [hgoal, b1, b2, b3]


/-- **The complementary Poisson series is `O(N/√t + log (N t) + 1)`.** -/
theorem tsum_compl_bound
    (C1 : ℝ) (hC1nn : 0 ≤ C1)
    (hC1 : ∀ (t p z : ℝ), 2 ≤ t → 1/4 ≤ p → p ≤ z → z ≤ 1 →
      ‖∫ s in p..z, vdcPhase t s‖ ≤ C1/Real.sqrt t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℝ), 0 < d → d ≤ 1/4 → ∀ (N : ℕ), 1 ≤ N →
      ∀ (t : ℝ), 100 ≤ t → (N:ℝ) ≤ t →
      (1:ℝ)/2 < (N:ℝ) - d → t*d ≤ (N:ℝ)^2/32 → 1/d ≤ 4 + 32*t/(N:ℝ)^2 →
      ‖∑' k : {k : ℤ // k ∉ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
          ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)}, vdcI d N t (k:ℤ)‖
        ≤ C * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) := by
  set Kc : ℝ := (40*(2*vwM2+1)+200)/(2*Real.pi) with hKcdef
  set Kf : ℝ := (40*(2*vwM2+1)+200)*Real.pi/4 with hKfdef
  have hKc1 : (1:ℝ) ≤ Kc := by
    rw [hKcdef]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)]
    nlinarith [Real.pi_lt_four, vwM2_nonneg]
  have hKf1 : (1:ℝ) ≤ Kf := by
    rw [hKfdef]
    nlinarith [Real.pi_gt_three, vwM2_nonneg]
  have hlogKc : (0:ℝ) ≤ Real.log (2 + Kc) := Real.log_nonneg (by linarith)
  have hlogKf : (0:ℝ) ≤ Real.log (2 + Kf) := Real.log_nonneg (by linarith)
  set Cc : ℝ := 108*(C1+170) + 20 + 12/Real.pi
      + (4/Real.pi)*(5 + Real.log (2 + Kc)) + (4/Real.pi)*(5 + Real.log (2 + Kf)) with hCcdef
  have hT3 : (0:ℝ) ≤ (4/Real.pi)*(5 + Real.log (2 + Kc)) :=
    mul_nonneg (by positivity) (by linarith)
  have hT4 : (0:ℝ) ≤ (4/Real.pi)*(5 + Real.log (2 + Kf)) :=
    mul_nonneg (by positivity) (by linarith)
  have hT1 : (0:ℝ) ≤ 108*(C1+170) + 20 := by linarith [hC1nn]
  have hT1' : (0:ℝ) < 108*(C1+170) + 20 := by linarith [hC1nn]
  have hT2 : (0:ℝ) ≤ 12/Real.pi := by positivity
  have hCc_pos : (0:ℝ) < Cc := by rw [hCcdef]; linarith
  have hCc1 : 108*(C1+170) + 20 ≤ Cc := by rw [hCcdef]; linarith
  have hCc2 : 12/Real.pi ≤ Cc := by rw [hCcdef]; linarith
  have hCc3 : (4/Real.pi)*(5 + Real.log (2 + Kc)) ≤ Cc := by rw [hCcdef]; linarith
  have hCc4 : (4/Real.pi)*(5 + Real.log (2 + Kf)) ≤ Cc := by rw [hCcdef]; linarith
  have hCsum : 12/Real.pi + (4/Real.pi)*(5 + Real.log (2 + Kc))
      + (4/Real.pi)*(5 + Real.log (2 + Kf)) ≤ Cc := by rw [hCcdef]; linarith
  refine ⟨Cc, hCc_pos, ?_⟩
  intro d hd hd0 N hN t ht hNt hd2 htd hdinv
  have hd1 : d ≤ 1/2 := le_trans hd0 (by norm_num)
  have ht1 : (1:ℝ) ≤ t := by linarith
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have heta : (1:ℝ) ≤ (N:ℝ)*t := by
    have h : (0:ℝ) ≤ ((N:ℝ) - 1)*(t - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h, hN1, ht1]
  set M : ℝ := (N:ℝ)*t with hMdef
  have hY1 : (1:ℝ) ≤ M := by rw [hMdef]; exact heta
  have hlogM : (0:ℝ) ≤ Real.log M := Real.log_nonneg hY1
  have hfin : ∀ F : Finset {k : ℤ // k ∉ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
      ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)},
      ∑ k ∈ F, ‖vdcI d N t (k:ℤ)‖
        ≤ 100*(C1+170)*(N:ℝ)/Real.sqrt t + 8*(C1+170)*(N:ℝ)/Real.sqrt t + 20*(N:ℝ)/t
          + (4/Real.pi)*(1 + Real.log (2 + t/(2*Real.pi*(2*(N:ℝ)+d))))
          + (4/Real.pi)*(3 + Real.log (2 + vdcKc d N t/(2*Real.pi)))
          + (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi))) := by
    intro F
    have hinj : Set.InjOn (fun k : {k : ℤ // k ∉ Finset.Icc
        ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
        ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)} => (k:ℤ)) (F : Set _) := by
      intro a _ b _ h; exact Subtype.ext h
    have h1 : ∑ z ∈ F.image (fun k : {k : ℤ // k ∉ Finset.Icc
          ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
          ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)} => (k:ℤ)), ‖vdcI d N t z‖
        = ∑ k ∈ F, ‖vdcI d N t (k:ℤ)‖ :=
      Finset.sum_image hinj
    rw [← h1]
    exact finset_compl_le (d := d) (N := N) (t := t) (C1 := C1) hN ht hd hd1 hd0 hd2
      htd hC1nn hC1 (F := F.image (fun k : {k : ℤ // k ∉ Finset.Icc
          ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
          ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)} => (k:ℤ))) (fun z hz => by
        rw [Finset.mem_image] at hz
        obtain ⟨k, _, rfl⟩ := hz
        exact k.2)
  have hsub : ‖∑' k : {k : ℤ // k ∉ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
        ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)}, vdcI d N t (k:ℤ)‖
      ≤ ∑' k : {k : ℤ // k ∉ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
        ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)}, ‖vdcI d N t (k:ℤ)‖ :=
    norm_tsum_le_tsum_norm (((summable_vdcI N hd hd1 hN t).norm).subtype _)
  have htsum := Real.tsum_le_of_sum_le
    (f := fun k : {k : ℤ // k ∉ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
        ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)} => ‖vdcI d N t (k:ℤ)‖)
    (fun k => norm_nonneg _) hfin
  -- log comparisons
  have hlogc : (4/Real.pi)*(1 + Real.log (2 + t/(2*Real.pi*(2*(N:ℝ)+d))))
      ≤ (12/Real.pi) * (Real.log M + 1) := by
    have hXnn : (0:ℝ) ≤ t/(2*Real.pi*(2*(N:ℝ)+d)) := by positivity
    have hc1 : (1:ℝ) ≤ 2*Real.pi*(2*(N:ℝ)+d) := by
      nlinarith [Real.pi_gt_three, hN1, hd.le]
    have hstep : t/(2*Real.pi*(2*(N:ℝ)+d)) ≤ t := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(2*(N:ℝ)+d))]
      nlinarith [hc1, ht1]
    have hXY : t/(2*Real.pi*(2*(N:ℝ)+d)) ≤ M := by
      rw [hMdef]; nlinarith [hstep, ht1, hN1]
    have h := Commons.Analysis.Log.log_two_add_le (X := t/(2*Real.pi*(2*(N:ℝ)+d)))
      (Y := M) hXnn hY1 hXY
    have h1 : (4/Real.pi)*(1 + Real.log (2 + t/(2*Real.pi*(2*(N:ℝ)+d))))
        ≤ (4/Real.pi)*(3*((Real.log M) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [h, hlogM]
    have h2 : (4/Real.pi)*(3*((Real.log M) + 1)) = (12/Real.pi)*((Real.log M) + 1) := by
      ring
    linarith [h1, h2]
  have hXa : vdcKc d N t/(2*Real.pi) ≤ Kc * M^2 := by
    have h := vdcKc_le (d := d) hN ht1 hNt hd hd0 hdinv
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)]
    have e : Kc * M^2 * (2*Real.pi) = (40*(2*vwM2+1)+200) * ((N:ℝ)*t)^2 := by
      rw [hKcdef, hMdef]
      field_simp; try ring
    rw [e]
    exact h
  have hloga : (4/Real.pi)*(3 + Real.log (2 + vdcKc d N t/(2*Real.pi)))
      ≤ (4/Real.pi)*(5 + Real.log (2 + Kc)) * (Real.log M + 1) := by
    have hXnn : (0:ℝ) ≤ vdcKc d N t/(2*Real.pi) :=
      div_nonneg (vdcKc_nonneg hd hN (by linarith) hd1) (by positivity)
    have h := log_two_add_le_sq' (X := vdcKc d N t/(2*Real.pi)) (Y := M) (K := Kc)
      hKc1 hXnn hY1 hXa
    have h1 : (3:ℝ) + Real.log (2 + vdcKc d N t/(2*Real.pi))
        ≤ (5 + Real.log (2 + Kc)) * (Real.log M + 1) := by nlinarith [h, hlogM]
    calc (4/Real.pi)*(3 + Real.log (2 + vdcKc d N t/(2*Real.pi)))
        ≤ (4/Real.pi)*((5 + Real.log (2 + Kc)) * (Real.log M + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (4/Real.pi)*(5 + Real.log (2 + Kc)) * (Real.log M + 1) := by ring
  have hXf : vdcKcf d N t/(4/Real.pi) ≤ Kf * M^2 := by
    have h := vdcKcf_le (d := d) hN ht1 hNt hd hd0 hdinv
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4/Real.pi)]
    have e : Kf * M^2 * (4/Real.pi) = (40*(2*vwM2+1)+200) * ((N:ℝ)*t)^2 := by
      rw [hKfdef, hMdef]
      field_simp; try ring
    rw [e]
    exact h
  have hlogf : (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi)))
      ≤ (4/Real.pi)*(5 + Real.log (2 + Kf)) * (Real.log M + 1) := by
    have hXnn : (0:ℝ) ≤ vdcKcf d N t/(4/Real.pi) :=
      div_nonneg (vdcKcf_nonneg hd hd1 hN (by linarith)) (by positivity)
    have h := log_two_add_le_sq' (X := vdcKcf d N t/(4/Real.pi)) (Y := M) (K := Kf)
      hKf1 hXnn hY1 hXf
    have h1 : (3:ℝ) + Real.log (2 + vdcKcf d N t/(4/Real.pi))
        ≤ (5 + Real.log (2 + Kf)) * (Real.log M + 1) := by nlinarith [h, hlogM]
    calc (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi)))
        ≤ (4/Real.pi)*((5 + Real.log (2 + Kf)) * (Real.log M + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (4/Real.pi)*(5 + Real.log (2 + Kf)) * (Real.log M + 1) := by ring
  -- the rational part
  have hNtt : 20*(N:ℝ)/t ≤ 20*(N:ℝ)/Real.sqrt t := by
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < t) (Real.sqrt_pos.mpr (by linarith))]
    have hs1 : (1:ℝ) ≤ Real.sqrt t := by
      nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ t), Real.sqrt_nonneg t, ht1]
    nlinarith [hs1, Real.sq_sqrt (by linarith : (0:ℝ) ≤ t), hN1, ht1]
  have hNt' : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t := by positivity
  have hsupt : (0:ℝ) ≤ Real.log M + 1 := by linarith
  have hRA : 108*(C1+170)*(N:ℝ)/Real.sqrt t + 20*(N:ℝ)/t ≤ Cc * ((N:ℝ)/Real.sqrt t) := by
    have h1 : 108*(C1+170)*(N:ℝ)/Real.sqrt t + 20*(N:ℝ)/Real.sqrt t
        = (108*(C1+170)+20)*((N:ℝ)/Real.sqrt t) := by ring
    have h2 := mul_le_mul_of_nonneg_right hCc1 hNt'
    nlinarith [hNtt, h1, h2]
  have hRL : (4/Real.pi)*(1 + Real.log (2 + t/(2*Real.pi*(2*(N:ℝ)+d))))
      + (4/Real.pi)*(3 + Real.log (2 + vdcKc d N t/(2*Real.pi)))
      + (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi)))
      ≤ Cc * (Real.log M + 1) := by
    have hsumL : (4/Real.pi)*(1 + Real.log (2 + t/(2*Real.pi*(2*(N:ℝ)+d))))
        + (4/Real.pi)*(3 + Real.log (2 + vdcKc d N t/(2*Real.pi)))
        + (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi)))
        ≤ (12/Real.pi + (4/Real.pi)*(5 + Real.log (2 + Kc))
            + (4/Real.pi)*(5 + Real.log (2 + Kf))) * (Real.log M + 1) := by
      have e : (12/Real.pi + (4/Real.pi)*(5 + Real.log (2 + Kc))
            + (4/Real.pi)*(5 + Real.log (2 + Kf))) * (Real.log M + 1)
          = (12/Real.pi)*(Real.log M + 1)
            + (4/Real.pi)*(5 + Real.log (2 + Kc))*(Real.log M + 1)
            + (4/Real.pi)*(5 + Real.log (2 + Kf))*(Real.log M + 1) := by ring
      linarith [hlogc, hloga, hlogf, e]
    have h2 := mul_le_mul_of_nonneg_right hCsum hsupt
    linarith [hsumL, h2]
  have hmain : 100*(C1+170)*(N:ℝ)/Real.sqrt t + 8*(C1+170)*(N:ℝ)/Real.sqrt t
      + 20*(N:ℝ)/t
      + (4/Real.pi)*(1 + Real.log (2 + t/(2*Real.pi*(2*(N:ℝ)+d))))
      + (4/Real.pi)*(3 + Real.log (2 + vdcKc d N t/(2*Real.pi)))
      + (4/Real.pi)*(3 + Real.log (2 + vdcKcf d N t/(4/Real.pi)))
      ≤ Cc * ((N:ℝ)/Real.sqrt t + Real.log M + 1) := by
    have e : Cc * ((N:ℝ)/Real.sqrt t + Real.log M + 1)
        = Cc * ((N:ℝ)/Real.sqrt t) + Cc * (Real.log M + 1) := by ring
    have e2 : 100*(C1+170)*(N:ℝ)/Real.sqrt t + 8*(C1+170)*(N:ℝ)/Real.sqrt t
        = 108*(C1+170)*(N:ℝ)/Real.sqrt t := by ring
    linarith [hRA, hRL, e, e2]
  rw [hMdef] at hmain
  refine le_trans (le_trans hsub htsum) ?_
  rw [hMdef]
  linarith [hmain]


/-- Reindexing `Σ_{k ∈ Icc A K ⊂ ℤ} vdcI k = Σ_{k ∈ Icc A K ⊂ ℕ} vdcI (k:ℤ)`. -/
lemma vdc_sum_Icc_eq (d : ℝ) (N : ℕ) (t : ℝ) (A K : ℕ) :
    ∑ k ∈ Finset.Icc ((A:ℤ)) ((K:ℤ)), vdcI d N t k
      = ∑ k ∈ Finset.Icc A K, vdcI d N t (k:ℤ) := by
  rw [← sum_Icc_int_eq_sum_Icc_nat' A K (fun m : ℕ => vdcI d N t (m:ℤ))]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_Icc] at hn
  have h0 : (0:ℤ) ≤ n := by
    have hA : (0:ℤ) ≤ (A:ℤ) := by exact_mod_cast Nat.zero_le A
    linarith [hn.1]
  rw [Int.toNat_of_nonneg h0]

/-- **The van der Corput transform error** (with the hypothesis `N ≤ t`):
`‖vdcS N t − vdcMain N t‖ = O(N/√t + log (N t) + 1)`. -/
theorem vdc_transform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ), (N : ℝ) ≤ t → 1 ≤ t →
      ‖vdcS N t - vdcMain N t‖
        ≤ C * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.Analysis.StationaryPhase.log_phase_half_line_left
  have hC1nn : (0:ℝ) ≤ C1 := le_of_lt hC1pos
  obtain ⟨Ci, hCipos, hCi⟩ := dual_interior_sum_bound C1 hC1nn hC1
  obtain ⟨Cc, hCcpos, hCcall⟩ := tsum_compl_bound C1 hC1nn hC1
  refine ⟨max 10000000 (Ci + Cc), lt_max_of_lt_left (by norm_num), ?_⟩
  intro N hN t hNt ht1
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have ht0 : (0:ℝ) < t := by linarith
  have hlog : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := Real.log_nonneg (by nlinarith)
  have hsqrtpos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hnonneg : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1 := by
    have h := div_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)) hsqrtpos.le
    linarith
  by_cases ht100 : t ≤ 100
  · have h := vdc_trivial_regime N hN t hNt ht100
    have hCge : (10000000:ℝ) ≤ max 10000000 (Ci + Cc) := le_max_left _ _
    nlinarith [h, hCge, hnonneg]
  · push_neg at ht100
    set dd : ℝ := min (1/4:ℝ) ((N:ℝ)^2/(32*t)) with hdd
    have hdd0 : (0:ℝ) < dd := by
      rw [hdd]; exact lt_min (by norm_num) (by positivity)
    have hdd4 : dd ≤ 1/4 := by rw [hdd]; exact min_le_left _ _
    have hdd2 : dd ≤ 1/2 := le_trans hdd4 (by norm_num)
    have hddle : dd ≤ (N:ℝ)^2/(32*t) := by rw [hdd]; exact min_le_right _ _
    have hddhalf : (1:ℝ)/2 < (N:ℝ) - dd := by linarith
    have hddhtd : t*dd ≤ (N:ℝ)^2/32 := by
      have h := mul_le_mul_of_nonneg_left hddle ht0.le
      have e : t * ((N:ℝ)^2/(32*t)) = (N:ℝ)^2/32 := by field_simp; try ring
      linarith [h, e]
    have hddiv : 1/dd ≤ 4 + 32*t/(N:ℝ)^2 := by
      have hbase : (0:ℝ) < 4 + 32*t/(N:ℝ)^2 := by positivity
      have hstep : 1/(4 + 32*t/(N:ℝ)^2) ≤ dd := by
        rw [hdd]
        apply le_min
        · rw [div_le_div_iff₀ hbase (by norm_num : (0:ℝ) < 4)]
          nlinarith [hbase, (by positivity : (0:ℝ) ≤ 32*t/(N:ℝ)^2)]
        · rw [div_le_div_iff₀ hbase (by positivity : (0:ℝ) < 32*t)]
          have h : (N:ℝ)^2*(4 + 32*t/(N:ℝ)^2) = 4*(N:ℝ)^2 + 32*t := by
            field_simp; try ring
          have hN2 : (0:ℝ) ≤ (N:ℝ)^2 := by positivity
          linarith [h, hN2]
      have := mul_le_mul_of_nonneg_left hstep hbase.le
      have he : (4 + 32*t/(N:ℝ)^2) * (1/(4 + 32*t/(N:ℝ)^2)) = 1 := by field_simp
      rw [he] at this
      exact (div_le_iff₀ hdd0).mpr this
    have hcompl := hCcall dd hdd0 hdd4 N hN t (by linarith) hNt hddhalf hddhtd hddiv
    have hinter := hCi dd hdd0 hdd2 N hN t (by linarith)
    have hbridge : ∑ k ∈ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
          ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ), vdcI dd N t k
        = ∑ k ∈ Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
            (Nat.floor (t/(2*Real.pi*(N:ℝ)))), vdcI dd N t (k:ℤ) :=
      vdc_sum_Icc_eq dd N t _ _
    have heq : vdcS N t - vdcMain N t
        = (∑ k ∈ Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
              (Nat.floor (t/(2*Real.pi*(N:ℝ)))),
            (vdcI dd N t (k:ℤ)
              - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t))
          + ∑' k : {k : ℤ // k ∉ Finset.Icc ((Nat.ceil (t/(4*Real.pi*(N:ℝ)))) : ℤ)
              ((Nat.floor (t/(2*Real.pi*(N:ℝ)))) : ℤ)}, vdcI dd N t (k:ℤ) := by
      rw [vdcMain_eq N hN t ht0, vdc_poisson_split (d := dd) N hdd0 hdd2 hN t, hbridge,
        Finset.sum_sub_distrib]
      ring
    rw [heq]
    have h1 : ‖∑ k ∈ Finset.Icc (Nat.ceil (t/(4*Real.pi*(N:ℝ))))
              (Nat.floor (t/(2*Real.pi*(N:ℝ)))),
            (vdcI dd N t (k:ℤ)
              - (((vdcX t k : ℝ)):ℂ)^((1:ℂ) + Complex.I * (t:ℂ)) * vdcF t)‖
        ≤ Ci * ((N:ℝ)/Real.sqrt t + Real.log ((N:ℝ)*t) + 1) :=
      le_trans (norm_sum_le _ _) hinter
    have hCge : Ci + Cc ≤ max 10000000 (Ci + Cc) := le_max_right _ _
    refine le_trans (norm_add_le _ _) ?_
    nlinarith [h1, hcompl, hCge, hnonneg]

/-- **The transform-error input** with the hypotheses needed for the main regime. -/
theorem transform_error_bound :
    ∃ CE : ℝ, 0 < CE ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ), (N : ℝ) ≤ t → 100 ≤ t →
      ‖vdcS N t - kappa t * vdcD N t‖
        ≤ CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1) := by
  obtain ⟨C, hC, h⟩ := vdc_transform_error
  refine ⟨C, hC, fun N hN t hNt ht => ?_⟩
  have h1 := h N hN t hNt (by linarith)
  simpa only [vdcMain, kappa] using h1

theorem fresnel_lower :
    ∃ T₀ c : ℝ, 100 ≤ T₀ ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ t : ℝ, T₀ ≤ t → c / Real.sqrt t ≤ ‖vdcF t‖ := by
  refine ⟨10^16, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  intro t ht
  have ht0 : (0:ℝ) < t := by linarith
  have ht2 : (2:ℝ) ≤ t := by linarith
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hlog : Real.log t ≤ 4 * t ^ (1/4:ℝ) := by
    have h := Real.log_le_rpow_div (x := t) (ε := 1/4) ht0.le (by norm_num)
    rw [show t ^ (1/4:ℝ) / (1/4) = 4 * t ^ (1/4:ℝ) by ring] at h
    exact h
  have ht4 : (4000:ℝ)^4 ≤ t := by norm_num; linarith
  have h4 : (4000:ℝ) ≤ t ^ (1/4:ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (4000:ℝ)^4) ht4 (by norm_num : (0:ℝ) ≤ (1/4:ℝ))
    have h1 : ((4000:ℝ)^4) ^ (1/4:ℝ) = 4000 := by
      rw [show ((4000:ℝ)^4) = (4000:ℝ)^((4:ℕ):ℝ) by rw [Real.rpow_natCast],
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4000),
        show ((4:ℕ):ℝ) * (1/4:ℝ) = 1 by norm_num, Real.rpow_one]
    rwa [h1] at h
  have hsq : t ^ (1/2:ℝ) = Real.sqrt t := by
    rw [← Real.sqrt_eq_rpow]
  have h4b : (4000:ℝ) * t ^ (1/4:ℝ) ≤ Real.sqrt t := by
    have h2 : t ^ (1/4:ℝ) * t ^ (1/4:ℝ) = t ^ (1/2:ℝ) := by
      rw [← Real.rpow_add (by positivity)]
      norm_num
    calc (4000:ℝ) * t ^ (1/4:ℝ) ≤ t ^ (1/4:ℝ) * t ^ (1/4:ℝ) :=
          mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg ht0.le _)
      _ = t ^ (1/2:ℝ) := h2
      _ = Real.sqrt t := hsq
  -- main term
  have hcrit := Commons.Analysis.StationaryPhase.critical_region_bound (A := fun _ : ℝ => (1:ℂ)) ht2
    contDiff_const (fun y => by simp) (fun y => by simp)
  simp only [norm_one, one_mul, Complex.ofReal_one] at hcrit
  -- tails
  have hL := Commons.Analysis.StationaryPhase.log_phase_prim_left_general t (1/2) (3/4)
    (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hR := Commons.Analysis.StationaryPhase.log_phase_prim_right_general t (5/4) 6
    (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hL' : ‖∫ s in (1/2:ℝ)..(3/4), Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖ ≤ 96/t := by
    refine le_trans hL (le_trans (min_le_right _ _) ?_)
    have : t * (1 - 3/4) = t/4 := by ring
    rw [this, div_le_div_iff₀ (by positivity) ht0]
    ring_nf
    linarith
  have hR' : ‖∫ s in (5/4:ℝ)..6, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖ ≤ 576/t := by
    refine le_trans hR (le_trans (min_le_right _ _) ?_)
    have : t * (5/4 - 1) = t/4 := by ring
    rw [this]
    rw [div_le_div_iff₀ (by positivity) ht0]
    ring_nf
    linarith
  set E : ℝ → ℂ := fun y => Complex.exp (Complex.I * ((t * (Real.log y - y) : ℝ) : ℂ)) with hE
  have hEint : ∀ a b : ℝ, (1/2:ℝ) ≤ a → a ≤ 6 → (1/2:ℝ) ≤ b → b ≤ 6 →
      IntervalIntegrable E volume a b := by
    intro a b ha ha6 hb hb6
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [hE]
    rw [Set.uIcc] at hy
    have hy1 : (0:ℝ) < y := lt_of_lt_of_le (by norm_num) (le_trans (le_min ha hb) hy.1)
    have h1 : ContinuousAt (fun z : ℝ => Real.log z - z) y :=
      (Real.continuousAt_log (ne_of_gt hy1)).sub continuousAt_id
    have h2 : ContinuousAt (fun z : ℝ => (t * (Real.log z - z) : ℝ)) y := continuousAt_const.mul h1
    have h3 : ContinuousAt (fun z : ℝ => ((t * (Real.log z - z) : ℝ) : ℂ)) y :=
      Complex.continuous_ofReal.continuousAt.comp h2
    have h4 : ContinuousAt (fun z : ℝ => Complex.I * ((t * (Real.log z - z) : ℝ) : ℂ)) y :=
      continuousAt_const.mul h3
    exact (Complex.continuous_exp.continuousAt.comp h4).continuousWithinAt
  have hsplit : vdcF t = (∫ y in (1/2:ℝ)..(3/4), E y) + (∫ y in (3/4:ℝ)..(5/4), E y)
      + (∫ y in (5/4:ℝ)..6, E y) := by
    rw [vdcF, hE]
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hEint (1/2) (5/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
          (hEint (5/4) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num))]
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hEint (1/2) (3/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
          (hEint (3/4) (5/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))]
  -- Efun matching
  have hEfun : (∫ y in (3/4:ℝ)..(5/4), E y)
      = ∫ y in (3/4:ℝ)..(5/4), Commons.Analysis.StationaryPhase.Efun t y := by
    apply intervalIntegral.integral_congr
    intro y _
    rw [hE, Commons.Analysis.StationaryPhase.Efun]
    congr 1
    push_cast
    ring
  have hcrit2 : ‖(∫ y in (3/4:ℝ)..(5/4), E y)
      - ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * Complex.I)
          * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      ≤ 1000 * (Real.log t / t) := by
    rw [hEfun]
    convert hcrit using 2 <;> ring_nf
  rw [hsplit]
  have hnorm : ‖(∫ y in (3/4:ℝ)..(5/4), E y)‖
      ≥ Real.sqrt (2 * Real.pi / t) - 1000 * (Real.log t / t) := by
    have h1 : ‖((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * Complex.I)
        * Complex.exp (-(Real.pi / 4) * Complex.I)‖ = Real.sqrt (2 * Real.pi / t) := by
      have h2 : ‖((Real.sqrt (2*Real.pi/t) : ℝ) : ℂ)‖ = Real.sqrt (2*Real.pi/t) := by
        rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (Real.sqrt_nonneg _)]
      have h3 : ‖Complex.exp (-(t : ℂ) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      have h4 : ‖Complex.exp (-(Real.pi/4) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [norm_mul, norm_mul, h2, h3, h4, mul_one, mul_one]
    have h2 : ‖((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * Complex.I)
        * Complex.exp (-(Real.pi / 4) * Complex.I)‖
        ≤ ‖∫ y in (3/4:ℝ)..(5/4), E y‖
          + ‖((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * Complex.I)
            * Complex.exp (-(Real.pi / 4) * Complex.I) - ∫ y in (3/4:ℝ)..(5/4), E y‖ := by
      have h := norm_add_le
        ((((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * Complex.I)
          * Complex.exp (-(Real.pi / 4) * Complex.I)) - ∫ y in (3/4:ℝ)..(5/4), E y)
        (∫ y in (3/4:ℝ)..(5/4), E y)
      rw [sub_add_cancel] at h
      linarith [h]
    rw [h1] at h2
    rw [norm_sub_rev] at hcrit2
    linarith [hcrit2]
  have hL2 : ‖∫ y in (1/2:ℝ)..(3/4), E y‖ ≤ 96/t := by
    rw [hE]; exact hL'
  have hR2 : ‖∫ y in (5/4:ℝ)..6, E y‖ ≤ 576/t := by
    rw [hE]; exact hR'
  have htri : ‖(∫ y in (1/2:ℝ)..(3/4), E y) + (∫ y in (3/4:ℝ)..(5/4), E y)
      + (∫ y in (5/4:ℝ)..6, E y)‖ ≥ ‖(∫ y in (3/4:ℝ)..(5/4), E y)‖ - 96/t - 576/t := by
    have h1 : ‖(∫ y in (1/2:ℝ)..(3/4), E y) + (∫ y in (3/4:ℝ)..(5/4), E y)‖
        ≤ ‖(∫ y in (1/2:ℝ)..(3/4), E y) + (∫ y in (3/4:ℝ)..(5/4), E y)
            + (∫ y in (5/4:ℝ)..6, E y)‖ + ‖∫ y in (5/4:ℝ)..6, E y‖ := by
      have := norm_sub_le ((∫ y in (1/2:ℝ)..(3/4), E y) + (∫ y in (3/4:ℝ)..(5/4), E y)
        + (∫ y in (5/4:ℝ)..6, E y)) (∫ y in (5/4:ℝ)..6, E y)
      simpa using this
    have h2 : ‖(∫ y in (3/4:ℝ)..(5/4), E y)‖
        ≤ ‖(∫ y in (1/2:ℝ)..(3/4), E y) + (∫ y in (3/4:ℝ)..(5/4), E y)‖
          + ‖∫ y in (1/2:ℝ)..(3/4), E y‖ := by
      have := norm_sub_le ((∫ y in (1/2:ℝ)..(3/4), E y) + (∫ y in (3/4:ℝ)..(5/4), E y))
        (∫ y in (1/2:ℝ)..(3/4), E y)
      simpa using this
    linarith [hL2, hR2]
  -- arithmetic
  have h1000 : 1000 * Real.log t ≤ Real.sqrt t := by
    have h1 := mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 1000)
    linarith [h4b]
  have h1344 : (1344:ℝ) ≤ Real.sqrt t := by
    have h4 : Real.sqrt (1344^2) ≤ Real.sqrt t := by
      apply Real.sqrt_le_sqrt; nlinarith
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1344)] at h4
  -- 1000 log t / t ≤ 1/√t
  have hA1 : 1000 * (Real.log t / t) ≤ 1 / Real.sqrt t := by
    have h5 : 1000 * (Real.log t / t) * Real.sqrt t = (1000 * Real.log t * Real.sqrt t)/t := by ring
    have hb1 : 1000 * (Real.log t / t) * Real.sqrt t ≤ 1 := by
      rw [h5, div_le_one ht0]
      calc 1000 * Real.log t * Real.sqrt t ≤ Real.sqrt t * Real.sqrt t :=
            mul_le_mul_of_nonneg_right h1000 (Real.sqrt_nonneg t)
        _ = t := by rw [← sq, Real.sq_sqrt ht0.le]
    rw [le_div_iff₀ hsqrt_pos]
    exact hb1
  -- 672/t ≤ (1/2)/√t
  have hA2 : 672/t ≤ (1/2) / Real.sqrt t := by
    have h6 : (1/2) / Real.sqrt t * t = (1/2) * Real.sqrt t := by
      field_simp
      nlinarith [Real.sq_sqrt ht0.le]
    rw [div_le_iff₀ ht0, h6]
    linarith [h1344]
  have h672 : (96:ℝ)/t + 576/t = 672/t := by rw [← add_div]; norm_num
  have h2pi : (2:ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hsq2 : Real.sqrt (2 * Real.pi / t) = Real.sqrt (2 * Real.pi) / Real.sqrt t :=
    Real.sqrt_div (by positivity) t
  have hroot : (1/2:ℝ) / Real.sqrt t
      ≤ Real.sqrt (2*Real.pi) / Real.sqrt t - 1000*(Real.log t/t) - 672/t := by
    have h1 : (1/2:ℝ) / Real.sqrt t + 1000*(Real.log t/t) + 672/t
        ≤ Real.sqrt (2*Real.pi) / Real.sqrt t := by
      have hs : 1000*(Real.log t/t) + 672/t ≤ 1/Real.sqrt t + (1/2)/Real.sqrt t := by
        linarith [hA1, hA2]
      have h7 : (1/2:ℝ)/Real.sqrt t + (1/Real.sqrt t + (1/2)/Real.sqrt t) = 2/Real.sqrt t := by ring
      have h9 : (2:ℝ)/Real.sqrt t ≤ Real.sqrt (2*Real.pi)/Real.sqrt t := by
        rw [div_le_div_iff₀ hsqrt_pos hsqrt_pos]
        nlinarith [h2pi, hsqrt_pos]
      linarith [hs, h7, h9]
    linarith [h1]
  have hgoal : ‖vdcF t‖ ≥ (1/2:ℝ) / Real.sqrt t := by
    rw [hsplit]
    have h1 : ‖((∫ y in (1/2:ℝ)..(3/4), E y) + (∫ y in (3/4:ℝ)..(5/4), E y)
        + (∫ y in (5/4:ℝ)..6, E y))‖
        ≥ Real.sqrt (2*Real.pi/t) - 1000*(Real.log t/t) - 672/t := by
      linarith [hnorm, htri, h672]
    rw [hsq2] at h1
    linarith [h1, hroot]
  linarith [hgoal]

/-- **The reduction**: a transform-error bound and the Fresnel lower bound imply the target. -/
theorem target_of_transform_error
    (herr : ∃ CE : ℝ, 0 < CE ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ), (N : ℝ) ≤ t → 100 ≤ t →
      ‖vdcS N t - kappa t * vdcD N t‖
        ≤ CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1))
    (hfres : ∃ T₀ c : ℝ, 100 ≤ T₀ ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ t : ℝ, T₀ ≤ t → c / Real.sqrt t ≤ ‖vdcF t‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ), (N : ℝ) ≤ t →
      Real.sqrt t * ‖vdcD N t‖
        ≤ C * (‖vdcS N t‖ + (N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1) := by
  obtain ⟨CE, hCEpos, hE⟩ := herr
  obtain ⟨T₀, c, hT₀, hcpos, hc1, hc⟩ := hfres
  refine ⟨max (Real.sqrt T₀ * (1 + 8*Real.pi)) ((2*Real.pi/c) * (CE + 1)), ?_, ?_⟩
  · refine lt_of_lt_of_le (by positivity) (le_max_left _ _)
  intro N hN t htN
  set X : ℝ := ‖vdcS N t‖ + (N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1 with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    have h21 : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t := by positivity
    have h22 : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := by
      apply Real.log_nonneg
      have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      nlinarith [htN]
    linarith [norm_nonneg (vdcS N t)]
  have hX1 : (1:ℝ) ≤ X := by
    rw [hX]
    have h21 : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t := by positivity
    have h22 : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := by
      apply Real.log_nonneg
      have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      nlinarith [htN]
    linarith [norm_nonneg (vdcS N t)]
  rcases lt_or_ge t T₀ with hT | hT
  · -- crude regime
    have hD : ‖vdcD N t‖ ≤ 1 + 8*Real.pi := vdcD_norm_le N hN t htN
    have hsqrt : Real.sqrt t ≤ Real.sqrt T₀ := Real.sqrt_le_sqrt hT.le
    have h1 : Real.sqrt t * ‖vdcD N t‖ ≤ Real.sqrt T₀ * (1 + 8*Real.pi) :=
      mul_le_mul hsqrt hD (norm_nonneg _) (Real.sqrt_nonneg _)
    have hC0 : 0 ≤ max (Real.sqrt T₀ * (1 + 8*Real.pi)) ((2*Real.pi/c) * (CE + 1)) := by
      positivity
    calc Real.sqrt t * ‖vdcD N t‖ ≤ Real.sqrt T₀ * (1 + 8*Real.pi) := h1
      _ ≤ max (Real.sqrt T₀ * (1 + 8*Real.pi)) ((2*Real.pi/c) * (CE + 1)) := le_max_left _ _
      _ = max (Real.sqrt T₀ * (1 + 8*Real.pi)) ((2*Real.pi/c) * (CE + 1)) * 1 := by ring
      _ ≤ max (Real.sqrt T₀ * (1 + 8*Real.pi)) ((2*Real.pi/c) * (CE + 1)) * X :=
          mul_le_mul_of_nonneg_left hX1 hC0
  · -- main regime
    have ht100 : (100:ℝ) ≤ t := le_trans hT₀ hT
    have ht1 : (0:ℝ) < t := by linarith
    have hFpos : (0:ℝ) < ‖vdcF t‖ := lt_of_lt_of_le (by positivity) (hc t hT)
    have hFsqrt : c ≤ ‖vdcF t‖ * Real.sqrt t := by
      have h := hc t hT
      have hsq : (c / Real.sqrt t) * Real.sqrt t = c :=
        div_mul_cancel₀ c (ne_of_gt (Real.sqrt_pos.mpr ht1))
      calc c = (c / Real.sqrt t) * Real.sqrt t := hsq.symm
        _ ≤ ‖vdcF t‖ * Real.sqrt t := mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg t)
    have hκnorm : ‖kappa t‖ = ‖vdcF t‖ * (t/(2*Real.pi)) := by
      rw [kappa, norm_mul, norm_cpow_one_add_I_mul (x := t/(2*Real.pi)) (by positivity) t]
      ring
    have hEbd : ‖vdcS N t - kappa t * vdcD N t‖
        ≤ CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1) := hE N hN t htN ht100
    have hkey : ‖vdcD N t‖ * ‖kappa t‖
        ≤ ‖vdcS N t‖ + CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1) := by
      have h1 : ‖kappa t * vdcD N t‖ ≤ ‖vdcS N t‖ + ‖vdcS N t - kappa t * vdcD N t‖ := by
        calc ‖kappa t * vdcD N t‖ = ‖vdcS N t - (vdcS N t - kappa t * vdcD N t)‖ := by
              congr 1; ring
          _ ≤ ‖vdcS N t‖ + ‖vdcS N t - kappa t * vdcD N t‖ := norm_sub_le _ _
      rw [norm_mul] at h1
      linarith
    have hDbd : ‖vdcD N t‖
        ≤ (‖vdcS N t‖ + CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1))
          / (‖vdcF t‖ * (t/(2*Real.pi))) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < ‖vdcF t‖ * (t/(2*Real.pi)))]
      rw [hκnorm] at hkey
      exact hkey
    have hstep : Real.sqrt t * ‖vdcD N t‖
        ≤ 2*Real.pi/(‖vdcF t‖ * Real.sqrt t)
            * (‖vdcS N t‖ + CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1)) := by
      calc Real.sqrt t * ‖vdcD N t‖
          ≤ Real.sqrt t * ((‖vdcS N t‖ + CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1))
              / (‖vdcF t‖ * (t/(2*Real.pi)))) :=
            mul_le_mul_of_nonneg_left hDbd (Real.sqrt_nonneg t)
        _ = 2*Real.pi/(‖vdcF t‖ * Real.sqrt t)
            * (‖vdcS N t‖ + CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1)) := by
            exact sqrt_div_model_smul ht1 ‖vdcF t‖
              (‖vdcS N t‖ + CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1)) hFpos
    have hcoef : 2*Real.pi/(‖vdcF t‖ * Real.sqrt t) ≤ 2*Real.pi/c := by
      rw [div_le_div_iff₀ (by positivity) hcpos]
      nlinarith [hFsqrt, Real.pi_pos]
    have hY0 : (0:ℝ) ≤ (N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1 := by
      have h21 : (0:ℝ) ≤ (N:ℝ)/Real.sqrt t := by positivity
      have h22 : (0:ℝ) ≤ Real.log ((N:ℝ)*t) := by
        apply Real.log_nonneg
        have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
        nlinarith [htN]
      linarith
    refine le_trans hstep ?_
    have harg : ‖vdcS N t‖ + CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1)
        ≤ (CE + 1) * X := by
      rw [hX]; nlinarith [hCEpos, norm_nonneg (vdcS N t), hY0]
    have harg0 : (0:ℝ) ≤ ‖vdcS N t‖ + CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1) := by
      nlinarith [hCEpos, norm_nonneg (vdcS N t), hY0]
    have h2 : 2*Real.pi/(‖vdcF t‖ * Real.sqrt t)
            * (‖vdcS N t‖ + CE * ((N : ℝ)/Real.sqrt t + Real.log ((N : ℝ)*t) + 1))
        ≤ 2*Real.pi/c * ((CE + 1) * X) := by
      exact mul_le_mul hcoef harg harg0 (le_trans (by positivity) hcoef)
    refine le_trans h2 ?_
    rw [show 2*Real.pi/c * ((CE + 1) * X) = (2*Real.pi/c * (CE + 1)) * X by ring]
    exact mul_le_mul_of_nonneg_right (le_max_right (Real.sqrt T₀ * (1 + 8*Real.pi))
      ((2*Real.pi/c) * (CE + 1))) hX0

/-- **The reverse van der Corput transform** (the assigned statement). -/
theorem vdc_transform_log_phase_reverse :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ), (N : ℝ) ≤ t →
      Real.sqrt t * ‖∑ k ∈ Finset.Icc (Nat.ceil (t / (4 * Real.pi * N)))
            (Nat.floor (t / (2 * Real.pi * N))),
            (k : ℂ) ^ (-(Complex.I * (t : ℂ))) / (k : ℂ)‖
        ≤ C * (‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (t : ℂ))‖
            + (N : ℝ) / Real.sqrt t + Real.log ((N : ℝ) * t) + 1) := by
  have h := target_of_transform_error transform_error_bound fresnel_lower
  simpa only [vdcD, vdcS] using h

end

end Commons.NumberTheory.DirichletPolynomial
