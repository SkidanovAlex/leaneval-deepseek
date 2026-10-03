/-
# Pointwise bounds for the differentiated model weight `m0w`  (Area A7)

This module proves `Work.A7.m0w_bound`: the pointwise bound and the second-derivative bound for
the weight

  `m0w P ξ₁ ξ₂ j₁ j₂ t = (2πi t)^{j₁} (2πi P(t))^{j₂} e(ξ₁t + ξ₂P(t))`

of the sharp `M₀` estimate of the §6 model approximation (`Submission/Work/A7/M0WBasic.lean`),
on `[0,N]`, under the frequency hypotheses `|ξ₁| ≤ 2^{k₁+1}/N`, `|ξ₂| ≤ 2^{d(k₂+1)}/N^d`
(`d = P.natDegree`) and for `j₁, j₂ ≤ 2`:

  `‖m0w u‖ ≤ C N^{j₁+dj₂}`  and  `‖(m0w)'' u‖ ≤ C N^{j₁+dj₂-2} (1 + S + S²)`, `S = Sval P k₁ k₂`.

The proof is the product rule for `m0w = m0poly · momFun`, together with the homogeneous bounds
for the two factors `m0f1 j₁ = (2πi t)^{j₁}` and `m0f2 P j₂ = (2πi P(t))^{j₂}` (and their first
two derivatives), which are proved here from the power rule, and the bounds on `PevalR` and
`momFun` (delegated to `A7/Pev/PevalR_deriv_bounds.lean` and `A7/Mom/momFun_deriv_bounds.lean`).
-/
import Mathlib
import Submission.Work.A7.M0WBasic
import Submission.Work.A7.Pev.PevalR_deriv_bounds
import Submission.Work.A7.Mom.momFun_deriv_bounds

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7

noncomputable section

open MeasureTheory Polynomial Finset Topology
open scoped BigOperators

/-! ## 1. Elementary analytic lemmas -/

/-- The norm of a real number seen in `ℂ` is its absolute value. -/
lemma norm_ofReal_eq_abs' (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  rw [← Real.sqrt_sq (norm_nonneg _), h1, Real.sqrt_sq_eq_abs]

/-- The norm of the constant `2πi`. -/
lemma norm_two_pi_I : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  rw [show (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I from by
    push_cast; ring]
  rw [norm_mul, Complex.norm_I, mul_one, norm_ofReal_eq_abs', abs_of_pos (by positivity)]

/-- `‖(2πi) · x‖ = 2π|x|` for real `x`. -/
lemma norm_two_pi_I_mul_ofReal (x : ℝ) :
    ‖(2 * Real.pi * Complex.I : ℂ) * ((x : ℝ) : ℂ)‖ = 2 * Real.pi * |x| := by
  rw [norm_mul, norm_two_pi_I, norm_ofReal_eq_abs']

/-- The derivative of `s ↦ ↑(g s)` is `s ↦ ↑(g' s)`, for differentiable `g`. -/
lemma deriv_ofReal_comp' (g : ℝ → ℝ) (hg : Differentiable ℝ g) (t : ℝ) :
    deriv (fun s : ℝ => ((g s : ℝ) : ℂ)) t = ((deriv g t : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ g t := hg.differentiableAt
  exact (hd.hasDerivAt.ofReal_comp).deriv

/-- The derivative of `s ↦ c * ↑(g s)` is `c * ↑(g' t)`. -/
lemma deriv_const_mul_ofReal (g : ℝ → ℝ) (c : ℂ) (t : ℝ) (hg : DifferentiableAt ℝ g t) :
    deriv (fun s : ℝ => c * ((g s : ℝ) : ℂ)) t = c * ((deriv g t : ℝ) : ℂ) :=
  ((hg.hasDerivAt.ofReal_comp).const_mul c).deriv

/-- The second iterated derivative of `s ↦ ↑(g s)` is `↑(g'' t)` for `C²` functions. -/
lemma iteratedDeriv_two_ofReal_comp (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => ((g s : ℝ) : ℂ)) t = ((iteratedDeriv 2 g t : ℝ) : ℂ) := by
  have h1 : deriv (fun s : ℝ => ((g s : ℝ) : ℂ)) = fun s : ℝ => ((deriv g s : ℝ) : ℂ) := by
    funext s
    have hd : DifferentiableAt ℝ g s := (hg.differentiable (by norm_num)).differentiableAt
    exact (hd.hasDerivAt.ofReal_comp).deriv
  have h2 : deriv (fun s : ℝ => ((deriv g s : ℝ) : ℂ))
      = fun s : ℝ => ((deriv (deriv g) s : ℝ) : ℂ) := by
    funext s
    have hd : DifferentiableAt ℝ (deriv g) s := by
      have h := hg.differentiable_iteratedDeriv' 1
      have h2 : deriv g = iteratedDeriv 1 g := by rw [iteratedDeriv_one]
      rw [h2]; exact h.differentiableAt
    exact (hd.hasDerivAt.ofReal_comp).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2, iteratedDeriv_succ, iteratedDeriv_one]

/-- The second iterated derivative of `s ↦ c * ↑(g s)` is `c * ↑(g'' t)`. -/
lemma iteratedDeriv_two_const_mul_ofReal (g : ℝ → ℝ) (c : ℂ) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => c * ((g s : ℝ) : ℂ)) t
      = c * ((iteratedDeriv 2 g t : ℝ) : ℂ) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_two_ofReal_comp g hg t]

/-! ## 2. The power bound -/

/-- **Power bound.**  If `v` has the homogeneous bounds `a`, `a/N`, `a/N²` at `t` (`a ≥ 0`,
`N > 0`) and `j ≤ 2`, then `v^j` has the homogeneous bounds `a^j`, `2a^j/N`, `4a^j/N²`. -/
lemma norm_pow_bounds {v : ℝ → ℂ} {t a N : ℝ} (ha : 0 ≤ a) (hN : 0 < N) {j : ℕ} (hj : j ≤ 2)
    (hv : ContDiffAt ℝ 2 v t) (hv0 : ‖v t‖ ≤ a) (hv1 : ‖deriv v t‖ ≤ a / N)
    (hv2 : ‖iteratedDeriv 2 v t‖ ≤ a / N ^ 2) :
    ‖v t ^ j‖ ≤ a ^ j ∧
    ‖deriv (fun s : ℝ => v s ^ j) t‖ ≤ 2 * a ^ j / N ∧
    ‖iteratedDeriv 2 (fun s : ℝ => v s ^ j) t‖ ≤ 4 * a ^ j / N ^ 2 := by
  interval_cases j
  · refine ⟨by simp, ?_, ?_⟩
    · simp only [pow_zero, mul_one]
      simp [deriv_const]
      positivity
    · simp only [pow_zero, mul_one]
      simp [iteratedDeriv_const]
      positivity
  · refine ⟨by simpa using hv0, ?_, ?_⟩
    · simp only [pow_one]
      exact le_trans hv1 (div_le_div_of_nonneg_right (by linarith) hN.le)
    · simp only [pow_one]
      exact le_trans hv2 (div_le_div_of_nonneg_right (by linarith) (by positivity))
  · have hv' : DifferentiableAt ℝ v t := hv.differentiableAt (by norm_num)
    have h2 : (fun s : ℝ => v s ^ 2) = v * v := by funext s; rw [pow_two, Pi.mul_apply]
    have hn1 : (0 : ℝ) ≤ a / N := div_nonneg ha hN.le
    have hn2 : (0 : ℝ) ≤ a / N ^ 2 := div_nonneg ha (by positivity)
    refine ⟨?_, ?_, ?_⟩
    · rw [pow_two, norm_mul, pow_two]
      exact mul_le_mul hv0 hv0 (norm_nonneg _) ha
    · rw [h2, deriv_mul hv' hv']
      calc ‖deriv v t * v t + v t * deriv v t‖
          ≤ ‖deriv v t * v t‖ + ‖v t * deriv v t‖ := norm_add_le _ _
        _ = ‖deriv v t‖ * ‖v t‖ + ‖v t‖ * ‖deriv v t‖ := by rw [norm_mul, norm_mul]
        _ ≤ (a / N) * a + a * (a / N) :=
              add_le_add (mul_le_mul hv1 hv0 (norm_nonneg _) hn1)
                         (mul_le_mul hv0 hv1 (norm_nonneg _) ha)
        _ = 2 * a ^ 2 / N := by field_simp; ring
    · rw [h2]
      rw [iteratedDeriv_mul hv hv]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
        Nat.choose_one_right, Nat.choose_self, iteratedDeriv_zero, iteratedDeriv_one, zero_add]
      norm_num
      have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
      have hX : ‖v t * iteratedDeriv 2 v t‖ ≤ a * (a / N ^ 2) := by
        rw [norm_mul]; exact mul_le_mul hv0 hv2 (norm_nonneg _) ha
      have hY : ‖2 * deriv v t * deriv v t‖ ≤ (2 * (a / N)) * (a / N) := by
        rw [norm_mul, norm_mul, h2c]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hv1 (by norm_num)) hv1 (norm_nonneg _)
          (mul_nonneg (by norm_num) hn1)
      have hZ : ‖iteratedDeriv 2 v t * v t‖ ≤ (a / N ^ 2) * a := by
        rw [norm_mul]; exact mul_le_mul hv2 hv0 (norm_nonneg _) hn2
      calc ‖v t * iteratedDeriv 2 v t + 2 * deriv v t * deriv v t + iteratedDeriv 2 v t * v t‖
          ≤ (a * (a / N ^ 2) + (2 * (a / N)) * (a / N)) + (a / N ^ 2) * a := by
            refine le_trans (norm_add_le _ _) (add_le_add ?_ hZ)
            exact le_trans (norm_add_le _ _) (add_le_add hX hY)
        _ = 4 * a ^ 2 / N ^ 2 := by field_simp; ring

/-- For `0 ≤ a` and `j ≤ 2`, `a^j ≤ max 1 (a^2)`. -/
lemma pow_le_max_sq {a : ℝ} (ha : 0 ≤ a) {j : ℕ} (hj : j ≤ 2) : a ^ j ≤ max 1 (a ^ 2) := by
  rcases le_or_gt a 1 with h | h
  · exact le_trans (pow_le_one₀ ha h) (le_max_left _ _)
  · exact le_trans (pow_le_pow_right₀ h.le hj) (le_max_right _ _)

/-! ## 3. The two factors of `m0poly` -/

/-- The first factor `(2πi t)^{j}` of `m0poly`. -/
noncomputable def m0f1 (j : ℕ) : ℝ → ℂ := fun s => (2 * Real.pi * Complex.I * (s : ℂ)) ^ j

/-- The second factor `(2πi P(t))^{j}` of `m0poly`. -/
noncomputable def m0f2 (P : Polynomial ℤ) (j : ℕ) : ℝ → ℂ :=
  fun s => (2 * Real.pi * Complex.I * ((Work.KMTAreas.A7.PevalR P s : ℝ) : ℂ)) ^ j

lemma contDiff_m0f1_inner :
    ContDiff ℝ 2 (fun s : ℝ => 2 * Real.pi * Complex.I * (s : ℂ)) :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_id)

lemma contDiff_m0f2_inner (P : Polynomial ℤ) :
    ContDiff ℝ 2 (fun s : ℝ => 2 * Real.pi * Complex.I * ((Work.KMTAreas.A7.PevalR P s : ℝ) : ℂ)) :=
  contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp ((contDiff_PevalR P).of_le (by norm_num)))

lemma contDiff_m0f1 (j : ℕ) : ContDiff ℝ 2 (m0f1 j) := contDiff_m0f1_inner.pow j

lemma contDiff_m0f2 (P : Polynomial ℤ) (j : ℕ) : ContDiff ℝ 2 (m0f2 P j) :=
  (contDiff_m0f2_inner P).pow j

lemma two_pi_pow_le (j : ℕ) (hj : j ≤ 2) : (2 * Real.pi) ^ j ≤ 64 := by
  interval_cases j <;> nlinarith [Real.pi_lt_four, Real.pi_pos]

/-- **Bounds for the first factor** `m0f1 j = (2πi t)^j` on `[0,N]`. -/
lemma m0f1_bounds {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (N : ℝ)) {j : ℕ}
    (hj : j ≤ 2) :
    ‖m0f1 j t‖ ≤ 400 * (N : ℝ) ^ j ∧
    ‖deriv (m0f1 j) t‖ ≤ 400 * (N : ℝ) ^ j / (N : ℝ) ∧
    ‖iteratedDeriv 2 (m0f1 j) t‖ ≤ 400 * (N : ℝ) ^ j / (N : ℝ) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hv0 : ‖2 * Real.pi * Complex.I * (t : ℂ)‖ ≤ 2 * Real.pi * (N : ℝ) := by
    rw [norm_two_pi_I_mul_ofReal t, abs_of_nonneg ht.1]
    nlinarith [Real.pi_pos, ht.2]
  have hv1 : ‖deriv (fun s : ℝ => 2 * Real.pi * Complex.I * (s : ℂ)) t‖
      ≤ (2 * Real.pi * (N : ℝ)) / (N : ℝ) := by
    have hd : deriv (fun s : ℝ => 2 * Real.pi * Complex.I * (s : ℂ)) t
        = 2 * Real.pi * Complex.I := by
      have h := (((hasDerivAt_id t).ofReal_comp).const_mul (2 * Real.pi * Complex.I)).deriv
      simpa using h
    rw [hd, norm_two_pi_I]
    rw [show 2 * Real.pi * (N : ℝ) / (N : ℝ) = 2 * Real.pi from by
      rw [mul_div_assoc, div_self (ne_of_gt hNpos), mul_one]]
  have hv2 : ‖iteratedDeriv 2 (fun s : ℝ => 2 * Real.pi * Complex.I * (s : ℂ)) t‖
      ≤ (2 * Real.pi * (N : ℝ)) / (N : ℝ) ^ 2 := by
    have h0 : iteratedDeriv 2 (fun s : ℝ => 2 * Real.pi * Complex.I * (s : ℂ)) t = 0 := by
      have hd : deriv (fun s : ℝ => 2 * Real.pi * Complex.I * (s : ℂ))
          = fun _ : ℝ => 2 * Real.pi * Complex.I := by
        funext s
        have h := (((hasDerivAt_id s).ofReal_comp).const_mul (2 * Real.pi * Complex.I)).deriv
        simpa using h
      rw [iteratedDeriv_succ, iteratedDeriv_one, hd, deriv_const]
    rw [h0, norm_zero]
    positivity
  obtain ⟨h0, h1, h2⟩ := norm_pow_bounds (v := fun s : ℝ => 2 * Real.pi * Complex.I * (s : ℂ))
    (t := t) (a := 2 * Real.pi * (N : ℝ)) (N := (N : ℝ)) (by positivity) hNpos hj
    contDiff_m0f1_inner.contDiffAt hv0 hv1 hv2
  have h64 : (2 * Real.pi) ^ j ≤ 64 := two_pi_pow_le j hj
  have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ j := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc ‖m0f1 j t‖ = ‖(fun s : ℝ => 2 * Real.pi * Complex.I * (s : ℂ)) t ^ j‖ := rfl
      _ ≤ (2 * Real.pi * (N : ℝ)) ^ j := h0
      _ = (2 * Real.pi) ^ j * (N : ℝ) ^ j := by rw [mul_pow]
      _ ≤ 64 * (N : ℝ) ^ j := mul_le_mul_of_nonneg_right h64 hNpow
      _ ≤ 400 * (N : ℝ) ^ j := by nlinarith [hNpow]
  · calc ‖deriv (m0f1 j) t‖
        ≤ 2 * (2 * Real.pi * (N : ℝ)) ^ j / (N : ℝ) := h1
      _ = 2 * ((2 * Real.pi) ^ j * (N : ℝ) ^ j) / (N : ℝ) := by rw [mul_pow]
      _ ≤ 400 * (N : ℝ) ^ j / (N : ℝ) := by
            apply div_le_div_of_nonneg_right _ hNpos.le
            nlinarith [h64, hNpow]
  · calc ‖iteratedDeriv 2 (m0f1 j) t‖
        ≤ 4 * (2 * Real.pi * (N : ℝ)) ^ j / (N : ℝ) ^ 2 := h2
      _ = 4 * ((2 * Real.pi) ^ j * (N : ℝ) ^ j) / (N : ℝ) ^ 2 := by rw [mul_pow]
      _ ≤ 400 * (N : ℝ) ^ j / (N : ℝ) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            nlinarith [h64, hNpow]

/-- **Bounds for the second factor** `m0f2 P j = (2πi P(t))^j` on `[0,N]`, from the bounds on
`PevalR` and its first two derivatives. -/
lemma m0f2_bounds (P : Polynomial ℤ) {A : ℝ} (hA : 0 ≤ A)
    (hval : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |Work.KMTAreas.A7.PevalR P t| ≤ A * (N : ℝ) ^ P.natDegree)
    (hP1 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |deriv (Work.KMTAreas.A7.PevalR P) t| ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ))
    (hP2 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t|
        ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2)
    {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (N : ℝ)) {j : ℕ} (hj : j ≤ 2) :
    ‖m0f2 P j t‖ ≤ 4 * max 1 ((2 * Real.pi * A) ^ 2) * (N : ℝ) ^ (P.natDegree * j) ∧
    ‖deriv (m0f2 P j) t‖
      ≤ 4 * max 1 ((2 * Real.pi * A) ^ 2) * (N : ℝ) ^ (P.natDegree * j) / (N : ℝ) ∧
    ‖iteratedDeriv 2 (m0f2 P j) t‖
      ≤ 4 * max 1 ((2 * Real.pi * A) ^ 2) * (N : ℝ) ^ (P.natDegree * j) / (N : ℝ) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hPA : (0 : ℝ) ≤ 2 * Real.pi * A := by positivity
  have hNpownn : (0 : ℝ) ≤ (N : ℝ) ^ P.natDegree := by positivity
  have hdiff : Differentiable ℝ (Work.KMTAreas.A7.PevalR P) :=
    Polynomial.differentiable (P.map (Int.castRingHom ℝ))
  have hcont : ContDiff ℝ 2 (Work.KMTAreas.A7.PevalR P) :=
    (contDiff_PevalR P).of_le (by norm_num)
  have hw0 : ‖2 * Real.pi * Complex.I * ((Work.KMTAreas.A7.PevalR P t : ℝ) : ℂ)‖
      ≤ 2 * Real.pi * A * (N : ℝ) ^ P.natDegree := by
    rw [norm_two_pi_I_mul_ofReal (Work.KMTAreas.A7.PevalR P t)]
    calc 2 * Real.pi * |Work.KMTAreas.A7.PevalR P t|
        ≤ 2 * Real.pi * (A * (N : ℝ) ^ P.natDegree) :=
          mul_le_mul_of_nonneg_left (hval N hN t ht) (by positivity)
      _ = 2 * Real.pi * A * (N : ℝ) ^ P.natDegree := by ring
  have hw1 : ‖deriv (fun s : ℝ => 2 * Real.pi * Complex.I * ((Work.KMTAreas.A7.PevalR P s : ℝ) : ℂ)) t‖
      ≤ 2 * Real.pi * A * (N : ℝ) ^ P.natDegree / (N : ℝ) := by
    rw [deriv_const_mul_ofReal (Work.KMTAreas.A7.PevalR P) (2 * Real.pi * Complex.I) t
      hdiff.differentiableAt]
    rw [norm_two_pi_I_mul_ofReal (deriv (Work.KMTAreas.A7.PevalR P) t)]
    calc 2 * Real.pi * |deriv (Work.KMTAreas.A7.PevalR P) t|
        ≤ 2 * Real.pi * (A * (N : ℝ) ^ P.natDegree / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (hP1 N hN t ht) (by positivity)
      _ = 2 * Real.pi * A * (N : ℝ) ^ P.natDegree / (N : ℝ) := by ring
  have hw2 : ‖iteratedDeriv 2
        (fun s : ℝ => 2 * Real.pi * Complex.I * ((Work.KMTAreas.A7.PevalR P s : ℝ) : ℂ)) t‖
      ≤ 2 * Real.pi * A * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2 := by
    rw [iteratedDeriv_two_const_mul_ofReal (Work.KMTAreas.A7.PevalR P) (2 * Real.pi * Complex.I)
      hcont t]
    rw [norm_two_pi_I_mul_ofReal (iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t)]
    calc 2 * Real.pi * |iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t|
        ≤ 2 * Real.pi * (A * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hP2 N hN t ht) (by positivity)
      _ = 2 * Real.pi * A * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2 := by ring
  obtain ⟨h0, h1, h2⟩ := norm_pow_bounds
    (v := fun s : ℝ => 2 * Real.pi * Complex.I * ((Work.KMTAreas.A7.PevalR P s : ℝ) : ℂ))
    (t := t) (a := 2 * Real.pi * A * (N : ℝ) ^ P.natDegree) (N := (N : ℝ))
    (mul_nonneg hPA hNpownn) hNpos hj (contDiff_m0f2_inner P).contDiffAt hw0 hw1 hw2
  have hK : (2 * Real.pi * A) ^ j ≤ 4 * max 1 ((2 * Real.pi * A) ^ 2) := by
    have hmax : (0 : ℝ) ≤ max 1 ((2 * Real.pi * A) ^ 2) :=
      le_trans (by norm_num) (le_max_left _ _)
    nlinarith [pow_le_max_sq hPA hj, hmax]
  have hNj : (0 : ℝ) ≤ (N : ℝ) ^ (P.natDegree * j) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc ‖m0f2 P j t‖
        = ‖(fun s : ℝ => 2 * Real.pi * Complex.I * ((Work.KMTAreas.A7.PevalR P s : ℝ) : ℂ)) t ^ j‖ :=
          rfl
      _ ≤ (2 * Real.pi * A * (N : ℝ) ^ P.natDegree) ^ j := h0
      _ = (2 * Real.pi * A) ^ j * (N : ℝ) ^ (P.natDegree * j) := by rw [mul_pow, pow_mul]
      _ ≤ (4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j) :=
          mul_le_mul_of_nonneg_right hK hNj
  · calc ‖deriv (m0f2 P j) t‖
        ≤ 2 * (2 * Real.pi * A * (N : ℝ) ^ P.natDegree) ^ j / (N : ℝ) := h1
      _ = 2 * ((2 * Real.pi * A) ^ j * (N : ℝ) ^ (P.natDegree * j)) / (N : ℝ) := by
          rw [mul_pow, pow_mul]
      _ ≤ 4 * max 1 ((2 * Real.pi * A) ^ 2) * (N : ℝ) ^ (P.natDegree * j) / (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ hNpos.le
          nlinarith [hK, hNj, pow_le_max_sq hPA hj]
  · calc ‖iteratedDeriv 2 (m0f2 P j) t‖
        ≤ 4 * (2 * Real.pi * A * (N : ℝ) ^ P.natDegree) ^ j / (N : ℝ) ^ 2 := h2
      _ = 4 * ((2 * Real.pi * A) ^ j * (N : ℝ) ^ (P.natDegree * j)) / (N : ℝ) ^ 2 := by
          rw [mul_pow, pow_mul]
      _ ≤ 4 * max 1 ((2 * Real.pi * A) ^ 2) * (N : ℝ) ^ (P.natDegree * j) / (N : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [hK, hNj, pow_le_max_sq hPA hj]

/-! ## 4. `m0poly` -/

lemma m0poly_eq_mul (P : Polynomial ℤ) (j₁ j₂ : ℕ) :
    m0poly P j₁ j₂ = m0f1 j₁ * m0f2 P j₂ := by
  funext t; rfl

/-- **Bounds for `m0poly = m0f1 j₁ · m0f2 P j₂` and its first two derivatives.** -/
lemma m0poly_bounds (P : Polynomial ℤ) {A : ℝ} (hA : 0 ≤ A)
    (hval : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |Work.KMTAreas.A7.PevalR P t| ≤ A * (N : ℝ) ^ P.natDegree)
    (hP1 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |deriv (Work.KMTAreas.A7.PevalR P) t| ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ))
    (hP2 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t|
        ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2)
    {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (N : ℝ)) {j₁ j₂ : ℕ}
    (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) :
    ‖m0poly P j₁ j₂ t‖
        ≤ 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (j₁ + P.natDegree * j₂) ∧
    ‖deriv (m0poly P j₁ j₂) t‖
        ≤ 2 * (400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)))
            * (N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ) ∧
    ‖iteratedDeriv 2 (m0poly P j₁ j₂) t‖
        ≤ 4 * (400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)))
            * (N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ) ^ 2 := by
  obtain ⟨hf1_0, hf1_1, hf1_2⟩ := m0f1_bounds hN ht hj₁
  obtain ⟨hf2_0, hf2_1, hf2_2⟩ := m0f2_bounds P hA hval hP1 hP2 hN ht hj₂
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hB1 : (0 : ℝ) ≤ 400 * (N : ℝ) ^ j₁ := by positivity
  have hC1 : (0 : ℝ) ≤ 400 * (N : ℝ) ^ j₁ / (N : ℝ) := by positivity
  have hB3 : (0 : ℝ) ≤ 400 * (N : ℝ) ^ j₁ / (N : ℝ) ^ 2 := by positivity
  have hd1 : DifferentiableAt ℝ (m0f1 j₁) t :=
    ((contDiff_m0f1 j₁).differentiable (by norm_num)).differentiableAt
  have hd2 : DifferentiableAt ℝ (m0f2 P j₂) t :=
    ((contDiff_m0f2 P j₂).differentiable (by norm_num)).differentiableAt
  have hcd1 : ContDiffAt ℝ 2 (m0f1 j₁) t := (contDiff_m0f1 j₁).contDiffAt
  have hcd2 : ContDiffAt ℝ 2 (m0f2 P j₂) t := (contDiff_m0f2 P j₂).contDiffAt
  refine ⟨?_, ?_, ?_⟩
  · rw [m0poly_eq_mul, Pi.mul_apply, norm_mul]
    calc ‖m0f1 j₁ t‖ * ‖m0f2 P j₂ t‖
        ≤ (400 * (N : ℝ) ^ j₁)
            * ((4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j₂)) :=
          mul_le_mul hf1_0 hf2_0 (norm_nonneg _) hB1
      _ = 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2))
            * ((N : ℝ) ^ j₁ * (N : ℝ) ^ (P.natDegree * j₂)) := by ring
      _ = 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2))
            * (N : ℝ) ^ (j₁ + P.natDegree * j₂) := by rw [pow_add]
  · rw [m0poly_eq_mul, deriv_mul hd1 hd2]
    calc ‖deriv (m0f1 j₁) t * m0f2 P j₂ t + m0f1 j₁ t * deriv (m0f2 P j₂) t‖
        ≤ ‖deriv (m0f1 j₁) t * m0f2 P j₂ t‖ + ‖m0f1 j₁ t * deriv (m0f2 P j₂) t‖ :=
          norm_add_le _ _
      _ = ‖deriv (m0f1 j₁) t‖ * ‖m0f2 P j₂ t‖ + ‖m0f1 j₁ t‖ * ‖deriv (m0f2 P j₂) t‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (400 * (N : ℝ) ^ j₁ / (N : ℝ))
            * ((4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j₂))
          + (400 * (N : ℝ) ^ j₁)
            * ((4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j₂) / (N : ℝ)) :=
          add_le_add (mul_le_mul hf1_1 hf2_0 (norm_nonneg _) hC1)
                     (mul_le_mul hf1_0 hf2_1 (norm_nonneg _) hB1)
      _ = 2 * (400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)))
            * (N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ) := by
          rw [pow_add]; ring
  · rw [m0poly_eq_mul]
    rw [iteratedDeriv_mul hcd1 hcd2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.choose_self, iteratedDeriv_zero, iteratedDeriv_one, zero_add]
    norm_num
    have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hX : ‖m0f1 j₁ t * iteratedDeriv 2 (m0f2 P j₂) t‖
        ≤ (400 * (N : ℝ) ^ j₁)
            * ((4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j₂)
                / (N : ℝ) ^ 2) := by
      rw [norm_mul]; exact mul_le_mul hf1_0 hf2_2 (norm_nonneg _) hB1
    have hY : ‖2 * deriv (m0f1 j₁) t * deriv (m0f2 P j₂) t‖
        ≤ (2 * (400 * (N : ℝ) ^ j₁ / (N : ℝ)))
            * ((4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j₂)
                / (N : ℝ)) := by
      rw [norm_mul, norm_mul, h2c]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hf1_1 (by norm_num)) hf2_1 (norm_nonneg _)
        (mul_nonneg (by norm_num) hC1)
    have hZ : ‖iteratedDeriv 2 (m0f1 j₁) t * m0f2 P j₂ t‖
        ≤ (400 * (N : ℝ) ^ j₁ / (N : ℝ) ^ 2)
            * ((4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j₂)) := by
      rw [norm_mul]; exact mul_le_mul hf1_2 hf2_0 (norm_nonneg _) hB3
    calc ‖m0f1 j₁ t * iteratedDeriv 2 (m0f2 P j₂) t + 2 * deriv (m0f1 j₁) t * deriv (m0f2 P j₂) t
          + iteratedDeriv 2 (m0f1 j₁) t * m0f2 P j₂ t‖
        ≤ (400 * (N : ℝ) ^ j₁)
            * ((4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j₂) / (N : ℝ) ^ 2)
          + (2 * (400 * (N : ℝ) ^ j₁ / (N : ℝ)))
            * ((4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j₂) / (N : ℝ))
          + (400 * (N : ℝ) ^ j₁ / (N : ℝ) ^ 2)
            * ((4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (P.natDegree * j₂)) := by
          refine le_trans (norm_add_le _ _) (add_le_add ?_ hZ)
          exact le_trans (norm_add_le _ _) (add_le_add hX hY)
      _ = 4 * (400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)))
            * (N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ) ^ 2 := by
          rw [pow_add]; ring

/-! ## 5. `m0w` -/

/-- **The product-rule expansion for the second derivative of `m0w = m0poly · momFun`.** -/
lemma m0w_iteratedDeriv_two_le (P : Polynomial ℤ) (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) (u : ℝ) :
    ‖iteratedDeriv 2 (m0w P ξ₁ ξ₂ j₁ j₂) u‖
      ≤ ‖iteratedDeriv 2 (m0poly P j₁ j₂) u‖ * ‖momFun P ξ₁ ξ₂ u‖
        + 2 * ‖deriv (m0poly P j₁ j₂) u‖ * ‖deriv (momFun P ξ₁ ξ₂) u‖
        + ‖m0poly P j₁ j₂ u‖ * ‖iteratedDeriv 2 (momFun P ξ₁ ξ₂) u‖ := by
  have hcd1 : ContDiffAt ℝ 2 (m0poly P j₁ j₂) u :=
    ((contDiff_m0poly P j₁ j₂).of_le le_top).contDiffAt
  have hcd2 : ContDiffAt ℝ 2 (momFun P ξ₁ ξ₂) u := (momFun_contDiff P ξ₁ ξ₂).contDiffAt
  rw [show m0w P ξ₁ ξ₂ j₁ j₂ = m0poly P j₁ j₂ * momFun P ξ₁ ξ₂ from rfl,
    iteratedDeriv_mul hcd1 hcd2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.choose_self, iteratedDeriv_zero, iteratedDeriv_one, zero_add]
  norm_num
  have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h1 : ‖m0poly P j₁ j₂ u * iteratedDeriv 2 (momFun P ξ₁ ξ₂) u‖
      ≤ ‖m0poly P j₁ j₂ u‖ * ‖iteratedDeriv 2 (momFun P ξ₁ ξ₂) u‖ := le_of_eq (norm_mul _ _)
  have h2' : ‖2 * deriv (m0poly P j₁ j₂) u * deriv (momFun P ξ₁ ξ₂) u‖
      ≤ (2 * ‖deriv (m0poly P j₁ j₂) u‖) * ‖deriv (momFun P ξ₁ ξ₂) u‖ :=
    le_of_eq (by rw [norm_mul, norm_mul, h2c])
  have h3 : ‖iteratedDeriv 2 (m0poly P j₁ j₂) u * momFun P ξ₁ ξ₂ u‖
      ≤ ‖iteratedDeriv 2 (m0poly P j₁ j₂) u‖ * ‖momFun P ξ₁ ξ₂ u‖ := le_of_eq (norm_mul _ _)
  calc ‖m0poly P j₁ j₂ u * iteratedDeriv 2 (momFun P ξ₁ ξ₂) u
          + 2 * deriv (m0poly P j₁ j₂) u * deriv (momFun P ξ₁ ξ₂) u
          + iteratedDeriv 2 (m0poly P j₁ j₂) u * momFun P ξ₁ ξ₂ u‖
      ≤ ‖m0poly P j₁ j₂ u * iteratedDeriv 2 (momFun P ξ₁ ξ₂) u
            + 2 * deriv (m0poly P j₁ j₂) u * deriv (momFun P ξ₁ ξ₂) u‖
          + ‖iteratedDeriv 2 (m0poly P j₁ j₂) u * momFun P ξ₁ ξ₂ u‖ := norm_add_le _ _
    _ ≤ (‖m0poly P j₁ j₂ u * iteratedDeriv 2 (momFun P ξ₁ ξ₂) u‖
            + ‖2 * deriv (m0poly P j₁ j₂) u * deriv (momFun P ξ₁ ξ₂) u‖)
          + ‖iteratedDeriv 2 (m0poly P j₁ j₂) u * momFun P ξ₁ ξ₂ u‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖m0poly P j₁ j₂ u‖ * ‖iteratedDeriv 2 (momFun P ξ₁ ξ₂) u‖
          + (2 * ‖deriv (m0poly P j₁ j₂) u‖) * ‖deriv (momFun P ξ₁ ξ₂) u‖
          + ‖iteratedDeriv 2 (m0poly P j₁ j₂) u‖ * ‖momFun P ξ₁ ξ₂ u‖ := by
          linarith [h1, h2', h3]
    _ = ‖iteratedDeriv 2 (m0poly P j₁ j₂) u‖ * ‖momFun P ξ₁ ξ₂ u‖
          + 2 * ‖deriv (m0poly P j₁ j₂) u‖ * ‖deriv (momFun P ξ₁ ξ₂) u‖
          + ‖m0poly P j₁ j₂ u‖ * ‖iteratedDeriv 2 (momFun P ξ₁ ξ₂) u‖ := by ring

/-- **Absorption step.**  Homogeneous bounds on the two factors transfer to the product-rule
combination `x₂b₀ + 2x₁b₁ + x₀b₂`, with the gain of the factor `4 + 5B`. -/
lemma m0w_absorb {x0 x1 x2 b0 b1 b2 M Bc S Nn : ℝ} {E : ℕ} (hM : 0 ≤ M) (hB : 0 ≤ Bc)
    (hS : 0 ≤ S) (hN : 0 < Nn) (hNe : 0 ≤ Nn ^ E)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h0 : x0 ≤ M * Nn ^ E) (h1 : x1 ≤ 2 * M * Nn ^ E / Nn) (h2 : x2 ≤ 4 * M * Nn ^ E / Nn ^ 2)
    (hB0 : b0 ≤ 1) (hB1 : b1 ≤ Bc * S / Nn) (hB2 : b2 ≤ Bc * (1 + S + S ^ 2) / Nn ^ 2) :
    x2 * b0 + 2 * x1 * b1 + x0 * b2
      ≤ M * (4 + 5 * Bc) * (Nn ^ E / Nn ^ 2) * (1 + S + S ^ 2) := by
  have hr : 0 ≤ Nn ^ E / Nn ^ 2 := div_nonneg hNe (by positivity)
  have hpos1 : 0 ≤ 2 * M * Nn ^ E / Nn :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hNe) hN.le
  have hpos2 : 0 ≤ 4 * M * Nn ^ E / Nn ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hNe) (by positivity)
  have hX : x2 * b0 ≤ 4 * M * Nn ^ E / Nn ^ 2 := by
    calc x2 * b0 ≤ (4 * M * Nn ^ E / Nn ^ 2) * 1 := mul_le_mul h2 hB0 hb0 hpos2
      _ = 4 * M * Nn ^ E / Nn ^ 2 := by ring
  have hY : 2 * x1 * b1 ≤ 4 * M * Bc * S * Nn ^ E / Nn ^ 2 := by
    calc 2 * x1 * b1 ≤ (2 * (2 * M * Nn ^ E / Nn)) * (Bc * S / Nn) :=
          mul_le_mul (by linarith [h1]) hB1 hb1 (by linarith [hpos1])
      _ = 4 * M * Bc * S * Nn ^ E / Nn ^ 2 := by ring
  have hZ : x0 * b2 ≤ M * Bc * (1 + S + S ^ 2) * Nn ^ E / Nn ^ 2 := by
    calc x0 * b2 ≤ (M * Nn ^ E) * (Bc * (1 + S + S ^ 2) / Nn ^ 2) :=
          mul_le_mul h0 hB2 hb2 (by positivity)
      _ = M * Bc * (1 + S + S ^ 2) * Nn ^ E / Nn ^ 2 := by ring
  have hbracket : 4 + 4 * Bc * S + Bc * (1 + S + S ^ 2) ≤ (4 + 5 * Bc) * (1 + S + S ^ 2) := by
    nlinarith [hB, hS, sq_nonneg S]
  have hkey : (4 * M + 4 * M * Bc * S + M * Bc * (1 + S + S ^ 2))
      ≤ M * (4 + 5 * Bc) * (1 + S + S ^ 2) := by
    have h2' := mul_le_mul_of_nonneg_left hbracket hM
    calc 4 * M + 4 * M * Bc * S + M * Bc * (1 + S + S ^ 2)
        = M * (4 + 4 * Bc * S + Bc * (1 + S + S ^ 2)) := by ring
      _ ≤ M * ((4 + 5 * Bc) * (1 + S + S ^ 2)) := h2'
      _ = M * (4 + 5 * Bc) * (1 + S + S ^ 2) := by ring
  calc x2 * b0 + 2 * x1 * b1 + x0 * b2
      ≤ (4 * M * Nn ^ E / Nn ^ 2) + (4 * M * Bc * S * Nn ^ E / Nn ^ 2)
          + (M * Bc * (1 + S + S ^ 2) * Nn ^ E / Nn ^ 2) := by linarith
    _ = (4 * M + 4 * M * Bc * S + M * Bc * (1 + S + S ^ 2)) * (Nn ^ E / Nn ^ 2) := by ring
    _ ≤ (M * (4 + 5 * Bc) * (1 + S + S ^ 2)) * (Nn ^ E / Nn ^ 2) :=
          mul_le_mul_of_nonneg_right hkey hr
    _ = M * (4 + 5 * Bc) * (Nn ^ E / Nn ^ 2) * (1 + S + S ^ 2) := by ring

/-- The bridge from the natural-number exponent to the real (rpow) exponent of the target. -/
lemma rpow_natCast_sub_two (Nn : ℝ) (hN : 0 < Nn) (e : ℕ) :
    Nn ^ ((e : ℝ) - 2) = Nn ^ e / Nn ^ 2 := by
  rw [Real.rpow_sub hN, Real.rpow_natCast]
  rw [show Nn ^ (2 : ℝ) = Nn ^ 2 from Real.rpow_ofNat Nn 2]

/-- **The bound `Work.A7.m0w_bound`.** -/
theorem m0w_bound (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N k₁ k₂ j₁ j₂ : ℕ) (ξ₁ ξ₂ : ℝ),
      1 ≤ N → j₁ ≤ 2 → j₂ ≤ 2 →
      |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) →
      |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree →
      ∀ u ∈ Set.Icc (0 : ℝ) (N : ℝ),
        ‖m0w P ξ₁ ξ₂ j₁ j₂ u‖ ≤ C * (N : ℝ) ^ (((j₁ + P.natDegree * j₂ : ℕ) : ℝ)) ∧
        ‖iteratedDeriv 2 (m0w P ξ₁ ξ₂ j₁ j₂) u‖
          ≤ C * (N : ℝ) ^ (((j₁ + P.natDegree * j₂ : ℕ) : ℝ) - 2)
              * (1 + Sval P k₁ k₂ + (Sval P k₁ k₂) ^ 2) := by
  obtain ⟨A, hApos, hPev⟩ := Work.A7.Pev.PevalR_deriv_bounds P
  have hA : 0 ≤ A := le_of_lt hApos
  have hval : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |Work.KMTAreas.A7.PevalR P t| ≤ A * (N : ℝ) ^ P.natDegree :=
    fun N hN t ht => (hPev N hN t ht).1
  have hP1 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |deriv (Work.KMTAreas.A7.PevalR P) t| ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ) :=
    fun N hN t ht => (hPev N hN t ht).2.1
  have hP2 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t|
        ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2 :=
    fun N hN t ht => (hPev N hN t ht).2.2
  obtain ⟨B, hBpos, hMom⟩ := Work.A7.Mom.momFun_deriv_bounds P hApos hP1 hP2
  have hB : 0 ≤ B := le_of_lt hBpos
  refine ⟨400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)) * (4 + 5 * B), ?_, ?_⟩
  · positivity
  · intro N k₁ k₂ j₁ j₂ ξ₁ ξ₂ hN hj₁ hj₂ hξ₁ hξ₂ u hu
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    obtain ⟨hp_0, hp_1, hp_2⟩ := m0poly_bounds P hA hval hP1 hP2 hN hu hj₁ hj₂
    obtain ⟨hm_0, hm_1, hm_2⟩ := hMom N k₁ k₂ ξ₁ ξ₂ hN hξ₁ hξ₂ u hu
    have hS : (0 : ℝ) ≤ Sval P k₁ k₂ := by unfold Sval; positivity
    have hM : (0 : ℝ) ≤ 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)) := by positivity
    have hNe : (0 : ℝ) ≤ (N : ℝ) ^ (j₁ + P.natDegree * j₂) := by positivity
    refine ⟨?_, ?_⟩
    · have hfirst : ‖m0w P ξ₁ ξ₂ j₁ j₂ u‖
          ≤ 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)) * (N : ℝ) ^ (j₁ + P.natDegree * j₂) := by
        rw [show m0w P ξ₁ ξ₂ j₁ j₂ u = m0poly P j₁ j₂ u * momFun P ξ₁ ξ₂ u from rfl, norm_mul]
        calc ‖m0poly P j₁ j₂ u‖ * ‖momFun P ξ₁ ξ₂ u‖
            ≤ (400 * (4 * max 1 ((2 * Real.pi * A) ^ 2))
                * (N : ℝ) ^ (j₁ + P.natDegree * j₂)) * 1 :=
              mul_le_mul hp_0 hm_0 (norm_nonneg _) (mul_nonneg hM hNe)
          _ = 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2))
                * (N : ℝ) ^ (j₁ + P.natDegree * j₂) := by ring
      calc ‖m0w P ξ₁ ξ₂ j₁ j₂ u‖
          ≤ 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2))
              * (N : ℝ) ^ (j₁ + P.natDegree * j₂) := hfirst
        _ ≤ 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)) * (4 + 5 * B)
              * (N : ℝ) ^ (j₁ + P.natDegree * j₂) := by
            refine mul_le_mul_of_nonneg_right ?_ hNe
            exact le_mul_of_one_le_right hM (by linarith)
        _ = 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)) * (4 + 5 * B)
              * (N : ℝ) ^ (((j₁ + P.natDegree * j₂ : ℕ) : ℝ)) := by
            rw [Real.rpow_natCast]
    · have hexp := m0w_iteratedDeriv_two_le P ξ₁ ξ₂ j₁ j₂ u
      have habs := m0w_absorb (x0 := ‖m0poly P j₁ j₂ u‖)
        (x1 := ‖deriv (m0poly P j₁ j₂) u‖) (x2 := ‖iteratedDeriv 2 (m0poly P j₁ j₂) u‖)
        (b0 := ‖momFun P ξ₁ ξ₂ u‖) (b1 := ‖deriv (momFun P ξ₁ ξ₂) u‖)
        (b2 := ‖iteratedDeriv 2 (momFun P ξ₁ ξ₂) u‖)
        (M := 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2))) (Bc := B) (S := Sval P k₁ k₂)
        (Nn := (N : ℝ)) (E := j₁ + P.natDegree * j₂)
        hM hB hS hNpos hNe (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        hp_0 hp_1 hp_2 hm_0 hm_1 hm_2
      calc ‖iteratedDeriv 2 (m0w P ξ₁ ξ₂ j₁ j₂) u‖
          ≤ ‖iteratedDeriv 2 (m0poly P j₁ j₂) u‖ * ‖momFun P ξ₁ ξ₂ u‖
              + 2 * ‖deriv (m0poly P j₁ j₂) u‖ * ‖deriv (momFun P ξ₁ ξ₂) u‖
              + ‖m0poly P j₁ j₂ u‖ * ‖iteratedDeriv 2 (momFun P ξ₁ ξ₂) u‖ := hexp
        _ ≤ 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)) * (4 + 5 * B)
              * ((N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ) ^ 2)
              * (1 + Sval P k₁ k₂ + (Sval P k₁ k₂) ^ 2) := habs
        _ = 400 * (4 * max 1 ((2 * Real.pi * A) ^ 2)) * (4 + 5 * B)
              * (N : ℝ) ^ (((j₁ + P.natDegree * j₂ : ℕ) : ℝ) - 2)
              * (1 + Sval P k₁ k₂ + (Sval P k₁ k₂) ^ 2) := by
            rw [rpow_natCast_sub_two (N : ℝ) hNpos (j₁ + P.natDegree * j₂)]
            try ring

end

end Work.A7
