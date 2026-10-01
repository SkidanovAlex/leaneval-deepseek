import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace Commons.NumberTheory.DirichletCharacter

open Complex MeasureTheory Filter
open scoped Real Topology ArithmeticFunction.Moebius

noncomputable section

/-! ## Summability of log-weighted p-series -/

private lemma summable_log_mul_neg_three_halves :
    Summable (fun n : ℕ => Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ)) := by
  have h5 : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 / 4) : ℝ)) :=
    ((Real.summable_nat_rpow_inv (p := (5 : ℝ) / 4)).mpr (by norm_num : (1 : ℝ) < 5 / 4)).congr
      (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => 4 * (n : ℝ) ^ (-(5 / 4) : ℝ))
    (g := fun n : ℕ => Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ)) ?_ ?_ (h5.mul_left 4)
  · intro n
    exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.log_zero, Real.zero_rpow (by norm_num : (-(3 / 2) : ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (-(5 / 4) : ℝ) ≠ 0)]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hlog : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
        have h := Real.log_le_rpow_div (x := (n : ℝ)) (ε := (1 : ℝ) / 4)
          (Nat.cast_nonneg n) (by norm_num)
        rw [div_eq_mul_inv, show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at h
        simpa [mul_comm] using h
      have h1 : (0 : ℝ) ≤ (n : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have step1 : Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ)
          ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * (n : ℝ) ^ (-(3 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right hlog h1
      have step2 : (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * (n : ℝ) ^ (-(3 / 2) : ℝ)
          = 4 * (n : ℝ) ^ (-(5 / 4) : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hnpos]
        norm_num
      linarith [step1, step2.le]

private lemma summable_neg_three_halves :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
  ((Real.summable_nat_rpow_inv (p := (3 : ℝ) / 2)).mpr (by norm_num : (1 : ℝ) < 3 / 2)).congr
    (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])

/-- `∑ n⁻³ᐟ²`. -/
private noncomputable def Sconst : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ)

/-- `∑ log n · n⁻³ᐟ²`. -/
private noncomputable def Tconst : ℝ := ∑' n : ℕ, Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ)

private lemma Sconst_pos : 0 < Sconst := by
  have h1 : (1 : ℝ) ≤ Sconst := by
    have := summable_neg_three_halves.le_tsum 1 (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg j) _)
    rw [Sconst]
    simpa using this
  linarith

private lemma Tconst_nonneg : 0 ≤ Tconst := by
  rw [Tconst]
  exact tsum_nonneg (fun n => mul_nonneg (Real.log_natCast_nonneg n)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _))

private lemma Tconst_summable :
    Summable (fun n : ℕ => Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
  summable_log_mul_neg_three_halves

/-! ## Bounds for `LFunction χ` and its logarithmic derivative -/

private lemma norm_moebius_cast_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

private lemma LFunction_norm_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re → Sconst⁻¹ ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  intro s hs
  have hs1 : 1 < s.re := by linarith
  set g : ℕ → ℂ := (fun n : ℕ => χ (n : ZMod N)) * (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
    with hg
  have hbound : ‖LSeries g s‖ ≤ Sconst := by
    have hterm : ∀ n : ℕ, ‖LSeries.term g s n‖ ≤ (n : ℝ) ^ (-(3 / 2) : ℝ) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term_zero, Real.zero_rpow (by norm_num : (-(3 / 2) : ℝ) ≠ 0)]
      · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
        have hgn : ‖g n‖ ≤ 1 := by
          rw [hg]
          simp only [Pi.mul_apply, norm_mul]
          exact mul_le_one₀ (DirichletCharacter.norm_le_one χ (n : ZMod N))
            (norm_nonneg _) (norm_moebius_cast_le_one n)
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        have hrpow : ((n : ℝ) ^ s.re)⁻¹ ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div]
          exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < n) _)
            (Real.rpow_le_rpow_of_exponent_le hn1 hs)
        calc ‖g n‖ / (n : ℝ) ^ s.re
            ≤ 1 / (n : ℝ) ^ s.re :=
              div_le_div_of_nonneg_right hgn (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ = ((n : ℝ) ^ s.re)⁻¹ := by rw [one_div]
          _ ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := hrpow
          _ = (n : ℝ) ^ (-(3 / 2) : ℝ) := by
              rw [Real.rpow_neg (Nat.cast_nonneg n)]
    have hsumn : Summable (fun n : ℕ => ‖LSeries.term g s n‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm summable_neg_three_halves
    calc ‖LSeries g s‖ = ‖∑' n : ℕ, LSeries.term g s n‖ := by rw [LSeries]
      _ ≤ ∑' n : ℕ, ‖LSeries.term g s n‖ := norm_tsum_le_tsum_norm hsumn
      _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ) :=
          Summable.tsum_le_tsum hterm hsumn summable_neg_three_halves
      _ = Sconst := rfl
  have hid : DirichletCharacter.LFunction χ s * LSeries g s = 1 := by
    rw [hg, DirichletCharacter.LFunction_eq_LSeries χ hs1]
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ hs1
  have hnorm : ‖DirichletCharacter.LFunction χ s‖ * ‖LSeries g s‖ = 1 := by
    rw [← norm_mul, hid, norm_one]
  have htwo : (1 : ℝ) ≤ ‖DirichletCharacter.LFunction χ s‖ * Sconst := by
    calc (1 : ℝ) = ‖DirichletCharacter.LFunction χ s‖ * ‖LSeries g s‖ := hnorm.symm
      _ ≤ ‖DirichletCharacter.LFunction χ s‖ * Sconst :=
          mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  show Sconst⁻¹ ≤ ‖DirichletCharacter.LFunction χ s‖
  rw [inv_eq_one_div, div_le_iff₀ Sconst_pos]
  exact htwo

private lemma deriv_LFunction_norm_upper {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re → ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ Tconst := by
  intro s hs
  have hs1 : 1 < s.re := by linarith
  have hab : LSeries.abscissaOfAbsConv (fun n => χ (n : ZMod N)) = 1 :=
    DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) χ
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs1,
    LSeries_deriv (f := fun n => χ (n : ZMod N))
      (by rw [hab]; exact_mod_cast hs1), norm_neg]
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (LSeries.logMul (fun n => χ (n : ZMod N))) s n‖
        ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero, Real.log_zero]
    · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        LSeries.logMul, norm_mul]
      have hlog : ‖Complex.log (n : ℂ)‖ = Real.log (n : ℝ) := by
        rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_natCast_nonneg n)]
      rw [hlog]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hrpow : ((n : ℝ) ^ s.re)⁻¹ ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < n) _)
          (Real.rpow_le_rpow_of_exponent_le hn1 hs)
      calc Real.log (n : ℝ) * ‖χ (n : ZMod N)‖ / (n : ℝ) ^ s.re
          ≤ Real.log (n : ℝ) * 1 / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _)
                (Real.log_natCast_nonneg n)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = Real.log (n : ℝ) * ((n : ℝ) ^ s.re)⁻¹ := by rw [mul_one, div_eq_mul_inv]
        _ ≤ Real.log (n : ℝ) * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_left hrpow (Real.log_natCast_nonneg n)
        _ = Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ) := by
            rw [Real.rpow_neg (Nat.cast_nonneg n)]
  have hsumn : Summable
      (fun n : ℕ => ‖LSeries.term (LSeries.logMul (fun n => χ (n : ZMod N))) s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm Tconst_summable
  calc ‖LSeries (LSeries.logMul (fun n => χ (n : ZMod N))) s‖
      = ‖∑' n : ℕ, LSeries.term (LSeries.logMul (fun n => χ (n : ZMod N))) s n‖ := by rw [LSeries]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (LSeries.logMul (fun n => χ (n : ZMod N))) s n‖ :=
        norm_tsum_le_tsum_norm hsumn
    _ ≤ ∑' n : ℕ, Real.log (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ) :=
        Summable.tsum_le_tsum hterm hsumn Tconst_summable
    _ = Tconst := rfl

private lemma logDeriv_LFunction_norm_upper {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ Tconst * Sconst := by
  intro s hs
  have hup := deriv_LFunction_norm_upper χ hχ s hs
  have hlow := LFunction_norm_lower χ hχ s hs
  have hLpos : 0 < ‖DirichletCharacter.LFunction χ s‖ :=
    lt_of_lt_of_le (inv_pos.mpr Sconst_pos) hlow
  rw [logDeriv_apply, norm_div, div_le_iff₀ hLpos]
  have hTS : (0 : ℝ) ≤ Tconst * Sconst := mul_nonneg Tconst_nonneg Sconst_pos.le
  calc ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ Tconst := hup
    _ = (Tconst * Sconst) * Sconst⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ Sconst_pos.ne', mul_one]
    _ ≤ (Tconst * Sconst) * ‖DirichletCharacter.LFunction χ s‖ :=
        mul_le_mul_of_nonneg_left hlow hTS

/-! ## The contour shift -/

private noncomputable def cc (a b : ℝ) : ℂ := ((3 / 2 : ℝ) : ℂ) - (a : ℂ) - (b : ℂ) * I

private noncomputable def kern (lam : ℝ) (s : ℂ) : ℂ :=
  (Complex.exp (-(s * (lam : ℂ))) - 1) / s ^ 2

private noncomputable def FF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a b lam : ℝ) (s : ℂ) : ℂ :=
  logDeriv (DirichletCharacter.LFunction χ) (s + cc a b) * kern lam s

private noncomputable def U (a b : ℝ) : Set ℂ := {s : ℂ | 1 < (s + cc a b).re} ∩ {0}ᶜ

private lemma FF_shift_re (a b : ℝ) (s : ℂ) : (s + cc a b).re = s.re + (3 / 2 - a) := by
  simp only [cc, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero]
  ring

private lemma FF_norm_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {a b lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    ∀ x y : ℝ, a ≤ x →
      ‖FF χ a b lam ((x : ℂ) + (y : ℂ) * I)‖
        ≤ (Tconst * Sconst) * (Real.exp (-(lam * x)) + 1) / (x ^ 2 + y ^ 2) := by
  intro x y hx
  have hxpos : 0 < x := lt_of_lt_of_le ha hx
  set s : ℂ := (x : ℂ) + (y : ℂ) * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hMnn : (0 : ℝ) ≤ Tconst * Sconst := mul_nonneg Tconst_nonneg Sconst_pos.le
  have hregion : (3 / 2 : ℝ) ≤ (s + cc a b).re := by
    rw [FF_shift_re, hsre]; linarith
  have hbound1 : ‖logDeriv (DirichletCharacter.LFunction χ) (s + cc a b)‖ ≤ Tconst * Sconst :=
    logDeriv_LFunction_norm_upper χ hχ _ hregion
  have hkern : ‖kern lam s‖ ≤ (Real.exp (-(lam * x)) + 1) / (x ^ 2 + y ^ 2) := by
    rw [kern, norm_div]
    have hnum : ‖Complex.exp (-(s * (lam : ℂ))) - 1‖ ≤ Real.exp (-(lam * x)) + 1 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [Complex.norm_exp, norm_one]
      have hre : (-(s * (lam : ℂ))).re = -(lam * x) := by
        rw [Complex.neg_re, Complex.mul_re]
        simp [hsre, hsim]
        ring
      rw [hre]
    have hden : ‖s ^ 2‖ = x ^ 2 + y ^ 2 := by
      rw [pow_two, norm_mul, ← pow_two, Complex.sq_norm, Complex.normSq_apply, hsre, hsim]
      ring
    rw [hden]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  rw [FF, norm_mul, mul_div_assoc]
  exact mul_le_mul hbound1 hkern (norm_nonneg _) hMnn

private lemma differentiableAt_FF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (a b lam : ℝ) {s : ℂ} (h1 : 1 < (s + cc a b).re) (hs0 : s ≠ 0) :
    DifferentiableAt ℂ (FF χ a b lam) s := by
  have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hLne : DirichletCharacter.LFunction χ (s + cc a b) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_lt h1)
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) (s + cc a b) :=
    hLdiff.differentiableOn.analyticAt Filter.univ_mem
  have hlog : DifferentiableAt ℂ (logDeriv (DirichletCharacter.LFunction χ)) (s + cc a b) :=
    ((han.deriv.div han hLne)).differentiableAt
  have hshift : DifferentiableAt ℂ (fun w : ℂ => w + cc a b) s := differentiableAt_id.add_const _
  have h1' : DifferentiableAt ℂ
      (fun w : ℂ => logDeriv (DirichletCharacter.LFunction χ) (w + cc a b)) s :=
    hlog.comp s hshift
  have hkern : DifferentiableAt ℂ (kern lam) s := by
    have hnum : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-(w * (lam : ℂ))) - 1) s := by
      fun_prop
    have hden : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) s := by fun_prop
    exact hnum.div hden (pow_ne_zero 2 hs0)
  show DifferentiableAt ℂ (fun w : ℂ => logDeriv (DirichletCharacter.LFunction χ) (w + cc a b)
    * kern lam w) s
  exact h1'.mul hkern

private lemma differentiableOn_FF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (a b lam : ℝ) : DifferentiableOn ℂ (FF χ a b lam) (U a b) := by
  intro s hs
  simp only [U, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  exact (differentiableAt_FF χ hχ a b lam hs.1 hs.2).differentiableWithinAt

private lemma isOpen_U (a b : ℝ) : IsOpen (U a b) := by
  refine IsOpen.inter ?_ isOpen_compl_singleton
  exact isOpen_lt continuous_const (continuous_re.comp (continuous_id.add continuous_const))

private lemma integrable_inv_sq_add {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) volume := by
  have hg : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) volume := integrable_inv_one_add_sq
  have h1 : Integrable (fun y : ℝ => (1 + (y / a) ^ 2)⁻¹) volume := hg.comp_div ha.ne'
  have h2 : Integrable (fun y : ℝ => (a ^ 2)⁻¹ * (1 + (y / a) ^ 2)⁻¹) volume := h1.const_mul _
  refine h2.congr ?_
  filter_upwards with y
  rw [div_pow]
  field_simp

private lemma integrable_FF_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {a b lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    Integrable (fun y : ℝ => FF χ a b lam ((a : ℂ) + (y : ℂ) * I)) volume := by
  have hcont : Continuous (fun y : ℝ => FF χ a b lam ((a : ℂ) + (y : ℂ) * I)) := by
    refine ContinuousOn.comp_continuous (differentiableOn_FF χ hχ a b lam).continuousOn ?_ ?_
    · fun_prop
    · intro y
      simp only [U, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · have h2 : (((a : ℂ) + (y : ℂ) * I) + cc a b).re = 3 / 2 := by
          rw [FF_shift_re]; simp
        rw [h2]; norm_num
      · intro h0
        have h2 : ((a : ℂ) + (y : ℂ) * I).re = a := by simp
        rw [h0] at h2; simp at h2; linarith
  have hdom : Integrable
      (fun y : ℝ => (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) * (a ^ 2 + y ^ 2)⁻¹) volume :=
    (integrable_inv_sq_add ha).const_mul _
  refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
  filter_upwards with y
  have h := FF_norm_le (b := b) χ hχ ha hlam a y le_rfl
  rw [div_eq_mul_inv] at h
  exact h
private noncomputable def Aint {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a b lam : ℝ) (T : ℝ) : ℂ :=
  ∫ x in a..T, FF χ a b lam ((x : ℂ) + ((-T : ℝ) : ℂ) * I)

private noncomputable def Bint {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a b lam : ℝ) (T : ℝ) : ℂ :=
  ∫ x in a..T, FF χ a b lam ((x : ℂ) + (T : ℂ) * I)

private noncomputable def CTint {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a b lam : ℝ) (T : ℝ) : ℂ :=
  ∫ y in -T..T, FF χ a b lam ((T : ℂ) + (y : ℂ) * I)

private noncomputable def Caint {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a b lam : ℝ) (T : ℝ) : ℂ :=
  ∫ y in -T..T, FF χ a b lam ((a : ℂ) + (y : ℂ) * I)

private lemma rect_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {a b lam : ℝ} (ha : 0 < a) :
    ∀ᶠ T in atTop, Aint χ a b lam T - Bint χ a b lam T + I * CTint χ a b lam T
      - I * Caint χ a b lam T = 0 := by
  filter_upwards [Filter.eventually_gt_atTop a] with T hT
  have hzre : (((a : ℂ) + ((-T : ℝ) : ℂ) * I)).re = a := by simp
  have hzim : (((a : ℂ) + ((-T : ℝ) : ℂ) * I)).im = -T := by simp
  have hwre : (((T : ℂ) + (T : ℂ) * I)).re = T := by simp
  have hwim : (((T : ℂ) + (T : ℂ) * I)).im = T := by simp
  have hdiff : DifferentiableOn ℂ (FF χ a b lam)
      (Set.uIcc (((a : ℂ) + ((-T : ℝ) : ℂ) * I)).re (((T : ℂ) + (T : ℂ) * I)).re ×ℂ
        Set.uIcc (((a : ℂ) + ((-T : ℝ) : ℂ) * I)).im (((T : ℂ) + (T : ℂ) * I)).im) := by
    rw [hzre, hzim, hwre, hwim]
    refine (differentiableOn_FF χ hχ a b lam).mono ?_
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    obtain ⟨hs1, hs2⟩ := hs
    rw [Set.uIcc_of_le hT.le] at hs1
    simp only [Set.mem_Icc] at hs1
    simp only [U, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rw [FF_shift_re]; linarith [hs1.1]
    · intro h0
      have hh : s.re = 0 := by rw [h0]; simp
      linarith [hs1.1, hh, ha]
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (FF χ a b lam) _ _ hdiff
  rw [hzre, hzim, hwre, hwim] at h
  simpa only [Aint, Bint, CTint, Caint, smul_eq_mul] using h

private lemma Aint_tend {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {a b lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    Tendsto (fun T => Aint χ a b lam T) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun T : ℝ => (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop a, Filter.eventually_gt_atTop (0 : ℝ)] with T hTa hT0
    have hbound : ‖Aint χ a b lam T‖
        ≤ (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T := by
      rw [Aint]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T ^ 2) ?_) ?_
      · intro x hx
        rw [Set.uIoc_of_le hTa.le, Set.mem_Ioc] at hx
        obtain ⟨hax, hxT⟩ := hx
        refine le_trans (FF_norm_le χ hχ ha hlam x (-T) (le_of_lt hax)) ?_
        have hexp : Real.exp (-(lam * x)) ≤ Real.exp (-(lam * a)) :=
          Real.exp_le_exp.mpr (by nlinarith [hax, hlam])
        have hnum : (Tconst * Sconst) * (Real.exp (-(lam * x)) + 1)
            ≤ (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg Tconst_nonneg Sconst_pos.le)
        calc (Tconst * Sconst) * (Real.exp (-(lam * x)) + 1) / (x ^ 2 + (-T) ^ 2)
            ≤ (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / (x ^ 2 + (-T) ^ 2) :=
              div_le_div_of_nonneg_right hnum (by positivity)
          _ ≤ (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T ^ 2 := by
              refine div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg Tconst_nonneg Sconst_pos.le) (by positivity)) (by positivity) ?_
              nlinarith [sq_nonneg x]
      · rw [abs_of_pos (sub_pos.mpr hTa)]
        have hfrac : (T - a) / T ^ 2 ≤ 1 / T := by
          rw [div_le_div_iff₀ (by positivity) hT0]
          nlinarith [hTa.le, ha, hT0]
        calc ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T ^ 2) * (T - a)
            = ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1)) * ((T - a) / T ^ 2) := by ring
          _ ≤ ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1)) * (1 / T) :=
              mul_le_mul_of_nonneg_left hfrac (mul_nonneg (mul_nonneg Tconst_nonneg Sconst_pos.le) (by positivity))
          _ = (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T := by rw [mul_one_div]
    exact hbound
  · have hb : Tendsto (fun T : ℝ => ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1)) * T⁻¹)
        atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul
        ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1))
    refine hb.congr' ?_
    filter_upwards with T
    rw [div_eq_mul_inv]

private lemma Bint_tend {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {a b lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    Tendsto (fun T => Bint χ a b lam T) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun T : ℝ => (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop a, Filter.eventually_gt_atTop (0 : ℝ)] with T hTa hT0
    have hbound : ‖Bint χ a b lam T‖
        ≤ (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T := by
      rw [Bint]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T ^ 2) ?_) ?_
      · intro x hx
        rw [Set.uIoc_of_le hTa.le, Set.mem_Ioc] at hx
        obtain ⟨hax, hxT⟩ := hx
        refine le_trans (FF_norm_le χ hχ ha hlam x T (le_of_lt hax)) ?_
        have hexp : Real.exp (-(lam * x)) ≤ Real.exp (-(lam * a)) :=
          Real.exp_le_exp.mpr (by nlinarith [hax, hlam])
        have hnum : (Tconst * Sconst) * (Real.exp (-(lam * x)) + 1)
            ≤ (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg Tconst_nonneg Sconst_pos.le)
        calc (Tconst * Sconst) * (Real.exp (-(lam * x)) + 1) / (x ^ 2 + T ^ 2)
            ≤ (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / (x ^ 2 + T ^ 2) :=
              div_le_div_of_nonneg_right hnum (by positivity)
          _ ≤ (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T ^ 2 := by
              refine div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg Tconst_nonneg Sconst_pos.le) (by positivity)) (by positivity) ?_
              nlinarith [sq_nonneg x]
      · rw [abs_of_pos (sub_pos.mpr hTa)]
        have hfrac : (T - a) / T ^ 2 ≤ 1 / T := by
          rw [div_le_div_iff₀ (by positivity) hT0]
          nlinarith [hTa.le, ha, hT0]
        calc ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T ^ 2) * (T - a)
            = ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1)) * ((T - a) / T ^ 2) := by ring
          _ ≤ ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1)) * (1 / T) :=
              mul_le_mul_of_nonneg_left hfrac (mul_nonneg (mul_nonneg Tconst_nonneg Sconst_pos.le) (by positivity))
          _ = (Tconst * Sconst) * (Real.exp (-(lam * a)) + 1) / T := by rw [mul_one_div]
    exact hbound
  · have hb : Tendsto (fun T : ℝ => ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1)) * T⁻¹)
        atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul
        ((Tconst * Sconst) * (Real.exp (-(lam * a)) + 1))
    refine hb.congr' ?_
    filter_upwards with T
    rw [div_eq_mul_inv]

private lemma CTint_tend {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {a b lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    Tendsto (fun T => CTint χ a b lam T) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun T : ℝ => 4 * (Tconst * Sconst) / T) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (max a 0)] with T hT
    have hTa : a ≤ T := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hT)
    have hT0 : 0 < T := lt_of_le_of_lt (le_max_right _ _) hT
    have hexp : Real.exp (-(lam * T)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hlam, hT0]
    have hbound : ‖CTint χ a b lam T‖ ≤ 4 * (Tconst * Sconst) / T := by
      rw [CTint]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 2 * (Tconst * Sconst) / T ^ 2) ?_) ?_
      · intro y hy
        rw [Set.uIoc_of_le (by linarith : -T ≤ T), Set.mem_Ioc] at hy
        refine le_trans (FF_norm_le χ hχ ha hlam T y hTa) ?_
        have hnum : (Tconst * Sconst) * (Real.exp (-(lam * T)) + 1)
            ≤ 2 * (Tconst * Sconst) := by
          nlinarith [hexp, mul_nonneg Tconst_nonneg Sconst_pos.le]
        calc (Tconst * Sconst) * (Real.exp (-(lam * T)) + 1) / (T ^ 2 + y ^ 2)
            ≤ 2 * (Tconst * Sconst) / (T ^ 2 + y ^ 2) :=
              div_le_div_of_nonneg_right hnum (by positivity)
          _ ≤ 2 * (Tconst * Sconst) / T ^ 2 := by
              refine div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (mul_nonneg Tconst_nonneg Sconst_pos.le)) (by positivity) ?_
              nlinarith [sq_nonneg y]
      · rw [abs_of_pos (by linarith : (0 : ℝ) < T - (-T))]
        rw [show T - (-T) = 2 * T by ring, div_mul_eq_mul_div]
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < T ^ 2) hT0]
        ring_nf
        exact le_refl _
    exact hbound
  · have hb : Tendsto (fun T : ℝ => (4 * (Tconst * Sconst)) * T⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (4 * (Tconst * Sconst))
    refine hb.congr' ?_
    filter_upwards with T
    rw [div_eq_mul_inv]

private lemma Caint_tend {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {a b lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    Tendsto (fun T => Caint χ a b lam T) atTop (𝓝 0) := by
  have heq : (fun T => Caint χ a b lam T) =ᶠ[atTop]
      (fun T => I⁻¹ * (Aint χ a b lam T - Bint χ a b lam T) + CTint χ a b lam T) := by
    filter_upwards [rect_identity χ hχ ha] with T hT
    have h1 : Aint χ a b lam T - Bint χ a b lam T + I * CTint χ a b lam T
        = I * Caint χ a b lam T := sub_eq_zero.mp hT
    have h2 : Caint χ a b lam T
        = I⁻¹ * (Aint χ a b lam T - Bint χ a b lam T + I * CTint χ a b lam T) := by
      rw [h1, ← mul_assoc, inv_mul_cancel₀ I_ne_zero, one_mul]
    rw [h2]
    ring_nf
    rw [mul_inv_cancel₀ I_ne_zero]
    ring
  have hAB : Tendsto (fun T => Aint χ a b lam T - Bint χ a b lam T) atTop (𝓝 0) := by
    simpa using (Aint_tend χ hχ ha hlam).sub (Bint_tend χ hχ ha hlam)
  have h1 : Tendsto (fun T => I⁻¹ * (Aint χ a b lam T - Bint χ a b lam T)) atTop (𝓝 0) := by
    simpa using hAB.const_mul I⁻¹
  have hRHS : Tendsto (fun T => I⁻¹ * (Aint χ a b lam T - Bint χ a b lam T)
      + CTint χ a b lam T) atTop (𝓝 0) := by
    simpa using h1.add (CTint_tend χ hχ ha hlam)
  exact Tendsto.congr' heq.symm hRHS

private lemma FF_integral_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {a b lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    (∫ y : ℝ, FF χ a b lam ((a : ℂ) + (y : ℂ) * I)) = 0 := by
  have hline_int := integrable_FF_line (b := b) χ hχ ha hlam
  have hphi : AECover volume atTop (fun T : ℝ => Set.Ioc (-T) T) :=
    aecover_Ioc tendsto_neg_atTop_atBot tendsto_id
  have hCa_tend' : Tendsto (fun T : ℝ => ∫ y in Set.Ioc (-T) T, FF χ a b lam ((a : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
    refine (Caint_tend (b := b) χ hχ ha hlam).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    rw [Caint, intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact AECover.integral_eq_of_tendsto hphi 0 hline_int hCa_tend'

/-- The key integral vanishes. -/
theorem LFunction_logDeriv_rightHalf_kernel_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (a lam b : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    (∫ u : ℝ, logDeriv (DirichletCharacter.LFunction χ) ((3/2:ℝ) - ((b - u : ℝ) : ℂ) * Complex.I) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2))) = 0 := by
  have key : (∫ u : ℝ, FF χ a b lam ((a : ℂ) + (u : ℂ) * Complex.I)) = 0 :=
    FF_integral_eq_zero χ hχ ha hlam
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only [FF, kern]
  rw [show ((3/2:ℝ):ℂ) - ((b - u : ℝ) : ℂ) * I = (a : ℂ) + (u : ℂ) * I + cc a b from by
    rw [cc]; push_cast; ring]

end

end Commons.NumberTheory.DirichletCharacter