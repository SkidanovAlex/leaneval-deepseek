import Mathlib
import Submission.Work.A14D.ppc_aux

namespace Work.A14D

open PowerSeries

/-!
# `deriv_evp_pureB6`

The derivative of the analytic function `z ↦ evp (B₇ ∘ y) z` on the open unit disc, where
`B₇ = ∫ B₄/y` is the seventh pure function of Calegari–Dimitrov–Tang (`Submission.CDTPlan.B7`,
i.e. `Submission.CDTPlan.pureB 6`) and `y = x²/(x−1)` is the symmetrisation coordinate.

The content is the `x`-side identity `Work.C7.g67_deriv` (specialised to `g 6 = B₇ ∘ y`,
`g 3 = B₄ ∘ y`)

  `(x − 1)² · (B₇ ∘ y)' = (x − 2)² · (2 Li₂(x) + ½ log(1−x)²)`,

evaluated with `Work.CPull.evp` on the unit disc; `evp` is multiplicative on the disc
(`Work.CPull.evpMul`) and `evp (derivative f) z = deriv (evp f) z` for polynomially growing
coefficients (`Work.A14D.evp_deriv`).
-/

/-! ## 1. Evaluation of polynomial series -/

/-- The evaluation `Work.CPull.evp` of the power series attached to a polynomial is the usual
evaluation of that polynomial at `z`. -/
private lemma evp_coe_polynomial (p : Polynomial ℚ) (z : ℂ) :
    Work.CPull.evp ((p : Polynomial ℚ) : PowerSeries ℚ) z
      = Polynomial.eval₂ (algebraMap ℚ ℂ) z p := by
  rw [Work.CPull.evp, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [tsum_eq_sum (s := p.support) (fun n hn => by
      have h0 : p.coeff n = 0 := by
        by_contra h
        exact hn ((Polynomial.mem_support_iff).mpr h)
      rw [Polynomial.coeff_coe, h0]
      simp)]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Polynomial.coeff_coe]
  rfl

/-- The coercion of `(2 : Polynomial ℚ)` to power series is `(2 : PowerSeries ℚ)`. -/
private lemma coe_two_poly : ((2 : Polynomial ℚ) : PowerSeries ℚ) = (2 : PowerSeries ℚ) := by
  rw [show (2 : Polynomial ℚ) = Polynomial.C 2 from rfl, Polynomial.coe_C,
    PowerSeries.C_eq_algebraMap, map_ofNat]

private lemma evp_sub_one_sq (z : ℂ) :
    Work.CPull.evp (((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2) z = (z - 1) ^ 2 := by
  have hcoe : ((↑((Polynomial.X - 1 : Polynomial ℚ) ^ 2) : PowerSeries ℚ))
      = ((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2 := by
    rw [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_one]
  rw [← hcoe, evp_coe_polynomial, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_one]

private lemma evp_sub_two_sq (z : ℂ) :
    Work.CPull.evp (((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2) z = (z - 2) ^ 2 := by
  have hcoe : ((↑((Polynomial.X - 2 : Polynomial ℚ) ^ 2) : PowerSeries ℚ))
      = ((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2 := by
    rw [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_X, coe_two_poly]
  rw [← hcoe, evp_coe_polynomial, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X]
  norm_num

/-! ## 2. Coefficients of `(x − c)²` -/

private lemma coe_two_PS : (PowerSeries.C (2 : ℚ) : PowerSeries ℚ) = 2 := by
  rw [PowerSeries.C_eq_algebraMap, map_ofNat]

private lemma coe_four_PS : (PowerSeries.C (4 : ℚ) : PowerSeries ℚ) = 4 := by
  rw [PowerSeries.C_eq_algebraMap, map_ofNat]

private lemma coeff_sub_one_sq (n : ℕ) :
    PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2)
      = if n = 0 then 1 else if n = 1 then -2 else if n = 2 then 1 else 0 := by
  have hf : ((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2
      = (PowerSeries.X : PowerSeries ℚ) ^ 2 - PowerSeries.C 2 * PowerSeries.X + 1 := by
    rw [coe_two_PS]; ring
  rw [hf, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_X, PowerSeries.coeff_one]
  split_ifs <;> (first | omega | norm_num)

private lemma coeff_sub_two_sq (n : ℕ) :
    PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2)
      = if n = 0 then 4 else if n = 1 then -4 else if n = 2 then 1 else 0 := by
  have hf : ((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2
      = (PowerSeries.X : PowerSeries ℚ) ^ 2 - PowerSeries.C 4 * PowerSeries.X
        + PowerSeries.C 4 := by
    rw [coe_four_PS]; ring
  rw [hf, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_X, PowerSeries.coeff_C]
  split_ifs <;> (first | omega | norm_num)

/-! ## 3. Coefficient bounds and summability on the unit disc -/

private lemma norm_ratCast_c (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := by simp

private lemma norm_coeff_sub_one_sq_le (n : ℕ) :
    ‖((PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2) : ℚ) : ℂ)‖ ≤ 2 := by
  rw [coeff_sub_one_sq n]
  split_ifs <;> norm_num

private lemma norm_coeff_sub_two_sq_le (n : ℕ) :
    ‖((PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2) : ℚ) : ℂ)‖ ≤ 4 := by
  rw [coeff_sub_two_sq n]
  split_ifs <;> norm_num

private lemma norm_coeff_Li2ps_le (n : ℕ) :
    ‖((PowerSeries.coeff n Work.C7.Li2ps : ℚ) : ℂ)‖ ≤ 1 := by
  rw [Work.C7.coeff_Li2ps]
  split_ifs with h
  · simp
  · rw [norm_ratCast_c]
    have hn : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
    rw [abs_of_nonneg (by positivity), ← Rat.cast_one, Rat.cast_le]
    exact inv_le_one_of_one_le₀ (by nlinarith)

private lemma norm_coeff_Lps_le (n : ℕ) :
    ‖((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ)‖ ≤ 1 := by
  rw [Work.C7.coeff_Lps]
  split_ifs with h
  · simp
  · rw [Rat.cast_neg, norm_neg, norm_ratCast_c]
    have hn : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
    rw [abs_of_nonneg (by positivity), ← Rat.cast_one, Rat.cast_le]
    exact inv_le_one_of_one_le₀ (by nlinarith)

private lemma summable_geom_z {z : ℂ} (hz : ‖z‖ < 1) : Summable fun n : ℕ => ‖z‖ ^ n :=
  summable_geometric_of_norm_lt_one (by simpa using hz)

private lemma summable_coeff_of_bound {f : PowerSeries ℚ} {C : ℝ}
    (hb : ∀ n, ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ C) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geom_z hz).mul_left C)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hb n) (pow_nonneg (norm_nonneg z) n)

private lemma summable_norm_Li2ps {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖((PowerSeries.coeff n Work.C7.Li2ps : ℚ) : ℂ) * z ^ n‖ :=
  summable_coeff_of_bound (C := 1) norm_coeff_Li2ps_le hz

private lemma summable_norm_Lps {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n‖ :=
  summable_coeff_of_bound (C := 1) norm_coeff_Lps_le hz

private lemma summable_norm_sq_sub_one {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2) : ℚ) : ℂ) * z ^ n‖ :=
  summable_coeff_of_bound (C := 2) norm_coeff_sub_one_sq_le hz

private lemma summable_norm_sq_sub_two {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2) : ℚ) : ℂ) * z ^ n‖ :=
  summable_coeff_of_bound (C := 4) norm_coeff_sub_two_sq_le hz

private lemma summable_norm_C_mul {c : ℚ} {f : PowerSeries ℚ} {z : ℂ}
    (h : Summable fun n : ℕ => ‖((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n‖) :
    Summable fun n : ℕ => ‖((PowerSeries.coeff n (PowerSeries.C c * f) : ℚ) : ℂ) * z ^ n‖ := by
  refine (h.mul_left ‖(c : ℂ)‖).congr (fun n => ?_)
  rw [PowerSeries.coeff_C_mul]
  push_cast
  simp only [norm_mul]
  ring

private lemma summable_norm_Qps {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖((PowerSeries.coeff n
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2) : ℚ) : ℂ) * z ^ n‖ := by
  have h1 : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (2 * Work.C7.Li2ps) : ℚ) : ℂ) * z ^ n‖ :=
    summable_norm_C_mul (c := 2) (summable_norm_Li2ps hz)
  have h2 : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2) : ℚ) : ℂ)
        * z ^ n‖ := by
    have hLL := (Work.CPull.evpMul Work.C7.Lps Work.C7.Lps z
      (summable_norm_Lps hz) (summable_norm_Lps hz)).1
    simpa [pow_two] using summable_norm_C_mul (c := 1 / 2) hLL
  have hsplit : (fun n : ℕ => ‖((PowerSeries.coeff n
          (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2) : ℚ) : ℂ)
            * z ^ n‖)
      = fun n : ℕ => ‖((PowerSeries.coeff n (2 * Work.C7.Li2ps) : ℚ) : ℂ) * z ^ n
          + ((PowerSeries.coeff n (PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2) : ℚ) : ℂ)
            * z ^ n‖ := by
    funext n
    congr 1
    rw [map_add]
    push_cast
    ring
  rw [hsplit]
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_add_le _ _) (h1.add h2)

/-! ## 4. Evaluation of `2 Li₂ + ½ L²` -/

private lemma evp_C_mul' (c : ℚ) (f : PowerSeries ℚ) (z : ℂ) :
    Work.CPull.evp (PowerSeries.C c * f) z = (c : ℂ) * Work.CPull.evp f z := by
  rw [Work.CPull.evp, Work.CPull.evp]
  have h : (fun n => ((PowerSeries.coeff n (PowerSeries.C c * f) : ℚ) : ℂ) * z ^ n)
      = fun n => (c : ℂ) * (((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n) := by
    funext n
    rw [PowerSeries.coeff_C_mul]
    push_cast
    ring
  rw [h, tsum_mul_left]

private lemma evp_Qps (z : ℂ) (hz : ‖z‖ < 1) :
    Work.CPull.evp (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2) z
      = 2 * Work.CPull.evp Work.C7.Li2ps z + (1 / 2) * (Complex.log (1 - z)) ^ 2 := by
  have hLi2n := summable_norm_Li2ps hz
  have hLpsn := summable_norm_Lps hz
  have hLLn := (Work.CPull.evpMul Work.C7.Lps Work.C7.Lps z hLpsn hLpsn).1
  have hLi2s : Summable (fun n => ((PowerSeries.coeff n Work.C7.Li2ps : ℚ) : ℂ) * z ^ n) :=
    hLi2n.of_norm
  have h2Li2s : Summable (fun n =>
      ((PowerSeries.coeff n (2 * Work.C7.Li2ps) : ℚ) : ℂ) * z ^ n) := by
    refine (hLi2s.mul_left (2 : ℂ)).congr (fun n => ?_)
    rw [show (2 * Work.C7.Li2ps : PowerSeries ℚ) = PowerSeries.C 2 * Work.C7.Li2ps from rfl,
      PowerSeries.coeff_C_mul]
    push_cast
    ring
  have hLLs : Summable (fun n =>
      ((PowerSeries.coeff n (Work.C7.Lps * Work.C7.Lps) : ℚ) : ℂ) * z ^ n) :=
    hLLn.of_norm
  have hCLLs : Summable (fun n =>
      ((PowerSeries.coeff n (PowerSeries.C (1 / 2 : ℚ) * (Work.C7.Lps * Work.C7.Lps)) : ℚ) : ℂ)
        * z ^ n) := by
    refine (hLLs.mul_left (((1 / 2 : ℚ) : ℂ))).congr (fun n => ?_)
    rw [PowerSeries.coeff_C_mul]
    push_cast
    ring
  have hLval : Work.CPull.evp Work.C7.Lps z = Complex.log (1 - z) := Work.C7.evA_Lps hz
  rw [show 2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2
        = 2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * (Work.C7.Lps * Work.C7.Lps)
        from by rw [pow_two]]
  rw [(Work.CPull.evp_add_mul (2 * Work.C7.Li2ps)
        (PowerSeries.C (1 / 2 : ℚ) * (Work.C7.Lps * Work.C7.Lps)) z h2Li2s hCLLs).1]
  rw [show (2 * Work.C7.Li2ps : PowerSeries ℚ) = PowerSeries.C 2 * Work.C7.Li2ps from rfl]
  rw [evp_C_mul', evp_C_mul',
    (Work.CPull.evpMul Work.C7.Lps Work.C7.Lps z hLpsn hLpsn).2.2.2, hLval, pow_two]
  push_cast
  ring

/-! ## 5. The product identity `(x−1)² · (B₇∘y)' = (x−2)² · (2Li₂ + ½L²)` and its evaluation -/

/-- The `x`-side identity of `Work.C7.g67_deriv` for `g 6 = B₇ ∘ y`. -/
private lemma g67_pureB6 :
    (((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2)
        * PowerSeries.derivative (R := ℚ)
            ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY)
      = (((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2)
        * (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2) := by
  have h67 := Work.C7.g67_deriv Work.C7.g_form.2.1 Work.C7.g_form.2.2
    Work.C17.B6_deriv Work.C17.B7_deriv
  have h := h67.2
  rw [show Work.C7.g (6 : Fin 7)
      = (Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY from rfl] at h
  exact h

/-- Evaluation of the left-hand side of `g67_pureB6`. -/
private lemma evp_prod_left (z : ℂ) (hz : ‖z‖ < 1) :
    Work.CPull.evp ((((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2)
        * PowerSeries.derivative (R := ℚ)
            ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY)) z
      = (z - 1) ^ 2 * Work.CPull.evp (PowerSeries.derivative (R := ℚ)
            ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY)) z := by
  obtain ⟨C, hC, k, hbound⟩ := pureB_subst_poly_growth (6 : Fin 7)
  obtain ⟨C', hC', k', hbound'⟩ :=
    poly_growth_deriv (f := (Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY) hC hbound
  have hHn : Summable fun n : ℕ => ‖((PowerSeries.coeff n
      (PowerSeries.derivative (R := ℚ) ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY))
      : ℚ) : ℂ) * z ^ n‖ :=
    summable_abs_coeff_of_poly_growth hC' hbound' hz
  rw [(Work.CPull.evpMul (((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2) _ z
    (summable_norm_sq_sub_one hz) hHn).2.2.2, evp_sub_one_sq z]

/-- Evaluation of the right-hand side of `g67_pureB6`. -/
private lemma evp_prod_right (z : ℂ) (hz : ‖z‖ < 1) :
    Work.CPull.evp ((((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2)
        * (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2)) z
      = (z - 2) ^ 2 * (2 * Work.CPull.evp Work.C7.Li2ps z
          + (1 / 2) * (Complex.log (1 - z)) ^ 2) := by
  rw [(Work.CPull.evpMul (((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2) _ z
    (summable_norm_sq_sub_two hz) (summable_norm_Qps hz)).2.2.2, evp_sub_two_sq z]
  rw [evp_Qps z hz]

/-- The value of `evp ((B₇∘y)')` at `z`, `‖z‖ < 1`. -/
private theorem evp_deriv_pureB6_val (z : ℂ) (hz : ‖z‖ < 1) :
    Work.CPull.evp (PowerSeries.derivative (R := ℚ)
        ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY)) z
      = ((z - 2) ^ 2 / (z - 1) ^ 2)
        * (2 * Work.CPull.evp Work.C7.Li2ps z + (1 / 2) * (Complex.log (1 - z)) ^ 2) := by
  have heq : (z - 1) ^ 2 * Work.CPull.evp (PowerSeries.derivative (R := ℚ)
        ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY)) z
      = (z - 2) ^ 2 * (2 * Work.CPull.evp Work.C7.Li2ps z
          + (1 / 2) * (Complex.log (1 - z)) ^ 2) := by
    rw [← evp_prod_left z hz, g67_pureB6, evp_prod_right z hz]
  have hz1 : ((z - 1) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr (by intro h; rw [h] at hz; norm_num at hz))
  have h1 : ((z - 1) ^ 2)⁻¹ * ((z - 1) ^ 2 * Work.CPull.evp (PowerSeries.derivative (R := ℚ)
        ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY)) z)
      = ((z - 1) ^ 2)⁻¹ * ((z - 2) ^ 2 * (2 * Work.CPull.evp Work.C7.Li2ps z
          + (1 / 2) * (Complex.log (1 - z)) ^ 2)) := by
    rw [heq]
  rw [← mul_assoc, inv_mul_cancel₀ hz1, one_mul] at h1
  rw [h1, div_eq_mul_inv]
  ring

/-! ## 6. The statement -/

theorem deriv_evp_pureB6 (z : ℂ) (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt (fun w : ℂ =>
        Work.CPull.evp ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY) w)
      (((z - 2) ^ 2 / (z - 1) ^ 2) * (2 * Work.CPull.evp Work.C7.Li2ps z
        + (1 / 2) * (Complex.log (1 - z)) ^ 2)) z := by
  obtain ⟨C, hC, k, hbound⟩ := pureB_subst_poly_growth (6 : Fin 7)
  have hderiv : Work.CPull.evp (PowerSeries.derivative (R := ℚ)
        ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY)) z
      = deriv (fun w : ℂ => Work.CPull.evp
          ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY) w) z :=
    evp_deriv hC hbound hz
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => Work.CPull.evp
      ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY) w) z :=
    (differentiableOn_evp_of_poly_growth hC hbound).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hz))
  have hd := hdiff.hasDerivAt
  rw [← hderiv] at hd
  rw [evp_deriv_pureB6_val z hz] at hd
  exact hd

end Work.A14D
