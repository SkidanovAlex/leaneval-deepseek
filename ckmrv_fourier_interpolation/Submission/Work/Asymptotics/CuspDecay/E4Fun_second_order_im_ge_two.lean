import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Modular.E4_qExpansion_coeff

namespace Work.Asymptotics.CuspDecay

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold Bundle

noncomputable section

/-! ## Elementary estimates

The two ingredients of the explicit second-order `q`-expansion bound are an elementary
comparison of the shifted fourth power with a geometric sequence and the numerical bound
`e^{-4π} ≤ 1/40000`. -/

/-- `((m : ℝ) + 2)⁴ ≤ 16·8^m` for every `m : ℕ`.  (`8 = 2³` is the smallest integer base for
which the induction is uniform, and `16` dominates the finitely many small values: the cases
`m = 0` are equal and `m = 1` gives `81 ≤ 128`.) -/
private lemma pow_add_two_pow_four_le (m : ℕ) : ((m : ℝ) + 2) ^ 4 ≤ 16 * (8 : ℝ) ^ m := by
  have aux : ∀ k : ℕ, 1 ≤ k → ((k : ℝ) + 2) ^ 4 ≤ 16 * (8 : ℝ) ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hstep : ((n : ℝ) + 3) ≤ (4 / 3) * ((n : ℝ) + 2) := by linarith
      have h2 : ((n : ℝ) + 3) ^ 4 ≤ ((4 / 3 : ℝ) * ((n : ℝ) + 2)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hstep 4
      have h3 : ((4 / 3 : ℝ) * ((n : ℝ) + 2)) ^ 4 = (256 / 81) * ((n : ℝ) + 2) ^ 4 := by ring
      have h4 : (256 / 81 : ℝ) * ((n : ℝ) + 2) ^ 4 ≤ 8 * ((n : ℝ) + 2) ^ 4 := by
        nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2) 4]
      calc (((n + 1 : ℕ) : ℝ) + 2) ^ 4 = ((n : ℝ) + 3) ^ 4 := by push_cast; ring
        _ ≤ ((4 / 3 : ℝ) * ((n : ℝ) + 2)) ^ 4 := h2
        _ = (256 / 81) * ((n : ℝ) + 2) ^ 4 := h3
        _ ≤ 8 * ((n : ℝ) + 2) ^ 4 := h4
        _ ≤ 8 * (16 * (8 : ℝ) ^ n) := by linarith
        _ = 16 * (8 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; norm_num
  · exact aux m hm

/-- `∑_{m ≥ 0} ((m : ℝ) + 2)⁴ rᵐ` is summable for `0 ≤ r` and `8 r < 1`. -/
private lemma summable_pow_add_two (r : ℝ) (hr0 : 0 ≤ r) (hr : 8 * r < 1) :
    Summable (fun m : ℕ => ((m : ℝ) + 2) ^ 4 * r ^ m) := by
  have h8r0 : 0 ≤ 8 * r := by linarith
  have hgeo : Summable (fun m : ℕ => (8 * r) ^ m) := summable_geometric_of_lt_one h8r0 hr
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (by positivity) (pow_nonneg hr0 m))
    (fun m => ?_) (Summable.mul_left 16 hgeo)
  have h1 := pow_add_two_pow_four_le m
  calc ((m : ℝ) + 2) ^ 4 * r ^ m ≤ (16 * (8 : ℝ) ^ m) * r ^ m :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hr0 m)
    _ = 16 * (8 * r) ^ m := by rw [mul_pow]; ring

/-- `∑_{m ≥ 0} ((m : ℝ) + 2)⁴ rᵐ ≤ 16 (1 - 8r)⁻¹` for `0 ≤ r` and `8 r < 1`:
the comparison `((m : ℝ) + 2)⁴ ≤ 16·8^m` turns the series into `16 ∑ (8r)ᵐ`. -/
private lemma tsum_pow_add_two_le (r : ℝ) (hr0 : 0 ≤ r) (hr : 8 * r < 1) :
    ∑' m : ℕ, ((m : ℝ) + 2) ^ 4 * r ^ m ≤ 16 * (1 - 8 * r)⁻¹ := by
  have h8r0 : 0 ≤ 8 * r := by linarith
  have hgeo : Summable (fun m : ℕ => (8 * r) ^ m) := summable_geometric_of_lt_one h8r0 hr
  have hgeo16 : Summable (fun m : ℕ => (16 : ℝ) * (8 * r) ^ m) := Summable.mul_left 16 hgeo
  have hterm : ∀ m : ℕ, ((m : ℝ) + 2) ^ 4 * r ^ m ≤ 16 * (8 * r) ^ m := by
    intro m
    have h1 := pow_add_two_pow_four_le m
    calc ((m : ℝ) + 2) ^ 4 * r ^ m ≤ (16 * (8 : ℝ) ^ m) * r ^ m :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hr0 m)
      _ = 16 * (8 * r) ^ m := by rw [mul_pow]; ring
  have hlhs := summable_pow_add_two r hr0 hr
  calc ∑' m : ℕ, ((m : ℝ) + 2) ^ 4 * r ^ m ≤ ∑' m : ℕ, (16 : ℝ) * (8 * r) ^ m :=
        Summable.tsum_le_tsum hterm hlhs hgeo16
    _ = 16 * (1 - 8 * r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one h8r0 hr]

/-- `e^{4π} ≥ 40000`, equivalently `e^{-4π} ≤ 1/40000`. -/
private lemma exp_four_pi_ge : (40000 : ℝ) ≤ Real.exp (4 * Real.pi) := by
  have h12 : (12 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : Real.exp 12 ≤ Real.exp (4 * Real.pi) := Real.exp_le_exp.mpr h12
  have h2 : (Real.exp 1) ^ 12 = Real.exp 12 := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num
  have h3 : (2.7182818283 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 12
  have h4 : (40000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
  linarith

/-- `‖q(u)‖ ≤ 1/40000` for `Im u ≥ 2`, i.e. `‖q u‖ = e^{-2π Im u} ≤ e^{-4π} ≤ 10^{-4.6}`. -/
private lemma qParam_norm_le {u : ℍ} (hu : 2 ≤ u.im) :
    ‖Work.Kernels.qParamFun u‖ ≤ 1 / 40000 := by
  have hq_eq : Function.Periodic.qParam 1 (u : ℂ) = Work.Kernels.qParamFun u := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  have hqnorm : ‖Work.Kernels.qParamFun u‖ = Real.exp (-(2 * Real.pi * u.im)) := by
    rw [← hq_eq, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
    congr 1; ring
  rw [hqnorm]
  have h2 : (40000 : ℝ) ≤ Real.exp (4 * Real.pi) := exp_four_pi_ge
  have h3 : Real.exp (-(2 * Real.pi * u.im)) ≤ Real.exp (-(2 * Real.pi * 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hu])
  have h4 : Real.exp (-(2 * Real.pi * 2)) = 1 / Real.exp (4 * Real.pi) := by
    rw [show -(2 * Real.pi * 2) = -(4 * Real.pi) by ring, Real.exp_neg, one_div]
  have h5 : 1 / Real.exp (4 * Real.pi) ≤ 1 / 40000 :=
    one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- Second-order `q`-expansion of `E₄` on the region `Im ≥ 2`, with an **explicit** constant.

On `Im u ≥ 2` one has `‖q u‖ = e^{-2π Im u} ≤ e^{-4π} ≤ 10^{-5}`.  The `q`-expansion
`E₄ = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ` (`Work.Modular.E4_qExpansion_coeff`, via
`UpperHalfPlane.hasSum_qExpansion`) together with the elementary comparisons
`σ₃(m+2) ≤ (m+2)⁴` and `(m+2)⁴ ≤ 16·8^m` (valid for all `m : ℕ`) gives the tail bound
`∑_{m ≥ 0} (m+2)⁴ ‖q‖^m ≤ 16/(1 - 8‖q‖) ≤ 16.01` (using `‖q u‖ ≤ 10^{-5}`), hence
`‖E₄ u - 1 - 240 q u‖ ≤ 240 · 16.01 · ‖q u‖² < 4000 ‖q u‖²`.

The point of the explicit constant is that it must be comparable with the concrete number
`‖q u‖ ≤ 10^{-5}`; an existential constant from `Work.Residues.E4FunSecondOrder` cannot be. -/
theorem E4Fun_second_order_im_ge_two (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖Work.Kernels.E4Fun u - 1 - 240 * Work.Kernels.qParamFun u‖
      ≤ 4000 * ‖Work.Kernels.qParamFun u‖ ^ 2 := by
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E4Fun)
    one_pos hper hhol hbdd u
  have hq_eq : Function.Periodic.qParam 1 (u : ℂ) = Work.Kernels.qParamFun u := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  have hs2 := (hasSum_nat_add_iff' 2).mpr hs
  rw [hq_eq] at hs2
  -- the coefficients
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff]
    norm_num
  have hc1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 1 = 240 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl,
      Work.Modular.E4_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have hsum2 : (∑ i ∈ Finset.range 2,
      (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff i
        • Work.Kernels.qParamFun u ^ i) = 1 + 240 * Work.Kernels.qParamFun u := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1]
    simp [smul_eq_mul]
  have htsum : (∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
        • Work.Kernels.qParamFun u ^ (n + 2))
      = Work.Kernels.E4Fun u - 1 - 240 * Work.Kernels.qParamFun u := by
    rw [hsum2] at hs2
    rw [hs2.tsum_eq]
    ring
  -- coefficient bound `‖c_{n+2}‖ ≤ 240 ((n : ℝ) + 2)⁴`
  have hcoeff : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)‖
        ≤ 240 * ((n : ℝ) + 2) ^ 4 := by
    intro n
    have hne : (n + 2 : ℕ) ≠ 0 := by omega
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl,
      Work.Modular.E4_qExpansion_coeff (n + 2), if_neg hne]
    have hσ : ((ArithmeticFunction.sigma 3 (n + 2) : ℕ) : ℝ) ≤ ((n : ℝ) + 2) ^ 4 := by
      have h' : ((ArithmeticFunction.sigma 3 (n + 2) : ℕ) : ℝ)
          ≤ (((n + 2) ^ 4 : ℕ) : ℝ) := by
        exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 3 (n + 2)
      push_cast at h'
      linarith
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  -- the norm of `q`
  set r : ℝ := ‖Work.Kernels.qParamFun u‖ with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; exact norm_nonneg _
  have hr : r ≤ 1 / 40000 := by rw [hrdef]; exact qParam_norm_le hu
  have hr8 : 8 * r < 1 := by
    have : 8 * r ≤ 8 * (1 / 40000) := by linarith
    linarith
  have hSsum := summable_pow_add_two r hr0 hr8
  have hS := tsum_pow_add_two_le r hr0 hr8
  -- termwise bound, tail of the series
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
        • Work.Kernels.qParamFun u ^ (n + 2)‖
      ≤ (240 * r ^ 2) * (((n : ℝ) + 2) ^ 4 * r ^ n) := by
    intro n
    have hc := hcoeff n
    have hrpow : ‖Work.Kernels.qParamFun u ^ (n + 2)‖ = r ^ (n + 2) := by
      rw [norm_pow, hrdef]
    rw [smul_eq_mul, norm_mul, hrpow]
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)‖ * r ^ (n + 2)
        ≤ (240 * ((n : ℝ) + 2) ^ 4) * r ^ (n + 2) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (240 * r ^ 2) * (((n : ℝ) + 2) ^ 4 * r ^ n) := by rw [pow_add]; ring
  have hmaj : Summable (fun n : ℕ => (240 * r ^ 2) * (((n : ℝ) + 2) ^ 4 * r ^ n)) :=
    hSsum.mul_left (240 * r ^ 2)
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
        • Work.Kernels.qParamFun u ^ (n + 2)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  -- numerical comparison
  have hden : (1 - 8 * r)⁻¹ ≤ 25 / 24 := by
    have h1 : 8 * r ≤ 1 / 25 := by
      have : 8 * r ≤ 8 * (1 / 40000) := by linarith
      linarith
    have h2 : (24 : ℝ) / 25 ≤ 1 - 8 * r := by linarith
    have h3 : (0 : ℝ) < 1 - 8 * r := by linarith
    have h4 : (1 - 8 * r)⁻¹ ≤ ((24 : ℝ) / 25)⁻¹ :=
      (inv_le_inv₀ h3 (by norm_num)).mpr h2
    have h5 : ((24 : ℝ) / 25)⁻¹ = 25 / 24 := by norm_num
    linarith
  have hfinal : 240 * (16 * (1 - 8 * r)⁻¹) ≤ 4000 := by
    have h1 : 16 * (1 - 8 * r)⁻¹ ≤ 16 * (25 / 24) :=
      mul_le_mul_of_nonneg_left hden (by norm_num)
    linarith
  calc ‖Work.Kernels.E4Fun u - 1 - 240 * Work.Kernels.qParamFun u‖
      = ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
          • Work.Kernels.qParamFun u ^ (n + 2)‖ := by rw [htsum]
    _ ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
          • Work.Kernels.qParamFun u ^ (n + 2)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (240 * r ^ 2) * (((n : ℝ) + 2) ^ 4 * r ^ n) :=
        Summable.tsum_le_tsum hterm hsumm hmaj
    _ = (240 * r ^ 2) * ∑' n : ℕ, (((n : ℝ) + 2) ^ 4 * r ^ n) := tsum_mul_left
    _ ≤ (240 * r ^ 2) * (16 * (1 - 8 * r)⁻¹) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (240 * (16 * (1 - 8 * r)⁻¹)) * r ^ 2 := by ring
    _ ≤ 4000 * r ^ 2 := mul_le_mul_of_nonneg_right hfinal (pow_nonneg hr0 2)

end

end Work.Asymptotics.CuspDecay
