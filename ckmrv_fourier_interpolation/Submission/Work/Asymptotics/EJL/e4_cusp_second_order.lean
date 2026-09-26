import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Modular.E4_qExpansion_coeff

namespace Work.Asymptotics.EJL

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold Bundle

noncomputable section

/-! ## Elementary estimates

The second-order `q`-expansion bound for `E₄` needs the comparison `n⁴ ≤ 4·3ⁿ` of the fourth
power with a geometric sequence (the same one used by `Work.Asymptotics.E4Fun_sub_one_explicit`,
reproved here since it is `private` there), together with the numerical bound
`e^{-2π} ≤ 1/6`.  The last one is what makes the constant `20000` work: with
`r = ‖q‖ ≤ 1/6` one has `3r ≤ 1/2` and therefore
`1/(1-3r) ≤ 2`, which is exactly what the tail estimate below needs. -/

/-- `n⁴ ≤ 4·3ⁿ` for every `n : ℕ`. -/
private lemma pow_four_le_four_mul_three_pow (n : ℕ) : n ^ 4 ≤ 4 * 3 ^ n := by
  have aux : ∀ m : ℕ, 5 ≤ m → ((m : ℝ)) ^ 4 ≤ 4 * (3 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hk5 : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
      have h1 : (k : ℝ) + 1 ≤ (6 / 5) * (k : ℝ) := by linarith
      have h2 : ((k : ℝ) + 1) ^ 4 ≤ ((6 / 5) * (k : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) h1 4
      have h3 : ((6 / 5) * (k : ℝ)) ^ 4 = (1296 / 625) * (k : ℝ) ^ 4 := by ring
      have h4 : (1296 / 625 : ℝ) * (k : ℝ) ^ 4 ≤ 3 * (k : ℝ) ^ 4 := by
        nlinarith [pow_nonneg hk0 4]
      have h5 : 3 * (k : ℝ) ^ 4 ≤ 3 * (4 * (3 : ℝ) ^ k) := by linarith
      have h6 : 3 * (4 * (3 : ℝ) ^ k) = 4 * (3 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      calc (((k + 1 : ℕ)) : ℝ) ^ 4 = ((k : ℝ) + 1) ^ 4 := by push_cast; ring
        _ ≤ ((6 / 5) * (k : ℝ)) ^ 4 := h2
        _ = (1296 / 625) * (k : ℝ) ^ 4 := h3
        _ ≤ 3 * (k : ℝ) ^ 4 := h4
        _ ≤ 4 * (3 : ℝ) ^ (k + 1) := by rw [← h6]; linarith
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> norm_num
  · have h : ((n : ℝ)) ^ 4 ≤ 4 * (3 : ℝ) ^ n := aux n hn
    exact_mod_cast h

/-- The form of `pow_four_le_four_mul_three_pow` used for the `q`-expansion:
`((n : ℝ) + 1)⁴ ≤ 4·3^{n+1}`. -/
private lemma pow_four_succ_le (n : ℕ) : ((n : ℝ) + 1) ^ 4 ≤ 4 * 3 ^ (n + 1) := by
  have h := pow_four_le_four_mul_three_pow (n + 1)
  have h' : (((n + 1 : ℕ)) : ℝ) ^ 4 ≤ 4 * (3 : ℝ) ^ (n + 1) := by exact_mod_cast h
  simpa using h'

/-- `((n : ℝ) + 2)⁴ ≤ 4·3^{n+2}`, the shifted form needed for the tail starting at `n = 2`. -/
private lemma pow_four_two_le (n : ℕ) : ((n : ℝ) + 2) ^ 4 ≤ 4 * (3 : ℝ) ^ (n + 2) := by
  have h1 := pow_four_succ_le (n + 1)
  have h2 : ((n : ℝ) + 2) = (((n + 1 : ℕ)) : ℝ) + 1 := by push_cast; ring
  rw [h2]
  exact h1

/-- `e^{-2π} ≤ 1/6`.  Only `π > 3` and `e^6 ≥ 6` are used; this is the numerical bound that
turns `1 - 3r ≥ 1/2` into the constant `20000` below. -/
private lemma exp_neg_two_pi_le_sixth : Real.exp (-(2 * Real.pi)) ≤ 1 / 6 := by
  have h1 : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-6) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-6) ≤ 1 / 6 := by
    rw [Real.exp_neg]
    have h6 : (6 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp 6]
    calc (Real.exp 6)⁻¹ ≤ ((6 : ℝ))⁻¹ := (inv_le_inv₀ (Real.exp_pos 6) (by norm_num)).mpr h6
      _ = 1 / 6 := by norm_num
  linarith

/-- The majorant of the second-order tail is summable: `(n+2)⁴ r^{n+2} ≤ 4 (3r)^{n+2}`. -/
private lemma summable_pow_four_shift_two (r : ℝ) (hr0 : 0 ≤ r) (hr : 3 * r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 2) ^ 4 * r ^ (n + 2)) := by
  have h3r0 : 0 ≤ 3 * r := by linarith
  have hgeo : Summable (fun n : ℕ => (3 * r) ^ n) := summable_geometric_of_lt_one h3r0 hr
  have hgeo2 : Summable (fun n : ℕ => (3 * r) ^ (n + 2)) :=
    (summable_nat_add_iff (f := fun m : ℕ => (3 * r) ^ m) 2).mpr hgeo
  have hgeo4 : Summable (fun n : ℕ => (4 : ℝ) * (3 * r) ^ (n + 2)) :=
    Summable.mul_left 4 hgeo2
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo4
  have h1 := pow_four_two_le n
  have h3 : (0 : ℝ) ≤ r ^ (n + 2) := pow_nonneg hr0 _
  calc ((n : ℝ) + 2) ^ 4 * r ^ (n + 2) ≤ (4 * 3 ^ (n + 2)) * r ^ (n + 2) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = 4 * (3 * r) ^ (n + 2) := by rw [mul_pow]; ring

/-- `∑_{n ≥ 0} (n+2)⁴ r^{n+2} ≤ 72 r²` for `0 ≤ r ≤ 1/6`: the comparison
`(n+2)⁴ ≤ 4·3^{n+2}` turns the series into `4 ∑ (3r)^{n+2} = 36 r²/(1-3r) ≤ 72 r²`. -/
private lemma tsum_pow_four_shift_two_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 6) :
    ∑' n : ℕ, ((n : ℝ) + 2) ^ 4 * r ^ (n + 2) ≤ 72 * r ^ 2 := by
  have h3r0 : 0 ≤ 3 * r := by linarith
  have h3r1 : 3 * r < 1 := by linarith
  have hgeo : Summable (fun n : ℕ => (3 * r) ^ n) := summable_geometric_of_lt_one h3r0 h3r1
  have hgeo2 : Summable (fun n : ℕ => (3 * r) ^ (n + 2)) :=
    (summable_nat_add_iff (f := fun m : ℕ => (3 * r) ^ m) 2).mpr hgeo
  have hgeo4 : Summable (fun n : ℕ => (4 : ℝ) * (3 * r) ^ (n + 2)) :=
    Summable.mul_left 4 hgeo2
  have hterm : ∀ n : ℕ, ((n : ℝ) + 2) ^ 4 * r ^ (n + 2) ≤ 4 * (3 * r) ^ (n + 2) := by
    intro n
    have h1 := pow_four_two_le n
    have h3 : (0 : ℝ) ≤ r ^ (n + 2) := pow_nonneg hr0 _
    calc ((n : ℝ) + 2) ^ 4 * r ^ (n + 2) ≤ (4 * 3 ^ (n + 2)) * r ^ (n + 2) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ = 4 * (3 * r) ^ (n + 2) := by rw [mul_pow]; ring
  have hlhs : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ 4 * r ^ (n + 2)) :=
    summable_pow_four_shift_two r hr0 h3r1
  have hshift : ∑' n : ℕ, (3 * r) ^ (n + 2) = (3 * r) ^ 2 * (1 - 3 * r)⁻¹ := by
    have h := Summable.sum_add_tsum_nat_add 2 hgeo
    rw [tsum_geometric_of_lt_one h3r0 h3r1] at h
    have h2 : (∑ i ∈ Finset.range 2, (3 * r) ^ i) = 1 + 3 * r := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]; ring
    rw [h2] at h
    have hpos : (0 : ℝ) < 1 - 3 * r := by linarith
    have hmain : ∑' i : ℕ, (3 * r) ^ (i + 2) = (1 - 3 * r)⁻¹ - (1 + 3 * r) := by linarith
    rw [hmain]
    field_simp
    ring
  have htsum : ∑' n : ℕ, ((n : ℝ) + 2) ^ 4 * r ^ (n + 2)
      ≤ 4 * ((3 * r) ^ 2 * (1 - 3 * r)⁻¹) := by
    calc ∑' n : ℕ, ((n : ℝ) + 2) ^ 4 * r ^ (n + 2)
        ≤ ∑' n : ℕ, (4 : ℝ) * (3 * r) ^ (n + 2) := Summable.tsum_le_tsum hterm hlhs hgeo4
      _ = 4 * (∑' n : ℕ, (3 * r) ^ (n + 2)) := tsum_mul_left
      _ = 4 * ((3 * r) ^ 2 * (1 - 3 * r)⁻¹) := by rw [hshift]
  have hpos : (0 : ℝ) < 1 - 3 * r := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ 1 - 3 * r := by linarith
  have hinv : (1 - 3 * r)⁻¹ ≤ 2 := by
    have h : (1 - 3 * r)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := (inv_le_inv₀ hpos (by norm_num)).mpr hhalf
    norm_num at h
    exact h
  calc ∑' n : ℕ, ((n : ℝ) + 2) ^ 4 * r ^ (n + 2)
      ≤ 4 * ((3 * r) ^ 2 * (1 - 3 * r)⁻¹) := htsum
    _ ≤ 4 * ((3 * r) ^ 2 * 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hinv (sq_nonneg (3 * r))
    _ = 72 * r ^ 2 := by ring

/-- For `Im τ ≥ 1`, the weight-four Eisenstein series satisfies `E₄(τ) = 1 + 240 q + O(q²)`
with the explicit constant `20000`, where `q = e^{2πiτ}`.

Proof route (see `Submission/Work/Asymptotics/E4Fun_sub_one_explicit.lean`, which proves the
first-order analogue `‖E₄ τ - 1‖ ≤ 20000 ‖q‖`): `UpperHalfPlane.hasSum_qExpansion` for
`ModularForm.E₄` gives `E₄ τ = Σ'ₙ cₙ qⁿ` with `c₀ = 1` and `cₙ = 240 σ₃(n)` for `n ≥ 1`
(`Work.Modular.E4_qExpansion_coeff`).  Dropping the first two terms and using
`ArithmeticFunction.sigma_le_pow_succ` (`σ₃(n) ≤ n⁴`) and `n⁴ ≤ 4·3ⁿ` (proved privately in the
file above; copy or reprove it) gives
`‖E₄ τ - 1 - 240 q‖ ≤ 240·4·Σ'_{n≥2}(3r)ⁿ = 8640 r²/(1-3r) ≤ 20000 r²`
where `r = ‖q‖ = e^{-2π Im τ} ≤ e^{-2π} ≤ 1/512` (so `3r ≤ 1/2`, `1-3r ≥ 509/512`).
Note: one needs `r ≤ 1/512` here, not the weaker `r ≤ 1/4` used in the first-order file. -/
-- Proof note: the argument below only uses `r ≤ 1/6`, which follows from `e^{-2π} ≤ 1/6`
-- (`exp_neg_two_pi_le_sixth`); then `1 - 3r ≥ 1/2` and
-- `8640 r²/(1-3r) ≤ 17280 r² ≤ 20000 r²`, so the sharp numerical input `1/512` is not needed.
theorem e4_cusp_second_order :
    ∀ w : UpperHalfPlane, 1 ≤ w.im →
      ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w‖
        ≤ 20000 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
  intro w hw
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E4Fun)
    one_pos hper hhol hbdd w
  have hs2 := (hasSum_nat_add_iff' 2).mpr hs
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff]
    norm_num
  have hc1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 1 = 240 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff 1]
    norm_num [ArithmeticFunction.sigma, Nat.divisors_one]
  have hq_eq : Function.Periodic.qParam 1 (w : ℂ) = Work.Kernels.qParamFun w := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  have hsum2 : (∑ i ∈ Finset.range 2,
      (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff i
        • Function.Periodic.qParam 1 (w : ℂ) ^ i) = 1 + 240 * Work.Kernels.qParamFun w := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hc1, hc0, hq_eq]
    simp [smul_eq_mul]
  rw [hsum2] at hs2
  have hs3 : HasSum (fun n : ℕ =>
      (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
        • Work.Kernels.qParamFun w ^ (n + 2))
      (Work.Kernels.E4Fun w - (1 + 240 * Work.Kernels.qParamFun w)) := by
    simpa [hq_eq] using hs2
  have hsum_eq : (∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
      • Work.Kernels.qParamFun w ^ (n + 2))
      = Work.Kernels.E4Fun w - (1 + 240 * Work.Kernels.qParamFun w) := hs3.tsum_eq
  have hqnorm : ‖Work.Kernels.qParamFun w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    rw [← hq_eq, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
    congr 1; ring
  have hcoeff : ∀ m : ℕ, 1 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m‖ ≤ 240 * (m : ℝ) ^ 4 := by
    intro m _hm
    have hm0 : m ≠ 0 := by omega
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl,
      Work.Modular.E4_qExpansion_coeff m, if_neg hm0]
    have hσ : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m : ℝ) ^ 4 := by
      have h' : ArithmeticFunction.sigma 3 m ≤ m ^ 4 := by
        simpa using ArithmeticFunction.sigma_le_pow_succ 3 m
      exact_mod_cast h'
    rw [norm_mul]
    have h240 : ‖(240 : ℂ)‖ = (240 : ℝ) := by norm_num
    rw [h240, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  have hbound : ‖Work.Kernels.E4Fun w - (1 + 240 * Work.Kernels.qParamFun w)‖
      ≤ 20000 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
    set r : ℝ := ‖Work.Kernels.qParamFun w‖ with hr_def
    have hr0 : 0 ≤ r := by rw [hr_def]; exact norm_nonneg _
    have hr6 : r ≤ 1 / 6 := by
      rw [hqnorm]
      have h1 : Real.exp (-(2 * Real.pi * w.im)) ≤ Real.exp (-(2 * Real.pi)) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hw]
      linarith [exp_neg_two_pi_le_sixth]
    have hrw : ‖Work.Kernels.qParamFun w‖ = r := hr_def.symm
    have hterm : ∀ n : ℕ,
        ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
          • Work.Kernels.qParamFun w ^ (n + 2)‖
        ≤ 240 * (((n : ℝ) + 2) ^ 4 * r ^ (n + 2)) := by
      intro n
      have hc := hcoeff (n + 2) (by omega)
      calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
            • Work.Kernels.qParamFun w ^ (n + 2)‖
          = ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)‖
            * ‖Work.Kernels.qParamFun w‖ ^ (n + 2) := by rw [smul_eq_mul, norm_mul, norm_pow]
        _ ≤ (240 * (((n + 2 : ℕ)) : ℝ) ^ 4) * ‖Work.Kernels.qParamFun w‖ ^ (n + 2) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = 240 * (((n : ℝ) + 2) ^ 4 * r ^ (n + 2)) := by rw [← hrw]; push_cast; ring
    have hsum_four : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ 4 * r ^ (n + 2)) :=
      summable_pow_four_shift_two r hr0 (by linarith)
    have hmaj : Summable (fun n : ℕ => (240 : ℝ) * (((n : ℝ) + 2) ^ 4 * r ^ (n + 2))) :=
      Summable.mul_left 240 hsum_four
    have hsumn : Summable (fun n : ℕ =>
        ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
          • Work.Kernels.qParamFun w ^ (n + 2)‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
    calc ‖Work.Kernels.E4Fun w - (1 + 240 * Work.Kernels.qParamFun w)‖
        = ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
            • Work.Kernels.qParamFun w ^ (n + 2)‖ := by rw [← hsum_eq]
      _ ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
            • Work.Kernels.qParamFun w ^ (n + 2)‖ := norm_tsum_le_tsum_norm hsumn
      _ ≤ ∑' n : ℕ, (240 : ℝ) * (((n : ℝ) + 2) ^ 4 * r ^ (n + 2)) :=
          Summable.tsum_le_tsum hterm hsumn hmaj
      _ = 240 * ∑' n : ℕ, (((n : ℝ) + 2) ^ 4 * r ^ (n + 2)) := tsum_mul_left
      _ ≤ 240 * (72 * r ^ 2) :=
          mul_le_mul_of_nonneg_left (tsum_pow_four_shift_two_le r hr0 hr6) (by norm_num)
      _ = 17280 * r ^ 2 := by ring
      _ ≤ 20000 * r ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg r)
  calc ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w‖
      = ‖Work.Kernels.E4Fun w - (1 + 240 * Work.Kernels.qParamFun w)‖ := by congr 1; ring
    _ ≤ 20000 * ‖Work.Kernels.qParamFun w‖ ^ 2 := hbound

end

end Work.Asymptotics.EJL
