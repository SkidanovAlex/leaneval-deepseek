import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.CKFinal.LineDecay.qParamFun_norm_le_quarter
import Submission.Work.CKFinal.LineDecay.E4tail_series_bound

/-!
# The two-term cusp expansion of `E₄` with an explicit constant

`E₄(τ) = 1 + 240 q(τ) + O(q(τ)²)` with `q(τ) = e^{2πiτ}`: for `Im τ ≥ 1` the remainder is
bounded by `40000 ‖q‖²`.  The constant comes from the coefficient bound `‖c_m‖ = 240 σ₃(m)
≤ 240 m⁴` for `m ≥ 2` together with the elementary series estimate
`Σ_{n ≥ 0} (n+2)⁴ r^{n+2} ≤ 144 r²` valid for `0 ≤ r ≤ 1/4`:

  `‖E₄ τ - 1 - 240 q‖ ≤ 240 · 144 ‖q‖² = 34560 ‖q‖² ≤ 40000 ‖q‖²`.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold Bundle

noncomputable section

theorem E4_two_term_explicit :
    ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
        ≤ 40000 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
  intro z hz
  set q : ℂ := Work.Kernels.qParamFun z with hqdef
  -- the `q`-expansion of `E₄` and its index shift by two
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E4Fun)
    one_pos hper hhol hbdd z
  have hs2 := (hasSum_nat_add_iff' 2).mpr hs
  have hqeq : Function.Periodic.qParam 1 (z : ℂ) = q := by
    rw [hqdef]
    simp [Work.Kernels.qParamFun, Function.Periodic.qParam]
  rw [hqeq] at hs2
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff]
    norm_num
  have hc1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 1 = 240 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff 1,
      if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have hsum2 : (∑ i ∈ Finset.range 2,
      (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff i • q ^ i) = 1 + 240 * q := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1]
    simp [smul_eq_mul]
  have htsum : (∑' n : ℕ,
      (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2) • q ^ (n + 2))
      = Work.Kernels.E4Fun z - 1 - 240 * q := by
    rw [hs2.tsum_eq, hsum2]; ring
  -- the coefficient bound `‖c_m‖ ≤ 240 m⁴` for `m ≥ 2`
  have hcoeff : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)‖
        ≤ 240 * ((n : ℝ) + 2) ^ 4 := by
    intro n
    have hn0 : n + 2 ≠ 0 := by omega
    have hc : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)
        = (240 : ℂ) * ((ArithmeticFunction.sigma 3 (n + 2) : ℕ) : ℂ) := by
      rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
          = (UpperHalfPlane.qExpansion 1 Work.Modular.E4) from rfl,
        Work.Modular.E4_qExpansion_coeff (n + 2), if_neg hn0]
    have hsig : (ArithmeticFunction.sigma 3 (n + 2) : ℝ) ≤ ((n : ℝ) + 2) ^ 4 := by
      have h' : ArithmeticFunction.sigma 3 (n + 2) ≤ (n + 2) ^ 4 := by
        simpa using ArithmeticFunction.sigma_le_pow_succ 3 (n + 2)
      have h'' : (((n + 2) ^ 4 : ℕ) : ℝ) = ((n : ℝ) + 2) ^ 4 := by push_cast; ring
      rw [← h'']
      exact_mod_cast h'
    rw [hc, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hsig (by norm_num)
  -- the elementary series bound
  have hqle : ‖q‖ ≤ 1 / 4 := by
    rw [show ‖q‖ = ‖Work.Kernels.qParamFun z‖ from by rw [hqdef]]
    exact qParamFun_norm_le_quarter z hz
  obtain ⟨hser_sum, hser_bd⟩ := E4tail_series_bound ‖q‖ (norm_nonneg q) hqle
  -- termwise comparison
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2) • q ^ (n + 2)‖
        ≤ 240 * (((n : ℝ) + 2) ^ 4 * ‖q‖ ^ (n + 2)) := by
    intro n
    rw [smul_eq_mul, norm_mul, norm_pow]
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2)‖ * ‖q‖ ^ (n + 2)
        ≤ (240 * ((n : ℝ) + 2) ^ 4) * ‖q‖ ^ (n + 2) :=
          mul_le_mul_of_nonneg_right (hcoeff n) (by positivity)
      _ = 240 * (((n : ℝ) + 2) ^ 4 * ‖q‖ ^ (n + 2)) := by ring
  have hmaj : Summable (fun n : ℕ => 240 * (((n : ℝ) + 2) ^ 4 * ‖q‖ ^ (n + 2))) :=
    hser_sum.mul_left 240
  have hnormsum : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2) • q ^ (n + 2)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  rw [← htsum]
  calc ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2) • q ^ (n + 2)‖
      ≤ ∑' n : ℕ,
          ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 2) • q ^ (n + 2)‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, 240 * (((n : ℝ) + 2) ^ 4 * ‖q‖ ^ (n + 2)) :=
        Summable.tsum_le_tsum hterm hnormsum hmaj
    _ = 240 * ∑' n : ℕ, (((n : ℝ) + 2) ^ 4 * ‖q‖ ^ (n + 2)) := tsum_mul_left
    _ ≤ 240 * (144 * ‖q‖ ^ 2) := mul_le_mul_of_nonneg_left hser_bd (by norm_num)
    _ = 34560 * ‖q‖ ^ 2 := by ring
    _ ≤ 40000 * ‖q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num : (34560 : ℝ) ≤ 40000) (by positivity)

end

end Work.CKFinal.LineDecay
