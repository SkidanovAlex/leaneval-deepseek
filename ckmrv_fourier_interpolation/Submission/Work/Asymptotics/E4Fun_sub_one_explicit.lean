import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Modular.E4_qExpansion_coeff

namespace Work.Asymptotics

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold Bundle

noncomputable section

/-! ## Elementary estimates

The two ingredients of the explicit `q`-expansion bound are an elementary comparison of the
fourth power with a geometric sequence and the numerical bound `e^{-2π} ≤ 1/4`. -/

/-- `n⁴ ≤ 4·3ⁿ` for every `n : ℕ` (the optimal constant-free comparison used below: `3` is the
smallest integer base for which the induction is uniform, and `4` dominates the finitely many
small values). -/
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

/-- `∑_{n ≥ 0} (n+1)⁴ r^{n+1} ≤ 48 r` for `0 ≤ r ≤ 1/4`: the comparison
`(n+1)⁴ ≤ 4·3^{n+1}` turns the series into `4 ∑ (3r)^{n+1} = 12 r/(1-3r) ≤ 48 r`. -/
private lemma tsum_pow_four_mul_pow_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 4) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ (n + 1) ≤ 48 * r := by
  have h3r0 : 0 ≤ 3 * r := by linarith
  have h3r1 : 3 * r < 1 := by linarith
  have hgeo : Summable (fun n : ℕ => (3 * r) ^ n) := summable_geometric_of_lt_one h3r0 h3r1
  have hgeo1 : Summable (fun n : ℕ => (3 * r) ^ (n + 1)) := by
    have hh := (summable_nat_add_iff (f := fun m : ℕ => (3 * r) ^ m) 1).mpr hgeo
    simpa [add_comm] using hh
  have hgeo4 : Summable (fun n : ℕ => (4 : ℝ) * (3 * r) ^ (n + 1)) :=
    Summable.mul_left 4 hgeo1
  have hterm : ∀ n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ (n + 1) ≤ 4 * (3 * r) ^ (n + 1) := by
    intro n
    have h1 : ((n : ℝ) + 1) ^ 4 ≤ 4 * (3 : ℝ) ^ (n + 1) := pow_four_succ_le n
    have h2 : (0 : ℝ) ≤ r ^ (n + 1) := pow_nonneg hr0 _
    calc ((n : ℝ) + 1) ^ 4 * r ^ (n + 1) ≤ (4 * 3 ^ (n + 1)) * r ^ (n + 1) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = 4 * (3 * r) ^ (n + 1) := by rw [mul_pow]; ring
  have hlhs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 4 * r ^ (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hterm hgeo4
  have htsum : ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ (n + 1) ≤ 4 * (3 * r) * (1 - 3 * r)⁻¹ := by
    calc ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ (n + 1)
        ≤ ∑' n : ℕ, (4 : ℝ) * (3 * r) ^ (n + 1) :=
          Summable.tsum_le_tsum hterm hlhs hgeo4
      _ = 4 * (3 * r * (1 - 3 * r)⁻¹) := by
          rw [tsum_mul_left]
          congr 1
          simp_rw [pow_succ']
          rw [tsum_mul_left, tsum_geometric_of_lt_one h3r0 h3r1]
      _ = 4 * (3 * r) * (1 - 3 * r)⁻¹ := by ring
  have hpos : (0 : ℝ) < 1 - 3 * r := by linarith
  have hquarter : (1 : ℝ) / 4 ≤ 1 - 3 * r := by linarith
  have hinv : (1 - 3 * r)⁻¹ ≤ 4 := by
    have h : (1 - 3 * r)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := (inv_le_inv₀ hpos (by norm_num)).mpr hquarter
    norm_num at h
    exact h
  calc ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ (n + 1) ≤ 4 * (3 * r) * (1 - 3 * r)⁻¹ := htsum
    _ ≤ 4 * (3 * r) * 4 := by
        apply mul_le_mul_of_nonneg_left hinv
        linarith
    _ = 48 * r := by ring

/-- `e^{-2π} ≤ 1/4`. -/
private lemma exp_neg_two_pi_le_quarter : Real.exp (-(2 * Real.pi)) ≤ 1 / 4 := by
  have h1 : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-6) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-6) ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ Real.exp 6 := by
      have h : Real.exp 6 = (Real.exp 1) ^ 6 := by simp
      rw [h]
      have h5 : (2.7182818283 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 6
      have h3 : (4 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
      linarith
    have hprod : Real.exp 6 * Real.exp (-6) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-6), h4, hprod]
  linarith

/-- **Explicit first-order bound for `E₄` at the cusp.**

`‖E₄(w) - 1‖ ≤ 20000 ‖q(w)‖` for `Im w ≥ 1`, with an explicit constant.  This is the
quantitative form of `Work.Residues.E4Fun_decay`, whose existential constant cannot be compared
with the concrete numbers `e^{-4π}` (`Im τ ≥ 2`) and `e^{-6π}` (`t ≥ 3`) needed to make the
funnel tail estimates uniform: the applications only need `20000 · e^{-4π} ≤ 1/2`.

*Proof.*  `UpperHalfPlane.hasSum_qExpansion` applied to `ModularForm.E₄` (periodicity
`SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL`,
holomorphy `ModularForm.holo' ModularForm.E₄`, boundedness
`ModularFormClass.bdd_at_infty ModularForm.E₄`) together with
`Work.Modular.E4_qExpansion_coeff` gives `E₄(w) = Σ'ₙ cₙ qⁿ` with `c₀ = 1` and
`‖cₙ‖ = 240 σ₃(n) ≤ 240 n⁴` (`ArithmeticFunction.sigma_le_pow_succ`).  Hence
`‖E₄(w) - 1‖ ≤ 240 Σ'_{n≥1} n⁴‖q‖ⁿ`.  With `r = ‖q‖ ≤ e^{-2π} ≤ 1/4` the elementary estimate
`n⁴ ≤ 4·3ⁿ` (all `n ≥ 1`) gives
`Σ'_{n≥1} n⁴ rⁿ ≤ 4 Σ'_{n≥1} (3r)ⁿ = 12r/(1-3r) ≤ 48r`, so
`‖E₄(w) - 1‖ ≤ 240·48 r = 11520 r ≤ 20000 r`. -/
theorem E4Fun_sub_one_explicit {w : UpperHalfPlane} (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E4Fun w - 1‖ ≤ 20000 * ‖Work.Kernels.qParamFun w‖ := by
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E4Fun)
    one_pos hper hhol hbdd w
  have hs1 := (hasSum_nat_add_iff' 1).mpr hs
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff]
    norm_num
  have hsum1 : (∑ i ∈ Finset.range 1,
      (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff i
        • Function.Periodic.qParam 1 (w : ℂ) ^ i) = 1 := by
    rw [Finset.sum_range_one, hc0, pow_zero, smul_eq_mul, mul_one]
  rw [hsum1] at hs1
  have hq_eq : Function.Periodic.qParam 1 (w : ℂ) = Work.Kernels.qParamFun w := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  rw [hq_eq] at hs1
  have hqnorm : ‖Work.Kernels.qParamFun w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    rw [← hq_eq, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
    congr 1; ring
  have hr : ‖Work.Kernels.qParamFun w‖ ≤ 1 / 4 := by
    rw [hqnorm]
    have h1 : Real.exp (-(2 * Real.pi * w.im)) ≤ Real.exp (-(2 * Real.pi)) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hw]
    linarith [exp_neg_two_pi_le_quarter]
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
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1)
        • Work.Kernels.qParamFun w ^ (n + 1)‖
      ≤ 240 * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun w‖ ^ (n + 1)) := by
    intro n
    have hc := hcoeff (n + 1) (by omega)
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1)
          • Work.Kernels.qParamFun w ^ (n + 1)‖
        = ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1)‖
          * ‖Work.Kernels.qParamFun w‖ ^ (n + 1) := by
          rw [smul_eq_mul, norm_mul, norm_pow]
      _ ≤ (240 * (((n + 1 : ℕ)) : ℝ) ^ 4) * ‖Work.Kernels.qParamFun w‖ ^ (n + 1) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 240 * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun w‖ ^ (n + 1)) := by
          push_cast; ring
  have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ := norm_nonneg _
  have hr3 : 3 * ‖Work.Kernels.qParamFun w‖ < 1 := by linarith
  have hgeo : Summable (fun n : ℕ => (3 * ‖Work.Kernels.qParamFun w‖) ^ n) :=
    summable_geometric_of_lt_one (by linarith) hr3
  have hgeo1 : Summable (fun n : ℕ => (3 * ‖Work.Kernels.qParamFun w‖) ^ (n + 1)) := by
    have hh := (summable_nat_add_iff
      (f := fun m : ℕ => (3 * ‖Work.Kernels.qParamFun w‖) ^ m) 1).mpr hgeo
    simpa [add_comm] using hh
  have hgeo4 : Summable (fun n : ℕ => (960 : ℝ) * (3 * ‖Work.Kernels.qParamFun w‖) ^ (n + 1)) :=
    Summable.mul_left 960 hgeo1
  have hterm2 : ∀ n : ℕ, (240 : ℝ) * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun w‖ ^ (n + 1))
      ≤ 960 * (3 * ‖Work.Kernels.qParamFun w‖) ^ (n + 1) := by
    intro n
    have h1 := pow_four_succ_le n
    have h2 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ ^ (n + 1) := pow_nonneg hr0 _
    calc (240 : ℝ) * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun w‖ ^ (n + 1))
        ≤ 240 * (4 * 3 ^ (n + 1) * ‖Work.Kernels.qParamFun w‖ ^ (n + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right h1 h2
      _ = 960 * (3 * ‖Work.Kernels.qParamFun w‖) ^ (n + 1) := by rw [mul_pow]; ring
  have hmaj : Summable (fun n : ℕ =>
      (240 : ℝ) * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun w‖ ^ (n + 1))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hterm2 hgeo4
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1)
        • Work.Kernels.qParamFun w ^ (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  calc ‖Work.Kernels.E4Fun w - 1‖
      = ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1)
          • Work.Kernels.qParamFun w ^ (n + 1)‖ := by rw [hs1.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1)
          • Work.Kernels.qParamFun w ^ (n + 1)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (240 : ℝ) * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun w‖ ^ (n + 1)) :=
        Summable.tsum_le_tsum hterm hsumm hmaj
    _ = 240 * ∑' n : ℕ, (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun w‖ ^ (n + 1)) := by
        rw [tsum_mul_left]
    _ ≤ 240 * (48 * ‖Work.Kernels.qParamFun w‖) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact tsum_pow_four_mul_pow_le _ hr0 hr
    _ = 11520 * ‖Work.Kernels.qParamFun w‖ := by ring
    _ ≤ 20000 * ‖Work.Kernels.qParamFun w‖ :=
        mul_le_mul_of_nonneg_right (by norm_num) hr0

end

end Work.Asymptotics
