/-
# The upper bound `‖j τ - j ζ‖ ≤ C exp (2 π Im τ)` on the disc of radius `29/20`

This is the companion of `Work.Asymptotics.SpikeCircle.divisorLowerDisc`: on the disc of radius
`29/20` around a point `τ` of the funnel, the gradient of the `j`-invariant is bounded by a
constant times `exp (2 π Im τ)`, the size of the leading cusp term `q^{-1}`.

The two ingredients are

* `E4Fun_sub_one_explicit_half` : the explicit cusp bound `‖E₄ w - 1‖ ≤ 20000 ‖q(w)‖` on the
  half-plane `Im w ≥ 1/2`.  The library version `Work.Asymptotics.E4Fun_sub_one_explicit` states
  this for `Im w ≥ 1`; its proof only needs `‖q(w)‖ ≤ 1/4`, which already holds for `Im w ≥ 1/2`,
  so the same argument applies (the numerical lemmas are reproduced below).
* `Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf` : the two-sided bound `Δ ≍ q` on `Im ≥ 1/2`.

Together they give `jInvariantFun_strip_bound`, i.e. `‖j w‖ ≤ C exp (2 π Im w)` for `Im w ≥ 1/2`.
Since `‖ζ - τ‖ ≤ 29/20` forces `Im ζ ≥ 11/20 ≥ 1/2` and
`Im ζ ≤ Im τ + 29/20`, this bound for `ζ` and the funnel bound
`Work.Asymptotics.exists_jInvariantFun_Funnel_bound` for `τ` give the assertion.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
import Submission.Work.Modular.E4_qExpansion_coeff

namespace Work.Asymptotics.SpikeCircle

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold Bundle

noncomputable section

/-! ## The half-plane `Im ≥ 1/2` for `E₄` -/

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

/-- `((n : ℝ) + 1)⁴ ≤ 4·3^{n+1}`. -/
private lemma pow_four_succ_le (n : ℕ) : ((n : ℝ) + 1) ^ 4 ≤ 4 * 3 ^ (n + 1) := by
  have h := pow_four_le_four_mul_three_pow (n + 1)
  have h' : (((n + 1 : ℕ)) : ℝ) ^ 4 ≤ 4 * (3 : ℝ) ^ (n + 1) := by exact_mod_cast h
  simpa using h'

/-- `∑_{n ≥ 0} (n+1)⁴ r^{n+1} ≤ 48 r` for `0 ≤ r ≤ 1/4`. -/
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

/-- **Explicit first-order bound for `E₄` on `Im ≥ 1/2`.**

`‖E₄(w) - 1‖ ≤ 20000 ‖q(w)‖` for `Im w ≥ 1/2`.  This is
`Work.Asymptotics.E4Fun_sub_one_explicit` with the weaker hypothesis `Im w ≥ 1/2`: the proof
only requires `‖q(w)‖ ≤ 1/4`, and `‖q(w)‖ = exp (-2 π Im w) ≤ exp (-π) ≤ 1/4` as soon as
`Im w ≥ 1/2`. -/
theorem E4Fun_sub_one_explicit_half {w : UpperHalfPlane} (hw : (1 / 2 : ℝ) ≤ w.im) :
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
  have hqnorm : ‖Work.Kernels.qParamFun w‖ = Real.exp (-(2 * Real.pi * w.im)) :=
    Work.Asymptotics.norm_qParamFun w
  have hexp_pi : Real.exp (-Real.pi) ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ Real.exp Real.pi := by
      have h5 : (4 : ℝ) ≤ Real.exp 3 := by
        have := Real.add_one_le_exp (3 : ℝ); linarith
      exact le_trans h5 (Real.exp_le_exp.mpr (le_of_lt Real.pi_gt_three))
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h4
  have hr : ‖Work.Kernels.qParamFun w‖ ≤ 1 / 4 := by
    rw [hqnorm]
    have h1 : Real.exp (-(2 * Real.pi * w.im)) ≤ Real.exp (-Real.pi) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hw]
    linarith
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

/-! ## The `j`-invariant on the half-plane `Im ≥ 1/2` -/

/-- `‖j w‖ ≤ C exp (2 π Im w)` for `Im w ≥ 1/2`. -/
theorem jInvariantFun_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ w : UpperHalfPlane, (1 / 2 : ℝ) ≤ w.im →
      ‖Work.Kernels.jInvariantFun w‖ ≤ C * Real.exp (2 * Real.pi * w.im) := by
  obtain ⟨c, _C, hc, _hC, hΔ⟩ := DeltaFunBoundsHalf
  have hE4 : ∀ w : UpperHalfPlane, (1 / 2 : ℝ) ≤ w.im → ‖Work.Kernels.E4Fun w‖ ≤ 5001 := by
    intro w hw
    have h1 : ‖Work.Kernels.E4Fun w - 1‖ ≤ 20000 * ‖Work.Kernels.qParamFun w‖ :=
      E4Fun_sub_one_explicit_half hw
    have hq : ‖Work.Kernels.qParamFun w‖ ≤ 1 / 4 := by
      rw [Work.Asymptotics.norm_qParamFun]
      have h2 : Real.exp (-(2 * Real.pi * w.im)) ≤ Real.exp (-Real.pi) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hw]
      have h4 : (4 : ℝ) ≤ Real.exp Real.pi := by
        have h5 : (4 : ℝ) ≤ Real.exp 3 := by
          have := Real.add_one_le_exp (3 : ℝ); linarith
        exact le_trans h5 (Real.exp_le_exp.mpr (le_of_lt Real.pi_gt_three))
      have h6 : Real.exp (-Real.pi) ≤ 1 / 4 := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) h4
      linarith
    have h3 : ‖Work.Kernels.E4Fun w‖ ≤ ‖Work.Kernels.E4Fun w - 1‖ + 1 := by
      have hh := norm_add_le (Work.Kernels.E4Fun w - 1) (1 : ℂ)
      simpa using hh
    linarith [mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 20000)]
  refine ⟨(5001 : ℝ) ^ 3 / c + 1, by positivity, fun w hw => ?_⟩
  have hΔlo : c * Real.exp (-(2 * Real.pi * w.im)) ≤ ‖Work.Kernels.DeltaFun w‖ := (hΔ w hw).1
  have hE := hE4 w hw
  have hf : ‖Work.Kernels.E4Fun w ^ 3‖ ≤ (5001 : ℝ) ^ 3 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE 3
  have hkey : ‖Work.Kernels.E4Fun w ^ 3 / Work.Kernels.DeltaFun w‖
      ≤ (5001 : ℝ) ^ 3 / (c * Real.exp (-(2 * Real.pi * w.im))) :=
    Work.Asymptotics.norm_div_le_of_lower hf hΔlo hc (Real.exp_pos _)
  have heq : (5001 : ℝ) ^ 3 / (c * Real.exp (-(2 * Real.pi * w.im)))
      = ((5001 : ℝ) ^ 3 / c) * Real.exp (2 * Real.pi * w.im) := by
    rw [Real.exp_neg, div_eq_mul_inv, mul_inv, inv_inv]
    ring
  calc ‖Work.Kernels.jInvariantFun w‖
      = ‖Work.Kernels.E4Fun w ^ 3 / Work.Kernels.DeltaFun w‖ := rfl
    _ ≤ (5001 : ℝ) ^ 3 / (c * Real.exp (-(2 * Real.pi * w.im))) := hkey
    _ = ((5001 : ℝ) ^ 3 / c) * Real.exp (2 * Real.pi * w.im) := heq
    _ ≤ ((5001 : ℝ) ^ 3 / c + 1) * Real.exp (2 * Real.pi * w.im) := by
        have h := Real.exp_pos (2 * Real.pi * w.im)
        have hc0 : (0 : ℝ) ≤ (5001 : ℝ) ^ 3 / c := div_nonneg (by norm_num) hc.le
        nlinarith

/-! ## The main theorem -/

theorem jInvariantFunUpperDisc : ∃ C : ℝ, 0 < C ∧ ∀ τ ζ : UpperHalfPlane, Work.Asymptotics.Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20 → ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨C₁, hC₁, h₁⟩ := Work.Asymptotics.exists_jInvariantFun_Funnel_bound
  obtain ⟨C₂, hC₂, h₂⟩ := jInvariantFun_strip_bound
  refine ⟨C₁ + C₂ * Real.exp (2 * Real.pi * (29 / 20)) + 1, ?_,
    fun τ ζ hτ hζ => ?_⟩
  · have hK := Real.exp_pos (2 * Real.pi * (29 / 20))
    nlinarith [hC₁, hC₂]
  · have hdiff : |ζ.im - τ.im| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := by
      have h1 : ((ζ : ℂ) - (τ : ℂ)).im = ζ.im - τ.im := by
        simp [UpperHalfPlane.coe_im]
      rw [← h1]
      exact Complex.abs_im_le_norm _
    have hζim_lo : (1 / 2 : ℝ) ≤ ζ.im := by
      have h2 : 2 ≤ τ.im := Work.Asymptotics.Funnel.im_two hτ
      rw [abs_le] at hdiff
      linarith [hdiff.1]
    have hζim_hi : ζ.im ≤ τ.im + 29 / 20 := by
      rw [abs_le] at hdiff
      linarith [hdiff.2]
    have hτb : ‖Work.Kernels.jInvariantFun τ‖ ≤ C₁ * Real.exp (2 * Real.pi * τ.im) := h₁ τ hτ
    have hζb : ‖Work.Kernels.jInvariantFun ζ‖ ≤ C₂ * Real.exp (2 * Real.pi * ζ.im) := h₂ ζ hζim_lo
    have hζexp : Real.exp (2 * Real.pi * ζ.im)
        ≤ Real.exp (2 * Real.pi * (29 / 20)) * Real.exp (2 * Real.pi * τ.im) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, hζim_hi]
    have hstep : C₂ * Real.exp (2 * Real.pi * ζ.im)
        ≤ C₂ * (Real.exp (2 * Real.pi * (29 / 20)) * Real.exp (2 * Real.pi * τ.im)) :=
      mul_le_mul_of_nonneg_left hζexp hC₂.le
    calc ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖
        ≤ ‖Work.Kernels.jInvariantFun τ‖ + ‖Work.Kernels.jInvariantFun ζ‖ := norm_sub_le _ _
      _ ≤ C₁ * Real.exp (2 * Real.pi * τ.im)
            + C₂ * Real.exp (2 * Real.pi * ζ.im) := by linarith
      _ ≤ C₁ * Real.exp (2 * Real.pi * τ.im)
            + C₂ * (Real.exp (2 * Real.pi * (29 / 20)) * Real.exp (2 * Real.pi * τ.im)) := by
          linarith
      _ ≤ (C₁ + C₂ * Real.exp (2 * Real.pi * (29 / 20)) + 1)
            * Real.exp (2 * Real.pi * τ.im) := by
          have hK := Real.exp_pos (2 * Real.pi * (29 / 20))
          have hE := Real.exp_pos (2 * Real.pi * τ.im)
          nlinarith [mul_nonneg hC₂.le hK.le]

end

end Work.Asymptotics.SpikeCircle
