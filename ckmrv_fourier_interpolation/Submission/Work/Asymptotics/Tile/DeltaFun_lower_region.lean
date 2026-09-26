import Mathlib
import Submission.Work.Kernels.Classical

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold Modular ModularForm

/-! ## Lower bound for `‖Δ‖` in the region `Im τ ≥ 1`

Mathlib knows the eta-product expansion `Δ = q ∏ (1 - q^{n+1})²⁴` with `q = e^{2πiτ}`.
For `Im τ ≥ 1` we have `‖q‖ ≤ 1/4 < 1`, so each factor `(1 - q^{n+1})` is close to `1`
and the whole product is bounded below by `2/3`. Multiplying by `‖q‖ = e^{-2π Im τ}`
gives the claimed exponential lower bound with constant `(2/3)²⁴`.

The proof follows the second conjunct of `Work.Residues.ThetaLowerBound`, with the
private helper lemmas re-derived here so that this module imports nothing beyond
Mathlib and `Submission.Work.Kernels.Classical`. -/

/-- Product estimate `∏ (1 - aᵢ) ≥ 1 - ∑ aᵢ` for `aᵢ ∈ [0,1]`. -/
private lemma one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hi0 : 0 ≤ a i := ha i (Finset.mem_insert_self i s)
      have hs0 : 0 ≤ ∑ j ∈ s, a j :=
        Finset.sum_nonneg fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hih := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      have h1 : (1 - a i) * (1 - ∑ j ∈ s, a j) ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
        mul_le_mul_of_nonneg_left hih (by linarith [ha1 i (Finset.mem_insert_self i s)])
      nlinarith [h1, mul_nonneg hi0 hs0]

/-- Geometric-tail bound `∑_{i<N} r^i ≤ (1-r)⁻¹` for `0 ≤ r < 1`. -/
private lemma geom_sum_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, r ^ i ≤ (1 - r)⁻¹ := by
  have hs : Summable fun i : ℕ => r ^ i := summable_geometric_of_lt_one hr0 hr1
  calc ∑ i ∈ Finset.range N, r ^ i ≤ ∑' i : ℕ, r ^ i :=
        hs.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

/-- `∏ (1 - q^{n+1})` is multipliable for `q = e^{2πiτ}` (the eta product). -/
private lemma multipliable_one_sub_eta_q (τ : UpperHalfPlane) :
    Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ:ℂ)) := by
  have hq_lt : ‖Function.Periodic.qParam 1 (τ:ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact τ.im_pos)
  exact ModularForm.multipliable_one_sub_pow hq_lt

/-- For `Im τ ≥ 1` the eta product `∏ (1 - q^{n+1})` is bounded below by `2/3`. -/
private lemma tprod_one_sub_eta_q_lower (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    (2/3 : ℝ) ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ:ℂ))‖ := by
  set q : ℂ := Function.Periodic.qParam 1 (τ:ℂ) with hqdef
  have hq_lt : ‖q‖ < 1 := by
    rw [hqdef]
    exact Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact τ.im_pos)
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hq_le1 : ‖q‖ ≤ 1 := le_of_lt hq_lt
  have hq_le : ‖q‖ ≤ 1/4 := by
    rw [hqdef, Function.Periodic.norm_qParam]
    have h4 : (4:ℝ) ≤ Real.exp (2 * Real.pi) := by
      have h6 : Real.exp 6 ≤ Real.exp (2 * Real.pi) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      have h7 : (7:ℝ) ≤ Real.exp 6 := by
        have := Real.add_one_le_exp (6:ℝ); linarith
      linarith
    have harg : 2 * Real.pi ≤ 2 * Real.pi * (τ:ℂ).im := by
      rw [UpperHalfPlane.coe_im]; nlinarith [Real.pi_pos, hτ]
    have hge : (4:ℝ) ≤ Real.exp (2 * Real.pi * (τ:ℂ).im) :=
      h4.trans (Real.exp_le_exp.mpr harg)
    have harg2 : -2 * Real.pi * (τ:ℂ).im / 1 = -(2*Real.pi*(τ:ℂ).im) := by ring
    rw [harg2, Real.exp_neg, show (1/4:ℝ) = (4:ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 4)).mpr hge
  have hmul : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ:ℂ)) :=
    multipliable_one_sub_eta_q τ
  have hlim := hmul.tendsto_prod_tprod_nat
  refine ge_of_tendsto hlim.norm ?_
  filter_upwards with N
  have hfac : ∀ n : ℕ, 1 - ‖q‖^(n+1) ≤ ‖(1 - ModularForm.eta_q n (τ:ℂ))‖ := by
    intro n
    have hnorm : ‖ModularForm.eta_q n (τ:ℂ)‖ = ‖q‖^(n+1) := by
      simp [ModularForm.eta_q, hqdef, norm_pow]
    have h := norm_add_le (1 - ModularForm.eta_q n (τ:ℂ)) (ModularForm.eta_q n (τ:ℂ))
    rw [sub_add_cancel, norm_one] at h
    rw [hnorm] at h
    linarith
  have hgeom : ∑ n ∈ Finset.range N, ‖q‖^(n+1) ≤ 1/3 := by
    have heq : ∑ n ∈ Finset.range N, ‖q‖^(n+1) = ‖q‖ * ∑ n ∈ Finset.range N, ‖q‖^n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [pow_succ']
    rw [heq]
    have hg := geom_sum_range_le hr0 hq_lt N
    have h1 : ‖q‖ * (∑ n ∈ Finset.range N, ‖q‖^n) ≤ ‖q‖ * (1 - ‖q‖)⁻¹ :=
      mul_le_mul_of_nonneg_left hg hr0
    refine h1.trans ?_
    have hden : 0 < 1 - ‖q‖ := by linarith
    exact (div_le_iff₀ hden).mpr (by linarith [hq_le])
  have h1 : ∏ n ∈ Finset.range N, (1 - ‖q‖^(n+1))
      ≤ ∏ n ∈ Finset.range N, ‖(1 - ModularForm.eta_q n (τ:ℂ))‖ :=
    Finset.prod_le_prod₀ (fun n hn => by
      have : ‖q‖^(n+1) ≤ ‖q‖^1 := pow_le_pow_of_le_one hr0 hq_le1 (by omega)
      linarith) (fun n hn => hfac n)
  have h2 : 1 - ∑ n ∈ Finset.range N, ‖q‖^(n+1)
      ≤ ∏ n ∈ Finset.range N, (1 - ‖q‖^(n+1)) :=
    one_sub_sum_le_prod _ _ (fun n hn => by positivity) (fun n hn => by
      have : ‖q‖^(n+1) ≤ ‖q‖^1 := pow_le_pow_of_le_one hr0 hq_le1 (by omega)
      linarith)
  rw [norm_prod]
  linarith

/-- Lower bound near the cusp: `‖Δ τ‖ ≥ (2/3)²⁴ · e^{-2π Im τ}` for `Im τ ≥ 1`. -/
theorem DeltaFun_lower_region : ∃ c : ℝ, 0 < c ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
    c * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  refine ⟨(2/3 : ℝ)^24, by positivity, ?_⟩
  intro τ hτ
  have hA := tprod_one_sub_eta_q_lower τ hτ
  have hmul := multipliable_one_sub_eta_q τ
  have hnormq : ‖Function.Periodic.qParam 1 (τ:ℂ)‖ = Real.exp (-(2*Real.pi*τ.im)) := by
    rw [Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
    congr 1
    ring
  calc (2/3 : ℝ)^24 * Real.exp (-(2 * Real.pi * τ.im))
      = Real.exp (-(2 * Real.pi * τ.im)) * (2/3 : ℝ)^24 := by ring
    _ ≤ Real.exp (-(2 * Real.pi * τ.im))
          * ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ:ℂ))‖^24 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hA 24) (Real.exp_nonneg _)
    _ = ‖Work.Kernels.DeltaFun τ‖ := by
        rw [Work.Kernels.DeltaFun, CuspForm.coe_discriminant,
            ModularForm.discriminant_eq_q_prod, norm_mul, hmul.tprod_pow, norm_pow, hnormq]

end Work.Asymptotics.Tile
