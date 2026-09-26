import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.cuspAtomLimits
import Submission.Work.Residues.LogLambdaBound
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Asymptotics.MFix.KAux

namespace Work.Asymptotics.MFix

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

set_option maxHeartbeats 4000000

noncomputable section

/-! ## A lower bound for `Δ` on `Im ≥ 1`

`Δ = q ∏ (1 - q^{n+1})^24` with `‖q‖ = e^{-2π Im}` and the product `≥ 2/3` for `Im ≥ 1`, so
`‖Δ‖ ≥ (2/3)^24 e^{-2π Im}`.  (Repeated here because the module `Work.Residues.ThetaLowerBound`
clashes with the `theta_lower_bound` line imported through `Kernels.All`.) -/

private lemma one_sub_sum_le_prod_c {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
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

private lemma geom_sum_range_le_c {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, r ^ i ≤ (1 - r)⁻¹ := by
  have hs : Summable fun i : ℕ => r ^ i := summable_geometric_of_lt_one hr0 hr1
  calc ∑ i ∈ Finset.range N, r ^ i ≤ ∑' i : ℕ, r ^ i :=
        hs.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

private lemma multipliable_one_sub_eta_q_c (z : UpperHalfPlane) :
    Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (z:ℂ)) := by
  have hq_lt : ‖Function.Periodic.qParam 1 (z:ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact z.im_pos)
  exact ModularForm.multipliable_one_sub_pow hq_lt

private lemma tprod_one_sub_eta_q_lower_c (z : UpperHalfPlane) (hz : 1 ≤ z.im) :
    (2/3 : ℝ) ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (z:ℂ))‖ := by
  set q : ℂ := Function.Periodic.qParam 1 (z:ℂ) with hqdef
  have hq_lt : ‖q‖ < 1 := by
    rw [hqdef]
    exact Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact z.im_pos)
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
    have harg : 2 * Real.pi ≤ 2 * Real.pi * (z:ℂ).im := by
      rw [UpperHalfPlane.coe_im]; nlinarith [Real.pi_pos, hz]
    have hge : (4:ℝ) ≤ Real.exp (2 * Real.pi * (z:ℂ).im) :=
      h4.trans (Real.exp_le_exp.mpr harg)
    have harg2 : -2 * Real.pi * (z:ℂ).im / 1 = -(2*Real.pi*(z:ℂ).im) := by ring
    rw [harg2, Real.exp_neg, show (1/4:ℝ) = (4:ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 4)).mpr hge
  have hmul : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (z:ℂ)) :=
    multipliable_one_sub_eta_q_c z
  have hlim := hmul.tendsto_prod_tprod_nat
  refine ge_of_tendsto hlim.norm ?_
  filter_upwards with N
  have hfac : ∀ n : ℕ, 1 - ‖q‖^(n+1) ≤ ‖(1 - ModularForm.eta_q n (z:ℂ))‖ := by
    intro n
    have hnorm : ‖ModularForm.eta_q n (z:ℂ)‖ = ‖q‖^(n+1) := by
      simp [ModularForm.eta_q, hqdef, norm_pow]
    have h := norm_add_le (1 - ModularForm.eta_q n (z:ℂ)) (ModularForm.eta_q n (z:ℂ))
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
    have hg := geom_sum_range_le_c hr0 hq_lt N
    have h1 : ‖q‖ * (∑ n ∈ Finset.range N, ‖q‖^n) ≤ ‖q‖ * (1 - ‖q‖)⁻¹ :=
      mul_le_mul_of_nonneg_left hg hr0
    refine h1.trans ?_
    have hden : 0 < 1 - ‖q‖ := by linarith
    exact (div_le_iff₀ hden).mpr (by linarith [hq_le])
  have h1 : ∏ n ∈ Finset.range N, (1 - ‖q‖^(n+1))
      ≤ ∏ n ∈ Finset.range N, ‖(1 - ModularForm.eta_q n (z:ℂ))‖ :=
    Finset.prod_le_prod₀ (fun n hn => by
      have : ‖q‖^(n+1) ≤ ‖q‖^1 := pow_le_pow_of_le_one hr0 hq_le1 (by omega)
      linarith) (fun n hn => hfac n)
  have h2 : 1 - ∑ n ∈ Finset.range N, ‖q‖^(n+1)
      ≤ ∏ n ∈ Finset.range N, (1 - ‖q‖^(n+1)) :=
    one_sub_sum_le_prod_c _ _ (fun n hn => by positivity) (fun n hn => by
      have : ‖q‖^(n+1) ≤ ‖q‖^1 := pow_le_pow_of_le_one hr0 hq_le1 (by omega)
      linarith)
  rw [norm_prod]
  linarith

/-- `‖Δ z‖ ≥ (2/3)^24 e^{-2π Im z}` for `Im z ≥ 1`. -/
lemma DeltaFun_lower_cusp : ∃ c : ℝ, 0 < c ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
    c * Real.exp (-(2 * Real.pi * z.im)) ≤ ‖Work.Kernels.DeltaFun z‖ := by
  refine ⟨(2/3 : ℝ)^24, by norm_num, ?_⟩
  intro z hz
  have hA := tprod_one_sub_eta_q_lower_c z hz
  have hmul := multipliable_one_sub_eta_q_c z
  have hnormq : ‖Function.Periodic.qParam 1 (z:ℂ)‖ = Real.exp (-(2*Real.pi*z.im)) := by
    rw [Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
    norm_num
  calc (2/3 : ℝ)^24 * Real.exp (-(2 * Real.pi * z.im))
      = Real.exp (-(2 * Real.pi * z.im)) * (2/3 : ℝ)^24 := by ring
    _ ≤ Real.exp (-(2 * Real.pi * z.im))
          * ‖∏' n : ℕ, (1 - ModularForm.eta_q n (z:ℂ))‖^24 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hA 24) (Real.exp_nonneg _)
    _ = ‖Work.Kernels.DeltaFun z‖ := by
        rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant,
            ModularForm.discriminant_eq_q_prod, norm_mul, hmul.tprod_pow, norm_pow, hnormq]

/-! ## Cusp bounds in the `z`-variable -/

/-- `‖j τ‖ = ‖E₄ τ‖³/‖Δ τ‖`. -/
lemma jInvariantFun_norm_eq (τ : UpperHalfPlane) : ‖Work.Kernels.jInvariantFun τ‖ =
    ‖Work.Kernels.E4Fun τ‖ ^ 3 / ‖ModularForm.discriminant τ‖ := by
  rw [Work.Kernels.jInvariantFun, Work.Kernels.DeltaFun, CuspForm.coe_discriminant, norm_div,
    norm_pow]

/-- `𝓛_S z = O(e^{-π Im z})` for `Im z ≥ 1`. -/
lemma LS_decay_cusp (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖ℓ.L_S z‖ ≤ C * Real.exp (-(Real.pi * z.im)) :=
  (Work.Residues.LogLambdaBound ℓ).2

/-- `U² - W² = V(U + W) = O(e^{-π Im z})` for `Im z ≥ 1`, using `U = W + V`. -/
lemma UW_sq_decay_cusp :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2‖ ≤
        C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨CU, hCU, hU⟩ := Work.Residues.UFun_decay
  obtain ⟨CW, hCW, hW⟩ := Work.Residues.WFun_decay
  obtain ⟨CV, hCV, hV⟩ := Work.Residues.VFun_decay
  refine ⟨CV * (2 + CU + CW) + 1, by positivity, fun z hz => ?_⟩
  have ht1 : Real.exp (-(Real.pi * z.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz]
  have ht0 : (0:ℝ) ≤ Real.exp (-(Real.pi * z.im)) := Real.exp_nonneg _
  have hUz := hU z hz
  have hWz := hW z hz
  have hVz := hV z hz
  have hq := Work.Kernels.TildeFacts.theta_quartic z
  have hfac : Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2
      = Work.Kernels.VFun z * (Work.Kernels.UFun z + Work.Kernels.WFun z) := by
    rw [hq]; ring
  have hU1 : ‖Work.Kernels.UFun z‖ ≤ 1 + CU * Real.exp (-(Real.pi * z.im)) := by
    have h := norm_add_le (Work.Kernels.UFun z - 1) (1:ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hW1 : ‖Work.Kernels.WFun z‖ ≤ 1 + CW * Real.exp (-(Real.pi * z.im)) := by
    have h := norm_add_le (Work.Kernels.WFun z - 1) (1:ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hUW : ‖Work.Kernels.UFun z + Work.Kernels.WFun z‖ ≤ 2 + CU + CW := by
    have h := norm_add_le (Work.Kernels.UFun z) (Work.Kernels.WFun z)
    have h2 : CU * Real.exp (-(Real.pi * z.im)) ≤ CU := by nlinarith [ht1, hCU.le]
    have h3 : CW * Real.exp (-(Real.pi * z.im)) ≤ CW := by nlinarith [ht1, hCW.le]
    linarith
  rw [hfac, norm_mul]
  have hkey : ‖Work.Kernels.VFun z‖ * ‖Work.Kernels.UFun z + Work.Kernels.WFun z‖
      ≤ (CV * (2 + CU + CW)) * Real.exp (-(Real.pi * z.im)) := by
    have h1 : ‖Work.Kernels.VFun z‖ * ‖Work.Kernels.UFun z + Work.Kernels.WFun z‖
        ≤ (CV * Real.exp (-(Real.pi * z.im))) * (2 + CU + CW) :=
      mul_le_mul hVz hUW (norm_nonneg _) (by positivity)
    calc ‖Work.Kernels.VFun z‖ * ‖Work.Kernels.UFun z + Work.Kernels.WFun z‖
        ≤ (CV * Real.exp (-(Real.pi * z.im))) * (2 + CU + CW) := h1
      _ = (CV * (2 + CU + CW)) * Real.exp (-(Real.pi * z.im)) := by ring
  calc ‖Work.Kernels.VFun z‖ * ‖Work.Kernels.UFun z + Work.Kernels.WFun z‖
      ≤ (CV * (2 + CU + CW)) * Real.exp (-(Real.pi * z.im)) := hkey
    _ ≤ (CV * (2 + CU + CW) + 1) * Real.exp (-(Real.pi * z.im)) := by nlinarith [ht0]

/-- `E₄` is bounded on `Im z ≥ 1`. -/
lemma E4_bdd_cusp : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
    ‖Work.Kernels.E4Fun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E4Fun_decay
  refine ⟨1 + C, by linarith, fun z hz => ?_⟩
  have h1 := h z hz
  have ht : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz]
  have h2 : ‖Work.Kernels.E4Fun z - 1‖ ≤ C := by
    nlinarith [h1, hC.le, ht, Real.exp_nonneg (-(2 * Real.pi * z.im))]
  have h3 := norm_add_le (Work.Kernels.E4Fun z - 1) (1:ℂ)
  rw [sub_add_cancel, norm_one] at h3
  linarith

/-- `E₆` is bounded on `Im z ≥ 1`. -/
lemma E6_bdd_cusp : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
    ‖Work.Kernels.E6Fun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E6Fun_decay
  refine ⟨1 + C, by linarith, fun z hz => ?_⟩
  have h1 := h z hz
  have ht : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz]
  have h2 : ‖Work.Kernels.E6Fun z - 1‖ ≤ C := by
    nlinarith [h1, hC.le, ht, Real.exp_nonneg (-(2 * Real.pi * z.im))]
  have h3 := norm_add_le (Work.Kernels.E6Fun z - 1) (1:ℂ)
  rw [sub_add_cancel, norm_one] at h3
  linarith

/-- Dividing a function bounded on `Im ≥ 1` by `Δ`: the result grows at most like `e^{2π Im z}`. -/
lemma div_Delta_grow {f : UpperHalfPlane → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ z : UpperHalfPlane, 1 ≤ z.im → ‖f z‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖f z / Work.Kernels.DeltaFun z‖ ≤ C * Real.exp (2 * Real.pi * z.im) := by
  obtain ⟨c, hc, hlow⟩ := DeltaFun_lower_cusp
  refine ⟨B / c + 1, by positivity, fun z hz => ?_⟩
  have hzlow := hlow z hz
  have he : 0 < Real.exp (-(2 * Real.pi * z.im)) := Real.exp_pos _
  have hce : 0 < c * Real.exp (-(2 * Real.pi * z.im)) := mul_pos hc he
  have hDpos : 0 < ‖Work.Kernels.DeltaFun z‖ := lt_of_lt_of_le hce hzlow
  rw [norm_div]
  have h1 : ‖f z‖ / ‖Work.Kernels.DeltaFun z‖ ≤ B / (c * Real.exp (-(2 * Real.pi * z.im))) :=
    div_le_div₀ hB (hf z hz) hce hzlow
  refine le_trans h1 ?_
  rw [Real.exp_neg, ← div_eq_mul_inv, div_div_eq_mul_div,
    show B * Real.exp (2 * Real.pi * z.im) / c
        = (B / c) * Real.exp (2 * Real.pi * z.im) by ring]
  nlinarith [Real.exp_nonneg (2 * Real.pi * z.im), hB, hc]

/-- `E₁₄/Δ = O(e^{2π Im z})` for `Im z ≥ 1`. -/
lemma E14_div_Delta_grow :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z‖ ≤
        C * (Real.exp (Real.pi * z.im)) ^ 2 := by
  obtain ⟨B4, hB4, h4⟩ := E4_bdd_cusp
  obtain ⟨B6, hB6, h6⟩ := E6_bdd_cusp
  have hE14 : ∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E14Fun z‖ ≤ B4 ^ 2 * B6 := by
    intro z hz
    have h1 := h4 z hz
    have h2 := h6 z hz
    have heq : Work.Kernels.E14Fun z = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z := rfl
    rw [heq, norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2 (norm_nonneg _) (by positivity)
  obtain ⟨C, hC, h⟩ := div_Delta_grow (f := Work.Kernels.E14Fun) (B := B4 ^ 2 * B6)
    (by positivity) hE14
  refine ⟨C, hC, fun z hz => ?_⟩
  have hh := h z hz
  rwa [show Real.exp (2 * Real.pi * z.im) = (Real.exp (Real.pi * z.im)) ^ 2 by
        rw [sq, ← Real.exp_add]; ring_nf] at hh

/-- `E₁₀/Δ = O(e^{2π Im z})` for `Im z ≥ 1`. -/
lemma E10_div_Delta_grow :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z‖ ≤
        C * (Real.exp (Real.pi * z.im)) ^ 2 := by
  obtain ⟨B4, hB4, h4⟩ := E4_bdd_cusp
  obtain ⟨B6, hB6, h6⟩ := E6_bdd_cusp
  have hE10 : ∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E10Fun z‖ ≤ B4 * B6 := by
    intro z hz
    have h1 := h4 z hz
    have h2 := h6 z hz
    have heq : Work.Kernels.E10Fun z = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z := rfl
    rw [heq, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) hB4.le
  obtain ⟨C, hC, h⟩ := div_Delta_grow (f := Work.Kernels.E10Fun) (B := B4 * B6)
    (by positivity) hE10
  refine ⟨C, hC, fun z hz => ?_⟩
  have hh := h z hz
  rwa [show Real.exp (2 * Real.pi * z.im) = (Real.exp (Real.pi * z.im)) ^ 2 by
        rw [sq, ← Real.exp_add]; ring_nf] at hh

/-- `j = O(e^{2π Im z})` for `Im z ≥ 1`. -/
lemma jInvariantFun_grow :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.jInvariantFun z‖ ≤ C * (Real.exp (Real.pi * z.im)) ^ 2 := by
  obtain ⟨B4, hB4, h4⟩ := E4_bdd_cusp
  have hE43 : ∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E4Fun z ^ 3‖ ≤ B4 ^ 3 := by
    intro z hz
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h4 z hz) 3
  obtain ⟨C, hC, h⟩ := div_Delta_grow (f := fun z => Work.Kernels.E4Fun z ^ 3)
    (B := B4 ^ 3) (by positivity) hE43
  refine ⟨C, hC, fun z hz => ?_⟩
  have hh := h z hz
  have heq : Work.Kernels.jInvariantFun z = Work.Kernels.E4Fun z ^ 3 / Work.Kernels.DeltaFun z :=
    rfl
  rw [heq]
  rwa [show Real.exp (2 * Real.pi * z.im) = (Real.exp (Real.pi * z.im)) ^ 2 by
        rw [sq, ← Real.exp_add]; ring_nf] at hh

/-! ## Bounds on the `τ`-factors on a closed ball -/

/-- `ψ_i` is bounded on a closed hyperbolic ball. -/
lemma psiVec_ball_bound (ℓ : Work.Kernels.LogLambdaData) {τ₀ : UpperHalfPlane} {R : ℝ} :
    ∃ B : ℝ, 0 < B ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ∀ i : Fin 3,
      ‖Work.Kernels.psiVec ℓ τ i‖ ≤ B := by
  obtain ⟨B2, hB2, h2⟩ := bound_on_ball (τ₀ := τ₀) (R := R) (continuous_psi2 ℓ)
  obtain ⟨B4, hB4, h4⟩ := bound_on_ball (τ₀ := τ₀) (R := R) (continuous_psi4 ℓ)
  refine ⟨max 1 (max B2 B4), lt_of_lt_of_le one_pos (le_max_left _ _), fun τ hτ i => ?_⟩
  fin_cases i
  · simp only [Work.Kernels.psiVec]
    exact le_trans (le_of_eq (norm_one)) (le_max_left _ _)
  · simp only [Work.Kernels.psiVec]
    exact le_trans (h2 τ hτ) (le_trans (le_max_left B2 B4) (le_max_right 1 (max B2 B4)))
  · simp only [Work.Kernels.psiVec]
    exact le_trans (h4 τ hτ) (le_trans (le_max_right B2 B4) (le_max_right 1 (max B2 B4)))

/-- `f_k(v_i^{(8)})` is bounded on a closed hyperbolic ball. -/
lemma fk_ball_bound_8 {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ∀ i : Fin 3,
      ‖Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ‖ ≤ B := by
  obtain ⟨B4, hB4, h4⟩ := bound_on_ball (τ₀ := τ₀) (R := R)
    (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous)
  obtain ⟨B6, hB6, h6⟩ := bound_on_ball (τ₀ := τ₀) (R := R)
    (Work.Kernels.ClassicalFacts.E6Fun_mem_InP.1.continuous)
  obtain ⟨δ, Aj, hδ, hAj, hΔl, hAjb⟩ := exists_delta_Aj (τ₀ := τ₀) (R := R) hR
  refine ⟨B4 + B4^2 * B6 / δ + 1, by positivity, fun τ hτ i => ?_⟩
  have h2 : 0 ≤ B4^2 * B6 / δ := by positivity
  have hBnd : B4 ≤ B4 + B4^2 * B6 / δ + 1 := by linarith
  have hBnd2 : B4^2 * B6 / δ ≤ B4 + B4^2 * B6 / δ + 1 := by linarith
  have hBnd3 : (1:ℝ) ≤ B4 + B4^2 * B6 / δ + 1 := by linarith
  have hkey : ∀ j : Fin 3, ‖Work.Kernels.fk (Work.Asymptotics.vlen 8 j) τ‖ ≤
      B4 + B4^2 * B6 / δ + 1 := by
    intro j
    fin_cases j <;> simp only [Fin.reduceFinMk]
    · have hv : Work.Kernels.fk (Work.Asymptotics.vlen 8 0) τ = Work.Kernels.E4Fun τ := by
        simp [Work.Asymptotics.vlen, Work.Kernels.fk]
      rw [hv]; exact le_trans (h4 τ hτ) hBnd
    · have hv : Work.Kernels.fk (Work.Asymptotics.vlen 8 1) τ =
          Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ := by
        simp [Work.Asymptotics.vlen, Work.Kernels.fk]
      rw [hv, norm_div]
      have hΔ := hΔl τ hτ
      have hdpos : 0 < ‖Work.Kernels.DeltaFun τ‖ := lt_of_lt_of_le hδ hΔ
      have hE4 := h4 τ hτ
      have hE6 := h6 τ hτ
      have hnum : ‖Work.Kernels.E14Fun τ‖ ≤ B4^2 * B6 := by
        have heq : Work.Kernels.E14Fun τ = Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ := rfl
        rw [heq, norm_mul, norm_pow]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE4 2) hE6 (norm_nonneg _) (by positivity)
      exact le_trans (div_le_div₀ (by positivity) hnum hδ hΔ) hBnd2
    · have hv : Work.Kernels.fk (Work.Asymptotics.vlen 8 2) τ = 1 := by
        simp [Work.Asymptotics.vlen, Work.Kernels.fk]
      rw [hv, norm_one]; exact hBnd3
  exact hkey i

/-- `f_k(v_i^{(24)})` is bounded on a closed hyperbolic ball. -/
lemma fk_ball_bound_24 {τ₀ : UpperHalfPlane} {R : ℝ} :
    ∃ B : ℝ, 0 < B ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ∀ i : Fin 3,
      ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖ ≤ B := by
  obtain ⟨B4, hB4, h4⟩ := bound_on_ball (τ₀ := τ₀) (R := R)
    (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous)
  obtain ⟨B6, hB6, h6⟩ := bound_on_ball (τ₀ := τ₀) (R := R)
    (Work.Kernels.ClassicalFacts.E6Fun_mem_InP.1.continuous)
  obtain ⟨BΔ, hBΔ, hΔb⟩ := bound_on_ball (τ₀ := τ₀) (R := R)
    (Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous)
  refine ⟨B4 * B6 + B4^2 + BΔ + 1, by positivity, fun τ hτ i => ?_⟩
  have hbnd1 : BΔ ≤ B4 * B6 + B4^2 + BΔ + 1 := by
    have : 0 ≤ B4 * B6 + B4^2 := by positivity
    linarith
  have hbnd2 : B4 * B6 ≤ B4 * B6 + B4^2 + BΔ + 1 := by
    have : 0 ≤ B4^2 + BΔ := by positivity
    linarith
  have hbnd3 : B4^2 ≤ B4 * B6 + B4^2 + BΔ + 1 := by
    have : 0 ≤ B4 * B6 + BΔ := by positivity
    linarith
  have hkey : ∀ j : Fin 3, ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 j) τ‖ ≤
      B4 * B6 + B4^2 + BΔ + 1 := by
    intro j
    fin_cases j <;> simp only [Fin.reduceFinMk]
    · have hv : Work.Kernels.fk (Work.Asymptotics.vlen 24 0) τ = Work.Kernels.DeltaFun τ := by
        simp [Work.Asymptotics.vlen, Work.Kernels.fk]
      rw [hv]; exact le_trans (hΔb τ hτ) hbnd1
    · have hv : Work.Kernels.fk (Work.Asymptotics.vlen 24 1) τ = Work.Kernels.E10Fun τ := by
        simp [Work.Asymptotics.vlen, Work.Kernels.fk]
      rw [hv]
      have heq : Work.Kernels.E10Fun τ = Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ := rfl
      rw [heq, norm_mul]
      exact le_trans (mul_le_mul (h4 τ hτ) (h6 τ hτ) (norm_nonneg _) hB4) hbnd2
    · have hv : Work.Kernels.fk (Work.Asymptotics.vlen 24 2) τ = Work.Kernels.E8Fun τ := by
        simp [Work.Asymptotics.vlen, Work.Kernels.fk]
      rw [hv]
      have heq : Work.Kernels.E8Fun τ = Work.Kernels.E4Fun τ ^ 2 := rfl
      rw [heq, norm_pow]
      exact le_trans (pow_le_pow_left₀ (norm_nonneg _) (h4 τ hτ) 2) hbnd3
  exact hkey i

/-- **A uniform cusp bound for the cleared numerator `Ncusp`.**  For `τ` in a closed hyperbolic
ball and `Im z ≥ 1` the numerator grows at most like `e^{π Im z}`, with a constant depending
only on the ball. -/
theorem KMinusCuspBallBound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → 1 ≤ z.im →
      ‖Work.Asymptotics.Ncusp ℓ d τ z‖ ≤ C * Real.exp (Real.pi * z.im) := by
  rcases hd with rfl | rfl
  · -- ## `d = 8`
    obtain ⟨Bψ, hBψpos, hBψ⟩ := psiVec_ball_bound ℓ (τ₀ := τ₀) (R := R)
    obtain ⟨Bf, hBfpos, hBf⟩ := fk_ball_bound_8 (τ₀ := τ₀) (R := R) hR
    obtain ⟨δ, Aj, hδpos, hAjnn, hδle, hAjle⟩ := exists_delta_Aj (τ₀ := τ₀) (R := R) hR
    obtain ⟨CLS, hCLSpos, hLSb⟩ := LS_decay_cusp ℓ
    obtain ⟨CV, hCVpos, hVb⟩ := Work.Residues.VFun_decay
    obtain ⟨CUW, hCUWpos, hUWb⟩ := UW_sq_decay_cusp
    obtain ⟨C4z, hC4zpos, h4z⟩ := E4_bdd_cusp
    obtain ⟨C6z, hC6zpos, h6z⟩ := E6_bdd_cusp
    set Bv : ℝ := Bψ * Bf with hBvdef
    set Bm : ℝ := 3456 + (1728 + Aj + 1) + (Aj + 1) with hBmdef
    set K0 : ℝ := 3 * Bv * Bm * (C4z * C6z) * CLS with hK0def
    set K1 : ℝ := 3 * Bv * Bm * (C4z ^ 2) * CV with hK1def
    set K2 : ℝ := 3 * Bv * Bm * C6z * CUW with hK2def
    have hBvpos : 0 < Bv := by rw [hBvdef]; positivity
    have hK0nn : 0 ≤ K0 := by rw [hK0def]; positivity
    have hK1nn : 0 ≤ K1 := by rw [hK1def]; positivity
    have hK2nn : 0 ≤ K2 := by rw [hK2def]; positivity
    refine ⟨‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (K0 + K1 + K2) + 1, ?_, ?_⟩
    · have h1 : 0 ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
      nlinarith [h1, hK0nn, hK1nn, hK2nn]
    · intro τ z hτ hz
      set t : ℝ := Real.exp (-(Real.pi * z.im)) with ht
      set P : ℝ := Real.exp (Real.pi * z.im) with hP
      have htP : t * P = 1 := by
        rw [ht, hP, ← Real.exp_add,
          show -(Real.pi * z.im) + Real.pi * z.im = 0 by ring, Real.exp_zero]
      have ht1 : t ≤ 1 := by rw [ht, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz]
      have hP1 : 1 ≤ P := by rw [hP, Real.one_le_exp_iff]; nlinarith [Real.pi_pos, hz]
      have htleP : t ≤ P := le_trans ht1 hP1
      have hPnn : 0 ≤ P := le_trans zero_le_one hP1
      have hpsi_fk : ∀ i : Fin 3,
          ‖Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ‖ ≤ Bv := by
        intro i
        rw [norm_mul, hBvdef]
        exact mul_le_mul (hBψ τ hτ i) (hBf τ hτ i) (norm_nonneg _) hBψpos.le
      have hjnn : 0 ≤ ‖Work.Kernels.jInvariantFun τ‖ := norm_nonneg _
      have hsub : ‖(1728:ℂ) - Work.Kernels.jInvariantFun τ‖ ≤ 1728 + Aj := by
        have h := norm_sub_le (1728:ℂ) (Work.Kernels.jInvariantFun τ)
        rw [show ‖(1728:ℂ)‖ = 1728 by norm_num] at h
        linarith [h, hAjle τ hτ]
      have hj2 : ‖Work.Kernels.E4Fun τ‖ ^ 3 / ‖ModularForm.discriminant τ‖ ≤ Aj := by
        simpa [Work.Kernels.jInvariantFun, Work.Kernels.DeltaFun, CuspForm.coe_discriminant,
          norm_div, norm_pow] using hAjle τ hτ
      have hMc : ∀ i m : Fin 3, ‖Work.Asymptotics.Mcusp 8 τ z i m‖ ≤ Bm := by
        intro i m
        rw [hBmdef]
        fin_cases i <;> fin_cases m <;>
          norm_num [Work.Asymptotics.Mcusp, Work.Kernels.c1728, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val] <;>
          linarith [hAjle τ hτ, hj2, hAjnn, hjnn, hsub]
      have hF0 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z‖ ≤ C4z * C6z := by
        have hv : Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z = Work.Kernels.E10Fun z := by
          simp [Work.Asymptotics.ulen, Work.Kernels.fk]
        rw [hv]
        show ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z‖ ≤ C4z * C6z
        rw [norm_mul]
        exact mul_le_mul (h4z z hz) (h6z z hz) (norm_nonneg _) hC4zpos.le
      have hF1 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z‖ ≤ C4z ^ 2 := by
        have hv : Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z = Work.Kernels.E8Fun z := by
          simp [Work.Asymptotics.ulen, Work.Kernels.fk]
        rw [hv]
        show ‖Work.Kernels.E4Fun z ^ 2‖ ≤ C4z ^ 2
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (h4z z hz) 2
      have hF2 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z‖ ≤ C6z := by
        have hv : Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z = Work.Kernels.E6Fun z := by
          simp [Work.Asymptotics.ulen, Work.Kernels.fk]
        rw [hv]; exact h6z z hz
      have hP0 : ‖Work.Asymptotics.Pcusp ℓ 0 z‖ ≤ CLS * t := by
        rw [Work.Asymptotics.Pcusp_zero, ht]; exact hLSb z hz
      have hP1 : ‖Work.Asymptotics.Pcusp ℓ 1 z‖ ≤ CV * t := by
        rw [Work.Asymptotics.Pcusp_one, ht, norm_neg]; exact hVb z hz
      have hP2 : ‖Work.Asymptotics.Pcusp ℓ 2 z‖ ≤ CUW * t := by
        rw [Work.Asymptotics.Pcusp_two, ht]; exact hUWb z hz
      set g : Fin 3 → ℂ := fun m => (∑ i : Fin 3,
            Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i m * Work.Kernels.fk (Work.Asymptotics.ulen 8 m) z) *
            Work.Asymptotics.Pcusp ℓ m z with hg
      have hm0 : ‖g 0‖ ≤ K0 * P := by
        rw [hg]; simp only []; rw [norm_mul]
        have hper : ∀ i : Fin 3,
            ‖Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i 0 * Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z‖
            ≤ Bv * Bm * (C4z * C6z) := by
          intro i
          rw [norm_mul, norm_mul, norm_mul, hBvdef]
          exact mul_le_mul (mul_le_mul (mul_le_mul (hBψ τ hτ i) (hBf τ hτ i) (norm_nonneg _)
            hBψpos.le) (hMc i 0) (norm_nonneg _) (by positivity)) hF0 (norm_nonneg _)
            (by positivity)
        have hinner : ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i 0 * Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z‖
            ≤ 3 * (Bv * Bm * (C4z * C6z)) := by
          calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
                Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
                Work.Asymptotics.Mcusp 8 τ z i 0 * Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z‖
              ≤ ∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i *
                Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
                Work.Asymptotics.Mcusp 8 τ z i 0 * Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _i : Fin 3, (Bv * Bm * (C4z * C6z)) := Finset.sum_le_sum (fun i _ => hper i)
            _ = 3 * (Bv * Bm * (C4z * C6z)) := by rw [Fin.sum_univ_three]; ring
        calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i 0 * Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z‖ *
              ‖Work.Asymptotics.Pcusp ℓ 0 z‖
            ≤ (3 * (Bv * Bm * (C4z * C6z))) * (CLS * t) :=
              mul_le_mul hinner hP0 (norm_nonneg _) (by positivity)
          _ = K0 * t := by rw [hK0def]; ring
          _ ≤ K0 * P := mul_le_mul_of_nonneg_left htleP hK0nn
      have hm1 : ‖g 1‖ ≤ K1 * P := by
        rw [hg]; simp only []; rw [norm_mul]
        have hper : ∀ i : Fin 3,
            ‖Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i 1 * Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z‖
            ≤ Bv * Bm * (C4z ^ 2) := by
          intro i
          rw [norm_mul, norm_mul, norm_mul, hBvdef]
          exact mul_le_mul (mul_le_mul (mul_le_mul (hBψ τ hτ i) (hBf τ hτ i) (norm_nonneg _)
            hBψpos.le) (hMc i 1) (norm_nonneg _) (by positivity)) hF1 (norm_nonneg _)
            (by positivity)
        have hinner : ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i 1 * Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z‖
            ≤ 3 * (Bv * Bm * (C4z ^ 2)) := by
          calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
                Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
                Work.Asymptotics.Mcusp 8 τ z i 1 * Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z‖
              ≤ ∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i *
                Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
                Work.Asymptotics.Mcusp 8 τ z i 1 * Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _i : Fin 3, (Bv * Bm * (C4z ^ 2)) := Finset.sum_le_sum (fun i _ => hper i)
            _ = 3 * (Bv * Bm * (C4z ^ 2)) := by rw [Fin.sum_univ_three]; ring
        calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i 1 * Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z‖ *
              ‖Work.Asymptotics.Pcusp ℓ 1 z‖
            ≤ (3 * (Bv * Bm * (C4z ^ 2))) * (CV * t) :=
              mul_le_mul hinner hP1 (norm_nonneg _) (by positivity)
          _ = K1 * t := by rw [hK1def]; ring
          _ ≤ K1 * P := mul_le_mul_of_nonneg_left htleP hK1nn
      have hm2 : ‖g 2‖ ≤ K2 * P := by
        rw [hg]; simp only []; rw [norm_mul]
        have hper : ∀ i : Fin 3,
            ‖Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i 2 * Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z‖
            ≤ Bv * Bm * C6z := by
          intro i
          rw [norm_mul, norm_mul, norm_mul, hBvdef]
          exact mul_le_mul (mul_le_mul (mul_le_mul (hBψ τ hτ i) (hBf τ hτ i) (norm_nonneg _)
            hBψpos.le) (hMc i 2) (norm_nonneg _) (by positivity)) hF2 (norm_nonneg _)
            (by positivity)
        have hinner : ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i 2 * Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z‖
            ≤ 3 * (Bv * Bm * C6z) := by
          calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
                Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
                Work.Asymptotics.Mcusp 8 τ z i 2 * Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z‖
              ≤ ∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i *
                Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
                Work.Asymptotics.Mcusp 8 τ z i 2 * Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _i : Fin 3, (Bv * Bm * C6z) := Finset.sum_le_sum (fun i _ => hper i)
            _ = 3 * (Bv * Bm * C6z) := by rw [Fin.sum_univ_three]; ring
        calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 8 i) τ *
              Work.Asymptotics.Mcusp 8 τ z i 2 * Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z‖ *
              ‖Work.Asymptotics.Pcusp ℓ 2 z‖
            ≤ (3 * (Bv * Bm * C6z)) * (CUW * t) :=
              mul_le_mul hinner hP2 (norm_nonneg _) (by positivity)
          _ = K2 * t := by rw [hK2def]; ring
          _ ≤ K2 * P := mul_le_mul_of_nonneg_left htleP hK2nn
      have hfin : ‖∑ m : Fin 3, g m‖ ≤ (K0 + K1 + K2) * P := by
        rw [Fin.sum_univ_three]
        have hA := norm_add_le (g 0 + g 1) (g 2)
        have hB := norm_add_le (g 0) (g 1)
        calc ‖g 0 + g 1 + g 2‖ ≤ ‖g 0‖ + ‖g 1‖ + ‖g 2‖ := by linarith
          _ ≤ K0 * P + K1 * P + K2 * P := by linarith
          _ = (K0 + K1 + K2) * P := by ring
      have hNc : Work.Asymptotics.Ncusp ℓ 8 τ z =
          ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * ∑ m : Fin 3, g m := by
        unfold Work.Asymptotics.Ncusp
        rw [← hg]
      calc ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
          = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖∑ m : Fin 3, g m‖ := by
            rw [hNc, norm_mul]
        _ ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ((K0 + K1 + K2) * P) :=
            mul_le_mul_of_nonneg_left hfin (norm_nonneg _)
        _ = (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (K0 + K1 + K2)) * P := by ring
        _ ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (K0 + K1 + K2) + 1) * P := by
            nlinarith [hPnn, norm_nonneg ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹]
  · -- ## `d = 24`
    obtain ⟨Bψ, hBψpos, hBψ⟩ := psiVec_ball_bound ℓ (τ₀ := τ₀) (R := R)
    obtain ⟨Bf, hBfpos, hBf⟩ := fk_ball_bound_24 (τ₀ := τ₀) (R := R)
    obtain ⟨δ, Aj, hδpos, hAjnn, hδle, hAjle⟩ := exists_delta_Aj (τ₀ := τ₀) (R := R) hR
    obtain ⟨Cz, hCzpos, hCj⟩ := jInvariantFun_grow
    obtain ⟨CLS, hCLSpos, hLSb⟩ := LS_decay_cusp ℓ
    obtain ⟨CV, hCVpos, hVb⟩ := Work.Residues.VFun_decay
    obtain ⟨CUW, hCUWpos, hUWb⟩ := UW_sq_decay_cusp
    obtain ⟨C14D, hC14Dpos, h14⟩ := E14_div_Delta_grow
    obtain ⟨C10D, hC10Dpos, h10⟩ := E10_div_Delta_grow
    set Bv : ℝ := Bψ * Bf with hBvdef
    set D1 : ℝ := 3456 * (Aj + Cz) + (3 * Aj + 2 * Cz) + (1728 + 3 * Aj + 2 * Cz) with hD1def
    set Am0 : ℝ := 3456 * C14D with hAm0def
    set Am2 : ℝ := C10D with hAm2def
    set K0 : ℝ := 3 * Bv * Am0 * CLS with hK0def
    set K1 : ℝ := 3 * Bv * D1 * CV with hK1def
    set K2 : ℝ := 3 * Bv * Am2 * CUW with hK2def
    have hBvpos : 0 < Bv := by rw [hBvdef]; positivity
    have hK0nn : 0 ≤ K0 := by rw [hK0def]; positivity
    have hK1nn : 0 ≤ K1 := by rw [hK1def]; positivity
    have hK2nn : 0 ≤ K2 := by rw [hK2def]; positivity
    refine ⟨‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (K0 + K1 + K2) + 1, ?_, ?_⟩
    · have h1 : 0 ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
      nlinarith [h1, hK0nn, hK1nn, hK2nn]
    · intro τ z hτ hz
      set t : ℝ := Real.exp (-(Real.pi * z.im)) with ht
      set P : ℝ := Real.exp (Real.pi * z.im) with hP
      have htP : t * P = 1 := by
        rw [ht, hP, ← Real.exp_add,
          show -(Real.pi * z.im) + Real.pi * z.im = 0 by ring, Real.exp_zero]
      have ht1 : t ≤ 1 := by rw [ht, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz]
      have hP1 : 1 ≤ P := by rw [hP, Real.one_le_exp_iff]; nlinarith [Real.pi_pos, hz]
      have hP2 : 1 ≤ P ^ 2 := by nlinarith [hP1]
      have hP0nn : 0 ≤ P := le_trans zero_le_one hP1
      have hCznn : 0 ≤ Cz := hCzpos.le
      have hpsi_fk : ∀ i : Fin 3,
          ‖Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖ ≤ Bv := by
        intro i
        rw [norm_mul, hBvdef]
        exact mul_le_mul (hBψ τ hτ i) (hBf τ hτ i) (norm_nonneg _) hBψpos.le
      have hj2 : ‖Work.Kernels.E4Fun τ‖ ^ 3 / ‖ModularForm.discriminant τ‖ ≤ Aj := by
        simpa [Work.Kernels.jInvariantFun, Work.Kernels.DeltaFun, CuspForm.coe_discriminant,
          norm_div, norm_pow] using hAjle τ hτ
      have hjz2 : ‖Work.Kernels.E4Fun z‖ ^ 3 / ‖ModularForm.discriminant z‖ ≤ Cz * P ^ 2 := by
        rw [hP]
        simpa [Work.Kernels.jInvariantFun, Work.Kernels.DeltaFun, CuspForm.coe_discriminant,
          norm_div, norm_pow] using hCj z hz
      have hdiffJ : ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ ≤ Aj + Cz * P ^ 2 := by
        have h := norm_sub_le (Work.Kernels.jInvariantFun τ) (Work.Kernels.jInvariantFun z)
        rw [jInvariantFun_norm_eq τ, jInvariantFun_norm_eq z] at h
        linarith only [h, hj2, hjz2]
      have hAy : ‖Work.Kernels.jInvariantFun τ‖ ≤ Aj := hAjle τ hτ
      have hMc240 : ∀ i : Fin 3, ‖Work.Asymptotics.Mcusp 24 τ z i 0‖ ≤ 3456 := by
        intro i
        fin_cases i <;>
          norm_num [Work.Asymptotics.Mcusp, Work.Kernels.c1728, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
      have hMc241' : ∀ i : Fin 3, ‖Work.Asymptotics.Mcusp 24 τ z i 1‖ ≤
          (3456 * (Aj + Cz) + (3 * Aj + 2 * Cz) + (1728 + 3 * Aj + 2 * Cz)) * P ^ 2 := by
        intro i
        fin_cases i <;>
          norm_num [Work.Asymptotics.Mcusp, Work.Kernels.c1728, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
        · calc 3456 * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖
              ≤ 3456 * (Aj + Cz * P^2) := mul_le_mul_of_nonneg_left hdiffJ (by norm_num)
            _ ≤ (3456 * (Aj + Cz) + (3 * Aj + 2 * Cz) + (1728 + 3 * Aj + 2 * Cz)) * P ^ 2 := by
                nlinarith [hP2, hAjnn, hCznn, hP0nn]
        · have h2 : ‖(2:ℂ) * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
              = 2 * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
            rw [norm_mul]; norm_num
          calc ‖Work.Kernels.jInvariantFun τ + 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
              ≤ ‖Work.Kernels.jInvariantFun τ‖
                + ‖(2:ℂ) * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := norm_add_le _ _
            _ = ‖Work.Kernels.jInvariantFun τ‖ + 2 * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
                rw [h2]
            _ ≤ Aj + 2 * (Aj + Cz * P^2) := by linarith [hAy, hdiffJ]
            _ ≤ (3456 * (Aj + Cz) + (3 * Aj + 2 * Cz) + (1728 + 3 * Aj + 2 * Cz)) * P ^ 2 := by
                nlinarith [hP2, hAjnn, hCznn, hP0nn]
        · have h2 : ‖(2:ℂ) * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
              = 2 * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
            rw [norm_mul]; norm_num
          calc ‖(1728:ℂ) - 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) - Work.Kernels.jInvariantFun τ‖
              ≤ ‖(1728:ℂ) - 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
                + ‖Work.Kernels.jInvariantFun τ‖ := norm_sub_le _ _
            _ ≤ (1728 + ‖(2:ℂ) * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
                + ‖Work.Kernels.jInvariantFun τ‖ := by
                have hthis := norm_sub_le (1728:ℂ) (2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))
                rw [show ‖(1728:ℂ)‖ = 1728 by norm_num] at hthis
                linarith
            _ = 1728 + 2 * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖
                + ‖Work.Kernels.jInvariantFun τ‖ := by rw [h2]
            _ ≤ 1728 + 2 * (Aj + Cz * P^2) + Aj := by linarith [hAy, hdiffJ]
            _ ≤ (3456 * (Aj + Cz) + (3 * Aj + 2 * Cz) + (1728 + 3 * Aj + 2 * Cz)) * P ^ 2 := by
                nlinarith [hP2, hAjnn, hCznn, hP0nn]
      have hMc241 : ∀ i : Fin 3, ‖Work.Asymptotics.Mcusp 24 τ z i 1‖ ≤ D1 * P ^ 2 := by
        intro i; rw [hD1def]; exact hMc241' i
      have hMc242 : ∀ i : Fin 3, ‖Work.Asymptotics.Mcusp 24 τ z i 2‖ ≤ 1 := by
        intro i
        fin_cases i <;>
          norm_num [Work.Asymptotics.Mcusp, Work.Kernels.c1728, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
      have hF0 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖ ≤ C14D * P ^ 2 := by
        have hv : Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z =
            Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z := by
          simp [Work.Asymptotics.ulen, Work.Kernels.fk]
        rw [hv, hP]; exact h14 z hz
      have hF1 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖ ≤ 1 := by
        have hv : Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z = 1 := by
          simp [Work.Asymptotics.ulen, Work.Kernels.fk]
        rw [hv, norm_one]
      have hF2 : ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖ ≤ C10D * P ^ 2 := by
        have hv : Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z =
            Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z := by
          simp [Work.Asymptotics.ulen, Work.Kernels.fk]
        rw [hv, hP]; exact h10 z hz
      have hP0 : ‖Work.Asymptotics.Pcusp ℓ 0 z‖ ≤ CLS * t := by
        rw [Work.Asymptotics.Pcusp_zero, ht]; exact hLSb z hz
      have hP1 : ‖Work.Asymptotics.Pcusp ℓ 1 z‖ ≤ CV * t := by
        rw [Work.Asymptotics.Pcusp_one, ht, norm_neg]; exact hVb z hz
      have hP2' : ‖Work.Asymptotics.Pcusp ℓ 2 z‖ ≤ CUW * t := by
        rw [Work.Asymptotics.Pcusp_two, ht]; exact hUWb z hz
      have hMF0 : ∀ i : Fin 3, ‖Work.Asymptotics.Mcusp 24 τ z i 0‖ *
            ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖ ≤ Am0 * P ^ 2 := by
        intro i
        rw [hAm0def]
        calc ‖Work.Asymptotics.Mcusp 24 τ z i 0‖ *
              ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖ ≤ 3456 * (C14D * P ^ 2) :=
              mul_le_mul (hMc240 i) hF0 (norm_nonneg _) (by positivity)
          _ = 3456 * C14D * P ^ 2 := by ring
      have hMF1 : ∀ i : Fin 3, ‖Work.Asymptotics.Mcusp 24 τ z i 1‖ *
            ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖ ≤ D1 * P ^ 2 := by
        intro i
        rw [hD1def]
        calc ‖Work.Asymptotics.Mcusp 24 τ z i 1‖ *
              ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖ ≤ (D1 * P ^ 2) * 1 :=
              mul_le_mul (hMc241 i) hF1 (norm_nonneg _) (by positivity)
          _ = D1 * P ^ 2 := by ring
      have hMF2 : ∀ i : Fin 3, ‖Work.Asymptotics.Mcusp 24 τ z i 2‖ *
            ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖ ≤ Am2 * P ^ 2 := by
        intro i
        rw [hAm2def]
        calc ‖Work.Asymptotics.Mcusp 24 τ z i 2‖ *
              ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖ ≤ 1 * (C10D * P ^ 2) :=
              mul_le_mul (hMc242 i) hF2 (norm_nonneg _) (by positivity)
          _ = C10D * P ^ 2 := by ring
      have hS0 : ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
            Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
            Work.Asymptotics.Mcusp 24 τ z i 0 * Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖
          ≤ 3 * (Bv * Am0 * P ^ 2) := by
        have hper : ∀ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 0 *
              Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖ ≤ Bv * Am0 * P ^ 2 := by
          intro i
          rw [norm_mul, norm_mul, norm_mul, hBvdef]
          have h1 : ‖Work.Kernels.psiVec ℓ τ i‖ *
              ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖ ≤ Bψ * Bf :=
            mul_le_mul (hBψ τ hτ i) (hBf τ hτ i) (norm_nonneg _) hBψpos.le
          calc ((‖Work.Kernels.psiVec ℓ τ i‖ *
                ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖) *
                ‖Work.Asymptotics.Mcusp 24 τ z i 0‖) *
                ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖
              = (‖Work.Kernels.psiVec ℓ τ i‖ *
                  ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖) *
                (‖Work.Asymptotics.Mcusp 24 τ z i 0‖ *
                  ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖) := by ring
            _ ≤ (Bψ * Bf) * (Am0 * P ^ 2) :=
                mul_le_mul h1 (hMF0 i) (by positivity) (by positivity)
            _ = Bψ * Bf * Am0 * P ^ 2 := by ring
        calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 0 * Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖
            ≤ ∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 0 * Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _i : Fin 3, (Bv * Am0 * P ^ 2) := Finset.sum_le_sum (fun i _ => hper i)
          _ = 3 * (Bv * Am0 * P ^ 2) := by rw [Fin.sum_univ_three]; ring
      have hS1 : ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
            Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
            Work.Asymptotics.Mcusp 24 τ z i 1 * Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖
          ≤ 3 * (Bv * D1 * P ^ 2) := by
        have hper : ∀ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 1 *
              Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖ ≤ Bv * D1 * P ^ 2 := by
          intro i
          rw [norm_mul, norm_mul, norm_mul, hBvdef]
          have h1 : ‖Work.Kernels.psiVec ℓ τ i‖ *
              ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖ ≤ Bψ * Bf :=
            mul_le_mul (hBψ τ hτ i) (hBf τ hτ i) (norm_nonneg _) hBψpos.le
          calc ((‖Work.Kernels.psiVec ℓ τ i‖ *
                ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖) *
                ‖Work.Asymptotics.Mcusp 24 τ z i 1‖) *
                ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖
              = (‖Work.Kernels.psiVec ℓ τ i‖ *
                  ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖) *
                (‖Work.Asymptotics.Mcusp 24 τ z i 1‖ *
                  ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖) := by ring
            _ ≤ (Bψ * Bf) * (D1 * P ^ 2) :=
                mul_le_mul h1 (hMF1 i) (by positivity) (by positivity)
            _ = Bψ * Bf * D1 * P ^ 2 := by ring
        calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 1 * Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖
            ≤ ∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 1 * Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _i : Fin 3, (Bv * D1 * P ^ 2) := Finset.sum_le_sum (fun i _ => hper i)
          _ = 3 * (Bv * D1 * P ^ 2) := by rw [Fin.sum_univ_three]; ring
      have hS2 : ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
            Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
            Work.Asymptotics.Mcusp 24 τ z i 2 * Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖
          ≤ 3 * (Bv * Am2 * P ^ 2) := by
        have hper : ∀ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 2 *
              Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖ ≤ Bv * Am2 * P ^ 2 := by
          intro i
          rw [norm_mul, norm_mul, norm_mul, hBvdef]
          have h1 : ‖Work.Kernels.psiVec ℓ τ i‖ *
              ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖ ≤ Bψ * Bf :=
            mul_le_mul (hBψ τ hτ i) (hBf τ hτ i) (norm_nonneg _) hBψpos.le
          calc ((‖Work.Kernels.psiVec ℓ τ i‖ *
                ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖) *
                ‖Work.Asymptotics.Mcusp 24 τ z i 2‖) *
                ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖
              = (‖Work.Kernels.psiVec ℓ τ i‖ *
                  ‖Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ‖) *
                (‖Work.Asymptotics.Mcusp 24 τ z i 2‖ *
                  ‖Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖) := by ring
            _ ≤ (Bψ * Bf) * (Am2 * P ^ 2) :=
                mul_le_mul h1 (hMF2 i) (by positivity) (by positivity)
            _ = Bψ * Bf * Am2 * P ^ 2 := by ring
        calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 2 * Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖
            ≤ ∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 2 * Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _i : Fin 3, (Bv * Am2 * P ^ 2) := Finset.sum_le_sum (fun i _ => hper i)
          _ = 3 * (Bv * Am2 * P ^ 2) := by rw [Fin.sum_univ_three]; ring
      set g : Fin 3 → ℂ := fun m => (∑ i : Fin 3,
            Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i m * Work.Kernels.fk (Work.Asymptotics.ulen 24 m) z) *
            Work.Asymptotics.Pcusp ℓ m z with hg
      have hm0 : ‖g 0‖ ≤ K0 * P := by
        rw [hg]; simp only []; rw [norm_mul]
        calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 0 * Work.Kernels.fk (Work.Asymptotics.ulen 24 0) z‖ *
              ‖Work.Asymptotics.Pcusp ℓ 0 z‖
            ≤ (3 * (Bv * Am0 * P ^ 2)) * (CLS * t) :=
              mul_le_mul hS0 hP0 (norm_nonneg _) (by positivity)
          _ = K0 * P := by
              rw [hK0def]
              linear_combination (3 * Bv * Am0 * CLS * P) * htP
      have hm1 : ‖g 1‖ ≤ K1 * P := by
        rw [hg]; simp only []; rw [norm_mul]
        calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 1 * Work.Kernels.fk (Work.Asymptotics.ulen 24 1) z‖ *
              ‖Work.Asymptotics.Pcusp ℓ 1 z‖
            ≤ (3 * (Bv * D1 * P ^ 2)) * (CV * t) :=
              mul_le_mul hS1 hP1 (norm_nonneg _) (by positivity)
          _ = K1 * P := by
              rw [hK1def]
              linear_combination (3 * Bv * D1 * CV * P) * htP
      have hm2 : ‖g 2‖ ≤ K2 * P := by
        rw [hg]; simp only []; rw [norm_mul]
        calc ‖∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
              Work.Kernels.fk (Work.Asymptotics.vlen 24 i) τ *
              Work.Asymptotics.Mcusp 24 τ z i 2 * Work.Kernels.fk (Work.Asymptotics.ulen 24 2) z‖ *
              ‖Work.Asymptotics.Pcusp ℓ 2 z‖
            ≤ (3 * (Bv * Am2 * P ^ 2)) * (CUW * t) :=
              mul_le_mul hS2 hP2' (norm_nonneg _) (by positivity)
          _ = K2 * P := by
              rw [hK2def]
              linear_combination (3 * Bv * Am2 * CUW * P) * htP
      have hfin : ‖∑ m : Fin 3, g m‖ ≤ (K0 + K1 + K2) * P := by
        rw [Fin.sum_univ_three]
        have hA := norm_add_le (g 0 + g 1) (g 2)
        have hB := norm_add_le (g 0) (g 1)
        calc ‖g 0 + g 1 + g 2‖ ≤ ‖g 0‖ + ‖g 1‖ + ‖g 2‖ := by linarith
          _ ≤ K0 * P + K1 * P + K2 * P := by linarith
          _ = (K0 + K1 + K2) * P := by ring
      have hNc : Work.Asymptotics.Ncusp ℓ 24 τ z =
          ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * ∑ m : Fin 3, g m := by
        unfold Work.Asymptotics.Ncusp
        rw [← hg]
      calc ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖
          = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖∑ m : Fin 3, g m‖ := by
            rw [hNc, norm_mul]
        _ ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ((K0 + K1 + K2) * P) :=
            mul_le_mul_of_nonneg_left hfin (norm_nonneg _)
        _ = (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (K0 + K1 + K2)) * P := by ring
        _ ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (K0 + K1 + K2) + 1) * P := by
            nlinarith [hP0nn, norm_nonneg ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹]

end

end Work.Asymptotics.MFix
