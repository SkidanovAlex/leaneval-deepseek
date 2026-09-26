import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.cusp_U_second
import Submission.Work.Asymptotics.cusp_W_second
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Asymptotics.ratio_second_order
import Submission.Work.Asymptotics.Compact.zsmall
import Submission.Work.FunnelNumerics.Delta_funnel_bounds
import Submission.Work.FunnelNumerics.Lamb_funnel_bound
import Submission.Work.Residues.LamSExpBound
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs

set_option maxHeartbeats 4000000

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Residues

noncomputable section

/-! ## A calculus of `O(‖E‖ᵏ)` on the funnel

`E = Ept τ = e^{πiτ}` and `‖E‖ = tpar τ = e^{-π Im τ} ≤ e^{-2π}` on the funnel. -/

/-- `IsSm k f`: `f = O(‖E‖ᵏ)` on the funnel. -/
def IsSm (k : ℕ) (f : ℍ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ → ‖f τ‖ ≤ C * ‖Work.Residues.Ept τ‖ ^ k

namespace IsSm

theorem mono {k l : ℕ} {f : ℍ → ℂ} (h : IsSm k f) (hl : l ≤ k) : IsSm l f := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h1 : ‖Work.Residues.Ept τ‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one τ)
  have h2 : ‖Work.Residues.Ept τ‖ ^ k ≤ ‖Work.Residues.Ept τ‖ ^ l :=
    pow_le_pow_of_le_one (norm_nonneg _) h1 hl
  exact le_trans (hf τ hτ) (mul_le_mul_of_nonneg_left h2 hC.le)

theorem bdd {f : ℍ → ℂ} {B : ℝ} (hB : 0 < B)
    (h : ∀ τ : ℍ, Work.Asymptotics.Funnel τ → ‖f τ‖ ≤ B) : IsSm 0 f :=
  ⟨B, hB, fun τ hτ => by simpa using h τ hτ⟩

theorem congr {k : ℕ} {f g : ℍ → ℂ} (h : IsSm k f) (hfg : ∀ τ, f τ = g τ) : IsSm k g := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun τ hτ => by rw [← hfg τ]; exact hf τ hτ⟩

theorem congr_on {k : ℕ} {f g : ℍ → ℂ} (h : IsSm k f)
    (hfg : ∀ τ : ℍ, Work.Asymptotics.Funnel τ → f τ = g τ) : IsSm k g := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun τ hτ => by rw [← hfg τ hτ]; exact hf τ hτ⟩

theorem neg {k : ℕ} {f : ℍ → ℂ} (h : IsSm k f) : IsSm k (fun τ => -f τ) := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun τ hτ => by simpa using hf τ hτ⟩

theorem const_mul (c : ℂ) {k : ℕ} {f : ℍ → ℂ} (h : IsSm k f) :
    IsSm k (fun τ => c * f τ) := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨‖c‖ * C + 1, by positivity, fun τ hτ => ?_⟩
  have h1 := hf τ hτ
  have h2 : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ ^ k := by positivity
  rw [norm_mul]
  calc ‖c‖ * ‖f τ‖ ≤ ‖c‖ * (C * ‖Work.Residues.Ept τ‖ ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (‖c‖ * C) * ‖Work.Residues.Ept τ‖ ^ k := by ring
    _ ≤ (‖c‖ * C + 1) * ‖Work.Residues.Ept τ‖ ^ k := by nlinarith [h2]

theorem add {k l : ℕ} {f g : ℍ → ℂ} (hf : IsSm k f) (hg : IsSm l g) :
    IsSm (min k l) (fun τ => f τ + g τ) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, by positivity, fun τ hτ => ?_⟩
  have h1 : ‖Work.Residues.Ept τ‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one τ)
  have hk : ‖Work.Residues.Ept τ‖ ^ k ≤ ‖Work.Residues.Ept τ‖ ^ min k l :=
    pow_le_pow_of_le_one (norm_nonneg _) h1 (min_le_left _ _)
  have hl : ‖Work.Residues.Ept τ‖ ^ l ≤ ‖Work.Residues.Ept τ‖ ^ min k l :=
    pow_le_pow_of_le_one (norm_nonneg _) h1 (min_le_right _ _)
  calc ‖f τ + g τ‖ ≤ ‖f τ‖ + ‖g τ‖ := norm_add_le _ _
    _ ≤ Cf * ‖Work.Residues.Ept τ‖ ^ min k l + Cg * ‖Work.Residues.Ept τ‖ ^ min k l :=
        add_le_add (le_trans (hf τ hτ) (mul_le_mul_of_nonneg_left hk hCf.le))
          (le_trans (hg τ hτ) (mul_le_mul_of_nonneg_left hl hCg.le))
    _ = (Cf + Cg) * ‖Work.Residues.Ept τ‖ ^ min k l := by ring

theorem sub {k l : ℕ} {f g : ℍ → ℂ} (hf : IsSm k f) (hg : IsSm l g) :
    IsSm (min k l) (fun τ => f τ - g τ) := by
  have h := IsSm.add hf (IsSm.neg hg)
  exact IsSm.congr h (fun τ => by simp [sub_eq_add_neg])

theorem mul {k l : ℕ} {f g : ℍ → ℂ} (hf : IsSm k f) (hg : IsSm l g) :
    IsSm (k + l) (fun τ => f τ * g τ) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf * Cg, by positivity, fun τ hτ => ?_⟩
  have h1 : ‖f τ‖ ≤ Cf * ‖Work.Residues.Ept τ‖ ^ k := hf τ hτ
  have h2 : ‖g τ‖ ≤ Cg * ‖Work.Residues.Ept τ‖ ^ l := hg τ hτ
  have h3 : (0 : ℝ) ≤ Cg * ‖Work.Residues.Ept τ‖ ^ l :=
    mul_nonneg hCg.le (by positivity)
  rw [norm_mul, pow_add]
  calc ‖f τ‖ * ‖g τ‖ ≤ (Cf * ‖Work.Residues.Ept τ‖ ^ k) * (Cg * ‖Work.Residues.Ept τ‖ ^ l) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (Cf * Cg) * (‖Work.Residues.Ept τ‖ ^ k * ‖Work.Residues.Ept τ‖ ^ l) := by ring


theorem pow {k : ℕ} {f : ℍ → ℂ} (h : IsSm k f) (n : ℕ) :
    IsSm (k * n) (fun τ => f τ ^ n) := by
  induction n with
  | zero => exact IsSm.bdd (B := 1) (by norm_num) (fun τ _ => by simp)
  | succ m ih =>
    have hm : IsSm (k * m + k) (fun τ => f τ ^ m * f τ) := IsSm.mul ih h
    have heq : k * (m + 1) = k * m + k := by ring
    rw [heq]
    exact IsSm.congr hm (fun τ => by rw [pow_succ])

theorem one : IsSm 0 (fun _ : ℍ => (1 : ℂ)) :=
  IsSm.bdd (B := 1) (by norm_num) (fun _ _ => by simp)

end IsSm

/-- `Ept τ` itself is `O(‖E‖)`. -/
theorem isSm_Ept : IsSm 1 (fun τ => Work.Residues.Ept τ) :=
  ⟨1, one_pos, fun τ _ => by simp⟩

/-- `qParamFun τ = Ept τ ^ 2` is `O(‖E‖²)`. -/
theorem isSm_qParam : IsSm 2 (fun τ => Work.Kernels.qParamFun τ) := by
  refine ⟨1, one_pos, fun τ _ => ?_⟩
  have h : Work.Kernels.qParamFun τ = (Work.Residues.Ept τ) ^ 2 :=
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq τ
  show ‖Work.Kernels.qParamFun τ‖ ≤ 1 * ‖Work.Residues.Ept τ‖ ^ 2
  rw [h, norm_pow]
  ring_nf
  rfl

/-- A monomial `c * E^k` is `O(‖E‖ᵏ)`. -/
theorem isSm_Epow (c : ℂ) (k : ℕ) :
    IsSm k (fun τ => c * (Work.Residues.Ept τ) ^ k) := by
  have h : IsSm k (fun τ => (Work.Residues.Ept τ) ^ k) := by
    simpa using isSm_Ept.pow k
  exact IsSm.const_mul c h


/-! ## Refined cusp expansions of `θ₀₀`, `θ₀₁` -/

private lemma exp_neg_pi_le_half : Real.exp (-Real.pi) ≤ 1 / 2 := by
  have h : (2 : ℝ) ≤ Real.exp Real.pi := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    have h2 : Real.exp 1 ≤ Real.exp Real.pi := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  calc Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
    _ = 1 / 2 := by norm_num

/-- `θ₀₀ = 1 + 2E + 2E⁴ + O(‖E‖⁹)`. -/
private lemma theta00_refined (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ - 2 * (Ept τ) ^ 4‖ ≤ 4 * ‖Ept τ‖ ^ 9 := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖Ept τ‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact norm_Ept_lt_one τ
  have hr2 : r ≤ 1 / 2 := by
    rw [hr]; exact (norm_Ept_le_exp_neg_pi τ hτ).trans exp_neg_pi_le_half
  have hy : 0 < (τ : ℂ).im := by simpa using τ.im_pos
  have htheta : Work.Kernels.theta00Fun τ
      = 1 + 2 * (∑' n : ℕ, Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ))) := by
    have h := jacobiTheta_eq_tsum_nat hy
    rw [show Work.Kernels.theta00Fun τ = jacobiTheta (τ : ℂ) from rfl, h]
  set F : ℕ → ℂ := fun n => Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ))
    with hFdef
  have hsm : Summable F := by
    have hsum : HasSum F ((Work.Kernels.theta00Fun τ - 1) / 2) := by
      simpa [Work.Kernels.theta00Fun] using hasSum_nat_jacobiTheta hy
    exact hsum.summable
  have hnorm_eq : ∀ m : ℕ, ‖F m‖ = r ^ ((m + 1) ^ 2) := by
    intro m
    have h1 : ‖F m‖ = Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * τ.im)) := by
      simp only [hFdef]
      rw [norm_cexp_pi_I_sq_mul' (τ : ℂ) m, UpperHalfPlane.coe_im]
    rw [h1, show ((m : ℝ) + 1) ^ 2 = (((m + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring,
      exp_neg_pi_im_nat_mul, ← hr]
  have hF0 : F 0 = Ept τ := by
    simp only [hFdef]
    simp [Ept]
  have hF1 : F 1 = (Ept τ) ^ 4 := by
    have hthis : Complex.exp (Real.pi * Complex.I * (((1 : ℕ) : ℂ) + 1) ^ 2 * (τ : ℂ))
        = (Ept τ) ^ 4 := by
      have harg : Real.pi * Complex.I * (((1 : ℕ) : ℂ) + 1) ^ 2 * (τ : ℂ)
          = 4 * (Real.pi * Complex.I * (τ : ℂ)) := by norm_num; ring
      rw [harg, show Complex.exp (4 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)))
          = (Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ))) ^ 4 by
        rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul]]
      rfl
    simpa only [hFdef] using hthis
  have hsplit : (∑' n : ℕ, F n) = F 0 + ∑' n : ℕ, F (n + 1) := hsm.tsum_eq_zero_add
  have hshift : (∑' n : ℕ, F (n + 1)) = F 1 + ∑' n : ℕ, F (n + 2) := by
    have hinj : Function.Injective (fun n : ℕ => n + 1) := fun a b h => Nat.succ_injective h
    have hsm' : Summable (fun n : ℕ => F (n + 1)) := hsm.comp_injective hinj
    have h := hsm'.tsum_eq_zero_add
    have h2 : (∑' n : ℕ, F (n + 1 + 1)) = ∑' n : ℕ, F (n + 2) :=
      tsum_congr (fun n => by rw [show n + 1 + 1 = n + 2 from by omega])
    rw [h2] at h
    simpa using h
  have hmain : Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ - 2 * (Ept τ) ^ 4
      = 2 * ∑' n : ℕ, F (n + 2) := by
    rw [htheta, hsplit, hF0, hshift, hF1]
    ring
  have htailterm : ∀ n : ℕ, ‖F (n + 2)‖ ≤ r ^ (n + 9) := by
    intro n
    rw [hnorm_eq (n + 2)]
    have h2 : n + 9 ≤ (n + 3) ^ 2 := by nlinarith
    calc r ^ ((n + 2 + 1) ^ 2) = r ^ ((n + 3) ^ 2) := by ring_nf
      _ ≤ r ^ (n + 9) := pow_le_pow_of_le_one hr0 (le_of_lt hr1) h2
  have hg : HasSum (fun n : ℕ => r ^ (n + 9)) (r ^ 9 / (1 - r)) := by
    have h0 : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr0 hr1
    have h1 := h0.mul_left (r ^ 9)
    have h2 : r ^ 9 * (1 - r)⁻¹ = r ^ 9 / (1 - r) := by rw [div_eq_mul_inv]
    rw [h2] at h1
    refine h1.congr_fun (fun n => ?_)
    rw [mul_comm, pow_add]
  have hsumtail : Summable (fun n : ℕ => ‖F (n + 2)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) htailterm hg.summable
  have htail : ‖∑' n : ℕ, F (n + 2)‖ ≤ r ^ 9 / (1 - r) := by
    refine le_trans (norm_tsum_le_tsum_norm hsumtail) ?_
    have h1 : (∑' n : ℕ, ‖F (n + 2)‖) ≤ ∑' n : ℕ, r ^ (n + 9) :=
      Summable.tsum_le_tsum htailterm hsumtail hg.summable
    rwa [hg.tsum_eq] at h1
  have hden : 0 < 1 - r := by linarith
  have hden2 : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]; linarith
  rw [hmain, norm_mul, Complex.norm_ofNat]
  calc 2 * ‖∑' n : ℕ, F (n + 2)‖ ≤ 2 * (r ^ 9 / (1 - r)) := by linarith [htail]
    _ = 2 * r ^ 9 * (1 - r)⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ 2 * r ^ 9 * 2 := by
        have h0 : (0 : ℝ) ≤ 2 * r ^ 9 := by positivity
        exact mul_le_mul_of_nonneg_left hden2 h0
    _ = 4 * r ^ 9 := by ring
    _ = 4 * ‖Ept τ‖ ^ 9 := by rw [hr]

/-- `θ₀₁ = 1 - 2E + 2E⁴ + O(‖E‖⁹)`. -/
private lemma theta01_refined (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.theta01Fun τ - 1 + 2 * Ept τ - 2 * (Ept τ) ^ 4‖ ≤ 4 * ‖Ept τ‖ ^ 9 := by
  have hτ' : (1 : ℝ) ≤ (ModularGroup.T • τ).im := by
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.vadd_im]; exact hτ
  have h := theta00_refined (ModularGroup.T • τ) hτ'
  rw [Work.Kernels.theta00Fun_T τ, Ept_T τ] at h
  have h' : ‖Work.Kernels.theta01Fun τ - 1 + 2 * Ept τ - 2 * (Ept τ) ^ 4‖
      = ‖Work.Kernels.theta01Fun τ - 1 - 2 * (-Ept τ) - 2 * (-Ept τ) ^ 4‖ := by
    congr 1
    ring
  rw [h']
  rw [norm_neg] at h
  exact h


/-! ## The expansions of `U`, `W`, `V` -/

/-- The fourth-order remainder of `θ₀₀` at the cusp. -/
noncomputable def theta00Rem (τ : ℍ) : ℂ :=
  Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ - 2 * (Ept τ) ^ 4

/-- The fourth-order remainder of `θ₀₁` at the cusp. -/
noncomputable def theta01Rem (τ : ℍ) : ℂ :=
  Work.Kernels.theta01Fun τ - 1 + 2 * Ept τ - 2 * (Ept τ) ^ 4

theorem isSm_theta00Rem : IsSm 6 theta00Rem := by
  refine ⟨4, by norm_num, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) (Work.Asymptotics.Funnel.im_two hτ)
  have h := theta00_refined τ him
  have h9 : ‖Ept τ‖ ^ 9 ≤ ‖Ept τ‖ ^ 6 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (norm_Ept_lt_one τ)) (by norm_num)
  show ‖theta00Rem τ‖ ≤ 4 * ‖Ept τ‖ ^ 6
  simp only [theta00Rem]
  linarith

theorem isSm_theta01Rem : IsSm 6 theta01Rem := by
  refine ⟨4, by norm_num, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) (Work.Asymptotics.Funnel.im_two hτ)
  have h := theta01_refined τ him
  have h9 : ‖Ept τ‖ ^ 9 ≤ ‖Ept τ‖ ^ 6 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (norm_Ept_lt_one τ)) (by norm_num)
  show ‖theta01Rem τ‖ ≤ 4 * ‖Ept τ‖ ^ 6
  simp only [theta01Rem]
  linarith

/-- `1 + 2E + 2E⁴` is bounded on the funnel. -/
theorem isSm_U0 : IsSm 0 (fun τ => 1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) := by
  refine IsSm.bdd (B := 5) (by norm_num) (fun τ _ => ?_)
  have he1 : ‖Ept τ‖ ≤ 1 := le_of_lt (norm_Ept_lt_one τ)
  have h := norm_add_le ((1 : ℂ) + 2 * Ept τ) (2 * (Ept τ) ^ 4)
  have h2 := norm_add_le (1 : ℂ) (2 * Ept τ)
  rw [norm_one] at h2
  have h3 : ‖(2 : ℂ) * Ept τ‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat]; linarith
  have h4 : ‖(2 : ℂ) * (Ept τ) ^ 4‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h5 : ‖Ept τ‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) he1
    linarith
  linarith

/-- `U = 1 + 8E + 24E² + 32E³ + 24E⁴ + O(‖E‖⁵)`. -/
theorem Ufun_exp5 : IsSm 5 (fun τ => Work.Kernels.UFun τ - 1 - 8 * Ept τ - 24 * (Ept τ) ^ 2
    - 32 * (Ept τ) ^ 3 - 24 * (Ept τ) ^ 4) := by
  have hP : IsSm 5 (fun τ => (48 : ℂ) * (Ept τ) ^ 5 + 96 * (Ept τ) ^ 6 + 64 * (Ept τ) ^ 7
      + 24 * (Ept τ) ^ 8 * (1 + 2 * Ept τ) ^ 2
      + 32 * (Ept τ) ^ 12 * (1 + 2 * Ept τ) + 16 * (Ept τ) ^ 16) := by
    have h1 : IsSm 5 (fun τ => (48 : ℂ) * (Ept τ) ^ 5) := isSm_Epow 48 5
    have h2 : IsSm 5 (fun τ => (96 : ℂ) * (Ept τ) ^ 6) := IsSm.mono (isSm_Epow 96 6) (by norm_num)
    have h3 : IsSm 5 (fun τ => (64 : ℂ) * (Ept τ) ^ 7) := IsSm.mono (isSm_Epow 64 7) (by norm_num)
    have hb : IsSm 0 (fun τ => 1 + 2 * Ept τ) := by
      refine IsSm.bdd (B := 3) (by norm_num) (fun τ _ => ?_)
      have he1 : ‖Ept τ‖ ≤ 1 := le_of_lt (norm_Ept_lt_one τ)
      have h := norm_add_le (1 : ℂ) (2 * Ept τ)
      rw [norm_one] at h
      have h3 : ‖(2 : ℂ) * Ept τ‖ ≤ 2 := by rw [norm_mul, Complex.norm_ofNat]; linarith
      linarith
    have h4 : IsSm 5 (fun τ => (24 : ℂ) * (Ept τ) ^ 8 * (1 + 2 * Ept τ) ^ 2) := by
      have h8 : IsSm 8 (fun τ => (24 : ℂ) * (Ept τ) ^ 8) := isSm_Epow 24 8
      have hb2 : IsSm 0 (fun τ => (1 + 2 * Ept τ) ^ 2) := IsSm.mono (IsSm.pow hb 2) (by norm_num)
      have hm := IsSm.mul h8 hb2
      have heq : (fun τ => (24 : ℂ) * (Ept τ) ^ 8 * (1 + 2 * Ept τ) ^ 2)
          = (fun τ => ((24 : ℂ) * (Ept τ) ^ 8) * ((1 + 2 * Ept τ) ^ 2)) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h5 : IsSm 5 (fun τ => (32 : ℂ) * (Ept τ) ^ 12 * (1 + 2 * Ept τ)) := by
      have h12 : IsSm 12 (fun τ => (32 : ℂ) * (Ept τ) ^ 12) := isSm_Epow 32 12
      have hm := IsSm.mul h12 hb
      have heq : (fun τ => (32 : ℂ) * (Ept τ) ^ 12 * (1 + 2 * Ept τ))
          = (fun τ => ((32 : ℂ) * (Ept τ) ^ 12) * (1 + 2 * Ept τ)) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h6 : IsSm 5 (fun τ => (16 : ℂ) * (Ept τ) ^ 16) := IsSm.mono (isSm_Epow 16 16) (by norm_num)
    have h12 := IsSm.add h1 h2
    have h34 := IsSm.add h3 h4
    have h56 := IsSm.add h5 h6
    have h1234 := IsSm.add h12 h34
    have hall := IsSm.add h1234 h56
    have hmin : min (min (min 5 5) (min 5 5)) (min 5 5) = 5 := by norm_num
    rw [hmin] at hall
    exact IsSm.congr hall (fun τ => by ring)
  have hQ : IsSm 5 (fun τ => 4 * theta00Rem τ * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3
      + 6 * theta00Rem τ ^ 2 * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2
      + 4 * theta00Rem τ ^ 3 * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) + theta00Rem τ ^ 4) := by
    have hd : IsSm 6 theta00Rem := isSm_theta00Rem
    have hB : IsSm 0 (fun τ => 1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) := isSm_U0
    have hB3 : IsSm 0 (fun τ => (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3) :=
      IsSm.mono (IsSm.pow hB 3) (by norm_num)
    have hB2 : IsSm 0 (fun τ => (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) :=
      IsSm.mono (IsSm.pow hB 2) (by norm_num)
    have h1 : IsSm 5 (fun τ => 4 * theta00Rem τ * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3) := by
      have h4 : IsSm 6 (fun τ => (4 : ℂ) * theta00Rem τ) := IsSm.const_mul 4 hd
      have hm := IsSm.mul h4 hB3
      have heq : (fun τ => (4 : ℂ) * theta00Rem τ * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3)
          = (fun τ => ((4 : ℂ) * theta00Rem τ) * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h2 : IsSm 5 (fun τ => 6 * theta00Rem τ ^ 2 * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) := by
      have hd2 : IsSm 12 (fun τ => theta00Rem τ ^ 2) := IsSm.pow hd 2
      have h4 : IsSm 12 (fun τ => (6 : ℂ) * theta00Rem τ ^ 2) := IsSm.const_mul 6 hd2
      have hm := IsSm.mul h4 hB2
      have heq : (fun τ => (6 : ℂ) * theta00Rem τ ^ 2 * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2)
          = (fun τ => ((6 : ℂ) * theta00Rem τ ^ 2) * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h3 : IsSm 5 (fun τ => 4 * theta00Rem τ ^ 3 * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4)) := by
      have hd3 : IsSm 18 (fun τ => theta00Rem τ ^ 3) := IsSm.pow hd 3
      have h4 : IsSm 18 (fun τ => (4 : ℂ) * theta00Rem τ ^ 3) := IsSm.const_mul 4 hd3
      have hm := IsSm.mul h4 hB
      have heq : (fun τ => (4 : ℂ) * theta00Rem τ ^ 3 * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4))
          = (fun τ => ((4 : ℂ) * theta00Rem τ ^ 3) * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4)) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h4 : IsSm 5 (fun τ => theta00Rem τ ^ 4) := IsSm.mono (IsSm.pow hd 4) (by norm_num)
    have h12 := IsSm.add h1 h2
    have h34 := IsSm.add h3 h4
    have hall := IsSm.add h12 h34
    have hmin : min (min 5 5) (min 5 5) = 5 := by norm_num
    rw [hmin] at hall
    exact IsSm.congr hall (fun τ => by ring)
  have hpoint : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ((48 : ℂ) * (Ept τ) ^ 5 + 96 * (Ept τ) ^ 6 + 64 * (Ept τ) ^ 7
          + 24 * (Ept τ) ^ 8 * (1 + 2 * Ept τ) ^ 2
          + 32 * (Ept τ) ^ 12 * (1 + 2 * Ept τ) + 16 * (Ept τ) ^ 16)
        + (4 * theta00Rem τ * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3
          + 6 * theta00Rem τ ^ 2 * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2
          + 4 * theta00Rem τ ^ 3 * (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4) + theta00Rem τ ^ 4)
      = Work.Kernels.UFun τ - 1 - 8 * Ept τ - 24 * (Ept τ) ^ 2 - 32 * (Ept τ) ^ 3
        - 24 * (Ept τ) ^ 4 := by
    intro τ _
    have hθ : Work.Kernels.theta00Fun τ = 1 + 2 * Ept τ + 2 * (Ept τ) ^ 4 + theta00Rem τ := by
      simp only [theta00Rem]; ring
    have hU : Work.Kernels.UFun τ = (1 + 2 * Ept τ + 2 * (Ept τ) ^ 4 + theta00Rem τ) ^ 4 := by
      show (Work.Kernels.theta00Fun τ) ^ 4 = _
      rw [hθ]
    rw [hU]
    ring
  exact IsSm.congr_on (IsSm.add hP hQ) hpoint


/-- `1 - 2E` is bounded on the funnel. -/
theorem isSm_W0 : IsSm 0 (fun τ => 1 - 2 * Ept τ) := by
  refine IsSm.bdd (B := 3) (by norm_num) (fun τ _ => ?_)
  have he1 : ‖Ept τ‖ ≤ 1 := le_of_lt (norm_Ept_lt_one τ)
  have h := norm_add_le (1 : ℂ) (-(2 * Ept τ))
  rw [norm_one, norm_neg] at h
  have h3 : ‖(2 : ℂ) * Ept τ‖ ≤ 2 := by rw [norm_mul, Complex.norm_ofNat]; linarith
  have h4 : ‖(1 : ℂ) - 2 * Ept τ‖ ≤ 1 + 2 := by
    have h5 : ‖(1 : ℂ) + -(2 * Ept τ)‖ ≤ 1 + ‖(2 : ℂ) * Ept τ‖ := h
    have h6 : ‖(1 : ℂ) - 2 * Ept τ‖ ≤ ‖(1 : ℂ) + -(2 * Ept τ)‖ := by
      rw [show (1 : ℂ) - 2 * Ept τ = (1 : ℂ) + -(2 * Ept τ) from by ring]
    linarith [h5, h6, h3]
  linarith

/-- `1 - 2E + 2E⁴` is bounded on the funnel. -/
theorem isSm_W0' : IsSm 0 (fun τ => 1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) := by
  refine IsSm.bdd (B := 5) (by norm_num) (fun τ _ => ?_)
  have he1 : ‖Ept τ‖ ≤ 1 := le_of_lt (norm_Ept_lt_one τ)
  have h2 := norm_sub_le (1 : ℂ) (2 * Ept τ)
  rw [norm_one] at h2
  have h3 : ‖(2 : ℂ) * Ept τ‖ ≤ 2 := by rw [norm_mul, Complex.norm_ofNat]; linarith
  have hb1 : ‖(1 : ℂ) - 2 * Ept τ‖ ≤ 1 + 2 := by linarith
  have h4 : ‖(2 : ℂ) * (Ept τ) ^ 4‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h5 : ‖Ept τ‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) he1
    linarith
  have h5 : ‖(1 : ℂ) - 2 * Ept τ + 2 * (Ept τ) ^ 4‖ ≤ (1 + 2) + 2 :=
    le_trans (norm_add_le _ _) (add_le_add hb1 h4)
  linarith

/-- `W = 1 - 8E + 24E² - 32E³ + 24E⁴ + O(‖E‖⁵)`. -/
theorem Wfun_exp5 : IsSm 5 (fun τ => Work.Kernels.WFun τ - 1 + 8 * Ept τ - 24 * (Ept τ) ^ 2
    + 32 * (Ept τ) ^ 3 - 24 * (Ept τ) ^ 4) := by
  have hP : IsSm 5 (fun τ => (-48 : ℂ) * (Ept τ) ^ 5 + 96 * (Ept τ) ^ 6 - 64 * (Ept τ) ^ 7
      + 24 * (Ept τ) ^ 8 * (1 - 2 * Ept τ) ^ 2
      + 32 * (Ept τ) ^ 12 * (1 - 2 * Ept τ) + 16 * (Ept τ) ^ 16) := by
    have h1 : IsSm 5 (fun τ => (-48 : ℂ) * (Ept τ) ^ 5) := isSm_Epow (-48) 5
    have h2 : IsSm 5 (fun τ => (96 : ℂ) * (Ept τ) ^ 6) := IsSm.mono (isSm_Epow 96 6) (by norm_num)
    have h3 : IsSm 5 (fun τ => (-64 : ℂ) * (Ept τ) ^ 7) := IsSm.mono (isSm_Epow (-64) 7) (by norm_num)
    have hb : IsSm 0 (fun τ => 1 - 2 * Ept τ) := isSm_W0
    have h4 : IsSm 5 (fun τ => (24 : ℂ) * (Ept τ) ^ 8 * (1 - 2 * Ept τ) ^ 2) := by
      have h8 : IsSm 8 (fun τ => (24 : ℂ) * (Ept τ) ^ 8) := isSm_Epow 24 8
      have hb2 : IsSm 0 (fun τ => (1 - 2 * Ept τ) ^ 2) := IsSm.mono (IsSm.pow hb 2) (by norm_num)
      have hm := IsSm.mul h8 hb2
      have heq : (fun τ => (24 : ℂ) * (Ept τ) ^ 8 * (1 - 2 * Ept τ) ^ 2)
          = (fun τ => ((24 : ℂ) * (Ept τ) ^ 8) * ((1 - 2 * Ept τ) ^ 2)) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h5 : IsSm 5 (fun τ => (32 : ℂ) * (Ept τ) ^ 12 * (1 - 2 * Ept τ)) := by
      have h12 : IsSm 12 (fun τ => (32 : ℂ) * (Ept τ) ^ 12) := isSm_Epow 32 12
      have hm := IsSm.mul h12 hb
      have heq : (fun τ => (32 : ℂ) * (Ept τ) ^ 12 * (1 - 2 * Ept τ))
          = (fun τ => ((32 : ℂ) * (Ept τ) ^ 12) * (1 - 2 * Ept τ)) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h6 : IsSm 5 (fun τ => (16 : ℂ) * (Ept τ) ^ 16) := IsSm.mono (isSm_Epow 16 16) (by norm_num)
    have h12 := IsSm.add h1 h2
    have h34 := IsSm.add h3 h4
    have h56 := IsSm.add h5 h6
    have h1234 := IsSm.add h12 h34
    have hall := IsSm.add h1234 h56
    have hmin : min (min (min 5 5) (min 5 5)) (min 5 5) = 5 := by norm_num
    rw [hmin] at hall
    exact IsSm.congr hall (fun τ => by ring)
  have hQ : IsSm 5 (fun τ => 4 * theta01Rem τ * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3
      + 6 * theta01Rem τ ^ 2 * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2
      + 4 * theta01Rem τ ^ 3 * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) + theta01Rem τ ^ 4) := by
    have hd : IsSm 6 theta01Rem := isSm_theta01Rem
    have hB : IsSm 0 (fun τ => 1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) := isSm_W0'
    have hB3 : IsSm 0 (fun τ => (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3) :=
      IsSm.mono (IsSm.pow hB 3) (by norm_num)
    have hB2 : IsSm 0 (fun τ => (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) :=
      IsSm.mono (IsSm.pow hB 2) (by norm_num)
    have h1 : IsSm 5 (fun τ => 4 * theta01Rem τ * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3) := by
      have h4 : IsSm 6 (fun τ => (4 : ℂ) * theta01Rem τ) := IsSm.const_mul 4 hd
      have hm := IsSm.mul h4 hB3
      have heq : (fun τ => (4 : ℂ) * theta01Rem τ * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3)
          = (fun τ => ((4 : ℂ) * theta01Rem τ) * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h2 : IsSm 5 (fun τ => 6 * theta01Rem τ ^ 2 * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) := by
      have hd2 : IsSm 12 (fun τ => theta01Rem τ ^ 2) := IsSm.pow hd 2
      have h4 : IsSm 12 (fun τ => (6 : ℂ) * theta01Rem τ ^ 2) := IsSm.const_mul 6 hd2
      have hm := IsSm.mul h4 hB2
      have heq : (fun τ => (6 : ℂ) * theta01Rem τ ^ 2 * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2)
          = (fun τ => ((6 : ℂ) * theta01Rem τ ^ 2) * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h3 : IsSm 5 (fun τ => 4 * theta01Rem τ ^ 3 * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4)) := by
      have hd3 : IsSm 18 (fun τ => theta01Rem τ ^ 3) := IsSm.pow hd 3
      have h4 : IsSm 18 (fun τ => (4 : ℂ) * theta01Rem τ ^ 3) := IsSm.const_mul 4 hd3
      have hm := IsSm.mul h4 hB
      have heq : (fun τ => (4 : ℂ) * theta01Rem τ ^ 3 * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4))
          = (fun τ => ((4 : ℂ) * theta01Rem τ ^ 3) * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4)) := by
        funext τ; ring
      rw [heq]
      exact IsSm.mono hm (by norm_num)
    have h4 : IsSm 5 (fun τ => theta01Rem τ ^ 4) := IsSm.mono (IsSm.pow hd 4) (by norm_num)
    have h12 := IsSm.add h1 h2
    have h34 := IsSm.add h3 h4
    have hall := IsSm.add h12 h34
    have hmin : min (min 5 5) (min 5 5) = 5 := by norm_num
    rw [hmin] at hall
    exact IsSm.congr hall (fun τ => by ring)
  have hpoint : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ((-48 : ℂ) * (Ept τ) ^ 5 + 96 * (Ept τ) ^ 6 - 64 * (Ept τ) ^ 7
          + 24 * (Ept τ) ^ 8 * (1 - 2 * Ept τ) ^ 2
          + 32 * (Ept τ) ^ 12 * (1 - 2 * Ept τ) + 16 * (Ept τ) ^ 16)
        + (4 * theta01Rem τ * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3
          + 6 * theta01Rem τ ^ 2 * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2
          + 4 * theta01Rem τ ^ 3 * (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4) + theta01Rem τ ^ 4)
      = Work.Kernels.WFun τ - 1 + 8 * Ept τ - 24 * (Ept τ) ^ 2 + 32 * (Ept τ) ^ 3
        - 24 * (Ept τ) ^ 4 := by
    intro τ _
    have hθ : Work.Kernels.theta01Fun τ = 1 - 2 * Ept τ + 2 * (Ept τ) ^ 4 + theta01Rem τ := by
      simp only [theta01Rem]; ring
    have hW : Work.Kernels.WFun τ = (1 - 2 * Ept τ + 2 * (Ept τ) ^ 4 + theta01Rem τ) ^ 4 := by
      show (Work.Kernels.theta01Fun τ) ^ 4 = _
      rw [hθ]
    rw [hW]
    ring
  exact IsSm.congr_on (IsSm.add hP hQ) hpoint

/-- `V = U - W = 16E + 64E³ + O(‖E‖⁵)` (the quartic identity `U = W + V`). -/
theorem Vfun_exp5 : IsSm 5 (fun τ => Work.Kernels.VFun τ - 16 * Ept τ - 64 * (Ept τ) ^ 3) := by
  have hpoint : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      (Work.Kernels.UFun τ - 1 - 8 * Ept τ - 24 * (Ept τ) ^ 2 - 32 * (Ept τ) ^ 3
          - 24 * (Ept τ) ^ 4)
        - (Work.Kernels.WFun τ - 1 + 8 * Ept τ - 24 * (Ept τ) ^ 2 + 32 * (Ept τ) ^ 3
          - 24 * (Ept τ) ^ 4)
      = Work.Kernels.VFun τ - 16 * Ept τ - 64 * (Ept τ) ^ 3 := by
    intro τ _
    have hq := Work.Kernels.TildeFacts.theta_quartic τ
    show _ = Work.Kernels.VFun τ - 16 * Ept τ - 64 * (Ept τ) ^ 3
    have : Work.Kernels.UFun τ = Work.Kernels.WFun τ + Work.Kernels.VFun τ := hq
    rw [this]
    ring
  exact IsSm.congr_on (IsSm.sub Ufun_exp5 Wfun_exp5) hpoint

/-! ## The two-term expansions of `E₄`, `E₆`, `Δ`, `E₂` -/

theorem E4_two : IsSm 4 (fun τ => Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E4FunSecondOrder
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) (Work.Asymptotics.Funnel.im_two hτ)
  have h1 := h τ him
  have h2 : ‖Work.Kernels.qParamFun τ‖ ^ 2 = ‖Ept τ‖ ^ 4 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq, norm_pow]
    ring
  rwa [h2] at h1

theorem E6_two : IsSm 4 (fun τ => Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E6FunSecondOrder
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) (Work.Asymptotics.Funnel.im_two hτ)
  have h1 := h τ him
  have h2 : ‖Work.Kernels.qParamFun τ‖ ^ 2 = ‖Ept τ‖ ^ 4 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq, norm_pow]
    ring
  rwa [h2] at h1

theorem Delta_two : IsSm 4 (fun τ => Work.Kernels.DeltaFun τ - (Ept τ) ^ 2) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.DeltaExpansion
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) (Work.Asymptotics.Funnel.im_two hτ)
  exact h τ him

theorem E2_two : IsSm 4 (fun τ => Work.Kernels.E2Fun τ - 1 + 24 * (Ept τ) ^ 2) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.Small.E2_sub_one_second
  refine ⟨C, hC, fun τ hτ => ?_⟩
  show ‖Work.Kernels.E2Fun τ - 1 + 24 * (Ept τ) ^ 2‖ ≤ C * ‖Ept τ‖ ^ 4
  have him : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) (Work.Asymptotics.Funnel.im_two hτ)
  have h2 : ‖Work.Kernels.qParamFun τ‖ ^ 2 = ‖Ept τ‖ ^ 4 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq, norm_pow]
    ring
  have h0 : Work.Kernels.E2Fun τ - 1 + 24 * (Ept τ) ^ 2
      = Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq]
  have h1 : ‖Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ‖
      ≤ C * ‖Ept τ‖ ^ 4 := by
    have := h τ him
    rwa [h2] at this
  rwa [h0]



/-! ## The logarithmic Taylor remainder -/

private lemma log_taylor3 (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)‖ ≤ 2 * ‖z‖ ^ 4 := by
  have hzlt : ‖z‖ < 1 := by linarith
  have h := Complex.norm_log_sub_logTaylor_le 3 (z := z) hzlt
  have hlt : Complex.logTaylor 4 z = z - z ^ 2 / 2 + z ^ 3 / 3 := by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    ring
  rw [hlt] at h
  norm_num at h
  have hpos : (0 : ℝ) < 1 - ‖z‖ := by linarith [norm_nonneg z]
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos (by norm_num)]; linarith
  have h4 : (0 : ℝ) ≤ ‖z‖ ^ 4 := by positivity
  calc ‖Complex.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)‖
      ≤ ‖z‖ ^ 4 * (1 - ‖z‖)⁻¹ / 4 := h
    _ ≤ ‖z‖ ^ 4 * 2 / 4 := by gcongr
    _ = ‖z‖ ^ 4 / 2 := by ring
    _ ≤ 2 * ‖z‖ ^ 4 := by linarith

/-- `‖E‖ ≤ 1/16` on the funnel. -/
private lemma e_le_inv_sixteen (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Ept τ‖ ≤ 1 / 16 := by
  have h2 : (2 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_two hτ
  have h : ‖Ept τ‖ = Real.exp (-(Real.pi * τ.im)) := norm_Ept τ
  rw [h]
  have h1 : (6 : ℝ) ≤ Real.pi * τ.im := by nlinarith [Real.pi_gt_three]
  calc Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp 6)⁻¹ := Real.exp_neg 6
    _ ≤ (16 : ℝ)⁻¹ := by
        refine inv_anti₀ (by norm_num) ?_
        have h4 : Real.exp 6 = (Real.exp 1) ^ 6 := by
          rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        rw [h4]
        have h5 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h5 4
          _ ≤ (Real.exp 1) ^ 6 := by
              have h6 : (1 : ℝ) ≤ Real.exp 1 := le_of_lt (Real.one_lt_exp_iff.mpr (by norm_num))
              exact pow_le_pow_right₀ h6 (by norm_num)
    _ = 1 / 16 := by norm_num

/-- The remainder of `θ₀₀` is `O(‖E‖⁶)`. -/
theorem theta00Rem_le (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖theta00Rem τ‖ ≤ 4 * ‖Ept τ‖ ^ 6 := by
  have him : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) (Work.Asymptotics.Funnel.im_two hτ)
  have h := theta00_refined τ him
  have h9 : ‖Ept τ‖ ^ 9 ≤ ‖Ept τ‖ ^ 6 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (norm_Ept_lt_one τ)) (by norm_num)
  show ‖theta00Rem τ‖ ≤ 4 * ‖Ept τ‖ ^ 6
  simp only [theta00Rem]
  linarith

/-- The remainder of `θ₀₁` is `O(‖E‖⁶)`. -/
theorem theta01Rem_le (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖theta01Rem τ‖ ≤ 4 * ‖Ept τ‖ ^ 6 := by
  have him : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) (Work.Asymptotics.Funnel.im_two hτ)
  have h := theta01_refined τ him
  have h9 : ‖Ept τ‖ ^ 9 ≤ ‖Ept τ‖ ^ 6 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (norm_Ept_lt_one τ)) (by norm_num)
  show ‖theta01Rem τ‖ ≤ 4 * ‖Ept τ‖ ^ 6
  simp only [theta01Rem]
  linarith

/-- `z₀ = 2E + 2E⁴`, the leading part of `θ₀₀ - 1`. -/
noncomputable def Z00 (τ : ℍ) : ℂ := 2 * Ept τ + 2 * (Ept τ) ^ 4 + theta00Rem τ

/-- `z₀' = -2E + 2E⁴`, the leading part of `θ₀₁ - 1`. -/
noncomputable def Z01 (τ : ℍ) : ℂ := -2 * Ept τ + 2 * (Ept τ) ^ 4 + theta01Rem τ

theorem Z00_le (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) : ‖Z00 τ‖ ≤ 8 * ‖Ept τ‖ := by
  have he : ‖Ept τ‖ ≤ 1 / 16 := e_le_inv_sixteen τ hτ
  have h1 : ‖2 * Ept τ‖ = 2 * ‖Ept τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  have h2 : ‖2 * (Ept τ) ^ 4‖ = 2 * ‖Ept τ‖ ^ 4 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
  have h3 : ‖theta00Rem τ‖ ≤ 4 * ‖Ept τ‖ ^ 6 := theta00Rem_le τ hτ
  have h4 : ‖Ept τ‖ ^ 4 ≤ ‖Ept τ‖ :=
    (by simpa using pow_le_pow_of_le_one (norm_nonneg _) (le_trans he (by norm_num)) (by norm_num : 1 ≤ 4))
  have h5 : ‖Ept τ‖ ^ 6 ≤ ‖Ept τ‖ :=
    (by simpa using pow_le_pow_of_le_one (norm_nonneg _) (le_trans he (by norm_num)) (by norm_num : 1 ≤ 6))
  have h := norm_add_le (2 * Ept τ + 2 * (Ept τ) ^ 4) (theta00Rem τ)
  have h6 := norm_add_le (2 * Ept τ) (2 * (Ept τ) ^ 4)
  show ‖Z00 τ‖ ≤ 8 * ‖Ept τ‖
  simp only [Z00]
  rw [h1, h2] at h6
  ring_nf at h h6 ⊢
  linarith

theorem Z00_half (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) : ‖Z00 τ‖ ≤ 1 / 2 := by
  have h := Z00_le τ hτ
  have he : ‖Ept τ‖ ≤ 1 / 16 := e_le_inv_sixteen τ hτ
  linarith

theorem Z01_le (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) : ‖Z01 τ‖ ≤ 8 * ‖Ept τ‖ := by
  have he : ‖Ept τ‖ ≤ 1 / 16 := e_le_inv_sixteen τ hτ
  have h1 : ‖2 * Ept τ‖ = 2 * ‖Ept τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  have h2 : ‖2 * (Ept τ) ^ 4‖ = 2 * ‖Ept τ‖ ^ 4 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
  have h3 : ‖theta01Rem τ‖ ≤ 4 * ‖Ept τ‖ ^ 6 := theta01Rem_le τ hτ
  have h4 : ‖Ept τ‖ ^ 4 ≤ ‖Ept τ‖ :=
    (by simpa using pow_le_pow_of_le_one (norm_nonneg _) (le_trans he (by norm_num)) (by norm_num : 1 ≤ 4))
  have h5 : ‖Ept τ‖ ^ 6 ≤ ‖Ept τ‖ :=
    (by simpa using pow_le_pow_of_le_one (norm_nonneg _) (le_trans he (by norm_num)) (by norm_num : 1 ≤ 6))
  have h := norm_add_le ((-2 * Ept τ) + 2 * (Ept τ) ^ 4) (theta01Rem τ)
  have h6 := norm_add_le (-(2 * Ept τ)) (2 * (Ept τ) ^ 4)
  rw [norm_neg, h1, h2] at h6
  show ‖Z01 τ‖ ≤ 8 * ‖Ept τ‖
  simp only [Z01]
  ring_nf at h h6 ⊢
  linarith

theorem Z01_half (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) : ‖Z01 τ‖ ≤ 1 / 2 := by
  have h := Z01_le τ hτ
  have he : ‖Ept τ‖ ≤ 1 / 16 := e_le_inv_sixteen τ hτ
  linarith

theorem isSm_Z00 : IsSm 1 Z00 := by
  have h1 : IsSm 1 (fun τ => (2 : ℂ) * Ept τ) := by simpa using isSm_Epow (2 : ℂ) 1
  have h2 : IsSm 1 (fun τ => (2 : ℂ) * (Ept τ) ^ 4) :=
    IsSm.mono (isSm_Epow 2 4) (show 1 ≤ 4 by norm_num)
  have h3 : IsSm 1 theta00Rem := IsSm.mono isSm_theta00Rem (show 1 ≤ 6 by norm_num)
  have h12 : IsSm 1 (fun τ => (2 : ℂ) * Ept τ + (2 : ℂ) * (Ept τ) ^ 4) := by
    have h := IsSm.add h1 h2
    have hmin : min 1 1 = 1 := by norm_num
    rw [hmin] at h
    exact h
  have hall : IsSm 1 (fun τ => (2 : ℂ) * Ept τ + (2 : ℂ) * (Ept τ) ^ 4 + theta00Rem τ) := by
    have h := IsSm.add h12 h3
    have hmin : min 1 1 = 1 := by norm_num
    rw [hmin] at h
    exact h
  exact IsSm.congr hall (fun τ => by simp only [Z00]; try ring)

theorem isSm_Z01 : IsSm 1 Z01 := by
  have h1 : IsSm 1 (fun τ => (-2 : ℂ) * Ept τ) := by
    simpa using isSm_Epow (-2 : ℂ) 1
  have h2 : IsSm 1 (fun τ => (2 : ℂ) * (Ept τ) ^ 4) :=
    IsSm.mono (isSm_Epow 2 4) (show 1 ≤ 4 by norm_num)
  have h3 : IsSm 1 theta01Rem := IsSm.mono isSm_theta01Rem (show 1 ≤ 6 by norm_num)
  have h12 : IsSm 1 (fun τ => (-2 : ℂ) * Ept τ + (2 : ℂ) * (Ept τ) ^ 4) := by
    have h := IsSm.add h1 h2
    have hmin : min 1 1 = 1 := by norm_num
    rw [hmin] at h
    exact h
  have hall : IsSm 1 (fun τ => (-2 : ℂ) * Ept τ + 2 * (Ept τ) ^ 4 + theta01Rem τ) := by
    have h := IsSm.add h12 h3
    have hmin : min 1 1 = 1 := by norm_num
    rw [hmin] at h
    exact h
  exact IsSm.congr hall (fun τ => by rfl)

/-- `‖2E + 2E⁴‖ ≤ 1/4` on the funnel. -/
theorem Z00_lead_le (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖2 * Ept τ + 2 * (Ept τ) ^ 4‖ ≤ 1 / 4 := by
  have he : ‖Ept τ‖ ≤ 1 / 16 := e_le_inv_sixteen τ hτ
  have he1 : ‖Ept τ‖ ≤ 1 := le_trans he (by norm_num)
  have h0 : (0 : ℝ) ≤ ‖Ept τ‖ := norm_nonneg _
  have h4 : ‖Ept τ‖ ^ 4 ≤ ‖Ept τ‖ :=
    (by simpa using pow_le_pow_of_le_one h0 he1 (by norm_num : 1 ≤ 4))
  have h1 : ‖2 * Ept τ‖ = 2 * ‖Ept τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  have h2 : ‖2 * (Ept τ) ^ 4‖ = 2 * ‖Ept τ‖ ^ 4 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
  have h6 := norm_add_le (2 * Ept τ) (2 * (Ept τ) ^ 4)
  rw [h1, h2] at h6
  linarith

/-- `‖-2E + 2E⁴‖ ≤ 1/4` on the funnel. -/
theorem Z01_lead_le (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖-2 * Ept τ + 2 * (Ept τ) ^ 4‖ ≤ 1 / 4 := by
  have he : ‖Ept τ‖ ≤ 1 / 16 := e_le_inv_sixteen τ hτ
  have he1 : ‖Ept τ‖ ≤ 1 := le_trans he (by norm_num)
  have h0 : (0 : ℝ) ≤ ‖Ept τ‖ := norm_nonneg _
  have h4 : ‖Ept τ‖ ^ 4 ≤ ‖Ept τ‖ :=
    (by simpa using pow_le_pow_of_le_one h0 he1 (by norm_num : 1 ≤ 4))
  have h1 : ‖2 * Ept τ‖ = 2 * ‖Ept τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  have h2 : ‖2 * (Ept τ) ^ 4‖ = 2 * ‖Ept τ‖ ^ 4 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
  have h6 := norm_add_le (-(2 * Ept τ)) (2 * (Ept τ) ^ 4)
  rw [norm_neg, h1, h2] at h6
  have heq : ‖-2 * Ept τ + 2 * (Ept τ) ^ 4‖ = ‖-(2 * Ept τ) + 2 * (Ept τ) ^ 4‖ := by
    congr 1; ring
  rw [heq]
  linarith

noncomputable def B00 (τ : ℍ) : ℂ := (1 : ℂ) - (Z00 τ + (2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2
    + (Z00 τ ^ 2 + Z00 τ * (2 * Ept τ + 2 * (Ept τ) ^ 4) + (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3

noncomputable def B01 (τ : ℍ) : ℂ := (1 : ℂ) - (Z01 τ + (-2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2
    + (Z01 τ ^ 2 + Z01 τ * (-2 * Ept τ + 2 * (Ept τ) ^ 4) + (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3

theorem isSm_Z00_lead : IsSm 0 (fun τ => 2 * Ept τ + 2 * (Ept τ) ^ 4) :=
  IsSm.bdd (B := 1/4) (by norm_num) (fun τ hτ => Z00_lead_le τ hτ)

theorem isSm_Z01_lead : IsSm 0 (fun τ => -2 * Ept τ + 2 * (Ept τ) ^ 4) :=
  IsSm.bdd (B := 1/4) (by norm_num) (fun τ hτ => Z01_lead_le τ hτ)

theorem e_le_inv_256 (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) : ‖Ept τ‖ ≤ 1 / 256 := by
  have h2 : (2 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_two hτ
  have h : ‖Ept τ‖ = Real.exp (-(Real.pi * τ.im)) := norm_Ept τ
  rw [h]
  have h1 : (6 : ℝ) ≤ Real.pi * τ.im := by nlinarith [Real.pi_gt_three]
  have hmono : Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
  have h64 : (256 : ℝ) ≤ Real.exp 6 := by
    have h5 : (2.7 : ℝ) ≤ Real.exp 1 :=
      le_of_lt (lt_trans (by norm_num : (2.7 : ℝ) < 2.7182818283) Real.exp_one_gt_d9)
    have h6 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) h5 6
    have h7 : (Real.exp 1) ^ 6 = Real.exp 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h7] at h6
    nlinarith [h6]
  calc Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-6) := hmono
    _ = (Real.exp 6)⁻¹ := Real.exp_neg 6
    _ ≤ (256 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h64
    _ = 1 / 256 := by norm_num

theorem Z00_le16 (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) : ‖Z00 τ‖ ≤ 1 / 16 := by
  have h := Z00_le τ hτ
  have he : ‖Ept τ‖ ≤ 1 / 256 := e_le_inv_256 τ hτ
  linarith

/-- `‖U - 1‖ ≤ 1/2` on the funnel. -/
theorem Usub1_le (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.UFun τ - 1‖ ≤ 1 / 2 := by
  have hθ : Work.Kernels.theta00Fun τ = 1 + Z00 τ := by
    simp only [Z00, theta00Rem]; ring
  have hx : ‖Z00 τ‖ ≤ 1 / 16 := Z00_le16 τ hτ
  have hU : Work.Kernels.UFun τ = (1 + Z00 τ) ^ 4 := by
    show (Work.Kernels.theta00Fun τ) ^ 4 = _
    rw [hθ]
  rw [hU]
  have hkey : (1 + Z00 τ) ^ 4 - 1 = Z00 τ * (4 + 6 * Z00 τ + 4 * Z00 τ ^ 2 + Z00 τ ^ 3) := by
    ring
  rw [hkey, norm_mul]
  have h1 : ‖4 + 6 * Z00 τ + 4 * Z00 τ ^ 2 + Z00 τ ^ 3‖ ≤ 4 + 6 * (1 / 16) + 4 * (1 / 16) ^ 2
      + (1 / 16) ^ 3 := by
    have h2 : ‖(6 : ℂ) * Z00 τ‖ = 6 * ‖Z00 τ‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h3 : ‖(4 : ℂ) * Z00 τ ^ 2‖ = 4 * ‖Z00 τ‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h4 : ‖Z00 τ ^ 3‖ = ‖Z00 τ‖ ^ 3 := norm_pow _ _
    have h5 : ‖(4 : ℂ)‖ = 4 := by norm_num
    have h6 := norm_add_le ((4 : ℂ) + 6 * Z00 τ + 4 * Z00 τ ^ 2) (Z00 τ ^ 3)
    have h7 := norm_add_le ((4 : ℂ) + 6 * Z00 τ) (4 * Z00 τ ^ 2)
    have h8 := norm_add_le (4 : ℂ) (6 * Z00 τ)
    rw [h5] at h8
    rw [h2] at h8
    rw [h3] at h7
    rw [h4] at h6
    have h9 : ‖Z00 τ‖ ^ 2 ≤ (1 / 16) ^ 2 := by nlinarith [hx, norm_nonneg (Z00 τ)]
    have h10 : ‖Z00 τ‖ ^ 3 ≤ (1 / 16) ^ 3 := by nlinarith [hx, norm_nonneg (Z00 τ)]
    linarith
  have hb : ‖4 + 6 * Z00 τ + 4 * Z00 τ ^ 2 + Z00 τ ^ 3‖ ≤ 5 := by
    nlinarith [h1]
  nlinarith [hx, hb, norm_nonneg (Z00 τ)]

theorem Usub1_le_e (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.UFun τ - 1‖ ≤ 41 * ‖Ept τ‖ := by
  have hθ : Work.Kernels.theta00Fun τ = 1 + Z00 τ := by
    simp only [Z00, theta00Rem]; ring
  have hx : ‖Z00 τ‖ ≤ 8 * ‖Ept τ‖ := Z00_le τ hτ
  have he : ‖Ept τ‖ ≤ 1 / 256 := e_le_inv_256 τ hτ
  have hU : Work.Kernels.UFun τ = (1 + Z00 τ) ^ 4 := by
    show (Work.Kernels.theta00Fun τ) ^ 4 = _
    rw [hθ]
  rw [hU]
  have hkey : (1 + Z00 τ) ^ 4 - 1 = Z00 τ * (4 + 6 * Z00 τ + 4 * Z00 τ ^ 2 + Z00 τ ^ 3) := by
    ring
  rw [hkey, norm_mul]
  have h1 : ‖4 + 6 * Z00 τ + 4 * Z00 τ ^ 2 + Z00 τ ^ 3‖ ≤ 5 := by
    have h2 : ‖(6 : ℂ) * Z00 τ‖ = 6 * ‖Z00 τ‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h3 : ‖(4 : ℂ) * Z00 τ ^ 2‖ = 4 * ‖Z00 τ‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h4 : ‖Z00 τ ^ 3‖ = ‖Z00 τ‖ ^ 3 := norm_pow _ _
    have h5 : ‖(4 : ℂ)‖ = 4 := by norm_num
    have h6 := norm_add_le ((4 : ℂ) + 6 * Z00 τ + 4 * Z00 τ ^ 2) (Z00 τ ^ 3)
    have h7 := norm_add_le ((4 : ℂ) + 6 * Z00 τ) (4 * Z00 τ ^ 2)
    have h8 := norm_add_le (4 : ℂ) (6 * Z00 τ)
    rw [h5] at h8
    rw [h2] at h8
    rw [h3] at h7
    rw [h4] at h6
    have h0 : (0 : ℝ) ≤ ‖Z00 τ‖ := norm_nonneg _
    have h9 : ‖Z00 τ‖ ^ 2 ≤ (8 * ‖Ept τ‖) ^ 2 := pow_le_pow_left₀ h0 hx 2
    have h10 : ‖Z00 τ‖ ^ 3 ≤ (8 * ‖Ept τ‖) ^ 3 := pow_le_pow_left₀ h0 hx 3
    have he0 : (0 : ℝ) ≤ ‖Ept τ‖ := norm_nonneg _
    have he1 : ‖Ept τ‖ ≤ 1 := le_trans he (by norm_num)
    nlinarith [h6, h7, h8, h9, h10, he0, he1]
  have h0 : (0 : ℝ) ≤ ‖Z00 τ‖ := norm_nonneg _
  have he0 : (0 : ℝ) ≤ ‖Ept τ‖ := norm_nonneg _
  nlinarith [hx, h1, h0, he0, he]

/-- **The logarithmic expansion of `θ₀₀`**: `log θ₀₀ = 2E - 2E² + (8/3)E³ + O(‖E‖⁴)`. -/
theorem isSm_log_theta00 : IsSm 4 (fun τ => Complex.log (Work.Kernels.theta00Fun τ)
    - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3)) := by
  -- the logarithmic Taylor remainder
  have hR : IsSm 4 (fun τ => Complex.log (1 + Z00 τ)
      - (Z00 τ - Z00 τ ^ 2 / 2 + Z00 τ ^ 3 / 3)) := by
    refine ⟨8193, by norm_num, fun τ hτ => ?_⟩
    have h := log_taylor3 (Z00 τ) (Z00_half τ hτ)
    have hz : ‖Z00 τ‖ ≤ 8 * ‖Ept τ‖ := Z00_le τ hτ
    have h4 : ‖Z00 τ‖ ^ 4 ≤ (8 * ‖Ept τ‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hz 4
    have he0 : (0 : ℝ) ≤ ‖Ept τ‖ ^ 4 := by positivity
    calc ‖Complex.log (1 + Z00 τ) - (Z00 τ - Z00 τ ^ 2 / 2 + Z00 τ ^ 3 / 3)‖
        ≤ 2 * ‖Z00 τ‖ ^ 4 := h
      _ ≤ 2 * (8 * ‖Ept τ‖) ^ 4 := by linarith
      _ = 8192 * ‖Ept τ‖ ^ 4 := by ring
      _ ≤ 8193 * ‖Ept τ‖ ^ 4 := by linarith [he0]
  -- the boundedness of the second-order factor
  have hBdd : IsSm 0 B00 := by
    refine IsSm.bdd (B := 2) (by norm_num) (fun τ hτ => ?_)
    have hz : ‖Z00 τ‖ ≤ 1 / 2 := Z00_half τ hτ
    have hz0 : ‖2 * Ept τ + 2 * (Ept τ) ^ 4‖ ≤ 1 / 4 := Z00_lead_le τ hτ
    have hsum : ‖Z00 τ + (2 * Ept τ + 2 * (Ept τ) ^ 4)‖ ≤ 1 / 2 + 1 / 4 :=
      le_trans (norm_add_le _ _) (add_le_add hz hz0)
    have hs2 : ‖Z00 τ ^ 2 + Z00 τ * (2 * Ept τ + 2 * (Ept τ) ^ 4)
        + (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2‖ ≤ 1 / 4 + 1 / 8 + 1 / 16 := by
      have hA : ‖Z00 τ ^ 2‖ ≤ 1 / 4 := by rw [norm_pow]; nlinarith [hz, norm_nonneg (Z00 τ)]
      have hB : ‖Z00 τ * (2 * Ept τ + 2 * (Ept τ) ^ 4)‖ ≤ 1 / 8 := by
        rw [norm_mul]
        nlinarith [hz, hz0, norm_nonneg (Z00 τ), norm_nonneg (2 * Ept τ + 2 * (Ept τ) ^ 4)]
      have hC : ‖(2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2‖ ≤ 1 / 16 := by
        rw [norm_pow]; nlinarith [hz0, norm_nonneg (2 * Ept τ + 2 * (Ept τ) ^ 4)]
      have h1 := norm_add_le (Z00 τ ^ 2 + Z00 τ * (2 * Ept τ + 2 * (Ept τ) ^ 4))
        ((2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2)
      have h0 := norm_add_le (Z00 τ ^ 2) (Z00 τ * (2 * Ept τ + 2 * (Ept τ) ^ 4))
      linarith
    have h1 : ‖(1 : ℂ) - (Z00 τ + (2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2‖ ≤ 1 + (1 / 2 + 1 / 4) / 2 := by
      have h := norm_sub_le (1 : ℂ) ((Z00 τ + (2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2)
      rw [norm_one] at h
      have h3 : ‖(Z00 τ + (2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2‖ ≤ (1 / 2 + 1 / 4) / 2 := by
        rw [norm_div, Complex.norm_ofNat]; linarith
      linarith
    have h2 : ‖(Z00 τ ^ 2 + Z00 τ * (2 * Ept τ + 2 * (Ept τ) ^ 4)
        + (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3‖ ≤ (1 / 4 + 1 / 8 + 1 / 16) / 3 := by
      rw [norm_div, Complex.norm_ofNat]; linarith
    have h := norm_add_le ((1 : ℂ) - (Z00 τ + (2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2)
      ((Z00 τ ^ 2 + Z00 τ * (2 * Ept τ + 2 * (Ept τ) ^ 4)
          + (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3)
    have hB00 : B00 τ = (1 : ℂ) - (Z00 τ + (2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2
      + (Z00 τ ^ 2 + Z00 τ * (2 * Ept τ + 2 * (Ept τ) ^ 4)
          + (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3 := rfl
    rw [hB00]
    linarith
  have hQ : IsSm 4 (fun τ => theta00Rem τ * B00 τ) := by
    have hm := IsSm.mul isSm_theta00Rem hBdd
    exact IsSm.mono hm (by norm_num)
  -- the polynomial part
  have hP : IsSm 4 (fun τ => (2 * Ept τ + 2 * (Ept τ) ^ 4)
      - (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2 / 2 + (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3 / 3
      - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3)) := by
    have hcore : IsSm 0 (fun τ => 2 - 4 * Ept τ + 8 * (Ept τ) ^ 2 - 2 * (Ept τ) ^ 4
        + 8 * (Ept τ) ^ 5 + (8 / 3 : ℂ) * (Ept τ) ^ 8) := by
      have h1 : IsSm 0 (fun τ => (2 : ℂ) * (Ept τ) ^ 0) := isSm_Epow 2 0
      have h2 : IsSm 0 (fun τ => (-4 : ℂ) * (Ept τ) ^ 1) := IsSm.mono (isSm_Epow (-4) 1) (by norm_num)
      have h3 : IsSm 0 (fun τ => (8 : ℂ) * (Ept τ) ^ 2) := IsSm.mono (isSm_Epow 8 2) (by norm_num)
      have h4 : IsSm 0 (fun τ => (-2 : ℂ) * (Ept τ) ^ 4) := IsSm.mono (isSm_Epow (-2) 4) (by norm_num)
      have h5 : IsSm 0 (fun τ => (8 : ℂ) * (Ept τ) ^ 5) := IsSm.mono (isSm_Epow 8 5) (by norm_num)
      have h6 : IsSm 0 (fun τ => (8 / 3 : ℂ) * (Ept τ) ^ 8) := IsSm.mono (isSm_Epow (8/3) 8) (by norm_num)
      have h12 := IsSm.add h1 h2
      have hmin : min 0 0 = 0 := by norm_num
      rw [hmin] at h12
      have h34 := IsSm.add h3 h4
      rw [hmin] at h34
      have h56 := IsSm.add h5 h6
      rw [hmin] at h56
      have h1234 := IsSm.add h12 h34
      rw [hmin] at h1234
      have hall := IsSm.add h1234 h56
      rw [hmin] at hall
      exact IsSm.congr hall (fun τ => by ring)
    have hm := IsSm.mul (isSm_Epow (1 : ℂ) 4) hcore
    refine IsSm.congr_on hm (fun τ _ => ?_)
    ring
  -- assembling
  have hsplit : ∀ τ : ℍ, (Z00 τ - Z00 τ ^ 2 / 2 + Z00 τ ^ 3 / 3)
      - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3)
      = ((2 * Ept τ + 2 * (Ept τ) ^ 4) - (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2 / 2
          + (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3 / 3
          - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3))
        + theta00Rem τ * B00 τ := by
    intro τ
    have hZ : Z00 τ = 2 * Ept τ + 2 * (Ept τ) ^ 4 + theta00Rem τ := rfl
    have hB : B00 τ = (1 : ℂ) - (Z00 τ + (2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2
        + (Z00 τ ^ 2 + Z00 τ * (2 * Ept τ + 2 * (Ept τ) ^ 4)
            + (2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3 := rfl
    rw [hB, hZ]
    ring
  have halg : IsSm 4 (fun τ => (Z00 τ - Z00 τ ^ 2 / 2 + Z00 τ ^ 3 / 3)
      - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3)) := by
    have h := IsSm.add hP hQ
    have hmin : min 4 4 = 4 := by norm_num
    rw [hmin] at h
    refine IsSm.congr h (fun τ => ?_)
    exact (hsplit τ).symm
  have hpoint : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      (Complex.log (1 + Z00 τ) - (Z00 τ - Z00 τ ^ 2 / 2 + Z00 τ ^ 3 / 3))
        + ((Z00 τ - Z00 τ ^ 2 / 2 + Z00 τ ^ 3 / 3)
          - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3))
      = Complex.log (Work.Kernels.theta00Fun τ)
        - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3) := by
    intro τ _
    have hθ : Work.Kernels.theta00Fun τ = 1 + Z00 τ := by
      simp only [Z00, theta00Rem]; ring
    rw [hθ]
    ring
  have hmain := IsSm.add hR halg
  have hmin : min 4 4 = 4 := by norm_num
  rw [hmin] at hmain
  exact IsSm.congr_on hmain hpoint

/-- **The logarithmic expansion of `θ₀₁`**: `log θ₀₁ = -2E - 2E² - (8/3)E³ + O(‖E‖⁴)`. -/
theorem isSm_log_theta01 : IsSm 4 (fun τ => Complex.log (Work.Kernels.theta01Fun τ)
    - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3)) := by
  have hR : IsSm 4 (fun τ => Complex.log (1 + Z01 τ)
      - (Z01 τ - Z01 τ ^ 2 / 2 + Z01 τ ^ 3 / 3)) := by
    refine ⟨8193, by norm_num, fun τ hτ => ?_⟩
    have h := log_taylor3 (Z01 τ) (Z01_half τ hτ)
    have hz : ‖Z01 τ‖ ≤ 8 * ‖Ept τ‖ := Z01_le τ hτ
    have h4 : ‖Z01 τ‖ ^ 4 ≤ (8 * ‖Ept τ‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hz 4
    have he0 : (0 : ℝ) ≤ ‖Ept τ‖ ^ 4 := by positivity
    calc ‖Complex.log (1 + Z01 τ) - (Z01 τ - Z01 τ ^ 2 / 2 + Z01 τ ^ 3 / 3)‖
        ≤ 2 * ‖Z01 τ‖ ^ 4 := h
      _ ≤ 2 * (8 * ‖Ept τ‖) ^ 4 := by linarith
      _ = 8192 * ‖Ept τ‖ ^ 4 := by ring
      _ ≤ 8193 * ‖Ept τ‖ ^ 4 := by linarith [he0]
  have isSm_z0 : IsSm 0 (fun τ => -2 * Ept τ + 2 * (Ept τ) ^ 4) := isSm_Z01_lead
  have hBdd : IsSm 0 B01 := by
    refine IsSm.bdd (B := 2) (by norm_num) (fun τ hτ => ?_)
    have hz : ‖Z01 τ‖ ≤ 1 / 2 := Z01_half τ hτ
    have hz0 : ‖-2 * Ept τ + 2 * (Ept τ) ^ 4‖ ≤ 1 / 4 := Z01_lead_le τ hτ
    have hsum : ‖Z01 τ + (-2 * Ept τ + 2 * (Ept τ) ^ 4)‖ ≤ 1 / 2 + 1 / 4 :=
      le_trans (norm_add_le _ _) (add_le_add hz hz0)
    have hs2 : ‖Z01 τ ^ 2 + Z01 τ * (-2 * Ept τ + 2 * (Ept τ) ^ 4)
        + (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2‖ ≤ 1 / 4 + 1 / 8 + 1 / 16 := by
      have hA : ‖Z01 τ ^ 2‖ ≤ 1 / 4 := by rw [norm_pow]; nlinarith [hz, norm_nonneg (Z01 τ)]
      have hB : ‖Z01 τ * (-2 * Ept τ + 2 * (Ept τ) ^ 4)‖ ≤ 1 / 8 := by
        rw [norm_mul]
        nlinarith [hz, hz0, norm_nonneg (Z01 τ), norm_nonneg (-2 * Ept τ + 2 * (Ept τ) ^ 4)]
      have hC : ‖(-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2‖ ≤ 1 / 16 := by
        rw [norm_pow]; nlinarith [hz0, norm_nonneg (-2 * Ept τ + 2 * (Ept τ) ^ 4)]
      have h1 := norm_add_le (Z01 τ ^ 2 + Z01 τ * (-2 * Ept τ + 2 * (Ept τ) ^ 4))
        ((-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2)
      have h0 := norm_add_le (Z01 τ ^ 2) (Z01 τ * (-2 * Ept τ + 2 * (Ept τ) ^ 4))
      linarith
    have h1 : ‖(1 : ℂ) - (Z01 τ + (-2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2‖ ≤ 1 + (1 / 2 + 1 / 4) / 2 := by
      have h := norm_sub_le (1 : ℂ) ((Z01 τ + (-2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2)
      rw [norm_one] at h
      have h3 : ‖(Z01 τ + (-2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2‖ ≤ (1 / 2 + 1 / 4) / 2 := by
        rw [norm_div, Complex.norm_ofNat]; linarith
      linarith
    have h2 : ‖(Z01 τ ^ 2 + Z01 τ * (-2 * Ept τ + 2 * (Ept τ) ^ 4)
        + (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3‖ ≤ (1 / 4 + 1 / 8 + 1 / 16) / 3 := by
      rw [norm_div, Complex.norm_ofNat]; linarith
    have h := norm_add_le ((1 : ℂ) - (Z01 τ + (-2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2)
      ((Z01 τ ^ 2 + Z01 τ * (-2 * Ept τ + 2 * (Ept τ) ^ 4)
          + (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3)
    have hB01 : B01 τ = (1 : ℂ) - (Z01 τ + (-2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2
      + (Z01 τ ^ 2 + Z01 τ * (-2 * Ept τ + 2 * (Ept τ) ^ 4)
          + (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3 := rfl
    rw [hB01]
    linarith
  have hQ : IsSm 4 (fun τ => theta01Rem τ * B01 τ) := by
    have hm := IsSm.mul isSm_theta01Rem hBdd
    exact IsSm.mono hm (by norm_num)
  have hP : IsSm 4 (fun τ => (-2 * Ept τ + 2 * (Ept τ) ^ 4)
      - (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2 / 2 + (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3 / 3
      - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3)) := by
    have hcore : IsSm 0 (fun τ => 2 + 4 * Ept τ + 8 * (Ept τ) ^ 2 - 2 * (Ept τ) ^ 4
        - 8 * (Ept τ) ^ 5 + (8 / 3 : ℂ) * (Ept τ) ^ 8) := by
      have h1 : IsSm 0 (fun τ => (2 : ℂ) * (Ept τ) ^ 0) := isSm_Epow 2 0
      have h2 : IsSm 0 (fun τ => (4 : ℂ) * (Ept τ) ^ 1) := IsSm.mono (isSm_Epow 4 1) (by norm_num)
      have h3 : IsSm 0 (fun τ => (8 : ℂ) * (Ept τ) ^ 2) := IsSm.mono (isSm_Epow 8 2) (by norm_num)
      have h4 : IsSm 0 (fun τ => (-2 : ℂ) * (Ept τ) ^ 4) := IsSm.mono (isSm_Epow (-2) 4) (by norm_num)
      have h5 : IsSm 0 (fun τ => (-8 : ℂ) * (Ept τ) ^ 5) := IsSm.mono (isSm_Epow (-8) 5) (by norm_num)
      have h6 : IsSm 0 (fun τ => (8 / 3 : ℂ) * (Ept τ) ^ 8) := IsSm.mono (isSm_Epow (8/3) 8) (by norm_num)
      have h12 := IsSm.add h1 h2
      have hmin : min 0 0 = 0 := by norm_num
      rw [hmin] at h12
      have h34 := IsSm.add h3 h4
      rw [hmin] at h34
      have h56 := IsSm.add h5 h6
      rw [hmin] at h56
      have h1234 := IsSm.add h12 h34
      rw [hmin] at h1234
      have hall := IsSm.add h1234 h56
      rw [hmin] at hall
      exact IsSm.congr hall (fun τ => by ring)
    have hm := IsSm.mul (isSm_Epow (1 : ℂ) 4) hcore
    refine IsSm.congr_on hm (fun τ _ => ?_)
    ring
  have hsplit : ∀ τ : ℍ, (Z01 τ - Z01 τ ^ 2 / 2 + Z01 τ ^ 3 / 3)
      - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3)
      = ((-2 * Ept τ + 2 * (Ept τ) ^ 4) - (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2 / 2
          + (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 3 / 3
          - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3))
        + theta01Rem τ * B01 τ := by
    intro τ
    have hZ : Z01 τ = -2 * Ept τ + 2 * (Ept τ) ^ 4 + theta01Rem τ := rfl
    have hB : B01 τ = (1 : ℂ) - (Z01 τ + (-2 * Ept τ + 2 * (Ept τ) ^ 4)) / 2
        + (Z01 τ ^ 2 + Z01 τ * (-2 * Ept τ + 2 * (Ept τ) ^ 4)
            + (-2 * Ept τ + 2 * (Ept τ) ^ 4) ^ 2) / 3 := rfl
    rw [hB, hZ]
    ring
  have halg : IsSm 4 (fun τ => (Z01 τ - Z01 τ ^ 2 / 2 + Z01 τ ^ 3 / 3)
      - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3)) := by
    have h := IsSm.add hP hQ
    have hmin : min 4 4 = 4 := by norm_num
    rw [hmin] at h
    refine IsSm.congr h (fun τ => ?_)
    exact (hsplit τ).symm
  have hpoint : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      (Complex.log (1 + Z01 τ) - (Z01 τ - Z01 τ ^ 2 / 2 + Z01 τ ^ 3 / 3))
        + ((Z01 τ - Z01 τ ^ 2 / 2 + Z01 τ ^ 3 / 3)
          - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3))
      = Complex.log (Work.Kernels.theta01Fun τ)
        - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3) := by
    intro τ _
    have hθ : Work.Kernels.theta01Fun τ = 1 + Z01 τ := by
      simp only [Z01, theta01Rem]; ring
    rw [hθ]
    ring
  have hmain := IsSm.add hR halg
  have hmin : min 4 4 = 4 := by norm_num
  rw [hmin] at hmain
  exact IsSm.congr_on hmain hpoint


/-! ## The expansion of `𝓛_S` -/

private lemma inv_one_add_rem (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖(1 + u)⁻¹ - (1 - u + u ^ 2 - u ^ 3)‖ ≤ 2 * ‖u‖ ^ 4 := by
  have h1u : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) + u‖ := by
    have h := abs_norm_sub_norm_le (1 : ℂ) (-u)
    rw [norm_one, norm_neg] at h
    have h2 : (1 : ℂ) - (-u) = 1 + u := by ring
    rw [h2] at h
    have h3 := (abs_le.mp h).2
    linarith
  have hne : (1 : ℂ) + u ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1u
    norm_num at h1u
  have hfac : (1 + u)⁻¹ - (1 - u + u ^ 2 - u ^ 3) = u ^ 4 * (1 + u)⁻¹ := by
    field_simp
    ring
  rw [hfac, norm_mul, norm_pow]
  have hinv : ‖(1 + u)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc (‖(1 : ℂ) + u‖)⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num) h1u
      _ = 2 := by norm_num
  have h0 : (0 : ℝ) ≤ ‖u‖ ^ 4 := by positivity
  nlinarith [hinv, h0]

/-- `𝓛_S = -16E - (64/3)E³ + O(‖E‖⁴)`. -/
theorem isSm_LS (ℓ : Work.Kernels.LogLambdaData) :
    IsSm 4 (fun τ => ℓ.L_S τ + 16 * Ept τ + (64 / 3 : ℂ) * (Ept τ) ^ 3) := by
  have hlog0 : IsSm 4 (fun τ => Complex.log (Work.Kernels.theta00Fun τ)
      - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3)) := isSm_log_theta00
  have hlog1 : IsSm 4 (fun τ => Complex.log (Work.Kernels.theta01Fun τ)
      - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3)) := isSm_log_theta01
  -- the combination is `4 log θ₀₁ - 4 log θ₀₀`
  have hbody : IsSm 4 (fun τ => 4 * (Complex.log (Work.Kernels.theta01Fun τ)
        - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3))
      - 4 * (Complex.log (Work.Kernels.theta00Fun τ)
        - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3))) := by
    have h1 := IsSm.const_mul (4 : ℂ) hlog1
    have h2 := IsSm.const_mul (-4 : ℂ) hlog0
    have h := IsSm.add h1 h2
    have hmin : min 4 4 = 4 := by norm_num
    rw [hmin] at h
    exact IsSm.congr h (fun τ => by ring)
  have hpoint : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      (4 * (Complex.log (Work.Kernels.theta01Fun τ)
          - (-2 * Ept τ - 2 * (Ept τ) ^ 2 - (8 / 3 : ℂ) * (Ept τ) ^ 3))
        - 4 * (Complex.log (Work.Kernels.theta00Fun τ)
          - (2 * Ept τ - 2 * (Ept τ) ^ 2 + (8 / 3 : ℂ) * (Ept τ) ^ 3)))
      = ℓ.L_S τ + 16 * Ept τ + (64 / 3 : ℂ) * (Ept τ) ^ 3 := by
    intro τ hτ
    have hhalf : (1 / 2 : ℝ) < τ.im := by
      have := Work.Asymptotics.Funnel.im_two hτ
      linarith
    rw [Work.Residues.LogLambdaData_LS_eq_LamS ℓ τ hhalf]
    simp only [Work.Kernels.LogLambda.LamS, Work.Kernels.LogLambda.thetaC01,
      Work.Kernels.LogLambda.thetaC00, Work.Kernels.theta01Fun, Work.Kernels.theta00Fun]
    ring
  exact IsSm.congr_on hbody hpoint

/-! ## The expansion of `𝓛` (equivalently of `ρ = 𝓛 - πiτ - c`) -/

/-- The ratio `V/(16 E U) = λ/(16E)`, whose principal logarithm is `𝓛 - πiτ - c`. -/
noncomputable def wRatio (τ : ℍ) : ℂ :=
  Work.Kernels.VFun τ / (16 * Ept τ * Work.Kernels.UFun τ)

theorem isSm_U1 : IsSm 4 (fun τ => Work.Kernels.UFun τ - 1 - 8 * Ept τ - 24 * (Ept τ) ^ 2
    - 32 * (Ept τ) ^ 3) := by
  have h5 := IsSm.mono Ufun_exp5 (show 4 ≤ 5 by norm_num)
  have h24 : IsSm 4 (fun τ => (24 : ℂ) * (Ept τ) ^ 4) := isSm_Epow 24 4
  have h := IsSm.add h5 h24
  have hmin : min 4 4 = 4 := by norm_num
  rw [hmin] at h
  exact IsSm.congr h (fun τ => by ring)

theorem isSm_Vdiv : IsSm 4 (fun τ => (Work.Kernels.VFun τ - 16 * Ept τ - 64 * (Ept τ) ^ 3)
    / (16 * Ept τ)) := by
  have hV := Vfun_exp5
  obtain ⟨C, hC, hVb⟩ := hV
  refine ⟨C / 16, by positivity, fun τ hτ => ?_⟩
  have he : 0 < ‖Ept τ‖ := by rw [norm_Ept]; positivity
  have h1 : ‖Work.Kernels.VFun τ - 16 * Ept τ - 64 * (Ept τ) ^ 3‖ ≤ C * ‖Ept τ‖ ^ 5 := hVb τ hτ
  have h2 : ‖(16 : ℂ) * Ept τ‖ = 16 * ‖Ept τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  rw [norm_div, h2, div_le_iff₀ (by positivity)]
  calc ‖Work.Kernels.VFun τ - 16 * Ept τ - 64 * (Ept τ) ^ 3‖
      ≤ C * ‖Ept τ‖ ^ 5 := h1
    _ = (C / 16) * ‖Ept τ‖ ^ 4 * (16 * ‖Ept τ‖) := by ring

noncomputable def U1f (τ : ℍ) : ℂ := Work.Kernels.UFun τ - 1

noncomputable def U0t (τ : ℍ) : ℂ := 8 * Ept τ + 24 * (Ept τ) ^ 2 + 32 * (Ept τ) ^ 3

noncomputable def G1f (τ : ℍ) : ℂ := 1 - U1f τ + (U1f τ) ^ 2 - (U1f τ) ^ 3

noncomputable def GTf (τ : ℍ) : ℂ := 1 - U0t τ + (U0t τ) ^ 2 - (U0t τ) ^ 3

noncomputable def VCf (τ : ℍ) : ℂ :=
  (Work.Kernels.VFun τ - 16 * Ept τ - 64 * (Ept τ) ^ 3) / (16 * Ept τ)

theorem isSm_VCf : IsSm 4 VCf := isSm_Vdiv

theorem isSm_Vdiv' : IsSm 4 (fun τ => (Work.Kernels.VFun τ - 16 * Ept τ - 64 * (Ept τ) ^ 3)
    / (16 * Ept τ)) := isSm_Vdiv

theorem isSm_U0t : IsSm 1 U0t := by
  have h1 : IsSm 1 (fun τ => (8 : ℂ) * Ept τ) := by simpa using isSm_Epow (8 : ℂ) 1
  have h2 : IsSm 2 (fun τ => (24 : ℂ) * (Ept τ) ^ 2) := isSm_Epow 24 2
  have h3 : IsSm 3 (fun τ => (32 : ℂ) * (Ept τ) ^ 3) := isSm_Epow 32 3
  have h12 := IsSm.add h1 (IsSm.mono h2 (show 1 ≤ 2 by norm_num))
  have hmin : min 1 1 = 1 := by norm_num
  rw [hmin] at h12
  have h123 := IsSm.add h12 (IsSm.mono h3 (show 1 ≤ 3 by norm_num))
  rw [hmin] at h123
  exact IsSm.congr h123 (fun τ => by simp only [U0t]; try ring)

theorem isSm_U1f : IsSm 1 U1f := by
  have hu1 : IsSm 1 (fun τ => Work.Kernels.UFun τ - 1 - 8 * Ept τ - 24 * (Ept τ) ^ 2
      - 32 * (Ept τ) ^ 3) := IsSm.mono isSm_U1 (show 1 ≤ 4 by norm_num)
  have h := IsSm.add hu1 isSm_U0t
  have hmin : min 1 1 = 1 := by norm_num
  rw [hmin] at h
  refine IsSm.congr h (fun τ => ?_)
  simp only [U1f, U0t]
  try ring

theorem isSm_G1f_sub_GTf : IsSm 4 (fun τ => G1f τ - GTf τ) := by
  have hA : IsSm 4 (fun τ => U1f τ - U0t τ) := by
    have h := IsSm.mono isSm_U1 (show 4 ≤ 4 by norm_num)
    refine IsSm.congr h (fun τ => ?_)
    simp only [U1f, U0t]
    ring
  have hsum : IsSm 1 (fun τ => U1f τ + U0t τ) := by
    have h := IsSm.add isSm_U1f isSm_U0t
    have hmin : min 1 1 = 1 := by norm_num
    rw [hmin] at h
    exact h
  have hsum2 : IsSm 0 (fun τ => (U1f τ) ^ 2 + U1f τ * U0t τ + (U0t τ) ^ 2) := by
    have h1 : IsSm 0 (fun τ => (U1f τ) ^ 2) := IsSm.mono (IsSm.pow isSm_U1f 2) (by norm_num)
    have h2 : IsSm 0 (fun τ => U1f τ * U0t τ) :=
      IsSm.mono (IsSm.mul isSm_U1f isSm_U0t) (by norm_num)
    have h3 : IsSm 0 (fun τ => (U0t τ) ^ 2) := IsSm.mono (IsSm.pow isSm_U0t 2) (by norm_num)
    have h12 := IsSm.add h1 h2
    have hmin : min 0 0 = 0 := by norm_num
    rw [hmin] at h12
    have hall := IsSm.add h12 h3
    rw [hmin] at hall
    exact hall
  have hB : IsSm 4 (fun τ => (U1f τ) ^ 2 - (U0t τ) ^ 2) := by
    have hm := IsSm.mul hA hsum
    have heq : (fun τ => (U1f τ) ^ 2 - (U0t τ) ^ 2)
        = (fun τ => (U1f τ - U0t τ) * (U1f τ + U0t τ)) := by
      funext τ; ring
    rw [heq]
    exact IsSm.mono hm (by norm_num)
  have hC : IsSm 4 (fun τ => (U1f τ) ^ 3 - (U0t τ) ^ 3) := by
    have hm := IsSm.mul hA hsum2
    have heq : (fun τ => (U1f τ) ^ 3 - (U0t τ) ^ 3)
        = (fun τ => (U1f τ - U0t τ) * ((U1f τ) ^ 2 + U1f τ * U0t τ + (U0t τ) ^ 2)) := by
      funext τ; ring
    rw [heq]
    exact IsSm.mono hm (by norm_num)
  have h := IsSm.add (IsSm.add (IsSm.neg hA) hB) (IsSm.neg hC)
  have hmin : min (min 4 4) 4 = 4 := by norm_num
  rw [hmin] at h
  refine IsSm.congr h (fun τ => ?_)
  simp only [G1f, GTf, U1f, U0t]
  ring

theorem isSm_GTf : IsSm 0 GTf := by
  have h1 : IsSm 0 (fun τ => (1 : ℂ)) := IsSm.one
  have h2 : IsSm 0 (fun τ => -U0t τ) := IsSm.mono (IsSm.neg isSm_U0t) (show 0 ≤ 1 by norm_num)
  have h3 : IsSm 0 (fun τ => (U0t τ) ^ 2) := IsSm.mono (IsSm.pow isSm_U0t 2) (by norm_num)
  have h4 : IsSm 0 (fun τ => -(U0t τ) ^ 3) := IsSm.mono (IsSm.neg (IsSm.pow isSm_U0t 3)) (by norm_num)
  have h12 := IsSm.add h1 h2
  have hmin : min 0 0 = 0 := by norm_num
  rw [hmin] at h12
  have h123 := IsSm.add h12 h3
  rw [hmin] at h123
  have hall := IsSm.add h123 h4
  rw [hmin] at hall
  exact IsSm.congr hall (fun τ => by simp only [GTf, U0t]; ring)

theorem isSm_wRatio : IsSm 4 (fun τ => wRatio τ - 1 + 8 * Ept τ - 44 * (Ept τ) ^ 2
    + 192 * (Ept τ) ^ 3) := by
  -- the polynomial part
  have hpoly : IsSm 4 (fun τ => (1 + 4 * (Ept τ) ^ 2) * GTf τ
      - (1 - 8 * Ept τ + 44 * (Ept τ) ^ 2 - 192 * (Ept τ) ^ 3)) := by
    have hcore : IsSm 4 (fun τ => (-3360 : ℂ) * (Ept τ) ^ 4 - 19072 * (Ept τ) ^ 5
        - 63744 * (Ept τ) ^ 6 - 153600 * (Ept τ) ^ 7 - 272384 * (Ept τ) ^ 8
        - 352256 * (Ept τ) ^ 9 - 294912 * (Ept τ) ^ 10 - 131072 * (Ept τ) ^ 11) := by
      have h1 : IsSm 4 (fun τ => (-3360 : ℂ) * (Ept τ) ^ 4) := isSm_Epow (-3360) 4
      have h2 : IsSm 4 (fun τ => (-19072 : ℂ) * (Ept τ) ^ 5) :=
        IsSm.mono (isSm_Epow (-19072) 5) (by norm_num)
      have h3 : IsSm 4 (fun τ => (-63744 : ℂ) * (Ept τ) ^ 6) :=
        IsSm.mono (isSm_Epow (-63744) 6) (by norm_num)
      have h4 : IsSm 4 (fun τ => (-153600 : ℂ) * (Ept τ) ^ 7) :=
        IsSm.mono (isSm_Epow (-153600) 7) (by norm_num)
      have h5 : IsSm 4 (fun τ => (-272384 : ℂ) * (Ept τ) ^ 8) :=
        IsSm.mono (isSm_Epow (-272384) 8) (by norm_num)
      have h6 : IsSm 4 (fun τ => (-352256 : ℂ) * (Ept τ) ^ 9) :=
        IsSm.mono (isSm_Epow (-352256) 9) (by norm_num)
      have h7 : IsSm 4 (fun τ => (-294912 : ℂ) * (Ept τ) ^ 10) :=
        IsSm.mono (isSm_Epow (-294912) 10) (by norm_num)
      have h8 : IsSm 4 (fun τ => (-131072 : ℂ) * (Ept τ) ^ 11) :=
        IsSm.mono (isSm_Epow (-131072) 11) (by norm_num)
      have h12 := IsSm.add h1 h2
      have h34 := IsSm.add h3 h4
      have h56 := IsSm.add h5 h6
      have h78 := IsSm.add h7 h8
      have ha := IsSm.add h12 h34
      have hb := IsSm.add h56 h78
      have hall := IsSm.add ha hb
      have hmin : min (min 4 4) (min 4 4) = 4 := by norm_num
      rw [hmin] at hall
      exact IsSm.congr hall (fun τ => by ring)
    refine IsSm.congr_on hcore (fun τ _ => ?_)
    simp only [GTf, U0t]
    ring
  -- multiplication by `1 + 4E²`
  have hb4 : IsSm 0 (fun τ => 1 + 4 * (Ept τ) ^ 2) := by
    have h1 : IsSm 0 (fun τ => (1 : ℂ)) := IsSm.one
    have h2 : IsSm 0 (fun τ => (4 : ℂ) * (Ept τ) ^ 2) :=
      IsSm.mono (isSm_Epow 4 2) (by norm_num)
    have h := IsSm.add h1 h2
    have hmin : min 0 0 = 0 := by norm_num
    rw [hmin] at h
    exact IsSm.congr h (fun τ => by ring)
  have hcast : IsSm 4 (fun τ => (1 + 4 * (Ept τ) ^ 2) * (G1f τ - GTf τ)) := by
    have hm := IsSm.mul hb4 isSm_G1f_sub_GTf
    exact IsSm.mono hm (by norm_num)
  have hpoly' : IsSm 4 (fun τ => (1 + 4 * (Ept τ) ^ 2) * G1f τ
      - (1 - 8 * Ept τ + 44 * (Ept τ) ^ 2 - 192 * (Ept τ) ^ 3)) := by
    have h := IsSm.add hpoly hcast
    have hmin : min 4 4 = 4 := by norm_num
    rw [hmin] at h
    refine IsSm.congr h (fun τ => ?_)
    ring
  -- the `V`-correction times `G1f`
  have hG1bdd : IsSm 0 G1f := by
    have h1 : IsSm 0 (fun τ => (1 : ℂ)) := IsSm.one
    have h2 : IsSm 0 (fun τ => -U1f τ) :=
      IsSm.mono (IsSm.neg isSm_U1f) (show 0 ≤ 1 by norm_num)
    have h3 : IsSm 0 (fun τ => (U1f τ) ^ 2) := IsSm.mono (IsSm.pow isSm_U1f 2) (by norm_num)
    have h4 : IsSm 0 (fun τ => -(U1f τ) ^ 3) :=
      IsSm.mono (IsSm.neg (IsSm.pow isSm_U1f 3)) (by norm_num)
    have h12 := IsSm.add h1 h2
    have hmin : min 0 0 = 0 := by norm_num
    rw [hmin] at h12
    have h123 := IsSm.add h12 h3
    rw [hmin] at h123
    have hall := IsSm.add h123 h4
    rw [hmin] at hall
    exact IsSm.congr hall (fun τ => by simp only [G1f, U1f]; ring_nf)
  have hsV1 : IsSm 4 (fun τ => VCf τ * G1f τ) := by
    have hm := IsSm.mul isSm_VCf hG1bdd
    exact IsSm.mono hm (by norm_num)
  -- the remainder times the factor
  have hrem : IsSm 4 (fun τ => ((1 : ℂ) + U1f τ)⁻¹
      - (1 - U1f τ + (U1f τ) ^ 2 - (U1f τ) ^ 3)) := by
    refine ⟨2 * 41 ^ 4 + 1, by norm_num, fun τ hτ => ?_⟩
    have hu2 : ‖U1f τ‖ ≤ 1 / 2 := by
      have h := Usub1_le_e τ hτ
      have he : ‖Ept τ‖ ≤ 1 / 256 := e_le_inv_256 τ hτ
      have heq : U1f τ = Work.Kernels.UFun τ - 1 := rfl
      rw [heq]
      linarith
    have h := inv_one_add_rem (U1f τ) hu2
    have huK : ‖U1f τ‖ ≤ 41 * ‖Ept τ‖ := by
      have h := Usub1_le_e τ hτ
      have heq : U1f τ = Work.Kernels.UFun τ - 1 := rfl
      rw [heq]
      exact h
    have h4 : ‖U1f τ‖ ^ 4 ≤ (41 * ‖Ept τ‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) huK 4
    calc ‖((1 : ℂ) + U1f τ)⁻¹ - (1 - U1f τ + (U1f τ) ^ 2 - (U1f τ) ^ 3)‖
        ≤ 2 * ‖U1f τ‖ ^ 4 := h
      _ ≤ 2 * (41 * ‖Ept τ‖) ^ 4 := by linarith
      _ = 2 * 41 ^ 4 * ‖Ept τ‖ ^ 4 := by ring
      _ ≤ (2 * 41 ^ 4 + 1) * ‖Ept τ‖ ^ 4 := by
          have h0 : (0:ℝ) ≤ ‖Ept τ‖ ^ 4 := by positivity
          nlinarith
  have hrem' : IsSm 4 (fun τ => (1 + 4 * (Ept τ) ^ 2 + VCf τ) * (((1 : ℂ) + U1f τ)⁻¹
      - (1 - U1f τ + (U1f τ) ^ 2 - (U1f τ) ^ 3))) := by
    have hVb : IsSm 0 VCf := IsSm.mono isSm_VCf (by norm_num)
    have hsum : IsSm 0 (fun τ => 1 + 4 * (Ept τ) ^ 2 + VCf τ) := by
      have h := IsSm.add hb4 hVb
      have hmin : min 0 0 = 0 := by norm_num
      rw [hmin] at h
      exact h
    have hm := IsSm.mul hsum hrem
    exact IsSm.mono hm (by norm_num)
  -- assemble
  have hpoint : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ((1 + 4 * (Ept τ) ^ 2) * G1f τ
          - (1 - 8 * Ept τ + 44 * (Ept τ) ^ 2 - 192 * (Ept τ) ^ 3))
        + VCf τ * G1f τ
        + (1 + 4 * (Ept τ) ^ 2 + VCf τ) * (((1 : ℂ) + U1f τ)⁻¹
          - (1 - U1f τ + (U1f τ) ^ 2 - (U1f τ) ^ 3))
      = wRatio τ - 1 + 8 * Ept τ - 44 * (Ept τ) ^ 2 + 192 * (Ept τ) ^ 3 := by
    intro τ _
    have hw : wRatio τ = (1 + 4 * (Ept τ) ^ 2 + VCf τ) * ((1 : ℂ) + U1f τ)⁻¹ := by
      have hnum : (1 + 4 * (Ept τ) ^ 2 + VCf τ) = Work.Kernels.VFun τ / (16 * Ept τ) := by
        simp only [VCf]
        field_simp
        ring
      have hden : (1 : ℂ) + U1f τ = Work.Kernels.UFun τ := by
        simp only [U1f]; ring
      rw [hnum, hden, wRatio]
      ring
    rw [hw]
    simp only [G1f]
    ring
  have hmain : IsSm 4 (fun τ => ((1 + 4 * (Ept τ) ^ 2) * G1f τ
          - (1 - 8 * Ept τ + 44 * (Ept τ) ^ 2 - 192 * (Ept τ) ^ 3))
        + VCf τ * G1f τ
        + (1 + 4 * (Ept τ) ^ 2 + VCf τ) * (((1 : ℂ) + U1f τ)⁻¹
          - (1 - U1f τ + (U1f τ) ^ 2 - (U1f τ) ^ 3))) := by
    have h1 := IsSm.add hpoly' hsV1
    have hmin : min 4 4 = 4 := by norm_num
    rw [hmin] at h1
    have h2 := IsSm.add h1 hrem'
    rw [hmin] at h2
    exact h2
  exact IsSm.congr_on hmain hpoint


end

end Work.Asymptotics.KhatE1
