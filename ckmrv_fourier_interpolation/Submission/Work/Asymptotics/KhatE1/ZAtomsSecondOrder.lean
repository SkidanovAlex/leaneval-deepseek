import Mathlib
import Submission.Work.Asymptotics.Compact.zsmall
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Asymptotics.funnel_tauAtom_second_order
import Submission.Work.Asymptotics.KhatE1.KdevE2Expansions
import Submission.Work.Kernels.TildeFacts.theta_quartic

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Residues

noncomputable section

/-- `IsSmH k f`: `f = O(‖Ept z‖ᵏ)` on the half-plane `{z : 1 ≤ Im z}`. -/
def IsSmH (k : ℕ) (f : ℍ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * ‖Ept z‖ ^ k

namespace IsSmH

variable {k l : ℕ} {f g : ℍ → ℂ}

theorem mono (h : IsSmH k f) (hl : l ≤ k) : IsSmH l f := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, fun z hz => ?_⟩
  have h1 : ‖Ept z‖ ≤ 1 := le_of_lt (norm_Ept_lt_one z)
  have h2 : ‖Ept z‖ ^ k ≤ ‖Ept z‖ ^ l :=
    pow_le_pow_of_le_one (norm_nonneg _) h1 hl
  exact le_trans (hf z hz) (mul_le_mul_of_nonneg_left h2 hC.le)

theorem bdd {B : ℝ} (hB : 0 < B) (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ B) : IsSmH 0 f :=
  ⟨B, hB, fun z hz => by simpa using h z hz⟩

theorem congr (h : IsSmH k f) (hfg : ∀ z, f z = g z) : IsSmH k g := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun z hz => by rw [← hfg z]; exact hf z hz⟩

theorem neg (h : IsSmH k f) : IsSmH k (fun z => -f z) := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun z hz => by simpa using hf z hz⟩

theorem const_mul (c : ℂ) (h : IsSmH k f) : IsSmH k (fun z => c * f z) := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨‖c‖ * C + 1, by positivity, fun z hz => ?_⟩
  have h1 := hf z hz
  have h2 : (0 : ℝ) ≤ ‖Ept z‖ ^ k := by positivity
  rw [norm_mul]
  calc ‖c‖ * ‖f z‖ ≤ ‖c‖ * (C * ‖Ept z‖ ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (‖c‖ * C) * ‖Ept z‖ ^ k := by ring
    _ ≤ (‖c‖ * C + 1) * ‖Ept z‖ ^ k := by nlinarith [h2]

theorem add (hf : IsSmH k f) (hg : IsSmH l g) : IsSmH (min k l) (fun z => f z + g z) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, by positivity, fun z hz => ?_⟩
  have h1 : ‖Ept z‖ ≤ 1 := le_of_lt (norm_Ept_lt_one z)
  have hk : ‖Ept z‖ ^ k ≤ ‖Ept z‖ ^ min k l :=
    pow_le_pow_of_le_one (norm_nonneg _) h1 (min_le_left _ _)
  have hl : ‖Ept z‖ ^ l ≤ ‖Ept z‖ ^ min k l :=
    pow_le_pow_of_le_one (norm_nonneg _) h1 (min_le_right _ _)
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ Cf * ‖Ept z‖ ^ min k l + Cg * ‖Ept z‖ ^ min k l :=
        add_le_add (le_trans (hf z hz) (mul_le_mul_of_nonneg_left hk hCf.le))
          (le_trans (hg z hz) (mul_le_mul_of_nonneg_left hl hCg.le))
    _ = (Cf + Cg) * ‖Ept z‖ ^ min k l := by ring

theorem sub (hf : IsSmH k f) (hg : IsSmH l g) : IsSmH (min k l) (fun z => f z - g z) := by
  have h := add hf (neg hg)
  exact congr h (fun z => by simp [sub_eq_add_neg])

theorem mul (hf : IsSmH k f) (hg : IsSmH l g) : IsSmH (k + l) (fun z => f z * g z) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf * Cg, by positivity, fun z hz => ?_⟩
  have h1 := hf z hz
  have h2 := hg z hz
  have h3 : (0 : ℝ) ≤ ‖g z‖ := norm_nonneg _
  rw [norm_mul, pow_add]
  calc ‖f z‖ * ‖g z‖ ≤ (Cf * ‖Ept z‖ ^ k) * (Cg * ‖Ept z‖ ^ l) :=
        mul_le_mul h1 h2 h3 (by positivity)
    _ = (Cf * Cg) * (‖Ept z‖ ^ k * ‖Ept z‖ ^ l) := by ring

theorem pow (h : IsSmH k f) (n : ℕ) : IsSmH (k * n) (fun z => f z ^ n) := by
  induction n with
  | zero => exact IsSmH.bdd (B := 1) (by norm_num) (fun z _ => by simp)
  | succ m ih =>
    have hm : IsSmH (k * m + k) (fun z => f z ^ m * f z) := IsSmH.mul ih h
    have heq : k * (m + 1) = k * m + k := by ring
    rw [heq]
    exact IsSmH.congr hm (fun z => by rw [pow_succ])

theorem one : IsSmH 0 (fun _ : ℍ => (1 : ℂ)) :=
  IsSmH.bdd (B := 1) (by norm_num) (fun _ _ => by simp)

theorem add6 {f g : ℍ → ℂ} (hf : IsSmH 6 f) (hg : IsSmH 6 g) :
    IsSmH 6 (fun z => f z + g z) := by
  have h := hf.add hg; rw [min_self] at h; exact h

theorem add0 {f g : ℍ → ℂ} (hf : IsSmH 0 f) (hg : IsSmH 0 g) :
    IsSmH 0 (fun z => f z + g z) := by
  have h := hf.add hg; rw [min_self] at h; exact h

end IsSmH

theorem isSmH_Ept : IsSmH 1 (fun z => Ept z) :=
  ⟨1, one_pos, fun z _ => by simp⟩

theorem isSmH_Epow (c : ℂ) (k : ℕ) : IsSmH k (fun z => c * (Ept z) ^ k) := by
  have h : IsSmH k (fun z => (Ept z) ^ k) := by
    simpa using isSmH_Ept.pow k
  exact IsSmH.const_mul c h

private lemma isSmH_mono6 (c : ℂ) (k : ℕ) (hk : 6 ≤ k) :
    IsSmH 6 (fun z => c * (Ept z) ^ k) :=
  IsSmH.mono (isSmH_Epow c k) hk

private lemma isSmH_mono0 (c : ℂ) (k : ℕ) :
    IsSmH 0 (fun z => c * (Ept z) ^ k) :=
  IsSmH.mono (isSmH_Epow c k) (Nat.zero_le k)

private lemma exp_neg_pi_le_half : Real.exp (-Real.pi) ≤ 1 / 2 := by
  have h : (2 : ℝ) ≤ Real.exp Real.pi := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    have h2 : Real.exp 1 ≤ Real.exp Real.pi := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  calc Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
    _ = 1 / 2 := by norm_num

/-- `θ₀₀ = 1 + 2E + 2E⁴ + O(‖E‖⁹)` on `{1 ≤ Im τ}`. -/
private lemma theta00_refinedH (τ : ℍ) (hτ : 1 ≤ τ.im) :
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
    simp only [hFdef]; simp [Ept]
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

/-- `θ₀₁ = 1 - 2E + 2E⁴ + O(‖E‖⁹)` on `{1 ≤ Im τ}`. -/
private lemma theta01_refinedH (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.theta01Fun τ - 1 + 2 * Ept τ - 2 * (Ept τ) ^ 4‖ ≤ 4 * ‖Ept τ‖ ^ 9 := by
  have hτ' : (1 : ℝ) ≤ (ModularGroup.T • τ).im := by
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.vadd_im]; exact hτ
  have h := theta00_refinedH (ModularGroup.T • τ) hτ'
  rw [Work.Kernels.theta00Fun_T τ, Ept_T τ] at h
  have h' : ‖Work.Kernels.theta01Fun τ - 1 + 2 * Ept τ - 2 * (Ept τ) ^ 4‖
      = ‖Work.Kernels.theta01Fun τ - 1 - 2 * (-Ept τ) - 2 * (-Ept τ) ^ 4‖ := by
    congr 1; ring
  rw [h']
  rw [norm_neg] at h
  exact h

private lemma isSmH_theta00Rem : IsSmH 6 (theta00Rem : ℍ → ℂ) := by
  refine ⟨4, by norm_num, fun z hz => ?_⟩
  have h := theta00_refinedH z hz
  have h9 : ‖Ept z‖ ^ 9 ≤ ‖Ept z‖ ^ 6 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (norm_Ept_lt_one z)) (by norm_num)
  show ‖theta00Rem z‖ ≤ 4 * ‖Ept z‖ ^ 6
  simp only [theta00Rem]
  linarith

private lemma isSmH_theta01Rem : IsSmH 6 (theta01Rem : ℍ → ℂ) := by
  refine ⟨4, by norm_num, fun z hz => ?_⟩
  have h := theta01_refinedH z hz
  have h9 : ‖Ept z‖ ^ 9 ≤ ‖Ept z‖ ^ 6 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (norm_Ept_lt_one z)) (by norm_num)
  show ‖theta01Rem z‖ ≤ 4 * ‖Ept z‖ ^ 6
  simp only [theta01Rem]
  linarith

private lemma isSmH_B00 : IsSmH 0 (fun z : ℍ => 1 + 2 * Ept z + 2 * (Ept z) ^ 4) := by
  refine IsSmH.bdd (B := 5) (by norm_num) (fun z hz => ?_)
  have he1 : ‖Ept z‖ ≤ 1 := le_of_lt (norm_Ept_lt_one z)
  have h := norm_add_le ((1 : ℂ) + 2 * Ept z) (2 * (Ept z) ^ 4)
  have h2 := norm_add_le (1 : ℂ) (2 * Ept z)
  rw [norm_one] at h2
  have h3 : ‖(2 : ℂ) * Ept z‖ ≤ 2 := by rw [norm_mul, Complex.norm_ofNat]; linarith
  have h4 : ‖(2 : ℂ) * (Ept z) ^ 4‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h5 : ‖Ept z‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) he1
    linarith
  linarith

private lemma isSmH_B01 : IsSmH 0 (fun z : ℍ => 1 - 2 * Ept z + 2 * (Ept z) ^ 4) := by
  refine IsSmH.bdd (B := 5) (by norm_num) (fun z hz => ?_)
  have he1 : ‖Ept z‖ ≤ 1 := le_of_lt (norm_Ept_lt_one z)
  have h2 := norm_sub_le (1 : ℂ) (2 * Ept z)
  rw [norm_one] at h2
  have h3 : ‖(2 : ℂ) * Ept z‖ ≤ 2 := by rw [norm_mul, Complex.norm_ofNat]; linarith
  have hb1 : ‖(1 : ℂ) - 2 * Ept z‖ ≤ 1 + 2 := by linarith
  have h4 : ‖(2 : ℂ) * (Ept z) ^ 4‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h5 : ‖Ept z‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) he1
    linarith
  have h5 : ‖(1 : ℂ) - 2 * Ept z + 2 * (Ept z) ^ 4‖ ≤ (1 + 2) + 2 :=
    le_trans (norm_add_le _ _) (add_le_add hb1 h4)
  linarith

/-- `U = (1 + 2E + 2E⁴)⁴ + O(‖E‖⁶)`. -/
private lemma U_sub_polyH : IsSmH 6 (fun z : ℍ => Work.Kernels.UFun z
    - (1 + 2 * Ept z + 2 * (Ept z) ^ 4) ^ 4) := by
  have hx6 : IsSmH 6 (theta00Rem : ℍ → ℂ) := isSmH_theta00Rem
  have hx0 : IsSmH 0 (theta00Rem : ℍ → ℂ) := IsSmH.mono hx6 (by norm_num)
  have hbr : IsSmH 0 (fun z : ℍ => 4 * (1 + 2 * Ept z + 2 * (Ept z) ^ 4) ^ 3
      + 6 * (1 + 2 * Ept z + 2 * (Ept z) ^ 4) ^ 2 * theta00Rem z
      + 4 * (1 + 2 * Ept z + 2 * (Ept z) ^ 4) * theta00Rem z ^ 2
      + theta00Rem z ^ 3) :=
    (((IsSmH.const_mul 4 (isSmH_B00.pow 3)).add
      ((IsSmH.const_mul 6 (isSmH_B00.pow 2)).mul hx0)).add
      ((IsSmH.const_mul 4 isSmH_B00).mul (hx0.pow 2))).add (hx0.pow 3)
  refine IsSmH.congr (hx6.mul hbr) (fun z => ?_)
  have hU : Work.Kernels.UFun z = (1 + 2 * Ept z + 2 * (Ept z) ^ 4 + theta00Rem z) ^ 4 := by
    show Work.Kernels.theta00Fun z ^ 4 = _
    congr 1
    simp only [theta00Rem]
    ring
  rw [hU]; ring

/-- `W = (1 - 2E + 2E⁴)⁴ + O(‖E‖⁶)`. -/
private lemma W_sub_polyH : IsSmH 6 (fun z : ℍ => Work.Kernels.WFun z
    - (1 - 2 * Ept z + 2 * (Ept z) ^ 4) ^ 4) := by
  have hy6 : IsSmH 6 (theta01Rem : ℍ → ℂ) := isSmH_theta01Rem
  have hy0 : IsSmH 0 (theta01Rem : ℍ → ℂ) := IsSmH.mono hy6 (by norm_num)
  have hbr : IsSmH 0 (fun z : ℍ => 4 * (1 - 2 * Ept z + 2 * (Ept z) ^ 4) ^ 3
      + 6 * (1 - 2 * Ept z + 2 * (Ept z) ^ 4) ^ 2 * theta01Rem z
      + 4 * (1 - 2 * Ept z + 2 * (Ept z) ^ 4) * theta01Rem z ^ 2
      + theta01Rem z ^ 3) :=
    (((IsSmH.const_mul 4 (isSmH_B01.pow 3)).add
      ((IsSmH.const_mul 6 (isSmH_B01.pow 2)).mul hy0)).add
      ((IsSmH.const_mul 4 isSmH_B01).mul (hy0.pow 2))).add (hy0.pow 3)
  refine IsSmH.congr (hy6.mul hbr) (fun z => ?_)
  have hW : Work.Kernels.WFun z = (1 - 2 * Ept z + 2 * (Ept z) ^ 4 + theta01Rem z) ^ 4 := by
    show Work.Kernels.theta01Fun z ^ 4 = _
    congr 1
    simp only [theta01Rem]
    ring
  rw [hW]; ring

/-- `U = 1 + 8E + 24E² + 32E³ + 24E⁴ + 48E⁵ + O(‖E‖⁶)`. -/
theorem UfunSixthH : IsSmH 6 (fun z : ℍ => Work.Kernels.UFun z
    - (1 + 8 * Ept z + 24 * (Ept z) ^ 2 + 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
        + 48 * (Ept z) ^ 5)) := by
  have h1 : IsSmH 6 (fun z : ℍ => Work.Kernels.UFun z - (1 + 2 * Ept z + 2 * (Ept z) ^ 4) ^ 4) :=
    U_sub_polyH
  have h2 : IsSmH 6 (fun z : ℍ => (1 + 2 * Ept z + 2 * (Ept z) ^ 4) ^ 4
      - (1 + 8 * Ept z + 24 * (Ept z) ^ 2 + 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
        + 48 * (Ept z) ^ 5)) := by
    have hpoly : IsSmH 6 (fun z : ℍ =>
        96 * (Ept z) ^ 6 + 64 * (Ept z) ^ 7 + 24 * (Ept z) ^ 8 + 96 * (Ept z) ^ 9
        + 96 * (Ept z) ^ 10 + 32 * (Ept z) ^ 12 + 64 * (Ept z) ^ 13 + 16 * (Ept z) ^ 16) :=
      IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (IsSmH.add6
        (isSmH_mono6 96 6 (le_refl 6)) (isSmH_mono6 64 7 (by norm_num)))
        (isSmH_mono6 24 8 (by norm_num))) (isSmH_mono6 96 9 (by norm_num)))
        (isSmH_mono6 96 10 (by norm_num))) (isSmH_mono6 32 12 (by norm_num)))
        (isSmH_mono6 64 13 (by norm_num))) (isSmH_mono6 16 16 (by norm_num))
    exact IsSmH.congr hpoly (fun z => by ring)
  exact IsSmH.congr (IsSmH.add6 h1 h2) (fun z => by ring)

/-- `W = 1 - 8E + 24E² - 32E³ + 24E⁴ - 48E⁵ + O(‖E‖⁶)`. -/
theorem WfunSixthH : IsSmH 6 (fun z : ℍ => Work.Kernels.WFun z
    - (1 - 8 * Ept z + 24 * (Ept z) ^ 2 - 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
        - 48 * (Ept z) ^ 5)) := by
  have h1 : IsSmH 6 (fun z : ℍ => Work.Kernels.WFun z - (1 - 2 * Ept z + 2 * (Ept z) ^ 4) ^ 4) :=
    W_sub_polyH
  have h2 : IsSmH 6 (fun z : ℍ => (1 - 2 * Ept z + 2 * (Ept z) ^ 4) ^ 4
      - (1 - 8 * Ept z + 24 * (Ept z) ^ 2 - 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
        - 48 * (Ept z) ^ 5)) := by
    have hpoly :=
      IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (IsSmH.add6
        (isSmH_mono6 96 6 (le_refl 6)) (isSmH_mono6 (-64) 7 (by norm_num)))
        (isSmH_mono6 24 8 (by norm_num))) (isSmH_mono6 (-96) 9 (by norm_num)))
        (isSmH_mono6 96 10 (by norm_num))) (isSmH_mono6 32 12 (by norm_num)))
        (isSmH_mono6 (-64) 13 (by norm_num))) (isSmH_mono6 16 16 (by norm_num))
    exact IsSmH.congr hpoly (fun z => by ring)
  exact IsSmH.congr (IsSmH.add6 h1 h2) (fun z => by ring)

/-! ## The sixth-order expansion of `U² - V²` -/

private lemma u5H : IsSmH 0 (fun z : ℍ => 8 * Ept z + 24 * (Ept z) ^ 2 + 32 * (Ept z) ^ 3
    + 24 * (Ept z) ^ 4 + 48 * (Ept z) ^ 5) :=
  IsSmH.congr (IsSmH.add0 (IsSmH.add0 (IsSmH.add0 (IsSmH.add0 (isSmH_mono0 8 1)
    (isSmH_mono0 24 2)) (isSmH_mono0 32 3)) (isSmH_mono0 24 4)) (isSmH_mono0 48 5))
    (fun z => by ring)

private lemma w5H : IsSmH 0 (fun z : ℍ => -8 * Ept z + 24 * (Ept z) ^ 2 - 32 * (Ept z) ^ 3
    + 24 * (Ept z) ^ 4 - 48 * (Ept z) ^ 5) :=
  IsSmH.congr (IsSmH.add0 (IsSmH.add0 (IsSmH.add0 (IsSmH.add0 (isSmH_mono0 (-8) 1)
    (isSmH_mono0 24 2)) (isSmH_mono0 (-32) 3)) (isSmH_mono0 24 4)) (isSmH_mono0 (-48) 5))
    (fun z => by ring)

/-- `U² - V² = 1 + 16E - 144E² + 448E³ - 912E⁴ + 2016E⁵ + O(‖E‖⁶)`. -/
theorem UVSqSixthH : IsSmH 6 (fun z : ℍ => (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
    - (1 + 16 * Ept z - 144 * (Ept z) ^ 2 + 448 * (Ept z) ^ 3 - 912 * (Ept z) ^ 4
        + 2016 * (Ept z) ^ 5)) := by
  have hu : IsSmH 6 (fun z : ℍ => (Work.Kernels.UFun z - 1)
      - (8 * Ept z + 24 * (Ept z) ^ 2 + 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
          + 48 * (Ept z) ^ 5)) :=
    IsSmH.congr UfunSixthH (fun z => by ring)
  have hw : IsSmH 6 (fun z : ℍ => (Work.Kernels.WFun z - 1)
      - (-8 * Ept z + 24 * (Ept z) ^ 2 - 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
          - 48 * (Ept z) ^ 5)) :=
    IsSmH.congr WfunSixthH (fun z => by ring)
  have hu0 : IsSmH 0 (fun z : ℍ => Work.Kernels.UFun z - 1) :=
    IsSmH.congr (IsSmH.add0 (IsSmH.mono hu (by norm_num)) u5H) (fun z => by ring)
  have hw0 : IsSmH 0 (fun z : ℍ => Work.Kernels.WFun z - 1) :=
    IsSmH.congr (IsSmH.add0 (IsSmH.mono hw (by norm_num)) w5H) (fun z => by ring)
  have hR :=
    IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (IsSmH.add6 (isSmH_mono6 (-4224) 6 (le_refl 6))
      (isSmH_mono6 3840 7 (by norm_num))) (isSmH_mono6 (-8640) 8 (by norm_num)))
      (isSmH_mono6 2304 9 (by norm_num))) (isSmH_mono6 (-6912) 10 (by norm_num))
  have hA : IsSmH 6 (fun z : ℍ => 2 * ((Work.Kernels.UFun z - 1)
      - (8 * Ept z + 24 * (Ept z) ^ 2 + 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
          + 48 * (Ept z) ^ 5))) := IsSmH.const_mul 2 hu
  have hB : IsSmH 6 (fun z : ℍ => 2 * (((Work.Kernels.UFun z - 1)
        - (8 * Ept z + 24 * (Ept z) ^ 2 + 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
            + 48 * (Ept z) ^ 5)) * (Work.Kernels.WFun z - 1)
      + (8 * Ept z + 24 * (Ept z) ^ 2 + 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
          + 48 * (Ept z) ^ 5) * ((Work.Kernels.WFun z - 1)
            - (-8 * Ept z + 24 * (Ept z) ^ 2 - 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
                - 48 * (Ept z) ^ 5)))) := by
    have h1 : IsSmH 6 (fun z : ℍ => ((Work.Kernels.UFun z - 1)
          - (8 * Ept z + 24 * (Ept z) ^ 2 + 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
              + 48 * (Ept z) ^ 5)) * (Work.Kernels.WFun z - 1)) := IsSmH.mul hu hw0
    have h2 : IsSmH 6 (fun z : ℍ => (8 * Ept z + 24 * (Ept z) ^ 2 + 32 * (Ept z) ^ 3
          + 24 * (Ept z) ^ 4 + 48 * (Ept z) ^ 5) * ((Work.Kernels.WFun z - 1)
            - (-8 * Ept z + 24 * (Ept z) ^ 2 - 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
                - 48 * (Ept z) ^ 5))) := IsSmH.mul u5H hw
    exact IsSmH.const_mul 2 (IsSmH.add6 h1 h2)
  have hC := IsSmH.const_mul (-1)
    (IsSmH.mul hw (IsSmH.add0 hw0 w5H))
  refine IsSmH.congr (IsSmH.add6 (IsSmH.add6 (IsSmH.add6 hR hA) hB) hC) ?_
  intro z
  have hVz : Work.Kernels.VFun z = Work.Kernels.UFun z - Work.Kernels.WFun z := by
    rw [Work.Kernels.TildeFacts.theta_quartic z]; ring
  rw [hVz]
  ring

/-- `E₄² = 1 + 480q + 61920q² + O(‖q‖³)`. -/
theorem E4sqThirdOrder : Work.Asymptotics.Small.IsSmallT 1 (fun z : ℍ =>
    Work.Kernels.E4Fun z ^ 2 - 1 - 480 * Work.Kernels.qParamFun z
      - 61920 * Work.Kernels.qParamFun z ^ 2) 3 := by
  obtain ⟨C4, hC4, hE4⟩ := E4Fun_second_order
  refine ⟨1036800 + 4665600 + 2 * 2401 * C4 + C4 ^ 2 + 1, by positivity, fun z hz => ?_⟩
  dsimp only
  rw [show Work.Kernels.E4Fun z ^ 2 - 1 - 480 * Work.Kernels.qParamFun z
        - 61920 * Work.Kernels.qParamFun z ^ 2
      = Work.Kernels.E4Fun z ^ 2 - (1 + 480 * Work.Kernels.qParamFun z
        + 61920 * Work.Kernels.qParamFun z ^ 2) by ring]
  have he1 : ‖Ept z‖ ≤ 1 := le_of_lt (norm_Ept_lt_one z)
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) he1
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq4 : ‖Work.Kernels.qParamFun z‖ ^ 4 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 :=
    pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  have hq3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
  have he : ‖Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
      + 2160 * Work.Kernels.qParamFun z ^ 2)‖
      ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have h := hE4 z hz
    rw [show Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * Work.Kernels.qParamFun z ^ 2
        = Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2) by ring] at h
    exact h
  have hP : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
      + 2160 * Work.Kernels.qParamFun z ^ 2‖ ≤ 2401 := by
    have h1 : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2‖
        ≤ 1 + 240 * ‖Work.Kernels.qParamFun z‖
          + 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      calc ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2‖
          ≤ ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z‖
            + ‖2160 * Work.Kernels.qParamFun z ^ 2‖ := norm_add_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖240 * Work.Kernels.qParamFun z‖)
            + ‖2160 * Work.Kernels.qParamFun z ^ 2‖ := by
            linarith [norm_add_le (1 : ℂ) (240 * Work.Kernels.qParamFun z)]
        _ = 1 + 240 * ‖Work.Kernels.qParamFun z‖
            + 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
            rw [norm_one, norm_mul, norm_mul, norm_pow]
            norm_num
    nlinarith [h1, hq0, hq1]
  have hkey : Work.Kernels.E4Fun z ^ 2 - (1 + 480 * Work.Kernels.qParamFun z
        + 61920 * Work.Kernels.qParamFun z ^ 2)
      = (((1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2) ^ 2
          - (1 + 480 * Work.Kernels.qParamFun z + 61920 * Work.Kernels.qParamFun z ^ 2))
        + 2 * ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2) * (Work.Kernels.E4Fun z
            - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
              + 2160 * Work.Kernels.qParamFun z ^ 2))
        + (Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2)) ^ 2 := by ring
  rw [hkey]
  have h1 : ‖((1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2) ^ 2
        - (1 + 480 * Work.Kernels.qParamFun z + 61920 * Work.Kernels.qParamFun z ^ 2)‖
      ≤ 1036800 * ‖Work.Kernels.qParamFun z‖ ^ 3
        + 4665600 * ‖Work.Kernels.qParamFun z‖ ^ 4 := by
    rw [show ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2) ^ 2
          - (1 + 480 * Work.Kernels.qParamFun z + 61920 * Work.Kernels.qParamFun z ^ 2)
        = 1036800 * Work.Kernels.qParamFun z ^ 3
          + 4665600 * Work.Kernels.qParamFun z ^ 4 by ring]
    have ha := norm_add_le ((1036800 : ℂ) * Work.Kernels.qParamFun z ^ 3)
      ((4665600 : ℂ) * Work.Kernels.qParamFun z ^ 4)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat, Complex.norm_ofNat] at ha
    exact ha
  have h2 : ‖2 * ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2) * (Work.Kernels.E4Fun z
        - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2))‖
      ≤ 2 * 2401 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
    calc ‖2 * ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2) * (Work.Kernels.E4Fun z
          - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2))‖
        = ‖(2 : ℂ)‖ * ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2‖
          * ‖Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2)‖ := by rw [norm_mul, norm_mul]
      _ = 2 * ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2‖
          * ‖Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2)‖ := by rw [Complex.norm_ofNat]
      _ ≤ 2 * 2401 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
          nlinarith [hP, he, hC4.le, norm_nonneg (Work.Kernels.E4Fun z
            - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
              + 2160 * Work.Kernels.qParamFun z ^ 2))]
  have h3 : ‖(Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2)) ^ 2‖
      ≤ C4 ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [norm_pow]
    have h4 : ‖Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2)‖ ^ 2
        ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) he 2
    calc ‖Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2)‖ ^ 2
        ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) ^ 2 := h4
      _ = C4 ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 6 := by ring
      _ ≤ C4 ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hC4.le 2)
          calc ‖Work.Kernels.qParamFun z‖ ^ 6
              = ‖Work.Kernels.qParamFun z‖ ^ 3 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
            _ ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 * 1 :=
                mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) (by positivity)
            _ = ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  calc ‖(((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2) ^ 2
          - (1 + 480 * Work.Kernels.qParamFun z + 61920 * Work.Kernels.qParamFun z ^ 2))
        + 2 * ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2) * (Work.Kernels.E4Fun z
            - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
              + 2160 * Work.Kernels.qParamFun z ^ 2))
        + (Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2)) ^ 2‖
      ≤ ‖((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2) ^ 2
          - (1 + 480 * Work.Kernels.qParamFun z + 61920 * Work.Kernels.qParamFun z ^ 2)‖
        + ‖2 * ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2) * (Work.Kernels.E4Fun z
            - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
              + 2160 * Work.Kernels.qParamFun z ^ 2))‖
        + ‖(Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2)) ^ 2‖ := by
        have ha := norm_add_le (((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2) ^ 2
          - (1 + 480 * Work.Kernels.qParamFun z + 61920 * Work.Kernels.qParamFun z ^ 2)
          + 2 * ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2) * (Work.Kernels.E4Fun z
            - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
              + 2160 * Work.Kernels.qParamFun z ^ 2)))
          ((Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2)) ^ 2)
        have hb := norm_add_le (((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2) ^ 2
          - (1 + 480 * Work.Kernels.qParamFun z + 61920 * Work.Kernels.qParamFun z ^ 2))
          (2 * ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2) * (Work.Kernels.E4Fun z
            - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
              + 2160 * Work.Kernels.qParamFun z ^ 2)))
        linarith
    _ ≤ (1036800 * ‖Work.Kernels.qParamFun z‖ ^ 3
          + 4665600 * ‖Work.Kernels.qParamFun z‖ ^ 4)
        + 2 * 2401 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3)
        + C4 ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by linarith
    _ ≤ (1036800 + 4665600 + 2 * 2401 * C4 + C4 ^ 2 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        nlinarith [hq3, hq4, hq1, hq0, hC4.le, sq_nonneg C4]

/-- `E₄E₆ = 1 - 264q - 135432q² + O(‖q‖³)`. -/
theorem E4E6ThirdOrder : Work.Asymptotics.Small.IsSmallT 1 (fun z : ℍ =>
    Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - 1 + 264 * Work.Kernels.qParamFun z
      + 135432 * Work.Kernels.qParamFun z ^ 2) 3 := by
  obtain ⟨C4, hC4, hE4⟩ := E4Fun_second_order
  obtain ⟨C6, hC6, hE6⟩ := E6Fun_second_order
  refine ⟨5080320 + 35925120 + 2401 * C6 + C4 * 17137 + C4 * C6 + 1, by positivity,
    fun z hz => ?_⟩
  dsimp only
  rw [show Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - 1
        + 264 * Work.Kernels.qParamFun z + 135432 * Work.Kernels.qParamFun z ^ 2
      = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
        - (1 - 264 * Work.Kernels.qParamFun z
          - 135432 * Work.Kernels.qParamFun z ^ 2) by ring]
  have he1 : ‖Ept z‖ ≤ 1 := le_of_lt (norm_Ept_lt_one z)
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) he1
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq4 : ‖Work.Kernels.qParamFun z‖ ^ 4 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 :=
    pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  have hq3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
  have hq6 : ‖Work.Kernels.qParamFun z‖ ^ 6 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    calc ‖Work.Kernels.qParamFun z‖ ^ 6
        = ‖Work.Kernels.qParamFun z‖ ^ 3 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
      _ ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) (by positivity)
      _ = ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have he4 : ‖Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
      + 2160 * Work.Kernels.qParamFun z ^ 2)‖
      ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have h := hE4 z hz
    rw [show Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * Work.Kernels.qParamFun z ^ 2
        = Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2) by ring] at h
    exact h
  have he6 : ‖Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
      - 16632 * Work.Kernels.qParamFun z ^ 2)‖
      ≤ C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have h := hE6 z hz
    rw [show Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
          + 16632 * Work.Kernels.qParamFun z ^ 2
        = Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
          - 16632 * Work.Kernels.qParamFun z ^ 2) by ring] at h
    exact h
  have hP4 : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
      + 2160 * Work.Kernels.qParamFun z ^ 2‖ ≤ 2401 := by
    have h1 : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2‖
        ≤ 1 + 240 * ‖Work.Kernels.qParamFun z‖
          + 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      calc ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2‖
          ≤ ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z‖
            + ‖2160 * Work.Kernels.qParamFun z ^ 2‖ := norm_add_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖240 * Work.Kernels.qParamFun z‖)
            + ‖2160 * Work.Kernels.qParamFun z ^ 2‖ := by
            linarith [norm_add_le (1 : ℂ) (240 * Work.Kernels.qParamFun z)]
        _ = 1 + 240 * ‖Work.Kernels.qParamFun z‖
            + 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
            rw [norm_one, norm_mul, norm_mul, norm_pow]
            norm_num
    nlinarith [h1, hq0, hq1]
  have hP6 : ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z
      - 16632 * Work.Kernels.qParamFun z ^ 2‖ ≤ 17137 := by
    have h1 : ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z
        - 16632 * Work.Kernels.qParamFun z ^ 2‖
        ≤ 1 + 504 * ‖Work.Kernels.qParamFun z‖
          + 16632 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      calc ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z
            - 16632 * Work.Kernels.qParamFun z ^ 2‖
          ≤ ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z‖
            + ‖16632 * Work.Kernels.qParamFun z ^ 2‖ := norm_sub_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖504 * Work.Kernels.qParamFun z‖)
            + ‖16632 * Work.Kernels.qParamFun z ^ 2‖ := by
            linarith [norm_sub_le (1 : ℂ) (504 * Work.Kernels.qParamFun z)]
        _ = 1 + 504 * ‖Work.Kernels.qParamFun z‖
            + 16632 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
            rw [norm_one, norm_mul, norm_mul, norm_pow]
            norm_num
    nlinarith [h1, hq0, hq1]
  have hkey : Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
        - (1 - 264 * Work.Kernels.qParamFun z - 135432 * Work.Kernels.qParamFun z ^ 2)
      = (((1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
          * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
          - (1 - 264 * Work.Kernels.qParamFun z - 135432 * Work.Kernels.qParamFun z ^ 2))
        + ((1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
          * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
            - 16632 * Work.Kernels.qParamFun z ^ 2))
        + (Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2))
          * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
        + (Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2))
          * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
            - 16632 * Work.Kernels.qParamFun z ^ 2)) := by ring
  rw [hkey]
  have h1 : ‖((1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2)
        * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
        - (1 - 264 * Work.Kernels.qParamFun z - 135432 * Work.Kernels.qParamFun z ^ 2)‖
      ≤ 5080320 * ‖Work.Kernels.qParamFun z‖ ^ 3
        + 35925120 * ‖Work.Kernels.qParamFun z‖ ^ 4 := by
    rw [show ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2)
          * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
          - (1 - 264 * Work.Kernels.qParamFun z - 135432 * Work.Kernels.qParamFun z ^ 2)
        = (-(5080320 : ℂ)) * Work.Kernels.qParamFun z ^ 3
          + (-(35925120 : ℂ)) * Work.Kernels.qParamFun z ^ 4 by ring]
    have ha := norm_add_le ((-(5080320 : ℂ)) * Work.Kernels.qParamFun z ^ 3)
      ((-(35925120 : ℂ)) * Work.Kernels.qParamFun z ^ 4)
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_ofNat] at ha
    exact ha
  have h2 : ‖((1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
        * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
          - 16632 * Work.Kernels.qParamFun z ^ 2))‖
      ≤ 2401 * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hP4 he6 (norm_nonneg _) (by norm_num)
  have h3 : ‖(Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2))
        * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)‖
      ≤ 17137 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
    rw [norm_mul]
    calc ‖Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2)‖
          * ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2‖
        ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * 17137 :=
          mul_le_mul he4 hP6 (norm_nonneg _) (by positivity)
      _ = 17137 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by ring
  have h4 : ‖(Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2))
        * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
          - 16632 * Work.Kernels.qParamFun z ^ 2))‖ ≤ C4 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [norm_mul]
    calc ‖Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2)‖
          * ‖Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
            - 16632 * Work.Kernels.qParamFun z ^ 2)‖
        ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3)
          * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3) :=
          mul_le_mul he4 he6 (norm_nonneg _) (mul_nonneg hC4.le (by positivity))
      _ = C4 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 6 := by ring
      _ ≤ C4 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
          mul_le_mul_of_nonneg_left hq6 (mul_nonneg hC4.le hC6.le)
  calc ‖(((1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
        * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
        - (1 - 264 * Work.Kernels.qParamFun z - 135432 * Work.Kernels.qParamFun z ^ 2))
      + ((1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
        * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
          - 16632 * Work.Kernels.qParamFun z ^ 2))
      + (Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2))
        * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
      + (Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2))
        * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
          - 16632 * Work.Kernels.qParamFun z ^ 2))‖
      ≤ (5080320 * ‖Work.Kernels.qParamFun z‖ ^ 3 + 35925120 * ‖Work.Kernels.qParamFun z‖ ^ 4)
        + 2401 * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3)
        + 17137 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3)
        + C4 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        have ha := norm_add_le (((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2)
            * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
            - (1 - 264 * Work.Kernels.qParamFun z - 135432 * Work.Kernels.qParamFun z ^ 2)
            + ((1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
              * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
                - 16632 * Work.Kernels.qParamFun z ^ 2))
            + (Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
                + 2160 * Work.Kernels.qParamFun z ^ 2))
              * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2))
          ((Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
              + 2160 * Work.Kernels.qParamFun z ^ 2))
            * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
              - 16632 * Work.Kernels.qParamFun z ^ 2)))
        have hb := norm_add_le (((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2)
            * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
            - (1 - 264 * Work.Kernels.qParamFun z - 135432 * Work.Kernels.qParamFun z ^ 2)
            + ((1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
              * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
                - 16632 * Work.Kernels.qParamFun z ^ 2)))
          ((Work.Kernels.E4Fun z - ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
              + 2160 * Work.Kernels.qParamFun z ^ 2))
            * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2))
        have hc := norm_add_le (((1 : ℂ) + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2)
            * ((1 : ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
            - (1 - 264 * Work.Kernels.qParamFun z - 135432 * Work.Kernels.qParamFun z ^ 2))
          (((1 : ℂ) + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
            * (Work.Kernels.E6Fun z - ((1 : ℂ) - 504 * Work.Kernels.qParamFun z
              - 16632 * Work.Kernels.qParamFun z ^ 2)))
        linarith
    _ ≤ (5080320 + 35925120 + 2401 * C6 + C4 * 17137 + C4 * C6 + 1)
        * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        nlinarith [hq0, hq1, hq3, hq4, hC4.le, hC6.le]

theorem ZAtomsSecondOrder :
    ∃ T : ℝ, 1 ≤ T ∧
      Work.Asymptotics.Small.IsSmallT T (fun z : UpperHalfPlane => Work.Kernels.E4Fun z - 1
          - 240 * Work.Kernels.qParamFun z - 2160 * Work.Kernels.qParamFun z ^ 2) 3 ∧
      Work.Asymptotics.Small.IsSmallT T (fun z : UpperHalfPlane => Work.Kernels.E6Fun z - 1
          + 504 * Work.Kernels.qParamFun z + 16632 * Work.Kernels.qParamFun z ^ 2) 3 ∧
      Work.Asymptotics.Small.IsSmallT T (fun z : UpperHalfPlane => Work.Kernels.E2Fun z - 1
          + 24 * Work.Kernels.qParamFun z + 72 * Work.Kernels.qParamFun z ^ 2) 3 ∧
      Work.Asymptotics.Small.IsSmallT T (fun z : UpperHalfPlane => Work.Kernels.DeltaFun z
          - Work.Kernels.qParamFun z + 24 * Work.Kernels.qParamFun z ^ 2
          - 252 * Work.Kernels.qParamFun z ^ 3) 4 ∧
      Work.Asymptotics.Small.IsSmallT T (fun z : UpperHalfPlane => Work.Kernels.E4Fun z ^ 2 - 1
          - 480 * Work.Kernels.qParamFun z - 61920 * Work.Kernels.qParamFun z ^ 2) 3 ∧
      Work.Asymptotics.Small.IsSmallT T (fun z : UpperHalfPlane =>
          Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - 1
          + 264 * Work.Kernels.qParamFun z + 135432 * Work.Kernels.qParamFun z ^ 2) 3 ∧
      (∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.WFun z - (1 - 8 * Work.Residues.Ept z + 24 * Work.Kernels.qParamFun z
          - 32 * (Work.Residues.Ept z) ^ 3 + 24 * Work.Kernels.qParamFun z ^ 2
          - 48 * (Work.Residues.Ept z) ^ 5)‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 6) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖(Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2) - (1 + 16 * Work.Residues.Ept z
          - 144 * Work.Kernels.qParamFun z + 448 * (Work.Residues.Ept z) ^ 3
          - 912 * Work.Kernels.qParamFun z ^ 2 + 2016 * (Work.Residues.Ept z) ^ 5)‖
          ≤ C * ‖Work.Residues.Ept z‖ ^ 6) := by
  refine ⟨1, le_refl 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E4Fun_second_order
  · exact E6Fun_second_order
  · exact E2Fun_second_order
  · obtain ⟨C, hC, h⟩ := DeltaFun_fourth_order
    refine ⟨C, hC, fun z hz => ?_⟩
    dsimp only
    rw [show Work.Kernels.DeltaFun z - Work.Kernels.qParamFun z
          + 24 * Work.Kernels.qParamFun z ^ 2 - 252 * Work.Kernels.qParamFun z ^ 3
        = Work.Kernels.DeltaFun z - (Work.Kernels.qParamFun z
          - 24 * Work.Kernels.qParamFun z ^ 2 + 252 * Work.Kernels.qParamFun z ^ 3) by ring]
    exact h z hz
  · exact E4sqThirdOrder
  · exact E4E6ThirdOrder
  · obtain ⟨C, hC, h⟩ := WfunSixthH
    refine ⟨C, hC, fun z hz => ?_⟩
    have key : (1 - 8 * Ept z + 24 * Work.Kernels.qParamFun z - 32 * Ept z ^ 3
        + 24 * Work.Kernels.qParamFun z ^ 2 - 48 * Ept z ^ 5)
        = (1 - 8 * Ept z + 24 * (Ept z) ^ 2 - 32 * (Ept z) ^ 3 + 24 * (Ept z) ^ 4
            - 48 * (Ept z) ^ 5) := by
      rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]; ring
    rw [key]
    exact h z hz
  · obtain ⟨C, hC, h⟩ := UVSqSixthH
    refine ⟨C, hC, fun z hz => ?_⟩
    have key : (1 + 16 * Ept z - 144 * Work.Kernels.qParamFun z + 448 * Ept z ^ 3
        - 912 * Work.Kernels.qParamFun z ^ 2 + 2016 * Ept z ^ 5)
        = (1 + 16 * Ept z - 144 * (Ept z) ^ 2 + 448 * (Ept z) ^ 3 - 912 * (Ept z) ^ 4
            + 2016 * (Ept z) ^ 5) := by
      rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]; ring
    rw [key]
    exact h z hz

end

end Work.Asymptotics.KhatE1
