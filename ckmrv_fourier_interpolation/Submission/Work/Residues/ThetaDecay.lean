import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.Kernels
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.theta2_at_cusp

namespace Work.Residues

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold Modular ModularForm

noncomputable section

/-! ## Elementary estimates -/

/-- `(x + 1) ^ K ≤ 2 ^ K * (x ^ K + 1)` for `x ≥ 0`. -/
lemma succ_pow_le (K : ℕ) {x : ℝ} (hx : 0 ≤ x) : (x + 1) ^ K ≤ 2 ^ K * (x ^ K + 1) := by
  have h1 : x + 1 ≤ 2 * max x 1 := by
    rcases le_total 1 x with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  calc (x + 1) ^ K ≤ (2 * max x 1) ^ K := pow_le_pow_left₀ (by linarith) h1 K
    _ = 2 ^ K * (max x 1) ^ K := mul_pow 2 (max x 1) K
    _ ≤ 2 ^ K * (x ^ K + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total 1 x with h | h
        · rw [max_eq_left h]; linarith [pow_nonneg hx K]
        · rw [max_eq_right h, one_pow]; linarith [pow_nonneg hx K]

/-- The shifted polynomial-geometric series `∑ ((m : ℝ) + 1) ^ K ρ ^ m` converges for
`0 ≤ ρ < 1`. -/
lemma summable_succ_pow_mul_geometric (K : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ K * ρ ^ m) := by
  have hρ : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  have hbase : Summable (fun m : ℕ => (m : ℝ) ^ K * ρ ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one K hρ
  have hone : Summable (fun m : ℕ => (1 : ℝ) * ρ ^ m) :=
    (summable_geometric_of_norm_lt_one hρ).mul_left 1
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((hbase.add hone).mul_left (2 ^ K))
  calc ((m : ℝ) + 1) ^ K * ρ ^ m ≤ (2 ^ K * ((m : ℝ) ^ K + 1)) * ρ ^ m := by
        exact mul_le_mul_of_nonneg_right (succ_pow_le K (Nat.cast_nonneg m)) (by positivity)
    _ = 2 ^ K * ((m : ℝ) ^ K * ρ ^ m + 1 * ρ ^ m) := by ring

/-- `3 ≤ e ^ π`. -/
lemma three_le_exp_pi : (3 : ℝ) ≤ Real.exp Real.pi := by
  have h1 : (3 : ℝ) ≤ Real.exp 3 := by
    have he : Real.exp 3 = (Real.exp 1) ^ 3 := by
      have := Real.exp_nat_mul 1 3
      simpa using this
    rw [he]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    have h3 : (2 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
    norm_num at h3
    linarith
  exact le_trans h1 (Real.exp_le_exp.mpr Real.pi_gt_three.le)

/-- `e ^ (-π) < 1`. -/
lemma exp_neg_pi_lt_one : Real.exp (-Real.pi) < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])

/-- The constant `2 / (1 - e ^ (-π))`. -/
def thetaA : ℝ := 2 / (1 - Real.exp (-Real.pi))

lemma thetaA_pos : 0 < thetaA := by
  have h : (0 : ℝ) < 1 - Real.exp (-Real.pi) := by linarith [exp_neg_pi_lt_one]
  rw [thetaA]; positivity

lemma thetaA_nonneg : 0 ≤ thetaA := thetaA_pos.le

/-- `θ₃(z) - 1` decays like `e ^ (-π Im z)` uniformly for `Im z ≥ 1`. -/
lemma norm_jacobiTheta_sub_one_bound (z : ℂ) (hz : 1 ≤ z.im) :
    ‖jacobiTheta z - 1‖ ≤ thetaA * Real.exp (-(Real.pi * z.im)) := by
  have hzpos : 0 < z.im := lt_of_lt_of_le zero_lt_one hz
  have h := norm_jacobiTheta_sub_one_le hzpos
  have he : Real.exp (-Real.pi * z.im) ≤ Real.exp (-Real.pi) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hz]
  have hden : (0 : ℝ) < 1 - Real.exp (-Real.pi) := by linarith [exp_neg_pi_lt_one]
  rw [show -(Real.pi * z.im) = -Real.pi * z.im by ring]
  calc ‖jacobiTheta z - 1‖
      ≤ 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im) := h
    _ = 2 * Real.exp (-Real.pi * z.im) / (1 - Real.exp (-Real.pi * z.im)) := by ring
    _ ≤ 2 * Real.exp (-Real.pi * z.im) / (1 - Real.exp (-Real.pi)) := by
        apply div_le_div_of_nonneg_left (by positivity) hden
        linarith [he]
    _ = thetaA * Real.exp (-Real.pi * z.im) := by rw [thetaA]; ring

/-- `‖θ₃(z)‖ ≤ 2` for `Im z ≥ 1`. -/
lemma norm_jacobiTheta_le_two (z : ℂ) (hz : 1 ≤ z.im) : ‖jacobiTheta z‖ ≤ 2 := by
  have h1 := norm_jacobiTheta_sub_one_bound z hz
  have he : Real.exp (-(Real.pi * z.im)) ≤ Real.exp (-Real.pi) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hz]
  have hAc : thetaA * Real.exp (-Real.pi) ≤ 1 := by
    have h3 : (3 : ℝ) * Real.exp (-Real.pi) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right three_le_exp_pi (Real.exp_pos (-Real.pi)).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    have hden : (0 : ℝ) < 1 - Real.exp (-Real.pi) := by linarith [exp_neg_pi_lt_one]
    rw [thetaA, div_mul_eq_mul_div, div_le_one hden]
    linarith
  have h2 : ‖jacobiTheta z‖ ≤ 1 + thetaA * Real.exp (-(Real.pi * z.im)) := by
    have haux : ‖(jacobiTheta z - 1) + 1‖ ≤ ‖jacobiTheta z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at haux
    rw [sub_add_cancel] at haux
    linarith
  have h3 : thetaA * Real.exp (-(Real.pi * z.im)) ≤ thetaA * Real.exp (-Real.pi) :=
    mul_le_mul_of_nonneg_left he thetaA_nonneg
  linarith

/-- If `w` is close to `1` and `‖w‖ ≤ 2`, then `‖w ^ 4 - 1‖ ≤ 15 A e`. -/
lemma norm_pow_four_sub_one_le {w : ℂ} {A e : ℝ} (hA : 0 ≤ A) (he : 0 ≤ e)
    (h1 : ‖w - 1‖ ≤ A * e) (h2 : ‖w‖ ≤ 2) : ‖w ^ 4 - 1‖ ≤ 15 * A * e := by
  have hfac : w ^ 4 - 1 = (w - 1) * (w ^ 3 + w ^ 2 + w + 1) := by ring
  have hw3 : ‖w ^ 3‖ ≤ 8 := by
    rw [norm_pow]; exact le_trans (pow_le_pow_left₀ (norm_nonneg w) h2 3) (by norm_num)
  have hw2 : ‖w ^ 2‖ ≤ 4 := by
    rw [norm_pow]; exact le_trans (pow_le_pow_left₀ (norm_nonneg w) h2 2) (by norm_num)
  have hb : ‖w ^ 3 + w ^ 2 + w + 1‖ ≤ 15 := by
    have ha : ‖w ^ 3 + w ^ 2 + w + 1‖ ≤ ‖w ^ 3 + w ^ 2 + w‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at ha
    have hb1 : ‖w ^ 3 + w ^ 2 + w‖ ≤ ‖w ^ 3 + w ^ 2‖ + ‖w‖ := norm_add_le _ _
    have hb2 : ‖w ^ 3 + w ^ 2‖ ≤ ‖w ^ 3‖ + ‖w ^ 2‖ := norm_add_le _ _
    linarith
  rw [hfac, norm_mul]
  calc ‖w - 1‖ * ‖w ^ 3 + w ^ 2 + w + 1‖ ≤ (A * e) * 15 :=
        mul_le_mul h1 hb (norm_nonneg _) (mul_nonneg hA he)
    _ = 15 * A * e := by ring

/-- If `z` and `w` are close to `1` then `z ^ 3 - w ^ 2` is small, quantitatively. -/
lemma norm_cube_sub_sq_le {A B c e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hec : e ≤ c)
    {z w : ℂ} (hz : ‖z - 1‖ ≤ A * e) (hw : ‖w - 1‖ ≤ B * e) :
    ‖z ^ 3 - w ^ 2‖
      ≤ (A * ((1 + A * c) ^ 2 + (1 + A * c) + 1) + B * (2 + B * c)) * e := by
  have hzc : ‖z‖ ≤ 1 + A * c := by
    have h1 : ‖z‖ ≤ ‖z - 1‖ + 1 := by
      have h := norm_add_le (z - 1) 1
      rw [norm_one, sub_add_cancel] at h
      exact h
    have h2 : ‖z - 1‖ ≤ A * c := le_trans hz (mul_le_mul_of_nonneg_left hec hA)
    linarith
  have hwc : ‖w‖ ≤ 1 + B * c := by
    have h1 : ‖w‖ ≤ ‖w - 1‖ + 1 := by
      have h := norm_add_le (w - 1) 1
      rw [norm_one, sub_add_cancel] at h
      exact h
    have h2 : ‖w - 1‖ ≤ B * c := le_trans hw (mul_le_mul_of_nonneg_left hec hB)
    linarith
  have hz2 : ‖z ^ 2 + z + 1‖ ≤ (1 + A * c) ^ 2 + (1 + A * c) + 1 := by
    have ha : ‖z ^ 2 + z + 1‖ ≤ ‖z ^ 2 + z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at ha
    have hb : ‖z ^ 2 + z‖ ≤ ‖z ^ 2‖ + ‖z‖ := norm_add_le _ _
    have hc : ‖z ^ 2‖ ≤ (1 + A * c) ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg z) hzc 2
    linarith
  have hw2 : ‖w + 1‖ ≤ 2 + B * c := by
    have ha : ‖w + 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at ha
    linarith
  have hsplit : z ^ 3 - w ^ 2 = (z - 1) * (z ^ 2 + z + 1) - (w - 1) * (w + 1) := by ring
  rw [hsplit]
  have ha : ‖(z - 1) * (z ^ 2 + z + 1) - (w - 1) * (w + 1)‖
      ≤ ‖(z - 1) * (z ^ 2 + z + 1)‖ + ‖(w - 1) * (w + 1)‖ := norm_sub_le _ _
  have hb : ‖(z - 1) * (z ^ 2 + z + 1)‖ ≤ (A * e) * ((1 + A * c) ^ 2 + (1 + A * c) + 1) := by
    rw [norm_mul]; exact mul_le_mul hz hz2 (norm_nonneg _) (mul_nonneg hA he)
  have hc : ‖(w - 1) * (w + 1)‖ ≤ (B * e) * (2 + B * c) := by
    rw [norm_mul]; exact mul_le_mul hw hw2 (norm_nonneg _) (mul_nonneg hB he)
  calc ‖(z - 1) * (z ^ 2 + z + 1) - (w - 1) * (w + 1)‖
      ≤ ‖(z - 1) * (z ^ 2 + z + 1)‖ + ‖(w - 1) * (w + 1)‖ := ha
    _ ≤ (A * e) * ((1 + A * c) ^ 2 + (1 + A * c) + 1) + (B * e) * (2 + B * c) := add_le_add hb hc
    _ = (A * ((1 + A * c) ^ 2 + (1 + A * c) + 1) + B * (2 + B * c)) * e := by ring

/-! ## The decay of a `q`-expansion with polynomially bounded coefficients -/

/-- If `f` is periodic of period one, holomorphic and bounded at the cusp, and its
`q`-expansion coefficients of index `≥ 1` grow at most like `M m ^ K`, then `f` differs from
its constant `q`-coefficient by `O (e ^ (-2 π Im τ))`. -/
theorem qExpansion_decay {f : ℍ → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
    (M : ℝ) (K : ℕ) (hM : 0 ≤ M)
    (ha : ∀ m : ℕ, 1 ≤ m → ‖(UpperHalfPlane.qExpansion 1 f).coeff m‖ ≤ M * (m : ℝ) ^ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖f τ - (UpperHalfPlane.qExpansion 1 f).coeff 0‖ ≤
        C * Real.exp (-(2 * Real.pi * τ.im)) := by
  set ρ : ℝ := Real.exp (-(2 * Real.pi)) with hρdef
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hSsum : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ K * ρ ^ m) :=
    summable_succ_pow_mul_geometric K hρ0 hρ1
  set S : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) ^ K * ρ ^ m with hSdef
  have hSnonneg : 0 ≤ S := tsum_nonneg (fun m => by positivity)
  refine ⟨M * S + 1, by positivity, fun τ hτ => ?_⟩
  set q : ℂ := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hqnorm : ‖q‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hqdef, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
    congr 1
    ring
  have hqle : ‖q‖ ≤ ρ := by
    rw [hqnorm, hρdef, Real.exp_le_exp]
    nlinarith [Real.pi_pos, hτ]
  -- the `HasSum` of the tail
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := f) one_pos hper hhol hbdd τ
  have hs' : HasSum (fun m : ℕ => (UpperHalfPlane.qExpansion 1 f).coeff (m + 1) * q ^ (m + 1))
      (f τ - (UpperHalfPlane.qExpansion 1 f).coeff 0) := by
    have h := (hasSum_nat_add_iff' 1).mpr hs
    have h0 : (∑ i ∈ Finset.range 1,
        (UpperHalfPlane.qExpansion 1 f).coeff i • Function.Periodic.qParam 1 (τ : ℂ) ^ i)
        = (UpperHalfPlane.qExpansion 1 f).coeff 0 := by simp
    rw [h0] at h
    simpa [← hqdef, smul_eq_mul] using h
  rw [← hs'.tsum_eq]
  have hterm : ∀ m : ℕ, ‖(UpperHalfPlane.qExpansion 1 f).coeff (m + 1) * q ^ (m + 1)‖
      ≤ (M * ‖q‖) * (((m : ℝ) + 1) ^ K * ρ ^ m) := by
    intro m
    have h1 : ‖(UpperHalfPlane.qExpansion 1 f).coeff (m + 1)‖ ≤ M * ((m : ℝ) + 1) ^ K := by
      have := ha (m + 1) (by omega)
      simpa [Nat.cast_add, Nat.cast_one] using this
    have h2 : ‖q ^ (m + 1)‖ ≤ ‖q‖ * ρ ^ m := by
      rw [norm_pow, pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg q) hqle m) (norm_nonneg q)
    rw [norm_mul]
    calc ‖(UpperHalfPlane.qExpansion 1 f).coeff (m + 1)‖ * ‖q ^ (m + 1)‖
        ≤ (M * ((m : ℝ) + 1) ^ K) * (‖q‖ * ρ ^ m) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (M * ‖q‖) * (((m : ℝ) + 1) ^ K * ρ ^ m) := by ring
  have hmaj : Summable (fun m : ℕ => (M * ‖q‖) * (((m : ℝ) + 1) ^ K * ρ ^ m)) :=
    hSsum.mul_left _
  have hsumm : Summable (fun m : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 f).coeff (m + 1) * q ^ (m + 1)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm hmaj
  calc ‖∑' m : ℕ, (UpperHalfPlane.qExpansion 1 f).coeff (m + 1) * q ^ (m + 1)‖
      ≤ ∑' m : ℕ, ‖(UpperHalfPlane.qExpansion 1 f).coeff (m + 1) * q ^ (m + 1)‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' m : ℕ, (M * ‖q‖) * (((m : ℝ) + 1) ^ K * ρ ^ m) :=
        Summable.tsum_le_tsum hterm hsumm hmaj
    _ = (M * ‖q‖) * ∑' m : ℕ, ((m : ℝ) + 1) ^ K * ρ ^ m := tsum_mul_left
    _ = (M * ‖q‖) * S := by rw [hSdef]
    _ ≤ (M * S + 1) * Real.exp (-(2 * Real.pi * τ.im)) := by
        rw [hqnorm]
        nlinarith [Real.exp_pos (-(2 * Real.pi * τ.im)), hSnonneg, hM]

/-! ## The Eisenstein series `E₄`, `E₆` and `Δ` -/

/-- `E₄ - 1 = O (e ^ (-2 π Im τ))`. -/
theorem E4Fun_decay : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖Work.Kernels.E4Fun τ - 1‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im)) := by
  have hcoeff : ∀ m : ℕ, 1 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff m‖ ≤ 240 * (m : ℝ) ^ 4 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have hcoeff : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff m
        = (240 : ℂ) * ((ArithmeticFunction.sigma 3 m : ℕ) : ℂ) := by
      rw [Work.Modular.E4_qExpansion_coeff m, if_neg hm0]
    have hsig : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m : ℝ) ^ 4 := by
      have h' : ArithmeticFunction.sigma 3 m ≤ m ^ 4 := by
        simpa using ArithmeticFunction.sigma_le_pow_succ 3 m
      exact_mod_cast h'
    rw [hcoeff, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hsig (by norm_num)
  obtain ⟨C, hC, h⟩ := qExpansion_decay (f := (⇑ModularForm.E₄ : ℍ → ℂ))
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularForm.holo' ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄)
    240 4 (by norm_num) hcoeff
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff 0 = 1 := by
    simpa using Work.Modular.E4_qExpansion_coeff 0
  have := h τ hτ
  rw [h0] at this
  simpa [Work.Kernels.E4Fun] using this

/-- `E₆ - 1 = O (e ^ (-2 π Im τ))`. -/
theorem E6Fun_decay : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖Work.Kernels.E6Fun τ - 1‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im)) := by
  have hcoeff : ∀ m : ℕ, 1 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff m‖ ≤ 504 * (m : ℝ) ^ 6 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have hcoeff : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff m
        = -((504 : ℂ) * ((ArithmeticFunction.sigma 5 m : ℕ) : ℂ)) := by
      rw [Work.Modular.E6_qExpansion_coeff m, if_neg hm0]
      ring
    have hsig : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m : ℝ) ^ 6 := by
      have h' : ArithmeticFunction.sigma 5 m ≤ m ^ 6 := by
        simpa using ArithmeticFunction.sigma_le_pow_succ 5 m
      exact_mod_cast h'
    rw [hcoeff, norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hsig (by norm_num)
  obtain ⟨C, hC, h⟩ := qExpansion_decay (f := (⇑ModularForm.E₆ : ℍ → ℂ))
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL)
    (ModularForm.holo' ModularForm.E₆) (ModularFormClass.bdd_at_infty ModularForm.E₆)
    504 6 (by norm_num) hcoeff
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff 0 = 1 := by
    simpa using Work.Modular.E6_qExpansion_coeff 0
  have := h τ hτ
  rw [h0] at this
  simpa [Work.Kernels.E6Fun] using this

/-- `Δ = O (e ^ (-2 π Im τ))`. -/
theorem DeltaFun_decay : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖Work.Kernels.DeltaFun τ‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨C4, hC4, h4⟩ := E4Fun_decay
  obtain ⟨C6, hC6, h6⟩ := E6Fun_decay
  refine ⟨(C4 * ((1 + C4 * Real.exp (-(2 * Real.pi))) ^ 2 + (1 + C4 * Real.exp (-(2 * Real.pi)))
      + 1) + C6 * (2 + C6 * Real.exp (-(2 * Real.pi)))) / 1728 + 1, ?_, fun τ hτ => ?_⟩
  · have h3 : (0 : ℝ) < 1 + C4 * Real.exp (-(2 * Real.pi)) := by
      have := Real.exp_pos (-(2 * Real.pi)); nlinarith
    have h4' : (0 : ℝ) < 2 + C6 * Real.exp (-(2 * Real.pi)) := by
      have := Real.exp_pos (-(2 * Real.pi)); nlinarith
    positivity
  · set e : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with hedef
    have hepos : 0 < e := by rw [hedef]; exact Real.exp_pos _
    have heρ : e ≤ Real.exp (-(2 * Real.pi)) := by
      rw [hedef, Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]
    have hA : ‖Work.Kernels.E4Fun τ - 1‖ ≤ C4 * e := by
      simpa [← hedef] using h4 τ hτ
    have hB : ‖Work.Kernels.E6Fun τ - 1‖ ≤ C6 * e := by
      simpa [← hedef] using h6 τ hτ
    have hΔ : Work.Kernels.DeltaFun τ
        = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) / 1728 := by
      have h1 : Work.Kernels.DeltaFun τ = ModularForm.discriminant τ := by
        rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
      rw [h1, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    have hkey := norm_cube_sub_sq_le (A := C4) (B := C6) (c := Real.exp (-(2 * Real.pi))) (e := e)
      hC4.le hC6.le hepos.le heρ hA hB
    rw [hΔ, norm_div, Complex.norm_ofNat]
    have h1 : ‖Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2‖ / 1728 ≤
        (C4 * ((1 + C4 * Real.exp (-(2 * Real.pi))) ^ 2 + (1 + C4 * Real.exp (-(2 * Real.pi)))
          + 1) + C6 * (2 + C6 * Real.exp (-(2 * Real.pi)))) / 1728 * e := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hkey (by norm_num)
    have h2 : (C4 * ((1 + C4 * Real.exp (-(2 * Real.pi))) ^ 2 + (1 + C4 * Real.exp (-(2 * Real.pi)))
        + 1) + C6 * (2 + C6 * Real.exp (-(2 * Real.pi)))) / 1728 * e
        ≤ ((C4 * ((1 + C4 * Real.exp (-(2 * Real.pi))) ^ 2
          + (1 + C4 * Real.exp (-(2 * Real.pi))) + 1)
          + C6 * (2 + C6 * Real.exp (-(2 * Real.pi)))) / 1728 + 1) * e := by
      nlinarith [hepos.le]
    linarith [h1, h2]

/-! ## The theta quartics -/

/-- `U - 1 = O (e ^ (-π Im τ))`. -/
theorem UFun_decay : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖Work.Kernels.UFun τ - 1‖ ≤ C * Real.exp (-(Real.pi * τ.im)) := by
  refine ⟨15 * thetaA + 1, ?_, fun τ hτ => ?_⟩
  · have := thetaA_pos; linarith
  · have hz : 1 ≤ (τ : ℂ).im := hτ
    have h1 := norm_jacobiTheta_sub_one_bound (τ : ℂ) hz
    have h2 := norm_jacobiTheta_le_two (τ : ℂ) hz
    have h3 := norm_pow_four_sub_one_le (w := jacobiTheta (τ : ℂ)) (A := thetaA)
      (e := Real.exp (-(Real.pi * (τ : ℂ).im))) thetaA_nonneg (Real.exp_nonneg _) h1 h2
    have hU : Work.Kernels.UFun τ = jacobiTheta (τ : ℂ) ^ 4 := rfl
    rw [hU]
    simp only [UpperHalfPlane.coe_im] at h3
    nlinarith [h3, Real.exp_pos (-(Real.pi * τ.im))]

/-- `W - 1 = O (e ^ (-π Im τ))`. -/
theorem WFun_decay : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖Work.Kernels.WFun τ - 1‖ ≤ C * Real.exp (-(Real.pi * τ.im)) := by
  refine ⟨15 * thetaA + 1, ?_, fun τ hτ => ?_⟩
  · have := thetaA_pos; linarith
  · set z : ℂ := ((ModularGroup.T • τ : ℍ) : ℂ) with hzdef
    have hcoe : z = (τ : ℂ) + 1 := by
      rw [hzdef, modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
    have him : z.im = τ.im := by rw [hcoe]; simp
    have hz : 1 ≤ z.im := by rw [him]; exact hτ
    have h1 : ‖jacobiTheta z - 1‖ ≤ thetaA * Real.exp (-(Real.pi * τ.im)) := by
      have := norm_jacobiTheta_sub_one_bound z hz
      simpa only [him] using this
    have h2 := norm_jacobiTheta_le_two z hz
    have h3 := norm_pow_four_sub_one_le (w := jacobiTheta z) (A := thetaA)
      (e := Real.exp (-(Real.pi * τ.im))) thetaA_nonneg (Real.exp_nonneg _) h1 h2
    have hW : Work.Kernels.WFun τ = jacobiTheta z ^ 4 := by
      have h4 : Work.Modular.theta4 τ = jacobiTheta z := by
        rw [← Work.Modular.theta3_T_smul τ]
        rfl
      rw [show Work.Kernels.WFun τ = Work.Modular.theta4 τ ^ 4 from rfl, h4]
    rw [hW]
    nlinarith [h3, Real.exp_pos (-(Real.pi * τ.im))]

/-- `V = O (e ^ (-π Im τ))`. -/
theorem VFun_decay : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖Work.Kernels.VFun τ‖ ≤ C * Real.exp (-(Real.pi * τ.im)) := by
  refine ⟨Work.Modular.theta2BoundConst ^ 4 + 1, ?_, fun τ hτ => ?_⟩
  · have := sq_nonneg (Work.Modular.theta2BoundConst ^ 2); linarith
  · have h := Work.Modular.norm_theta2_le_exp τ (by simpa using hτ)
    have hV : Work.Kernels.VFun τ = Work.Modular.theta2 τ ^ 4 := rfl
    rw [hV, norm_pow]
    have h1 : ‖Work.Modular.theta2 τ‖ ^ 4 ≤
        (Real.exp (-Real.pi * (τ : ℂ).im / 4) * Work.Modular.theta2BoundConst) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) h 4
    have h2 : (Real.exp (-Real.pi * (τ : ℂ).im / 4) * Work.Modular.theta2BoundConst) ^ 4
        = Work.Modular.theta2BoundConst ^ 4 * Real.exp (-(Real.pi * τ.im)) := by
      rw [mul_pow]
      have hexp : Real.exp (-Real.pi * (τ : ℂ).im / 4) ^ 4 = Real.exp (-(Real.pi * τ.im)) := by
        rw [← Real.exp_nat_mul]
        simp only [UpperHalfPlane.coe_im]
        congr 1
        ring
      rw [hexp]
      ring
    rw [h2] at h1
    nlinarith [h1, Real.exp_pos (-(Real.pi * τ.im)), sq_nonneg (Work.Modular.theta2BoundConst ^ 2)]

end

/-- The basic decay of the theta quartics and of the level-one modular forms `E₄`, `E₆`, `Δ`
near the cusp `i∞`: `U - 1`, `W - 1`, `V` are `O(e^{-π Im τ})`, while `Δ`, `E₄ - 1`, `E₆ - 1`
are `O(e^{-2π Im τ})`. -/
theorem ThetaDecay :
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.UFun τ - 1‖ ≤ C * Real.exp (-(Real.pi * τ.im))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.WFun τ - 1‖ ≤ C * Real.exp (-(Real.pi * τ.im))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.VFun τ‖ ≤ C * Real.exp (-(Real.pi * τ.im))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.DeltaFun τ‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.E4Fun τ - 1‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.E6Fun τ - 1‖ ≤ C * Real.exp (-(2 * Real.pi * τ.im))) :=
  ⟨UFun_decay, WFun_decay, VFun_decay, DeltaFun_decay, E4Fun_decay, E6Fun_decay⟩

end Work.Residues
