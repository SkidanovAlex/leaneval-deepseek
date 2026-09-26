import Mathlib
import Submission.Work.Residues.ThetaDecay

/-!
# Tail bounds for `q`-expansions of modular forms

If `f` is periodic of period one, holomorphic and bounded at the cusp, and the coefficients of
its `q`-expansion of index `≥ r` grow at most like `M · m ^ K`, then `f` differs from the
polynomial part `∑_{m < r} c_m · q ^ m` of its `q`-expansion by `O (‖q‖ ^ r)`.
-/

namespace Work.Residues

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold Modular ModularForm

noncomputable section

theorem qExpansion_tail_bound (r : ℕ) {f : ℍ → ℂ}
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
    (M : ℝ) (K : ℕ) (hM : 0 ≤ M)
    (ha : ∀ m : ℕ, r ≤ m → ‖(UpperHalfPlane.qExpansion 1 f).coeff m‖ ≤ M * (m : ℝ) ^ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖f τ - ∑ m ∈ Finset.range r,
          (UpperHalfPlane.qExpansion 1 f).coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m‖
        ≤ C * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ r := by
  set ρ : ℝ := Real.exp (-(2 * Real.pi)) with hρdef
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hSsum : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ K * ρ ^ m) :=
    summable_succ_pow_mul_geometric K hρ0 hρ1
  set S : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) ^ K * ρ ^ m with hSdef
  have hSnonneg : 0 ≤ S := tsum_nonneg (fun m => by positivity)
  refine ⟨M * (max 1 (r : ℝ)) ^ K * S + 1, by positivity, fun τ hτ => ?_⟩
  set q : ℂ := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hqnorm : ‖q‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hqdef, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
    congr 1; ring
  have hqle : ‖q‖ ≤ ρ := by
    rw [hqnorm, hρdef, Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := f) one_pos hper hhol hbdd τ
  have hs' := (hasSum_nat_add_iff' r).mpr hs
  have h0 : (∑ i ∈ Finset.range r, (UpperHalfPlane.qExpansion 1 f).coeff i • q ^ i)
      = ∑ i ∈ Finset.range r, (UpperHalfPlane.qExpansion 1 f).coeff i * q ^ i :=
    Finset.sum_congr rfl (fun i _ => smul_eq_mul ..)
  have htsum : (∑' n : ℕ, (UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r))
      = f τ - ∑ i ∈ Finset.range r, (UpperHalfPlane.qExpansion 1 f).coeff i * q ^ i := by
    rw [← h0]; exact hs'.tsum_eq
  rw [← htsum]
  -- termwise bound
  have hstep : ∀ n : ℕ, ((n : ℝ) + r) ^ K ≤ (max 1 (r : ℝ)) ^ K * ((n : ℝ) + 1) ^ K := by
    intro n
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hnr : ((n : ℝ) + r) ≤ (max 1 (r : ℝ)) * ((n : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp
      · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        rw [max_eq_right hr1]
        nlinarith
    calc ((n : ℝ) + r) ^ K ≤ ((max 1 (r : ℝ)) * ((n : ℝ) + 1)) ^ K :=
          pow_le_pow_left₀ (by positivity) hnr K
      _ = (max 1 (r : ℝ)) ^ K * ((n : ℝ) + 1) ^ K := mul_pow _ _ _
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r)‖
        ≤ (M * (max 1 (r : ℝ)) ^ K * ‖q‖ ^ r) * (((n : ℝ) + 1) ^ K * ρ ^ n) := by
    intro n
    have hcoe : ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r)‖ ≤ M * ((n : ℝ) + r) ^ K := by
      have h := ha (n + r) (Nat.le_add_left r n)
      simpa [Nat.cast_add] using h
    have hpow : ‖q ^ (n + r)‖ ≤ ‖q‖ ^ r * ρ ^ n := by
      rw [norm_pow, pow_add, mul_comm (‖q‖ ^ n)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg q) hqle n) (by positivity)
    rw [smul_eq_mul, norm_mul]
    calc ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r)‖ * ‖q ^ (n + r)‖
        ≤ (M * ((n : ℝ) + r) ^ K) * (‖q‖ ^ r * ρ ^ n) :=
          mul_le_mul hcoe hpow (norm_nonneg _) (by positivity)
      _ ≤ (M * ((max 1 (r : ℝ)) ^ K * ((n : ℝ) + 1) ^ K)) * (‖q‖ ^ r * ρ ^ n) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hstep n) hM
      _ = (M * (max 1 (r : ℝ)) ^ K * ‖q‖ ^ r) * (((n : ℝ) + 1) ^ K * ρ ^ n) := by ring
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hSsum.mul_left _)
  calc ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r)‖
      ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r)‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (M * (max 1 (r : ℝ)) ^ K * ‖q‖ ^ r) * (((n : ℝ) + 1) ^ K * ρ ^ n) :=
        Summable.tsum_le_tsum hterm hsumm (hSsum.mul_left _)
    _ = (M * (max 1 (r : ℝ)) ^ K * ‖q‖ ^ r) * S := tsum_mul_left
    _ ≤ (M * (max 1 (r : ℝ)) ^ K * S + 1) * ‖q‖ ^ r := by
        have h1 : (0:ℝ) ≤ ‖q‖ ^ r := by positivity
        nlinarith [h1, hSnonneg, hM, pow_nonneg (by positivity : (0:ℝ) ≤ max 1 (r:ℝ)) K]

end

end Work.Residues
