/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.InverseTheory.Basic

/-!
# Elementary API for the halved average `AhalfZ` and the discrete `ℓ^p` seminorms

The small structural facts about `AhalfZ`, `ellOne` and `SupportIn` on which the §6 statements of
Krause–Mirek–Tao rest:

* `norm_AhalfZ_le` — `Ã_N(f,g)` is pointwise dominated by the pointwise bounds on `f` and `g`;
* `supportIn_AhalfZ` — `Ã_N(f,g)` is supported in `[-(M+N), M+N]` when `f` and `g` are supported
  in `[-M, M]`;
* `ellOne_le_of_supportIn` — a pointwise bound on a function supported in `[-M, M]` bounds its
  `ℓ¹` seminorm by `(2M+1)` times that bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Analysis.InverseTheory

/-- Pointwise bound for the halved average: if `‖f‖ ≤ Mf` and `‖g‖ ≤ Mg` pointwise, then
`‖Ã_N(f,g)(x)‖ ≤ Mf * Mg`. -/
theorem norm_AhalfZ_le (N : ℕ) (P : Polynomial ℤ) (f g : ℤ → ℂ) {Mf Mg : ℝ} (hMf : 0 ≤ Mf)
    (hMg : 0 ≤ Mg) (hf : ∀ y : ℤ, ‖f y‖ ≤ Mf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Mg) (x : ℤ) :
    ‖AhalfZ N P f g x‖ ≤ Mf * Mg := by
  have hMfg : 0 ≤ Mf * Mg := mul_nonneg hMf hMg
  have hsum_le : ∀ s : Finset ℕ, ‖∑ n ∈ s, f (x + (n : ℤ)) * g (x + P.eval (n : ℤ))‖
      ≤ (s.card : ℝ) * (Mf * Mg) := by
    intro s
    refine (norm_sum_le _ _).trans ?_
    have : ∀ n ∈ s, ‖f (x + (n : ℤ)) * g (x + P.eval (n : ℤ))‖ ≤ Mf * Mg := fun n _ => by
      rw [norm_mul]
      exact mul_le_mul (hf _) (hg _) (norm_nonneg _) hMf
    calc ∑ n ∈ s, ‖f (x + (n : ℤ)) * g (x + P.eval (n : ℤ))‖ ≤ ∑ n ∈ s, Mf * Mg :=
          Finset.sum_le_sum this
      _ = (s.card : ℝ) * (Mf * Mg) := by rw [Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [AhalfZ, hMfg]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : (((Finset.Ioc (N / 2) N).card : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h1 : (Finset.Ioc (N / 2) N).card ≤ N := by
      calc (Finset.Ioc (N / 2) N).card ≤ (Finset.Ioc 0 N).card :=
            Finset.card_le_card fun m hm => by
              simp only [Finset.mem_Ioc] at hm ⊢; omega
        _ = N := by simp
    exact_mod_cast h1
  rw [AhalfZ, norm_mul]
  have hscalar : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [show (((N : ℝ)⁻¹ : ℝ) : ℂ) = ((N : ℂ))⁻¹ by push_cast; ring]
    rw [norm_inv, Complex.norm_natCast]
  rw [hscalar]
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N, f (x + (n : ℤ)) * g (x + P.eval (n : ℤ))‖
      ≤ (N : ℝ)⁻¹ * (((Finset.Ioc (N / 2) N).card : ℝ) * (Mf * Mg)) :=
        mul_le_mul_of_nonneg_left (hsum_le _) (inv_nonneg.mpr hNpos.le)
    _ = ((N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ)) * (Mf * Mg) := by ring
    _ ≤ 1 * (Mf * Mg) := by
        refine mul_le_mul_of_nonneg_right ?_ hMfg
        calc (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
              mul_le_mul_of_nonneg_left hcard (inv_nonneg.mpr hNpos.le)
          _ = 1 := inv_mul_cancel₀ hNpos.ne'
    _ = Mf * Mg := one_mul _

/-- Support of the halved average: if `f` and `g` are supported in `[-M, M]` then `Ã_N(f,g)` is
supported in `[-(M+N), M+N]`.  (Only the support of `f` is used.) -/
theorem supportIn_AhalfZ {N M : ℕ} {P : Polynomial ℤ} {f g : ℤ → ℂ} (hf : SupportIn f M)
    (_hg : SupportIn g M) : SupportIn (AhalfZ N P f g) (M + N) := by
  intro x hx
  rw [AhalfZ]
  refine mul_eq_zero_of_right _ ?_
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have hfn : f (x + (n : ℤ)) = 0 := by
    apply hf
    have h1 : x.natAbs ≤ (x + (n : ℤ)).natAbs + n := by
      have := Int.natAbs_add_le (x + (n : ℤ)) (-(n : ℤ))
      simpa using this
    omega
  rw [hfn, zero_mul]

/-- The `ℓ¹` seminorm of a function supported in `[-M, M]` and pointwise bounded by `C` is at
most `(2M+1) C`. -/
theorem ellOne_le_of_supportIn (f : ℤ → ℂ) (M : ℕ) (h : SupportIn f M) {C : ℝ}
    (hC : ∀ x : ℤ, ‖f x‖ ≤ C) : ellOne f ≤ (2 * (M : ℝ) + 1) * C := by
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hcard : ∀ x : ℤ, x ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) → ‖f x‖ = (0 : ℝ) := by
    intro x hx
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    rw [h x (by
      rcases hx with hx | hx
      · have : x + 1 ≤ -(M : ℤ) := hx
        omega
      · omega)]
    simp
  rw [ellOne, tsum_eq_sum hcard]
  calc ∑ x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ‖f x‖
      ≤ ∑ x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), C := Finset.sum_le_sum fun x _ => hC x
    _ = ((Finset.Icc (-(M : ℤ)) (M : ℤ)).card : ℝ) * C := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (2 * (M : ℝ) + 1) * C := by
        rw [Int.card_Icc]
        have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
        rw [this]; push_cast; ring

end Work.Analysis.InverseTheory
