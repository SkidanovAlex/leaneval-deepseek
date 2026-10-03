import Mathlib
import Submission.Work.Peluse.Nodes

/-!
# The trivial bound `‖Λ^{N₀,N}‖ ≤ 3`

`Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂ = (N₀ N)⁻¹ ∑_x f₀(x) ∑_{y ∈ [N]} f₁(x + y) f₂(x + P(y))`
is the multilinear average of Peluse's §3.  When `f₀` is supported in `[-N₀, N₀]`, the outer sum
has at most `2N₀ + 1` non-zero terms, each of modulus at most `N` (there are `N` terms `y ∈ [N]`,
each of modulus at most `1`), so

`‖Λ^{N₀,N}(f₀,f₁,f₂)‖ ≤ (N₀ N)⁻¹ · (2N₀ + 1) N = (2N₀ + 1)/N₀ ≤ 3`

for `N₀ ≥ 1`.  Only the support of `f₀` is used; `f₁`, `f₂` need only be `1`-bounded.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Crux

noncomputable section

/-- Every integer in `[-N, N]` has `natAbs ≤ N`. -/
private lemma mem_Icc_neg_of_natAbs_le {N : ℕ} {x : ℤ} (h : x.natAbs ≤ N) :
    x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  rw [Finset.mem_Icc]
  have h' : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at h'
  exact abs_le.mp h'

/-- An integer outside `[-N, N]` has `N < natAbs`. -/
private lemma natAbs_le_of_not_mem_Icc {N : ℕ} {x : ℤ}
    (hx : x ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) : N < x.natAbs := by
  by_contra h
  push Not at h
  exact hx (mem_Icc_neg_of_natAbs_le h)

/-- **The trivial bound for the multilinear average.**  For `1`-bounded `f₀, f₁, f₂` with `f₀`
supported in `[-N₀, N₀]`, `‖Λ^{N₀,N}(f₀,f₁,f₂)‖ ≤ 3`. -/
theorem LambdaZ_norm_le {N₀ N : ℕ} (hN₀ : 1 ≤ N₀) (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ f₂ : ℤ → ℂ)
    (hs0 : Work.Peluse.SupportIn f₀ N₀) (hs1 : Work.Peluse.SupportIn f₁ N₀) (hs2 : Work.Peluse.SupportIn f₂ N₀)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1) (hb2 : ∀ x : ℤ, ‖f₂ x‖ ≤ 1) :
    ‖Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂‖ ≤ 3 := by
  have hunfold : Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂
      = ((N₀ : ℂ) * (N : ℂ))⁻¹ * (∑' x : ℤ, f₀ x *
          ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))) := rfl
  -- the outer sum is supported in `[-N₀, N₀]`
  have hzero : ∀ x : ℤ, x ∉ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) →
      f₀ x * (∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))) = 0 := by
    intro x hx
    rw [hs0 x (natAbs_le_of_not_mem_Icc hx), zero_mul]
  have hS : (∑' x : ℤ, f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)))
      = ∑ x ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ),
          f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)) :=
    tsum_eq_sum hzero
  -- each summand of the outer sum has modulus at most `N`
  have hterm : ∀ x : ℤ,
      ‖f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖ ≤ (N : ℝ) := by
    intro x
    have hinner : ‖∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖ ≤ (N : ℝ) := by
      calc ‖∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖
          ≤ ∑ y ∈ Finset.Icc 1 N, ‖f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖ := norm_sum_le _ _
        _ ≤ ∑ _y ∈ Finset.Icc 1 N, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro y _
              rw [norm_mul]
              exact (mul_le_mul (hb1 _) (hb2 _) (norm_nonneg _) (by norm_num)).trans (by norm_num)
        _ = (N : ℝ) := by
              rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
              simp
    calc ‖f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖
        = ‖f₀ x‖ * ‖∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖ :=
          norm_mul _ _
      _ ≤ 1 * (N : ℝ) := mul_le_mul (hb0 x) hinner (norm_nonneg _) (by norm_num)
      _ = (N : ℝ) := by ring
  have hcard : (Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)).card = 2 * N₀ + 1 := by
    rw [Int.card_Icc]
    have h1 : (N₀ : ℤ) + 1 - (-(N₀ : ℤ)) = ((2 * N₀ + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, Int.toNat_natCast]
  have hSbound : ‖∑' x : ℤ, f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖
      ≤ (((2 * N₀ + 1) * N : ℕ) : ℝ) := by
    rw [hS]
    calc ‖∑ x ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ),
            f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖
        ≤ ∑ x ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ),
            ‖f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _x ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), (N : ℝ) :=
          Finset.sum_le_sum (fun x _ => hterm x)
      _ = ((Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)).card : ℝ) * N := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (((2 * N₀ + 1) * N : ℕ) : ℝ) := by rw [hcard]; push_cast; ring
  calc ‖Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂‖
      = ‖((N₀ : ℂ) * (N : ℂ))⁻¹‖ *
          ‖∑' x : ℤ, f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖ := by
          rw [hunfold, norm_mul]
    _ = (‖(N₀ : ℂ) * (N : ℂ)‖⁻¹) *
          ‖∑' x : ℤ, f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖ := by
          rw [norm_inv]
    _ = ((N₀ : ℝ) * (N : ℝ))⁻¹ *
          ‖∑' x : ℤ, f₀ x * ∑ y ∈ Finset.Icc 1 N, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))‖ := by
          rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    _ ≤ ((N₀ : ℝ) * (N : ℝ))⁻¹ * (((2 * N₀ + 1) * N : ℕ) : ℝ) := by
          apply mul_le_mul_of_nonneg_left hSbound
          positivity
    _ ≤ 3 := by
          have hN0pos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
          have hstep : ((N₀ : ℝ) * (N : ℝ))⁻¹ * (((2 * N₀ + 1) * N : ℕ) : ℝ)
              = ((2 * N₀ + 1 : ℝ)) / (N₀ : ℝ) := by
            rw [inv_mul_eq_div]
            push_cast
            field_simp
          rw [hstep]
          rw [div_le_iff₀ hN0pos]
          have h1 : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
          linarith

end

end Work.Peluse.Crux
