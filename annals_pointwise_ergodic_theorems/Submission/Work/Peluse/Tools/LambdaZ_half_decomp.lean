/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Nodes

/-!
# The halving identity for the bilinear average `Λ^{N,M}`

Peluse's paper (and Krause–Mirek–Tao's §5) use the elementary observation that the average over
the full range `[M]` of the `y`-variable splits into the average over the *upper half*
`y ∈ (M/2, M]` — which is exactly the workspace's `AhalfZ` / `LambdaHalfZ` — plus a multiple
(with coefficient `⌊M/2⌋/M ≤ 1/2`) of the average over the range `[⌊M/2⌋]`:

`Λ^{N,M}_{y,P}(f₀,f₁,f₂) = Λ^{(1/2),N,M}_{y,P}(f₀,f₁,f₂) + θ · Λ^{N,⌊M/2⌋}_{y,P}(f₀,f₁,f₂)`,
`‖θ‖ ≤ 1/2`.

Indeed `[M] = (M/2, M] ⊔ [M/2]` as a disjoint union of `ℕ`-intervals, so with
`θ = ⌊M/2⌋ / M` the identity is a rewriting of

`(1/(NM)) ∑_{y ∈ [M/2]} g(y) = (⌊M/2⌋/M) · (1/(N·⌊M/2⌋)) ∑_{y ∈ [M/2]} g(y)`.

The only point needing care is the case `⌊M/2⌋ = 0` (`M ≤ 1`), where the last subscript of
`Λ` is `0`: then the corresponding sum is empty and both sides vanish (`0⁻¹ = 0` in `ℂ`), so
the statement holds with the same value of `θ = 0`.

## Contents

* `core` : the integrand `f₁(x+y) f₂(x+P(y))` of the `y`-sum;
* `sum_Icc_split` : `∑_{y ∈ [M]} = ∑_{y ∈ (M/2,M]} + ∑_{y ∈ [M/2]}`;
* `summable_range_Ioc` / `summable_range_Icc` : the two `x`-summands are finitely supported
  (because `f₀` is), hence summable, so the `tsum` may be split;
* `half_coeff_norm_le` / `half_coeff_algebra` : the two facts about the coefficient
  `θ = ⌊M/2⌋ * M⁻¹` (norm bound and the exact rewriting of the prefactor);
* `LambdaZ_half_decomp` : the halving identity.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Tools

noncomputable section

/-- The integrand `f₁ (x + y) * f₂ (x + P(y))` of the `y`-sum in `LambdaZ`. -/
private def core (P : Polynomial ℤ) (f₁ f₂ : ℤ → ℂ) (x : ℤ) (y : ℕ) : ℂ :=
  f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))

/-- The `y`-range of the average splits as the upper half `(M/2, M]` together with `[M/2]`. -/
private lemma sum_Icc_split (M : ℕ) (g : ℕ → ℂ) :
    ∑ y ∈ Finset.Icc 1 M, g y
      = ∑ y ∈ Finset.Ioc (M / 2) M, g y + ∑ y ∈ Finset.Icc 1 (M / 2), g y := by
  have hdisj : Disjoint (Finset.Ioc (M / 2) M) (Finset.Icc 1 (M / 2)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [Finset.mem_Ioc] at hy1
    simp only [Finset.mem_Icc] at hy2
    omega
  have hunion : Finset.Ioc (M / 2) M ∪ Finset.Icc 1 (M / 2) = Finset.Icc 1 M := by
    ext y; simp only [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [← hunion, Finset.sum_union hdisj]

/-- The upper-half `x`-summand is finitely supported, hence summable. -/
private lemma summable_range_Ioc {N₀ M : ℕ} (P : Polynomial ℤ) (f₀ f₁ f₂ : ℤ → ℂ)
    (hs0 : Work.Peluse.SupportIn f₀ N₀) :
    Summable (fun x : ℤ => f₀ x * ∑ y ∈ Finset.Ioc (M / 2) M, core P f₁ f₂ x y) := by
  apply summable_of_hasFiniteSupport
  refine (Set.finite_Icc (-(N₀ : ℤ)) (N₀ : ℤ)).subset ?_
  intro x hx
  rw [Function.mem_support] at hx
  simp only [Set.mem_Icc]
  by_contra h
  exact hx (by simp [hs0 x (by omega)])

/-- The lower-half `x`-summand is finitely supported, hence summable. -/
private lemma summable_range_Icc {N₀ M : ℕ} (P : Polynomial ℤ) (f₀ f₁ f₂ : ℤ → ℂ)
    (hs0 : Work.Peluse.SupportIn f₀ N₀) :
    Summable (fun x : ℤ => f₀ x * ∑ y ∈ Finset.Icc 1 (M / 2), core P f₁ f₂ x y) := by
  apply summable_of_hasFiniteSupport
  refine (Set.finite_Icc (-(N₀ : ℤ)) (N₀ : ℤ)).subset ?_
  intro x hx
  rw [Function.mem_support] at hx
  simp only [Set.mem_Icc]
  by_contra h
  exact hx (by simp [hs0 x (by omega)])

/-- The coefficient `⌊M/2⌋ / M` has norm at most `1/2`. -/
private lemma half_coeff_norm_le (M : ℕ) : ‖(((M / 2 : ℕ) : ℂ) * (M : ℂ)⁻¹)‖ ≤ 1 / 2 := by
  by_cases hM : M = 0
  · subst hM; norm_num
  · have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
    rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast, ← div_eq_mul_inv]
    rw [div_le_iff₀ hMpos]
    have h1 : ((M / 2 : ℕ) : ℝ) ≤ (M : ℝ) / 2 := Nat.cast_div_le
    linarith

/-- The exact arithmetic of the halving: multiplying the `[⌊M/2⌋]`-average by `θ = ⌊M/2⌋/M`
reproduces the prefactor `(N₀ M)⁻¹` of the full average.  (This needs `⌊M/2⌋ ≠ 0`; when
`⌊M/2⌋ = 0` the corresponding sum is empty and the identity is handled separately.) -/
private lemma half_coeff_algebra {N₀ M : ℕ} (hm : M / 2 ≠ 0) (z : ℂ) :
    ((N₀ : ℂ) * (M : ℂ))⁻¹ * z
      = (((M / 2 : ℕ) : ℂ) * (M : ℂ)⁻¹) * (((N₀ : ℂ) * ((M / 2 : ℕ) : ℂ))⁻¹ * z) := by
  have hm0 : ((M / 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm
  have hM0 : (M : ℂ) ≠ 0 := by
    have : M ≠ 0 := fun h => hm (by rw [h])
    exact_mod_cast this
  field_simp

/-- **The halving identity** for Peluse's bilinear average:
`Λ^{N,M} = Λ^{(1/2),N,M} + θ Λ^{N,⌊M/2⌋}` with `‖θ‖ ≤ 1/2`. -/
theorem LambdaZ_half_decomp {N₀ M : ℕ} (hN₀ : 0 < N₀) (hM : 0 < M) (P : Polynomial ℤ)
    (f₀ f₁ f₂ : ℤ → ℂ) (hs0 : Work.Peluse.SupportIn f₀ N₀) (hs1 : Work.Peluse.SupportIn f₁ N₀)
    (hs2 : Work.Peluse.SupportIn f₂ N₀) :
    ∃ θ : ℂ, ‖θ‖ ≤ 1 / 2 ∧
      Work.Peluse.LambdaZ N₀ M P f₀ f₁ f₂
        = Work.Peluse.LambdaHalfZ N₀ M P f₀ f₁ f₂
          + θ * Work.Peluse.LambdaZ N₀ (M / 2) P f₀ f₁ f₂ := by
  classical
  -- the two halves of the `x`-sum
  set B : ℤ → ℂ := fun x => f₀ x * ∑ y ∈ Finset.Ioc (M / 2) M, core P f₁ f₂ x y with hB
  set C : ℤ → ℂ := fun x => f₀ x * ∑ y ∈ Finset.Icc 1 (M / 2), core P f₁ f₂ x y with hC
  have hsumB : Summable B := by
    rw [hB]; exact summable_range_Ioc P f₀ f₁ f₂ hs0
  have hsumC : Summable C := by
    rw [hC]; exact summable_range_Icc P f₀ f₁ f₂ hs0
  -- the full average is the sum of the two halves
  have hmain : Work.Peluse.LambdaZ N₀ M P f₀ f₁ f₂
      = ((N₀ : ℂ) * (M : ℂ))⁻¹ * (∑' x, B x + ∑' x, C x) := by
    rw [Work.Peluse.LambdaZ]
    congr 1
    rw [← hsumB.tsum_add hsumC]
    apply tsum_congr
    intro x
    simp only [hB, hC, core]
    rw [sum_Icc_split M (fun y : ℕ => f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)))]
    ring
  have hHalf : Work.Peluse.LambdaHalfZ N₀ M P f₀ f₁ f₂
      = ((N₀ : ℂ) * (M : ℂ))⁻¹ * ∑' x, B x := by
    rw [Work.Peluse.LambdaHalfZ]; simp only [hB, core]
  have hThird : Work.Peluse.LambdaZ N₀ (M / 2) P f₀ f₁ f₂
      = ((N₀ : ℂ) * ((M / 2 : ℕ) : ℂ))⁻¹ * ∑' x, C x := by
    rw [Work.Peluse.LambdaZ]; simp only [hC, core]
  refine ⟨((M / 2 : ℕ) : ℂ) * (M : ℂ)⁻¹, half_coeff_norm_le M, ?_⟩
  rw [hmain, hHalf, hThird]
  -- only the lower half needs the arithmetic of the coefficient
  have hkey : ((N₀ : ℂ) * (M : ℂ))⁻¹ * (∑' x, C x)
      = (((M / 2 : ℕ) : ℂ) * (M : ℂ)⁻¹) *
          (((N₀ : ℂ) * ((M / 2 : ℕ) : ℂ))⁻¹ * (∑' x, C x)) := by
    by_cases hm : M / 2 = 0
    · -- then the lower half is empty
      have hz : (∑' x, C x) = 0 := by
        have hzero : C = fun _ => 0 := by
          funext x; simp only [hC, hm]; simp
        rw [hzero]; exact tsum_zero
      rw [hz]; simp
    · exact half_coeff_algebra hm _
  rw [← hkey]
  ring

end

end Work.Peluse.Tools
