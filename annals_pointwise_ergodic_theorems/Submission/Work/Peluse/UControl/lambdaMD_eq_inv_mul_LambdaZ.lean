import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily

/-!
# The bridge `LambdaMD (C*N₀) = C⁻¹ • LambdaZ N₀`

The multilinear average `LambdaMD` of the *full* polynomial progression
`(x, x + y, x + y², …, x + y^{d-1}, x + P(y))` (`d = P.natDegree ≥ 2`) reduces to Peluse's
bilinear average `LambdaZ` for the progression `(x, x + y, x + P(y))` when all the intermediate
functions `F i` (`2 ≤ i ≤ d-1`) are trivial (`= 1`) on the range on which they are evaluated.
The normalisations differ: `LambdaMD` averages over `N = C * N₀` values of `x` while `LambdaZ`
averages over `N₀`, whence the factor `C⁻¹`.

The range condition is the scale hypothesis `N₀ + M ^ (d - 1) ≤ C * N₀`: for `|x| ≤ N₀`
(supplied by `SupportIn f₀ N₀` and `F 0 = f₀`) and `1 ≤ y ≤ M` one has
`|x + y ^ i| ≤ N₀ + M ^ (d-1) ≤ C * N₀` for every `2 ≤ i ≤ d-1`, which is exactly the range
on which `hmid` makes `F i` equal to `1`.
-/

open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

/-- The identity bridging the multilinear average `LambdaMD` of the full progression and Peluse's
bilinear average `LambdaZ` of `(x, x+y, x+P(y))`. -/
theorem lambdaMD_eq_inv_mul_LambdaZ {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (M C N₀ : ℕ) (hM : 1 ≤ M) (hN₀ : 1 ≤ N₀) (hC : 1 ≤ C)
    (hscale : N₀ + M ^ (P.natDegree - 1) ≤ C * N₀)
    (f₀ f₁ f₂ : ℤ → ℂ) (F : Fin (P.natDegree + 1) → ℤ → ℂ)
    (h0 : F ⟨0, Nat.succ_pos _⟩ = f₀)
    (h1 : F 1 = f₁)
    (hdF : F ⟨P.natDegree, Nat.lt_succ_self _⟩ = f₂)
    (hmid : ∀ (i : Fin (P.natDegree + 1)) (y : ℤ), 2 ≤ (i : ℕ) → (i : ℕ) ≤ P.natDegree - 1 →
      |y| ≤ ((C * N₀ : ℕ) : ℤ) → F i y = 1)
    (hsupp : SupportIn f₀ N₀) :
    LambdaMD (C * N₀) M P F = ((C : ℂ))⁻¹ * LambdaZ N₀ M P f₀ f₁ f₂ := by
  unfold LambdaMD LambdaZ
  -- the scale hypothesis, in `ℤ`
  have hsc : (N₀ : ℤ) + (M : ℤ) ^ (P.natDegree - 1) ≤ ((C * N₀ : ℕ) : ℤ) := by
    exact_mod_cast hscale
  -- `F 1 = f₁` for the `Fin`-index `⟨1, _⟩` used by the product
  have h1' : F (⟨1, by omega⟩ : Fin (P.natDegree + 1)) = f₁ := by
    rw [show (⟨1, by omega⟩ : Fin (P.natDegree + 1)) = 1 from by
      apply Fin.ext; show 1 = 1 % (P.natDegree + 1)
      rw [Nat.mod_eq_of_lt (by omega)], h1]
  -- the pointwise identity of the two `x`-integrands
  have hfun : ∀ x : ℤ,
      (F ⟨0, Nat.succ_pos _⟩ x) * (∑ y ∈ Finset.Icc 1 M,
        (∏ i : Fin (P.natDegree - 1), F ⟨i.val + 1, by omega⟩ (x + (y : ℤ) ^ (i.val + 1)))
          * F ⟨P.natDegree, Nat.lt_succ_self _⟩ (x + P.eval (y : ℤ)))
      = f₀ x * ∑ y ∈ Finset.Icc 1 M, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)) := by
    intro x
    by_cases hx : F ⟨0, Nat.succ_pos _⟩ x = 0
    · -- the summand vanishes at `x`
      have hf0 : f₀ x = 0 := by rw [← h0]; exact hx
      rw [hx, hf0, zero_mul, zero_mul]
    · -- `x` lies in the support of `f₀`, hence `|x| ≤ N₀`
      have hxabs : |x| ≤ (N₀ : ℤ) := by
        have hxle : x.natAbs ≤ N₀ := by
          by_contra h
          have hf0 : f₀ x = 0 := hsupp x (Nat.lt_of_not_le h)
          exact hx (by rw [h0]; exact hf0)
        have h : ((x.natAbs : ℕ) : ℤ) ≤ (N₀ : ℤ) := by exact_mod_cast hxle
        rwa [Int.natCast_natAbs] at h
      have hsum : (∑ y ∈ Finset.Icc 1 M, (∏ i : Fin (P.natDegree - 1),
            F ⟨i.val + 1, by omega⟩ (x + (y : ℤ) ^ (i.val + 1)))
              * F ⟨P.natDegree, Nat.lt_succ_self _⟩ (x + P.eval (y : ℤ)))
          = ∑ y ∈ Finset.Icc 1 M, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ)) := by
        apply Finset.sum_congr rfl
        intro y hy
        have hyM : (y : ℤ) ≤ (M : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hy).2
        -- the range of `x + y ^ k` for `2 ≤ k ≤ d - 1`
        have hbound : ∀ k : ℕ, 2 ≤ k → k ≤ P.natDegree - 1 →
            |x + (y : ℤ) ^ k| ≤ ((C * N₀ : ℕ) : ℤ) := by
          intro k hk2 hkd
          have hpowy : |(y : ℤ) ^ k| ≤ (M : ℤ) ^ (P.natDegree - 1) := by
            rw [abs_of_nonneg (pow_nonneg (by positivity : (0 : ℤ) ≤ (y : ℤ)) k)]
            calc (y : ℤ) ^ k ≤ (M : ℤ) ^ k := pow_le_pow_left₀ (by positivity) hyM k
              _ ≤ (M : ℤ) ^ (P.natDegree - 1) :=
                  pow_le_pow_right₀ (by omega : (1 : ℤ) ≤ (M : ℤ)) hkd
          calc |x + (y : ℤ) ^ k| ≤ |x| + |(y : ℤ) ^ k| := abs_add_le _ _
            _ ≤ (N₀ : ℤ) + (M : ℤ) ^ (P.natDegree - 1) := add_le_add hxabs hpowy
            _ ≤ ((C * N₀ : ℕ) : ℤ) := hsc
        -- the product collapses to its `i = 0` term, which is `F 1`
        have hprod : (∏ i : Fin (P.natDegree - 1),
              F ⟨i.val + 1, by omega⟩ (x + (y : ℤ) ^ (i.val + 1)))
            = F (⟨1, by omega⟩ : Fin (P.natDegree + 1)) (x + (y : ℤ)) := by
          have hfac : ∀ b : Fin (P.natDegree - 1),
              b ≠ (⟨0, by omega⟩ : Fin (P.natDegree - 1)) →
              F ⟨b.val + 1, by omega⟩ (x + (y : ℤ) ^ (b.val + 1)) = 1 := by
            intro b hb
            have hbv : 1 ≤ b.val := by
              have hz : b.val ≠ 0 := by
                intro hz0
                exact hb (Fin.ext (by simpa using hz0))
              omega
            have hk1 : 2 ≤ b.val + 1 := by omega
            have hk2 : b.val + 1 ≤ P.natDegree - 1 := by omega
            have hk3 : b.val + 1 < P.natDegree + 1 := by omega
            refine hmid ⟨b.val + 1, hk3⟩ _ ?_ ?_ ?_
            · show 2 ≤ b.val + 1; exact hk1
            · show b.val + 1 ≤ P.natDegree - 1; exact hk2
            · show |x + (y : ℤ) ^ (b.val + 1)| ≤ ((C * N₀ : ℕ) : ℤ)
              exact hbound (b.val + 1) hk1 hk2
          rw [Finset.prod_eq_single_of_mem (⟨0, by omega⟩ : Fin (P.natDegree - 1))
            (Finset.mem_univ _) (fun b _ hb => hfac b hb)]
          norm_num
        rw [hprod, h1']
        rw [show F ⟨P.natDegree, Nat.lt_succ_self _⟩ (x + P.eval (y : ℤ)) =
            f₂ (x + P.eval (y : ℤ)) from congrFun hdF _]
      rw [hsum, congrFun h0 x]
  rw [tsum_congr hfun]
  -- the two normalising factors
  have hcoef : (((C * N₀ : ℕ) : ℂ) * (M : ℂ))⁻¹ = (C : ℂ)⁻¹ * ((N₀ : ℂ) * (M : ℂ))⁻¹ := by
    rw [show ((C * N₀ : ℕ) : ℂ) * (M : ℂ) = (C : ℂ) * ((N₀ : ℂ) * (M : ℂ)) from by
      push_cast; ring, mul_inv]
  rw [hcoef, mul_assoc]

end Work.Peluse.UControl
