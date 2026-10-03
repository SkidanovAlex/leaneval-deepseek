import Mathlib
import Submission.Work.Peluse.SwapC.cUBIprodEq

namespace Work.Peluse.SwapC

open scoped BigOperators

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-!
# The concatenation identification in the `I`-form

`concatIdentSumI` is the variant of `concat_ident` in which the *mixed* corners of the corner
family are replaced by the indicator of the window `mixWin x₀ dH0 N = x₀ + dH0 + symIcc (3N)`
(the truncated family `cFunI`), and the box inner product is written as the `mCubeSum` over the
merged direction family `catDir`.

The route is a three-step sandwich:

1. `concat_ident` identifies the doubled `Rest`-product with the box inner product taken with the
   *untruncated* corner family `cUB` (`rw [concat_ident …]`);
2. `mCubeSum_split` unfolds the `mCubeSum` into the quadruple sum with the *truncated* corner family
   `cUBI`, and the two scalar prefactors `(card X)^{-4s}` and `|S|` cancel (they are inverse
   normalisations of the same sum: the `mCubeSum` normalisation `|S|^{-1} (card X)^{-4s}` is exactly
   the reciprocal of the prefactor `|S| · (card X)^{4s}`), leaving the quadruple sum with `cUBI`;
3. the two quadruple sums agree termwise by `cUBIprodEq`: at a mixed corner `cUB` is the constant
   `1` while `cUBI` is the indicator of `mixWin`, and the truncation does not change the value of
   the product, because whenever the product is nonzero the required `3`-point relation
   `z(ε,ε') - x₀ - dH0 = (z(ε,0) - x₀) + (z(0,ε') - x₀) - (z(0,0) + dH0 - x₀)`
   exhibits the mixed evaluation point inside `mixWin` (the three points on the right are forced
   into `x₀ + symIcc N` by the support hypothesis `hsup` and the non-vanishing of the corners
   `(ε,0)`, `(0,ε')`, `(0,0)`).

The only degenerate case is `M = 0` (then `Fin M × Fin M` is empty): for `s = 0` the exponents
`4 * s` and `2 * (2 * s)` both vanish and the normalisations are `1`; for `s ≥ 1` both sides
vanish.
-/

/-- **The concatenation identification, `I`-form.**  The doubled `Rest`-product of the `2s`-slot
cube equals the `mCubeSum` over the merged direction family `catDir`, with the truncated corner
family `cFunI`; the normalisations are inverse, so the `mCubeSum` carries the prefactor
`|S| · (card X)^{4s}`. -/
theorem concatIdentSumI (s M N : ℕ) (qL₁ qL₂ qR₁ qR₂ : Fin s → ℤ) (dH0 dH1 : ℤ) (f : ℤ → ℂ)
    (x₀ : ℤ)
    (hsup : ∀ x : ℤ, x ∉ (Work.Peluse.symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0) :
    (∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
        ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
          ∑' y : ℤ,
            Work.Peluse.SwapC.Rest (Fin.cons dH0 (fun j : Fin s =>
                Work.Peluse.LadderP.Swap.pdir (qL₁ j) (qL₂ j) (k₀ j)
                  - Work.Peluse.LadderP.Swap.pdir (qL₁ j) (qL₂ j) (k₀' j))) f y *
              star (Work.Peluse.SwapC.Rest (Fin.cons dH1 (fun j : Fin s =>
                Work.Peluse.LadderP.Swap.pdir (qR₁ j) (qR₂ j) (k₁ j)
                  - Work.Peluse.LadderP.Swap.pdir (qR₁ j) (qR₂ j) (k₁' j))) f y))
      = ((Work.Peluse.symIcc N).card : ℂ) * ((Fintype.card (Fin M × Fin M) : ℂ) ^ (4 * s)) *
          Work.Peluse.SwapC.mCubeSum (2 * s) (Fin M × Fin M)
            (Work.Peluse.SwapC.catDir M qL₁ qL₂ qR₁ qR₂) (Work.Peluse.symIcc N)
            (Work.Peluse.SwapC.cFunI s f x₀ dH0 dH1 N) := by
  classical
  -- Step 1: the doubled `Rest`-product is the box inner product with the untruncated family `cUB`.
  rw [concat_ident s (Fin M × Fin M) (fun j m => pdir (qL₁ j) (qL₂ j) m)
    (fun j m => pdir (qR₁ j) (qR₂ j) m) f dH0 dH1]
  -- Step 2: unfold the `mCubeSum` along the two halves.
  have hcat : catDir M qL₁ qL₂ qR₁ qR₂
      = fun j => if h : j.val < s then (fun m => pdir (qL₁ ⟨j.val, h⟩) (qL₂ ⟨j.val, h⟩) m)
                 else (fun m => pdir (qR₁ ⟨j.val - s, by omega⟩) (qR₂ ⟨j.val - s, by omega⟩) m) := by
    funext j m
    by_cases h : j.val < s
    · simp only [catDir, dif_pos h]
    · simp only [catDir, dif_neg h]
  have hcf : cFunI s f x₀ dH0 dH1 N = fun ω => cUBI s f x₀ dH0 dH1 N (cL s ω) (cR s ω) := rfl
  rw [hcat, hcf]
  rw [mCubeSum_split s (Fin M × Fin M) (fun j m => pdir (qL₁ j) (qL₂ j) m)
    (fun j m => pdir (qR₁ j) (qR₂ j) m) (Work.Peluse.symIcc N)
    (fun ε ε' => cUBI s f x₀ dH0 dH1 N ε ε')]
  -- Step 3: the two quadruple sums agree termwise (truncation of the mixed corners).
  have hprod : (∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
        ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M, ∑' y : ℤ,
          ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool, (star^[weight ε + weight ε'])
            (cUBI s f x₀ dH0 dH1 N ε ε'
              (y + cornerShift (fun j => pdir (qL₁ j) (qL₂ j) (k₀ j))
                     (fun j => pdir (qL₁ j) (qL₂ j) (k₀' j)) ε
                 + cornerShift (fun j => pdir (qR₁ j) (qR₂ j) (k₁ j))
                     (fun j => pdir (qR₁ j) (qR₂ j) (k₁' j)) ε')))
      = (∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
        ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M, ∑' y : ℤ,
          ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool, (star^[weight ε + weight ε'])
            (cUB s f dH0 dH1 ε ε'
              (y + cornerShift (fun j => pdir (qL₁ j) (qL₂ j) (k₀ j))
                     (fun j => pdir (qL₁ j) (qL₂ j) (k₀' j)) ε
                 + cornerShift (fun j => pdir (qR₁ j) (qR₂ j) (k₁ j))
                     (fun j => pdir (qR₁ j) (qR₂ j) (k₁' j)) ε'))) := by
    refine Finset.sum_congr rfl (fun k₀ _ => ?_)
    refine Finset.sum_congr rfl (fun k₀' _ => ?_)
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    refine Finset.sum_congr rfl (fun k₁' _ => ?_)
    exact tsum_congr (fun y => cUBIprodEq s x₀ dH0 dH1 N f hsup _ _ _ _ y)
  rw [hprod]
  -- Step 4: the scalar normalisations are inverse to each other.
  have hS : ((Work.Peluse.symIcc N).card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, by simp [Work.Peluse.symIcc]⟩)
  have key : ∀ (a b T : ℂ) (m : ℕ), a ≠ 0 → b ≠ 0 →
      a * b ^ m * (a⁻¹ * (b⁻¹) ^ m * T) = T := by
    intro a b T m ha hb
    have h2 : b ^ m * (b⁻¹) ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hb, one_pow]
    calc a * b ^ m * (a⁻¹ * (b⁻¹) ^ m * T)
        = (a * a⁻¹) * (b ^ m * (b⁻¹) ^ m) * T := by ring
      _ = 1 * 1 * T := by rw [mul_inv_cancel₀ ha, h2]
      _ = T := by ring
  by_cases hM : M = 0
  · -- `M = 0`: the index type `Fin M × Fin M` is empty.
    rw [hM] at *
    have hc0 : (Fintype.card (Fin 0 × Fin 0) : ℂ) = 0 := by simp
    rw [hc0]
    rcases Nat.eq_zero_or_pos s with hs | hs
    · -- `s = 0`: both exponents vanish, and the normalisations are `1`.
      subst hs
      simp only [Nat.mul_zero, pow_zero, mul_one]
      rw [← mul_assoc, mul_inv_cancel₀ hS, one_mul]
    · -- `s ≥ 1`: both sides vanish (the outer sums are empty).
      have hT : (∑ k₀ : Fin s → Fin 0 × Fin 0, ∑ k₀' : Fin s → Fin 0 × Fin 0,
          ∑ k₁ : Fin s → Fin 0 × Fin 0, ∑ k₁' : Fin s → Fin 0 × Fin 0, ∑' y : ℤ,
            ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool, (star^[weight ε + weight ε'])
              (cUB s f dH0 dH1 ε ε'
                (y + cornerShift (fun j => pdir (qL₁ j) (qL₂ j) (k₀ j))
                       (fun j => pdir (qL₁ j) (qL₂ j) (k₀' j)) ε
                   + cornerShift (fun j => pdir (qR₁ j) (qR₂ j) (k₁ j))
                       (fun j => pdir (qR₁ j) (qR₂ j) (k₁' j)) ε'))) = 0 := by
        have hempty : (Finset.univ : Finset (Fin s → Fin 0 × Fin 0)) = ∅ :=
          Finset.univ_eq_empty_iff.mpr ⟨fun x => Fin.elim0 ((x ⟨0, hs⟩).1)⟩
        rw [hempty, Finset.sum_empty]
      rw [hT]
      simp only [mul_zero]
  · -- `M ≠ 0`: cancel the two normalisations.
    have hX : ((Fintype.card (Fin M × Fin M) : ℂ)) ≠ 0 := by
      have h : Fintype.card (Fin M × Fin M) ≠ 0 := by
        rw [Fintype.card_prod, Fintype.card_fin]
        exact Nat.mul_ne_zero hM hM
      exact_mod_cast h
    rw [show 2 * (2 * s) = 4 * s from by ring]
    exact (key _ _ _ _ hS hX).symm

end

end Work.Peluse.SwapC
