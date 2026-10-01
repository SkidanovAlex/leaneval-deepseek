import Mathlib

namespace Work.LinnikAreas

/-- Summing a nonnegative, finitely-supported `g : ℂ → ℝ` over the second
coordinates of a finset of pairs `(χ, ·)` never exceeds the full `finsum` of
`g` over `ℂ`: the second-coordinate map is injective on such a finset. -/
theorem finset_sum_snd_le_finsum {ι : Type*} (T : Finset (ι × ℂ)) (χ : ι)
    (g : ℂ → ℝ) (h1 : ∀ z ∈ T, z.1 = χ) (hg : ∀ ρ, 0 ≤ g ρ)
    (hfin : (Function.support g).Finite) :
    (∑ z ∈ T, g z.2) ≤ ∑ᶠ ρ : ℂ, g ρ := by
  classical
  -- The second-coordinate map is injective on `T` because the first coordinate
  -- is forced to be `χ`.
  have hinj : Set.InjOn (fun z : ι × ℂ => z.2) ↑T := by
    intro x hx y hy h
    exact Prod.ext (by rw [h1 x hx, h1 y hy]) h
  -- Replace the sum over `T` by a sum over the image of the second coordinate.
  rw [← Finset.sum_image (g := (fun z : ι × ℂ => z.2)) hinj]
  set A := T.image (fun z : ι × ℂ => z.2) with hA
  -- Extend the sum over `A` to the sum over `A ∩ support g` (adds only zeroes).
  have hAeq : ∑ ρ ∈ A ∩ hfin.toFinset, g ρ = ∑ ρ ∈ A, g ρ := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro x hxA hxnot
    have hx' : x ∉ hfin.toFinset := fun h => hxnot (Finset.mem_inter.mpr ⟨hxA, h⟩)
    simpa [Set.Finite.mem_toFinset, Function.mem_support] using hx'
  rw [← hAeq]
  -- Now enlarge `A ∩ support g` to `support g`, using nonnegativity of `g`.
  have hle : ∑ ρ ∈ A ∩ hfin.toFinset, g ρ ≤ ∑ ρ ∈ hfin.toFinset, g ρ :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun i _ _ => hg i)
  -- Identify the `finsum` with the sum over the support.
  have hfs : ∑ᶠ ρ : ℂ, g ρ = ∑ ρ ∈ hfin.toFinset, g ρ :=
    finsum_eq_sum_of_support_subset g (by rw [Set.Finite.coe_toFinset])
  exact le_trans hle (le_of_eq hfs.symm)

end Work.LinnikAreas
