import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The van der Corput weight `μ_L` has total mass one

Peluse's weight `μ_L(h) = #{h₁, h₂ ∈ [L] : h₁ - h₂ = h}/L²` (`Work.Peluse.muL`) is the
distribution of the difference of two independent uniform points of `[L] = {1, …, L}`.
This file proves the normalisation `∑_{h ∈ ℤ} μ_L(h) = 1` for `L ≥ 1`.

The sum is really finite: `μ_L` vanishes off `[1-L, L-1]`, because the difference of two
elements of `[L]` lies in that interval.  On that interval the fibres of the map
`(h₁, h₂) ↦ h₁ - h₂ : [L]² → ℤ` partition the `L²` pairs of `[L]²`, so the mass is
`L²/L² = 1`.
-/

namespace Work.Peluse.MuL

open scoped BigOperators

/-- `[L] × [L]` has `L²` elements. -/
private lemma card_prod_Icc (L : ℕ) :
    ((Finset.Icc 1 L).product (Finset.Icc 1 L)).card = L * L := by
  rw [Finset.product_eq_sprod, Finset.card_product, Nat.card_Icc]
  have h : L + 1 - 1 = L := by omega
  rw [h]

/-- The difference of two points of `[L]²` lies in `[1-L, L-1]`, which is exactly the support
interval of `μ_L`. -/
private lemma diff_mem_Icc (L : ℕ) :
    ∀ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L),
      (p.1 : ℤ) - (p.2 : ℤ) ∈ Finset.Icc (1 - (L : ℤ)) ((L : ℤ) - 1) := by
  intro p hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
  obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.mp h1
  obtain ⟨h2a, h2b⟩ := Finset.mem_Icc.mp h2
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩ <;> omega

theorem muL_tsum (L : ℕ) (hL : 1 ≤ L) : ∑' h : ℤ, Work.Peluse.muL L h = 1 := by
  -- `μ_L` vanishes off its support interval `[1-L, L-1]`.
  have hsupp : ∀ h ∉ Finset.Icc (1 - (L : ℤ)) ((L : ℤ) - 1),
      Work.Peluse.muL L h = 0 := by
    intro h hh
    have hfilt : ((Finset.Icc 1 L).product (Finset.Icc 1 L)).filter
        (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp hpeq
      exact hh (hpeq ▸ diff_mem_Icc L p hp)
    unfold Work.Peluse.muL
    rw [hfilt]
    simp
  rw [tsum_eq_sum hsupp]
  -- The fibres of `(h₁, h₂) ↦ h₁ - h₂` over the support interval partition `[L]²`.
  have hfiber : (((Finset.Icc 1 L).product (Finset.Icc 1 L)).card)
      = ∑ h ∈ Finset.Icc (1 - (L : ℤ)) ((L : ℤ) - 1),
          (((Finset.Icc 1 L).product (Finset.Icc 1 L)).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card :=
    Finset.card_eq_sum_card_fiberwise (diff_mem_Icc L)
  have hrewrite : (∑ h ∈ Finset.Icc (1 - (L : ℤ)) ((L : ℤ) - 1), Work.Peluse.muL L h)
      = ((L : ℝ) ^ 2)⁻¹ * (((Finset.Icc 1 L).product (Finset.Icc 1 L)).card : ℝ) := by
    calc ∑ h ∈ Finset.Icc (1 - (L : ℤ)) ((L : ℤ) - 1), Work.Peluse.muL L h
        = ∑ h ∈ Finset.Icc (1 - (L : ℤ)) ((L : ℤ) - 1),
            ((L : ℝ) ^ 2)⁻¹ *
              ((((Finset.Icc 1 L).product (Finset.Icc 1 L)).filter
                (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro h _
          unfold Work.Peluse.muL
          rfl
      _ = ((L : ℝ) ^ 2)⁻¹ *
            ∑ h ∈ Finset.Icc (1 - (L : ℤ)) ((L : ℤ) - 1),
              ((((Finset.Icc 1 L).product (Finset.Icc 1 L)).filter
                (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card : ℝ) :=
          (Finset.mul_sum _ _ _).symm
      _ = ((L : ℝ) ^ 2)⁻¹ *
            (((∑ h ∈ Finset.Icc (1 - (L : ℤ)) ((L : ℤ) - 1),
                (((Finset.Icc 1 L).product (Finset.Icc 1 L)).filter
                  (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card) : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
      _ = ((L : ℝ) ^ 2)⁻¹ * (((Finset.Icc 1 L).product (Finset.Icc 1 L)).card : ℝ) := by
          rw [hfiber]
  rw [hrewrite, card_prod_Icc, Nat.cast_mul, pow_two]
  exact inv_mul_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega)))

end Work.Peluse.MuL
