import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Rewriting a `μ_L`-weighted sum as a double sum over `[L]²`

Peluse's weight `μ_L(h) = #{h₁,h₂ ∈ [L] : h₁ - h₂ = h}/L²` is the distribution of the
difference of two independent uniform points of `[L] = {1, …, L}`.  Consequently, for *any*
function `φ : ℤ → ℂ`,

  `∑_{h ∈ [-L,L]} μ_L(h) φ(h) = L⁻² ∑_{h₁,h₂ ∈ [L]} φ(h₁ - h₂)`,

which is the exact form of the weight needed in van der Corput's inequality (Peluse §2): the
weighted average of `φ` against `μ_L` equals the plain average of `φ` over all differences
coming from pairs in `[L]²`.

The proof is pure finite double counting: the fibres of `(h₁,h₂) ↦ h₁ - h₂` over `[-L,L]`
partition `[L]²` (they are empty at `±L`), so an exchange of summation turns the sum over
differences, weighted by the fibre cardinality, into the sum over pairs.

Outside the support `[1-L, L-1] ⊆ [-L,L]` of `μ_L` the weight is zero, so summing over the
larger interval `[-L,L]` loses nothing.
-/

set_option linter.unusedVariables false

namespace Work.Peluse.VanDerCorput

open scoped BigOperators

/-- **Van der Corput weight, unfolded.**  The `μ_L`-weighted sum equals `L⁻²` times the sum of
`φ` over all differences `h₁ - h₂` of pairs in `[L]²`. -/
theorem sum_muL_mul_eq {H : ℕ} (hH : 0 < H) (φ : ℤ → ℂ) :
    ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), (Work.Peluse.muL H h : ℂ) * φ h =
      ((H : ℂ) ^ 2)⁻¹ * ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
        φ ((p.1 : ℤ) - (p.2 : ℤ)) := by
  -- Every difference of two points of `[H]²` lies in the summation interval `[-H,H]`.
  have hmem : ∀ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
      (p.1 : ℤ) - (p.2 : ℤ) ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.mp h1
    obtain ⟨h2a, h2b⟩ := Finset.mem_Icc.mp h2
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩ <;> omega
  -- The cardinality of a fibre of `(h₁,h₂) ↦ h₁ - h₂`, as a sum of indicators.
  have hcard_eq : ∀ h : ℤ,
      ((((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
        (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card : ℂ)
      = ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
          (if (p.1 : ℤ) - (p.2 : ℤ) = h then (1:ℂ) else 0) := by
    intro h
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    simp
  -- Unfolding `μ_L` and pushing the cast `ℝ → ℂ`.
  have hmuL : ∀ h : ℤ, (Work.Peluse.muL H h : ℂ) =
      ((H : ℂ) ^ 2)⁻¹ * ((((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
        (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card : ℂ) := by
    intro h; unfold Work.Peluse.muL; push_cast; rfl
  calc ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), (Work.Peluse.muL H h : ℂ) * φ h
      = ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          ((H : ℂ) ^ 2)⁻¹ *
            (((((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
              (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card : ℂ) * φ h) := by
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [hmuL h]
        ring
    _ = ((H : ℂ) ^ 2)⁻¹ *
          ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
            ((((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
              (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card : ℂ) * φ h :=
        (Finset.mul_sum _ _ _).symm
    _ = ((H : ℂ) ^ 2)⁻¹ * ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
          φ ((p.1 : ℤ) - (p.2 : ℤ)) := by
        congr 1
        -- Rewrite the weighted sum over differences as a sum over the pairs themselves.
        calc ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
              ((((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
                (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card : ℂ) * φ h
            = ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
                (∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
                  (if (p.1 : ℤ) - (p.2 : ℤ) = h then (1:ℂ) else 0)) * φ h := by
              refine Finset.sum_congr rfl ?_; intro h _; rw [hcard_eq h]
          _ = ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
                ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
                  (if (p.1 : ℤ) - (p.2 : ℤ) = h then (1:ℂ) else 0) * φ h := by
              refine Finset.sum_congr rfl ?_; intro h _
              rw [Finset.sum_mul]
          _ = ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
                ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
                  (if (p.1 : ℤ) - (p.2 : ℤ) = h then (1:ℂ) else 0) * φ h :=
              Finset.sum_comm
          _ = ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
                ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
                  (if (p.1 : ℤ) - (p.2 : ℤ) = h then φ h else 0) := by
              refine Finset.sum_congr rfl ?_; intro p _
              refine Finset.sum_congr rfl ?_; intro h _
              by_cases hh : (p.1 : ℤ) - (p.2 : ℤ) = h
              · rw [if_pos hh, if_pos hh]; ring
              · rw [if_neg hh, if_neg hh]; ring
          _ = ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
                φ ((p.1 : ℤ) - (p.2 : ℤ)) := by
              refine Finset.sum_congr rfl ?_; intro p hp
              rw [Finset.sum_ite_eq, if_pos (hmem p hp)]

end Work.Peluse.VanDerCorput
