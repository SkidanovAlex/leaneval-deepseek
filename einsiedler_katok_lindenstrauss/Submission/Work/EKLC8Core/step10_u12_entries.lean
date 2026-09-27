/-
Step 10 of `ROUTE_LEAD.md` §5, **the `U_(12)` entries of the sheared displacement**
(EKL §4.5, the two displays (e:boundC) and (e:boundC2)).

`G` is the displacement matrix `g̃ = φ_τ g φ_τ⁻¹`, `κ = κ(G)`, `drift G r` is the maximum
of the three "drift" entries `|(a₂-a₁)r - G₁₀r²|`, `|G₁₂r|`, `|G₂₀r|`, and
`u12max M = max(|M₀₁|, |M₀₂|, |M₂₁|)` is the maximum of the three `U_(12)`-entries.

The entries of `shearMat G r` in the `U_(12)` positions are

  `(shearMat G r)₀₁ = G₀₁ + ((G₁₁-G₀₀)r - G₁₀r²)`,
  `(shearMat G r)₀₂ = G₀₂ + G₁₂r`,
  `(shearMat G r)₂₁ = G₂₁ - G₂₀r`,

so each differs from the corresponding drift term by the "small" entry `G₀₁, G₀₂, G₂₁`
of `G`.  Hence

  `drift G r - δ ≤ u12max (shearMat G r) ≤ drift G r + δ`,

and the claim is immediate from `ρ² ≤ drift ≤ 2ρ⁻¹⁰`, `δ ≤ ρ⁴/4 ≤ ρ²/2` and `δ ≤ 1`.
-/
import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.shearMat_entries

namespace Work.EKLC8Core

theorem step10_u12_entries {ρ δ κ r : ℝ} {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hδ0 : 0 < δ) (hδ : δ ≤ ρ ^ 4 / 4)
    (hκ : 0 < κ) (hκκ : kappa G = κ)
    (hg01 : |G 0 1| ≤ δ) (hg02 : |G 0 2| ≤ δ) (hg21 : |G 2 1| ≤ δ)
    (hlo : ρ ^ 2 ≤ drift G r) (hhi : drift G r ≤ 2 * (ρ⁻¹) ^ 10)
    (hr : |r| * κ ≤ (ρ⁻¹) ^ 5) :
    ρ ^ 2 / 2 ≤ u12max (shearMat G r) ∧ u12max (shearMat G r) ≤ 2 * (ρ⁻¹) ^ 10 + 1 := by
  -- the three `U_(12)`-entries of `shearMat G r`
  have e01 : (shearMat G r) 0 1 = G 0 1 + ((G 1 1 - G 0 0) * r - G 1 0 * r ^ 2) := by
    rw [shearMat_entries]; simp; ring
  have e02 : (shearMat G r) 0 2 = G 0 2 + G 1 2 * r := by
    rw [shearMat_entries]; simp
  have e21 : (shearMat G r) 2 1 = G 2 1 - G 2 0 * r := by
    rw [shearMat_entries]; simp
  -- smallness of `δ`
  have hρ2le : ρ ^ 2 ≤ 1 / 4 := by nlinarith
  have hρ4 : ρ ^ 4 ≤ ρ ^ 2 / 2 := by nlinarith
  have hδhalf : δ ≤ ρ ^ 2 / 2 := by linarith [hδ, hρ4]
  have hδ1 : δ ≤ 1 := by nlinarith
  -- upper bound: each `U_(12)`-entry differs from a drift term by a `G`-entry
  have hM01 : |(shearMat G r) 0 1| ≤ 2 * (ρ⁻¹) ^ 10 + 1 := by
    rw [e01]
    have h1 : |G 0 1 + ((G 1 1 - G 0 0) * r - G 1 0 * r ^ 2)|
        ≤ |G 0 1| + |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| := abs_add_le _ _
    have h2 : |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| ≤ drift G r := by
      simp only [drift]
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hM02 : |(shearMat G r) 0 2| ≤ 2 * (ρ⁻¹) ^ 10 + 1 := by
    rw [e02]
    have h1 : |G 0 2 + G 1 2 * r| ≤ |G 0 2| + |G 1 2 * r| := abs_add_le _ _
    have h2 : |G 1 2 * r| ≤ drift G r := by
      simp only [drift]
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hM21 : |(shearMat G r) 2 1| ≤ 2 * (ρ⁻¹) ^ 10 + 1 := by
    rw [e21]
    have h1 : |G 2 1 - G 2 0 * r| ≤ |G 2 1| + |G 2 0 * r| := by
      calc |G 2 1 - G 2 0 * r| = |G 2 1 + -(G 2 0 * r)| := by rw [sub_eq_add_neg]
        _ ≤ |G 2 1| + |-(G 2 0 * r)| := abs_add_le _ _
        _ = |G 2 1| + |G 2 0 * r| := by rw [abs_neg]
    have h2 : |G 2 0 * r| ≤ drift G r := by
      simp only [drift]
      exact le_max_right _ _
    linarith
  refine ⟨?_, ?_⟩
  · -- lower bound: some drift term is `≥ ρ²`, and the corresponding entry is within `δ`
    have key01 : |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| - |G 0 1|
        ≤ |(shearMat G r) 0 1| := by
      rw [e01]
      have k := abs_sub_abs_le_abs_sub ((G 1 1 - G 0 0) * r - G 1 0 * r ^ 2) (-(G 0 1))
      rw [abs_neg] at k
      have hX : (G 1 1 - G 0 0) * r - G 1 0 * r ^ 2 - -(G 0 1)
          = G 0 1 + ((G 1 1 - G 0 0) * r - G 1 0 * r ^ 2) := by ring
      rwa [hX] at k
    have key02 : |G 1 2 * r| - |G 0 2| ≤ |(shearMat G r) 0 2| := by
      rw [e02]
      have k := abs_sub_abs_le_abs_sub (G 1 2 * r) (-(G 0 2))
      rw [abs_neg] at k
      have hX : G 1 2 * r - -(G 0 2) = G 0 2 + G 1 2 * r := by ring
      rwa [hX] at k
    have key21 : |G 2 0 * r| - |G 2 1| ≤ |(shearMat G r) 2 1| := by
      rw [e21]
      have k := abs_sub_abs_le_abs_sub (-(G 2 0 * r)) (-(G 2 1))
      rw [abs_neg, abs_neg] at k
      have hX : -(G 2 0 * r) - -(G 2 1) = G 2 1 - G 2 0 * r := by ring
      rwa [hX] at k
    have hcases : ρ ^ 2 ≤ |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| ∨
        ρ ^ 2 ≤ |G 1 2 * r| ∨ ρ ^ 2 ≤ |G 2 0 * r| := by
      have h : ρ ^ 2 ≤ max (max |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| |G 1 2 * r|)
          |G 2 0 * r| := hlo
      rcases le_max_iff.mp h with h | h
      · rcases le_max_iff.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    rcases hcases with hD | hD | hD
    · simp only [u12max]
      have : ρ ^ 2 / 2 ≤ |(shearMat G r) 0 1| := by linarith [hD, hg01, key01, hδhalf]
      exact le_trans this (le_trans (le_max_left _ _) (le_max_left _ _))
    · simp only [u12max]
      have : ρ ^ 2 / 2 ≤ |(shearMat G r) 0 2| := by linarith [hD, hg02, key02, hδhalf]
      exact le_trans this (le_trans (le_max_right _ _) (le_max_left _ _))
    · simp only [u12max]
      have : ρ ^ 2 / 2 ≤ |(shearMat G r) 2 1| := by
        have hle : |G 2 0 * r| - δ ≤ |(shearMat G r) 2 1| := by linarith [hg21, key21]
        linarith
      exact le_trans this (le_max_right _ _)
  · simp only [u12max]
    exact max_le (max_le hM01 hM02) hM21

end Work.EKLC8Core
