import Submission.Work.Interfaces.Fatou

/-!
# FATOU, narrow contract (lead, insurance route without the uniformization library)

`FatouStatementL1` is `FatouStatement` with every `NearTranslationOn F Q` hypothesis strengthened to
`NearTranslationL1 F Q`: in addition, on every vertical line inside `Q`,
`∫ ‖F' - 1‖ dy ≤ 1/64` (as a `lintegral`, so divergence is `⊤`, never junk).  This is exactly what
the perturbation layer feeds in (for `F_f = w + 1 + O(|τ_f|)`, `F_f' - 1 = O(|τ_f||τ_f - σ|)`, the
line integrals are `O(1/ξ₁)`; for the unperturbed `F₀ = w + 1 + 1/(w-1)` on `x > ξ₁` they are
`≈ π/x`).  It allows a construction by the multiplicative cocycle `log ψ'` and the periodic
Cauchy–Heine operator, with no uniformization theorem.  `fatouL1_of_fatou` shows the old contract
implies the new one, so consumers may switch freely.
-/

open Set Filter Metric Complex MeasureTheory
open scoped Topology

namespace MandelDim

noncomputable section

/-- Near-translation with integrable derivative defect on vertical lines inside `Q`. -/
def NearTranslationL1 (F : ℂ → ℂ) (Q : Set ℂ) : Prop :=
  NearTranslationOn F Q ∧ ∀ x : ℝ, (∀ y : ℝ, (x : ℂ) + y * I ∈ Q) →
    ∫⁻ y : ℝ, ENNReal.ofReal ‖deriv F ((x : ℂ) + y * I) - 1‖ ≤ ENNReal.ofReal (1 / 64)

/-- `FatouExists` with the narrow (L¹) near-translation hypothesis. -/
def FatouExistsL1 : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F : ℂ → ℂ), QAdm b₁ b₂ → NearTranslationL1 F (Qreg b₁ b₂) →
    ∃ Φ : ℂ → ℂ, IsFatouCoordOn F Φ (Qreg b₁ b₂) ∧
      ∀ w : ℂ, ∃ z ∈ Qreg b₁ b₂, ∃ n : ℤ, Φ z = w + n

/-- `FatouOrbit` with the narrow (L¹) near-translation hypothesis. -/
def FatouOrbitL1 : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F Φ : ℂ → ℂ), QAdm b₁ b₂ → NearTranslationL1 F (Qreg b₁ b₂) →
    IsFatouCoordOn F Φ (Qreg b₁ b₂) →
    ∀ z ∈ Qreg b₁ b₂, ∀ z' ∈ Qreg b₁ b₂, ∀ k : ℕ, Φ z' = Φ z + k →
      (∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) ∧ F^[k] z = z'

/-- `FatouUnique` with the narrow (L¹) near-translation hypothesis. -/
def FatouUniqueL1 : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F Φ₁ Φ₂ : ℂ → ℂ), QAdm b₁ b₂ → NearTranslationL1 F (Qreg b₁ b₂) →
    IsFatouCoordOn F Φ₁ (Qreg b₁ b₂) → IsFatouCoordOn F Φ₂ (Qreg b₁ b₂) →
    ∃ c : ℂ, ∀ z ∈ Qreg b₁ b₂, Φ₂ z = Φ₁ z + c

/-- `FatouContinuity` with the narrow (L¹) near-translation hypothesis. -/
def FatouContinuityL1 : Prop :=
  ∀ (b₁ b₂ : ℕ → Option ℂ) (c₁ c₂ : Option ℂ) (F : ℕ → ℂ → ℂ) (F₀ : ℂ → ℂ)
    (Φ : ℕ → ℂ → ℂ) (Φ₀ : ℂ → ℂ) (z₀ : ℂ),
    (∀ n, QAdm (b₁ n) (b₂ n)) → QAdm c₁ c₂ →
    (∀ n, NearTranslationL1 (F n) (Qreg (b₁ n) (b₂ n))) → NearTranslationL1 F₀ (Qreg c₁ c₂) →
    (∀ K ⊆ Qreg c₁ c₂, IsCompact K →
      (∀ᶠ n in atTop, K ⊆ Qreg (b₁ n) (b₂ n)) ∧ TendstoUniformlyOn F F₀ atTop K) →
    (∀ n, IsFatouCoordOn (F n) (Φ n) (Qreg (b₁ n) (b₂ n))) → IsFatouCoordOn F₀ Φ₀ (Qreg c₁ c₂) →
    z₀ ∈ Qreg c₁ c₂ → (∀ᶠ n in atTop, Φ n z₀ = Φ₀ z₀) →
    ∀ K ⊆ Qreg c₁ c₂, IsCompact K → TendstoUniformlyOn Φ Φ₀ atTop K

/-- `FatouEnds` with the narrow (L¹) near-translation hypothesis. -/
def FatouEndsL1 : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F Φ : ℂ → ℂ) (ρ : ℂ) (M κ Y : ℝ), QAdm b₁ b₂ →
    NearTranslationL1 F (Qreg b₁ b₂) → IsFatouCoordOn F Φ (Qreg b₁ b₂) →
    0 < κ → ‖ρ - 1‖ ≤ 1 / 32 →
    ((∀ z ∈ Qreg b₁ b₂, Y < z.im → ‖F z - (z + ρ)‖ ≤ M * Real.exp (-(κ * z.im))) →
      ∃ c : ℂ, ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Qreg b₁ b₂, Y' < z.im → |z.re - x| ≤ 2 →
        ‖Φ z - z / ρ - c‖ < ε) ∧
    ((∀ z ∈ Qreg b₁ b₂, z.im < -Y → ‖F z - (z + ρ)‖ ≤ M * Real.exp (κ * z.im)) →
      ∃ c : ℂ, ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Qreg b₁ b₂, z.im < -Y' → |z.re - x| ≤ 2 →
        ‖Φ z - z / ρ - c‖ < ε)

/-- THE NARROW FATOU CONTRACT. -/
def FatouStatementL1 : Prop :=
  FatouExistsL1 ∧ FatouOrbitL1 ∧ FatouUniqueL1 ∧ FatouContinuityL1 ∧ FatouDerivEstimate ∧
    FatouEndsL1

theorem fatouL1_of_fatou (h : FatouStatement) : FatouStatementL1 := by
  obtain ⟨hE, hO, hU, hC, hD, hN⟩ := h
  refine ⟨?_, ?_, ?_, ?_, hD, ?_⟩
  · intro b₁ b₂ F hQ hF; exact hE b₁ b₂ F hQ hF.1
  · intro b₁ b₂ F Φ hQ hF; exact hO b₁ b₂ F Φ hQ hF.1
  · intro b₁ b₂ F Φ₁ Φ₂ hQ hF; exact hU b₁ b₂ F Φ₁ Φ₂ hQ hF.1
  · intro b₁ b₂ c₁ c₂ F F₀ Φ Φ₀ z₀ h1 h2 h3 h4
    exact hC b₁ b₂ c₁ c₂ F F₀ Φ Φ₀ z₀ h1 h2 (fun n => (h3 n).1) h4.1
  · intro b₁ b₂ F Φ ρ M κ Y hQ hF; exact hN b₁ b₂ F Φ ρ M κ Y hQ hF.1

/-! ## Weighted variant (lead, 09-28): the hypothesis a Banach-fixed-point existence proof needs

The multiplicative-cocycle construction `ψ' = e^g`, `Δg = log F' ∘ ψ_g` has `δψ` growing linearly in
`|Im|` between iterates (the end slopes of `ψ` are dictated by the limits of `F - id` at the two
ends), so its contraction estimate needs the `|y|`-weighted mass of `F''` on vertical lines.  This
holds for every map the perturbation layer feeds in (`F_f'' = O(|w|^{-3})` away from the lattice
`ℤ/α`, so the weighted line mass is `O(1/ξ₁)`; for `F₀ = w + 1 + 1/(w-1)` it is `≈ 2/x`). -/

/-- `|Im|`-weighted smallness of `F''` on the vertical lines inside `Q`. -/
def WeightedL1 (F : ℂ → ℂ) (Q : Set ℂ) : Prop :=
  ∀ x : ℝ, (∀ y : ℝ, (x : ℂ) + y * I ∈ Q) →
    ∫⁻ y : ℝ, ENNReal.ofReal ((1 + |y|) * ‖deriv (deriv F) ((x : ℂ) + y * I)‖) ≤
      ENNReal.ofReal (1 / 64)

/-- Existence with the extra weighted hypothesis. -/
def FatouExistsL1W : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F : ℂ → ℂ), QAdm b₁ b₂ → NearTranslationL1 F (Qreg b₁ b₂) →
    WeightedL1 F (Qreg b₁ b₂) →
    ∃ Φ : ℂ → ℂ, IsFatouCoordOn F Φ (Qreg b₁ b₂) ∧
      ∀ w : ℂ, ∃ z ∈ Qreg b₁ b₂, ∃ n : ℤ, Φ z = w + n

/-- The narrow contract with weighted existence (insurance route, see NOTES_LEAD_fatou). -/
def FatouStatementL1W : Prop :=
  FatouExistsL1W ∧ FatouOrbitL1 ∧ FatouUniqueL1 ∧ FatouContinuityL1 ∧ FatouDerivEstimate ∧
    FatouEndsL1

theorem fatouL1W_of_fatouL1 (h : FatouStatementL1) : FatouStatementL1W := by
  obtain ⟨hE, hO, hU, hC, hD, hN⟩ := h
  exact ⟨fun b₁ b₂ F hQ hF _ => hE b₁ b₂ F hQ hF, hO, hU, hC, hD, hN⟩

end

end MandelDim
