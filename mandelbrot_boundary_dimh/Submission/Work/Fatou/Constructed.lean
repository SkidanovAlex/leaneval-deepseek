import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# FX8: the constructed Fatou coordinate, as a hypothesis package

`Work.Fatou.fatouU` (uniformization route) obtains the Fatou coordinate as `Φ = Ψ ∘ Π / b`, where
`Π : Qreg b₁ b₂ → XF D` is the "orbit projection" (fundamental-strip representative + level, from
`Work.Fatou.Surface.orbitCoord`) and `Ψ : XF D ≃ₘ ℂ` is the uniformizing biholomorphism.  The
output of that construction is exactly the following package:

* `IsFatouCoordOn F Φ (Qreg b₁ b₂)`: `Φ` is holomorphic, injective, and satisfies the Abel
  equation `Φ (F z) = Φ z + 1` whenever `z, F z ∈ Qreg b₁ b₂`;
* surjectivity modulo `ℤ` (Shishikura A.2.3: the cylinder `𝒬/⟨F⟩` is `ℂ/ℤ`): every `w : ℂ` is
  `Φ z - n` for some `z ∈ Qreg b₁ b₂` and `n : ℤ`;
* the **orbit relation for `Φ`** (A.2.1(i)): `Φ z' = Φ z + k` (`k : ℕ`) forces `z' = F^[k] z` with
  all intermediate iterates in `Qreg b₁ b₂`.

The orbit relation is *not* a formal consequence of `IsFatouCoordOn` and surjectivity modulo `ℤ`
for an arbitrary pair, but it is available for the constructed `Φ` (it is read off from `Π`,
which is injective on `Qreg` and satisfies `Π (F z) = Π z + 1`).

Downstream files (uniqueness, orbit, continuity, ends) take `FatouConstructed` as a hypothesis so
that they do not have to depend on the uniformization library at all.
-/

namespace Work.Fatou

open MandelDim

noncomputable section

/-- The output of the FX8 construction: a Fatou coordinate with the orbit relation. -/
def HasFatouCoordOrbit (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) : Prop :=
  ∃ Φ : ℂ → ℂ,
    MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂) ∧
    (∀ w : ℂ, ∃ z ∈ MandelDim.Qreg b₁ b₂, ∃ n : ℤ, Φ z = w + n) ∧
    (∀ z ∈ MandelDim.Qreg b₁ b₂, ∀ z' ∈ MandelDim.Qreg b₁ b₂, ∀ k : ℕ, Φ z' = Φ z + k →
      (∀ j ≤ k, F^[j] z ∈ MandelDim.Qreg b₁ b₂) ∧ F^[k] z = z')

/-- FX8 for all parameters: every near-translation on an admissible Shishikura region admits the
constructed Fatou coordinate, with the orbit relation. -/
def FatouConstructed : Prop :=
  ∀ (b₁ b₂ : Option ℂ) (F : ℂ → ℂ), MandelDim.QAdm b₁ b₂ →
    MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂) → HasFatouCoordOrbit b₁ b₂ F

/-- `FatouConstructed` gives the existence half of the FATOU contract. -/
theorem fatouExists_of_constructed (h : FatouConstructed) : MandelDim.FatouExists := by
  intro b₁ b₂ F hadm hNT
  obtain ⟨Φ, hΦ, hsurj, -⟩ := h b₁ b₂ F hadm hNT
  exact ⟨Φ, hΦ, hsurj⟩

end

end Work.Fatou
