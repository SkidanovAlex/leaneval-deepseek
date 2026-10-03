import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouL1.Surface.orbitCoord

/-!
# Orbit data for a near-translation on `Qreg b₁ b₂` (Shishikura A.2.1(i))

STATEMENT UNCHANGED.  This file proves `Work.FatouL1.orbitData` — the packaging of Shishikura
A.2.1(i) with an explicit *orbit coordinate* `(rep, lev)`: every point of `𝒬 = Qreg b₁ b₂` has a
canonical representative in the fundamental strip `fundStrip F 𝒬 x₀` together with an integer
level, satisfying

* `rep z ∈ fundStrip F 𝒬 x₀` for `z ∈ 𝒬`;
* `rep z = z` and `lev z = 0` for `z ∈ fundStrip F 𝒬 x₀`;
* `rep (F z) = rep z` and `lev (F z) = lev z + 1` whenever `z` and `F z` are both in `𝒬`;
* `(rep, lev)` is injective on `𝒬`;
* `z` and `rep z` lie on a common orbit piece contained in `𝒬`.

The argument is the one already formalised in this workspace as
`Work.FatouL1.Surface.orbitCoord` (namespace `Work.Fatou.Surface`): existence of a representative
comes from Shishikura's fundamental-strip theorem `MandelDim.FatouFundamental`
(`Work.Fatou.Qreg.fatouFundamental`), uniqueness of the pair `(representative, signed level)`
from `Work.Fatou.Surface.meetFund` / `meetUniqTarget`, and the step compatibility from
`Work.Fatou.Surface.specSucc`.  That lemma has the identical type, so the proof below is an
immediate application; its import closure contains only
`Work.Interfaces.Fatou` and `Work.Fatou.Qreg.*` / `Work.Fatou.Surface.{orbitDefs,meetFund,
meetUniqTarget,specSucc}` — in particular **no** uniformization library and no `Work.FatouCH`
dependency (`#print axioms` gives `propext, Classical.choice, Quot.sound`).
-/

namespace Work.FatouL1

/-- Shishikura A.2.1(i) in orbit-coordinate form (statement as requested, unchanged). -/
theorem orbitData {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ (rep : ℂ → ℂ) (lev : ℂ → ℤ),
      (∀ z ∈ MandelDim.Qreg b₁ b₂, rep z ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀) ∧
      (∀ z ∈ MandelDim.Qreg b₁ b₂, z ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀ →
        rep z = z ∧ lev z = 0) ∧
      (∀ z ∈ MandelDim.Qreg b₁ b₂, F z ∈ MandelDim.Qreg b₁ b₂ →
        rep (F z) = rep z ∧ lev (F z) = lev z + 1) ∧
      (∀ z ∈ MandelDim.Qreg b₁ b₂, ∀ z' ∈ MandelDim.Qreg b₁ b₂,
        rep z = rep z' → lev z = lev z' → z = z') ∧
      (∀ z ∈ MandelDim.Qreg b₁ b₂, ∃ k : ℕ,
        (F^[k] z = rep z ∧ ∀ j ≤ k, F^[j] z ∈ MandelDim.Qreg b₁ b₂) ∨
        (F^[k] (rep z) = z ∧ ∀ j ≤ k, F^[j] (rep z) ∈ MandelDim.Qreg b₁ b₂)) :=
  Work.FatouL1.Surface.orbitCoord hadm hF h₁ h₂

end Work.FatouL1
