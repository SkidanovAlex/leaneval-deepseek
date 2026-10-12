import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.cnPlus_le_bigM_mul`

The `m = 1` instance of the corpus's **spectral** `n₊`-window
(`Work.BoseBox.SpectralNPlusLe`, FS `eq:LocalizedNPlus`): the expectation bound

    `cnPlus ℓ Φ ≤ 𝓜 · ∫_{abox n ℓ} Φ²`   whenever `SpectralNPlusLe ℓ 𝓜 Φ`.

`cnPlus ℓ Φ = Σᵢ ∫_{abox n ℓ} (QᵢΦ)²` is the excited-particle count, and
`SpectralNPlusLe ℓ 𝓜 Φ` says `⟨Φ, n₊^m Φ⟩ ≤ 𝓜^m‖Φ‖²` for every `m`, where
`n₊ = Σᵢ Qᵢ` (`Work.BoseBox.nPlusFun`).  The `m = 1` instance is
`∫ (Σᵢ QᵢΦ)·Φ ≤ 𝓜 ∫Φ²`; since each `Qᵢ` is the orthogonal projection onto the
mean-free functions (`aQ_ortho_box`, i.e. `∫ (QᵢΦ)·Φ = ∫ (QᵢΦ)²`), the quadratic
form `∫ (Σᵢ QᵢΦ)·Φ` *equals* the sum of `L²`-norms `cnPlus ℓ Φ`
(`Work.UBBInputs4.cnPlus_eq_qform_nPlus`).  Substituting gives the claim.

No sign hypothesis on `𝓜` is needed: the inequality `h 1` is used as it stands,
and its left-hand side is *identified* with `cnPlus ℓ Φ`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- **The `m = 1` spectral window**: if the state `Φ` is spectrally confined to
`[0, 𝓜]` for the excited-particle operator `n₊ = Σᵢ Qᵢ`
(`Work.BoseBox.SpectralNPlusLe ℓ 𝓜 Φ`), then the excited count is at most
`𝓜 ‖Φ‖²`. -/
theorem cnPlus_le_bigM_mul {n : ℕ} {ℓ 𝓜 : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) (h : Work.BoseBox.SpectralNPlusLe ℓ 𝓜 (N := n) Φ) :
    Submission.BoseGases.cnPlus ℓ Φ ≤ 𝓜 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  -- Step 1: `cnPlus` is the quadratic form of `n₊ = Σᵢ Qᵢ`.
  have hq : Submission.BoseGases.cnPlus ℓ Φ
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (∑ i : Fin n, Submission.BoseGases.aQ ℓ i Φ x) * Φ x :=
    Work.UBBInputs4.cnPlus_eq_qform_nPlus (N := n) (L := ℓ) hℓ hΦc
  rw [hq]
  -- Step 2: the `m = 1` instance of the all-moments spectral window.
  have h1 := h 1
  simpa [Work.BoseBox.nPlusPow, Work.BoseBox.nPlusFun, pow_one] using h1

end Work.BoseBoxFock
