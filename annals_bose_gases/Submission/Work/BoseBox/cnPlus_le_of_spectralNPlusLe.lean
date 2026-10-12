import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.Nodes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox

/-- **The `m = 1` instance of the spectral window: the expectation bound.**

`Work.BoseBox.SpectralNPlusLe ℓ 𝓜 Φ` is FS `eq:LocalizedNPlus`
`1_{[0,𝓜]}(n₊)Φ = Φ` in the all-moments form `⟨Φ, n₊^mΦ⟩ ≤ 𝓜^m‖Φ‖²` (`m : ℕ`), where
`n₊ = Σᵢ aQ ℓ i` (`Work.BoseBox.nPlusFun`, `Work.BoseBox.nPlusPow`).  Its `m = 1` instance,
together with the self-adjointness and idempotence of the corpus's mean-free projections `aQ`,
gives the *expectation* window used throughout FS §8–§11:

    `cnPlus ℓ Φ ≤ 𝓜 · norm2N N ℓ Φ`,

i.e. `⟨n₊⟩ ≤ 𝓜‖Φ‖²` (`cnPlus ℓ Φ = Σᵢ∫_{abox N ℓ}(aQ ℓ i Φ)² = Σᵢ⟨Φ, QᵢΦ⟩`).  The ingredients
are the corpus's `aP_idem`/`aP_sym_box`/`aQ_ortho_box` (`Submission.CentredSector`), which give
`∫ (QᵢΦ)·Φ = ∫ (QᵢΦ)²`; `Continuous Φ` is required for those (integrability and the exchange of
the finite sum with the integral).  (`Work.UBBInputs4.cnPlus_eq_qform_nPlus` is the same
identity, in a module not imported here.) -/
theorem cnPlus_le_of_spectralNPlusLe {N : ℕ} {ℓ 𝓜 : ℝ} (hℓ : 0 < ℓ) (h𝓜 : 0 ≤ 𝓜)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (h : Work.BoseBox.SpectralNPlusLe ℓ 𝓜 Φ) :
    Submission.BoseGases.cnPlus ℓ Φ ≤ 𝓜 * Work.BoseBox.norm2N N ℓ Φ := by
  -- Step 1: `cnPlus` is the quadratic form of `n₊ = Σᵢ Qᵢ`, i.e.
  -- `cnPlus ℓ Φ = ∫_{abox N ℓ} (nPlusFun ℓ Φ) · Φ`.
  have hq : Submission.BoseGases.cnPlus ℓ Φ
      = ∫ x in Submission.BoseGases.abox N ℓ, nPlusFun ℓ Φ x * Φ x := by
    simpa [nPlusFun] using
      (Work.UBBInputs4.cnPlus_eq_qform_nPlus (N := N) (L := ℓ) hℓ hΦc)
  -- Step 2: the `m = 1` instance of the all-moments spectral window.
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ, nPlusFun ℓ Φ x * Φ x)
      ≤ 𝓜 * ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
    have hspec := h 1
    simpa [nPlusPow, nPlusFun, norm2N] using hspec
  rw [hq]
  simpa [norm2N] using h1

end Work.BoseBox
