/-
# Shared definitions for the `LIP` step of Area A4 (`peluseLipUniform`)

The proof of Proposition `lip` of Krause--Mirek--Tao, §5 (the "alternate inverse theorem for
`f`"), constructs from the inverse-theoretic conclusion of Theorem `pp` a major-arc function `F`
correlating with `f`.  The construction is

`F x = ∑_m w(m) G(x - q m)`,   `w(m) = ε (N')⁻¹ ∑_{m' ∈ [1,N']} ψ(ε(m - m'))`,

where `ψ` is a Schwartz function with `∫ψ = 1` whose Fourier transform is compactly supported,
`G` is the bounded test function dual to the progression average `m ↦ (N')⁻¹ ∑_{m' ∈ [N']} f(x+qm')`
(produced by `exists_bounded_correlation`), and `ε ∈ (0,1]` is the smoothing scale.

This module only fixes the vocabulary (`lipWeight`, `lipWindow`, `smoothOp`) shared by the
delegated lemmas and by the main file.
-/
import Mathlib
import Submission.Work.Analysis.InverseTheory.averaging_smooth
import Submission.Work.Analysis.InverseTheory.Smoothing
import Submission.Work.Analysis.InverseTheory.Transpose
import Submission.Work.Analysis.InverseTheory.AhalfZAPI

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The smoothing weight of Proposition `lip`:
`w(m) = ε (N')⁻¹ ∑_{m' ∈ [1,N']} ψ(ε (m - m'))`. -/
noncomputable def lipWeight (ψ : SchwartzR) (ε : ℝ) (N' : ℕ) : ℤ → ℂ :=
  fun m => (ε : ℂ) * ((N' : ℝ)⁻¹ * ∑ m' ∈ Finset.Icc 1 N', (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ))

/-- The indicator of the window `[1,N']` as a function of `ℤ`, normalised by `(N')⁻¹`: this is the
unsmoothed weight of the progression average. -/
noncomputable def lipWindow (N' : ℕ) : ℤ → ℂ :=
  fun m => ((N' : ℝ)⁻¹ : ℂ) * (if m ∈ Finset.Icc (1 : ℤ) (N' : ℤ) then 1 else 0)

/-- The smoothing operator `x ↦ ∑_m w(m) G(x - Q m)`. -/
noncomputable def smoothOp (w G : ℤ → ℂ) (Q : ℤ) : ℤ → ℂ :=
  fun x => ∑' m : ℤ, w m * G (x - Q * m)


/-- The Schwartz-space Fourier transform, packaged as a plain function of `ℝ` (so that
statements can mention it without opening the `FourierTransform` notation scope). -/
noncomputable def schFT (ψ : SchwartzR) : ℝ → ℂ := fun s => (𝓕 ψ) s

/-- The inverse Schwartz-space Fourier transform, as a plain function of `ℝ`. -/
noncomputable def schInvFT (χ : SchwartzR) : ℝ → ℂ := fun t => (𝓕⁻ χ) t

end Work.KMTAreas.A4
