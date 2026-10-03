import Mathlib
import Submission.Work.KMTPlan.A6.MdlTleKer

namespace Work.KMTAreas.A7Hi

/-- **Link 1 of the `l = 0` pipeline: at arithmetic height `0` the IW projection is the plain convolution operator.**

`Work.KMTAreas.A7.Tle ρ 0 φ = Work.KMTAreas.A7.convOp (Work.KMTAreas.A7.cw φ)` for `φ` integrable against Lebesgue measure (`Integrable φ MeasureTheory.volume`, matching the `∫` used in the definition of `cw`).

Proof recipe (verified: the reviewer compiled the statement and reports the proof goes through verbatim): `Work.KMTPlan.A6.Tle_eq_convOp_TleKer` is **pointwise** (`∀ f`), so start with `funext f`; then `Work.KMTPlan.A6.TleKer_eq_arChar_cw ρ 0 hφ i` gives `TleKer ρ 0 φ i = TleArChar ρ 0 i * cw φ i`; and `TleArChar ρ 0 i = 1` by `simp [TleArChar, iwArithFreqs, iwP]` — `Work.Analysis.IonescuWainger.iwC0 (ρ : ℝ) : ℕ` is a natural, so `iwP ρ 0 = Finset.Icc 1 (2 ^ 0) = {1}` and `iwArithFreqs ρ 0 = {(0 : Circle)}`, whence the character sum is `fourier (T := 1) (-i) 0 = 1`.

Traps found while drafting: (a) qualify `iwArithFreqs`/`iwP` as `Work.Analysis.IonescuWainger.…` — there is a same-named second copy under `Work.BourgainPlan.IonescuWainger`, and the bare names are ambiguous; (b) the integrability hypothesis must carry its measure explicitly.

Use: turns the plain family `T n = convOp (cw Φ n)` into the form `Tle ρ 0 (Φ n)` consumed by `Work.KMTAreas.A7.varEst_of_uniformSigns_of_measurable` (via Link 2, the sampling transfer, §6.10 of `NOTES_A7Hi_LinVarG_SESSION.md`). -/
theorem Tle_zero_eq_convOp_cw {φ : ℝ → ℂ} (hφ : MeasureTheory.Integrable φ MeasureTheory.volume)
    (ρ : ℝ) :
    Work.KMTAreas.A7.Tle ρ 0 φ = Work.KMTAreas.A7.convOp (Work.KMTAreas.A7.cw φ) := by
  -- At height `0` the arithmetic frequency set is the single frequency `0`, so the
  -- arithmetic character sum of `T^{≤0}` is identically `1`.
  have hAr : ∀ i : ℤ, Work.KMTPlan.A6.TleArChar ρ 0 i = 1 := fun i => by
    simp [Work.KMTPlan.A6.TleArChar, Work.Analysis.IonescuWainger.iwArithFreqs,
      Work.Analysis.IonescuWainger.iwP]
  -- Hence the kernel of `T^{≤0}_φ` is the continuous Fourier transform of `φ`.
  have hker : Work.KMTPlan.A6.TleKer ρ 0 φ = Work.KMTAreas.A7.cw φ := by
    funext i
    rw [Work.KMTPlan.A6.TleKer_eq_arChar_cw ρ 0 hφ i, hAr i, one_mul]
  -- `Tle` is by definition the convolution with `TleKer`, and `congr` in the kernel.
  funext f
  rw [Work.KMTPlan.A6.Tle_eq_convOp_TleKer, hker]

end Work.KMTAreas.A7Hi
