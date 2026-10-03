import Mathlib
import Submission.Work.FatouL1.crux
import Submission.Work.FatouCH.fatouCH

/-!
# `Work.FatouL1.fatouCoordExistsL1` — the seed of the narrow (`L¹`) FATOU area

## The statement (fixed; defined in `crux.lean`)

`Work.FatouL1.FatouCoordExistsL1` is Shishikura, Prop. A.2.1 (ii), in the `L¹` setting:

  for every admissible pair `b₁ b₂` and every near-translation `F` on `𝒬 = Qreg b₁ b₂` whose
  derivative defect is `L¹` along the vertical lines of `𝒬`, there is a **Fatou coordinate**
  `Φ : 𝒬 → ℂ` — holomorphic, injective, with `Φ (F z) = Φ z + 1` whenever `z, F z ∈ 𝒬`.

Nothing quantitative is required here (no bound on `Φ'`, no surjectivity mod `ℤ`, no orbit
relation): this is the *qualitative seed* of the narrow area.  It is also literally the seed of
the workspace: `Work.FatouL1.fatouCoord` (`fatouDerivSetup.lean`) is
`Classical.choose (fatouCoordExistsL1 b₁ b₂ F hadm hF)`, and every quantitative lemma of the
directory (`fatouSecondDerivWideBound`, `cocycleCorrectionWide`, `localAbelWide`,
`ChartOnWide`, hence `fatouL1` / `FatouStatementL1`) is derived from the resulting
`IsFatouCoordOn` property — with `fatouCoord` opaque, *only* that property is used.  Hence any
correct proof of this statement is a drop-in replacement for `cruxTemp.lean`'s placeholder, and
makes the whole 275-module `fatouL1` chain `sorryAx`-free.

## Which proof is used here, and the resulting caveat

* **Narrow (`L¹`, uniformization-free) route** — the one this area was designed for.  By the
  equivalence noted in `NOTES_FINDINGS_session13.md`: this statement is *equivalent*, relative to
  the already-proved machinery of the directory, to `ChartOnWide` for every datum (the chain
  `seed → fatouSecondDerivWideBound → cocycleCorrectionWide → localAbelWide → ChartOnWide` is the
  proof of one direction, and `hasFatouCoordOrbitL1_of_chart` — which is *not* circular, its
  closure contains neither `fatouDerivSetup` nor `cruxTemp` — the other).  So a narrow proof must
  solve the genuinely *sharp* small-`μ` cocycle problem on the wide strip: numerically the truth is
  `‖σ - 1‖ ≤ 1/31` and `ChartOnWide` tolerates only `≲ 1/26`, while the crude estimates
  (`flowModelDefect`'s `‖μ‖ ≤ 1/100` together with the `≤ 2`-step orbits inside the strip) give
  `≈ 0.039 > 1/26`.  That sharp statement is the open crux of the area (sessions 3–13; the lead's
  §3 "flow model" lead in `NOTES_FINDINGS_session13.md` is the current attack).  The proof below
  deliberately **does not** use any of the area's conditional machinery, so it cannot be circular.
* **Uniformization route** — the proof used below.  `Work.FatouCH.fatouCH : MandelDim.FatouStatement`
  is a proved, axiom-clean theorem of this workspace (`#print axioms` = `propext,
  Classical.choice, Quot.sound`), obtained by uniformizing the Écalle cylinder `𝒬/⟨F⟩`; the bridge
  `MandelDim.fatouL1_of_fatou : FatouStatement → FatouStatementL1` is proved in the fixed interface
  file `Submission/Work/Interfaces/FatouNarrow.lean`.  This is Shishikura's own strategy at the
  level of ideas: his proof of A.2.1 (ii) straightens the explicit quasiconformal chart
  `h₁ (x+iy) = (1-x)(z₀+iy) + x·F(z₀+iy)` with the Ahlfors–Bers measurable Riemann mapping
  theorem, i.e. by uniformization.

**Caveat (resource, not mathematics).**  The closure of this module therefore contains
`Submission/Lib/Unif2` (~674 modules).  The project lead's *budget* rule for this area (≤ ~40
`Unif2` modules; see `NOTES_FINDINGS_session12.md` §0) is respected by every other module of
`Submission/Work/FatouL1`, and the narrow chain `fatouL1` is `Unif2`-free *except* through this
seed.  Concretely: **do not** simply re-point `fatouDerivSetup.lean` at this module without
checking `REFS/closure_check.py` first — it prints `Submission.Lib.Unif2 = 674` for this file
(versus `31` for the area), so the lead's budget test will flag it.  If the sharp cocycle lands,
replace the three lines of the proof below by

    obtain ⟨x₀, h₁, h₂, hchart⟩ := ...            -- `exists_wideStrip` + a chart on the wide strip
    obtain ⟨Φ, hΦ, -⟩ := hasFatouCoordOrbitL1_of_chart hadm hF h₁ h₂ hchart
    exact ⟨Φ, hΦ⟩

(or, from `Work.FatouL1.existsFlatConjugacy`, by `existsFatouCoord_of_flatConjugacy`), and this
module becomes a `Unif2`-free, budget-conforming drop-in replacement with exactly the same name and
statement.  Nothing else in the directory has to change.

## Build hygiene

`cruxTemp.lean` declares the *same* name (`Work.FatouL1.fatouCoordExistsL1`, with `sorry`);
this module deliberately does not import it (nor anything importing it), so the two coexist as
separate modules and the lead's switch (§5 of `NOTES_FINDINGS_session13.md`:
delete `cruxTemp.lean`, re-point the two imports in `fatouDerivSetup.lean` and
`fatouDerivBoundedStrip.lean`) works once the budget question above is settled.
-/

namespace Work.FatouL1

/-- **Shishikura A.2.1 (ii), `L¹` form: the qualitative seed of the narrow FATOU area.** -/
theorem fatouCoordExistsL1 : Work.FatouL1.FatouCoordExistsL1 := by
  intro b₁ b₂ F hadm hF
  -- `FatouStatement` (uniformization route) ⟹ `FatouStatementL1` (proved bridge) ⟹ `FatouExistsL1`.
  obtain ⟨Φ, hΦ, -⟩ := (MandelDim.fatouL1_of_fatou Work.FatouCH.fatouCH).1 b₁ b₂ F hadm hF
  exact ⟨Φ, hΦ⟩

end Work.FatouL1
