import ChallengeDeps
import Submission.Work.BoseFixB1.BoxA2
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1B.sectorCountDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.rungDefs` — the vocabulary of the missing rungs

Read `Submission/Work/BoseFixB1B/FINDING_sectorCountSmallboxBox.md` (sections on the count core)
together with `FINDING_perBoxCrudeLowerB1_status.md` §3, `FINDING_sharpA2Sliding.md` and
`FINDING_boxBogCoreSliding_FALSE.md`.

This module carries (i) the corpus vocabulary the rung statements use, in one import point, and
(ii) the abbreviation `PairMass h` for FS's `ĝω(0) = ∫g₀ω` — the *LHY kernel mass*, which is
`Submission.BoseGases.g0w0Mass` written out (the definitional bridge `PairMass_eq_g0w0Mass` is
`rfl`).

`PairMass h` is the coefficient of FS's *sharp row*
`½(1+δ)·ĝω(0)·((n+1)n/|B|²)·∫χ_B²` in `eq:simpleaprioribog` (`final_v2.tex` l. 3762–3780), i.e.
of the payer that has to absorb the negativity of the pairing word `A₂` in
`lm:appbogolubov`.  At FS's parameters `PairMass h > 0` (the Born gap), which is what makes the
row able to cancel the `½μ²`-deficit of the target at the *resonance* `n/|B| ≈ μ`; see
`Work.BoseFixB1B.pairMass_pos` (the delegated positivity) and the FINDING §AM.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **FS's `ĝω(0)`** — the LHY kernel mass `∫ z, g₀(z)·ω(z)` at the chosen radial scattering
solution `ω = Classical.choose h` (`g₀ = v(1−ω)`).  Definitionally
`Submission.BoseGases.g0w0Mass h`. -/
noncomputable def PairMass {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : ℝ :=
  ∫ z : E3, Submission.BoseGases.g0 v h z * Classical.choose h z

/-- The definitional bridge to the corpus's name. -/
lemma PairMass_eq_g0w0Mass {v : E3 → ℝ} (h : Work.UBB.ScatSol v) :
    PairMass h = Submission.BoseGases.g0w0Mass h := rfl

/-- **The standing hypotheses of the target** at the sliding data: `u` is in the good set, `Φ` is
supported in the box `B(u)` (a.e., on `abox n ℓ`), and `Φ` is normalised there.  These are
verbatim the hypotheses of `Work.BoseFixB1B.SectorCountSmallboxBox` (`boxSupp`/`boxNorm` plus
`u ∈ goodSet`), packaged so that the rung statements below can name them. -/
def BoxStateHyp (v : E3 → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3) : Prop :=
  u ∈ goodSet (PBℓ v μ) (PBd v μ) μ ∧
    (∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (PBℓ v μ))),
      (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 → ∀ i : Fin n, x i ∈ PBB v μ u) ∧
    (∫ x in Submission.BoseGases.abox n (PBℓ v μ),
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1

end Work.BoseFixB1B
