import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.CubeWindowKinetic` — the **cube-window** vocabulary of the
# one-body kinetic half (FS's single cutoff `χ_B`), and the definitional half of the re-run

Holder of `Submission/Work/BoseFixB1S/LowCountWindowB1copy.lean`.  Companion of
`FINDING_LowCountWindowB1copy_session2.md` §5, which records the *decomposition* of the matched
(single-cube-cutoff) route.

## Why

The *frozen* sliding word `sbWord = sbKin + sbPot` mixes FS's two cutoffs: its kinetic slot carries
the **ball** window `chiB ℓ d u = chiScale ℓ · chiScale (ℓd) (· − (ℓd)u)`, whose small factor
vanishes identically on the corner band (two disjoint balls), while its kernel slot already carries
the **cube** window `chiSmallB M ℓ d u = chiScale ℓ · chiSmall M ((ℓd)⁻¹· − u)`.  FS use *one* cutoff
for both (`eq:chiBdefinition`), and the instruments that pay the pairing (the rung-4 payment, the
Bogoliubov port `Work.BoseFixB1B.slidingBogPort_proved`) are stated at the cube cutoff.  The
matched chapter therefore needs the localisation at the cube cutoff
(`Work.BoseFixB1B.SlidingBCube`, statement-only), whose one-body kinetic half is the re-run of
`Work.BoseFixB1.KH.kineticHalf_le_mainWord` at `chiSmallB`.

## What this module does (the *cheap* half — all definitional/bookkeeping)

* `cubeWin M a u z = chiSmall M (a⁻¹ • z − u)`: the cube-window *small factor* at scale `a` and
  shift `u`, so that `chiSmallB M ℓ d u = chiScale ℓ · cubeWin M (ℓd) u` — the exact cube analogue
  of the corpus's `bsWin a u z = chiScale a (z − a•u)`;
* `tBwordKinInd_cube_eq_bsW`: the sliding spectral slot at the cube window *is* an explicit
  `bsW`-integral of the mean-free, cube-windowed fibre.  The two lemmas it uses
  (`UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm`, `BSKinetic.tBdiagForm_one_eq_bsW`) are **generic in
  the window** given only the support hypothesis, and `chiSmallB`'s support in `dlBox` is PROVED
  (`Work.SlotWord.chiSmallB_support_mem_dlBox`, `1 ≤ M`).  No new analysis;
* `bsOneBodyUnprojCube` / `bsFamilyFormUnprojCube` — the cube analogues of
  `Work.BSKinetic.bsOneBodyUnproj` / `bsFamilyFormUnproj` (the shifted family form), and the
  definitional identity `twoPi_inv_bsW_cubeWin_eq_bsOneBodyUnprojCube`.

## What it does NOT do (the deep half — for the fleet; see §5 of the FINDING)

`Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol` is proved *through*
`Work.BSKinetic.familyFormUnproj_eq_kernelForm`, which is specific to the `bsWin`-family: it
identifies the family form with `∬ convScale ℓ (x−y)·kinKernel F (x−y)·ψx·ψy`, where `convScale ℓ` is
**that family's overlap kernel**, and the symbol comparison (`symA_fsKinCoeff_mix_scaled`, fed by
`con:BSlidingassp`) is a statement about *that* kernel.  The cube family has a *different* overlap
kernel, and pointwise domination does not pass to Fourier space, so the cube route needs its own
`familyFormUnprojCube_eq_kernelForm` and its own symbol comparison at the cube overlap kernel.  The
statements of those two (and of `Work.BoseFixB1S.corrInputCube`, the mean-mismatch at `chiSmallB`)
are the delegation targets recorded in the FINDING.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.UBBInputs8

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The cube small factor -/

/-- The **cube window's small factor** at scale `a` and shift `u`: FS's `χ_B`'s cosine bump,
L²-normalised, in the spelling of the corpus's `chiSmallB`. -/
noncomputable def cubeWin (M : ℕ) (a : ℝ) (u z : E3) : ℝ :=
  Submission.BoseGases.chiSmall M (a⁻¹ • z - u)

/-- The centred spelling: `cubeWin M a u z = chiSmall M (a⁻¹ • (z − a•u))`. -/
lemma cubeWin_eq_centred (M : ℕ) {a : ℝ} (ha : a ≠ 0) (u z : E3) :
    cubeWin M a u z = Submission.BoseGases.chiSmall M (a⁻¹ • (z - a • u)) := by
  rw [cubeWin]
  congr 1
  rw [smul_sub, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- **The factorisation**, the cube analogue of `chiB = chiScale ℓ · bsWin (ℓd) u`: the sliding
window `chiSmallB` is the *big-box* factor times the cube small factor. -/
lemma chiSmallB_eq_chiScale_mul_cubeWin (M : ℕ) (ℓ d : ℝ) (u : E3) :
    Submission.BoseGases.chiSmallB M ℓ d u
      = fun z : E3 => Submission.BoseGases.chiScale ℓ z * cubeWin M (ℓ * d) u z :=
  rfl

/-- `chiSmallB` is supported in the sliding box `dlBox ℓ d u` (contrapositive of the PROVED
`Work.SlotWord.chiSmallB_support_mem_dlBox`). -/
lemma chiSmallB_eq_zero_of_not_mem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) {z : E3} (hz : z ∉ Submission.BoseGases.dlBox ℓ d u) :
    Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
  by_contra h
  exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox (M := M) hM hℓ hd h)

/-! ## 2. The sliding spectral slot at the cube window is an explicit `bsW`-integral

`tBwordKinInd a A volA χ c Ψ = tBdiagFormInd a A volA χ (fsKinCoeff c) Ψ` (definitional), and the
two lemmas below it are window-generic given the support hypothesis. -/

/-- **The cube-window bridge**: the sliding spectral slot at `chiSmallB` is `(2π)⁻³` times the
`bsW`-integral of the mean-free, cube-windowed fibre.  Cube analogue of
`Work.BoseFixB1.KH.tBwordKinInd_eq_bsW'`. -/
theorem tBwordKinInd_cube_eq_bsW {M : ℕ} (hM : 1 ≤ M) {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (φ : X1 → ℝ) :
    Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c φ
      = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z *
            (φ (fun _ : Fin 1 => z)
              - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
                * ∫ z' in Submission.BoseGases.dlBox ℓ d u, φ (fun _ : Fin 1 => z'))) := by
  have hχ : ∀ z : E3, z ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.chiSmallB M ℓ d u z = 0 :=
    fun z hz => chiSmallB_eq_zero_of_not_mem_dlBox hM hℓ hd u hz
  rw [Work.UBBInputs8.tBwordKinInd,
    Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (Submission.BoseGases.fsKinCoeff c) φ hχ,
    Work.BSKinetic.tBdiagForm_one_eq_bsW (a := ℓ) hℓ]

/-! ## 3. The cube shifted family form, and its identification with `bsW` -/

/-- The **cube one-body unprojected form** at shift `u`: the cube analogue of
`Work.BSKinetic.bsOneBodyUnproj`. -/
noncomputable def bsOneBodyUnprojCube (M : ℕ) (a : ℝ) (F : ℝ → ℝ) (u : E3) (ψ : E3 → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : E3, F ‖p‖ * ‖Submission.BoseGases.kinFT
      (fun z : E3 => (cubeWin M a u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2

/-- The **cube family form**: the `u`-integral of the shifted cube forms. -/
noncomputable def bsFamilyFormUnprojCube (M : ℕ) (a : ℝ) (F : ℝ → ℝ) (ψ : E3 → ℝ) : ℝ :=
  ∫ u : E3, bsOneBodyUnprojCube M a F u ψ

/-- **Definitional identification**: `(2π)⁻³·bsW F (cubeWin·ψ)` is the cube unprojected form at the
same shift.  Cube analogue of `Work.BSKinetic.twoPi_inv_bsW_bsWin_eq_bsOneBodyUnproj`. -/
lemma twoPi_inv_bsW_cubeWin_eq_bsOneBodyUnprojCube (M : ℕ) (a : ℝ) (F : ℝ → ℝ) (u : E3)
    (ψ : E3 → ℝ) :
    ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW F (fun z : E3 => cubeWin M a u z * ψ z)
      = bsOneBodyUnprojCube M a F u ψ := by
  have hff : (fun z : E3 => ((cubeWin M a u z * ψ z : ℝ) : ℂ))
      = fun z : E3 => (cubeWin M a u z : ℂ) * (ψ z : ℂ) := by
    funext z
    exact Complex.ofReal_mul _ _
  simp only [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsPsi,
    bsOneBodyUnprojCube, hff]

end Work.BoseFixB1S
