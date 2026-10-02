/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue team
-/
import Mathlib
import Submission.Work.PARIMPL.Match
import Submission.Work.PARIMPL.Leak
import Submission.Work.FatouCoordFix.All
import Submission.Work.ParamRays.isClosed_filledJulia

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.ParImplGlue` — the `FatouCoord`/leak glue of the implosion side

The ledger `NOTES_LEAD_mandelbar_ledger.md` §2 lists three small glue items among the fields of
`Work.PARIMPL.ParImplInputs`:

* `fix : Work.PARIMPL.FlowerFix d (Ft c₀) (gtc c₀) d.z₁ Pa φa` — the `FatouCoord` fix of §3.1
  (`φa ∘ F = φa + 1` on the petal, together with a `g`-invariant sub-petal `Pg`);
* `zdecay : Work.PARIMPL.ZDecay d Ψ` — the decay `w (Ψ w − z₁) = A + O((1 + log ‖w‖)/‖w‖)` of the
  repelling coordinate at the far end (§A.7 of the flower note);
* `L.deep : ∀ y ∈ closedBall (x* − j₀) r₀, 0 < green c₀ (Ψ y)` — the leak disc is **deep** in the
  escaping region.

This file supplies the first and the third, and reduces the second to the single analytic estimate
`Work.FlowerGlue.zDecay_estimate` (the transfer form of FatouCoordFix's
`Repelling.Z_tendsto_zero`; see `Work.FlowerGlue.zDecay_of_estimate`).

## Why the adapter for `fix` is the whole content

`Work.FatouCoordFix.ParabolicFlowerFix` *is* the repaired flower: it carries `Pg`, its openness, its
`F`- and `g`-invariance and the Abel equation `φa ∘ F = φa + 1` on the whole petal — exactly the
five fields of `Work.PARIMPL.FlowerFix`.  The adapter is therefore a field-by-field transcription
(`Work.FlowerGlue.flowerFixOfFix`); the mathematical content (that the delivered flower has a
`g`-invariant half-petal on which the antiequivariance squares to the Abel equation, and that the
identity theorem then gives it on the whole petal) lives in `Work.FatouCoordFix` and in
`Work.FQC.EcalleData.ofFlower`.
-/

open scoped Topology ComplexConjugate
open Filter Set Metric Function
open Classical

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FlowerGlue

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

noncomputable section

/-! ## 1. The `FatouCoord` fix: the adapter to `Work.PARIMPL.FlowerFix` -/

/-- **The `FatouCoord` fix of the implosion side** (§3.1): the repaired flower's petal, Fatou
coordinate and `g`-invariant half-petal, in the field-by-field form of
`Work.PARIMPL.FlowerFix`. -/
def flowerFixOfFix {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (F c) ((Tantibar c)^[5]) d.z₁) :
    Work.PARIMPL.FlowerFix d (Work.PARIMPL.Ft c) (Work.PARIMPL.gtc c) d.z₁ fl.Pa fl.φa where
  shift := fun z hz => fl.φa_shift z hz
  Pg := fl.Pg
  Pg_sub := fl.Pg_sub
  isOpen_Pg := fl.isOpen_Pg
  mapsTo_F_Pg := fun z hz => fl.mapsTo_F_Pg hz
  mapsTo_G_Pg := fun z hz => fl.mapsTo_g_Pg hz

@[simp] theorem flowerFixOfFix_Pg {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (F c) ((Tantibar c)^[5]) d.z₁) :
    (flowerFixOfFix d fl).Pg = fl.Pg := rfl

/-! ## 2. The leak disc is deep -/

/-- **The leak disc is deep in the escaping region.**  If the equator point `Ψ x*` is not in the
filled Julia set `K c₀` — the ELRig input `Work.EL.equatorLeak` — then, `Ψ` being continuous and
`K c₀` closed, a whole neighbourhood of `x*` is mapped outside `K c₀`; on it the Green function is
positive.

(The ledger asks for the disc `x* − j₀ + …`; the integer shift is *not* needed for the existence of
such a disc at `j₀ = 0` — the shift is used by PARIMPL to place the disc in the outgoing window
`W_out`, and is available because `Ψ (w + 1) = F (Ψ w)` and `K` is totally invariant, see
`Work.PARIMPL.LeakData.deep`.) -/
theorem exists_leakDisc_deep {c₀ : ℂ} {Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) {xstar : ℝ}
    (hleak : Ψ ((xstar : ℝ) : ℂ) ∉ K c₀) :
    ∃ (j₀ : ℤ) (r₀ : ℝ), 0 < r₀ ∧
      ∀ y ∈ closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀,
        0 < Work.Bottcher.green c₀ (Ψ y) := by
  have hmem : ((xstar : ℝ) : ℂ) ∈ Ψ ⁻¹' (K c₀)ᶜ := hleak
  have hopen : IsOpen (Ψ ⁻¹' (K c₀)ᶜ) :=
    (Work.ParamRays.isClosed_filledJulia c₀).isOpen_compl.preimage hΨ
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  refine ⟨0, r / 2, half_pos hr, ?_⟩
  intro y hy
  have hyball : y ∈ Metric.ball ((xstar : ℝ) : ℂ) r := by
    simp only [Metric.mem_closedBall] at hy
    have h' : (((xstar - (((0 : ℤ) : ℝ)) : ℝ)) : ℂ) = ((xstar : ℝ) : ℂ) := by simp
    rw [h'] at hy
    simp only [Metric.mem_ball]
    linarith [hy]
  exact Work.PARIMPL.green_pos_of_notMem_K (hrsub hyball)

/-! ## 3. The `Z`-decay of the repelling coordinate (transfer form) -/

/-- The repelling coordinate in the **transfer form**: the affine image
`Ψ w = z₀ + lam * (-1 / V (w + c))` of the inverse of a germ conjugacy `V`
(`V (w+1) = wMap f (V w)`) transported to the dynamical plane of the family.  This is the
coordinate that `Work.FatouCoord.Flower.transfer_parabolicFlower` (and its repaired copy)
assigns to the flower of `(F, g)` at `z₀`, with `V` the repelling conjugacy of the germ built in
`Work.FatouCoordFix.Repelling`. -/
def repPsiTransfer (z₀ lam c : ℂ) (V : ℂ → ℂ) : ℂ → ℂ :=
  fun w => z₀ + lam * (-1 / V (w + c))

@[simp] theorem repPsiTransfer_apply (z₀ lam c : ℂ) (V : ℂ → ℂ) (w : ℂ) :
    repPsiTransfer z₀ lam c V w = z₀ + lam * (-1 / V (w + c)) := rfl

/-- **The `Z`-decay of the repelling coordinate**, from the estimate
`Work.FlowerGlue.zDecay_estimate`: with `A := -lam ≠ 0` the transferred repelling coordinate is
asymptotically `z₁ + A/w`, with a `(1 + log ‖w‖)/‖w‖` error — the field
`Work.PARIMPL.ZDecay.decay`. -/
def zDecay_of_estimate {c : ℂ} (d : RootParabolic c) {V : ℂ → ℂ} {z₀ lam c₀ : ℂ}
    (hlam : lam ≠ 0) (hz : z₀ = d.z₁) {K : ℝ} (hK : 0 < K)
    (hest : ∀ w : ℂ, w.re < -1 →
      ‖w * (repPsiTransfer z₀ lam c₀ V w - z₀) + lam‖ ≤ K * (1 + Real.log ‖w‖) / ‖w‖) :
    Work.PARIMPL.ZDecay d (repPsiTransfer z₀ lam c₀ V) where
  A := -lam
  A_ne := neg_ne_zero.mpr hlam
  K := K
  decay := by
    intro w hw
    have h := hest w hw
    have harg : w * (repPsiTransfer z₀ lam c₀ V w - d.z₁) - -lam
        = w * (repPsiTransfer z₀ lam c₀ V w - z₀) + lam := by
      rw [hz]
      ring
    rw [harg]
    exact h

end

end Work.FlowerGlue
