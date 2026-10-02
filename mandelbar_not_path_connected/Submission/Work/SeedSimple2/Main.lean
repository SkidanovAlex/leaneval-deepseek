/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — the assembly: `FSeedInput` from `NonCuspRootLimit` and the portrait

`NOTES_LEAD_mandelbar_seed.md` §3.5 and §6.3, item 7.  The cited clause `NonCuspRootLimit` is
discharged by the SeedExist area, which produces every field of `Work.FSeed.RootParabolicInput`
*except* the local ray portrait `portrait`.  This file isolates that production as
`RootInputNoPortrait`/`SeedData` and adds the portrait from `TwoRays.lean`:

* `rotationZero` (`RN0`) and `gfixedAvoid` (`GF`) are the two geometric inputs of `TwoRays.lean`
  — they are the *content* of §4.2's items `RN0` and `GF`, to be produced by the corresponding
  lemmas of this area (files `Rotation/`, `GFixed/`);
* `unlinkedLemma` (`U`) is `Unlinked/unlinked_of_coLands.lean`;
* the finite certificate `C` is `Cert.lean` (proved).

The theorem `fSeedInput_of_hypotheses` then returns `Work.FSeed.FSeedInput`, exactly the input of
`Work.FSeed.Classify`, with the `portrait` field now *proved* rather than cited.
-/
import Submission.Work.SeedSimple2.TwoRays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Function
open scoped Topology

noncomputable section

namespace Work.SeedSimple2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The unlinked lemma `U`** of §4.2, as a standing hypothesis: two co-landing pairs at
*distinct* points are unlinked.  (`Unlinked/unlinked_of_coLands.lean`, and the discharge
`unlinkedLemma_proved` in `UnlinkedBridge.lean`.) -/
def unlinkedLemma (hJ : Work.Top.JordanForm) : Prop :=
  ∀ {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {a b a' b' : ℝ} {w w' : ℂ}, w ≠ w' →
    a ∈ Set.Ico 0 1 → b ∈ Set.Ico 0 1 → a' ∈ Set.Ico 0 1 → b' ∈ Set.Ico 0 1 →
    Work.EL.LandsN hN a w → Work.EL.LandsN hN b w → Work.EL.LandsN hN a' w' →
    Work.EL.LandsN hN b' w' → PairwiseDistinct4 a b a' b' →
    Work.ELPull.Unlinked a b a' b'

/-- **Rotation number zero** (`RN0` of §4.2): every angle landing at the root point is fixed by
the angle map `θ ↦ 1024 θ mod 1`. -/
def rotationZero : Prop :=
  ∀ {c : ℂ} (d : Work.EL.RootParabolic c),
    ∀ θ ∈ LandAngles d.hN d.z₁, Int.fract (1024 * θ) = θ

/-- **`GF`** of §4.2: the `g`-fixed rays avoid the wake arc `(α₁, α₂)`. -/
def gfixedAvoid : Prop :=
  ∀ {c : ℂ} (d : Work.EL.RootParabolic c), ∀ θ ∈ LandAngles d.hN d.z₁, IsGFixed θ →
    ¬ Work.ELPull.InArc θ Work.EL.alpha1 Work.EL.alpha2

/-- **`Work.FSeed.RootParabolicInput` without the `portrait` field**: exactly the bundle the
SeedExist area builds from the cited clause (§3.5), the portrait being the contribution of this
area. -/
structure RootInputNoPortrait (c : ℂ) where
  /-- Böttcher's theorem in the dynamical plane. -/
  dyn : Work.FSeed.DynHomeo c
  /-- the characteristic parabolic point. -/
  z₁ : ℂ
  /-- `c` is a limit point of `R(α₁)` but not on it. -/
  ray_limit : c ∈ closure (Work.ParamRays.paramRay Work.EL.alpha1) ∧
    c ∉ Work.ParamRays.paramRay Work.EL.alpha1
  /-- the odd-period parabolic condition. -/
  odd_per : ∃ k : ℕ, Odd k ∧ (Tantibar c)^[k] z₁ = z₁ ∧
    (∀ j : ℕ, 0 < j → j < k → (Tantibar c)^[j] z₁ ≠ z₁) ∧
    Work.Landing.multiplier2 c k z₁ = 1
  /-- the first root ray lands at `z₁`. -/
  ray₁ : Work.Landing.landsAt c Work.EL.alpha1 z₁
  /-- `z₁` is not a cusp. -/
  simple : iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0
  /-- the critical orbit converges to `z₁` without hitting it. -/
  crit : Tendsto (fun n : ℕ => (Work.FSeed.F c)^[n] c) atTop (nhds z₁) ∧
    ∀ n : ℕ, (Work.FSeed.F c)^[n] c ≠ z₁
  /-- the wake condition for the critical orbit. -/
  wake : ∀ k : ℕ, 1 ≤ k →
    (Tantibar c)^[k] 0 ∈ Work.EL.wakeSide (φ := Work.ParamRays.dynPhiOf c)
      (Work.ParamRays.dynNakane dyn) z₁ ((k - 1) % 5)

/-- The SeedExist output at one parameter: the bundle without the portrait, together with the EL
root-parabolic structure and the flower at the *same* point `z₁`. -/
structure SeedData (c : ℂ) where
  /-- the bundle of `FSeed` minus the portrait. -/
  input : RootInputNoPortrait c
  /-- the EL root-parabolic bundle (no portrait field). -/
  d : Work.EL.RootParabolic c
  /-- the two `z₁` agree. -/
  hz₁ : d.z₁ = input.z₁
  /-- the repelling coordinate `Ψ` of the parabolic flower at `z₁`. -/
  Ψ : ℂ → ℂ

/-- The cited clause is the same statement as `Work.SeedExist.NonCuspRootLimit`. -/
theorem nonCuspRootLimit_iff (c z₁ : ℂ) :
    (c ∈ closure (Work.ParamRays.paramRay Work.EL.alpha1) ∧
      c ∉ Work.ParamRays.paramRay Work.EL.alpha1 ∧
      Work.Landing.landsAt c Work.EL.alpha1 z₁ ∧ Work.Landing.landsAt c Work.EL.alpha2 z₁ ∧
      iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0) ↔
    (c ∈ closure (Work.ParamRays.paramRay Work.EL.alpha1) ∧
      c ∉ Work.ParamRays.paramRay Work.EL.alpha1 ∧
      Work.Landing.landsAt c Work.EL.alpha1 z₁ ∧ Work.Landing.landsAt c Work.EL.alpha2 z₁ ∧
      iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0) := Iff.rfl

/-- **The assembly.**  From the cited clause `NonCuspRootLimit`, a producer of the SeedExist
bundle (which in the final tree is `Work.SeedExist.rootParabolicInput_of_nonCusp`, taking `gm`,
`hatt`, `hfat` as its inputs), the Jordan form and the three geometric inputs of §4.2, the whole
`Work.FSeed.FSeedInput` follows — with the portrait *proved*. -/
theorem fSeedInput_of_hypotheses (hJ : Work.Top.JordanForm)
    (hU : unlinkedLemma hJ) (hRN0 : rotationZero) (hGF : gfixedAvoid)
    (H : ∀ c z₁ : ℂ, c ∈ closure (Work.ParamRays.paramRay Work.EL.alpha1) →
      c ∉ Work.ParamRays.paramRay Work.EL.alpha1 →
      Work.Landing.landsAt c Work.EL.alpha1 z₁ → Work.Landing.landsAt c Work.EL.alpha2 z₁ →
      iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0 → ∃ S : SeedData c, S.input.z₁ = z₁)
    (h : NonCuspRootLimit) : Work.FSeed.FSeedInput := by
  obtain ⟨c, z₁, hclos, hnot, hl₁, hl₂, hsimple⟩ := h
  obtain ⟨S, hSz⟩ := H c z₁ hclos hnot hl₁ hl₂ hsimple
  have hportrait : Work.FSeed.LocalRayPortrait c z₁ := by
    have hp : Work.FSeed.LocalRayPortrait c S.input.z₁ := by
      rw [← S.hz₁]
      exact twoRays_of_inputs S.d hJ
        (fun {a b a' b'} {w w'} hw ha hb ha' hb' l1 l2 l3 l4 hd =>
          hU S.d.hN hw ha hb ha' hb' l1 l2 l3 l4 hd) (hRN0 S.d) (hGF S.d)
    rw [hSz] at hp
    exact hp
  refine ⟨c, Nonempty.intro ?_⟩
  exact ⟨S.input.dyn, z₁, S.input.ray_limit, by rw [← hSz]; exact S.input.odd_per,
    by rw [← hSz]; exact S.input.ray₁, hportrait, by rw [← hSz]; exact S.input.simple,
    by rw [← hSz]; exact S.input.crit, by rw [← hSz]; exact S.input.wake⟩

end Work.SeedSimple2

end
