/-
# SeedPortraitCert — the exact portrait of the seed's parabolic point

Area `Submission/Work/SeedPortraitCert/` of `mandelbar_not_path_connected`: **the deliverable**.

```lean
Work.SeedPortraitCert.seedPortrait (db : Work.EL.RootParabolic Work.SeedCert.cb) :
  ∀ θ ∈ Set.Ico 0 1,
    (Work.Landing.landsAt Work.SeedCert.cb θ db.z₁ ↔
      θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2)
```

The proof assembles the area:

* `Z1Eq.z1_eq` — the parabolic point of `db` is the certified point `Work.SeedCert.z1`
  (uniqueness of the landing point of `α₁`), hence `Z1Eq.z1_mem_Zb` puts it in `Zb`;
* `Excl.not_landsN_372_seed`, `Excl.not_landsN_403_seed` — the two `g`-fixed angles of the wake
  arc do not land there (the ray-chain certificate of `Chain.lean` + `ZbDisj.lean`);
* `Portrait.twoRays_of_excl` — the mod-1 portrait, from `RN0`
  (`Work.SeedSimple2.COP.rotationZero_proved`) and the unlinked lemma `U`
  (`Work.SeedSimple2.unlinkedLemma_proved`);
* `Portrait.portrait_iff_of_localRayPortrait` — the two-angle form.
-/
import Mathlib
import Submission.Work.SeedPortraitCert.Z1Eq
import Submission.Work.SeedPortraitCert.Portrait
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedPortraitCert

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-- **The exact portrait of the seed's parabolic point.**  At the certified seed parameter `cb`,
for every root-parabolic bundle of `cb`, the angles in `[0,1)` landing at `z₁` are exactly the
two root angles `α₁ = 371/1023` and `α₂ = 404/1023`. -/
theorem seedPortrait (db : Work.EL.RootParabolic Work.SeedCert.cb) :
    ∀ θ ∈ Set.Ico (0 : ℝ) 1,
      (Work.Landing.landsAt Work.SeedCert.cb θ db.z₁ ↔
        θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2) := by
  have hz : db.z₁ = Work.SeedCert.z1 := z1_eq db
  rw [hz]
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  have hU : ∀ {a b a' b' : ℝ} {w w' : ℂ}, w ≠ w' →
      a ∈ Set.Ico 0 1 → b ∈ Set.Ico 0 1 → a' ∈ Set.Ico 0 1 → b' ∈ Set.Ico 0 1 →
      Work.EL.LandsN db.hN a w → Work.EL.LandsN db.hN b w → Work.EL.LandsN db.hN a' w' →
      Work.EL.LandsN db.hN b' w' → Work.SeedSimple2.PairwiseDistinct4 a b a' b' →
      Work.ELPull.Unlinked a b a' b' :=
    fun {a b a' b'} {w w'} hw ha hb ha' hb' l1 l2 l3 l4 hd =>
      Work.SeedSimple2.unlinkedLemma_proved hJ db.hN hw ha hb ha' hb' l1 l2 l3 l4 hd
  have hp : Work.FSeed.LocalRayPortrait Work.SeedCert.cb db.z₁ :=
    twoRays_of_excl db hJ hU (Work.SeedSimple2.COP.rotationZero_proved hJ db)
      (not_landsN_372_seed db) (not_landsN_403_seed db)
  rw [hz] at hp
  exact portrait_iff_of_localRayPortrait hp ⟨seed_lands_alpha1, seed_lands_alpha2⟩

/-- The deliverable in the `∀ db`-first quantifier order of the contract. -/
theorem seedPortrait_forall :
    ∀ db : Work.EL.RootParabolic Work.SeedCert.cb, ∀ θ ∈ Set.Ico (0 : ℝ) 1,
      (Work.Landing.landsAt Work.SeedCert.cb θ db.z₁ ↔
        θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2) :=
  fun db => seedPortrait db

/-- The same, in the `LandsN` vocabulary of `Work.EL` (so that it feeds
`Work.ELAssembly.hzero_of_transfer` directly, with `z₁₂ = θ''`). -/
theorem seedPortrait_landsN (db : Work.EL.RootParabolic Work.SeedCert.cb) :
    ∀ θ ∈ Set.Ico (0 : ℝ) 1,
      (Work.EL.LandsN db.hN θ db.z₁ ↔
        θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2) :=
  hzero_of_localPortrait db
    (twoRays_of_excl db Work.TopJordan.jordanForm
      (fun {a b a' b'} {w w'} hw ha hb ha' hb' l1 l2 l3 l4 hd =>
        Work.SeedSimple2.unlinkedLemma_proved Work.TopJordan.jordanForm db.hN hw ha hb ha' hb'
          l1 l2 l3 l4 hd)
      (Work.SeedSimple2.COP.rotationZero_proved Work.TopJordan.jordanForm db)
      (not_landsN_372_seed db) (not_landsN_403_seed db))

end

end Work.SeedPortraitCert
