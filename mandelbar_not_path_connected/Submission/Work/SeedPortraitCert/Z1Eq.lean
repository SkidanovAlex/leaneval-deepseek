/-
# SeedPortraitCert — the parabolic point of the seed and the uniqueness of a landing

Area `Submission/Work/SeedPortraitCert/`.  The certificate of this area is *numerical*: the
exclusions `Excl.lean` are proved for every point `z₁` of the box `Zb`.  To apply them to the
parabolic point `z₁` of a bundle `db : Work.EL.RootParabolic Work.SeedCert.cb` we need
`db.z₁ ∈ Zb`.

That is what this file supplies.  The point is that `Work.EL.LandsN hN θ ·` is a *limit* (of the
ray points as the level tends to `1⁺`), hence unique: `db.z₁` and the certified seed's point
`Work.SeedCert.z1` are both landing points of the ray `α₁`, so they coincide — and
`Work.SeedCert.z1` is certified to lie in `Zb` by the area `SeedCertNum` (bridged in
`Work.MandelFinal.seedCert`).

The concrete landing `landsAt cb α₁ z1` is not exported by the seed assembly (which is an
existential `ExplicitRootSeed`); it is re-derived here from the same pieces, by feeding the
`SeedCertNum` petal data to `Work.SeedCertRay.landsAt_alphas_data` exactly as
`Work.MandelFinal.seedCert` does.
-/
import Mathlib
import Submission.Work.MandelFinal.seedCert
import Submission.Work.SeedCertRay.Final
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.SeedPortraitCert.Excl

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedPortraitCert

open Work.SeedCertRay
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## The concrete landing of the root rays at the certified seed -/

/-- **`α₁` lands at the certified parabolic point `z1` of the seed `cb`.** -/
theorem seed_lands_alpha1 :
    Work.Landing.landsAt Work.SeedCert.cb Work.EL.alpha1 Work.SeedCert.z1 := by
  obtain ⟨hAne, hρ₁, hδ, hRQ, hP1raw, hP2raw⟩ := Work.SeedCert.ee_petal4_data
  have hr4 : Work.SeedCert.RpetalR4 = 4 := Work.MandelFinal.seedCert_RpetalR4
  have hmain := Work.SeedCertRay.landsAt_alphas_data
    (c := Work.SeedCert.cb)
    (Work.ParamRays.dynNakane
      (Work.SeedDyn.dynBottcherHomeo Work.MandelFinal.seedCert_cb_mem_Mandelbar))
    (Work.ParamRays.isDynBottcher_dynPhiOf
      (Work.SeedDyn.dynBottcherHomeo Work.MandelFinal.seedCert_cb_mem_Mandelbar).exists)
    Work.MandelFinal.seedCert_cb_mem_Mandelbar Work.SeedCert.cb_norm_le_two
    Work.MandelFinal.seedCert_cb_mem_Xb Work.SeedCert.z1 Work.SeedCert.Aquad
    Work.MandelFinal.seedCert_z1_mem_Zb Work.MandelFinal.seedCert_Aquad_mem_Ab
    Work.SeedCert.g_fix Work.SeedCert.deltapR4 Work.SeedCert.rho1R4 hρ₁ hδ hAne hRQ
    (by
      intro z hz
      have h := hP1raw (z - Work.SeedCert.z1) (by simpa using hz)
      rw [hr4] at h
      rw [show Work.SeedCert.z1 + (z - Work.SeedCert.z1) = z by ring] at h
      rw [← Work.MandelFinal.seedCert_petal_eq_petalW] at h
      exact h)
    (by
      intro z hz hm
      have hm' : Work.FSeed.F Work.SeedCert.cb z ∈
          Work.SeedCert.petal Work.SeedCert.z1 Work.SeedCert.Aquad 4 := by
        rw [← Work.MandelFinal.seedCert_petal_eq_petalW]
        exact hm
      obtain ⟨h1, h2⟩ := hP2raw z hz (by rwa [hr4])
      refine ⟨?_, ?_⟩
      · rw [Work.MandelFinal.seedCert_petal_eq_petalW]
        rwa [hr4] at h1
      · rw [Work.MandelFinal.seedCert_fatou_eq_fatouW, Work.MandelFinal.seedCert_fatou_eq_fatouW]
        exact h2)
  exact hmain.1

theorem seed_lands_alpha2 :
    Work.Landing.landsAt Work.SeedCert.cb Work.EL.alpha2 Work.SeedCert.z1 := by
  obtain ⟨hAne, hρ₁, hδ, hRQ, hP1raw, hP2raw⟩ := Work.SeedCert.ee_petal4_data
  have hr4 : Work.SeedCert.RpetalR4 = 4 := Work.MandelFinal.seedCert_RpetalR4
  have hmain := Work.SeedCertRay.landsAt_alphas_data
    (c := Work.SeedCert.cb)
    (Work.ParamRays.dynNakane
      (Work.SeedDyn.dynBottcherHomeo Work.MandelFinal.seedCert_cb_mem_Mandelbar))
    (Work.ParamRays.isDynBottcher_dynPhiOf
      (Work.SeedDyn.dynBottcherHomeo Work.MandelFinal.seedCert_cb_mem_Mandelbar).exists)
    Work.MandelFinal.seedCert_cb_mem_Mandelbar Work.SeedCert.cb_norm_le_two
    Work.MandelFinal.seedCert_cb_mem_Xb Work.SeedCert.z1 Work.SeedCert.Aquad
    Work.MandelFinal.seedCert_z1_mem_Zb Work.MandelFinal.seedCert_Aquad_mem_Ab
    Work.SeedCert.g_fix Work.SeedCert.deltapR4 Work.SeedCert.rho1R4 hρ₁ hδ hAne hRQ
    (by
      intro z hz
      have h := hP1raw (z - Work.SeedCert.z1) (by simpa using hz)
      rw [hr4] at h
      rw [show Work.SeedCert.z1 + (z - Work.SeedCert.z1) = z by ring] at h
      rw [← Work.MandelFinal.seedCert_petal_eq_petalW] at h
      exact h)
    (by
      intro z hz hm
      have hm' : Work.FSeed.F Work.SeedCert.cb z ∈
          Work.SeedCert.petal Work.SeedCert.z1 Work.SeedCert.Aquad 4 := by
        rw [← Work.MandelFinal.seedCert_petal_eq_petalW]
        exact hm
      obtain ⟨h1, h2⟩ := hP2raw z hz (by rwa [hr4])
      refine ⟨?_, ?_⟩
      · rw [Work.MandelFinal.seedCert_petal_eq_petalW]
        rwa [hr4] at h1
      · rw [Work.MandelFinal.seedCert_fatou_eq_fatouW, Work.MandelFinal.seedCert_fatou_eq_fatouW]
        exact h2)
  exact hmain.2

/-! ## Uniqueness of the landing point -/

/-- The filter of the landing definition is nontrivial. -/
instance instNeBotNhdsWithinIoi : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := by
  rw [nhdsWithin_neBot]
  intro t ht
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨1 + ε / 2, hsub ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  · rw [Set.mem_Ioi]
    linarith

/-- **A landing point is unique**: two limits of the same ray family coincide. -/
theorem landsN_unique_of {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ : ℝ} {y y' : ℂ}
    (h : Work.EL.LandsN hN θ y) (h' : Work.EL.LandsN hN θ y') : y = y' :=
  tendsto_nhds_unique h h'

/-- **Every root-parabolic bundle at the seed has the certified parabolic point as its own.** -/
theorem z1_eq (d : Work.EL.RootParabolic Work.SeedCert.cb) : d.z₁ = Work.SeedCert.z1 := by
  have h1 : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 d.z₁).mpr d.rays.1
  have h2 : Work.EL.LandsN d.hN Work.EL.alpha1 Work.SeedCert.z1 :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 Work.SeedCert.z1).mpr
      seed_lands_alpha1
  exact tendsto_nhds_unique h1 h2

/-- **The parabolic point of any root-parabolic bundle at the seed lies in the box `Zb`.** -/
theorem z1_mem_Zb (d : Work.EL.RootParabolic Work.SeedCert.cb) : Zb.mem d.z₁ := by
  rw [z1_eq d]
  exact Work.MandelFinal.seedCert_z1_mem_Zb

/-! ## The two exclusions at the seed -/

/-- **`372/1023 = 12/33` does not land at the seed's parabolic point.** -/
theorem not_landsN_372_seed (d : Work.EL.RootParabolic Work.SeedCert.cb) :
    ¬ Work.EL.LandsN d.hN ((372 : ℝ) / 1023) d.z₁ := by
  have h := not_landsN_372 d.hN d.bottcher Work.MandelFinal.seedCert_cb_mem_Mandelbar
    Work.SeedCert.cb_norm_le_two Work.MandelFinal.seedCert_cb_mem_Xb
    Work.MandelFinal.seedCert_z1_mem_Zb
  rwa [← z1_eq d] at h

/-- **`403/1023 = 13/33` does not land at the seed's parabolic point.** -/
theorem not_landsN_403_seed (d : Work.EL.RootParabolic Work.SeedCert.cb) :
    ¬ Work.EL.LandsN d.hN ((403 : ℝ) / 1023) d.z₁ := by
  have h := not_landsN_403 d.hN d.bottcher Work.MandelFinal.seedCert_cb_mem_Mandelbar
    Work.SeedCert.cb_norm_le_two Work.MandelFinal.seedCert_cb_mem_Xb
    Work.MandelFinal.seedCert_z1_mem_Zb
  rwa [← z1_eq d] at h

end

end Work.SeedPortraitCert
