/-
# `Work.MandelWire.exists_seedData_cb`

The seed data `Work.SeedExist.RootSeedData` of the **certified** parameter
`Work.SeedCert.cb`, with the parameter pinned to `c_b` (the equality `S.c = cb`).

`Work.SeedExist.ExplicitRootSeed` (proved in `Submission/Work/MandelFinal/seedCert.lean`) is an
existential `∃ c z₁, …`, so its `toData` forgets *which* parameter it came from; the wiring of the
final theorem needs the seed at the explicit parameter `c_b`.  This file therefore re-runs the
instantiation of `Work.SeedCertRay.landsAt_alphas_data` at `c := Work.SeedCert.cb` (exposing the
pair of landing statements), and combines it with the `SeedCertNum` facts
(`g_fix`, `exact_period`, `mult_one`, `iteratedDeriv2_ne_zero`, `cb ∈ Mandelbar`).

Main results:

* `Work.MandelWire.landsAt_alphas_cb` — the two root rays land at `z1` at the parameter `c_b`;
* `Work.MandelWire.exists_seedData_cb` — the seed data with `S.c = cb`.
-/
import Mathlib
import Submission.Work.MandelWire.Deps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MandelWire

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-- **The two root rays land at the certified point, at the certified parameter.**

This is `Work.SeedCertRay.landsAt_alphas_data` at `c := Work.SeedCert.cb`, `z₁ := Work.SeedCert.z1`,
`A := Work.SeedCert.Aquad`, with the hypotheses discharged exactly as in
`Work.MandelFinal.seedCert`: the ray box data (`Xb`, `Zb`, `Ab`) from `Work.MandelFinal`,
the petal data from `Work.SeedCert.ee_petal4_data`, and the bridging identities
`Work.SeedCertRay.Petal = Work.SeedCert.petal` (at depth `4`) and
`Work.SeedCertRay.fatou = Work.SeedCert.fatouW`. -/
theorem landsAt_alphas_cb :
    Work.Landing.landsAt Work.SeedCert.cb Work.FSeed.α₁ Work.SeedCert.z1 ∧
      Work.Landing.landsAt Work.SeedCert.cb Work.FSeed.α₂ Work.SeedCert.z1 := by
  obtain ⟨hAne, hρ₁, hδ, hRQ, hP1raw, hP2raw⟩ := Work.SeedCert.ee_petal4_data
  have hr4 : Work.SeedCert.RpetalR4 = 4 := Work.MandelFinal.seedCert_RpetalR4
  have hP1 : ∀ z : ℂ, ‖z - Work.SeedCert.z1‖ = Work.SeedCert.rho1R4 →
      Work.EL.F Work.SeedCert.cb z ∉
        Work.SeedCertRay.Petal Work.SeedCert.z1 Work.SeedCert.Aquad 4 := by
    intro z hz
    have h := hP1raw (z - Work.SeedCert.z1) (by simpa using hz)
    rw [hr4] at h
    rw [show Work.SeedCert.z1 + (z - Work.SeedCert.z1) = z by ring] at h
    rw [← Work.MandelFinal.seedCert_petal_eq_petalW] at h
    exact h
  have hP2 : ∀ z : ℂ, ‖z - Work.SeedCert.z1‖ ≤ Work.SeedCert.rho1R4 →
      Work.EL.F Work.SeedCert.cb z ∈
        Work.SeedCertRay.Petal Work.SeedCert.z1 Work.SeedCert.Aquad 4 →
      z ∈ Work.SeedCertRay.Petal Work.SeedCert.z1 Work.SeedCert.Aquad 4 ∧
        (Work.SeedCertRay.fatou Work.SeedCert.z1 Work.SeedCert.Aquad z).re ≤
          (Work.SeedCertRay.fatou Work.SeedCert.z1 Work.SeedCert.Aquad
            (Work.EL.F Work.SeedCert.cb z)).re - Work.SeedCert.deltapR4 := by
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
      exact h2
  have hland := Work.SeedCertRay.landsAt_alphas_data
    (φ := Work.ParamRays.dynPhiOf Work.SeedCert.cb)
    (Work.ParamRays.dynNakane Work.MandelFinal.seedCert_dynBottcherHomeo)
    (Work.ParamRays.isDynBottcher_dynPhiOf Work.MandelFinal.seedCert_dynBottcherHomeo.exists)
    Work.MandelFinal.seedCert_cb_mem_Mandelbar Work.SeedCert.cb_norm_le_two
    Work.MandelFinal.seedCert_cb_mem_Xb Work.SeedCert.z1 Work.SeedCert.Aquad
    Work.MandelFinal.seedCert_z1_mem_Zb Work.MandelFinal.seedCert_Aquad_mem_Ab
    Work.SeedCert.g_fix Work.SeedCert.deltapR4 Work.SeedCert.rho1R4 hρ₁ hδ hAne hRQ hP1 hP2
  exact ⟨by simpa only [Work.EL.alpha1, Work.FSeed.α₁] using hland.1,
    by simpa only [Work.EL.alpha2, Work.FSeed.α₂] using hland.2⟩

/-- **The seed data of the certified parameter `c_b`**: a `RootSeedData` whose parameter is
`Work.SeedCert.cb`.

Every field is one of the facts certified by the area `SeedCertNum` / `SeedCertRay`:
membership in the Mandelbar (`Work.MandelFinal.seedCert_cb_mem_Mandelbar`), the fixed point and
exact period of `z₁` under `(T_cb)^[5]`, the multiplier `1` and the simplicity
(`Work.SeedCert.g_fix`, `exact_period`, `mult_one`, `iteratedDeriv2_ne_zero`), and the landing of
the two root rays (`landsAt_alphas_cb`). -/
theorem exists_seedData_cb : ∃ S : Work.SeedExist.RootSeedData, S.c = Work.SeedCert.cb := by
  obtain ⟨hl1, hl2⟩ := landsAt_alphas_cb
  exact ⟨{ c := Work.SeedCert.cb
           z₁ := Work.SeedCert.z1
           mem := Work.MandelFinal.seedCert_cb_mem_Mandelbar
           g_fix := Work.SeedCert.g_fix
           exact_period := Work.SeedCert.exact_period
           mult_one := Work.SeedCert.mult_one
           simple := Work.SeedCert.iteratedDeriv2_ne_zero
           lands_α₁ := hl1
           lands_α₂ := hl2 }, rfl⟩

end

end Work.MandelWire
