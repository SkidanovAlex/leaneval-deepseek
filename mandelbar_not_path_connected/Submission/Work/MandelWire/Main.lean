/-
# `Work.MandelWire.Main` — the final wiring of the mandelbar theorem (W5–W7)

`Work.MandelWire.mandelbar_not_path_connected_of` is the machine-checked endgame of the
mandelbar project with the *pointed* root of `Submission/Work/MandelWire/Root.lean`: the wiring
never goes through `Work.FinalFix.c₀Of`, so the quasiconformal conjugacy `θ` of MNS's height
shift is available for the tripod transfer (`Work.ELAssembly.AssemblyInputs.T`) and for the ray
portrait `hzero`.

The residual named inputs are the three live exports

* `hLav` — PARIMPL2's `Work.PARIMPL2.LavaursPhase` (the uniform lock-step transit);
* `hSat` — SatFree's sign-free half-plane saturation;
* `hport` — SeedPortraitCert's two-ray portrait at the certified seed `Work.SeedCert.cb`;

the two classical inputs `Work.FatouDeg.fatouParabolicInput_degenerate` and
`Work.SeedFatou.fatouCritInBasin` are **theorems** and are used directly.
-/
import Submission.Work.MandelWire.Deps
import Submission.Work.MandelWire.GATE2n.FinalCaseII
import Submission.Work.MandelWire.Root
import Submission.Work.MandelWire.endgame_at
import Submission.Work.MandelWire.exists_seedData_cb

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.MandelWire

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The mandelbar is not path-connected**, modulo the three live exports. -/
theorem mandelbar_not_path_connected_of
    (hLav : ∀ {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d)
        (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀)
          d.z₁),
        Work.PARIMPL2.LavaursPhase d P fl.Pa fl.φa fl.Ψ
          (Work.PARIMPL.nEnter d fl.toParabolicFlower))
    (hSat : ∀ {c₀ : ℂ} (d : Work.EL.RootParabolic c₀),
        ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀)
            d.z₁,
        ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
          Work.GATE2.SaturatedFlower fl.toParabolicFlower FF)
    (hport : ∀ (db : Work.EL.RootParabolic Work.SeedCert.cb),
        ∀ θ ∈ Set.Ico (0 : ℝ) 1, (Work.Landing.landsAt Work.SeedCert.cb θ db.z₁ ↔
          θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2)) :
    ¬ IsPathConnected Mandelbar := by
  classical
  -- ## 1. The certified seed, with its parameter exposed (`Work.MandelWire.exists_seedData_cb`)
  obtain ⟨S, hSc⟩ := exists_seedData_cb
  have hfatS : Work.SeedExist.FatouCritInBasin S.c S.z₁ (Work.SeedExist.flowerOf S).Pg :=
    Work.SeedFatou.fatouCritInBasin S
  have hdd : Work.ParamRays.DynBottcherHomeo S.c := Work.SeedDyn.dynBottcherHomeo S.mem
  have hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c) := Work.ParamRays.dynNakane hdd
  have hbott : Work.ParamRays.IsDynBottcher S.c (Work.ParamRays.dynPhiOf S.c) :=
    Work.ParamRays.isDynBottcher_dynPhiOf hdd.exists
  have hdbS : Nonempty (Work.EL.RootParabolic S.c) :=
    Work.SeedExist.rootParabolicEL_of_seedData S hN hbott hfatS Work.TopJordan.jordanForm
  -- transport the seed to the certified parameter, where the portrait `hport` lives
  have hdb : Nonempty (Work.EL.RootParabolic Work.SeedCert.cb) := by
    rw [← hSc]
    exact hdbS
  let db : Work.EL.RootParabolic Work.SeedCert.cb := hdb.some
  -- ## 2. The pointed root (W4): `c₀`, `θ`, `d₀`, `d₀.z₁ = θ db.z₁`, `FQC.critHeight d₀ = 0`
  let R : PointedRoot Work.SeedCert.cb db := pointedRoot db
  -- ## 3. The flower and the flower-fix, saturating (SatFree)
  obtain ⟨fl, FF, hSatF⟩ := hSat R.d₀
  -- ## 4. The normal form at `c₀` (PARIMPL)
  let P : Work.PARIMPL.ParNormal R.d₀ := (Work.PARIMPL.exists_parNormal R.d₀).some
  -- ## 5. The entry time of the critical orbit into the petal
  let nIn : ℕ := Work.PARIMPL.nEnter R.d₀ fl.toParabolicFlower
  -- ## 6. The ray-cylinder lift, deepened to `R ≥ 3/2`
  obtain ⟨Lray₀, han₀⟩ := Work.ELRig.exists_analytic_rayCylLift R.d₀ fl.toParabolicFlower
    ((Work.ELTop.landsN_iff_landsAt R.d₀.hN R.d₀.bottcher Work.EL.alpha1 R.d₀.z₁).mpr
      R.d₀.rays.1)
    ((Work.ELTop.landsN_iff_landsAt R.d₀.hN R.d₀.bottcher Work.EL.alpha2 R.d₀.z₁).mpr
      R.d₀.rays.2)
  obtain ⟨Lray, hγ₁, -, -, hR⟩ := Work.GATE2.RayCylLift_mono Lray₀ (le_max_left _ (3 / 2 : ℝ))
  have han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => Lray.γ₁ s)
      (Set.Ioo (n : ℝ) ((n : ℝ) + 1)) := by
    intro n
    rw [hγ₁]
    exact han₀ n
  have h3 : (3 / 2 : ℝ) ≤ Lray.R := by rw [hR]; exact le_max_right _ _
  have hside : Work.EL.PairSides R.d₀.hN (Work.ELAssembly.alphaPairOf R.d₀) :=
    Work.ELTop.pairSides R.d₀.hN Work.TopJordan.jordanForm (Work.ELAssembly.alphaPairOf R.d₀)
      Work.ELAssembly.arcLen_alpha_ne_zero
  -- ## 7. The assembly inputs (W5)
  let A : Work.ELAssembly.AssemblyInputs R.c₀ R.d₀
      (Work.ELNest.FlowerData.ofFatouCoord fl.toParabolicFlower) :=
    { L := 2
      hL := by norm_num
      T := Work.TripodCert.tripod_of_seed_transfer R.θ db.bottcher
        (Work.FQC.transfer_bottcher R.θ db.bottcher R.hconj R.hdecay)
        (Work.FQC.escaping_theta_iff R.θ R.hconj R.hdecay)
        R.d₀.hN R.d₀.bottcher Work.MandelFinal.seedCert_cb_mem_Mandelbar
        Work.MandelFinal.seedCert_cb_mem_Xb
      hzero := Work.ELAssembly.hzero_of_transfer R.θ db.bottcher
        (Work.FQC.transfer_bottcher R.θ db.bottcher R.hconj R.hdecay)
        (Work.FQC.escaping_theta_iff R.θ R.hconj R.hdecay)
        R.d₀.hN R.d₀.bottcher R.hz₁ (fun ϑ hϑ => hport db ϑ hϑ)
      SP := ⟨Lray.R + 2, fun u hu =>
        Work.ELRig.sidePreserve_core_parity R.d₀ fl.toParabolicFlower Lray han
          (Work.ELAssembly.alphaPairOf R.d₀) rfl rfl rfl hside
          (le_refl (Lray.R + 1)) u (by linarith)⟩ }
  have hnd : ∀ n : ℕ, Work.EL.arcLen ((Work.ELAssembly.NestData.ofInputs A).Qp n).a
      ((Work.ELAssembly.NestData.ofInputs A).Qp n).b ≠ 0 := by
    intro n
    rw [show ((Work.ELAssembly.NestData.ofInputs A).Qp n).a = Work.ELNest.bAng' n
        from (Work.ELAssembly.NestPairs.ofChains
          (Work.ELAssembly.chainInputs_of R.d₀ A.hzero)).Qpa n,
      show ((Work.ELAssembly.NestData.ofInputs A).Qp n).b = Work.ELNest.bAng n + 1
        from (Work.ELAssembly.NestPairs.ofChains
          (Work.ELAssembly.chainInputs_of R.d₀ A.hzero)).Qpb n]
    exact Work.ELAssembly.arcLen_bAng_ne_zero n
  let nest : Work.EL.Z1Nest R.d₀.hN R.d₀.z₁ fl.toParabolicFlower.Pa :=
    Work.ELAssembly.toZ1Nest (Work.ELAssembly.NestData.ofInputs A) Work.TopJordan.jordanForm hnd
  let tr : Work.EL.B2Data R.d₀.hN R.d₀.z₁ :=
    Work.ELAssembly.toB2Data (Work.ELAssembly.NestData.ofInputs A) Work.TopJordan.jordanForm
      (Work.ELAssembly.b2_not_postcrit_of_inputs A)
  have hsides := Work.GATE2.toZ1Nest_sides (Work.ELAssembly.NestData.ofInputs A)
    Work.TopJordan.jordanForm hnd
  -- ## 8. The transit phase (PARIMPL2)
  obtain ⟨θL, hLS⟩ := hLav R.d₀ P fl
  let x₀ : ℝ := (fl.φa (Work.PARIMPL.entryPt P nIn R.c₀)).re
  let trans : ℂ → ℂ := Work.PARIMPL2.transPh P x₀ θL
  have htrans_eq : trans = Work.PARIMPL2.transPh P x₀ θL := rfl
  have hcont : ContinuousOn trans (P.Nm ∩ Metric.ball R.c₀ 1) :=
    (Work.PARIMPL2.continuousOn_transPh P x₀ θL).mono Set.inter_subset_left
  have him : ∀ c ∈ P.Nm ∩ Metric.ball R.c₀ P.ρ₀, (trans c).im = 0 :=
    fun c _ => Work.PARIMPL2.transPh_im P x₀ θL c
  have hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball R.c₀ P.ρ₀,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot := by
    intro p hp
    have hball : p ∈ Metric.ball R.c₀ P.ρ₀ := hp.2
    have hnot : p ∉ P.Nm := by
      intro hmem
      have h2 : p ∈ P.Nm ∩ frontier P.Nm := ⟨hmem, hp.1⟩
      rw [P.isOpen_Nm.inter_frontier_eq] at h2
      exact h2
    exact Work.PARIMPL2.tendsto_transPh P x₀ θL p
      (P.a2_zero_of_closure_notMem (frontier_subset_closure hp.1) hball hnot) hball
  have hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧
      ∀ c ∈ P.Nm ∩ Metric.ball R.c₀ r, (trans c).re ≤ b := by
    intro b
    obtain ⟨ρ, hρ, hρb⟩ := Work.PARIMPL2.transPh_blow P x₀ θL (-b)
    refine ⟨ρ, hρ, fun c hc => ?_⟩
    rw [htrans_eq]
    simpa using hρb c hc
  -- ## 9. The endgame (W7 + W8)
  refine endgame_at (⟨R.d₀, fl.toParabolicFlower⟩ : Work.Final.RootArc R.c₀) P.Nm ?_ ?_
    Work.MandelFinal.nakaneInput Work.MandelFinal.repellingRayParamStable ?_ ?_
  · -- `noPath` (PARIMPL2 + the equator leak of ELAssembly)
    exact Work.PARIMPL2.Lavaurs.noPath_of_inputs R.d₀ P fl nIn
      { hnIn := le_refl _
        UT := hLav R.d₀ P fl
        leak := Work.ELAssembly.equatorLeak_of_inputs A fl rfl
        critHeight_zero := R.critHeight_zero fl P }
  · -- `twoSided` (GATE2 without `MatchData`/`TransitData`)
    exact Work.MandelWire.G2n.twoSided_of_exports (fl := fl.toParabolicFlower) FF (nIn := nIn)
      trans P.isOpen_Nm
      (P.mem_frontier_Nm (Work.PARIMPL.periodFiveGone R.d₀ P)
        (Work.PARIMPL.Nm_mem_closure R.d₀ P))
      (Work.PARIMPL.nEnter_spec R.d₀ fl.toParabolicFlower)
      (R.critHeight_zero fl P) hSatF
      (ρc := 1) one_pos hcont (ρh := P.ρ₀) P.hρ₀ him hblowup
      hblow hLS Work.NAKANE.greenEscapeOpen nest Lray han
      (Work.ELRig.flipHyp_of_jordan Work.TopJordan.jordanForm R.d₀ fl.toParabolicFlower nest.P0
        nest.P0_spec.1 nest.P0_spec.2.1 nest.P0_spec.2.2 nest.sides_P0 Lray)
      (fun n => (Work.ELAssembly.NestPairs.ofChains
        (Work.ELAssembly.chainInputs_of R.d₀ A.hzero)).Qpa n)
      (fun n => (Work.ELAssembly.NestPairs.ofChains
        (Work.ELAssembly.chainInputs_of R.d₀ A.hzero)).Qpb n)
      h3 hsides.1 hsides.2 tr
  · exact Work.MandelFinal.paramAngleRepelling Work.FatouDeg.fatouParabolicInput_degenerate
      (⟨R.d₀, fl.toParabolicFlower⟩ : Work.Final.RootArc R.c₀)
  · exact Work.MandelFinal.paramAngleRepelling_quarter Work.FatouDeg.fatouParabolicInput_degenerate

/-- **The note's original five-binder signature.**  The three classical/exported inputs
`hDeg` (`Work.FatouDeg.fatouParabolicInput_degenerate`), `hfat`
(`Work.SeedFatou.fatouCritInBasin`) and `hport` (`Work.SeedPortraitCert.seedPortrait`) have since
become theorems, so this form **ignores** `hDeg` and `hfat` and passes `hport` on.  It exists so
that a caller written against the wire note's exact binder list still elaborates. -/
theorem mandelbar_not_path_connected_of_five
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate)
    (hfat : ∀ S : Work.SeedExist.RootSeedData,
        Work.SeedExist.FatouCritInBasin S.c S.z₁ (Work.SeedExist.flowerOf S).Pg)
    (hLav : ∀ {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d)
        (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀)
          d.z₁),
        Work.PARIMPL2.LavaursPhase d P fl.Pa fl.φa fl.Ψ
          (Work.PARIMPL.nEnter d fl.toParabolicFlower))
    (hSat : ∀ {c₀ : ℂ} (d : Work.EL.RootParabolic c₀),
        ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀)
            d.z₁,
        ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
          Work.GATE2.SaturatedFlower fl.toParabolicFlower FF)
    (hport : ∀ (db : Work.EL.RootParabolic Work.SeedCert.cb),
        ∀ θ ∈ Set.Ico (0 : ℝ) 1, (Work.Landing.landsAt Work.SeedCert.cb θ db.z₁ ↔
          θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2)) :
    ¬ IsPathConnected Mandelbar :=
  mandelbar_not_path_connected_of hLav hSat hport

end Work.MandelWire
