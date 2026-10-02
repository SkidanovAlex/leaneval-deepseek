/-
# SeedExist — wiring the W-lemmas into the assembly

This file discharges the facts that `Submission/Work/SeedExist/Assembly.lean` takes as
hypotheses, using the lemmas of the area:

* `image_wakeSide` (W3), `critValue_mem_wakeSide` (W4), `cycle_mem_Snear` (W5),
  `characteristic_component` (W6), `wake_field` (W8);
* `interior_of_fatou` (E10), `mem_Pg_of_fatou` (W9a), `critOrbit_of_mem_Pg` (W9b);
* `iterate_ne_zero` (the elimination of `0` from the parabolic cycle).

The result is `rootParabolicEL_of_seedData`: from a `RootSeedData`, the Böttcher data, Fatou's
theorem `FatouCritInBasin` and the Jordan curve theorem, the structure
`Work.EL.RootParabolic` is produced.
-/
import Submission.Work.SeedExist.Assembly
import Submission.Work.SeedExist.Input
import Submission.Work.SeedExist.NonCusp
import Submission.Work.SeedExist.Sides.image_wakeSide
import Submission.Work.SeedExist.Sides.critValue_mem_wakeSide
import Submission.Work.SeedExist.Sides.cycle_mem_Snear
import Submission.Work.SeedExist.Sides.characteristic_component
import Submission.Work.SeedExist.Sides.wake_field
import Submission.Work.SeedExist.Fatou.mem_Pg_of_fatou
import Submission.Work.SeedExist.Fatou.critOrbit_of_mem_Pg
import Submission.Work.SeedExist.Fatou.interior_of_fatou
import Submission.Work.SeedExist.Pair.iterate_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

noncomputable section

namespace Work.SeedExist

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- `0 ∈ K c` from `c ∈ Mandelbar`. -/
theorem zero_mem_K_of_mem_mandelbar {c : ℂ} (hc : c ∈ Mandelbar) : (0 : ℂ) ∈ Work.EL.K c := by
  have h := hc
  simp only [Mandelbar, Set.mem_ofPred_eq] at h
  exact h

/-- The `g`-orbit of the critical value stays in the wake side of the level-`0` α-pair. -/
theorem gOrbit_mem_wakeSide {c : ℂ} {z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    {U : Set ℂ} (hcU : c ∈ U) (hgU : Set.MapsTo ((Tantibar c)^[5]) U U)
    (hUS : U ⊆ wakeSide hN z₁ 0) :
    ∀ m : ℕ, (((Tantibar c)^[5])^[m]) c ∈ wakeSide hN z₁ 0 := by
  intro m
  exact hUS ((hgU.iterate m) hcU)

/-- W5 at the seed. -/
theorem cycle_mem_Snear_of_seedData (S : RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c)) (hJ : Work.Top.JordanForm) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 4 → (Tantibar S.c)^[j] S.z₁ ∈ Snear hN S.z₁ :=
  fun j hj1 hj => Work.SeedExist.Sides.cycle_mem_Snear hN hJ S.lands_α₁ S.g_fix S.exact_period
    j hj1 hj

/-- W6 at the seed. -/
theorem characteristic_of_seedData (S : RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c)) (hJ : Work.Top.JordanForm)
    (hfat : FatouCritInBasin S.c S.z₁ (flowerOf S).Pg) :
    U S.c ⊆ wakeSide hN S.z₁ 0 ∧
      Set.MapsTo ((Tantibar S.c)^[5]) (U S.c) (U S.c) ∧
      Set.MapsTo ((Tantibar S.c)^[4]) (U S.c) (U₀ S.c) :=
  Work.SeedExist.Sides.characteristic_component hN hJ (flowerOf S) hfat
    (Work.SeedExist.Sides.critValue_mem_wakeSide hN hJ S.lands_α₁ S.lands_α₂
      (fun i hi => Work.SeedExist.Pair.iterate_ne_zero S.g_fix S.mult_one i hi)
      (zero_mem_K_of_mem_mandelbar S.mem))
    (cycle_mem_Snear_of_seedData S hN hJ) S.g_fix S.exact_period

/-- W9a at the seed: the critical orbit enters the half-petal `Pg`. -/
theorem mem_Pg_of_seedData (S : RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c)) (hJ : Work.Top.JordanForm)
    (hfat : FatouCritInBasin S.c S.z₁ (flowerOf S).Pg) :
    ∃ N : ℕ, (Work.FSeed.F S.c)^[N] S.c ∈ (flowerOf S).Pg := by
  have hE10 : S.c ∈ interior (Work.EL.K S.c) ∧ (0 : ℂ) ∈ interior (Work.EL.K S.c) :=
    Work.SeedExist.Fatou.interior_of_fatou (flowerOf S) hfat
  have hW6 := characteristic_of_seedData S hN hJ hfat
  exact Work.SeedExist.Fatou.mem_Pg_of_fatou hN hJ (flowerOf S) hfat S.lands_α₁ S.lands_α₂
    S.g_fix S.exact_period (mem_connectedComponentIn hE10.1) hW6.2.1 hW6.1
    (cycle_mem_Snear_of_seedData S hN hJ)

/-- The wake field at the seed. -/
theorem wakeField_of_seedData (S : RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c)) (hJ : Work.Top.JordanForm)
    (hfat : FatouCritInBasin S.c S.z₁ (flowerOf S).Pg) :
    ∀ k : ℕ, 1 ≤ k → (Tantibar S.c)^[k] 0 ∈ wakeSide hN S.z₁ ((k - 1) % 5) := by
  have hE10 : S.c ∈ interior (Work.EL.K S.c) ∧ (0 : ℂ) ∈ interior (Work.EL.K S.c) :=
    Work.SeedExist.Fatou.interior_of_fatou (flowerOf S) hfat
  have hW6 := characteristic_of_seedData S hN hJ hfat
  have hgOrbit := gOrbit_mem_wakeSide hN (mem_connectedComponentIn hE10.1) hW6.2.1 hW6.1
  have hzn : ∀ i : ℕ, i ≤ 4 → (Tantibar S.c)^[i] S.z₁ ≠ 0 :=
    fun i hi => Work.SeedExist.Pair.iterate_ne_zero S.g_fix S.mult_one i hi
  have hW3 : ∀ j : ℕ, j ≤ 3 →
      Tantibar S.c '' wakeSide hN S.z₁ j = wakeSide hN S.z₁ (j + 1) :=
    fun j hj => Work.SeedExist.Sides.image_wakeSide hN hJ S.lands_α₁ S.lands_α₂ hzn j hj
  exact fun k hk => Work.SeedExist.Sides.wake_field hN hW3 hgOrbit k hk

/-- The critical-orbit field at the seed. -/
theorem critField_of_seedData (S : RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c)) (hJ : Work.Top.JordanForm)
    (hfat : FatouCritInBasin S.c S.z₁ (flowerOf S).Pg) :
    Filter.Tendsto (fun n : ℕ => (Work.FSeed.F S.c)^[n] S.c) Filter.atTop (nhds S.z₁) ∧
      ∀ n : ℕ, (Work.FSeed.F S.c)^[n] S.c ≠ S.z₁ :=
  Work.SeedExist.Fatou.critOrbit_of_mem_Pg (flowerOf S) (mem_Pg_of_seedData S hN hJ hfat)

/-- **The wiring**: the root-parabolic bundle from the seed data, the Böttcher data, Fatou's
theorem and the Jordan curve theorem. -/
theorem rootParabolicEL_of_seedData (S : RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c))
    (hbott : Work.ParamRays.IsDynBottcher S.c (Work.ParamRays.dynPhiOf S.c))
    (hfat : FatouCritInBasin S.c S.z₁ (flowerOf S).Pg)
    (hJ : Work.Top.JordanForm) :
    Nonempty (Work.EL.RootParabolic S.c) :=
  rootParabolicEL_of_facts S hN hbott (wakeField_of_seedData S hN hJ hfat)
    (critField_of_seedData S hN hJ hfat)


/-- **The wiring, in the `∃ c` form.** -/
theorem exists_rootParabolic_of_seedData (S : RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c))
    (hbott : Work.ParamRays.IsDynBottcher S.c (Work.ParamRays.dynPhiOf S.c))
    (hfat : FatouCritInBasin S.c S.z₁ (flowerOf S).Pg)
    (hJ : Work.Top.JordanForm) :
    ∃ c : ℂ, Nonempty (Work.EL.RootParabolic c) :=
  ⟨S.c, rootParabolicEL_of_seedData S hN hbott hfat hJ⟩

/-- **The area's main theorem, in the form the lead asked for**: from the certified seed
`ExplicitRootSeed`, Böttcher's theorem in the dynamical plane, Fatou's theorem in the strong form
and the Jordan curve theorem, the root-parabolic bundle exists. -/
theorem rootParabolicEL_of_explicitSeed (h : ExplicitRootSeed)
    (hdyn : ∀ c : ℂ, c ∈ Mandelbar → Work.ParamRays.DynBottcherHomeo c)
    (hfat : ∀ c z (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c)
        ((Tantibar c)^[5]) z), c ∈ Mandelbar → FatouCritInBasin c z fl.Pg)
    (hJ : Work.Top.JordanForm) :
    ∃ c : ℂ, Nonempty (Work.EL.RootParabolic c) := by
  obtain ⟨S⟩ := ExplicitRootSeed.toData h
  have hdd : Work.ParamRays.DynBottcherHomeo S.c := hdyn S.c S.mem
  have hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c) := Work.ParamRays.dynNakane hdd
  have hbott : Work.ParamRays.IsDynBottcher S.c (Work.ParamRays.dynPhiOf S.c) :=
    Work.ParamRays.isDynBottcher_dynPhiOf hdd.exists
  exact ⟨S.c, rootParabolicEL_of_seedData S hN hbott (hfat S.c S.z₁ (flowerOf S) S.mem) hJ⟩

/-- **The `RootParabolicInput` bundle**, wired: from the seed data, the Böttcher homeomorphism,
the parameter-ray limit condition, the local portrait, Fatou's theorem and the Jordan curve
theorem.  All fields except `portrait` (area `SeedSimple2`) and `ray_limit` (not produced by the
certified-seed route) are derived. -/
theorem rootParabolicInput_of_seedData (S : RootSeedData)
    (hdyn : Work.ParamRays.DynBottcherHomeo S.c)
    (hray : S.c ∈ closure (Work.ParamRays.paramRay Work.FSeed.α₁) ∧
      S.c ∉ Work.ParamRays.paramRay Work.FSeed.α₁)
    (hportrait : Work.FSeed.LocalRayPortrait S.c S.z₁)
    (hfat : FatouCritInBasin S.c S.z₁ (flowerOf S).Pg)
    (hJ : Work.Top.JordanForm) :
    Nonempty (Work.FSeed.RootParabolicInput S.c) := by
  let hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c) := Work.ParamRays.dynNakane hdyn
  refine rootParabolicInput_of_facts S hdyn hray hportrait ?_
    (critField_of_seedData S hN hJ hfat)
  intro k hk
  exact wakeField_of_seedData S hN hJ hfat k hk

/-- The `RootParabolicInput` bundle, in the `∃ c` form. -/
theorem exists_rootParabolicInput_of_seedData (S : RootSeedData)
    (hdyn : Work.ParamRays.DynBottcherHomeo S.c)
    (hray : S.c ∈ closure (Work.ParamRays.paramRay Work.FSeed.α₁) ∧
      S.c ∉ Work.ParamRays.paramRay Work.FSeed.α₁)
    (hportrait : Work.FSeed.LocalRayPortrait S.c S.z₁)
    (hfat : FatouCritInBasin S.c S.z₁ (flowerOf S).Pg)
    (hJ : Work.Top.JordanForm) :
    ∃ c : ℂ, Nonempty (Work.FSeed.RootParabolicInput c) :=
  ⟨S.c, rootParabolicInput_of_seedData S hdyn hray hportrait hfat hJ⟩


end Work.SeedExist

end
