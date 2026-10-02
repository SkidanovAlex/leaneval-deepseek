/-
# `ELAssembly` — the assembly of `NestData` at the inputs of `AssemblyInputs`

`Work.ELNest.NestData c` collects the two nests of the equator-leak argument and the facts about
them as fields, with the fields that the neighbouring areas (ELTop, ELPull, the certificate)
supply.  This file builds a `NestData` from the bundle `Work.ELAssembly.AssemblyInputs`, deriving
the fields that the interface does *not* need to assume:

| derived | how |
|---|---|
| `P0`, `P0a`, `P0b`, `P0y` | `alphaPairOf d` from `d.rays` through `Work.ELTop.landsN_iff_landsAt` |
| `sides_P0` | `Work.ELTop.pairSides` (T6); non-degeneracy `arcLen α₁ α₂ ≠ 0` is a rational check |
| `side_disj` | `PairSides.disjoint` |
| `Qp`, `Qpa`, `Qpb`, `Za`, … | the bundle's `pairs` (`NestPairs d`) |
| `b2`, `b2_lands`, `b2_lands'` | the bundle's tripod `T` |
| `b2_fix` | from the three tripod rays (`Work.ELNest.T_sq_tripod` + `landsN_unique`) |
| `b2_not_int` | a landing point of a ray is not an interior point of `K c` |
| everything else | the bundle's `cert`, `SP`, `Pa_far`, and NEST (T6) via `nest_side_of_nearArc` |

Together with `Z1.lean`, `B2.lean` and `Main.lean` this closes the chain
`AssemblyInputs → NestData → Z1Nest/B2Data → ∃ x, Ψ x ∉ K c`.
-/
import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELAssembly.Inputs
import Submission.Work.ELNest.b2_fix_of_lands
import Submission.Work.ELNest.Qp_shift
import Submission.Work.ELTop.polyRegion_eq_inter_pairSideNear
import Submission.Work.ELAssembly.pot_iterate
import Submission.Work.ELAssembly.curveF_of_alphaPair
import Submission.Work.ELAssembly.Q_adm_of
import Submission.Work.ELAssembly.Qmem_of
import Submission.Work.ELAssembly.Qne_of
import Submission.Work.ELAssembly.z1_near_Q_of
import Submission.Work.ELAssembly.Dmem_of
import Submission.Work.ELAssembly.D_adm_of
import Submission.Work.ELAssembly.b2_locInj_of
import Submission.Work.ELAssembly.base_shift_of
import Submission.Work.ELAssembly.CutNe
import Submission.Work.ELAssembly.NestSide
import Submission.Work.ELAssembly.InverseBranch
import Submission.Work.ELAssembly.pullQ_bij
import Submission.Work.ELAssembly.pullD_bij
import Submission.Work.ELAssembly.qPullInputs_of
import Submission.Work.ELAssembly.dPullInputs_of
import Submission.Work.ELAssembly.diffOn_gQ
import Submission.Work.ELAssembly.diffOn_gD6
import Submission.Work.ELAssembly.PbAvoid_main
import Submission.Work.ELAssembly.portraitCount_of_flowerData
import Submission.Work.ELAssembly.b2_not_postcrit_of
import Submission.Work.ELAssembly.Derived.Fields
import Submission.Work.ELAssembly.Derived.AssemblyFields
import Submission.Work.ELAssembly.Dnest_cl_of
import Submission.Work.ELAssembly.Pa_far_of
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c} {fl : Work.ELNest.FlowerData c d.z₁}

/-- The angles of `Work.EL.alpha1` and `Work.ELNest.alpha1` agree. -/
theorem alpha1_eq : Work.EL.alpha1 = Work.ELNest.alpha1 := rfl

/-- The angles of `Work.EL.alpha2` and `Work.ELNest.alpha2` agree. -/
theorem alpha2_eq : Work.EL.alpha2 = Work.ELNest.alpha2 := rfl

/-- **`b₂` is fixed by `f_c²`** (the field `NestData.b2_fix`), from the three tripod rays.  This
is `Work.ELNest.b2_fix_of_lands` with the `NestData` replaced by its three landing fields. -/
theorem b2_fix_of_lands (hN : Work.EL.DynB c d.φ) (hB : Work.ParamRays.IsDynBottcher c d.φ)
    {b2 : ℂ} (h₁ : Work.EL.LandsN hN (22 / 63) b2) (h₂ : Work.EL.LandsN hN (25 / 63) b2) :
    Work.Landing.Tsq c b2 = b2 := by
  have h1 : Work.EL.LandsN hN (Work.EL.T^[2] (22 / 63)) ((Tantibar c)^[2] b2) :=
    Work.ELNest.landsN_iterate hN hB 2 h₁
  rw [Work.ELNest.T_sq_tripod] at h1
  have h2 : (Tantibar c)^[2] b2 = b2 := Work.ELNest.landsN_unique h1 h₂
  rw [show Work.Landing.Tsq c = (Tantibar c)^[2] from Work.ELNest.Tsq_eq_comp c]
  exact h2

/-- The admissibility of the level-`n` polygons of the `z₁`-nest (`Q_adm_of` from the portrait
`hzero`): the `hadm` input of `Work.ELAssembly.pullQ_bij`. -/
lemma polyAdmQ {c : ℂ} {d : Work.EL.RootParabolic c} {fl : Work.ELNest.FlowerData c d.z₁}
    (A : AssemblyInputs c d fl) :
    ∀ n : ℕ, Work.EL.PolyAdmissible
      [alphaPairOf d, (NestPairs.ofChains (chainInputs_of d A.hzero)).Qp n] :=
  fun n => Q_adm_of d _ (fun m => Qne_of d _ A.hzero m) n

/-- The admissibility of the level-`n` polygons of the `b₂`-nest (`D_adm_of` from the cut points):
the `hadm` input of `Work.ELAssembly.pullD_bij`. -/
lemma polyAdmD {c : ℂ} {d : Work.EL.RootParabolic c} {fl : Work.ELNest.FlowerData c d.z₁}
    (A : AssemblyInputs c d fl) :
    ∀ n : ℕ, Work.EL.PolyAdmissible
      [(NestPairs.ofChains (chainInputs_of d A.hzero)).Za n,
       (NestPairs.ofChains (chainInputs_of d A.hzero)).Zb n,
       (NestPairs.ofChains (chainInputs_of d A.hzero)).Zc n] :=
  fun n => D_adm_of_inputs A n

/-- **`hcvQ`, derived**: the ten critical values of `F c` avoid every level of the `z₁`-nest
(`Work.ELAssembly.PbAvoid_main` from the portrait `hzero` and the portrait count of the flower). -/
lemma hcvQ_of {c : ℂ} {d : Work.EL.RootParabolic c} {fl : Work.ELNest.FlowerData c d.z₁}
    (A : AssemblyInputs c d fl) :
    ∀ n : ℕ, ∀ k ∈ Set.Icc 1 10,
      (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0 ∉
        Work.EL.polyRegion [alphaPairOf d, (NestPairs.ofChains (chainInputs_of d A.hzero)).Qp n]
          (Work.ELNest.Qlev A.L n) := by
  intro n k hk
  exact (PbAvoid_main d A.hzero (portraitCount_of_flowerData d fl)
    (NestPairs.ofChains (chainInputs_of d A.hzero)) A.hL (polyAdmD A)).1 n k (by simpa using hk)

/-- **`hcvD`, derived**: the six critical values of `f_c^6` avoid every level of the `b₂`-nest. -/
lemma hcvD_of {c : ℂ} {d : Work.EL.RootParabolic c} {fl : Work.ELNest.FlowerData c d.z₁}
    (A : AssemblyInputs c d fl) :
    ∀ n : ℕ, ∀ k ∈ Set.Icc 1 6,
      (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0 ∉
        Work.EL.polyRegion
          [(NestPairs.ofChains (chainInputs_of d A.hzero)).Za n,
           (NestPairs.ofChains (chainInputs_of d A.hzero)).Zb n,
           (NestPairs.ofChains (chainInputs_of d A.hzero)).Zc n]
          (Work.ELNest.Dlev A.L n) := by
  intro n k hk
  exact (PbAvoid_main d A.hzero (portraitCount_of_flowerData d fl)
    (NestPairs.ofChains (chainInputs_of d A.hzero)) A.hL (polyAdmD A)).2 n k (by simpa using hk)

/-- **The assembly of a `NestData` from `AssemblyInputs`.** -/
noncomputable def NestData.ofInputs (A : AssemblyInputs c d fl) : Work.ELNest.NestData c where
  d := d
  fl := fl
  L := A.L
  hL := A.hL
  P0 := alphaPairOf d
  P0a := by rw [alphaPairOf_a]; exact alpha1_eq
  P0b := by rw [alphaPairOf_b]; exact alpha2_eq
  P0y := alphaPairOf_y d
  sides_P0 := sides_alphaPairOf d Work.TopJordan.jordanForm
  Qp := (NestPairs.ofChains (chainInputs_of d A.hzero)).Qp
  Qpa := (NestPairs.ofChains (chainInputs_of d A.hzero)).Qpa
  Qpb := (NestPairs.ofChains (chainInputs_of d A.hzero)).Qpb
  Za := (NestPairs.ofChains (chainInputs_of d A.hzero)).Za
  Zaa := (NestPairs.ofChains (chainInputs_of d A.hzero)).Zaa
  Zab := (NestPairs.ofChains (chainInputs_of d A.hzero)).Zab
  Zb := (NestPairs.ofChains (chainInputs_of d A.hzero)).Zb
  Zba := (NestPairs.ofChains (chainInputs_of d A.hzero)).Zba
  Zbb := (NestPairs.ofChains (chainInputs_of d A.hzero)).Zbb
  Zc := (NestPairs.ofChains (chainInputs_of d A.hzero)).Zc
  Zca := (NestPairs.ofChains (chainInputs_of d A.hzero)).Zca
  Zcb := (NestPairs.ofChains (chainInputs_of d A.hzero)).Zcb
  g := gQ c d A.L (alphaPairOf d) (NestPairs.ofChains (chainInputs_of d A.hzero))
  g6 := gD6 c A.L (NestPairs.ofChains (chainInputs_of d A.hzero))
  b2 := A.T.y
  b2_lands := ⟨A.T.lands₁, A.T.lands₂, A.T.lands₃⟩
  b2_lands' := A.T.lands₁'
  b2_fix := b2_fix_of_lands d.hN d.bottcher A.T.lands₁ A.T.lands₂
  b2_not_int := by
    have h := Work.ELTop.landing_notMem_interior d.hN A.T.lands₁
    simpa [Work.EL.b2a] using h
  b2_mem_D := b2_mem_D_of_inputs A
  Dnest_sub := Dnest_sub_of_inputs A
  Dnest_cl := Dnest_cl_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.T A.hL
  b2_locInj := by
    have hfix : Work.Landing.Tsq c A.T.y = A.T.y :=
      b2_fix_of_lands d.hN d.bottcher A.T.lands₁ A.T.lands₂
    refine b2_locInj_of hfix ?_
    refine Work.ELAssembly.b2_not_postcrit_of d.hN A.hzero ⟨?_, ?_⟩ hfix A.T.lands₁
    · have heq : (fun n : ℕ => (Work.Landing.Tsq c)^[5 * n] c)
          = fun n : ℕ => (Work.EL.F c)^[n] c := by
        funext n
        rw [Function.iterate_mul]
        rfl
      rw [heq]
      exact d.crit.1
    · intro n
      have hn : (Work.Landing.Tsq c)^[5 * n] c = (Work.EL.F c)^[n] c := by
        rw [Function.iterate_mul]
        rfl
      rw [hn]
      exact d.crit.2 n
  cutA_mem := (cut_mem_of_inputs A).1
  cutB_mem := (cut_mem_of_inputs A).2.1
  cutC_mem := (cut_mem_of_inputs A).2.2
  SP := A.SP
  Pa_far := Pa_far_of d fl
  side_disj := (sides_alphaPairOf d Work.TopJordan.jordanForm).disjoint
  curveF := curveF_of_alphaPair d
  nest_side := fun P Q harc hdisj => nest_side_of_nearArc d.hN Work.TopJordan.jordanForm P Q harc hdisj
  Qmem := fun n => Qmem_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) (fun m => Qne_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.hzero m) A.hL n
  Dmem := fun n => Dmem_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.hL
    (D_adm_of_inputs A) (arm_arcLen_ne d (NestPairs.ofChains (chainInputs_of d A.hzero))).1
    (arm_arcLen_ne d (NestPairs.ofChains (chainInputs_of d A.hzero))).2.1
    (arm_arcLen_ne d (NestPairs.ofChains (chainInputs_of d A.hzero))).2.2 n
  Q_adm := fun n => Q_adm_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) (fun m => Qne_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.hzero m) n
  D_adm := D_adm_of_inputs A
  Qp_disj := Qp_disj_of_inputs A
  z1_near_Q := fun n => z1_near_Q_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) Work.TopJordan.jordanForm n (Qne_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.hzero n)
  base_shift := base_shift_of d (NestPairs.ofChains (chainInputs_of d A.hzero))
  Qne := fun n => Qne_of d (NestPairs.ofChains (chainInputs_of d A.hzero)) A.hzero n
  pbQ := fun n => pullQ_bij (qPullInputs_of A.hL (hcvQ_of A)) (polyAdmQ A) n
  pbD := fun n => pullD_bij (dPullInputs_of A.hL (hcvD_of A)) (polyAdmD A) n
  g_left := gQ_left (pullQ_bij (qPullInputs_of A.hL (hcvQ_of A)) (polyAdmQ A) 0)
  g_mem := gQ_mem (pullQ_bij (qPullInputs_of A.hL (hcvQ_of A)) (polyAdmQ A) 0)
  g_diff := diffOn_gQ (pullQ_bij (qPullInputs_of A.hL (hcvQ_of A)) (polyAdmQ A) 0)
  g6_left := gD6_left (pullD_bij (dPullInputs_of A.hL (hcvD_of A)) (polyAdmD A) 0)
  g6_mem := gD6_mem (pullD_bij (dPullInputs_of A.hL (hcvD_of A)) (polyAdmD A) 0)
  g6_diff := diffOn_gD6 (pullD_bij (dPullInputs_of A.hL (hcvD_of A)) (polyAdmD A) 0)
  pot_F := fun z => by
    rw [Work.ELNest.F_eq_tantibar, pot_iterate d 10 z]
    norm_num
  pot_f6 := fun z => by
    rw [Work.ELNest.F6_eq_tantibar, pot_iterate d 6 z]
    norm_num

end Work.ELAssembly
