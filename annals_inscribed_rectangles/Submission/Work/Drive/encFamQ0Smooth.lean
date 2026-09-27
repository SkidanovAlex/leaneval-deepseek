import Mathlib
import Submission.Work.Drive.encFamQ0
import Submission.Work.Drive.encodedFamily
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.contDiff_shear_thetaS
import Submission.Work.Drive.diskHomotopyParamFamily
import Submission.Work.Drive.mk2CLM
import Submission.Work.Drive.encParReparam
import Submission.Work.Drive.encFamBoxReparam

/-!
# The smoothness of the `hodd` family `encFamQ0`

`Work.Drive.localSard_family_in_open` (the localized parametric Sard of §2.1 of
`NOTES_LEAD_hodd_blockT6.md`) needs, for the family it is applied to, the joint smoothness
`(parameter, box point) ↦ chain` of its three chains and the smoothness of each chain at a fixed
parameter.  For the design's family `Work.Drive.encFamQ0` (`Drive/encFamQ0.lean`) — whose parameter
space is the nested product `EncParQ0` and which is fed to the Sard through the linear
reparametrisation `Work.Drive.encParEquiv` (`Drive/encParReparam.lean`) — neither was on disk.

This file supplies both, in the shapes the two consumers need:

* `Work.Drive.contMDiff_encFamQ0_fam` — the `hG` of `Work.Drive.hrich_reparam_encParEquiv` (joint
  smoothness in `(s, x) ∈ 𝔼¹⁸ × 𝔼³`);
* `Work.Drive.contMDiff_encFamQ0_chain` — the `hsmooth` of `localSard_family_in_open`.

The seeds are Mathlib's `ContDiff` combinators together with the joint smoothness of the design's shear
and level twist `Work.Drive.contDiff_shear_thetaS` and the class perturbation
`Work.Drive.contMDiffAt_classMap_prod`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.projCharted Work.Drive.isManifold_projCharted

set_option maxHeartbeats 4000000

noncomputable section

/-- The product smooth structure on `ℝP³ × ℝ` (model `𝔼³ × ℝ`), from which
`Work.Drive.projTimesLineCharted` is obtained by the linear model change `Work.Drive.psiLin`. -/
local instance instProdChartedPlaneLevelE :
    ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ) (Projectivization ℝ (Eucl 3) × ℝ) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  exact prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ

/-! ## 1. The coordinate projections of the parameter space -/

theorem contDiff_q0P : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : EncParQ0 => q0P t) :=
  contDiff_fst

theorem contDiff_q0Q0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : EncParQ0 => q0Q0 t) :=
  contDiff_fst.comp contDiff_snd

theorem contDiff_q0Q1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : EncParQ0 => q0Q1 t) :=
  contDiff_fst.comp (contDiff_snd.comp contDiff_snd)

theorem contDiff_q0Q2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : EncParQ0 => q0Q2 t) :=
  contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))

theorem contDiff_q0R1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : EncParQ0 => q0R1 t) :=
  contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))

theorem contDiff_q0R2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : EncParQ0 => q0R2 t) :=
  contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))

/-! ## 2. The two easy blocks (`1` and `2`) -/

/-- The class part of block `1`: `A` composed with the sheared plane parameter. -/
theorem contMDiff_encFamQ0_class_one
    (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A) :
    ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        A (shear (q0Q1 z.1) (mk2CLM z.2))) :=
  hA.comp (contMDiff_iff_contDiff.mpr <| contDiff_shear_thetaS.1.comp <|
    (contDiff_q0Q1.comp contDiff_fst).prodMk (mk2CLM.contDiff.comp contDiff_snd))

/-- The level part of block `1`: the twist `thetaS` at the parameter `q0R1` and the level coordinate. -/
theorem contMDiff_encFamQ0_level_one :
    ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) => thetaS (q0R1 z.1) (z.2 2)) :=
  contMDiff_iff_contDiff.mpr <| contDiff_shear_thetaS.2.comp <|
    (contDiff_q0R1.comp contDiff_fst).prodMk (coordCLM2.contDiff.comp contDiff_snd)

/-- The class part of block `2`. -/
theorem contMDiff_encFamQ0_class_two
    (B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B) :
    ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        B (shear (q0Q2 z.1) (mk2CLM z.2))) :=
  hB.comp (contMDiff_iff_contDiff.mpr <| contDiff_shear_thetaS.1.comp <|
    (contDiff_q0Q2.comp contDiff_fst).prodMk (mk2CLM.contDiff.comp contDiff_snd))

/-- The level part of block `2`. -/
theorem contMDiff_encFamQ0_level_two :
    ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) => thetaS (q0R2 z.1) (z.2 2)) :=
  contMDiff_iff_contDiff.mpr <| contDiff_shear_thetaS.2.comp <|
    (contDiff_q0R2.comp contDiff_fst).prodMk (coordCLM2.contDiff.comp contDiff_snd)

/-- **The joint smoothness of blocks `1` and `2`** into the product structure on `ℝP³ × ℝ`. -/
theorem contMDiff_encFamQ0_block_one_two_prodCharted
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B) :
    (ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
          (A (shear (q0Q1 z.1) (mk2CLM z.2)), thetaS (q0R1 z.1) (z.2 2)))) ∧
      (ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
          (B (shear (q0Q2 z.1) (mk2CLM z.2)), thetaS (q0R2 z.1) (z.2 2)))) := by
  constructor
  · rw [modelWithCornersSelf_prod]
    exact (contMDiff_encFamQ0_class_one A hA).prodMk (contMDiff_encFamQ0_level_one)
  · rw [modelWithCornersSelf_prod]
    exact (contMDiff_encFamQ0_class_two B hB).prodMk (contMDiff_encFamQ0_level_two)


/-! ## 3. Block `0` (the class-perturbed homotopy at the sheared point) -/

/-- The class part of block `0`: `classMap (betaG (x 2) • p)` applied to the homotopy at the sheared
plane point. -/
theorem contMDiff_encFamQ0_class_zero
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1)))) :
    ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        classMap (betaG (z.2 2) • q0P z.1)
          (H (z.2 2, shear (q0Q0 z.1) (mk2CLM z.2)))) := by
  intro z
  have h1 : ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (Eucl 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z' : EncParQ0 × EuclideanSpace ℝ (Fin 3) => betaG (z'.2 2) • q0P z'.1) :=
    contMDiff_iff_contDiff.mpr <|
      (contDiff_betaG.comp (coordCLM2.contDiff.comp contDiff_snd)).smul
        (contDiff_q0P.comp contDiff_fst)
  have h2 : ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z' : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        H (z'.2 2, shear (q0Q0 z'.1) (mk2CLM z'.2))) := by
    have hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z' : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
          mk3CLM (shear (q0Q0 z'.1) (mk2CLM z'.2), z'.2 2)) :=
      mk3CLM.contDiff.comp
        ((contDiff_shear_thetaS.1.comp
            ((contDiff_q0Q0.comp contDiff_fst).prodMk
              (mk2CLM.contDiff.comp contDiff_snd))).prodMk
          (coordCLM2.contDiff.comp contDiff_snd))
    refine (hH.comp hX.contMDiff).congr (fun z' => ?_)
    simp only [Function.comp_def, mk3CLM_apply_zero, mk3CLM_apply_one, mk3CLM_apply_two, mk2_eta]
  have hpair := (h1.contMDiffAt (x := z)).prodMk (h2.contMDiffAt (x := z))
  have hcomp := (contMDiffAt_classMap_prod (betaG (z.2 2) • q0P z.1)
    (H (z.2 2, shear (q0Q0 z.1) (mk2CLM z.2)))).comp z hpair
  simpa only [Function.comp_def] using hcomp


/-- **Block `0` into the product structure**: the pair `(class, c₀)` of the class-perturbed homotopy. -/
theorem contMDiff_encFamQ0_block_zero_prodCharted
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1)))) :
    ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        (clsSh (chartPert (betaG (z.2 2) • q0P z.1)
          (capOf (H (z.2 2, shear (q0Q0 z.1) (mk2CLM z.2))))), c₀)) := by
  have hclass := contMDiff_encFamQ0_class_zero H hH
  have hfun : (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        (clsSh (chartPert (betaG (z.2 2) • q0P z.1)
          (capOf (H (z.2 2, shear (q0Q0 z.1) (mk2CLM z.2))))), c₀))
      = (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        (classMap (betaG (z.2 2) • q0P z.1)
          (H (z.2 2, shear (q0Q0 z.1) (mk2CLM z.2))), c₀)) := by
    funext z
    simp only [clsSh_chartPert, clsSh_capOf]
  rw [hfun]
  rw [modelWithCornersSelf_prod]
  have hconst : ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : EncParQ0 × EuclideanSpace ℝ (Fin 3) => c₀) := contMDiff_const
  exact hclass.prodMk hconst

/-! ## 4. The three chains of the family, jointly in the parameter -/

/-- **The joint smoothness of the design's family, parameter in `EncParQ0`**, into the *product*
structure on `ℝP³ × ℝ` (from which the transported structure is obtained by the model change
`Work.Drive.psiLin`). -/
theorem contMDiff_encFamQ0_famPar_prodCharted
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B) :
    ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) => encFamQ0 H A B c₀ z.1 k z.2) := by
  intro k
  obtain ⟨h12a, h12b⟩ := contMDiff_encFamQ0_block_one_two_prodCharted A B hA hB
  fin_cases k
  · show ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        (clsSh (chartPert (betaG (z.2 2) • q0P z.1)
          (capOf (H (z.2 2, shear (q0Q0 z.1) (mk2CLM z.2))))), c₀))
    exact contMDiff_encFamQ0_block_zero_prodCharted H c₀ hH
  · show ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        (A (shear (q0Q1 z.1) (mk2CLM z.2)), thetaS (q0R1 z.1) (z.2 2)))
    exact h12a
  · show ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) =>
        (B (shear (q0Q2 z.1) (mk2CLM z.2)), thetaS (q0R2 z.1) (z.2 2)))
    exact h12b

section Transported

attribute [local instance] Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

/-- **The joint smoothness of the design's family** in the transported `4`-manifold structure
`Work.Drive.projTimesLineCharted` — the smoothness `localSard_family_in_open` needs for its family. -/
theorem contMDiff_encFamQ0_famPar
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B) :
    ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) => encFamQ0 H A B c₀ z.1 k z.2) := by
  intro k
  have h := contMDiff_encFamQ0_famPar_prodCharted H A B c₀ hH hA hB k
  unfold Work.Drive.projTimesLineCharted
  exact fun z => (Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel' (𝕜 := ℝ)
    (I := modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
    (E := EuclideanSpace ℝ (Fin 3) × ℝ) (E' := EuclideanSpace ℝ (Fin 4))
    (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin.toHomeomorph psiLin.contDiff
    psiLin.symm.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (f := fun z : EncParQ0 × EuclideanSpace ℝ (Fin 3) => encFamQ0 H A B c₀ z.1 k z.2)
    Set.univ z).mpr (h z)

/-- **The `hG` of `Work.Drive.hrich_reparam_encParEquiv`**: the joint smoothness of the design's family
after the linear reparametrisation `Work.Drive.encParEquiv : 𝔼¹⁸ ≃L EncParQ0`. -/
theorem contMDiff_encFamQ0_fam
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B) :
    ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3) =>
        encFamQ0 H A B c₀ (encParEquiv q.1) k q.2) := by
  intro k
  let W : EncParQ0 × EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3) × ℝ :=
    fun z => encFamQ0 H A B c₀ z.1 k z.2
  have hW : ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W := by
    simpa only [W] using contMDiff_encFamQ0_famPar H A B c₀ hH hA hB k
  let Λ : (EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      (EncParQ0 × EuclideanSpace ℝ (Fin 3)) :=
    ((encParEquiv : EuclideanSpace ℝ (Fin 18) →L[ℝ] EncParQ0).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 18))
        (EuclideanSpace ℝ (Fin 3)))).prod
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 18)) (EuclideanSpace ℝ (Fin 3)))
  have hΛ : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 18) × EuclideanSpace ℝ (Fin 3) =>
        (encParEquiv q.1, q.2)) := by
    refine (contMDiff_iff_contDiff.mpr Λ.contDiff).congr (fun q => ?_)
    simp only [Λ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
    rfl
  have hcomp := hW.comp hΛ
  simpa only [Function.comp_def, W, Λ, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply] using hcomp

/-- **The `hsmooth` of `localSard_family_in_open`**: the smoothness of each chain at a fixed
(reparametrised) parameter. -/
theorem contMDiff_encFamQ0_chain
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B) :
    ∀ (k : Fin 3) (s : EuclideanSpace ℝ (Fin 18)),
      ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => encFamQ0 H A B c₀ (encParEquiv s) k x) := by
  intro k s
  let W : EncParQ0 × EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3) × ℝ :=
    fun z => encFamQ0 H A B c₀ z.1 k z.2
  have hW : ContMDiff (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W := by
    simpa only [W] using contMDiff_encFamQ0_famPar H A B c₀ hH hA hB k
  have hΛ : ContMDiff (𝓡 3)
      (modelWithCornersSelf ℝ (EncParQ0 × EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => (encParEquiv s, x)) :=
    contMDiff_iff_contDiff.mpr
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => (encParEquiv s, x)))
  have hcomp := hW.comp hΛ
  simpa only [Function.comp_def, W] using hcomp

end Transported

end

end Work.Drive
