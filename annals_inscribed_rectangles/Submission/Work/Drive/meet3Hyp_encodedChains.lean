import Mathlib
import Submission.Work.Drive.diskHomotopyChain
import Submission.Work.Drive.encodedTransverse
import Submission.Work.Drive.mfderivModelChange
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.mk2CLM

/-!
# `Meet3Hyp` for the encoded chains of the ends clause (the `trans` field)

`Work.Drive.HasClassLinearization` (`classTripleOdd.lean`) asks for `Meet3Hyp` of the three *encoded*
chains of the linearisation.  Its four fields are

* `smooth` — proved elsewhere (`contMDiff_chain_projTimesLine`, `…_plane`);
* `seam` — invariance under the antipodal involution of the parameter cube on the seam;
* `trans` — `TripleTransverse` of the three manifold derivatives at every meeting point.  **This is the
  content of this file**: the derivative of the encoded chains is computed explicitly, and then
  `TripleTransverse` is *equivalent* (`Work.Drive.tripleTransverseE_encoded`) to two checkable
  conditions — the homotopy chain is a **submersion** and the two class derivatives **span**;
* `face` — genuine transversality data of the configuration, which stays a hypothesis.
-/

namespace Work.Drive

open Manifold Set Function
open scoped Manifold ContDiff Topology

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

attribute [local instance] Work.Drive.projCharted

/-- The product smooth structure on `ℝP³ × ℝ` (model `ℝ³ × ℝ`). -/
local instance instProdChartedProjLine :
    ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ) (Projectivization ℝ (Eucl 3) × ℝ) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ

/-- `pt2` and `mk2` are the same map. -/
lemma pt2_eq_mk2 (a b : ℝ) : pt2 a b = mk2 a b := by
  ext i
  fin_cases i <;> simp [pt2, mk2]

/-! ## 0. The three encoded blocks as functions -/

section Blocks

variable {M : Type*}

/-- Block `0` of an encoded chain, as a function. -/
lemma encodedChains_fun_zero (W : EuclideanSpace ℝ (Fin 3) → M)
    (A B : EuclideanSpace ℝ (Fin 2) → M) (c : ℝ) :
    encodedChains W A B c 0 = fun x => (W x, c) := by
  funext x; exact encodedChains_zero W A B c x

/-- Block `1` of an encoded chain, as a function. -/
lemma encodedChains_fun_one (W : EuclideanSpace ℝ (Fin 3) → M)
    (A B : EuclideanSpace ℝ (Fin 2) → M) (c : ℝ) :
    encodedChains W A B c 1 = fun x => (A (pt2 (x 0) (x 1)), x 2) := by
  funext x; exact encodedChains_one W A B c x

/-- Block `2` of an encoded chain, as a function. -/
lemma encodedChains_fun_two (W : EuclideanSpace ℝ (Fin 3) → M)
    (A B : EuclideanSpace ℝ (Fin 2) → M) (c : ℝ) :
    encodedChains W A B c 2 = fun x => (B (pt2 (x 0) (x 1)), x 2) := by
  funext x; exact encodedChains_two W A B c x

end Blocks

/-- Block `0` of the encoded chain of a homotopy, in the `mk2` form of the block derivatives. -/
lemma encChains_H_zero (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) :
    encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 0
      = fun x : EuclideanSpace ℝ (Fin 3) => (H (x 2, mk2 (x 0) (x 1)), c₀) := by
  funext x
  simp [encodedChains, pt2_eq_mk2]

/-- Block `1` of the encoded chain of a homotopy, in the `mk2` form of the block derivatives. -/
lemma encChains_H_one (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) :
    encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 1
      = fun x : EuclideanSpace ℝ (Fin 3) => (A (mk2 (x 0) (x 1)), x 2) := by
  funext x
  simp [encodedChains, pt2_eq_mk2]

/-- Block `2` of the encoded chain of a homotopy, in the `mk2` form of the block derivatives. -/
lemma encChains_H_two (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) :
    encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 2
      = fun x : EuclideanSpace ℝ (Fin 3) => (B (mk2 (x 0) (x 1)), x 2) := by
  funext x
  simp [encodedChains, pt2_eq_mk2]

/-! ## 1. The two block derivatives, in the product structure on `ℝP³ × ℝ` -/

section Product

/-- The manifold derivative of the linear projection `mk2CLM` (both manifolds carrying their self
models). -/
lemma mfderiv_mk2CLM (x : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) (𝓡 2) (mk2CLM : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)) x
      = mk2CLM :=
  (hasMFDerivAt_iff_hasFDerivAt.mpr (ContinuousLinearMap.hasFDerivAt mk2CLM)).mfderiv

/-- The manifold derivative of the linear functional `coordCLM2` (self models). -/
lemma mfderiv_coordCLM2 (x : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) (𝓘(ℝ, ℝ))
      (coordCLM2 : EuclideanSpace ℝ (Fin 3) → ℝ) x = coordCLM2 :=
  (hasMFDerivAt_iff_hasFDerivAt.mpr (ContinuousLinearMap.hasFDerivAt coordCLM2)).mfderiv

/-- `u ↦ u 2` is manifold-differentiable (it is a continuous linear map). -/
lemma mdifferentiableAt_coord2 (x : EuclideanSpace ℝ (Fin 3)) :
    MDifferentiableAt (𝓡 3) (𝓘(ℝ, ℝ)) (fun u : EuclideanSpace ℝ (Fin 3) => u 2) x := by
  have h : (fun u : EuclideanSpace ℝ (Fin 3) => u 2) = coordCLM2 := by
    funext u; rw [coordCLM2_apply]
  rw [h]
  exact (hasMFDerivAt_iff_hasFDerivAt.mpr
    (ContinuousLinearMap.hasFDerivAt coordCLM2)).mdifferentiableAt

lemma mfderiv_coord2 (x : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) (𝓘(ℝ, ℝ)) (fun u : EuclideanSpace ℝ (Fin 3) => u 2) x = coordCLM2 := by
  have h : (fun u : EuclideanSpace ℝ (Fin 3) => u 2) = coordCLM2 := by
    funext u; rw [coordCLM2_apply]
  rw [h, mfderiv_coordCLM2]

/-- **The block-`0` derivative, in the product structure.** -/
theorem mfderiv_encodedChain_zero_prod
    (W : EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (x : EuclideanSpace ℝ (Fin 3))
    (hW : MDifferentiableAt (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) W x) :
    mfderiv (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ))
        (fun y : EuclideanSpace ℝ (Fin 3) => (W y, c₀)) x
      = encBlock0 (mfderiv (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) W x) := by
  rw [show (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) =
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod (modelWithCornersSelf ℝ ℝ)
    from modelWithCornersSelf_prod]
  have hconst : MDifferentiableAt (𝓡 3) (𝓘(ℝ, ℝ))
      (fun _ : EuclideanSpace ℝ (Fin 3) => c₀) x := mdifferentiableAt_const
  have hprod := mfderiv_prodMk (x := x) (f := W)
    (g := fun _ : EuclideanSpace ℝ (Fin 3) => c₀) hW hconst
  rw [hprod]
  have hc : mfderiv (𝓡 3) (𝓘(ℝ, ℝ)) (fun _ : EuclideanSpace ℝ (Fin 3) => c₀) x = 0 :=
    mfderiv_const
  rw [hc]
  rfl

/-- **The block-`1`/`2` derivative, in the product structure.** -/
theorem mfderiv_encodedChain_plane_prod
    (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (x : EuclideanSpace ℝ (Fin 3))
    (hA : MDifferentiableAt (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A
      (mk2 (x 0) (x 1))) :
    mfderiv (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ))
        (fun y : EuclideanSpace ℝ (Fin 3) => (A (mk2 (y 0) (y 1)), y 2)) x
      = encBlock (mfderiv (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A
          (mk2 (x 0) (x 1))) := by
  rw [show (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) =
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod (modelWithCornersSelf ℝ ℝ)
    from modelWithCornersSelf_prod]
  have hmk : MDifferentiableAt (𝓡 3) (𝓡 2)
      (mk2CLM : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)) x :=
    (hasMFDerivAt_iff_hasFDerivAt.mpr (ContinuousLinearMap.hasFDerivAt mk2CLM)).mdifferentiableAt
  have hfun : (fun y : EuclideanSpace ℝ (Fin 3) => A (mk2 (y 0) (y 1))) = A ∘ mk2CLM := by
    funext y; rw [Function.comp_apply, mk2CLM_apply]
  have hcomp : MDifferentiableAt (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (fun y : EuclideanSpace ℝ (Fin 3) => A (mk2 (y 0) (y 1))) x := by
    rw [hfun]; exact hA.comp x hmk
  have hg : MDifferentiableAt (𝓡 3) (𝓘(ℝ, ℝ))
      (fun y : EuclideanSpace ℝ (Fin 3) => y 2) x := mdifferentiableAt_coord2 x
  have hprod := mfderiv_prodMk (x := x)
    (f := fun y : EuclideanSpace ℝ (Fin 3) => A (mk2 (y 0) (y 1)))
    (g := fun y : EuclideanSpace ℝ (Fin 3) => y 2) hcomp hg
  rw [hprod]
  have h1 : mfderiv (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (fun y : EuclideanSpace ℝ (Fin 3) => A (mk2 (y 0) (y 1))) x
      = (mfderiv (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A
          (mk2 (x 0) (x 1))).comp mk2CLM := by
    rw [hfun, mfderiv_comp x hA hmk, mfderiv_mk2CLM x, mk2CLM_apply]
    rfl
  rw [h1, mfderiv_coord2]
  rfl

end Product

end

end Work.Drive

namespace Work.Drive

open Manifold Set Function
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 1000000

attribute [local instance] Work.Drive.projCharted

/-- The product smooth structure on `ℝP³ × ℝ` (model `ℝ³ × ℝ`). -/
local instance instProdChartedProjLine' :
    ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ) (Projectivization ℝ (Eucl 3) × ℝ) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ

/-! ## 2. The block derivatives in the transported structure `projTimesLineCharted` -/

section Proj

attribute [local instance] Work.Drive.projTimesLineCharted
  Work.Drive.isManifold_projTimesLineCharted

/-- The chart relation of the transported structure: its preferred chart is `psiLin` composed with the
product chart. -/
lemma chartAt_projTimesLine_eq (p : Projectivization ℝ (Eucl 3) × ℝ) :
    (fun y : Projectivization ℝ (Eucl 3) × ℝ =>
        @chartAt (EuclideanSpace ℝ (Fin 4)) _ _ _
          Work.Drive.projTimesLineCharted p y)
      = fun y => psiLin (chartAt (EuclideanSpace ℝ (Fin 3) × ℝ) p y) :=
  chartAt_chartedSpaceChangeModel_apply (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin p

/-- **The block-`0` derivative in the transported structure.** -/
theorem mfderiv_encodedChain_zero (c₀ : ℝ) (x : EuclideanSpace ℝ (Fin 3))
    (W : EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3))
    (hW : MDifferentiableAt (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) W x) :
    mfderiv (𝓡 3) (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 3) => (W y, c₀)) x
      = (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp
          (encBlock0 (mfderiv (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) W x)) := by
  have hprod : MDifferentiableAt (𝓡 3)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ))
      (fun y : EuclideanSpace ℝ (Fin 3) => (W y, c₀)) x := by
    rw [show (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) =
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod (modelWithCornersSelf ℝ ℝ)
      from modelWithCornersSelf_prod]
    have hconst : MDifferentiableAt (𝓡 3) (𝓘(ℝ, ℝ))
        (fun _ : EuclideanSpace ℝ (Fin 3) => c₀) x := mdifferentiableAt_const
    exact hW.prodMk hconst
  rw [mfderiv_of_chartAt_eq (k := 3) psiLin
    (fun p => chartAt_projTimesLine_eq p) hprod]
  rw [mfderiv_encodedChain_zero_prod W c₀ x hW]
  rfl

/-- **The block-`1`/`2` derivative in the transported structure.** -/
theorem mfderiv_encodedChain_plane (x : EuclideanSpace ℝ (Fin 3))
    (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hA : MDifferentiableAt (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A
      (mk2 (x 0) (x 1))) :
    mfderiv (𝓡 3) (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 3) => (A (mk2 (y 0) (y 1)), y 2)) x
      = (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp
          (encBlock (mfderiv (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A
            (mk2 (x 0) (x 1)))) := by
  have hprod : MDifferentiableAt (𝓡 3)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ))
      (fun y : EuclideanSpace ℝ (Fin 3) => (A (mk2 (y 0) (y 1)), y 2)) x := by
    rw [show (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) =
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod (modelWithCornersSelf ℝ ℝ)
      from modelWithCornersSelf_prod]
    have hg : MDifferentiableAt (𝓡 3) (𝓘(ℝ, ℝ))
        (fun y : EuclideanSpace ℝ (Fin 3) => y 2) x := mdifferentiableAt_coord2 x
    have hf : MDifferentiableAt (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (fun y : EuclideanSpace ℝ (Fin 3) => A (mk2 (y 0) (y 1))) x := by
      have hfun : (fun y : EuclideanSpace ℝ (Fin 3) => A (mk2 (y 0) (y 1))) = A ∘ mk2CLM := by
        funext y; rw [Function.comp_apply, mk2CLM_apply]
      have hmk : MDifferentiableAt (𝓡 3) (𝓡 2)
          (mk2CLM : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)) x :=
        (hasMFDerivAt_iff_hasFDerivAt.mpr (ContinuousLinearMap.hasFDerivAt mk2CLM)).mdifferentiableAt
      rw [hfun]
      exact hA.comp x hmk
    exact hf.prodMk hg
  rw [mfderiv_of_chartAt_eq (k := 3) psiLin
    (fun p => chartAt_projTimesLine_eq p) hprod]
  rw [mfderiv_encodedChain_plane_prod A x hA]
  rfl

end Proj

end

end Work.Drive

namespace Work.Drive

open Manifold Set Function
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 1000000

attribute [local instance] Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted
  Work.Drive.isManifold_projTimesLineCharted

/-- The linear isometry `psiLin` in the composition form used by the chain rule. -/
lemma psiLin_comp_apply (f : EuclideanSpace ℝ (Fin 3) →L[ℝ]
    (EuclideanSpace ℝ (Fin 3) × ℝ)) (v : EuclideanSpace ℝ (Fin 3)) :
    ((psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp f) v
      = psiLin (f v) := rfl

/-- **The `trans` field of `Meet3Hyp` for the encoded chains**: `TripleTransverse` of the three
manifold derivatives follows from (i) the *submersion* of the homotopy chain at `x 0` and (ii) the
spanning of the two class derivatives at the two class coordinates. -/
theorem tripleTransverse_encodedChains
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hW : MDifferentiableAt (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, mk2 (y 0) (y 1))) (x 0))
    (hA : MDifferentiableAt (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A
      (mk2 ((x 1) 0) ((x 1) 1)))
    (hB : MDifferentiableAt (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) B
      (mk2 ((x 2) 0) ((x 2) 1)))
    (hsub : Function.Surjective (mfderiv (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, mk2 (y 0) (y 1))) (x 0)))
    (hspan : (mfderiv (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A
          (mk2 ((x 1) 0) ((x 1) 1))).range ⊔
        (mfderiv (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) B
          (mk2 ((x 2) 0) ((x 2) 1))).range = ⊤) :
    TripleTransverse
      (mfderiv (𝓡 3) (𝓡 4) (encodedChains
        (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 0) (x 0))
      (mfderiv (𝓡 3) (𝓡 4) (encodedChains
        (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 1) (x 1))
      (mfderiv (𝓡 3) (𝓡 4) (encodedChains
        (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 2) (x 2)) := by
  rw [encChains_H_zero, encChains_H_one, encChains_H_two]
  rw [mfderiv_encodedChain_zero c₀ (x 0) _ hW,
    mfderiv_encodedChain_plane (x 1) A hA,
    mfderiv_encodedChain_plane (x 2) B hB]
  have hmain : TripleTransverseE
      (encBlock0 (E := EuclideanSpace ℝ (Fin 3)) (mfderiv (𝓡 3) (𝓡 3)
        (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, mk2 (y 0) (y 1))) (x 0)))
      (encBlock (E := EuclideanSpace ℝ (Fin 3)) (mfderiv (𝓡 2) (𝓡 3) A
        (mk2 ((x 1) 0) ((x 1) 1))))
      (encBlock (E := EuclideanSpace ℝ (Fin 3)) (mfderiv (𝓡 2) (𝓡 3) B
        (mk2 ((x 2) 0) ((x 2) 1)))) :=
    tripleTransverseE_encoded (E := EuclideanSpace ℝ (Fin 3))
      (mfderiv (𝓡 3) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, mk2 (y 0) (y 1)))
        (x 0))
      hsub
      (mfderiv (𝓡 2) (𝓡 3) A (mk2 ((x 1) 0) ((x 1) 1)))
      (mfderiv (𝓡 2) (𝓡 3) B (mk2 ((x 2) 0) ((x 2) 1)))
      hspan
  exact (tripleTransverseE_iff _ _ _).mpr
    ((tripleTransverseE_comp_continuousLinearEquiv psiLin
        (encBlock0 (E := EuclideanSpace ℝ (Fin 3)) (mfderiv (𝓡 3) (𝓡 3)
          (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, mk2 (y 0) (y 1))) (x 0)))
        (encBlock (E := EuclideanSpace ℝ (Fin 3)) (mfderiv (𝓡 2) (𝓡 3) A
          (mk2 ((x 1) 0) ((x 1) 1))))
        (encBlock (E := EuclideanSpace ℝ (Fin 3)) (mfderiv (𝓡 2) (𝓡 3) B
          (mk2 ((x 2) 0) ((x 2) 1))))).mpr hmain)

end

end Work.Drive

namespace Work.Drive

open Manifold Set Function
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 1000000

attribute [local instance] Work.Drive.projCharted

/-- The product smooth structure on `ℝP³ × ℝ` (model `ℝ³ × ℝ`). -/
local instance instProdChartedProjLine'' :
    ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ) (Projectivization ℝ (Eucl 3) × ℝ) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ

/-- The differentiability order `⊤` is not zero. -/
lemma top_ne_zero_m3h : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

end

end Work.Drive

namespace Work.Drive

open Manifold Set Function
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 1000000

attribute [local instance] Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted
  Work.Drive.isManifold_projTimesLineCharted

/-- **The `smooth` field of `Meet3Hyp` for the encoded chains.** -/
theorem contMDiff_encodedChains
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) (k : Fin 3)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B) :
    ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ k) := by
  match k with
  | 0 => rw [encChains_H_zero]; exact contMDiff_chain_projTimesLine H c₀ hH
  | 1 => rw [encChains_H_one]; exact contMDiff_chain_projTimesLine_plane A hA
  | 2 => rw [encChains_H_two]; exact contMDiff_chain_projTimesLine_plane B hB

/-- The coordinate form of the seam involution on the `mk2`-coordinates of a cube point. -/
lemma mk2_seamInv_mk2 (x : EuclideanSpace ℝ (Fin 3)) :
    mk2 ((seamInv x) 0) ((seamInv x) 1) = seamInv2 (mk2 (x 0) (x 1)) := by
  ext i
  fin_cases i <;> simp [seamInv, seamInv2, mk2]

/-- **The `seam` field of `Meet3Hyp` for the encoded chains.** -/
theorem seam_encodedChains
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) (k : Fin 3)
    (hH : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      H (t, seamInv2 y) = H (t, y))
    (hA : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → A (seamInv2 y) = A y)
    (hB : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → B (seamInv2 y) = B y)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : onSeam x) :
    encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ k x
      = encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ k
          (seamInv x) := by
  have hseam2 : onSeam2 (mk2 (x 0) (x 1)) := onSeam2_of_onSeam x hx
  have hcoord := mk2_seamInv_mk2 x
  match k with
  | 0 =>
    simp only [encChains_H_zero, hcoord, seamInv_apply_two]
    rw [hH (x 2) _ hseam2]
  | 1 =>
    simp only [encChains_H_one, hcoord, seamInv_apply_two]
    rw [hA _ hseam2]
  | 2 =>
    simp only [encChains_H_two, hcoord, seamInv_apply_two]
    rw [hB _ hseam2]

/-- **`Meet3Hyp` for the encoded chains of the homotopy/plane triad**, from the submersion of the
homotopy chain, the spanning of the two class derivatives, the seam invariance of the three maps, and
the face condition (which is genuine transversality data and stays a hypothesis). -/
theorem meet3Hyp_encodedChains
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hseamH : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      H (t, seamInv2 y) = H (t, y))
    (hseamA : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → A (seamInv2 y) = A y)
    (hseamB : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → B (seamInv2 y) = B y)
    (hsub : ∀ y ∈ Submission.Drive.unitBox 2,
      Function.Surjective (mfderiv (𝓡 3) (𝓡 3)
        (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) y))
    (hspan : ∀ (y y' : EuclideanSpace ℝ (Fin 2)),
      y ∈ Submission.Drive.unitBox 1 → y' ∈ Submission.Drive.unitBox 1 →
      (mfderiv (𝓡 2) (𝓡 3) A y).range ⊔ (mfderiv (𝓡 2) (𝓡 3) B y').range = ⊤)
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 0 (x 0)
        = encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 1
            (x 1) →
      encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 0 (x 0)
        = encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 2
            (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          TripleCommonDir
            (mfderiv (𝓡 3) (𝓡 4) (encodedChains
              (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 0) (x 0))
            (mfderiv (𝓡 3) (𝓡 4) (encodedChains
              (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 1) (x 1))
            (mfderiv (𝓡 3) (𝓡 4) (encodedChains
              (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀ 2) (x 2)) v ∧
          v k i ≠ 0) :
    Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
      (encodedChains (fun y : EuclideanSpace ℝ (Fin 3) => H (y 2, pt2 (y 0) (y 1))) A B c₀) := by
  refine ⟨?_, ?_, hface, ?_⟩
  · intro k
    exact contMDiff_encodedChains H A B c₀ k hH hA hB
  · intro x hx _ _
    refine tripleTransverse_encodedChains H A B c₀ x ?_ ?_ ?_ ?_ ?_
    · exact ((hH.contMDiffAt).mdifferentiableAt top_ne_zero_m3h)
    · exact ((hA.contMDiffAt).mdifferentiableAt top_ne_zero_m3h)
    · exact ((hB.contMDiffAt).mdifferentiableAt top_ne_zero_m3h)
    · exact hsub (x 0) (hx 0)
    · refine hspan (mk2 ((x 1) 0) ((x 1) 1)) (mk2 ((x 2) 0) ((x 2) 1)) ?_ ?_
      · intro i
        fin_cases i
        · simpa [mk2] using hx 1 0
        · simpa [mk2] using hx 1 1
      · intro i
        fin_cases i
        · simpa [mk2] using hx 2 0
        · simpa [mk2] using hx 2 1
  · intro k x hx
    exact seam_encodedChains H A B c₀ k hseamH hseamA hseamB x hx

end

end Work.Drive
