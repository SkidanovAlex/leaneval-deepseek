import Mathlib
import Submission.Work.Thom.ProdMapTools

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-!
# Naturality of the inductive step `Work.Thom.step` under an arbitrary base change

`Submission/Work/Thom/step_natural.lean` proves the naturality of the inductive step
`Work.Thom.step` (and of its two constituents `Work.Thom.stepDisc`, `Work.Thom.stepSph`) for the
*inclusions* `↥W × F → B × F` induced by a subset `W ⊆ B`.  The present file runs the same
argument for an *arbitrary* continuous map `g : C(B', B)`, using the map

`Work.Thom.prodMapA g F : B' × F → B × F`, `(b, v) ↦ (g b, v)`

of `Submission/Work/Thom/ProdMapTools.lean` together with the three commutation identities recorded
there (`discFullMap_comp_prodMapA`, `capMapPairSph_comp_prodMapA`,
`prodSubsetHomeoA_symm_comp_prodMapA`).  The proofs are verbatim transpositions of the ones for the
inclusion, with `baseIncl B W n`, `baseInclBall B W n`, `baseInclMSph B W (n+1)` replaced by
`prodMapA g (EuclideanSpace ℝ (Fin n))`, `prodMapA g (MBall n)`, `prodMapA g (MSph (n+1))`.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-! ## Naturality of `stepDisc` under an arbitrary base change -/

theorem stepDisc_natural_map {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    (relCohMap (prodMapA g (MBall n)) (DiscB B' n) (DiscB B n) (fun _ h => h) ℤ n).hom
        (stepDisc B n τ)
      = stepDisc B' n
          ((relCohMap (prodMapA g (EuclideanSpace ℝ (Fin n))) (Sph B' n) (Sph B n)
            (fun _ h => h) ℤ n).hom τ) := by
  rw [stepDisc, stepDisc]
  rw [relCohMap_compA_apply (DiscB B' n) (DiscB B n) (Sph B n) (prodMapA g (MBall n))
        (CleanA.discFullMap B n) (fun _ h => h) (CleanA.discFullMap_mem B n) (fun _ h => h)
        ℤ n τ]
  rw [relCohMap_compA_apply (DiscB B' n) (Sph B' n) (Sph B n) (CleanA.discFullMap B' n)
        (prodMapA g (EuclideanSpace ℝ (Fin n))) (CleanA.discFullMap_mem B' n) (fun _ h => h)
        (fun _ h => h) ℤ n τ]
  have hm : relCohMap ((CleanA.discFullMap B n).comp (prodMapA g (MBall n))) (DiscB B' n)
        (Sph B n) (fun _ h => h) ℤ n
      = relCohMap ((prodMapA g (EuclideanSpace ℝ (Fin n))).comp (CleanA.discFullMap B' n))
        (DiscB B' n) (Sph B n) (fun _ h => h) ℤ n :=
    relCohMap_congrA (DiscB B' n) (Sph B n) (discFullMap_comp_prodMapA g n)
      (fun _ h => h) (fun _ h => h) ℤ n
  rw [hm]

/-! ## Naturality of `stepSph` under an arbitrary base change -/

theorem stepSph_natural_map {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    (relCohMap (prodMapA g (MSph (n+1))) (SphB B' n) (SphB B n) (fun _ h => h) ℤ n).hom
        (stepSph B n τ)
      = stepSph B' n
          ((relCohMap (prodMapA g (EuclideanSpace ℝ (Fin n))) (Sph B' n) (Sph B n)
            (fun _ h => h) ℤ n).hom τ) := by
  have hinj : Function.Injective ((relCohMap (capMapPairSph B' n) (DiscB B' n) (SphB B' n)
        (CleanA.capMapPairSph_mem_mLower n) ℤ n).hom) :=
    (CleanA.capRelCohIso B' n n).1
  apply hinj
  rw [relCohMap_compA_apply (DiscB B' n) (SphB B' n) (SphB B n) (capMapPairSph B' n)
        (prodMapA g (MSph (n+1))) (CleanA.capMapPairSph_mem_mLower n) (fun _ h => h)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n (stepSph B n τ)]
  rw [stepSph_spec B' n
        ((relCohMap (prodMapA g (EuclideanSpace ℝ (Fin n))) (Sph B' n) (Sph B n)
          (fun _ h => h) ℤ n).hom τ)]
  have hm2 : relCohMap ((prodMapA g (MSph (n+1))).comp (capMapPairSph B' n)) (DiscB B' n)
        (SphB B n) (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n
      = relCohMap ((capMapPairSph B n).comp (prodMapA g (MBall n))) (DiscB B' n)
        (SphB B n) (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n :=
    relCohMap_congrA (DiscB B' n) (SphB B n) (capMapPairSph_comp_prodMapA g n)
      (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx)
      (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n
  rw [hm2]
  rw [← relCohMap_compA_apply (DiscB B' n) (DiscB B n) (SphB B n) (prodMapA g (MBall n))
        (capMapPairSph B n) (fun _ h => h) (CleanA.capMapPairSph_mem_mLower n)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n (stepSph B n τ)]
  rw [stepSph_spec B n τ]
  rw [stepDisc_natural_map g n τ]

/-! ## Naturality of the inductive step -/

theorem step_natural_map {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ)
    (τ : Work.Thom.RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Work.Thom.Sph B n)) :
    (Work.Thom.relCohMap (Work.Thom.prodMapA g (EuclideanSpace ℝ (Fin (n+1))))
      (Work.Thom.Sph B' (n+1)) (Work.Thom.Sph B (n+1)) (fun _ h => h) ℤ (n+1)).hom
        (Work.Thom.step B n τ)
      = Work.Thom.step B' n
          ((Work.Thom.relCohMap (Work.Thom.prodMapA g (EuclideanSpace ℝ (Fin n)))
            (Work.Thom.Sph B' n) (Work.Thom.Sph B n) (fun _ h => h) ℤ n).hom τ) := by
  rw [step, step]
  rw [pairDeltaNatural_restrict (prodMapA g (EuclideanSpace ℝ (Fin (n+1)))) (Sph B' (n+1))
        (Sph B (n+1)) (fun _ h => h) n]
  refine congrArg (fun w => (pairδC (Sph B' (n+1)) n).hom w) ?_
  rw [← stepSph_natural_map g n τ]
  rw [relCohMap_relToAbs_apply (prodMapA g (MSph (n+1))) (SphB B' n) (SphB B n) (fun _ h => h)
        ℤ n (stepSph B n τ)]
  rw [CohMap_comp_apply
        ((prodSubsetHomeoA B' (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
          C(↥(Sph B' (n+1)), B' × MSph (n+1)))
        (prodMapA g (MSph (n+1))) ℤ n
        ((relToAbs ℤ (SphB B n) n).hom (stepSph B n τ))]
  rw [prodSubsetHomeoA_symm_comp_prodMapA g n]
  rw [CohMap_comp_apply
        (restrictMap (prodMapA g (EuclideanSpace ℝ (Fin (n+1)))) (Sph B' (n+1))
          (Sph B (n+1)) (fun _ h => h))
        ((prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
          C(↥(Sph B (n+1)), B × MSph (n+1))) ℤ n
        ((relToAbs ℤ (SphB B n) n).hom (stepSph B n τ))]

end

end Work.Thom
