import Mathlib
import Submission.Work.Whitney.CupDefs
import Submission.Work.Thom.exists_rhoC_compat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# The cap transfer of the first factor's model class (piece (2) of the crux)

`Work.Thom.Mpun_spec` says `jMap (Mpun n Y) = Mn n Y`.  The purpose of this file is the companion
statement that pulling `pr1^*(Mpun n Y)` back along the **cap map** `capX Y n : Y × Dⁿ → tcmX Y n 1`
gives `stepDisc Y n (Mn n Y)`:

  `relCohMap (capX) (DiscB) (tcmA) ((relCohMap (tcmPr1) (tcmA)(Punct)) (Mpun n Y))
     = stepDisc Y n (Mn n Y)`.

Both sides live in `H^n(Y × Dⁿ, Y × S^{n-1})`.  The proof is *pure functoriality*:
`tcmPr1 ∘ capX = discFullMap` as functions (`(y,u) ↦ (y,u)`), and the composite *lands directly* in
the `DiscB`-relative group — which is why no relative-set comparison is needed here.
-/

namespace Work.Whitney

open Work.Thom
open Work.Cohomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

noncomputable section

/-! ## Coordinates of the inverse of the coordinate shuffle -/

/-- The `inl` coordinates of `tcmSumLin`'s inverse. -/
theorem tcmSumLin_symm_fst_coord (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    ((tcmSumLin n 1).symm v).1 i = v (finSumFinEquiv (Sum.inl i)) :=
  Work.Thom.finAddEquivProd_fst (𝕜 := ℝ) (n := n) (m := 1) v i

/-- `capMap` keeps the first `n` coordinates (in the `finSumFinEquiv`-indexing of `tcmSumLin`). -/
theorem capMap_finSumFinEquiv_inl (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (capMap n u) (finSumFinEquiv (Sum.inl i)) = u i := by
  have hidx : finSumFinEquiv (Sum.inl i) = Fin.castSucc i := Fin.ext rfl
  rw [hidx, capMap_castSucc]

/-- **The first `n` coordinates of a cap point are the disc coordinates.** -/
theorem capX_fst (Y : Type) [TopologicalSpace Y] (n : ℕ) (q : Y × MBall n) :
    (capX Y n q).2.1 = q.2.1 := by
  rw [capX_apply]
  ext i
  rw [tcmSumLin_symm_fst_coord, capMap_finSumFinEquiv_inl]

/-! ## The cap image avoids the first relative set -/

/-- The cap map carries the disc boundary into `tcmA`. -/
theorem capX_mem_tcmA (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    ∀ x ∈ DiscB Y n, capX Y n x ∈ tcmA Y n 1 := by
  intro q hq
  show (capX Y n q).2.1 ≠ 0
  rw [capX_fst]
  intro hz
  have h1 : ‖q.2.1‖ = 1 := hq
  rw [hz, norm_zero] at h1
  norm_num at h1

/-- **`tcmPr1 ∘ capX = discFullMap`**: the cap map is a section of the first projection over the
disc. -/
theorem tcmPr1_comp_capX (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    (tcmPr1 Y n 1).comp (capX Y n) = CleanA.discFullMap Y n := by
  refine ContinuousMap.ext (fun q => ?_)
  refine Prod.ext rfl ?_
  exact capX_fst Y n q

/-! ## The main statement -/

/-- **The cap transfer of the first factor's model class.**  Pulling `pr1^*(Mpun n Y)` back along
the cap map computes `stepDisc Y n (Mn n Y)`. -/
theorem capX_pr1_Mpun (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    (relCohMap (capX Y n) (DiscB Y n) (tcmA Y n 1) (capX_mem_tcmA Y n) ℤ n).hom
        ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom
          (Mpun n Y))
      = stepDisc Y n (Mn n Y) := by
  have hgf : ∀ x ∈ DiscB Y n, (tcmPr1 Y n 1).comp (capX Y n) x ∈ Punct Y n := by
    intro x hx
    rw [tcmPr1_comp_capX Y n]
    exact mem_Sph_punct Y n (CleanA.discFullMap Y n x) (CleanA.discFullMap_mem Y n x hx)
  rw [relCohMap_compA_apply (DiscB Y n) (tcmA Y n 1) (Punct Y n) (capX Y n) (tcmPr1 Y n 1)
    (capX_mem_tcmA Y n) (fun x hx => hx) hgf ℤ n (Mpun n Y)]
  rw [relCohMap_congrA (DiscB Y n) (Punct Y n) (tcmPr1_comp_capX Y n) hgf
    (fun x hx => mem_Sph_punct Y n (CleanA.discFullMap Y n x) (CleanA.discFullMap_mem Y n x hx))
    ℤ n]
  rw [show stepDisc Y n (Mn n Y)
      = (relCohMap (CleanA.discFullMap Y n) (DiscB Y n) (Sph Y n)
          (CleanA.discFullMap_mem Y n) ℤ n).hom (Mn n Y) from rfl]
  rw [← Mpun_spec n Y]
  exact (relCohMap_compA_apply (DiscB Y n) (Sph Y n) (Punct Y n) (CleanA.discFullMap Y n)
    (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin n))) (CleanA.discFullMap_mem Y n)
    (mem_Sph_punct Y n)
    (fun x hx => mem_Sph_punct Y n (CleanA.discFullMap Y n x) (CleanA.discFullMap_mem Y n x hx))
    ℤ n (Mpun n Y)).symm

end

end Work.Whitney
