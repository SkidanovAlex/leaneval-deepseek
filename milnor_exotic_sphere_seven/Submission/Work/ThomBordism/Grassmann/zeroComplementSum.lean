import Mathlib
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.realification
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.CohHomotopyEquiv
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.Pair
import Submission.Work.LerayHirsch.mv2_exact
import Submission.Work.ThomBordism.Grassmann.zStd_UV_cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The Mayer–Vietoris decomposition of the zero complement of a direct sum

For complex bundles `A` (rank `a`) and `C` (rank `b`) over a base `B`, the zero complement of the
realification of the sum `A ⊕ C` is covered by the two open pieces on which the first (resp. the
second) coordinate of the fibre does not vanish.  This module sets up that cover, proves that it is
an open cover, and records the Mayer–Vietoris argument that turns the vanishing of the cohomology of
the two pieces and of their intersection into the vanishing of the cohomology of the whole space.

The cohomology of the two pieces is that of the punctured total spaces of `A` and `C`
(this is the content of the companion files), and that of the intersection is that of the punctured
total space of the pullback of `C` over the punctured total space of `A`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-- The first coordinate of the splitting `ℂ^{a+b} ≅ ℂ^a × ℂ^b`. -/
def fstAB (a b : ℕ) : EuclideanSpace ℂ (Fin (a + b)) →L[ℂ] EuclideanSpace ℂ (Fin a) :=
  (ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin a)) (EuclideanSpace ℂ (Fin b))).comp
    ((Work.Whitney.sumFibreC a b).symm : EuclideanSpace ℂ (Fin (a + b)) →L[ℂ]
      (EuclideanSpace ℂ (Fin a) × EuclideanSpace ℂ (Fin b)))

/-- The second coordinate of the splitting `ℂ^{a+b} ≅ ℂ^a × ℂ^b`. -/
def sndAB (a b : ℕ) : EuclideanSpace ℂ (Fin (a + b)) →L[ℂ] EuclideanSpace ℂ (Fin b) :=
  (ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin a)) (EuclideanSpace ℂ (Fin b))).comp
    ((Work.Whitney.sumFibreC a b).symm : EuclideanSpace ℂ (Fin (a + b)) →L[ℂ]
      (EuclideanSpace ℂ (Fin a) × EuclideanSpace ℂ (Fin b)))

theorem fstAB_sumFibreC (a b : ℕ) (x : EuclideanSpace ℂ (Fin a))
    (y : EuclideanSpace ℂ (Fin b)) : fstAB a b (Work.Whitney.sumFibreC a b (x, y)) = x := by
  simp [fstAB]

theorem sndAB_sumFibreC (a b : ℕ) (x : EuclideanSpace ℂ (Fin a))
    (y : EuclideanSpace ℂ (Fin b)) : sndAB a b (Work.Whitney.sumFibreC a b (x, y)) = y := by
  simp [sndAB]

/-- The splitting is the inverse of the pair of coordinates. -/
theorem sumFibreC_fstAB_sndAB (a b : ℕ) (v : EuclideanSpace ℂ (Fin (a + b))) :
    Work.Whitney.sumFibreC a b (fstAB a b v, sndAB a b v) = v := by
  simp [fstAB, sndAB]

theorem sumFibreC_eq_zero_iff (a b : ℕ) {x : EuclideanSpace ℂ (Fin a)}
    {y : EuclideanSpace ℂ (Fin b)} :
    Work.Whitney.sumFibreC a b (x, y) = 0 ↔ x = 0 ∧ y = 0 := by
  rw [← map_zero (Work.Whitney.sumFibreC a b), (Work.Whitney.sumFibreC a b).injective.eq_iff]
  simp

theorem fstAB_or_sndAB_ne_zero (a b : ℕ) {v : EuclideanSpace ℂ (Fin (a + b))} (hv : v ≠ 0) :
    fstAB a b v ≠ 0 ∨ sndAB a b v ≠ 0 := by
  by_contra h
  push_neg at h
  refine hv ?_
  rw [← sumFibreC_fstAB_sndAB a b v, h.1, h.2]
  simp

-- the total space of the sum, its coordinate pieces, and their openness

variable (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
variable (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)

/-- The inverse splitting, in coordinates. -/
theorem sumFibreC_symm_apply (a b : ℕ) (v : EuclideanSpace ℂ (Fin (a + b))) :
    (Work.Whitney.sumFibreC a b).symm v = (fstAB a b v, sndAB a b v) := by
  ext <;> rfl

variable (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
variable (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)

/-- **The first coordinate of the sum transforms by the first coordinate of the transition
function.** -/
theorem fstAB_coordChange (i₁ : ι₁ × ι₂) (y : B)
    (v : EuclideanSpace ℂ (Fin (a + b))) :
    fstAB a b ((Work.Whitney.whitneySum A C).coordChange i₁
        ((Work.Whitney.whitneySum A C).indexAt y) y v)
      = A.coordChange i₁.1 (A.indexAt y) y (fstAB a b v) := by
  simp only [Work.Whitney.whitneySum_coordChange, Work.Whitney.whitneySum_indexAt,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_prodMap',
    Prod.map_apply, ContinuousLinearEquiv.coe_coe, sumFibreC_symm_apply, fstAB_sumFibreC]

/-- **The second coordinate of the sum transforms by the second coordinate of the transition
function.** -/
theorem sndAB_coordChange (i₁ : ι₁ × ι₂) (y : B)
    (v : EuclideanSpace ℂ (Fin (a + b))) :
    sndAB a b ((Work.Whitney.whitneySum A C).coordChange i₁
        ((Work.Whitney.whitneySum A C).indexAt y) y v)
      = C.coordChange i₁.2 (C.indexAt y) y (sndAB a b v) := by
  simp only [Work.Whitney.whitneySum_coordChange, Work.Whitney.whitneySum_indexAt,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_prodMap',
    Prod.map_apply, ContinuousLinearEquiv.coe_coe, sumFibreC_symm_apply, sndAB_sumFibreC]


/-- The first piece of the cover of the zero complement of `A ⊕ C`: the points whose first
coordinate does not vanish. -/
def pieceFst : Set ↥(Work.Thom.zeroComplement
    (Work.Thom.realification (Work.Whitney.whitneySum A C))) :=
  {p | fstAB a b p.1.2 ≠ 0}

/-- The second piece of the cover of the zero complement of `A ⊕ C`. -/
def pieceSnd : Set ↥(Work.Thom.zeroComplement
    (Work.Thom.realification (Work.Whitney.whitneySum A C))) :=
  {p | sndAB a b p.1.2 ≠ 0}

theorem mem_pieceFst {p : ↥(Work.Thom.zeroComplement
    (Work.Thom.realification (Work.Whitney.whitneySum A C)))} :
    p ∈ pieceFst A C ↔ fstAB a b p.1.2 ≠ 0 := Iff.rfl

theorem mem_pieceSnd {p : ↥(Work.Thom.zeroComplement
    (Work.Thom.realification (Work.Whitney.whitneySum A C)))} :
    p ∈ pieceSnd A C ↔ sndAB a b p.1.2 ≠ 0 := Iff.rfl

theorem pieceFst_union_pieceSnd :
    pieceFst A C ∪ pieceSnd A C = Set.univ := by
  ext p
  rw [Set.mem_union]
  constructor
  · intro _; trivial
  · intro _
    by_contra h
    rw [mem_pieceFst] at h
    rw [mem_pieceSnd] at h
    push_neg at h
    exact p.2 (by
      have h2 := sumFibreC_fstAB_sndAB a b p.1.2
      rw [h.1, h.2] at h2
      rw [h2.symm]
      simp)


/-- **Mayer–Vietoris, in the form consumed by `zeroComplement_whitneySum_vanish`**: if `H^k`
vanishes on the two open pieces `pieceFst`, `pieceSnd` of the cover of the zero complement of
`A ⊕ C` and `H^{k-1}` vanishes on their intersection (and `k ≥ 1`), then `H^k` of the zero
complement vanishes. -/
theorem subsingleton_zeroComplementSum_of_pieces
    (hU : IsOpen (pieceFst A C)) (hV : IsOpen (pieceSnd A C)) (m : ℕ) (hm : 1 ≤ m)
    (h1 : Subsingleton (Work.Thom.Coh ℤ m ↥(pieceFst A C)))
    (h2 : Subsingleton (Work.Thom.Coh ℤ m ↥(pieceSnd A C)))
    (h3 : Subsingleton (Work.Thom.Coh ℤ (m - 1) ↥(pieceFst A C ∩ pieceSnd A C))) :
    Subsingleton (Work.Thom.Coh ℤ m
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum A C)))) :=
  subsingleton_of_mv2 (pieceFst A C) (pieceSnd A C) hU hV (pieceFst_union_pieceSnd A C)
    m hm h1 h2 h3
end

end Work.ThomBordism.Grassmann
