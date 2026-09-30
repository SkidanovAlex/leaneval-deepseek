/-
# The ceiling data of the five cusps: the assembly

This file assembles `Work.RTOwed.CuspCeilingData` (the existence of the ceiling maps `mbarPt v`)
from the *certificates* about the concrete cusp development of `Work.FoldInst.Mbar` defined in
`Submission/Work/RTOwed/cuspDev.lean`.

The certificates (the statements in `CuspCertificates`) are the finite verifications of the
development:

* `mem`, `facet`: the affine image of the unit cube of `a` lies in `Q̄`, on the truncation facet of
  its ideal vertex;
* `cont`: `mbarPt v` is continuous (the gluing of the faces of the cubes);
* `inj`: `mbarPt v` is injective modulo the cusp lattice `Λ_v`;
* `cover`: every point of the truncation set is a ceiling point of one of the five cusps;
* `disj`: the five ceiling tori are disjoint;
* `lattice_eq`: `Λ_v = diag(latMod v) ℤ³` in cube coordinates.

Everything else (the periodicity of `mbarPt`, the range/truncation set identity, the homeomorphism
`τ_v : ℝ³/Λ_v ≃ₜ T_v` and the structure itself) is proved here.
-/
import Mathlib
import Submission.Work.RTOwed.CuspCeiling
import Submission.Work.RTOwed.cuspDev
import Submission.Work.RTOwed.cuspTorus_homeo_boundary
import Submission.Work.RTOwed.cuspCert.cube_quad
import Submission.Work.RTOwed.cuspCert.lattice_bridge
import Submission.Work.RTOwed.cuspCert.mbarPt_continuous
import Submission.Work.RTOwed.cuspCert.mbarPt_inj
import Submission.Work.RTOwed.cuspCert.tset_cover
import Submission.Work.RTOwed.cuspCert.cusp_disjoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed

/-! ### The certificate interface -/

/-- **The certificates of the cusp development.**  Each field is a finite verification about the
data of `Work.Cusp.Data` (see the module docstring). -/
structure CuspCertificates where
  /-- The affine image of the unit cube of `a` lies in `Q̄`. -/
  mem : ∀ (a : Fin 48) (x : CuspE3), x ∈ cubeBox a → kleinPt a x ∈ Work.FoldInst.Qbar
  /-- The affine image of the unit cube of `a` lies on the truncation facet of its ideal vertex. -/
  facet : ∀ (a : Fin 48) (x : CuspE3), x ∈ cubeBox a →
    Work.FoldInst.truncSlack (cubeVert a) (kleinPt a x) = 0
  /-- `mbarPt v` is continuous. -/
  cont : ∀ v : Fin 5, Continuous (mbarPt v)
  /-- The fibres of `mbarPt v` are exactly the cosets of the cusp lattice. -/
  inj : ∀ (v : Fin 5) (x x' : CuspE3), mbarPt v x = mbarPt v x' → latVec v (x - x')
  /-- Every point of the truncation set is a ceiling point. -/
  cover : ∀ y ∈ Work.FoldInst.Tset, ∃ (v : Fin 5) (x : CuspE3), mbarPt v x = y
  /-- The ceiling tori of two different cusps are disjoint. -/
  disj : ∀ v v' : Fin 5, v ≠ v' →
    Disjoint (Set.range (mbarPt v)) (Set.range (mbarPt v'))
  /-- The cusp lattice is the diagonal lattice of the data. -/
  lattice_eq : ∀ v : Fin 5,
    (Work.Cusp.lattice v : Set CuspE3) = {z | latVec v z}
  /-- `mbarPt v` is invariant under the cusp lattice. -/
  per : ∀ (v : Fin 5) (x : CuspE3) (l : CuspE3), latVec v l →
    mbarPt v (x + l) = mbarPt v x

/-! ### The ceiling map, unfolded -/

/-- The fallback branch of `cuspPtX` never fires: the affine image of the cube of `x` lies in `Q̄`. -/
theorem cuspPtX_eq (v : Fin 5) (x : CuspE3) :
    cuspPtX v x = xbarOf (cubeOf v x) (kleinPt (cubeOf v x) (redV v x))
      (cuspCert.cube_quad.1 (cubeOf v x) (redV v x) (redV_mem_cubeBox v x)) :=
  cuspPtX_of_mem v x _

/-- The ceiling map, as the class of the facet point of the cube of `x`. -/
theorem mbarPt_eq_mk (v : Fin 5) (x : CuspE3) :
    mbarPt v x = Work.FoldInst.mk (xbarOf (cubeOf v x) (kleinPt (cubeOf v x) (redV v x))
      (cuspCert.cube_quad.1 (cubeOf v x) (redV v x) (redV_mem_cubeBox v x))) := by
  rw [mbarPt, cuspPtX_eq]

/-! ### The ceiling points lie on the truncation set -/

/-- **The ceiling point of the `v`-th cusp lies on the truncation set.** -/
theorem mbarPt_mem_Tset (C : CuspCertificates) (v : Fin 5) (x : CuspE3) :
    mbarPt v x ∈ Work.FoldInst.Tset := by
  have hx : redV v x ∈ cubeBox (cubeOf v x) := redV_mem_cubeBox v x
  have hy : kleinPt (cubeOf v x) (redV v x) ∈ Work.FoldInst.Qbar := C.mem _ _ hx
  rw [mbarPt, cuspPtX_of_mem v x hy, Work.FoldInst.mem_Tset_iff]
  exact ⟨xbarOf (cubeOf v x) (kleinPt (cubeOf v x) (redV v x)) hy,
    ⟨cubeVert (cubeOf v x), C.facet _ _ hx⟩, rfl⟩

/-! ### The five ceiling tori cover the truncation set -/

/-- **The truncation set is the union of the five ceiling tori.** -/
theorem tset_eq_iUnion (C : CuspCertificates) :
    Work.FoldInst.Tset = ⋃ v : Fin 5, Set.range (mbarPt v) := by
  ext y
  constructor
  · intro hy
    obtain ⟨v, x, rfl⟩ := C.cover y hy
    exact Set.mem_iUnion.mpr ⟨v, Set.mem_range_self x⟩
  · intro hy
    obtain ⟨v, x, rfl⟩ := Set.mem_iUnion.mp hy
    exact mbarPt_mem_Tset C v x

/-! ### The ceiling torus is homeomorphic to the cusp torus -/

/-- The lattice membership, in the coordinate form of the data. -/
theorem latVec_of_mem (C : CuspCertificates) (v : Fin 5) {z : CuspE3}
    (h : z ∈ Work.Cusp.lattice v) : latVec v z :=
  (Set.ext_iff.1 (C.lattice_eq v) z).mp h

/-- The coordinate form of the lattice membership, as a lattice vector. -/
theorem mem_of_latVec (C : CuspCertificates) (v : Fin 5) {z : CuspE3}
    (h : latVec v z) : z ∈ Work.Cusp.lattice v :=
  (Set.ext_iff.1 (C.lattice_eq v) z).mpr h

/-- The lattice form of the periodicity. -/
theorem mbarPt_periodic (C : CuspCertificates) (v : Fin 5) {x x' : CuspE3}
    (h : x - x' ∈ Work.Cusp.lattice v) : mbarPt v x = mbarPt v x' := by
  have hmem : latVec v (x - x') := latVec_of_mem C v h
  have h2 : x = x' + (x - x') := by abel
  rw [h2]
  exact C.per v x' (x - x') hmem

/-- **The `τ_v` homeomorphism**: the cusp torus `ℝ³/Λ_v` is the ceiling torus of the `v`-th cusp. -/
noncomputable def tauHomeo (C : CuspCertificates) (v : Work.Space.Cusp) :
    Work.Cusp.CuspTorus v ≃ₜ Set.range (mbarPt v) := by
  classical
  -- the descended map
  have hper : ∀ x y : CuspE3, QuotientAddGroup.leftRel (Work.Cusp.lattice v) x y →
      mbarPt v x = mbarPt v y := by
    intro x y hxy
    have hxy' : -x + y ∈ Work.Cusp.lattice v := QuotientAddGroup.leftRel_apply.mp hxy
    have h : y - x ∈ Work.Cusp.lattice v := by simpa only [neg_add_eq_sub] using hxy'
    have hmem : latVec v (y - x) := latVec_of_mem C v h
    have h2 : y = x + (y - x) := by abel
    rw [h2]
    exact (C.per v x (y - x) hmem).symm
  let f : Work.Cusp.CuspTorus v → Work.FoldInst.Mbar := Quotient.lift (mbarPt v) hper
  let qm : CuspE3 → Work.Cusp.CuspTorus v :=
    Quotient.mk (QuotientAddGroup.leftRel (Work.Cusp.lattice v))
  have hf_mk : ∀ x : CuspE3, f (qm x) = mbarPt v x := fun x => rfl
  have hf_cont : Continuous f := by
    refine (isQuotientMap_quotient_mk'
      (s := QuotientAddGroup.leftRel (Work.Cusp.lattice v))).continuous_iff.mpr ?_
    change Continuous (f ∘ qm)
    rw [show f ∘ qm = mbarPt v from funext fun x => hf_mk x]
    exact C.cont v
  -- the map into the range
  have hFmem : ∀ t : Work.Cusp.CuspTorus v, f t ∈ Set.range (mbarPt v) := by
    intro t
    obtain ⟨x, hx⟩ := Quotient.exists_rep t
    refine ⟨x, ?_⟩
    rw [← hx]
    exact hf_mk x
  let F : Work.Cusp.CuspTorus v → Set.range (mbarPt v) := fun t => ⟨f t, hFmem t⟩
  have hF_cont : Continuous F := hf_cont.subtype_mk hFmem
  have hF_inj : Function.Injective F := by
    intro t t' htt'
    revert htt'
    refine Quotient.inductionOn₂ t t' ?_
    intro x y hxy
    have hxy' : f (qm x) = f (qm y) := congrArg Subtype.val hxy
    have hxy'' : mbarPt v x = mbarPt v y := by
      rw [← hf_mk x, ← hf_mk y]
      exact hxy'
    have hlat : latVec v (x - y) := C.inj v x y hxy''
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (mem_of_latVec C v hlat)
  have hF_surj : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨qm x, ?_⟩
    refine Subtype.ext ?_
    show f (qm x) = y.1
    rw [hf_mk]
    exact hx
  have hbij : Function.Bijective F := ⟨hF_inj, hF_surj⟩
  haveI : CompactSpace (Work.Cusp.CuspTorus v) := by
    obtain ⟨h⟩ := cuspTorus_homeo_circle_torus v
    exact h.symm.compactSpace
  refine Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hbij) ?_
  exact hF_cont

/-! ### The assembly -/

/-- **The ceiling data of the five cusps**, from the certificates. -/
theorem cuspCeilingData_of (C : CuspCertificates) : Nonempty Work.RTOwed.CuspCeilingData :=
  ⟨{ mbarPt := mbarPt
     tauHomeo := tauHomeo C
     tset_eq := tset_eq_iUnion C
     disjoint := C.disj }⟩

/-- **The seven certificates of the concrete cusp development**, assembled from the modules of
`Submission/Work/RTOwed/cuspCert/`. -/
theorem cuspCertificates : CuspCertificates where
  mem := fun a x hx => cuspCert.cube_quad.1 a x hx
  facet := fun a x hx => cuspCert.cube_quad.2 a x hx
  cont := cuspCert.mbarPt_continuous
  inj := cuspCert.mbarPt_inj
  cover := cuspCert.tset_cover
  disj := cuspCert.cusp_disjoint
  lattice_eq := cuspCert.lattice_bridge.1
  per := cuspCert.lattice_bridge.2

/-- **The ceiling data of the five cusps of `M̄`**: the missing inhabitant of
`Work.RTOwed.CuspCeilingData`. -/
theorem cuspCeilingData_exists : Nonempty Work.RTOwed.CuspCeilingData :=
  cuspCeilingData_of cuspCertificates

end Work.RTOwed
