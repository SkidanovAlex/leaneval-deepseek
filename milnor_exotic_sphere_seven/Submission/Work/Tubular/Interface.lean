import Submission.Work.Tubular.Collapse
import Submission.Work.Tubular.GenLoop
import Submission.Work.Tubular.Rank
import Submission.Work.Tubular.TubeBasic
import Submission.Work.Tubular.Local
import Submission.Work.Tubular.TubeLocal
import Submission.Work.Tubular.BundleCollapse
import Submission.Work.Tubular.Global
import Submission.Work.Tubular.Transversality
import Submission.Work.ThomBordism.PontryaginThom.Item1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The interface with the Pontryagin–Thom chapter

This file connects the tubular-neighbourhood chapter (`Work.Tubular`) with the vocabulary of
`Work.ThomBordism.PontryaginThom` — the chapter whose missing input is
`Work.ThomBordism.PontryaginThom.TubularThomIso`, i.e. `Work.ThomBordism.PontryaginThom.PTGeomMin`.

* `Work.Tubular.genLoop_comp` — a based map of spaces sends the cube loops of the source to the cube
  loops of the target (`GenLoop` is Mathlib's cube model of a homotopy group element).
* `Work.Tubular.TubeChart.collapseTo` — **the collapse of the chapter in the target**: the tubular
  neighbourhood of `V` gives an element of `GenLoop (Fin N) Y y` in any based space `Y` receiving a
  based map from the Thom space of the normal bundle, with the radius `R` supplied by
  `Work.Tubular.TubeChart.exists_box`.  This is the object the Pontryagin–Thom construction consumes
  (`PTRep.collapse`).
* `Work.Tubular.TubeThomRep` — the data that the chapter has to supply for a normal class
  `N : NormalBundlData V`: the collapse and **the two Hurewicz pairings** with the Thom classes
  `p₁²U`, `p₂U` of the universal bundle.  The pairings are the Thom-class naturality statement
  (the part that is still missing — see the chapter's `README.md` §5).
* `Work.Tubular.tubularThomIso_of_rep` — the assembly: if the data exists for every manifold and
  every normal class, then `TubularThomIso` (= `PTGeomMin`) holds.
-/

open scoped Manifold ContDiff Topology

open Work.ThomBordism.PontryaginThom

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {N : ℕ} {E : EmbeddingData V N} {ε : ℝ}

/-- **The collapse of a tube chart in any target**: given a tube chart of `V`, a basepoint of the
Thom space of its normal bundle and a based map into a space `Y`, the collapse of the chapter is an
element of `GenLoop (Fin N) Y y`. -/
def TubeChart.collapseTo (C : TubeChart E ε) (q : NormalSphSub E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin N, |y i| < R)
    {Y : Type*} [TopologicalSpace Y] (y : Y) (j : C(NormalThomSpace E ε, Y))
    (hj : j (normalThomBasepoint E ε q) = y) : GenLoop (Fin N) Y y :=
  ⟨j.comp (tubeCollapseCube C q R),
    genLoop_comp j hj (tubeCollapseCube_mem_genLoop C q hR hbox)⟩

@[simp] theorem TubeChart.collapseTo_apply (C : TubeChart E ε) (q : NormalSphSub E ε) {R : ℝ}
    (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin N, |y i| < R) {Y : Type*} [TopologicalSpace Y]
    (y : Y) (j : C(NormalThomSpace E ε, Y)) (hj : j (normalThomBasepoint E ε q) = y)
    (t : Fin N → unitInterval) :
    (C.collapseTo q hR hbox y j hj : C(Fin N → unitInterval, Y)) t =
      j (tubeCollapse C q (cubeToEuc N R t)) := rfl

/-! ## The data the Pontryagin–Thom chapter consumes -/

/-- **The output of the tubular-neighbourhood chapter for a normal class**: the collapse map of the
Pontryagin–Thom construction and the two Hurewicz pairings that compute the normal Pontryagin
numbers.  This is `PTRep` with the normal-bundle data `N` fixed and the collapse of the tubular
neighbourhood. -/
structure TubeThomRep (k : ℕ) (D : ThomTarget k) (V : Work.ThomBordism.Man8)
    (N : NormalBundlData V) where
  /-- the collapse map of the construction, as a cube loop of the universal Thom space -/
  collapse : GenLoop (Fin (k + 8)) D.T D.t₀
  /-- the pairing of its class with the Thom class `p₁²U` is the normal `p₁²`-number -/
  hurewicz_p1sq : Work.Cohomology.kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
      (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ collapse)) =
    N.normalP1Sq
  /-- the pairing of its class with the Thom class `p₂U` is the normal `p₂`-number -/
  hurewicz_p2 : Work.Cohomology.kronH ℤ (ssetOf D.T) (k + 8) D.p2U
      (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ collapse)) =
    N.normalP2

/-- **The assembly**: Pontryagin–Thom data for every manifold and every normal class is exactly
`TubularThomIso` (= `PTGeomMin`), the missing input of the Pontryagin–Thom chapter. -/
theorem tubularThomIso_of_rep {k : ℕ} {D : ThomTarget k}
    (h : ∀ (V : Work.ThomBordism.Man8) (N : NormalBundlData V), Nonempty (TubeThomRep k D V N)) :
    TubularThomIso k D :=
  fun V N => by
    obtain ⟨r⟩ := h V N
    exact ⟨r.collapse, r.hurewicz_p1sq, r.hurewicz_p2⟩

/-- The same assembly, stated in the original vocabulary: `PTGeomMin`. -/
theorem ptGeomMin_of_rep {k : ℕ} {D : ThomTarget k}
    (h : ∀ (V : Work.ThomBordism.Man8) (N : NormalBundlData V), Nonempty (TubeThomRep k D V N)) :
    PTGeomMin k D :=
  tubularThomIso_of_rep h

/-! ## The collapse class, unconditionally

The tubular neighbourhood theorem (`Work.Tubular.hasTubularNeighbourhood`) makes the *first* field of
`TubeThomRep` — the collapse class — exist without any hypothesis beyond the embedding.  The two
Hurewicz pairings (the Thom isomorphism) are the remaining input; they are not produced here. -/

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The collapse class exists.**  For a compact smooth `8`-manifold `V` smoothly embedded in
`ℝ^{8+k}` (`k > 0`), a choice of a based map `J` out of the Thom space of the normal bundle into a
based space `(Y, y₀)` produces an element of `π_{8+k}(Y, y₀)`: the collapse of `S^{8+k} = ℝ^{8+k} ∪
{∞}` along a tubular neighbourhood of `V`, followed by `J`.  No hypothesis on the embedding beyond
`EmbeddingData` is needed — this is `Work.Tubular.hasTubularNeighbourhood`. -/
theorem exists_collapse_genLoop (E : EmbeddingData V (8 + k)) [Nonempty V.pt] (hk : 0 < k)
    {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (J : ∀ ε : ℝ, NormalSphSub E ε → C(NormalThomSpace E ε, Y))
    (hJ : ∀ (ε : ℝ) (q : NormalSphSub E ε), J ε q (normalThomBasepoint E ε q) = y₀) :
    ∃ (ε : ℝ) (hε : 0 < ε) (C : TubeChart E ε) (q : NormalSphSub E ε) (R : ℝ) (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R),
      ∃ g : GenLoop (Fin (8 + k)) Y y₀, g = C.collapseTo q hR hbox y₀ (J ε q) (hJ ε q) := by
  obtain ⟨ε, hε, ⟨C⟩⟩ := hasTubularNeighbourhood E
  obtain ⟨q⟩ := nonempty_normalSphSub E hε (by omega)
  obtain ⟨R, hR, hbox⟩ := C.exists_box
  exact ⟨ε, hε, C, q, R, hR.le, hbox, C.collapseTo q hR.le hbox y₀ (J ε q) (hJ ε q), rfl⟩

end

end Work.Tubular
