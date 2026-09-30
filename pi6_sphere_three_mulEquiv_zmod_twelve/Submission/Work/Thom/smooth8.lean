import Mathlib
import Submission.Work.Thom.manifoldP1
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.SignatureBordism.Numbers
import Submission.Work.Cohomology.exists_capH

set_option synthInstance.maxHeartbeats 400000

open scoped Manifold Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The repaired interface for the dimension-`8` signature theorem (option F2 of NOTES §15.10)

`Submission/NOTES.md` §15.10 records that the interface
`Work.TangentClasses.ClosedOriented8Manifold` of the delivered `TangentClasses` chapter is
**refutable**: it carries `p₁`, `p₂ ∈ H^*(X;ℤ)` as *free data*, with nothing tying them to the
tangent bundle of any manifold, so instantiating it at any `X` with `σ ≠ 0` and `p₁ = p₂ = 0`
refutes the global statement `HirzebruchIdentity8`.

The repair (option **F2**) is to build the structure out of a *genuine* closed oriented smooth
`8`-manifold and to **define** the Pontryagin classes from the tangent bundle, never to carry them
as data.  That is what this module does, on top of item (4) of the deliverable
(`Work.Thom.p1Tangent'`, `Work.Thom.p2Tangent'` of `Submission/Work/Thom/manifoldP1.lean`):

* `Work.Thom.ClosedOrientedSmooth8` — a closed oriented smooth `8`-manifold: a type `pt` with
  `TopologicalSpace`, `ChartedSpace (EuclideanSpace ℝ (Fin 8))`, `IsManifold 𝓘(ℝ,ℝ⁸) 1`,
  `CompactSpace`, `ConnectedSpace`, together with a **fundamental class** `c ∈ H₈(pt;ℤ)` which
  *generates* `H₈(pt;ℤ) ≅ ℤ` (the workspace's encoding of "closed oriented", exactly as in
  `Work.TangentClasses.ClosedOriented8Manifold`);
* `Work.Thom.ClosedOrientedSmooth8.p1`, `.p2` — **definitions**, not fields:
  `p₁ = Work.Thom.p1Tangent' 𝓘(ℝ,ℝ⁸) pt` and `p₂ = Work.Thom.p2Tangent' 𝓘(ℝ,ℝ⁸) pt`;
* `.sigma`, `.p1Sq`, `.p2Num`, `.hirzebruch`, `.congruence` — the numbers and the identity
  (the same `Work.SignatureBordism` vocabulary the rest of the project uses);
* `Work.Thom.HirzebruchIdentity8` (the identity `45 σ = 7 p₂ - p₁²` for every such manifold) and
  `Work.Thom.HirzebruchCongruence8` (the congruence form `7 ∣ p₁² - 4 σ`), together with the
  *proof* that the first implies the second.

**What a future session must prove** (i.e. the two global statements below, which are the genuine
dimension-`8` signature theorem in this vocabulary):

* `Work.Thom.HirzebruchIdentity8 : ∀ M : ClosedOrientedSmooth8, M.hirzebruch`, and
* `Work.Thom.HirzebruchCongruence8 : ∀ M : ClosedOrientedSmooth8, 7 ∣ M.p1Sq - 4 * M.sigma`,

and also the **consistency** with the delivered `TangentClasses` chapter: for the capped manifold
`X = D(ξ) ∪_F D⁸` (which carries a `ChartedSpace (EuclideanSpace ℝ (Fin 8))` and a smooth structure,
`Work.Milnor.cappedChartedSpace`, `Work.Milnor.capped_isManifold`), the *defined* class
`Work.Thom.p1Tangent' 𝓘(ℝ,ℝ⁸) (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))` agrees with
`Work.TangentClasses.p1Tangent F hF S` (equivalently, up to sign, with
`Work.Milnor.cappedPontryaginClass F hF`); this needs the naturality of `chernClass` under
pullback/restriction — the splitting principle (`README.md` ADDENDUM 20).

Unlike `Work.TangentClasses.ClosedOriented8Manifold`, **no statement of this module can be refuted
by choosing `p₁`, `p₂`**: there is nothing to choose.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-! ## The repaired structure -/

/-- **A closed oriented smooth `8`-manifold**, with a generating fundamental class.

The manifold data are the workspace's model: a type with a topological space structure, a
`ChartedSpace (EuclideanSpace ℝ (Fin 8))`, a `IsManifold 𝓘(ℝ,ℝ⁸) 1` structure, and `CompactSpace`
and `ConnectedSpace` instances (compactness is what makes the finite chart cover of
`Work.Thom.exists_finite_chart_cover` available, hence `Work.Thom.p1Tangent'`).  "Oriented" is
encoded, as in the rest of the project, by a class `c ∈ H₈(pt;ℤ)` which *generates*.

The Pontryagin classes are **not** fields of this structure: they are defined
(`Work.Thom.ClosedOrientedSmooth8.p1`, `.p2`) from the tangent bundle. -/
structure ClosedOrientedSmooth8 where
  /-- the underlying type of the manifold -/
  pt : Type
  [topologicalSpace : TopologicalSpace pt]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 8)) pt]
  [isManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) 1 pt]
  [compactSpace : CompactSpace pt]
  [connectedSpace : ConnectedSpace pt]
  /-- the fundamental class -/
  c : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of pt))).homology 8
  /-- the fundamental class generates `H₈(pt;ℤ)` -/
  c_generates : Submodule.span ℤ {c} = ⊤

attribute [instance] ClosedOrientedSmooth8.topologicalSpace
  ClosedOrientedSmooth8.chartedSpace ClosedOrientedSmooth8.isManifold
  ClosedOrientedSmooth8.compactSpace ClosedOrientedSmooth8.connectedSpace

namespace ClosedOrientedSmooth8

variable (M : ClosedOrientedSmooth8)

/-- The singular simplicial set of the manifold. -/
abbrev sset : SSet := TopCat.toSSet.obj (TopCat.of M.pt)

/-- **The first Pontryagin class of the tangent bundle**, a *defined* class:
`p₁(TM) = Work.Thom.p1Tangent' 𝓘(ℝ,ℝ⁸) pt`. -/
def p1 : (Work.Cohomology.cochainC ℤ M.sset).homology 4 :=
  Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) M.pt

/-- **The second Pontryagin class of the tangent bundle**, a *defined* class:
`p₂(TM) = Work.Thom.p2Tangent' 𝓘(ℝ,ℝ⁸) pt`. -/
def p2 : (Work.Cohomology.cochainC ℤ M.sset).homology 8 :=
  Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) M.pt

/-- The defining equation of `p1`: it is the tangent-bundle Pontryagin class. -/
theorem p1_def : M.p1 = Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) M.pt := rfl

/-- The defining equation of `p2`: it is the tangent-bundle Pontryagin class. -/
theorem p2_def : M.p2 = Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) M.pt := rfl

/-- **The signature** `σ(M)` of the middle intersection form. -/
def sigma : ℤ := Work.SignatureBordism.sigma 4 M.sset M.c

/-- **The `p₁²`-number** `⟨p₁(TM) ⌣ p₁(TM), [M]⟩`. -/
def p1Sq : ℤ := Work.SignatureBordism.p₁SqNumber M.sset M.c M.p1

/-- **The `p₂`-number** `⟨p₂(TM), [M]⟩`. -/
def p2Num : ℤ := Work.SignatureBordism.p₂Number M.sset M.c M.p2

/-- **The dimension-`8` Hirzebruch identity** for `M`, with the Pontryagin classes *of its tangent
bundle*: `45 σ(M) = 7 p₂(M) − p₁(M)²`. -/
def hirzebruch : Prop := Work.SignatureBordism.HirzebruchEightManifold M.sset M.c M.p1 M.p2

/-- The identity is the identity between the three numbers. -/
theorem hirzebruch_iff : M.hirzebruch ↔ 45 * M.sigma = 7 * M.p2Num - M.p1Sq := Iff.rfl

/-- **The congruence form** `p₁² ≡ 4σ (mod 7)` of the dimension-`8` identity. -/
theorem congruence_of_hirzebruch (h : M.hirzebruch) : M.p1Sq ≡ 4 * M.sigma [ZMOD 7] :=
  Work.SignatureBordism.hirzebruchEightManifold_congruence M.sset M.c M.p1 M.p2 h

/-- The congruence form, as a divisibility statement. -/
theorem dvd_of_hirzebruch (h : M.hirzebruch) : 7 ∣ M.p1Sq - 4 * M.sigma :=
  Int.ModEq.dvd (M.congruence_of_hirzebruch h).symm

/-- **The congruence form of the dimension-`8` signature theorem** for `M`, as a `Prop`:
`7 ∣ p₁(M)² − 4 σ(M)`.  This is the form in which the statement closes the exotic-sphere project
(`Submission/NOTES.md` §15.10, §15.11). -/
def congruence : Prop := 7 ∣ M.p1Sq - 4 * M.sigma

end ClosedOrientedSmooth8

/-! ## The global statements -/

/-- **The dimension-`8` Hirzebruch identity for every closed oriented smooth `8`-manifold**, with
the Pontryagin classes *of the tangent bundle* (definitions, not data):
`45 σ(M) = 7 p₂(M) − p₁(M)²`.  This is the dimension-`8` signature theorem in this vocabulary, and
it is the corrected form of the refutable `Work.TangentClasses.HirzebruchIdentity8`
(`Submission/NOTES.md` §15.10). -/
def HirzebruchIdentity8 : Prop := ∀ M : ClosedOrientedSmooth8, M.hirzebruch

/-- **The congruence form of the dimension-`8` signature theorem**: for every closed oriented
smooth `8`-manifold, `7 ∣ p₁(TM)² − 4 σ(M)`.  It needs no `p₂`, it is implied by
`Work.Thom.HirzebruchIdentity8`, and it is the hypothesis that closes the project. -/
def HirzebruchCongruence8 : Prop := ∀ M : ClosedOrientedSmooth8, M.congruence

/-- The numerical form of `HirzebruchIdentity8`. -/
theorem hirzebruchIdentity8_iff :
    HirzebruchIdentity8 ↔
      ∀ M : ClosedOrientedSmooth8, 45 * M.sigma = 7 * M.p2Num - M.p1Sq :=
  ⟨fun h M => (M.hirzebruch_iff).mp (h M), fun h M => (M.hirzebruch_iff).mpr (h M)⟩

/-- **The identity implies the congruence**: `45 σ = 7 p₂ − p₁²` gives `7 ∣ p₁² − 4σ`. -/
theorem congruence8_of_hirzebruch8 (h : HirzebruchIdentity8) : HirzebruchCongruence8 :=
  fun M => M.dvd_of_hirzebruch (h M)

/-- The congruence, pointwise. -/
theorem HirzebruchCongruence8.apply (h : HirzebruchCongruence8) (M : ClosedOrientedSmooth8) :
    7 ∣ M.p1Sq - 4 * M.sigma := h M

end

end Work.Thom
