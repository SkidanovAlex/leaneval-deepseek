import Submission.Work.ThomBordism._gtd.P4
import Submission.Work.ThomBordism.padGaussFunM
import Submission.Work.ThomBordism._gtd.P5
import Submission.Work.PTGeometric.GenuineTransversality
import Submission.Work.PTGeometric.AmbientRealisation
import Submission.Work.PTGeometric.OrientationFree
import Submission.Work.Tubular.Gauss
import Submission.Work.PTGeometric.TubeAmbient
import Submission.Work.PTGeometric.PadAmb
import Submission.Work.PTGeometric.exists_projOfPlane
import Submission.Work.Tubular.LocalDegreeAll

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the genuine collapse data of a family, and the last mile in its honest form

The reduction of the chapter's `TransversalityFamily k D` to the target `TransversalityCoreFamily`
(`Submission/Work/ThomBordism/familyAssembly.lean`) takes as its geometric input a statement that
quantifies over an **arbitrary** `Work.Tubular.TubeThomRep`: a loop `GenLoop (Fin (k+8)) D.T D.t₀`
together with the two Hurewicz pairings.  Nothing in the structure forces that loop to be the
*geometric* collapse map of the piece — the Pontryagin–Thom collapse of its tubular neighbourhood
composed with the Gauss map of its normal bundle.  Consequently the class equation
`(∏ i, tubeAlpha (r i))^m = 1` — the hypothesis from which the null-homotopy is extracted — is a
statement about an arbitrary loop, and the geometric last mile (make the null-homotopy smooth and
transverse to the zero section, take the preimage) has no well-defined object to work on.  This is
the interface defect recorded in `README.md` §14.

This file fixes the interface: it names TUBULAR's **concrete** collapse map.

* `Work.PTGeometric.GenuineTubeGeometry k D ι Fam` — the genuine collapse data of a finite family:
  for every piece, TUBULAR's tubular neighbourhood of its embedding in `ℝ^{8+k}`
  (`EmbeddingData`, `TubeChart`, `NormalSphSub`), the Gauss/classifying map `J` of TUBULAR's
  `Gauss.lean` (`Th(ν) → D.T`, fixing the basepoint), the metric-free collapse `g`
  (`Th(ℝ^{8+k}) → Th(ν)`), the Pontryagin–Thom representative `rep` of the piece, the **identification**
  `isGeom` of `rep`'s loop with TUBULAR's concrete collapse `Work.Tubular.alphaV`, the core of the
  Thom space, and TUBULAR's **zero-set theorem** `tubeCollapse_mem_normalThomZero` in the form
  `zero`: the concrete collapse vanishes exactly on the embedded piece.
* `Work.PTGeometric.ConcreteLastMile k D` — G6 in its honest form: for every family and every
  *genuine* collapse datum of it, and every `m > 0` with the `m`-th power of the product of the pieces'
  genuine collapse classes trivial, a positive multiple of the family bounds.
* `Work.PTGeometric.concreteLastMile_of_genuineTransversality` — the old (interface-defective)
  `GenuineTransversality` implies the new statement, so nothing is lost: the new hypothesis is the
  honest *specialisation* of the old one to the genuine collapse data.
* `Work.PTGeometric.transversalityCoreFamily_of_concreteData` and its nonempty-family form
* `Work.PTGeometric.transversalityCoreFamilyNE_of_concreteDataNE` — the assembly of the deliverable from
  the new geometric input plus rational Hurewicz in the stable range.

## What the last mile still has to prove

`ConcreteLastMile k D` is *not* a restatement of the target: it quantifies only over the genuine
collapse data, and the geometric content it carries (the zero-set property `zero` and the concrete
map `alphaV`) is exactly what a Pontryagin–Thom argument consumes.  The construction of the source
from the null-homotopy of `∏ i, tubeAlpha (G.rep i)` is carried out in
`Submission/Work/PTGeometric/NullSourceRealisation.lean` up to the construction of
`Work.PTGeometric.NullSourceData`; see `README.md` §17 for the exact residual statement and for the
obstruction that makes the *global* form `AmbientCollapseEnd` unsatisfiable from the collapse data
alone.

## Main definitions

* `Work.PTGeometric.canonicalNormal`, `Work.PTGeometric.GenuineTubeGeometry`
* `Work.PTGeometric.ConcreteLastMile`
* `Work.PTGeometric.ConcreteLastMileSource` — the residual source construction

## Main results

* `Work.PTGeometric.concreteLastMile_of_genuineTransversality`
* `Work.PTGeometric.concreteLastMile_of_source` — the last mile reduces to the source construction
* `Work.PTGeometric.transversalityCoreFamily_of_concreteData` and its nonempty-family form
* `Work.PTGeometric.transversalityCoreFamilyNE_of_concreteDataNE`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom
open Work.Cohomology

/-- The canonical normal-bundle data of a closed oriented `8`-manifold: used to fix the *same* choice
of `NormalBundlData` in the geometric data and in the assembly, so that the Pontryagin–Thom
representatives of `GenuineTubeGeometry` are the ones the assembly consumes. -/
def canonicalNormal (V : Man8) : NormalBundlData V := Classical.choice (NormalBundlData.nonempty V)

/-- The reindexing `Fin (k+8) → Fin (8+k)` used to compare TUBULAR's cube collapse (whose dimension is
literal `8 + k`) with the Pontryagin–Thom representatives of the chapter (whose cube is
`Fin (k+8)`). -/
def finKR (k : ℕ) : Fin (k + 8) → Fin (8 + k) := Fin.cast (Nat.add_comm k 8)

/-- **The tie of a piece's normal data with the oriented Gauss data of its collapse.**

This is the coordination datum of the boundary sign (`Submission/Work/ThomBordism/NOTE_TIE_AND_SIGN_FREEDOM.md`
§§2–3): the Thom class `u = pulledThom i` of the piece is the Thom class of an *explicit* normal
datum `ND`, and the oriented Gauss data of the collapse (`gauss`, at the collapse value of a tube
point) is the **padded σ-corrected Gauss plane** `Work.ThomBordism.padGaussFunM E ND mU hmU` of that
**same** `ND` at the foot of the tube point, up to the global orientation reversal
`Work.ThomBordism.Grassmann.ogFlip`.

It is the datum that makes the comparison between the coorientation of the level set (whose
prescribed charts are pinned to the tube's normal frame,
`Work.PTGeometric.producedAmbientData_ellE_pinned`) and the piece's given orientation (which the
field `localDegree` ties to `pulledThom`) *statable* through an arbitrary
`G : GenuineTubeGeometry k D ι Fam`.  The two clauses are complementary: `projOfPlane` is blind to
the orientation (`Work.ThomBordism.Grassmann.projOfPlane_ogFlip`), so the `coord_collapse` field
alone determines `gauss` only up to `ogFlip`
(`Work.ThomBordism.Grassmann.projOfPlaneEqIff`), and this datum pins the missing sign. -/
def TiedGaussNormal {k : ℕ} (D : ThomTarget k) (V : Man8)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (R : ℝ) (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (J : C(OnePoint (Work.Tubular.NormalTotal E), D.T)) (hJ : J OnePoint.infty = D.t₀)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (u : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E))
    (mU : ℕ) (hmU : 8 ≤ mU)
    (gauss : {x : D.T // x ≠ D.t₀} → Work.ThomBordism.Grassmann.OG k mU) : Prop :=
  ∃ (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (Gc : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      Gc p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)),
    u = Work.ThomBordism.gtdU E ND Gc hgm ∧
    ∀ (t : Fin (8 + k) → unitInterval),
      Work.Tubular.cubeToEuc (8 + k) R t ∈ C.openTube →
        ∃ hne : Work.Tubular.alphaV C hR hbox D.t₀ J hJ g hg t ≠ D.t₀,
          gauss ⟨Work.Tubular.alphaV C hR hbox D.t₀ J hJ g hg t, hne⟩
              = Work.ThomBordism.padGaussFunM E ND mU hmU
                  ((C.inv (Work.Tubular.cubeToEuc (8 + k) R t)).1.1) ∨
          gauss ⟨Work.Tubular.alphaV C hR hbox D.t₀ J hJ g hg t, hne⟩
              = Work.ThomBordism.Grassmann.ogFlip k mU
                  (Work.ThomBordism.padGaussFunM E ND mU hmU
                    ((C.inv (Work.Tubular.cubeToEuc (8 + k) R t)).1.1))

/-- **The genuine collapse data of a finite family of closed oriented `8`-manifolds.**

For every piece `Fam i`: TUBULAR's tubular neighbourhood of an embedding `Fam i ⊂ ℝ^{8+k}`
(`emb`, `chart`, `q`, the box radius `R`), the Gauss/classifying map `J` of the normal bundle
(`Th(ν) → D.T`, fixing the basepoint, `Gauss.lean`), the metric-free Pontryagin–Thom collapse `g`,
the Pontryagin–Thom representative `rep` of the piece, the identification `isGeom` of `rep`'s loop
with TUBULAR's concrete collapse `Work.Tubular.alphaV`, the core of the universal Thom space `D.T`,
and TUBULAR's zero-set theorem `Work.Tubular.tubeCollapse_mem_normalThomZero` as `zero`.

This is the data that makes the geometric last mile well posed: the loop of `rep` is *the* collapse
map of the tubular neighbourhood of the piece, so the preimage of the core of `rep`'s loop is the
piece, and the class equation of the last mile is an equation about that map. -/
structure GenuineTubeGeometry (k : ℕ) (D : ThomTarget k) (ι : Type) [Fintype ι]
    (Fam : ι → Man8) where
  /-- the Pontryagin–Thom representative of each piece, on the canonical normal-bundle data -/
  rep : ∀ i, Work.Tubular.TubeThomRep k D (Fam i) (canonicalNormal (Fam i))
  /-- the embedding of the piece in `ℝ^{8+k}` -/
  emb : ∀ i, Work.ThomBordism.PontryaginThom.EmbeddingData (Fam i) (8 + k)
  /-- **the members of the family are connected.**

  This is *not* a cosmetic hypothesis: the uniqueness of the relative fundamental class
  (`Work.ThomBordism.isLocalDegreeClass_zsmul_eq`) and the uniformity of the Gauss branch
  (`Work.ThomBordism.gaussBranch_uniform_full` / `gaussBranch_uniform`) are proved from the univeral
  local-degree class `Work.ThomBordism.localDegree_universalThomClass`, whose non-degeneracy input
  needs one point of each piece, and for a disconnected piece the uniqueness of `w` genuinely fails
  (it must be argued componentwise).  Every *producer* of the structure supplies connectivity
  (`Work.ThomBordism.nonemptyGenuineTubeGeometryAtFamily` takes `hconn` as a hypothesis and the
  per-family wiring `Work.ThomBordism.transversalityCoreFamilyConn_orientedFam` quantifies over
  families of connected members), so carrying it as a field costs nothing and makes it available
  *inside* the source construction without threading it through `producedRawData`.  See the project
  lead's message of the session-70 handoff and `NOTE_SESSION64.md` sections 8-10. -/
  hconn : ∀ i, ConnectedSpace (Fam i).pt
  /-- the radius of the tube chart -/
  ε : ∀ i, ℝ
  hε : ∀ i, 0 < ε i
  /-- TUBULAR's tube chart of the embedding -/
  chart : ∀ i, Work.Tubular.TubeChart (emb i) (ε i)
  /-- a point of the normal sphere bundle -/
  q : ∀ i, Work.Tubular.NormalSphSub (emb i) (ε i)
  /-- the radius of the cube containing the tube -/
  R : ℝ
  hR : 0 ≤ R
  hbox : ∀ i, ∀ y ∈ (chart i).U, ∀ j : Fin (8 + k), |y.ofLp j| < R
  /-- the Gauss/classifying map of the normal bundle, on the metric-free Thom spaces -/
  J : ∀ i, C(OnePoint (Work.Tubular.NormalTotal (emb i)), D.T)
  hJ : ∀ i, J i OnePoint.infty = D.t₀
  /-- the metric-free Pontryagin–Thom collapse of the ambient space onto the normal bundle -/
  g : ∀ i, C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal (emb i)))
  hg : ∀ i, ∀ y, y ∉ (chart i).openTube → g i (OnePoint.some y) = OnePoint.infty
  /-- **the collapse is the tube's blow-up collapse**: on the open tube, the metric-free collapse
  `g` is the tube chart's inverse followed by the radial blow-up `normalBlowUp`.  This identifies the
  collapse class `collapseRelK8` with the tube's local geometry; it is a hypothesis of the
  local-degree chapter (`Work.ThomBordism.isLocalDegreeClass_eq_of_nondeg`,
  `Work.ThomBordism.gtdU_localDegreeExists`) and it is *not* derivable from the other fields. -/
  hg2 : ∀ i (y : Work.Tubular.Euc (8 + k)), y ∈ (chart i).openTube →
    g i (OnePoint.some y)
      = OnePoint.some (Work.Tubular.normalBlowUp (emb i) (ε i) ((chart i).inv y))
  /-- **the loop of the Pontryagin–Thom representative is TUBULAR's concrete collapse map** -/
  isGeom : ∀ i (t : Fin (8 + k) → unitInterval),
    (rep i).collapse (fun j => t (finKR k j)) =
      Work.Tubular.alphaV (chart i) hR (hbox i) D.t₀ (J i) (hJ i) (g i) (hg i) t
  /-- the core of the universal Thom space (the zero section of `γ_k`) -/
  core : Set D.T
  /-- **the concrete collapse vanishes exactly on the embedded piece** — TUBULAR's
  `Work.Tubular.tubeCollapse_mem_normalThomZero`, read in the metric-free model -/
  zero : ∀ i (t : Fin (8 + k) → unitInterval),
    Work.Tubular.alphaV (chart i) hR (hbox i) D.t₀ (J i) (hJ i) (g i) (hg i) t ∈ core ↔
      Work.Tubular.cubeToEuc (8 + k) R t ∈ Set.range (emb i).e
  /-- **the ambient dimension of the universal Thom space**: the target is `Th(γ_k)` over
  `G̃r_k(ℝ^{k+mU})`, so a point of the Thom space other than the base point reads off as a rank-`k`
  orthogonal projection of `ℝ^{k+mU}` and a vector of its plane.  It is kept as a *field* (rather
  than a parameter) so that every statement quantifying over `G : GenuineTubeGeometry k D ι Fam` is
  unchanged in shape; the source construction reads the collapse through the padding
  `ℝ^{k+8} = Euc (8+k) ↪ Amb (k+mU)` of `Work.PTGeometric.padAmb` (`NOTE_COORD_DIMENSION_FIX.md`). -/
  mU : ℕ
  /-- the padding `ℝ^{k+8} ↪ ℝ^{k+mU}` exists (the padding keeps the first `k+8` coordinates) -/
  hmU : 8 ≤ mU
  /-- **the ambient coordinates of a point of the Thom space other than the base point**: the
  orthogonal projection onto the plane (the Gauss plane of the point) and the vector of the plane.
  In the model `T = OnePoint (TotalSpace γ) ≅ E ∪ {∞}` these are `projOfPlane ∘ proj` and `evalVec`;
  they are what the last mile's source construction reads the null-homotopy with
  (`Work.PTGeometric.continuous_ambientCoords`). -/
  coord : {x : D.T // x ≠ D.t₀} →
    (Amb (k + mU) →L[ℝ] Amb (k + mU)) × Amb (k + mU)
  /-- the coordinate reading is continuous -/
  continuous_coord : Continuous coord
  /-- **the ambient coordinates of the collapse are TUBULAR's data**: at a point of the open tube, the
  coordinate reading of the collapse's value is the orthogonal projection onto the normal space at
  the foot and the normal coordinate.  This is the statement that identifies the collapse map with
  TUBULAR's tubular neighbourhood model (`Work.PTGeometric.tubeNormalProj`,
  `Work.PTGeometric.tubeNormalCoord`); for the concrete Thom target it is what the Gauss map
  `Work.Tubular.gaussMapOnePoint` provides.  It is the one piece of the *coordinate* structure of
  `D.T` that the abstract `ThomTarget` does not determine. -/
  coord_collapse : ∀ i (t : Fin (8 + k) → unitInterval),
    Work.Tubular.cubeToEuc (8 + k) R t ∈ (chart i).openTube →
      ∃ hne : Work.Tubular.alphaV (chart i) hR (hbox i) D.t₀ (J i) (hJ i) (g i) (hg i) t ≠ D.t₀,
        coord ⟨_, hne⟩ =
          (padEndEuc k mU hmU (Work.PTGeometric.tubeNormalProj (emb i) (chart i)
              (Work.Tubular.cubeToEuc (8 + k) R t)),
            padEuc k mU hmU (Work.PTGeometric.tubeNormalCoord (emb i) (chart i)
              (Work.Tubular.cubeToEuc (8 + k) R t)))
  /-- **the vector part of the ambient coordinates vanishes exactly on the zero section.**  For the
  concrete model, in which `coord` reads a point of the Thom space off as the orthogonal projection
  onto its plane and the vector of the plane, this is the statement that the vector vanishes exactly
  at the points of the zero section — i.e. that `core` *is* the zero section of `γ_k`.  It is needed
  by the last mile's source construction (`SOURCE_PLAN.md` §1) to identify the zero set of the ambient
  vector field with the preimage of the core, which the `zero` field alone does not do. -/
  core_iff_vec : ∀ (x : {x : D.T // x ≠ D.t₀}), x.1 ∈ core ↔ (coord x).2 = 0
  /-- **the core is closed** — in the concrete model it is the image of the zero section of `γ_k`
  over the compact Grassmannian, and a consumer of the source construction needs the zero set of the
  null-homotopy to be closed (`W₀ = H ⁻¹' core` is the null-bordism). -/
  isClosed_core : IsClosed core
  /-- **the basepoint is not in the core** — in the concrete model the basepoint is the point at
  infinity of the Thom space and the core is the zero section. -/
  t0_notMem_core : D.t₀ ∉ core
  /-- **the first component of `coord` is the orthogonal projection onto a `k`-plane.**  In the
  concrete model `coord` reads a point of the Thom space off as
  `(projOfPlane k m ∘ proj, evalVec)`, so this is
  `Work.PTGeometric.projOfPlane_mem_Gr` (see `Work.PTGeometric.continuous_ambientCoords`).  It is
  needed by the last mile's source construction to feed `Gr`-valuedness of the ambient projection
  to `Work.PTGeometric.ContinuousAmbientData` — `coord_collapse` identifies the two components with
  TUBULAR's tube data only over the *open tube*, while the source region contains points of the Thom
  space off the tube as well. -/
  coord_isProj : ∀ (x : {x : D.T // x ≠ D.t₀}),
    (coord x).1 ∈ Gr (k + mU) k
  /-- **the second component of `coord` lies in the plane of the first.**  In the concrete model this
  is `Work.PTGeometric.projOfPlane_fixed_iff` applied to `Work.PTGeometric.evalVec_memPlane`. -/
  coord_mem : ∀ (x : {x : D.T // x ≠ D.t₀}), (coord x).1 ((coord x).2) = (coord x).2
  /-- **the oriented Gauss data of the collapse**: the plane of the ambient coordinates comes with its
  *orientation*, i.e. it is the image under `Work.PTGeometric.projOfPlane` of a point of the **oriented**
  Grassmannian `Work.ThomBordism.Grassmann.OG k mU`.  For the concrete target
  `T = Th(γ_k) = OnePoint (TotalSpace γ_k)` this is simply the Grassmannian coordinate of the point:
  `T ∖ {t₀} = TotalSpace γ_k = {(P, v) : P ∈ OG k mU, v ∈ P}`, so a point *is* an oriented plane.

  This is the data that orients the normal bundle of the zero set of the null-homotopy: the plain
  projection field `coord.1` forgets the orientation of its plane (two trivialisations of `im (coord x).1`
  differ by an element of `O(k)`, and the prescribed charts built from
  `ContinuousLinearEquiv.ofFinrankEq` have uncontrolled determinant sign), so without this field the
  sign `ε_i` of the boundary identity of G5 is not determined.  It is what H4 supplies out of TUBULAR's
  Gauss map `J i` (which lands in `D.T`, i.e. on oriented planes). -/
  gauss : {x : D.T // x ≠ D.t₀} → Work.ThomBordism.Grassmann.OG k mU
  /-- the oriented Gauss data are continuous -/
  continuous_gauss : Continuous gauss
  /-- **the oriented Gauss data refine the projection field**: the plane of the ambient coordinates is
  the plane of the oriented Gauss point. -/
  gauss_proj : ∀ (x : {x : D.T // x ≠ D.t₀}),
    Work.PTGeometric.projOfPlane k mU (gauss x) = (coord x).1
  /-- **the Thom class of the member's normal bundle induced by the classifying map `J`**: the
  pullback `J^*τ_γ` of the universal Thom class of `γ_k` along the classifying map, as a relative
  class of the pair `(ν, ν∖0)` of the member's normal total space.  It is carried as *data* (rather
  than defined here) so that the last mile can name it without knowing the bridge between the
  one-point compactification of `ν` and the pair `(ν, ν∖0)`; H4 supplies it as the transport of
  `Work.ThomBordism.uThomGen` along the classifying chain of `J i`. -/
  pulledThom : ∀ i, Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal (emb i)))
      (Work.Tubular.normalNonzero (emb i))
  /-- **the orientation coordination of the member's local degree** (project lead's round-24 ruling).

  The class `pulledThom i` — the pullback of the universal Thom class along the classifying map `J i`
  — is the one for which TUBULAR's local degree holds for the member's **given** fundamental class.
  The collapse class `collapseRelK8` is fixed by the embedding and the chart (it does not depend on
  any orientation choice), so the identity *pins* `pulledThom i` (Kronecker duality: flipping it
  flips the left-hand side and not the right), and with it the orientation that the source
  construction induces on the member.  This is what makes the boundary sign `s_C = +1` of the last
  mile provable — see `Submission/Work/PTGeometric/NOTE_SIGN_FINAL.md` §7. -/
  localDegree : ∀ i (x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal (emb i)))),
    Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal (emb i)))
      (Work.Tubular.normalNonzero (emb i)) (k + 8)
      ((Nat.add_comm 8 k) ▸ Work.Cohomology.mixedCup
        (TopCat.of (Work.Tubular.NormalTotal (emb i))) (Work.Tubular.normalNonzero (emb i)) 8 k x
        (pulledThom i))
      (Work.Tubular.collapseRelK8 (chart i) (g i) (hg i) hR (hbox i))
    = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (Fam i).X) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal (emb i)) ℤ 8).hom x) (Fam i).c

  /-- **the normal data standing behind `pulledThom`, tied to the oriented Gauss data of the
  collapse** (`Work.PTGeometric.TiedGaussNormal`): the Thom class `pulledThom i` is the `gtdU` of an
  explicit normal datum `ND`, and the oriented plane `gauss` of the collapse at the tube points is
  the *padded `σ`-corrected* Gauss plane `Work.ThomBordism.padGaussFunM` of that **same** `ND`, up
  to the global orientation flip `Work.ThomBordism.Grassmann.ogFlip`.  This is what makes the
  comparison of the coorientation of the level set (the *pinned* prescribed charts) with the piece's
  given orientation (tied to `pulledThom` by `localDegree`) statable — see
  `Submission/Work/ThomBordism/NOTE_TIE_AND_SIGN_FREEDOM.md` §3. -/
  tie : ∀ i, TiedGaussNormal D (Fam i) (emb i) (chart i) R hR (hbox i) (J i) (hJ i) (g i) (hg i)
    (pulledThom i) mU hmU gauss
  /-- **the oriented Gauss/Thom link of the collapse, with its branch.**

  For each piece: `pulledThom i` is the `gtdU` of an explicit normal datum `ND` and bundle map
  `Gc`; the oriented plane of that *same* `Gc` is either the padded Gauss plane
  `Work.ThomBordism.Grassmann.padGaussFun` (branch `σ = 1`) or its orientation reversal (branch
  `σ = -1`); and the oriented Gauss field `gauss` at every nonempty tube point is the *same* branch
  of `padGaussFunM`.  This records, per piece, the orientation with which the source construction
  reads the coorientation of the level set (`gauss`), *tied to the class `pulledThom`* whose
  local-degree equation `GenuineTubeGeometry.localDegree` pins the piece's orientation.

  It is the lead's round-46 datum, in the ambient-dimension-safe form: the two `OG`-valued sides of
  any single equation would live in different ambient dimensions (`OG k 10` for the tautological
  bundle, `OG k mU` for `gauss`), so the branch `σ` — which is what the boundary sign actually
  depends on — is recorded once and used in both worlds.  `tie` alone cannot pin it: its second
  clause is a genuine disjunction (`Work.PTGeometric.tiedGaussNormal_flip_iff`), so without this
  field the boundary sign of the last mile is free data (`NOTE_SESSION48.md` §4). -/
  pulledThom_gauss : ∀ i,
    ∃ (ND : NormalData (Fam i) k (emb i).e)
      (Gc : C((Work.Tubular.normalBundle (emb i) ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle (emb i) ND),
        Gc p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (s : ℤ), (s = 1 ∨ s = -1) ∧
      pulledThom i = Work.ThomBordism.gtdU (emb i) ND Gc hgm ∧
      (∀ p : (Work.Tubular.normalBundle (emb i) ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (Gc p)
          = (if s = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10)
              (Work.ThomBordism.Grassmann.padGaussFun (emb i) ND p.1)) ∧
      (∀ p : (Work.Tubular.normalBundle (emb i) ND).TotalSpace,
        Work.ThomBordism.Grassmann.evalVec (Gc p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal (emb i) ND p))) ∧
      (∀ (t : Fin (8 + k) → unitInterval),
        Work.Tubular.cubeToEuc (8 + k) R t ∈ (chart i).openTube →
          ∃ hne : Work.Tubular.alphaV (chart i) hR (hbox i) D.t₀ (J i) (hJ i) (g i) (hg i) t
              ≠ D.t₀,
            gauss ⟨Work.Tubular.alphaV (chart i) hR (hbox i) D.t₀ (J i) (hJ i) (g i) (hg i) t,
                hne⟩ =
              (if s = 1 then id else Work.ThomBordism.Grassmann.ogFlip k mU)
                (Work.ThomBordism.padGaussFunM (emb i) ND mU hmU
                  ((chart i).inv (Work.Tubular.cubeToEuc (8 + k) R t)).1.1))

/-- **`GenuineTubeGeometry` forces every piece to be nonempty.**

`Work.Tubular.TubeChart.inv : Euc N → NormalTotal E` is a *total* function into
`NormalTotal E = {p : V.pt × Euc N // p.2 ∈ normalSpace E p.1}`, which is empty when `V.pt` is empty;
so a tube chart — hence the genuine collapse data — of an empty piece does not exist.  This is why the
deliverable's geometric input carries `(∀ i, Nonempty (F i).pt)`
(`Work.ThomBordism.TransversalityCoreFamilyNE`). -/
theorem GenuineTubeGeometry.nonempty {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} (G : GenuineTubeGeometry k D ι Fam) (i : ι) : Nonempty (Fam i).pt :=
  ⟨((G.chart i).inv 0).1.1⟩

/-- **G6, in the form that names the concrete collapse** (`ConcreteLastMile`).

For every finite family of closed oriented `8`-manifolds, every *genuine* collapse datum of it
(`GenuineTubeGeometry`, i.e. TUBULAR's tubular neighbourhoods, Gauss maps and collapse maps, with the
zero-set property), and every `m > 0`: if the `m`-th power of the product of the pieces' genuine
Pontryagin–Thom classes is trivial in `π_{8+k}(D.T)`, then a positive multiple of the family bounds.

Unlike `Work.ThomBordism.PontryaginThom.TransversalityFamily k D` (which quantifies over an arbitrary
loop with the family's Hurewicz pairings, and is therefore as strong as the target itself) and unlike
`Work.PTGeometric.GenuineTransversality k D` (which quantifies over an arbitrary `TubeThomRep`, whose
loop need not be the collapse map), this statement is a statement about the *geometric* collapse of
the disjoint union of the pieces: the object the Pontryagin–Thom construction works on. -/
def ConcreteLastMile (k : ℕ) (D : ThomTarget k) : Prop :=
  letI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  letI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  letI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  ∀ (ι : Type) [Fintype ι] (Fam : ι → Man8) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ),
    0 < m → (∏ i, tubeAlpha (G.rep i)) ^ m = 1 →
      ∃ N' : ℕ, 0 < N' ∧ Nonempty (NullBordismFamily (Fin N' × ι) (fun x => Fam x.2))

/-- **The source construction: the residual geometric statement of the last mile.**

For every finite family and every *genuine* collapse datum of it, and every `m > 0` with the `m`-th
power of the product of the pieces' genuine Pontryagin–Thom classes trivial in `π_{8+k}(D.T)`: a
positive multiple of the family carries the **ambient collapse-end data** of `LastMile.lean` — the
compact source with the ambient coordinates of the null-homotopy of the genuine collapse,
prescribed at the collapse end — together with the **orientation datum** of the situation
(`Work.PTGeometric.AmbientOrientationDataFree`: a `C^∞` `9`-manifold structure on the level set *with
its chart structure chosen by the producer*, an orientation family of it, and a relative fundamental
class of `(↥W, ∂)` whose interior local classes are that family and whose boundary is the **sum** of
the pieces' fundamental classes along the collapse identification — from ORIENT's relative fundamental
class and TUBULAR's local degree).  The chart structure is data (and not the canonical `Lvl` model of
`Work.PTGeometric.LevelOrientationDatum`) because the canonical model's charts are built from
`Classical.choose` witnesses of `Manifold.IsSubmersionAt` whose linear part is unconstrained, so no
lemma can control the orientation they induce — see `NOTE_G5_REPAIR.md` and
`Submission/Work/PTGeometric/OrientationFree.lean`.

This is the only geometric statement of the last mile that is not proved in this subproject; it is
the "make the null-homotopy smooth and transverse to the zero section, and take the preimage" step of
the blueprint (G0–G3), stated for the **genuine** collapse class `∏ i, tubeAlpha (G.rep i)` — i.e.
for the collapse map of the tubular neighbourhoods, whose zero set is the disjoint union of the
pieces by `GenuineTubeGeometry.zero`.  `README.md` §17 records the analysis of what the construction
of the source requires and the obstruction that rules out its *global* form
(`AmbientCollapseEnd` on the whole annulus). -/
def ConcreteLastMileSource (k : ℕ) (D : ThomTarget k) : Prop :=
  letI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  letI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  letI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  ∀ (ι : Type) [Fintype ι] (Fam : ι → Man8) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ),
    0 < m → (∏ i, tubeAlpha (G.rep i)) ^ m = 1 →
      ∃ N' : ℕ, 0 < N' ∧
        ∃ Esrc : AmbientCollapseEnd (k + G.mU) k (Fin N' × ι) (fun x => Fam x.2),
          AmbientOrientationDataFree Esrc

/-- **The source construction gives the last mile**: the ambient collapse-end data and the orientation
datum of the situation produce the null-bordism of a multiple of the family
(`Work.PTGeometric.exists_nullBordismFamily_of_ambientCollapseEnd`), so the last mile reduces to the
*source construction* alone.  Everything between them is proved in this directory. -/
theorem concreteLastMile_of_source {k : ℕ} {D : ThomTarget k}
    (h : ConcreteLastMileSource k D) : ConcreteLastMile k D := by
  intro ι _ Fam G m hm hpow
  obtain ⟨N', hN', Esrc, hOr⟩ := h ι Fam G m hm hpow
  exact ⟨N', hN', exists_nullBordismFamily_of_ambientOrientationDataFree hOr⟩

/-- **The old statement implies the new one**: `GenuineTransversality` quantifies over an arbitrary
Pontryagin–Thom representative, in particular over the genuine one carried by the geometric data.  So
the new last mile is the honest *specialisation* of the old, and the assembly below loses nothing. -/
theorem concreteLastMile_of_genuineTransversality {k : ℕ} {D : ThomTarget k}
    (h : GenuineTransversality k D) : ConcreteLastMile k D := by
  intro ι _ Fam G m hm hpow
  exact h ι Fam (fun i => canonicalNormal (Fam i)) (fun i => G.rep i) m hm hpow

/-- **The deliverable, from the concrete geometric data.**

For every finite family of closed oriented `8`-manifolds: a codimension `k ≥ 11`, a universal Thom
space `D`, the genuine collapse data of the family (`GenuineTubeGeometry`), and the last mile for it
(`ConcreteLastMile`: the null-homotopy of the genuine collapse class bounds a multiple of the family)
imply `Work.ThomBordism.TransversalityCoreFamily`, with rational Hurewicz in the stable range
(`Work.Drive.RationalHurewiczStable3`) as the only other input.

The proof is the one of `Work.ThomBordism.transversalityCoreFamily_of_familyData`: additivity
(`exists_ptFamilyRep_of_parts`) builds the Pontryagin–Thom class of the disjoint union out of the
pieces' genuine classes, rational Hurewicz makes a positive power of it trivial, and the last mile
turns that into the null-bordism.  The difference is that the class whose power is trivialised is the
class of the genuine collapse of the family (`tubeAlpha (G.rep i)`), not the class of an arbitrary
loop. -/
theorem transversalityCoreFamily_of_concreteData
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8),
      ∃ k : ℕ, 11 ≤ k ∧ ∃ D : ThomTarget k,
        Nonempty (GenuineTubeGeometry k D ι F) ∧ ConcreteLastMile k D)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily := by
  intro ι _ F h1 h2
  obtain ⟨k, hk, D, ⟨G⟩, hG⟩ := hdata ι F
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  haveI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  obtain ⟨ρ, hρα⟩ := exists_ptFamilyRep_of_parts (fun i => ptRepOfTubeThomRep (G.rep i))
  obtain ⟨m, hm, hpow⟩ := ρ.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  have hρ : ρ.α = ∏ i, tubeAlpha (G.rep i) := by rw [hρα]; rfl
  have hpow' : (∏ i, tubeAlpha (G.rep i)) ^ m = 1 := by rw [← hρ]; exact hpow
  exact hG ι F G m hm hpow'

/-- **The deliverable, from the concrete geometric data, in the nonempty-family form.**

This is `Work.PTGeometric.transversalityCoreFamily_of_concreteData` with the honest hypothesis that
every member of the family is nonempty.  The geometric data cannot be produced for an empty piece —
`Work.Tubular.TubeChart.inv` is a total function, so a tube chart of an empty manifold does not
exist, and `Work.PTGeometric.GenuineTubeGeometry` is uninhabited for it — while `Man8` carries no
nonemptiness (`Work.ThomBordism.Man8.empty`).  The consumer drops the empty members of a family
(their numbers vanish) and transports the null-bordism:
`Work.ThomBordism.transversalityCoreFamily_of_nonempty`. -/
theorem transversalityCoreFamilyNE_of_concreteDataNE
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, Nonempty (F i).pt) →
      ∃ k : ℕ, 11 ≤ k ∧ ∃ D : ThomTarget k,
        Nonempty (GenuineTubeGeometry k D ι F) ∧ ConcreteLastMile k D)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyNE := by
  intro ι _ F hne h1 h2
  obtain ⟨k, hk, D, ⟨G⟩, hG⟩ := hdata ι F hne
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  haveI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  obtain ⟨ρ, hρα⟩ := exists_ptFamilyRep_of_parts (fun i => ptRepOfTubeThomRep (G.rep i))
  obtain ⟨m, hm, hpow⟩ := ρ.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  have hρ : ρ.α = ∏ i, tubeAlpha (G.rep i) := by rw [hρα]; rfl
  have hpow' : (∏ i, tubeAlpha (G.rep i)) ^ m = 1 := by rw [← hρ]; exact hpow
  exact hG ι F G m hm hpow'

/-- **The deliverable, from the concrete geometric data, in the connected-family form.**

This is `Work.PTGeometric.transversalityCoreFamilyNE_of_concreteDataNE` with the family hypothesis
restricted to families whose members are **connected** — the form the geometric producers of the
*first* half (`GenLoop` tubular data, local degree) actually reach
(`Work.ThomBordism.TransversalityCoreFamilyConn`, `Work.ThomBordism.finalWiringConn`).  The proof never
uses the restriction. -/
theorem transversalityCoreFamilyConn_of_concreteDataConn
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
      ∃ k : ℕ, 11 ≤ k ∧ ∃ D : ThomTarget k,
        Nonempty (GenuineTubeGeometry k D ι F) ∧ ConcreteLastMile k D)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamilyConn := by
  intro ι _ F _ h1 h2
  obtain ⟨k, hk, D, ⟨G⟩, hG⟩ := hdata ι F (fun i => inferInstance)
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  haveI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  obtain ⟨ρ, hρα⟩ := exists_ptFamilyRep_of_parts (fun i => ptRepOfTubeThomRep (G.rep i))
  obtain ⟨m, hm, hpow⟩ := ρ.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  have hρ : ρ.α = ∏ i, tubeAlpha (G.rep i) := by rw [hρα]; rfl
  have hpow' : (∏ i, tubeAlpha (G.rep i)) ^ m = 1 := by rw [← hρ]; exact hpow
  exact hG ι F G m hm hpow'

end

end Work.PTGeometric
