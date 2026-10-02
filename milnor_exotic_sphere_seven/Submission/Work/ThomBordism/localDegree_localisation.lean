import Mathlib
import Submission.Work.ThomBordism.localDegree_universalThomClass_bridge
import Submission.Work.ThomBordism.nfGen_span
import Submission.Work.ThomBordism.stdModelGen_pm_stdThomGen
import Submission.Work.ThomBordism.tubeLocalDegreeGlobalSign
import Submission.Work.ThomBordism.nfRes_span_top_of_generator
import Submission.Work.ThomBordism.localDegreeGenExists
import Submission.Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen_uniform

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The localisation of the fibre reading of a local-degree class, and the target

This file assembles the target `Work.ThomBordism.localDegree_universalThomClass` out of three
statements, each of which is *strictly weaker* than the target and independent of the others
(they are dispatched as separate lemmas):

* **(A) `PieceA`** — there is a degree-`8` class `w` of the normal total space whose pairing with
  the fundamental class is `1` (the degree-`8` Kronecker pairing of a closed oriented connected
  `8`-manifold onto `ℤ` is surjective);
* **(P1) `PieceP1`** — *the localisation*: for such a `w` there is a generator `z` of the fibre pair
  `(ν_x, ν_x∖0)` such that the functional `U ↦ ⟨nfRes U, z⟩` is `U ↦ ⟨w ⌣ U, c⟩` (with `c` the
  collapse class); equivalently the fibre reading of a local-degree class is the geometric fibre
  fundamental class of the collapse;
* **(P2) `PieceP2`** — *the coorientation comparison*: the pairing of the *coorientation reference*
  `coorFibre` with that generator `z` is a single `t = ±1`, the same for every datum.

The assembly below proves

  `PieceA → PieceP1 → PieceP2 → ∃ t ∈ {±1}, ∀ (data) (U) (IsLocalDegreeClass U) (x),
      nfRes E x k U = t • coorFibre hk E ND x`,

and then the target by the bridge `Work.ThomBordism.localDegree_universalThomClass_of_uniformF2`
(the coorientation reference is a fixed multiple of `nfGen`, so the uniform `coorFibre` form gives
the uniform `nfGen` form).

The *content* of the three pieces: (P1) is the "cap product localises to the fibre" half of the
local-degree chapter (a homological statement about the collapse class), and (P2) is the comparison
of the collapse's fibre orientation with the σ-corrected Gauss frame — the sign that
`Work.ThomBordism.NOTE_SESSION41_UNIVERSAL.md` §4 calls the last-mile normalisation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

/-- **The coorientation reference generates the fibre module.**  `coorFibre hk E ND x` is the
reading of the determinate standard model generator `stdModelGen k` in the σ-corrected frame, and
the reading is surjective (it is the pullback along the frame identification `nfRead`, which is
surjective by `Work.ThomBordism.nfRead_surjective`), so it carries generators to generators. -/
theorem coorFibre_span {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Submodule.span ℤ ({Work.ThomBordism.coorFibre hk E ND x} : Set
      (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
        (Work.ThomBordism.nfPunct E x))) = ⊤ := by
  rw [Work.ThomBordism.coorFibre_eq]
  exact Work.Tubular.span_singleton_map_eq_top _
    (Work.ThomBordism.nfRead_surjective hk E ND x)
    (Work.ThomBordism.stdModelGen_span k hk)

/-- **(A)** There is a degree-`8` class of the normal total space whose pairing with the fundamental
class of the member is `1`. -/
def PieceA (k : ℕ) : Prop :=
  ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)),
    ∃ w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1

/-- **(P1) The localisation of the collapse class to the fibre.**  For a degree-`8` class `w` whose
pairing with the fundamental class is `1`, the functional `U ↦ ⟨nfRes U, z⟩` on the relative
cohomology of the Thom pair is `U ↦ ⟨w ⌣ U, c⟩`, for a suitable *generator* `z` of the fibre pair;
equivalently the fibre reading of a local-degree class is the geometric fibre fundamental class of
the collapse. -/
def PieceP1 (k : ℕ) : Prop :=
  ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (x : V.pt)
    (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)))
    (hw : Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1),
    ∃ z : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x)).homology k,
      Submodule.span ℤ ({z} : Set _) = ⊤ ∧
      ∀ U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E),
        Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
            (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U) z
          = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
              (Work.Tubular.normalNonzero E) (k + 8)
              ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
                (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w U))
              (Work.Tubular.collapseRelK8 C g hg hR hbox)

/-- **(P2) The coorientation comparison.**  The pairing of the coorientation reference `coorFibre`
with the fibre generator `z` of (P1) is a *single* `t = ±1`, the same for every datum. -/
def PieceP2 (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (x : V.pt)
      (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)))
      (z : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x)).homology k),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 →
      Submodule.span ℤ ({z} : Set _) = ⊤ →
      (∀ U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E),
        Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
            (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U) z
          = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
              (Work.Tubular.normalNonzero E) (k + 8)
              ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
                (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w U))
              (Work.Tubular.collapseRelK8 C g hg hR hbox)) →
      Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
          (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.coorFibre hk E ND x) z = t

/-- **The localisation of the fibre reading of a local-degree class.**  From the three pieces
`PieceA`, `PieceP1`, `PieceP2` the fibre reading of every local-degree class is a *single* unit
multiple `t • coorFibre` of the coorientation reference, the same for all data.

Proof: fix the datum and a local-degree class `U`; by the uniqueness of the local-degree class
(`isLocalDegreeClass_eq_of_generating` + `localDegreeGenExists`) the class generates
`H^k(ν, ν∖0)`; pick `w` by (A) and `z` by (P1).  Then `⟨nfRes U, z⟩ = ⟨w ⌣ U, c⟩ = ⟨z^*w, V.c⟩ = 1`
by (P1), the local-degree condition and (A), while `⟨coorFibre, z⟩ = t` by (P2).  Both `nfRes U` and
`coorFibre` are generators of the rank-one free fibre module (`nfRes_span_top_of_generator`,
`coorFibre_span`), hence differ by a sign (`eq_pm_of_span_eq_top_of_iso` with the iso
`nfRelCohIso`); the two values `1` and `t` then force the sign to be exactly `t`. -/
theorem localisation_of_pieces (k : ℕ) (hk : 1 ≤ k)
    (hA : PieceA k) (hP1 : PieceP1 k) (hP2 : PieceP2 k hk) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
        (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)) (x : V.pt),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
        Work.ThomBordism.nfRes E x k U
          = t • Work.ThomBordism.coorFibre hk E ND x := by
  classical
  obtain ⟨t, htm, hP2t⟩ := hP2
  refine ⟨t, htm, ?_⟩
  intro V _inst E ND ε C q hU R hR hbox g hg hg2 U x hUild
  -- a generating local-degree class and the uniqueness of the local-degree class
  obtain ⟨U₀, hU₀span, hU₀ild⟩ :=
    localDegreeGenExists hk E C.eps_pos C q hU hR hbox g hg hg2
  have hUeq : U = U₀ := isLocalDegreeClass_eq_of_generating (V := V) (k := k) (E := E) (C := C)
    q hR hbox g hg hg2 hU₀span hU₀ild hUild
  -- (A) and (P1)
  obtain ⟨w, hw⟩ := hA (V := V) E
  obtain ⟨z, hzspan, hzrel⟩ := hP1 (V := V) E C q hU hR hbox g hg hg2 x w hw
  -- the two values
  have h1 : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U) z = 1 := by
    rw [hzrel U, hUild w, hw]
  have h2 : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.coorFibre hk E ND x) z = t :=
    hP2t E ND C q hU hR hbox g hg hg2 x w z hw hzspan hzrel
  -- both classes generate the rank-one free fibre module
  have hspana : Submodule.span ℤ ({(Work.ThomBordism.nfRes E x k U)} : Set
      (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
        (Work.ThomBordism.nfPunct E x))) = ⊤ := by
    have hUspan : Submodule.span ℤ ({U} : Set (Work.Thom.RelCoh ℤ k
        (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤ := by
      rw [hUeq]; exact hU₀span
    exact Work.ThomBordism.nfRes_span_top_of_generator (V := V) (k := k) hk E ND x hUspan
  have hspanb : Submodule.span ℤ ({(Work.ThomBordism.coorFibre hk E ND x)} : Set
      (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
        (Work.ThomBordism.nfPunct E x))) = ⊤ :=
    coorFibre_span (V := V) (k := k) hk E ND x
  obtain ⟨e⟩ := Work.ThomBordism.nfRelCohIso (V := V) (k := k) hk E ND x
  rcases Work.ThomBordism.eq_pm_of_span_eq_top_of_iso e hspana hspanb with h | h
  · -- `nfRes U = coorFibre`; the two values give `t = 1`
    have ht1 : t = 1 := by rw [h] at h1; rw [h2] at h1; exact h1
    rw [h, ht1, one_smul]
  · -- `nfRes U = - coorFibre`; the two values give `t = -1`
    have ht1 : t = -1 := by
      have hneg : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
          (Work.ThomBordism.nfPunct E x) k (-(Work.ThomBordism.coorFibre hk E ND x)) z = 1 := by
        rw [← h]; exact h1
      rw [Work.Tubular.relKronH_neg_left, h2] at hneg
      omega
    rw [h, ht1, neg_one_zsmul]

/-- **The target from the three pieces.**  The uniform `coorFibre` form of the localisation gives the
uniform `nfGen` form (the two references differ by a fixed sign, `exists_coorFibre_eq_smul_nfGen`),
and `localDegree_universalThomClass_of_uniformF2` converts the latter into the target. -/
theorem localDegree_universalThomClass_of_pieces (k : ℕ) (hk : 1 ≤ k)
    (hA : PieceA k) (hP1 : PieceP1 k) (hP2 : PieceP2 k hk) :
    ∃ u₀ : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k,
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
        (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
          = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
        (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (Work.ThomBordism.gtdUWith E ND G hgm u₀) := by
  obtain ⟨t, htm, hloc⟩ := localisation_of_pieces k hk hA hP1 hP2
  obtain ⟨εm, hεm, hconv⟩ := Work.ThomBordism.exists_coorFibre_eq_smul_nfGen (k := k) hk
  refine Work.ThomBordism.localDegree_universalThomClass_of_uniformF2 k hk ⟨t * εm, ?_, ?_⟩
  · rcases htm with h | h <;> rcases hεm with h' | h' <;> rw [h, h'] <;> norm_num
  · intro V _inst E ND ε C q hU R hR hbox g hg hg2 U hUild x
    rw [hloc E ND C q hU hR hbox g hg hg2 U x hUild, hconv E ND x, smul_smul]

/-- **(P2) is the local-degree pairing of any class with fibre reading `coorFibre`.**  From the
(P1)-relation for the fibre generator `z` and the defining property of `coorFibre`, the pairing of
`coorFibre` with `z` is the *local-degree pairing* `⟨w ⌣ W, c⟩` of any class `W` whose fibre reading
is `coorFibre`.

In particular, taking `W` the canonical Gauss candidate
(`Work.ThomBordism.nfRes_gtdUWith_realThomClassOf_eq_coorFibre`, PROVED) identifies the left side of
(P2) with `⟨w ⌣ (G^*(Ucan)), c⟩`, i.e. with the *branch sign* of the canonical class: so (P2) *is*
the uniformity of the branch sign (the family's H4-L2660 crux,
`Work.ThomBordism.branchSign_uniform_gauss`), seen from the collapse side.  Nothing new is hidden in
(P2) beyond that uniformity. -/
theorem coorFibre_pairing_eq_of_fibreReading {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (x : V.pt)
    (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)))
    (z : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x)).homology k)
    (hzrel : ∀ U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E),
      Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
          (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U) z
        = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) (k + 8)
            ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
              (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w U))
            (Work.Tubular.collapseRelK8 C g hg hR hbox))
    (W : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E))
    (hW : Work.ThomBordism.nfRes E x k W = Work.ThomBordism.coorFibre hk E ND x) :
    Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.coorFibre hk E ND x) z
      = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w W))
          (Work.Tubular.collapseRelK8 C g hg hR hbox) := by
  rw [← hW]
  exact hzrel W

end

end Work.ThomBordism
