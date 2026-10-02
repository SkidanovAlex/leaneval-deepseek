import Mathlib
import Submission.Work.ThomBordism.localDegree_localisation
import Submission.Work.ThomBordism.value_eq_chartModelClass
import Submission.Work.ThomBordism.collapseLocalisation_ambientV2
import Submission.Work.ThomBordism.tubeInvHomologyCollapse
import Submission.Work.ThomBordism.exists_zeroSection_pairing_one
import Submission.Work.ThomBordism.fibreReading_collapseClass
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.gtdUWith_frameEval
import Submission.Work.ThomBordism.frameEval_realThomClassOf

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

open Work.ThomBordism.PontryaginThom Work.Tubular

/-!
# The ambient/fibre comparison, and the target from it

This file isolates the **one remaining cross-datum step** of the path
`ThomBordism/localDegree_universalThomClass` into two statements whose *conjunction* implies the
target, and proves that implication.

## The two inputs

* `Work.ThomBordism.AmbientUniform k` — **(CLA)**: the *ambient local degree of the collapse*,
  i.e. the pairing of the ambient chart model class with the collapse class,
  `⟨chartModelClass E C x, collapseRelK8 C g hg hR hbox⟩`, is a **single** `κ = ±1` over all data.
  This is exactly the statement of the project lead's round-47 chain
  (`Work.ThomBordism.collapseLocalisation_ambientV2`), phrased with the base point `x` inside the
  chart model class instead of in the ambient standard class (the two forms are equivalent by
  `Work.ThomBordism.value_eq_chartModelClass`, which is PROVED, together with the existence of a
  preimage of `collapseRelK8` under `tubeInvHomology`).
  Per datum the value is `±1` by `Work.ThomBordism.chartModelClass_pairing_eq_pm_one` (PROVED).

* `Work.ThomBordism.AmbientFibreLink k hk` — **(the link)**: the *sign comparison*
  `nfRes E x k U = (ε · ⟨chartModelClass E C x, collapseRelK8⟩) • coorFibre hk E ND x`
  for a **single** `ε = ±1` over all data, all local-degree classes `U` and all `x`.
  Equivalently (using the PROVED pin `⟨nfRes U, z⟩ = 1` and `⟨coorFibre, z⟩ = δ` of
  `Submission/Work/ThomBordism/localDegree_localisation.lean`): the branch sign `δ` of the
  local-degree class is the ambient local degree `⟨chartModelClass, collapseRelK8⟩`, up to the
  universal constant `ε`.  This is the lead's step **(d)** ("the Künneth contraction of the
  degree-`8+k` pairing to the fibre, composed with the chart-frame-versus-`gframe` comparison, which
  is the fixed σ/gauge factor pinned by TEL").

The two inputs are *independent*: `AmbientUniform` says nothing about fibre readings, and
`AmbientFibreLink` says nothing about the constancy of a sign over data.  Neither implies the target
alone; their conjunction does, and that is the theorem below.

## The reduction (PROVED here, axiom-clean)

    AmbientUniform k → AmbientFibreLink k hk → localDegree_universalThomClass k hk

Proof: on any datum and any local-degree class `U` the link gives
`nfRes U = (ε κ) • coorFibre`, with `ε κ` independent of the datum since `κ` is (CLA) and `ε` is
(the link).  `Work.ThomBordism.exists_coorFibre_eq_smul_nfGen` (PROVED) turns `coorFibre` into a
fixed multiple of `nfGen`, so the *uniform fibre restriction* UF2 holds, and
`Work.ThomBordism.localDegree_universalThomClass_of_uniformF2` (PROVED) produces a single `u₀`.
-/

/-- **The ambient chart model class of a datum**, with the continuity obligation of
`Work.ThomBordism.chartModelClass` discharged (`Work.ThomBordism.continuous_chartAffine_cap`). -/
noncomputable def ambientValueClass {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) :=
  Work.ThomBordism.chartModelClass E C x (Work.ThomBordism.continuous_chartAffine_cap E C x)

/-- **(CLA) `AmbientUniform`**: the *ambient local degree* of the collapse,
`⟨chartModelClass E C x, collapseRelK8 C g hg hR hbox⟩`, is a single `κ = ±1` over all data.

This is the chart-model-class form of the project lead's round-47 target
`Work.ThomBordism.collapseLocalisation_ambientV2`; the equivalence of the two forms is
`Work.ThomBordism.value_eq_chartModelClass` (PROVED) together with the existence of a preimage of
`collapseRelK8` under `tubeInvHomology` (`Work.ThomBordism.tubeInvHomologyCollapse`); see
`ambientUniform_of_claAmbient` below, where the preimage is a hypothesis.

The binders `q`, `hU`, `hg2` are not used by the conclusion (the collapse class does not see them);
they are carried so that the statement can be *produced* from the ambient form of the CLA theorem,
which carries them. -/
def AmbientUniform (k : ℕ) : Prop :=
  ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
      (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (x : V.pt),
      Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ ambientValueClass E C x)
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = κ

/-- **(The link)** `AmbientFibreLink`: the fibre reading of a local-degree class is the
coorientation reference, scaled by the *ambient local degree* of the collapse, up to a single
universal sign `ε`.

Equivalently: the branch sign of the local-degree class equals the ambient local degree of the
collapse, up to a universal constant.  This is step **(d)** of the project lead's route; it is a
*per-datum* statement (no cross-datum content), and it is the only input of the target that is not
covered by (CLA) and the per-datum results. -/
def AmbientFibreLink (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      {ε₀ : ℝ} (C : Work.Tubular.TubeChart E ε₀) (q : Work.Tubular.NormalSphSub E ε₀)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε₀ (C.inv y)))
      (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
      ∀ x : V.pt,
        Work.ThomBordism.nfRes E x k U
          = (ε * (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
                (Work.Tubular.normalNonzero E) (k + 8)
                ((Nat.add_comm 8 k) ▸ ambientValueClass E C x)
                (Work.Tubular.collapseRelK8 C g hg hR hbox)))
              • Work.ThomBordism.coorFibre (V := V) hk E ND x

/-- **The target from (CLA) and the link.** -/
theorem localDegree_universalThomClass_of_ambient (k : ℕ) (hk : 1 ≤ k)
    (hA : AmbientUniform k) (hd : AmbientFibreLink k hk) :
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
  obtain ⟨κ, hκ, hA'⟩ := hA
  obtain ⟨ε, hε, hd'⟩ := hd
  obtain ⟨εm, hεm, hconv⟩ := Work.ThomBordism.exists_coorFibre_eq_smul_nfGen (k := k) hk
  refine Work.ThomBordism.localDegree_universalThomClass_of_uniformF2 k hk
    ⟨ε * κ * εm, ?_, ?_⟩
  · rcases hκ with h | h <;> rcases hε with h' | h' <;> rcases hεm with h'' | h'' <;>
      rw [h, h', h''] <;> norm_num
  · intro V _inst E ND ε₀ C q hUc R hR hbox g hg hg2 U hILD x
    rw [hd' E ND C q hUc hR hbox g hg hg2 U hILD x,
      hA' E C q hUc hR hbox g hg hg2 x, hconv E ND x, smul_smul]

end


/-- **(PRE)**, as a hypothesis: `collapseRelK8` lies in the image of the tube-inverse map on relative
homology (this is `Work.ThomBordism.tubeInvHomologyCollapse`, delegated separately; the file with
that name is the intended supplier). -/
def TubePreimage (k : ℕ) : Prop :=
  ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R),
    ∃ δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8),
      Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox

/-- **(CLA), the ambient form** (verbatim the conclusion of
`Work.ThomBordism.collapseLocalisation_ambientV2`, the project lead's round-47 target). -/
def AmbientUniformAmbient (k : ℕ) : Prop :=
  ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
      (C : Work.Tubular.TubeChart E ε)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
      (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8)),
      Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox →
      Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x) δ = κ

/-- **The chart form of the CLA core from the ambient form plus the tube preimage.**
`Work.ThomBordism.value_eq_chartModelClass` (PROVED) identifies the ambient pairing with the chart
pairing; the preimage hypothesis supplies a `δ` for every datum, so that the ambient form is not
vacuous there. -/
theorem ambientUniform_of_claAmbient (k : ℕ) (hk : 1 ≤ k)
    (hpre : TubePreimage k) (hCLA : AmbientUniformAmbient k) : AmbientUniform k := by
  obtain ⟨κ, hκ, hcl⟩ := hCLA
  refine ⟨κ, hκ, ?_⟩
  intro V _inst E ε C q hU R hR hbox g hg hg2 x
  obtain ⟨δ, hδ⟩ := hpre E C g hg hg2 hR hbox
  exact (Work.ThomBordism.value_eq_chartModelClass E C g hg hR hbox x
    (Work.ThomBordism.continuous_chartAffine_cap E C x) δ hδ).symm.trans
    (hcl E C g hg hg2 hR hbox x δ hδ)


/-- **(PRE) is available unconditionally**: the tube inverse induces a *surjection* on relative
homology (`Work.ThomBordism.tubeInvHomology_surjective`, proved in
`Submission/Work/ThomBordism/tubeInvHomologyCollapse.lean`), so `collapseRelK8` has a preimage. -/
theorem tubePreimage (k : ℕ) : TubePreimage k := by
  intro V _inst E ε C g hg hg2 R hR hbox
  exact Work.ThomBordism.tubeInvHomologyCollapse (V := V) (k := k) E C g hg hg2 hR hbox

/-- **The chart form of the CLA core from its ambient form** (no extra hypothesis): the ambient form
is the single `sorry`ed target of `Submission/Work/ThomBordism/collapseLocalisation_ambientV2.lean`,
and the two forms are equivalent by `Work.ThomBordism.value_eq_chartModelClass` plus the tube
preimage `Work.ThomBordism.tubePreimage` above. -/
theorem ambientUniform_of_claAmbient' (k : ℕ) (hk : 1 ≤ k)
    (hCLA : AmbientUniformAmbient k) : AmbientUniform k :=
  ambientUniform_of_claAmbient k hk (tubePreimage k) hCLA

/-- **The target from the two remaining inputs, in the form in which the project lead's round-47
chain supplies them**: the *ambient* CLA theorem (the `sorry`ed target of
`collapseLocalisation_ambientV2.lean`) together with the ambient/fibre link
(`Work.ThomBordism.ambientFibreLink`). -/
theorem localDegree_universalThomClass_of_claAmbient_of_link (k : ℕ) (hk : 1 ≤ k)
    (hCLA : AmbientUniformAmbient k) (hd : AmbientFibreLink k hk) :
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
        (Work.ThomBordism.gtdUWith E ND G hgm u₀) :=
  localDegree_universalThomClass_of_ambient k hk
    (ambientUniform_of_claAmbient' k hk hCLA) hd


/-- **(A) is available**: `PieceA k` from the PROVED `exists_zeroSection_pairing_one`. -/
theorem pieceA (k : ℕ) : PieceA k := by
  intro V _ E
  exact Work.ThomBordism.exists_zeroSection_pairing_one (V := V) k E

/-- **(P1) is available**: `PieceP1 k` from the PROVED `fibreReading_collapseClass`. -/
theorem pieceP1 (k : ℕ) (hk : 1 ≤ k) : PieceP1 k := by
  intro V _ E ε C q hU R hR hbox g hg hg2 x w hw
  exact Work.ThomBordism.fibreReading_collapseClass (V := V) (k := k) hk E C q hU hR hbox g hg hg2
    x w hw

/-- **The target from (P2)** — the closure requested by the project lead's round-48 message: the
three pieces `PieceA`, `PieceP1`, `PieceP2` of `Submission/Work/ThomBordism/localDegree_localisation.lean`
give the target, and (A) and (P1) are proved here (`pieceA`, `pieceP1`), so the target follows from
(P2) alone (`Work.ThomBordism.coorFibre_fibreGenerator`, being closed along the lead's route
`KeyLocal ∧ (CLA) ⟹ (P2)`). -/
theorem localDegree_universalThomClass_of_p2 (k : ℕ) (hk : 1 ≤ k)
    (hP2 : PieceP2 k hk) :
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
        (Work.ThomBordism.gtdUWith E ND G hgm u₀) :=
  Work.ThomBordism.localDegree_universalThomClass_of_pieces k hk (pieceA k) (pieceP1 k hk) hP2

/-- **(CLA) holds unconditionally**: the ambient form is the PROVED
`Work.ThomBordism.collapseLocalisation_ambientV2` (project lead, round 48), transported to the chart
form by `ambientUniform_of_claAmbient'`. -/
theorem ambientUniform (k : ℕ) (hk : 1 ≤ k) : AmbientUniform k :=
  ambientUniform_of_claAmbient' k hk (Work.ThomBordism.collapseLocalisation_ambientV2 k hk)

/-- **The target from the link alone** (the CLA core now being proved). -/
theorem localDegree_universalThomClass_of_link (k : ℕ) (hk : 1 ≤ k)
    (hd : AmbientFibreLink k hk) :
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
        (Work.ThomBordism.gtdUWith E ND G hgm u₀) :=
  localDegree_universalThomClass_of_ambient k hk (ambientUniform k hk) hd


/-- **(KL) with the pinning clauses** — the project lead's `Work.ThomBordism.KeyLocal` with `hbp`
and `hvec` added.  The pinning is *necessary*: without it the statement is refutable by a constant
`G` (whose values lie in the zero complement, so that `hgm` holds but `gtdUWith … = 0`), see
`Submission/Work/ThomBordism/URGENT_KL_quantifier.md`; and `Work.ThomBordism.G_eq_frameEval` shows
such a `G` is unique, so nothing is lost.  Every use of
`Work.ThomBordism.nfRes_gtdUWith_realThomClassOf_eq_coorFibre` already needs `hbp`/`hvec`, which is
exactly why the unpinned form cannot be true. -/
def KeyLocalPinned (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
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
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
      (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E))),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 →
      Work.Cohomology.mixedCup
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w
          (Work.ThomBordism.gtdUWith E ND G hgm
            (Work.Thom.realThomClassOf hk
              (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.tautologicalBundle_horiO k)))
        = s • Work.ThomBordism.ambientValueClass E C x

/-- **The pinned KL implies the ambient/fibre link** — which mentions no `G` at all, so it is not
vulnerable to the `∀ G` mis-quantification.  The proof produces the *pinned* Gauss candidate
(`Work.ThomBordism.gtdGaussCandidate`) and converts the two `(P1)`-pins `⟨nfRes U, z⟩ = 1` and
`⟨nfRes Ucan, z⟩ = s κ` into the ratio of the two fibre readings. -/
theorem ambientFibreLink_of_keyLocalPinned (k : ℕ) (hk : 1 ≤ k) (hKL : KeyLocalPinned k hk) :
    AmbientFibreLink k hk := by
  classical
  obtain ⟨s, hs, hKL'⟩ := hKL
  obtain ⟨κ, hκ, hCLA⟩ := ambientUniform k hk
  refine ⟨s, hs, ?_⟩
  intro V _inst E ND ε₀ C q hUc R hR hbox g hg hg2 U hILD x
  -- a *pinned* Gauss candidate
  obtain ⟨G, hbp, hvec, hgm, -⟩ :=
    Work.ThomBordism.gtdGaussCandidate (V := V) (k := k) E ND C.eps_pos C q hUc hR hbox g hg hg2
  -- the canonical class and its fibre reading
  set Ucan : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) :=
    Work.ThomBordism.gtdUWith E ND G hgm
      (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.tautologicalBundle_horiO k)) with hUcandef
  have hnfCan : Work.ThomBordism.nfRes E x k Ucan
      = Work.ThomBordism.coorFibre (V := V) hk E ND x := by
    rw [hUcandef,
      Work.ThomBordism.nfRes_gtdUWith_eq_frameEval hk E ND G hgm hbp hvec x,
      Work.ThomBordism.frameEval_realThomClassOf k hk
        (Work.ThomBordism.tautologicalBundle_horiO k) (Work.ThomBordism.datumFrame E ND x)]
    exact (Work.ThomBordism.coorFibre_eq (V := V) hk E ND x).symm
  -- (A) and (P1) at this datum
  obtain ⟨w, hw⟩ := pieceA k (V := V) E
  obtain ⟨z, hzspan, hzrel⟩ := pieceP1 k hk (V := V) E C q hUc hR hbox g hg hg2 x w hw
  -- the uniform ambient value
  have hK : Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) (k + 8)
      ((Nat.add_comm 8 k) ▸ ambientValueClass E C x)
      (Work.Tubular.collapseRelK8 C g hg hR hbox) = κ :=
    hCLA E C q hUc hR hbox g hg hg2 x
  -- the two pairing identities
  have hpairU : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U) z = 1 := by
    rw [hzrel U, hILD w, hw]
  have hpairCan : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k Ucan) z = s * κ := by
    rw [hzrel Ucan, hKL' E ND G hgm hbp hvec C x w hw,
      Work.Tubular.relCoh_cast_zsmul, map_zsmul, LinearMap.smul_apply, hK]
    rfl
  have hpairCoor : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.coorFibre (V := V) hk E ND x) z
      = s * κ := by
    rw [← hnfCan]; exact hpairCan
  -- `U` generates, hence so does its fibre reading
  obtain ⟨U₀, hU₀span, hU₀ild⟩ :=
    localDegreeGenExists (V := V) (k := k) hk E C.eps_pos C q hUc hR hbox g hg hg2
  have hUeq : U = U₀ := isLocalDegreeClass_eq_of_generating (V := V) (k := k) (E := E) (C := C)
    q hR hbox g hg hg2 hU₀span hU₀ild hILD
  have hUspan : Submodule.span ℤ ({U} : Set (Work.Thom.RelCoh ℤ k
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤ := by
    rw [hUeq]; exact hU₀span
  have hspana : Submodule.span ℤ ({(Work.ThomBordism.nfRes E x k U)} : Set
      (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
        (Work.ThomBordism.nfPunct E x))) = ⊤ :=
    Work.ThomBordism.nfRes_span_top_of_generator (V := V) (k := k) hk E ND x hUspan
  have hspanb : Submodule.span ℤ ({(Work.ThomBordism.coorFibre (V := V) hk E ND x)} : Set
      (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
        (Work.ThomBordism.nfPunct E x))) = ⊤ :=
    coorFibre_span (V := V) (k := k) hk E ND x
  obtain ⟨e⟩ := Work.ThomBordism.nfRelCohIso (V := V) (k := k) hk E ND x
  -- the goal is the scalar equation; the pairing values pin the scalar
  rw [hK]
  rcases Work.ThomBordism.eq_pm_of_span_eq_top_of_iso e hspana hspanb with h | h
  · -- `nfRes U = coorFibre`; then `s * κ = 1`
    have hsκ : s * κ = 1 := by
      rw [← hpairCoor, ← h]
      exact hpairU
    rw [hsκ, one_smul]
    exact h
  · -- `nfRes U = - coorFibre`; then `s * κ = -1`
    have hsκ : s * κ = -1 := by
      have h1 : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
          (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U) z = -(s * κ) := by
        rw [h, Work.Tubular.relKronH_neg_left, hpairCoor]
      rw [h1] at hpairU
      omega
    rw [hsκ, neg_one_zsmul]
    exact h

/-- **The target from the pinned KL.** -/
theorem localDegree_universalThomClass_of_keyLocalPinned (k : ℕ) (hk : 1 ≤ k)
    (hKL : KeyLocalPinned k hk) :
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
        (Work.ThomBordism.gtdUWith E ND G hgm u₀) :=
  localDegree_universalThomClass_of_link k hk (ambientFibreLink_of_keyLocalPinned k hk hKL)

end Work.ThomBordism
