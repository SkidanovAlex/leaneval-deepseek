import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.ThomBordism.localDegreeGenExists
import Submission.Work.ThomBordism.FrameSigns.relKronH_natural
import Submission.Work.ThomBordism.localDegree_universalThomClass_bridge
import Submission.Work.ThomBordism.gtdUWith_eq_of_normalData
import Submission.Work.ThomBordism.fibreRes_gtdU_canonical
import Submission.Work.ThomBordism.collapseRelK8_indep_tube
import Submission.Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen_uniform
import Submission.Work.ThomBordism.ambientBase
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.ThomBordism.value_eq_chartModelClass
import Submission.Work.ThomBordism.tubeInvHomologyCollapse
import Submission.Work.ThomBordism.collapseLocalisation_ambientV2
import Submission.Work.ThomBordism.kronH_fund_injective_top
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.frameEval_realThomClassOf
import Submission.Work.ThomBordism.canonicalGauss_assembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `coorFibre_fibreGenerator`: the target, and its exact remaining input

## The statement

`Work.ThomBordism.coorFibre_fibreGenerator (k) (hk)` asserts a *single* `t = ±1` such that for every
configuration (`V`, `E`, `ND`, tube data `C, q, g`, a point `x`, a degree-`8` class `w` of the normal
total space with `⟨zs^*w, V.c⟩ = 1`, and a *generator* `z` of the fibre pair pinned by

    `∀ U, ⟨nfRes U, z⟩ = ⟨w ⌣ U, collapseRelK8⟩`,

one has `⟨coorFibre hk E ND x, z⟩ = t`.  It is *literally* the predicate `Work.ThomBordism.PieceP2`
of `Submission/Work/ThomBordism/localDegree_localisation.lean` (the assembly there derives the
project's uniform localisation from `PieceA`, `PieceP1`, `PieceP2`, and `PieceA`/`PieceP1` are
PROVED — `exists_zeroSection_pairing_one`, `fibreReading_collapseClass`).

## The reduction to (KL) — the state of this file (session 2)

The target now follows from **one** statement, the key local comparison (KL) of the project lead's
probe 48, which is `Work.ThomBordism.KeyLocal` of `Submission/Work/ThomBordism/keyLocal.lean`:

  * `KeyLocalData k hk` (this file) is KL with the ambient chart model class written out
    (`ambientValueClass E C x = chartModelClass E C x (continuous_chartAffine_cap E C x)` by
    definition, so the two statements are *definitionally equal*; this file is written against the
    expansion so that it depends only on stable modules):

      `π^*(w) ⌣ Ucan = s • (ambient chart model class)`   (`s = ±1` the same for all data),

    where `Ucan` is the canonical Thom class of the tautological oriented bundle.
  * `coorFibre_fibreGenerator_of_keyLocalData : KeyLocalData k hk → (the target)` — **PROVED here,
    axiom-clean**.  This is the project lead's (ALG) step: on any datum, apply the pin at
    `U := Ucan`; the fibre reading of `Ucan` is `coorFibre` (the PROVED
    `nfRes_gtdUWith_realThomClassOf_eq_coorFibre`, with the PROVED `frameEval_realThomClassOf` as
    its frame input), so
    `⟨coorFibre, z⟩ = ⟨w ⌣ Ucan, c⟩ = s · ⟨ambient chart model class, c⟩ = s · κ`.
  * `ambientPairing_uniform` — **PROVED here, axiom-clean**: the `κ`-chapter in chart-model form
    (`∃ κ = ±1, ∀ data, ⟨ambient chart model class, collapseRelK8⟩ = κ`), from the PROVED
    `collapseLocalisation_ambientV2` and `value_eq_chartModelClass`.
  * `zsmul_cast_relCoh` — the degree cast commutes with the scalar action (the row used by (ALG)).

So **the target is `KeyLocalData k hk`** (`Work.ThomBordism.keyLocal k hk`), and nothing else: the
target's proof below is literally
`coorFibre_fibreGenerator_of_keyLocalData k hk (Work.ThomBordism.keyLocal k hk)`, so it becomes
axiom-clean the moment `Work.ThomBordism.keyLocal` (in `Submission/Work/ThomBordism/keyLocal.lean`,
being proved in parallel) is `sorry`-free.  Note also the reduction
`keyLocalData_of_witness' : KeyLocalWitness k hk → KeyLocalData k hk`: by
`admissibleUnique` (from the PROVED `kronH_fund_injective_top`, i.e. Poincaré duality in degree `8`)
it suffices to prove the local comparison for **one** admissible class per datum — the witness form,
which is strictly weaker than KL (see `NOTE_L2678_ALG_and_KL_necessity.md`).

## What is also proved here (all axiom-clean)

* `coorFibre_fibreGenerator_of_uniformF2` — the *uniform fibre reading* UF2 implies the target (the
  reduction that shows nothing specific to the pinned `z` is missing).
* `coorFibre_eq_of_normalData` — `coorFibre` does not depend on the normal datum `ND`, so the
  target's `∀ ND` is redundant.
* `isLocalDegreeClass_eq_of_tubeData` — the local-degree class is *intrinsic* (`collapseRelK8` is
  independent of the tube data: `collapseRelK8_indep_tube`), so the target's `∀ (ε, C, q, hU, R, hR,
  hbox, g, hg, hg2)` is redundant.
* `nfPunctPush` and `nfRes_relKronH` — the pairing form of the localisation,
  `⟨nfRes U, z⟩ = ⟨U, nfPunctPush z⟩`, the tool that turns the target's pin into an identity about
  the classes themselves.

## Earlier rounds (recorded for the reader)

The previous route traded the target against `Work.ThomBordism.AmbientFibreLink` (equivalent to it,
hence circular); that section has been *deleted* from this file, as the project lead directed.  The
`AmbientUniform` form of the `κ`-chapter is re-derived here as `ambientPairing_uniform` so that this
file does not import `Submission/Work/ThomBordism/ambientFibreComparison.lean`.
-/

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

variable {V : Work.ThomBordism.Man8}

/-- **UF2 implies the target.**

If there is a single `t = ± 1` such that the fibre reading of *every* local-degree class is `t` times
the oriented fibre generator `nfGen` (the project's uniform fibre-restriction statement UF2,
`Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen_uniform`), then
`Work.ThomBordism.coorFibre_fibreGenerator` holds with that same `t` (transported to `coorFibre`
through `Work.ThomBordism.exists_coorFibre_eq_smul_nfGen`).

Proof: on any configuration satisfying the hypotheses, let `U₀` be the generating local-degree class
(`localDegreeGenExists`); the pin gives `⟨nfRes U₀, z⟩ = ⟨zs^*w, V.c⟩ = 1`, while
`nfRes U₀ = t • nfGen = (t·ε) • coorFibre`; since `t·ε = ±1`, the claim follows. -/
theorem coorFibre_fibreGenerator_of_uniformF2 (k : ℕ) (hk : 1 ≤ k)
    (hF2u : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
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
          (Work.Tubular.normalNonzero E)),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
        ∀ x : V.pt, Work.ThomBordism.nfRes E x k U = t • Work.ThomBordism.nfGen hk E ND x) :
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
            (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.coorFibre hk E ND x) z
          = t := by
  classical
  obtain ⟨t, htm, hF2⟩ := hF2u
  obtain ⟨εm, hεm, hconv⟩ := Work.ThomBordism.exists_coorFibre_eq_smul_nfGen (k := k) hk
  have htmul : t * εm = 1 ∨ t * εm = -1 := by
    rcases htm with h | h <;> rcases hεm with h' | h' <;> rw [h, h'] <;> norm_num
  refine ⟨t * εm, htmul, ?_⟩
  intro V _ E ND ε C q hU R hR hbox g hg hg2 x w z hw hspan hpin
  obtain ⟨U₀, hU₀span, hU₀ild⟩ :=
    Work.ThomBordism.localDegreeGenExists (V := V) (k := k) hk E C.eps_pos C q hU hR
      (fun y hy j => by simpa using hbox y hy j) g hg hg2
  have h1 : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U₀) z = 1 := by
    rw [hpin U₀, hU₀ild w, hw]
  have hng : Work.ThomBordism.nfGen hk E ND x
      = εm • Work.ThomBordism.coorFibre hk E ND x := by
    have h2' : εm * εm = 1 := by rcases hεm with h | h <;> rw [h] <;> norm_num
    calc Work.ThomBordism.nfGen hk E ND x
        = (1 : ℤ) • Work.ThomBordism.nfGen hk E ND x := (one_smul _ _).symm
      _ = (εm * εm) • Work.ThomBordism.nfGen hk E ND x := by rw [h2']
      _ = εm • (εm • Work.ThomBordism.nfGen hk E ND x) := by rw [smul_smul]
      _ = εm • Work.ThomBordism.coorFibre hk E ND x := by rw [← hconv E ND x]
  rcases htmul with h | h
  · have hsm : t • (εm • Work.ThomBordism.coorFibre hk E ND x)
        = (t * εm) • Work.ThomBordism.coorFibre hk E ND x := (smul_smul t εm _)
    have h2' : Work.ThomBordism.nfRes E x k U₀ = Work.ThomBordism.coorFibre hk E ND x := by
      rw [hF2 E ND C q hU hR hbox g hg hg2 U₀ hU₀ild x, hng, hsm, h, one_smul]
    rw [h2'] at h1
    rw [h]
    exact h1
  · have hsm : t • (εm • Work.ThomBordism.coorFibre hk E ND x)
        = (t * εm) • Work.ThomBordism.coorFibre hk E ND x := (smul_smul t εm _)
    have h2' : Work.ThomBordism.nfRes E x k U₀ = - Work.ThomBordism.coorFibre hk E ND x := by
      rw [hF2 E ND C q hU hR hbox g hg hg2 U₀ hU₀ild x, hng, hsm, h]
      simp
    simp only [h2', map_neg, LinearMap.neg_apply] at h1
    have hv : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.coorFibre hk E ND x) z = -1 := by
      linarith
    rw [h, hv]

/-- **`coorFibre` does not depend on the normal datum.**

For two normal data `ND`, `ND'` of the same embedding, *pinned* Gauss candidates `G`, `G'`
(`hbp`/`hvec` as in `gtdGaussCandidate`), the classes `coorFibre hk E ND x` and
`coorFibre hk E ND' x` agree.

Proof: `nfRes` is linear and does not involve `ND`, while
`Work.ThomBordism.gtdUWith_eq_of_normalData` (PROVED) says that the class
`gtdU E ND G hgm = gtdUWith E ND G hgm (tautologicalThomClass k 10)` is the *same* for `ND` and `ND'`.
Its fibre reading is `s • nfGen` with a *uniform* `s` (`fibreRes_gtdU_canonical`, PROVED) and
`nfGen = ε • coorFibre` with a *uniform* `ε` (`exists_coorFibre_eq_smul_nfGen`, PROVED), whence
`s ε • coorFibre hk E ND x = s ε • coorFibre hk E ND' x`, and `s ε = ±1`. -/
theorem coorFibre_eq_of_normalData {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND ND' : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (G' : C((Work.Tubular.normalBundle E ND').TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm' : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND'),
      G' p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp' : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G' p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND' p.1)
    (hvec' : ∀ p, Work.ThomBordism.Grassmann.evalVec (G' p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND' p)))
    (x : V.pt) :
    Work.ThomBordism.coorFibre hk E ND x = Work.ThomBordism.coorFibre hk E ND' x := by
  classical
  obtain ⟨s, _hs, hF1⟩ := Work.ThomBordism.fibreRes_gtdU_canonical (k := k) hk
  obtain ⟨ε, hε, hconv⟩ := Work.ThomBordism.exists_coorFibre_eq_smul_nfGen (k := k) hk
  have hng : ∀ (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt),
      Work.ThomBordism.nfGen hk E ND x = ε • Work.ThomBordism.coorFibre hk E ND x := by
    intro ND x
    have h2' : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    calc Work.ThomBordism.nfGen hk E ND x
        = (1 : ℤ) • Work.ThomBordism.nfGen hk E ND x := (one_smul _ _).symm
      _ = (ε * ε) • Work.ThomBordism.nfGen hk E ND x := by rw [h2']
      _ = ε • (ε • Work.ThomBordism.nfGen hk E ND x) := by rw [smul_smul]
      _ = ε • Work.ThomBordism.coorFibre hk E ND x := by rw [← hconv E ND x]
  have hcls : Work.ThomBordism.gtdU E ND G hgm = Work.ThomBordism.gtdU E ND' G' hgm' := by
    rw [Work.ThomBordism.gtdU_eq_gtdUWith E ND G hgm,
        Work.ThomBordism.gtdU_eq_gtdUWith E ND' G' hgm']
    exact Work.ThomBordism.gtdUWith_eq_of_normalData E ND ND' G hgm hbp hvec G' hgm' hbp' hvec'
      (Work.ThomBordism.Grassmann.tautologicalThomClass k 10)
  have h1 : Work.ThomBordism.nfRes E x k (Work.ThomBordism.gtdU E ND G hgm)
      = (s * ε) • Work.ThomBordism.coorFibre hk E ND x := by
    rw [hF1 E ND G hgm hbp hvec x, hng ND x, smul_smul]
  have h2 : Work.ThomBordism.nfRes E x k (Work.ThomBordism.gtdU E ND' G' hgm')
      = (s * ε) • Work.ThomBordism.coorFibre hk E ND' x := by
    rw [hF1 E ND' G' hgm' hbp' hvec' x, hng ND' x, smul_smul]
  rw [hcls] at h1
  have h3 : (s * ε) • Work.ThomBordism.coorFibre hk E ND x
      = (s * ε) • Work.ThomBordism.coorFibre hk E ND' x := h1.symm.trans h2
  have hse : s * ε = 1 ∨ s * ε = -1 := by
    rcases _hs with h | h <;> rcases hε with h' | h' <;> rw [h, h'] <;> norm_num
  rcases hse with h | h
  · simpa [h] using h3
  · rw [h] at h3
    exact neg_injective (by simpa using h3)

/-- **The local-degree class is intrinsic: it does not depend on the tube data.**

`Work.ThomBordism.collapseRelK8_indep_tube` (PROVED) says that the collapse class is the same for
*every* choice of tube chart, radius and collapse map.  Hence two generating local-degree classes of
the same embedding (one for each choice of tube data) satisfy the *same* local-degree identity, and
`Work.ThomBordism.isLocalDegreeClass_eq_of_generating` (uniqueness, from the separating functional
`exists_kronH_zeroSection_fund_ne_zero`) makes them equal.

Consequence for the target: the fibre reading `nfRes E x k U` of the local-degree class — hence the
sign `δ` of this file's header — depends on `(V, E, x)` only, not on the tube data; so the target's
`∀` over `(ε, C, q, hU, R, hR, hbox, g, hg, hg2)` is redundant. -/
theorem isLocalDegreeClass_eq_of_tubeData {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    {ε ε' : ℝ} {C : Work.Tubular.TubeChart E ε} {C' : Work.Tubular.TubeChart E ε'}
    (q : Work.Tubular.NormalSphSub E ε) (q' : Work.Tubular.NormalSphSub E ε')
    (hU : IsCompact C.U) (hU' : IsCompact C'.U) {R R' : ℝ} (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (hbox' : ∀ y ∈ C'.U, ∀ j : Fin (8 + k), |y j| < R')
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (g' : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg' : ∀ y, y ∉ C'.openTube → g' (OnePoint.some y) = OnePoint.infty)
    (hg2' : ∀ y, y ∈ C'.openTube →
      g' (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C'.inv y)))
    {U U' : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)}
    (hUld : Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U)
    (hspan : Submodule.span ℤ ({U} : Set _) = ⊤)
    (hUld' : Work.ThomBordism.IsLocalDegreeClass C' g' hg' hR' hbox' U')
    (hspan' : Submodule.span ℤ ({U'} : Set _) = ⊤) :
    U = U' := by
  have hc : Work.Tubular.collapseRelK8 C g hg hR hbox
      = Work.Tubular.collapseRelK8 C' g' hg' hR' hbox' :=
    Work.ThomBordism.collapseRelK8_indep_tube C C' g hg hg2 g' hg' hg2' hR hR' hbox hbox'
  have hUld'' : Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U' := by
    intro x
    have h := hUld' x
    rw [← hc] at h
    exact h
  exact (Work.ThomBordism.isLocalDegreeClass_eq_of_generating (V := V) (k := k) (E := E)
    (C := C) q hR hbox g hg hg2 hspan hUld hUld'').symm

/-! ## The push-forward of a fibre class into the Thom pair, and the localisation of the pairing

`Work.ThomBordism.FrameSigns.relKronH_natural` (PROVED) is the naturality of the relative Kronecker
pairing along a map of pairs.  Its specialisation to the inclusion `nfIncl E x` of the fibre pair
`(ν_x, ν_x∖0)` into the Thom pair `(ν, ν∖0)` is the *pairing form* of the localisation of the fibre
reading:

  `⟨nfRes E x k U, z⟩_{ν_x} = ⟨U, nfPunctPush E x z⟩_{ν, ν∖0}`,

i.e. the fibre reading of `U` pairs with `z` exactly as `U` pairs with the *push-forward* of `z` into
the total space.  This is the tool that turns the pin of the target's hypotheses (an identity about
`nfRes`) into an identity about the classes `U` themselves. -/

/-- **The push-forward of a fibre homology class into the Thom pair of the normal bundle**: the map
on relative homology induced by the inclusion `nfIncl E x` of the fibre pair over `x`. -/
noncomputable def nfPunctPush {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x)).homology k →ₗ[ℤ]
      (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)).homology k :=
  (HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMapOf (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.ThomBordism.nfPunct E x)
      (Work.Tubular.normalNonzero E) (TopCat.ofHom (Work.ThomBordism.nfIncl E x))
      (TopCat.ofHom ⟨fun a => ⟨Work.ThomBordism.nfIncl E x a.1,
          Work.ThomBordism.nfIncl_mem E x a.1 a.2⟩,
        Continuous.subtype_mk ((Work.ThomBordism.nfIncl E x).continuous.comp
          continuous_subtype_val) (fun a => Work.ThomBordism.nfIncl_mem E x a.1 a.2)⟩)
      (by apply TopCat.hom_ext; rfl)) k).hom

/-- **The localisation of the relative Kronecker pairing to the fibre.**  For a class `U` of the
Thom pair of the normal bundle and a class `z` of the fibre pair of the normal bundle over `x`:

  `⟨nfRes E x k U, z⟩ = ⟨U, nfPunctPush E x z⟩`.

This is the naturality of `Work.Tubular.relKronH` along the inclusion of the fibre pair, with the
definitional unfolding of `Work.ThomBordism.nfRes`. -/
theorem nfRes_relKronH {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E))
    (z : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
      (Work.ThomBordism.nfPunct E x)).homology k) :
    Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U) z
      = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) k U (nfPunctPush E x z) := by
  have h := Work.ThomBordism.FrameSigns.relKronH_natural
    (Work.ThomBordism.nfIncl E x) (Work.ThomBordism.nfIncl_mem E x) k U z
  rw [nfPunctPush]
  exact h


/-! ## The key local statement, and the target from it

`KeyLocalData k hk` (below) is the *local comparison*

  `π^*(w) ⌣ Ucan = s • (the ambient chart model class)`   (`s = ±1` a single sign over all data),

for every degree-`8` class `w` of the normal total space with `⟨(zeroSection)^* w, V.c⟩ = 1`, where
`Ucan` is the canonical (chart-constructed) Thom class of the tautological *oriented* bundle.  It is
the project lead's (KL) (`Work.ThomBordism.KeyLocal` of `Submission/Work/ThomBordism/keyLocal.lean`,
whose proof is being written in parallel), with the ambient chart model class written out: by
definition `ambientValueClass E C x` *is* `chartModelClass E C x (continuous_chartAffine_cap E C x)`,
so the two statements are definitionally equal, and this file depends only on stable modules.

The target follows by the project lead's (ALG) step.  On a datum satisfying the target's hypotheses,
apply the pin at `U := Ucan`; the fibre reading of `Ucan` is the coorientation reference `coorFibre`
by the PROVED `nfRes_gtdUWith_realThomClassOf_eq_coorFibre` (whose frame input is the PROVED
`frameEval_realThomClassOf`), so

  `⟨coorFibre, z⟩ = ⟨nfRes Ucan, z⟩ = ⟨w ⌣ Ucan, c⟩ = s · ⟨(ambient chart model class), c⟩ = s · κ`,

where `κ` is the *uniform* ambient local degree of the collapse class (`ambientPairing_uniform`
below, from the PROVED `collapseLocalisation_ambientV2` and `value_eq_chartModelClass`).  No
`AmbientFibreLink` is involved — that statement was only ever equivalent to the target. -/

/-- **The key local statement (KL)** (the project lead's probe 48), in the ambient-chart form: for
every datum and every degree-`8` class `w` with `⟨(zeroSection)^* w, V.c⟩ = 1`, the cup product of `w`
with the canonical Thom class `Ucan` is a *single* sign `s = ± 1` (the same for all data) times the
ambient chart model class. -/
def KeyLocalData (k : ℕ) (hk : 1 ≤ k) : Prop :=
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
        = s • Work.ThomBordism.chartModelClass E C x
            (Work.ThomBordism.continuous_chartAffine_cap E C x)

/-- **The `κ`-chapter in chart-model form**: the ambient local degree
`⟨(ambient chart model class), collapseRelK8⟩` of the collapse class is a single `κ = ±1` over all
data.  This is the PROVED `Work.ThomBordism.collapseLocalisation_ambientV2` combined with the PROVED
`Work.ThomBordism.value_eq_chartModelClass` (which identifies the ambient standard class with the
chart model class). -/
theorem ambientPairing_uniform (k : ℕ) (hk : 1 ≤ k) :
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
            ((Nat.add_comm 8 k) ▸ Work.ThomBordism.chartModelClass E C x
              (Work.ThomBordism.continuous_chartAffine_cap E C x))
            (Work.Tubular.collapseRelK8 C g hg hR hbox) = κ := by
  obtain ⟨κ, hκ, hcl⟩ := Work.ThomBordism.collapseLocalisation_ambientV2 k hk
  refine ⟨κ, hκ, ?_⟩
  intro V _inst E ε C q hU R hR hbox g hg hg2 x
  obtain ⟨δ, hδ⟩ :=
    Work.ThomBordism.tubeInvHomologyCollapse (V := V) (k := k) E C g hg hg2 hR hbox
  exact (Work.ThomBordism.value_eq_chartModelClass E C g hg hR hbox x
      (Work.ThomBordism.continuous_chartAffine_cap E C x) δ hδ).symm.trans
    (hcl E C g hg hg2 hR hbox x δ hδ)

/-- **The witness form of (KL)**: for every datum there is *some* degree-`8` class `w` of the normal
total space, admissible (`⟨zs^* w, V.c⟩ = 1`), for which the cup product with the canonical Thom
class is the single sign `s` times the ambient chart model class.

This is strictly weaker than `KeyLocalData` (an `∃` per datum instead of a `∀`), and it is the form
of the local comparison that the geometric argument (the project lead's (ii)–(v): the collapse read
on the chart, the product neighbourhood, the frame comparison) naturally proves: one computes the
identity for the *bump* class `π^*(o_x)`. -/
def KeyLocalWitness (k : ℕ) (hk : 1 ≤ k) : Prop :=
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
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt),
      ∃ w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
        Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 ∧
        Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w
            (Work.ThomBordism.gtdUWith E ND G hgm
              (Work.Thom.realThomClassOf hk
                (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.tautologicalBundle_horiO k)))
          = s • Work.ThomBordism.chartModelClass E C x
              (Work.ThomBordism.continuous_chartAffine_cap E C x)

/-- **The `w`-uniqueness hypothesis**: the admissibility condition `⟨zs^* w, V.c⟩ = 1` pins a
degree-`8` class of the normal total space uniquely.  This is the lead's plan-(i) input; it follows
from the injectivity of the top-degree pairing with the fundamental class
(`Work.ThomBordism.kronH_fund_injective_top`, delegated) because the zero section `zs : V → ν` is a
homotopy equivalence (the radial contraction `zs ∘ π ≃ 𝟙`), so `zs^*` is injective. -/
def AdmissibleUnique (k : ℕ) : Prop :=
  ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (w w' : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E))),
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 →
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w') V.c = 1 →
    w = w'

/-- **(KL) from the witness form plus the uniqueness of the admissible class.**

This is the lead's plan (i) as a formal reduction: it suffices to prove the local comparison for
**one** admissible class per datum, because admissibility pins that class. -/
theorem keyLocalData_of_witness (k : ℕ) (hk : 1 ≤ k)
    (huniq : AdmissibleUnique k) (hwit : KeyLocalWitness k hk) : KeyLocalData k hk := by
  obtain ⟨s, hs, hwit'⟩ := hwit
  refine ⟨s, hs, ?_⟩
  intro V _inst E ND G hgm hbp hvec ε C x w hw
  obtain ⟨w₀, hw₀adm, hw₀⟩ := hwit' E ND G hgm hbp hvec C x
  rw [huniq E w w₀ hw hw₀adm, hw₀]

/-! ## The uniqueness of the admissible degree-`8` class

The admissibility condition `⟨zs^* w, V.c⟩ = 1` pins `w`.  The mechanism is: the zero section
`zs : V → ν` is a homotopy equivalence (the **radial contraction** of the normal bundle), so
`zs^* : H⁸(ν) → H⁸(V)` is injective; hence it suffices that `zs^* (w - w') = 0`, and that follows
from the injectivity of the top-degree pairing with the fundamental class
(`Work.ThomBordism.kronH_fund_injective_top`, the Poincaré-duality input, delegated). -/

/-- The **radial contraction** of the normal total space onto its zero section, as a homotopy
`zs ∘ π ≃ 𝟙`. -/
noncomputable def radialHomotopy {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    TopCat.Homotopy
      (TopCat.ofHom (⟨Work.Tubular.NormalTotal.proj,
          Work.Tubular.NormalTotal.continuous_proj E⟩ :
            C(Work.Tubular.NormalTotal E, V.pt))
        ≫ TopCat.ofHom (Work.Tubular.zeroSectionNormal E))
      (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) where
  toFun := fun q : ↥(Set.Icc (0 : ℝ) 1) × Work.Tubular.NormalTotal E =>
      Work.ThomBordism.radialRescale E (fun _ => (q.1 : ℝ)) q.2
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    show Continuous fun q : ↥(Set.Icc (0 : ℝ) 1) × Work.Tubular.NormalTotal E =>
      (((q.2 : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1,
        (q.1 : ℝ) • ((q.2 : Work.Tubular.NormalTotal E) :
          V.pt × Work.Tubular.Euc (8 + k)).2)
    exact Continuous.prodMk
      ((continuous_subtype_val.comp continuous_snd).fst)
      ((continuous_subtype_val.comp continuous_fst).smul
        ((continuous_subtype_val.comp continuous_snd).snd))
  map_zero_left := by
    intro p
    apply Work.Tubular.NormalTotal.ext
    show (((Work.ThomBordism.radialRescale E
        (fun _ => ((0 : ↥(Set.Icc (0 : ℝ) 1)) : ℝ)) p :
        Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)))
      = ((Work.Tubular.zeroSectionNormal E (Work.Tubular.NormalTotal.proj p) :
        Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k))
    rw [Work.ThomBordism.radialRescale_coe, Work.Tubular.zeroSectionNormal_apply]
    refine Prod.ext rfl ?_
    simp
  map_one_left := by
    intro p
    apply Work.Tubular.NormalTotal.ext
    show (((Work.ThomBordism.radialRescale E
        (fun _ => ((1 : ↥(Set.Icc (0 : ℝ) 1)) : ℝ)) p :
        Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)))
      = ((p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k))
    rw [Work.ThomBordism.radialRescale_coe]
    refine Prod.ext rfl ?_
    simp

/-- **The admissible class is unique**, from the injectivity of the top-degree pairing with the
fundamental class (`Work.ThomBordism.kronH_fund_injective_top`). -/
theorem admissibleUnique_of_injective (k : ℕ)
    (hinj : ∀ {V : Work.ThomBordism.Man8} [PathConnectedSpace V.pt],
      ∀ u : Work.Thom.Coh ℤ 8 (TopCat.of V.pt),
        Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8 u V.c = 0 → u = 0) :
    AdmissibleUnique k := by
  intro V _inst E w w' hw hw'
  haveI : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  -- the zero section as a morphism, and the projection
  let zs : TopCat.of V.pt ⟶ TopCat.of (Work.Tubular.NormalTotal E) :=
    TopCat.ofHom (Work.Tubular.zeroSectionNormal E)
  let pr : TopCat.of (Work.Tubular.NormalTotal E) ⟶ TopCat.of V.pt :=
    TopCat.ofHom ⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩
  -- `zs` is a homotopy equivalence, hence `zs^*` is injective
  have hrefl : TopCat.Homotopy (zs ≫ pr) (𝟙 (TopCat.of V.pt)) := by
    have hzug : zs ≫ pr = 𝟙 (TopCat.of V.pt) := by
      apply TopCat.ext
      intro x
      exact Work.Tubular.zeroSectionNormal_proj E x
    rw [hzug]
    exact TopCat.Homotopy.refl _
  have hrad : TopCat.Homotopy (pr ≫ zs) (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) :=
    radialHomotopy E
  have hiso := Work.Cohomology.homotopyEquiv ℤ (TopCat.of V.pt)
    (TopCat.of (Work.Tubular.NormalTotal E)) zs pr hrefl hrad 8
  have hinjzs : Function.Injective
      ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom) := by
    intro x y hxy
    have hz : (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hleft : ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8)
        ≫ CategoryTheory.inv (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8))
        = 𝟙 _ := IsIso.hom_inv_id _
    have hx : x - y = 0 := by
      have h2 := congrArg (fun φ => φ.hom (x - y)) hleft
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero] at h2
      exact h2.symm
    exact sub_eq_zero.mp hx
  -- the difference has vanishing pairing with `V.c`
  have hpair : Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
      ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom (w - w')) V.c = 0 := by
    have hA : (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom (w - w')
        = (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w
          - (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w' :=
      map_sub _ w w'
    have hB : (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8)
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w
            - (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w')
        = (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8)
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w)
          - (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8)
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w') :=
      map_sub _ _ _
    rw [hA, hB, LinearMap.sub_apply, hw, hw', sub_self]
  have hzero : (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom (w - w') = 0 :=
    hinj _ hpair
  have hsame : (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom (w - w')
      = (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom 0 := by
    rw [hzero, map_zero]
  exact sub_eq_zero.mp (hinjzs hsame)

/-- **The admissible class is unique** — unconditional, from the PROVED top-degree injectivity
`Work.ThomBordism.kronH_fund_injective_top` (Poincaré duality in degree `8` for a `Man8`). -/
theorem admissibleUnique (k : ℕ) : AdmissibleUnique k :=
  admissibleUnique_of_injective k
    (fun {V} _ => Work.ThomBordism.kronH_fund_injective_top V)

/-- **(KL) from its witness form** — unconditional: by `admissibleUnique` it suffices to prove the
local comparison for *one* admissible class per datum. -/
theorem keyLocalData_of_witness' (k : ℕ) (hk : 1 ≤ k) (hwit : KeyLocalWitness k hk) :
    KeyLocalData k hk :=
  keyLocalData_of_witness k hk (admissibleUnique k) hwit

/-- **The scalar action commutes with a degree cast of a relative cohomology class.** -/
theorem zsmul_cast_relCoh {m n : ℕ} (h : m = n) {X : TopCat} {A : Set X} (s : ℤ)
    (x : Work.Thom.RelCoh ℤ m X A) :
    (h ▸ (s • x) : Work.Thom.RelCoh ℤ n X A) = s • (h ▸ x : Work.Thom.RelCoh ℤ n X A) := by
  cases h
  rfl

/-- **The target from (KL).** -/
theorem coorFibre_fibreGenerator_of_keyLocalData (k : ℕ) (hk : 1 ≤ k)
    (hKL : KeyLocalData k hk) :
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
            (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.coorFibre hk E ND x) z
          = t := by
  classical
  obtain ⟨κ, hκ, hA⟩ := ambientPairing_uniform k hk
  obtain ⟨s, hs, hKL'⟩ := hKL
  refine ⟨s * κ, ?_, ?_⟩
  · rcases hs with h | h <;> rcases hκ with h' | h' <;> rw [h, h'] <;> norm_num
  · intro V _inst E ND ε C q hU R hR hbox g hg hg2 x w z hw hspan hpin
    -- the Gauss/classifying candidate of the datum
    obtain ⟨G, hbp, hvec, hgm, -⟩ :=
      Work.ThomBordism.gtdGaussCandidate E ND C.eps_pos C q hU hR hbox g hg hg2
    -- the canonical class
    set Ucan := Work.ThomBordism.gtdUWith E ND G hgm
      (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.tautologicalBundle_horiO k)) with hUcan
    -- its fibre reading is the coorientation reference
    have hcoor : Work.ThomBordism.nfRes E x k Ucan = Work.ThomBordism.coorFibre hk E ND x :=
      Work.ThomBordism.nfRes_gtdUWith_realThomClassOf_eq_coorFibre hk
        (Work.ThomBordism.tautologicalBundle_horiO k)
        (Work.ThomBordism.frameEval_realThomClassOf k hk
          (Work.ThomBordism.tautologicalBundle_horiO k)) E ND G hgm hbp hvec x
    -- the pin at `Ucan`, and (KL) at `w`
    have hpinU := hpin Ucan
    have hstep : Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w Ucan))
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = s * κ := by
      rw [hKL' E ND G hgm hbp hvec C x w hw, zsmul_cast_relCoh, map_zsmul,
        LinearMap.smul_apply, hA E C q hU hR hbox g hg hg2 x, smul_eq_mul]
    rw [← hcoor, hpinU]
    exact hstep


end

end Work.ThomBordism
