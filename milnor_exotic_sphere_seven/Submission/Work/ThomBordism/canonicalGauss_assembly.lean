import Mathlib
import Submission.Work.ThomBordism.nfGen_span
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.ThomBordism.gtdUWith_frameEval
import Submission.Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.ThomBordism.nfRes_eq_of_span
import Submission.Work.ThomBordism.gtdU_localDegreeExists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Assembly lemmas for `Work.ThomBordism.canonicalGauss_isLocalDegreeClass`

The sharp statement `canonicalGauss_isLocalDegreeClass` is proved from the two *determinate* halves
`(A1-coor)` and `(A2-coor)` of `Submission/Work/ThomBordism/NOTE_CANONICAL_SHARP.md` §3, against the
determinate reference `Work.ThomBordism.coorFibre`:

* `(A1-coor)` — the localisation chapter — `Work.ThomBordism.coorFibre_localDegreeClass`
  (dispatched, child H4-L2668): the fibre reading of *every* local-degree class is `coorFibre`;
* `(A2-coor)` — the frame half — is assembled here from
  `Work.ThomBordism.nfRes_gtdUWith_eq_frameEval` (PROVED in
  `Submission/Work/ThomBordism/gtdUWith_frameEval.lean`: the fibre reading of `gtdUWith U` is the
  frame reading of `U`) and `Work.ThomBordism.canonicalThomClass_frameEval` (dispatched, child
  H4-L2670: `(frameEval σ)^*(realThomClassOf …).τ = stdModelGen k`), using the injectivity of the
  reading pullback proved below.

This file contains the *mechanical* part of that assembly.  The remaining steps, to be added when the
two dispatched lemmas land, are

* `(A2)`: instantiate `canonicalThomClass_frameEval` at `σ := datumFrame E ND x` and apply
  `reading_pullback_injective` (`nfRes_gtdUWith_eq_frameEval` gives exactly the LHS);
* the final step: two elements of the rank-one free module `H^k(ν, ν∖0)` that generate it and have
  equal fibre reading are *equal* — dispatched as `ThomBordism/nfRes_eq_of_span`.  With `(A1-coor)`
  for a generating local-degree class `Ugen` (`Work.ThomBordism.localDegreeGenExists`) this turns
  `nfRes (gtdUWith … Ucan) = nfRes Ugen` into `gtdUWith … Ucan = Ugen`, hence
  `IsLocalDegreeClass` of the canonical class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The reading pullback is injective.**  `Work.ThomBordism.nfRead E ND x` is a bijection of pairs
`(ν_x, ν_x∖0) → (ℝ^k, ℝ^k∖0)` (inverse `Work.ThomBordism.nfInv`, `Work.ThomBordism.nfRead_nfInv` /
`Work.ThomBordism.nfInv_nfRead`), so its pullback on relative cohomology is injective.  The proof
exhibits the left inverse `(relCohMap (nfInv E ND x))`, exactly as
`Work.ThomBordism.nfRead_surjective` exhibits the right one. -/
theorem reading_pullback_injective (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Function.Injective
      (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
        ({0}ᶜ : Set (Work.Tubular.Euc k))
        (fun p hp => nfRead_ne_zero hk E ND x p hp) ℤ k).hom := by
  classical
  have hΦmem : ∀ a ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)), nfInv E ND x a ∈ nfPunct E x :=
    fun a ha => nfInv_mem_nfPunct E ND x a ha
  have hmem : ∀ p ∈ nfPunct E x, nfRead E ND x p ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)) :=
    fun p hp => nfRead_ne_zero hk E ND x p hp
  have hgf : ∀ a ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)),
      nfRead E ND x (nfInv E ND x a) ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)) :=
    fun a ha => hmem _ (hΦmem a ha)
  have hcomp_eq : (nfRead E ND x).comp (nfInv E ND x)
      = ContinuousMap.id (Work.Tubular.Euc k) :=
    ContinuousMap.ext fun a => nfRead_nfInv E ND x a
  have hcomp : Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
        ({0}ᶜ : Set (Work.Tubular.Euc k)) hmem ℤ k
      ≫ Work.Thom.relCohMap (nfInv E ND x) ({0}ᶜ : Set (Work.Tubular.Euc k))
        (nfPunct E x) hΦmem ℤ k
      = 𝟙 (Work.Thom.RelCoh ℤ k (Work.Tubular.Euc k) ({0}ᶜ : Set (Work.Tubular.Euc k))) := by
    rw [Work.Thom.relCohMap_compA (A := ({0}ᶜ : Set (Work.Tubular.Euc k)))
      (B := nfPunct E x) (C := ({0}ᶜ : Set (Work.Tubular.Euc k)))
      (nfInv E ND x) (nfRead E ND x) hΦmem hmem hgf ℤ k]
    exact (Work.Thom.relCohMap_congrA (A := ({0}ᶜ : Set (Work.Tubular.Euc k)))
      (B := ({0}ᶜ : Set (Work.Tubular.Euc k))) hcomp_eq hgf (fun _ h => h) ℤ k).trans
      (Work.Thom.relCohMap_idA ({0}ᶜ : Set (Work.Tubular.Euc k)) ℤ k)
  have hlin : (Work.Thom.relCohMap (nfInv E ND x) ({0}ᶜ : Set (Work.Tubular.Euc k))
        (nfPunct E x) hΦmem ℤ k).hom.comp
      (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
        ({0}ᶜ : Set (Work.Tubular.Euc k)) hmem ℤ k).hom = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom hcomp
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  intro a b hab
  have key : ∀ y, (Work.Thom.relCohMap (nfInv E ND x) ({0}ᶜ : Set (Work.Tubular.Euc k))
      (nfPunct E x) hΦmem ℤ k).hom
      ((Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
        ({0}ᶜ : Set (Work.Tubular.Euc k)) hmem ℤ k).hom y) = y :=
    fun y => LinearMap.congr_fun hlin y
  calc a = (Work.Thom.relCohMap (nfInv E ND x) ({0}ᶜ : Set (Work.Tubular.Euc k))
        (nfPunct E x) hΦmem ℤ k).hom
        ((Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
          ({0}ᶜ : Set (Work.Tubular.Euc k)) hmem ℤ k).hom a) := (key a).symm
    _ = (Work.Thom.relCohMap (nfInv E ND x) ({0}ᶜ : Set (Work.Tubular.Euc k))
        (nfPunct E x) hΦmem ℤ k).hom
        ((Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
          ({0}ᶜ : Set (Work.Tubular.Euc k)) hmem ℤ k).hom b) := by rw [hab]
    _ = b := key b

end

end Work.ThomBordism

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **`(A2-coor)`, the frame half, from the pure frame statement.**  If the pullback of the canonical
Thom class of the tautological bundle along *every* frame evaluation is the determinate model
generator `stdModelGen k` (`Work.ThomBordism.canonicalThomClass_frameEval`), then the fibre reading
of the canonical Gauss candidate is the coorientation reference `coorFibre`. -/
theorem nfRes_gtdUWith_realThomClassOf_eq_coorFibre (hk : 1 ≤ k)
    (horiO : ∀ (i j : ChartIdx k 10)
      (x : ↥((tautologicalBundle k 10).baseSet i ∩ (tautologicalBundle k 10).baseSet j)),
      0 < LinearMap.det (((tautologicalBundle k 10).coordChange i j
        (x : OG k 10)).toLinearMap))
    (hframe : ∀ σ : Stiefel k 10,
      (Work.Thom.relCohMap (frameEvalMap k σ) (framePunct k)
        (Work.Thom.zeroComplement (tautologicalBundle k 10))
        (frameEvalMap_mem k σ) ℤ k).hom
        ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ)
      = stdModelGen k)
    (E : PontryaginThom.EmbeddingData V (8 + k))
    (ND : PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace, (tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
    (hbp : ∀ p, (tautologicalBundle k 10).proj (G p) = Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (x : V.pt) :
    nfRes E x k (gtdUWith E ND G hgm
        (Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO))
      = Work.ThomBordism.coorFibre hk E ND x := by
  rw [nfRes_gtdUWith_eq_frameEval hk E ND G hgm hbp hvec x, hframe (datumFrame E ND x)]
  rfl

end

end Work.ThomBordism


namespace Work.ThomBordism

noncomputable section

/-- **The full assembly of `canonicalGauss_isLocalDegreeClass` from the three determinate inputs.**

`hA1` is the localisation chapter `(A1-coor)`, `hA2` the frame half `(A2-coor)`, and `hspan` the
generator property of the canonical Gauss candidate (the `gtdU_span_top` analogue).  The proof is one
point of `V.pt` and the bookkeeping `nfRes_eq_of_span`: at a single `x : V.pt` both the local-degree
class `Ugen` (from `localDegreeGenExists`) and the canonical class have fibre reading `coorFibre`, so
they are equal, and `gtdUWith … Ucan` inherits `IsLocalDegreeClass` from `Ugen`. -/
theorem canonicalGauss_isLocalDegreeClass_of_coorFibre (k : ℕ) (hk : 1 ≤ k)
    (horiO : ∀ (i j : Work.ThomBordism.Grassmann.ChartIdx k 10)
      (x : ↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet i
        ∩ (Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet j)),
      0 < LinearMap.det (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).coordChange i j
        (x : Work.ThomBordism.Grassmann.OG k 10)).toLinearMap))
    (hA1 : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
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
      Work.ThomBordism.nfRes E x k U = Work.ThomBordism.coorFibre hk E ND x)
    (hA2 : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
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
      (x : V.pt),
      Work.ThomBordism.nfRes E x k (Work.ThomBordism.gtdUWith E ND G hgm
        (Work.Thom.realThomClassOf hk
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10) horiO))
        = Work.ThomBordism.coorFibre hk E ND x)
    (hspan : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
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
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p))),
      Submodule.span ℤ ({(Work.ThomBordism.gtdUWith E ND G hgm
        (Work.Thom.realThomClassOf hk
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10) horiO))} : Set
        (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E))) = ⊤) :
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
      {ε' : ℝ} (C : Work.Tubular.TubeChart E ε') (q : Work.Tubular.NormalSphSub E ε')
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (Work.ThomBordism.gtdUWith E ND G hgm
          (Work.Thom.realThomClassOf hk
            (Work.ThomBordism.Grassmann.tautologicalBundle k 10) horiO)) := by
  intro V _ E ND G hgm hbp hvec ε' C q hU R hR hbox g hg hg2
  obtain ⟨x⟩ := (inferInstance : Nonempty V.pt)
  obtain ⟨Ugen, hUgenspan, hUgenild⟩ :=
    localDegreeGenExists hk E C.eps_pos C q hU hR hbox g hg hg2
  have hUcan : Work.ThomBordism.gtdUWith E ND G hgm
      (Work.Thom.realThomClassOf hk
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10) horiO) = Ugen :=
    Work.ThomBordism.nfRes_eq_of_span hk E ND x (hspan E ND G hgm hbp hvec) hUgenspan
      ((hA2 E ND G hgm hbp hvec x).trans (hA1 E ND C q hU hR hbox g hg hg2 Ugen x hUgenild).symm)
  rw [hUcan]
  exact hUgenild

end

end Work.ThomBordism
