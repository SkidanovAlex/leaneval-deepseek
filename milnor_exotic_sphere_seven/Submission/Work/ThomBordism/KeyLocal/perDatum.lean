import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeCompareDefs
import Submission.Work.ThomBordism.KeyLocal.mixedCupLift
import Submission.Work.ThomBordism.KeyLocal.exists_admissible
import Submission.Work.ThomBordism.KeyLocal.admissible_pi_relToAbs
import Submission.Work.ThomBordism.coorFibre_fibreGeneratorAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

/-- **The per-datum comparison at an admissible tangential class.**

The hypothesis `hT : TubePointRelativeAll k hk` is the tube-level point-relative comparison: the
pullback along the tube inverse of the relative–relative cup of `π^*(o)` (with `o` a class of
`H⁸(V, V∖{x})` dual to the local fundamental class) with the canonical Thom class is `tauSign`
times the translation reading of the standard model class.

The proof is the final bookkeeping step of the last mile.  The admissible class `w` of the normal
total space is unique (`Work.ThomBordism.admissibleUnique`), so it suffices to treat the *bump*
class `w₀ := π^*((relToAbs).hom o)` of the PROVED `exists_admissible` (`admissiblePi` says `w₀` is
admissible: `Work.ThomBordism.KeyLocal.admissible_pi_relToAbs`).  For `w₀`, the PROVED
`Work.ThomBordism.KeyLocal.mixedCup_restrict_relRelCup` identifies `mixedCup 8 k w₀ Ucan` with the
restriction of the relative–relative cup to the zero-section-relative pair, and the remaining steps
are functoriality of `Work.Thom.relCohMap` (`relCohMap_compA_apply`, `relCohMap_congrA_apply`) along
the identity maps of pairs that compare the two relative sets:
`tubeInvPunct ⊆ tubeFootPunctCU ∪ tubeInvPunct` on the tube and
`normalNonzero ⊆ normalPunctAt x ∪ normalNonzero` on the normal bundle.  The `rfl`-identities
`(id) ∘ tubeInvMap = tubeInvMap` and `translation ∘ id = translation` absorb the two identities,
and the final term is exactly the definition of `Work.ThomBordism.ambientStandardClass`. -/
theorem perDatum {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ} (hk : 1 ≤ k)
    (hT : TubePointRelativeAll k hk)
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
    (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)))
    (hw : Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1) :
    (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
        (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
        (Work.ThomBordism.KeyLocal.tubeInvPunct_mem_normalNonzero E C) ℤ (8 + k)).hom
      (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) 8 k w
        (Work.ThomBordism.gtdUWith E ND G hgm
          (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.tautologicalBundle_horiO k))))
    = Work.ThomBordism.KeyLocal.tauSign • Work.ThomBordism.ambientStandardClass E C x := by
  classical
  -- the admissible class in `H⁸(ν)` is unique, so it suffices to treat the bump class
  -- `w₀ = π^*(relToAbs o)` produced by `exists_admissible`
  obtain ⟨o, ho⟩ := exists_admissible x
  set Ucan : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (Work.Tubular.normalNonzero E) :=
    Work.ThomBordism.gtdUWith E ND G hgm
      (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.tautologicalBundle_horiO k)) with hUcan
  set w₀ : Work.Thom.Coh ℤ 8 (TopCat.of (NormalTotal E)) :=
    (Work.Thom.CohMap (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ :
      C(NormalTotal E, V.pt)) ℤ 8).hom
      ((Work.Thom.relToAbs ℤ (FrameSigns.punct V x) 8).hom o) with hw₀
  have hw₀adm : Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
      ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w₀) V.c = 1 :=
    admissible_pi_relToAbs E x o ho
  rw [Work.ThomBordism.admissibleUnique k (V := V) E w w₀ hw hw₀adm]
  -- the point-relative comparison at `o` (the hypothesis `hT`)
  have hT' := hT E ND G hgm hbp hvec C x o ho
  -- the mixed cup is the restriction of the relative–relative cup
  have hstep1 : Work.Cohomology.mixedCup (TopCat.of (NormalTotal E))
        (Work.Tubular.normalNonzero E) 8 k w₀ Ucan
      = (Work.Thom.relCohMap (ContinuousMap.id (NormalTotal E)) (Work.Tubular.normalNonzero E)
          (normalPunctAt E x ∪ normalNonzero E) (fun z hz => Or.inr hz) ℤ (8 + k)).hom
        (Work.Whitney.relRelCupOpen (normalPunctAt E x) (normalNonzero E)
          (isOpen_normalPunctAt E x) (isOpen_normalNonzero E) 8 k
          ((Work.Thom.relCohMap (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ :
              C(NormalTotal E, V.pt)) (normalPunctAt E x) (FrameSigns.punct V x)
            (fun p hp => hp) ℤ 8).hom o) Ucan) := by
    rw [hw₀, hUcan]
    exact (mixedCup_restrict_relRelCup E x o Ucan).symm
  rw [hstep1]
  -- ## abbreviations (all definitional)
  let f : C(↥C.U, NormalTotal E) := Work.ThomBordism.tubeInvMap E C
  let idU : C(↥C.U, ↥C.U) := ContinuousMap.id ↥C.U
  let idN : C(NormalTotal E, NormalTotal E) := ContinuousMap.id (NormalTotal E)
  let tr : C(↥C.U, Work.Tubular.Euc (8 + k)) :=
    ⟨fun y : ↥C.U => (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩
  let A1 : Set ↥C.U := Work.ThomBordism.tubeInvPunct E C
  let A2 : Set ↥C.U := tubeFootPunctCU E C x ∪ Work.ThomBordism.tubeInvPunct E C
  let B1 : Set (NormalTotal E) := Work.Tubular.normalNonzero E
  let B2 : Set (NormalTotal E) := normalPunctAt E x ∪ normalNonzero E
  let P0 : Set (Work.Tubular.Euc (8 + k)) := {0}ᶜ
  let Ψ : Work.Thom.RelCoh ℤ (8 + k) (NormalTotal E) B2 :=
    Work.Whitney.relRelCupOpen (normalPunctAt E x) (normalNonzero E)
      (isOpen_normalPunctAt E x) (isOpen_normalNonzero E) 8 k
      ((Work.Thom.relCohMap (⟨NormalTotal.proj, NormalTotal.continuous_proj E⟩ :
          C(NormalTotal E, V.pt)) (normalPunctAt E x) (FrameSigns.punct V x)
        (fun p hp => hp) ℤ 8).hom o) Ucan
  -- ## the membership data
  have h1 : ∀ z ∈ A1, f z ∈ B1 := fun z hz => hz
  have hU : ∀ z ∈ A1, idU z ∈ A2 := fun z hz => Or.inr hz
  have hd : ∀ z ∈ B1, idN z ∈ B2 := fun z hz => Or.inr hz
  have hAB : ∀ z ∈ A2, f z ∈ B2 := fun z hz => hz
  have h2tr : ∀ z ∈ A2, tr z ∈ P0 := fun z hz => tubePoint_neCU E C x z hz
  have hgfA : ∀ z ∈ A1, idN (f z) ∈ B2 := fun z hz => Or.inr (h1 z hz)
  have hcA : ∀ z ∈ A1, f z ∈ B2 := fun z hz => Or.inr (h1 z hz)
  have hgfB : ∀ z ∈ A1, f (idU z) ∈ B2 := fun z hz => Or.inr (h1 z hz)
  have hcB : ∀ z ∈ A1, f z ∈ B2 := fun z hz => Or.inr (h1 z hz)
  have hgfC : ∀ z ∈ A1, tr (idU z) ∈ P0 := fun z hz => tubePoint_neCU E C x z (Or.inr hz)
  have hcC : ∀ z ∈ A1, tr z ∈ P0 := fun z hz => tubePoint_neCU E C x z (Or.inr hz)
  -- ## the map identities (all definitional)
  have hmapA : idN.comp f = f := rfl
  have hmapB : f.comp idU = f := rfl
  have hmapC : tr.comp idU = tr := rfl
  -- ## the chain of functoriality identities
  have E1 : (Work.Thom.relCohMap f A1 B1 h1 ℤ (8 + k)).hom
        ((Work.Thom.relCohMap idN B1 B2 hd ℤ (8 + k)).hom Ψ)
      = (Work.Thom.relCohMap (idN.comp f) A1 B2 hgfA ℤ (8 + k)).hom Ψ :=
    Work.Thom.relCohMap_compA_apply A1 B1 B2 f idN h1 hd hgfA ℤ (8 + k) Ψ
  have E2 : (Work.Thom.relCohMap (idN.comp f) A1 B2 hgfA ℤ (8 + k)).hom Ψ
      = (Work.Thom.relCohMap f A1 B2 hcA ℤ (8 + k)).hom Ψ :=
    relCohMap_congrA_apply hmapA A1 B2 hgfA hcA ℤ (8 + k) Ψ
  have E3 : (Work.Thom.relCohMap (f.comp idU) A1 B2 hgfB ℤ (8 + k)).hom Ψ
      = (Work.Thom.relCohMap f A1 B2 hcB ℤ (8 + k)).hom Ψ :=
    relCohMap_congrA_apply hmapB A1 B2 hgfB hcB ℤ (8 + k) Ψ
  have E4 : (Work.Thom.relCohMap idU A1 A2 hU ℤ (8 + k)).hom
        ((Work.Thom.relCohMap f A2 B2 hAB ℤ (8 + k)).hom Ψ)
      = (Work.Thom.relCohMap (f.comp idU) A1 B2 hgfB ℤ (8 + k)).hom Ψ :=
    Work.Thom.relCohMap_compA_apply A1 A2 B2 idU f hU hAB hgfB ℤ (8 + k) Ψ
  have E6 : (Work.Thom.relCohMap idU A1 A2 hU ℤ (8 + k)).hom
        ((Work.Thom.relCohMap tr A2 P0 h2tr ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)))
      = (Work.Thom.relCohMap (tr.comp idU) A1 P0 hgfC ℤ (8 + k)).hom
          (Work.ThomBordism.stdModelGen (8 + k)) :=
    Work.Thom.relCohMap_compA_apply A1 A2 P0 idU tr hU h2tr hgfC ℤ (8 + k) _
  have E7 : (Work.Thom.relCohMap (tr.comp idU) A1 P0 hgfC ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))
      = (Work.Thom.relCohMap tr A1 P0 hcC ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) :=
    relCohMap_congrA_apply hmapC A1 P0 hgfC hcC ℤ (8 + k) _
  have E8 : (Work.Thom.relCohMap tr A1 P0 hcC ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k))
      = Work.ThomBordism.ambientStandardClass E C x := rfl
  -- ## the assembly
  calc
    (Work.Thom.relCohMap f A1 B1 h1 ℤ (8 + k)).hom ((Work.Thom.relCohMap idN B1 B2 hd ℤ (8 + k)).hom Ψ)
        = (Work.Thom.relCohMap (idN.comp f) A1 B2 hgfA ℤ (8 + k)).hom Ψ := E1
    _ = (Work.Thom.relCohMap f A1 B2 hcA ℤ (8 + k)).hom Ψ := E2
    _ = (Work.Thom.relCohMap (f.comp idU) A1 B2 hgfB ℤ (8 + k)).hom Ψ := E3.symm
    _ = (Work.Thom.relCohMap idU A1 A2 hU ℤ (8 + k)).hom
          ((Work.Thom.relCohMap f A2 B2 hAB ℤ (8 + k)).hom Ψ) := E4.symm
    _ = (Work.Thom.relCohMap idU A1 A2 hU ℤ (8 + k)).hom
          (tauSign • (Work.Thom.relCohMap tr A2 P0 h2tr ℤ (8 + k)).hom
            (Work.ThomBordism.stdModelGen (8 + k))) := by rw [hT']
    _ = tauSign • (Work.Thom.relCohMap idU A1 A2 hU ℤ (8 + k)).hom
          ((Work.Thom.relCohMap tr A2 P0 h2tr ℤ (8 + k)).hom
            (Work.ThomBordism.stdModelGen (8 + k))) := by rw [map_zsmul]
    _ = tauSign • (Work.Thom.relCohMap (tr.comp idU) A1 P0 hgfC ℤ (8 + k)).hom
          (Work.ThomBordism.stdModelGen (8 + k)) := by rw [E6]
    _ = tauSign • (Work.Thom.relCohMap tr A1 P0 hcC ℤ (8 + k)).hom
          (Work.ThomBordism.stdModelGen (8 + k)) := by rw [E7]
    _ = tauSign • Work.ThomBordism.ambientStandardClass E C x := by rw [E8]

end

end Work.ThomBordism.KeyLocal
