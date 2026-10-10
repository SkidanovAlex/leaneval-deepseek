import Mathlib
import Submission.Work.K3.BaseChangeBirational
import Submission.Work.K3.partialMap_baseChangeAlong_equiv
import Submission.Work.K3.partialIso_baseChangeAlong_symm
import Submission.Work.Motivic.exists_partialIso_toBirationalMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.birationalMap_baseChangeAlong` — base change of a birational map

The descent step of `thm:K3` (see `Work.K3.Descent`) needs the L-link over `𝕜 ⊆ ℂ` to be the base
change of the `ℚ`-model of the link.  `Submission/Work/K3/BaseChange.lean` base changes *schemes*
and *morphisms*, `Submission/Work/K3/BaseChangeBirational.lean` base changes *partial maps*, and
`Submission/Work/K3/partialMap_baseChangeAlong_equiv.lean` /
`Submission/Work/K3/partialIso_baseChangeAlong.lean` show that this is compatible with the
equivalence relation on partial maps and with partial isomorphisms.

This file assembles the resulting base change of a **birational map**: for `f : T ⟶ S` surjective
and universally open, an `S`-birational map `ψ : X ⤏ Y` between irreducible `S`-schemes base
changes to a `T`-birational map `Ψ : X ×_S T ⤏ Y ×_S T`, uniquely characterised by the property
that the base change of any `S`-over partial-map representative of `ψ.hom` (resp. of `ψ.inv`)
represents `Ψ.hom` (resp. `Ψ.inv`).

## Proof

* `Work.Motivic.exists_partialIso_toBirationalMap` produces a partial isomorphism `i` with
  `i.toBirationalMap = ψ`; pick an `S`-over representative `g` of `i.toRationalMap` and restrict
  `i` to a dense open `W` on which `g` and `i.toPartialMap` agree: this produces a partial
  isomorphism `P` which is *over* `S` (`PartialIso.symm_toPartialMap_isOver` and the computation
  `PartialIso.restrictSource_toPartialMap_hom` of the underlying morphism of a source-restriction);
* `Work.K3.partialIso_baseChangeAlong_symm` base changes `P` to a partial isomorphism `h` of the
  base changes whose forward and inverse rational maps are the base changes of those of `P`;
* `h.toBirationalMap` is then the required `Ψ`: it is over `T` because the base-changed partial map
  is (`PartialMap.baseChangeAlong_isOver`), and it is the base change of an *arbitrary* `S`-over
  representative by `Work.K3.partialMap_baseChangeAlong_equiv`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-! ## Restricting the source of a partial isomorphism -/

/-- The morphism underlying `PartialIso.restrictSource` is the restriction of the underlying
morphism. -/
lemma PartialIso.restrictSource_toPartialMap_hom {X Y : Scheme} (f : X.PartialIso Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.source) :
    (f.restrictSource U hU hU').toPartialMap.hom = X.homOfLE hU' ≫ f.toPartialMap.hom := by
  have hcancel : (Opens.isoOfLE hU').inv ≫ (f.source.ι ⁻¹ᵁ U).ι = X.homOfLE hU' := by
    rw [← cancel_mono f.source.ι, Category.assoc, Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  calc (f.restrictSource U hU hU').toPartialMap.hom
      = ((Opens.isoOfLE hU').inv ≫ (f.source.ι ⁻¹ᵁ U).ι) ≫ f.iso.hom ≫ f.target.ι := by
        dsimp only [PartialIso.restrictSource, PartialIso.toPartialMap]
        simp only [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc,
          Hom.isoImage_hom_ι_assoc, Hom.isoImage_hom_ι]
    _ = X.homOfLE hU' ≫ f.toPartialMap.hom := by
        rw [hcancel]
        rfl

/-! ## `PartialIso.IsOver` and its symmetry -/

/-- `PartialIso.IsOver` is the same condition as `PartialMap.IsOver` of the underlying partial
map. -/
lemma partialIso_isOver_iff {S X Y : Scheme} [X.Over S] [Y.Over S] (i : X.PartialIso Y) :
    i.toPartialMap.IsOver S ↔ i.IsOver (X ↘ S) (Y ↘ S) := by
  constructor
  · intro h
    have h' : i.toPartialMap.hom ≫ (Y ↘ S) = (↑i.toPartialMap.domain ↘ S) :=
      (Hom.isOver_iff S).mp h
    rw [PartialIso.toPartialMap_hom] at h'
    rw [show (↑i.toPartialMap.domain ↘ S) = i.source.ι ≫ (X ↘ S) from
      Opens.ι_comp_over i.source S] at h'
    rw [PartialIso.IsOver]
    exact h'
  · intro h
    change (i.toPartialMap.hom).IsOver S
    refine (Hom.isOver_iff S).mpr ?_
    rw [PartialIso.IsOver] at h
    rw [show (↑i.toPartialMap.domain ↘ S) = i.source.ι ≫ (X ↘ S) from
      Opens.ι_comp_over i.source S]
    rw [PartialIso.toPartialMap_hom]
    exact h

/-- If the underlying partial map of a partial isomorphism is a map over `S`, then so is the
underlying partial map of its inverse. -/
lemma PartialIso.symm_toPartialMap_isOver {S X Y : Scheme} [X.Over S] [Y.Over S]
    (i : X.PartialIso Y) (h : i.toPartialMap.IsOver S) : i.symm.toPartialMap.IsOver S :=
  (partialIso_isOver_iff i.symm).mpr ((PartialIso.IsOver.symm ((partialIso_isOver_iff i).mp h)))

/-! ## Base change of a birational map -/

/-- **Base change of a birational map** along `f : T ⟶ S`: a birational map of the base changes
whose forward and inverse rational maps are those of the base-changed representatives of `ψ`.  This
is the scheme-theoretic heart of the descent step of `thm:K3`. -/
theorem birationalMap_baseChangeAlong {S T X Y : Scheme.{0}} (f : T ⟶ S) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] [Surjective f] [UniversallyOpen f]
    [IrreducibleSpace (Work.K3.baseChangeAlong f X)]
    [IrreducibleSpace (Work.K3.baseChangeAlong f Y)] (ψ : X.BirationalMap Y) (hψ : ψ.IsOver S) :
    ∃ Ψ : (Work.K3.baseChangeAlong f X).BirationalMap (Work.K3.baseChangeAlong f Y),
      Ψ.IsOver T ∧
      (∀ (g : X.PartialMap Y) [g.IsOver S], g.toRationalMap = ψ.hom →
        (Work.K3.PartialMap.baseChangeAlong f g).toRationalMap = Ψ.hom) ∧
      (∀ (g : Y.PartialMap X) [g.IsOver S], g.toRationalMap = ψ.inv →
        (Work.K3.PartialMap.baseChangeAlong f g).toRationalMap = Ψ.inv) := by
  classical
  -- a partial isomorphism representing `ψ`
  obtain ⟨i, hi⟩ := Work.Motivic.exists_partialIso_toBirationalMap ψ
  have hiHom : i.toRationalMap = ψ.hom := by
    rw [← PartialIso.toBirationalMap_hom i, hi]
  haveI : i.toRationalMap.IsOver S := by rw [hiHom]; exact hψ
  -- an `S`-over representative of `i.toRationalMap` and the dense open on which it agrees with
  -- `i.toPartialMap`
  obtain ⟨g, hgS, hg⟩ := i.toRationalMap.exists_partialMap_over S
  haveI hgS' : g.IsOver S := hgS
  have hgi : g.toRationalMap = i.toPartialMap.toRationalMap := by rw [hg]
  obtain ⟨W, hWd, hWl, hWr, he⟩ := PartialMap.toRationalMap_eq_iff.mp hgi
  -- the restriction of `i` to `W`, which is a partial isomorphism *over* `S`
  have hWr' : W ≤ i.source := by
    rw [← PartialIso.toPartialMap_domain]
    exact hWr
  let P : X.PartialIso Y := i.restrictSource W hWd hWr'
  have hPhom : P.toPartialMap.hom = X.homOfLE hWr' ≫ i.toPartialMap.hom :=
    PartialIso.restrictSource_toPartialMap_hom i W hWd hWr'
  have hPover : P.toPartialMap.IsOver S := by
    change (P.toPartialMap.hom).IsOver S
    refine (Hom.isOver_iff S).mpr ?_
    have h1 : (g.restrict W hWd hWl).hom ≫ (Y ↘ S) = W.ι ≫ (X ↘ S) :=
      (Hom.isOver_iff S).mp (inferInstance : (g.restrict W hWd hWl).IsOver S)
    rw [show (↑P.toPartialMap.domain ↘ S) = W.ι ≫ (X ↘ S) from Opens.ι_comp_over W S]
    rw [← h1, he, PartialMap.restrict_hom, hPhom]
  have hPrat : P.toRationalMap = i.toRationalMap := by
    have h1 : P.toPartialMap.toRationalMap = i.toPartialMap.toRationalMap := by
      rw [PartialMap.toRationalMap_eq_iff]
      refine ⟨W, hWd, le_rfl, hWr, ?_⟩
      simp only [PartialMap.restrict_hom, hPhom, Scheme.homOfLE_rfl, Category.id_comp]
    simpa only [PartialIso.toRationalMap] using h1
  have hPbm : P.toBirationalMap = ψ := by
    refine BirationalMap.ext _ _ ?_
    rw [PartialIso.toBirationalMap_hom, hPrat, hiHom]
  have hPinv : P.symm.toRationalMap = ψ.inv := by
    rw [← PartialIso.toBirationalMap_inv P, hPbm]
  haveI : P.toPartialMap.IsOver S := hPover
  haveI hPsymm : (P.symm.toPartialMap).IsOver S := PartialIso.symm_toPartialMap_isOver P hPover
  -- base change `P`
  obtain ⟨h, hhom, hinv⟩ := partialIso_baseChangeAlong_symm f P hPover
  haveI hbc : (Work.K3.PartialMap.baseChangeAlong f P.toPartialMap).IsOver T :=
    Work.K3.PartialMap.baseChangeAlong_isOver f P.toPartialMap
  haveI hbcRat : ((Work.K3.PartialMap.baseChangeAlong f P.toPartialMap).toRationalMap).IsOver T :=
    inferInstance
  refine ⟨h.toBirationalMap, ?_, ?_, ?_⟩
  · -- `Ψ` is a map over `T`
    change (h.toRationalMap).IsOver T
    exact hhom.symm ▸ hbcRat
  · -- the forward clause
    intro g' _ hg'ψ
    rw [PartialIso.toBirationalMap_hom, hhom]
    refine Work.K3.partialMap_baseChangeAlong_equiv f g' P.toPartialMap ?_
    rw [hg'ψ, ← hiHom]
    change i.toRationalMap = P.toRationalMap
    rw [hPrat]
  · -- the inverse clause
    intro g' _ hg'ψ
    rw [PartialIso.toBirationalMap_inv, hinv]
    refine Work.K3.partialMap_baseChangeAlong_equiv f g' P.symm.toPartialMap ?_
    rw [hg'ψ, ← hPinv]

end Work.K3
