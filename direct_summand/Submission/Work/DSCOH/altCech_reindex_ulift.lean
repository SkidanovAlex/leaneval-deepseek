/-
Area DSCOH — invariance of the geometric alternating Čech complex under a reindexing of the family
of opens by an order isomorphism.

`Work.DSCOH.altCech P U` depends on the index type `ι` only through the finsets of `ι`: its `q`-th
term is the product, over the `(q+1)`-element subsets `S` of `ι`, of the sections of `P` over
`⋂_{i∈S} U i`, and the differential is the alternating sum of the restriction maps.  If
`e : ι ≃o ι'` is an *order* isomorphism, then reindexing a subset `S ⊆ ι` as `S.map e ⊆ ι'` gives a
bijection between the `(q+1)`-element subsets of `ι` and of `ι'` which carries `S.inf U` to
`(S.map e).inf (U ∘ e.symm)` (`Finset.inf_map`), and the signs of the alternating differential are
preserved because `e` is order preserving (`OrderIso.lt_iff_lt`).  Hence there is an isomorphism of
cochain complexes

  `altCech P U ≅ altCech P (U ∘ ⇑e.symm)`,

whose components are obtained from `Equiv.piCongrLeft` (the combinatorial reindexing) followed by
the transports of the value modules along the (propositional) equalities of opens
(`LinearEquiv.cast`).  All of these transports are restriction maps of `P` along inclusions of
opens, and since morphisms in the category of opens form a subsingleton the differential
compatibility reduces to a bookkeeping of morphisms with the same source and target.

The application we need is the reindexing `ULift (Fin n) ≃o Fin n`, which identifies the complex of
the `ULift`-indexed cover used by the frozen F1 statement with the `Fin n`-indexed complex that the
chart comparison `altCech_iso_chartCech_of_termwise` consumes.
-/
import Mathlib
import Submission.Work.DSCOH.AltCechComplex

open CategoryTheory

universe u v w uι uι' uMod uA

namespace Work.DSCOH

set_option linter.unusedSectionVars false

/-! ## Restriction maps and transports along equalities of opens -/

section Transports

variable {X : Type v} [TopologicalSpace X] {A : Type w} [CommRing A]

/-- The restriction map of the presheaf `P` along the inclusion `W ≤ W'`: it is the map on sections
induced by the (unique) morphism `W ⟶ W'` of the category of opens. -/
noncomputable def Res (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    {W W' : TopologicalSpace.Opens X} (h : W ≤ W') :
    (P.obj (Opposite.op W')) →ₗ[A] (P.obj (Opposite.op W)) :=
  (P.map (CategoryTheory.homOfLE h).op).hom

/-- `Res` depends on the inclusion only through its source and target (morphisms of the category of
opens form a subsingleton). -/
theorem Res_congr (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    {W W' : TopologicalSpace.Opens X} (h₁ h₂ : W ≤ W') : Res P h₁ = Res P h₂ := by
  unfold Res; congr 1

/-- Two inclusions with the same source and target induce the same restriction map. -/
theorem Res_congr_apply (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    {W W' : TopologicalSpace.Opens X} (h₁ h₂ : W ≤ W') (y : P.obj (Opposite.op W')) :
    Res P h₁ y = Res P h₂ y := by
  rw [Res_congr P h₁ h₂]

/-- Functoriality of the restriction maps of `P`. -/
theorem Pmap_comp_apply (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    {W₁ W₂ W₃ : TopologicalSpace.Opens X} (h₁ : W₁ ≤ W₂) (h₂ : W₂ ≤ W₃)
    (y : P.obj (Opposite.op W₃)) :
    (P.map (CategoryTheory.homOfLE h₁).op).hom ((P.map (CategoryTheory.homOfLE h₂).op).hom y)
      = (P.map (CategoryTheory.homOfLE (h₁.trans h₂)).op).hom y := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← P.map_comp]
  congr 1

/-- The transport of the value of `P` along an equality of opens, as a linear map. -/
noncomputable def Pcast (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    {W₁ W₂ : TopologicalSpace.Opens X} (h : W₁ = W₂) :
    (P.obj (Opposite.op W₁)) →ₗ[A] (P.obj (Opposite.op W₂)) :=
  (P.map (CategoryTheory.homOfLE (le_of_eq h.symm)).op).hom

/-- `Pcast` agrees with the (linear) dependent transport `cast` along the equality of opens. -/
theorem Pcast_eq_cast (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    {W₁ W₂ : TopologicalSpace.Opens X} (h : W₁ = W₂) (x : P.obj (Opposite.op W₁)) :
    Pcast P h x
      = cast (congrArg (fun W : TopologicalSpace.Opens X => ↥(P.obj (Opposite.op W))) h) x := by
  subst h; simp [Pcast]

/-- The dependent transport of the values of a dependent function along an equality of indices. -/
theorem cast_congrArg_apply {α : Sort*} {β : α → Sort*} {a b : α} (h : a = b)
    (x : (i : α) → β i) : cast (congrArg β h) (x a) = x b := by
  subst h; rfl

end Transports

/-! ## The combinatorial reindexing of the index sets -/

section Reindex

variable {X : Type v} [TopologicalSpace X] {A : Type w} [CommRing A]
variable {ι : Type uι} {ι' : Type uι'} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [Fintype ι'] [DecidableEq ι'] [LinearOrder ι']

/-- The bijection between the `(q+1)`-element subsets of `ι` and of `ι'` induced by an equivalence
`e : ι ≃ ι'`: a subset is transported by `Finset.map`. -/
noncomputable abbrev fse (e : ι ≃ ι') (q : ℕ) :
    {S : Finset ι // S.card = q + 1} ≃ {S : Finset ι' // S.card = q + 1} where
  toFun S := ⟨(Equiv.finsetCongr e) S.1, by rw [Equiv.finsetCongr_apply, Finset.card_map]; exact S.2⟩
  invFun T := ⟨(Equiv.finsetCongr e.symm) T.1, by rw [Equiv.finsetCongr_apply, Finset.card_map]; exact T.2⟩
  left_inv S := by
    apply Subtype.ext
    show (Equiv.finsetCongr e.symm) ((Equiv.finsetCongr e) S.1) = S.1
    rw [← Equiv.finsetCongr_symm, Equiv.symm_apply_apply]
  right_inv T := by
    apply Subtype.ext
    show (Equiv.finsetCongr e) ((Equiv.finsetCongr e.symm) T.1) = T.1
    rw [← Equiv.finsetCongr_symm, Equiv.apply_symm_apply]

/-- The intersection of the reindexed family over the image of `S` equals the intersection over
`S`. -/
theorem althT (e : ι ≃o ι') (U : ι → TopologicalSpace.Opens X) (q : ℕ)
    (T : {S : Finset ι' // S.card = q + 1}) :
    ((fse (e : ι ≃ ι') q).symm T).1.inf U = T.1.inf (U ∘ ⇑e.symm) :=
  Finset.inf_map T.1 (e.symm).toEmbedding U

/-- **The reindexing of the terms of the alternating Čech complex**: the product over the
`(q+1)`-element subsets of `ι` is identified with the product over the `(q+1)`-element subsets of
`ι'`, the value at a subset being transported along the equality of intersections `althT`. -/
noncomputable def termEquiv (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A) (e : ι ≃o ι')
    (U : ι → TopologicalSpace.Opens X) (q : ℕ) :
    AltCechTerm P U q ≃ₗ[A] AltCechTerm P (U ∘ ⇑e.symm) q :=
  (LinearEquiv.piCongrLeft (R := A)
      (φ := fun S : {S : Finset ι // S.card = q + 1} => (↥(P.obj (Opposite.op (S.1.inf U)))))
      (e := (fse (e : ι ≃ ι') q).symm)).symm.trans
    (LinearEquiv.piCongrRight (R := A)
      (fun T : {S : Finset ι' // S.card = q + 1} =>
        LinearEquiv.cast (M := fun W : TopologicalSpace.Opens X => ↥(P.obj (Opposite.op W)))
          (althT e U q T)))

/-- The value of the reindexing on an element: it is the transport of the corresponding component
along the equality of intersections. -/
theorem termEquiv_apply (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A) (e : ι ≃o ι')
    (U : ι → TopologicalSpace.Opens X) (q : ℕ) (x : AltCechTerm P U q)
    (T : {S : Finset ι' // S.card = q + 1}) :
    termEquiv P e U q x T
      = Pcast P (althT e U q T) (x ((fse (e : ι ≃ ι') q).symm T)) := by
  simp only [termEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  rw [LinearEquiv.cast_apply]
  have h1 : (LinearEquiv.piCongrLeft A
        (fun S : {S : Finset ι // S.card = q + 1} => (↥(P.obj (Opposite.op (S.1.inf U)))))
        (Equiv.symm (fse (e : ι ≃ ι') q))).symm x T
      = x ((fse (e : ι ≃ ι') q).symm T) := by
    show (LinearEquiv.piCongrLeft' A (fun S : {S : Finset ι // S.card = q + 1} =>
        (↥(P.obj (Opposite.op (S.1.inf U))))) (Equiv.symm (fse (e : ι ≃ ι') q)).symm) x T
      = x ((fse (e : ι ≃ ι') q).symm T)
    rw [LinearEquiv.piCongrLeft'_apply]
    simp only [Equiv.symm_symm]
  rw [h1, ← Pcast_eq_cast]

/-- Applying `x` at two index sets with the same underlying finset: the `Pcast`-transport. -/
theorem Pcast_index_eq (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    {q : ℕ} (Aa Bb : {S : Finset ι // S.card = q + 1}) (h : Aa.1 = Bb.1)
    (U : ι → TopologicalSpace.Opens X) (x : AltCechTerm P U q) :
    x Bb = Pcast P (congrArg (fun s : Finset ι => s.inf U) h) (x Aa) := by
  rw [Pcast_eq_cast]
  have hsame : congrArg (fun W : TopologicalSpace.Opens X => ↥(P.obj (Opposite.op W)))
        (congrArg (fun s : Finset ι => s.inf U) h)
      = congrArg (fun S : {S : Finset ι // S.card = q + 1} =>
          ↥(P.obj (Opposite.op (S.1.inf U)))) (Subtype.ext h : Aa = Bb) :=
    Subsingleton.elim _ _
  rw [hsame]
  exact (cast_congrArg_apply (Subtype.ext h : Aa = Bb) x).symm

/-- The sign of the alternating differential is preserved by the reindexing: the number of elements
of `T` below `i` equals the number of elements of the reindexed finset below the reindexed
element. -/
theorem sign_eq (e : ι ≃o ι') (T : Finset ι') (i : ι') :
    (T.filter (fun j => j < i)).card
      = ((T.map (e.symm).toEmbedding).filter (fun k => k < e.symm i)).card := by
  rw [← Finset.card_map (f := (e.symm).toEmbedding), Finset.map_filter]
  congr 1
  apply Finset.filter_congr
  intro k _
  show e k < i ↔ k < e.symm i
  exact (show e k < i ↔ e k < e (e.symm i) from by rw [OrderIso.apply_symm_apply]).trans
    (e.lt_iff_lt (x := k) (y := e.symm i))

/-- The bijection between the attached elements of a finset and of its image under `e.symm`. -/
noncomputable def attachEquiv (e : ι ≃ ι') (T : Finset ι') :
    ↥T ≃ ↥(Finset.map (Equiv.toEmbedding e.symm) T) where
  toFun i := ⟨e.symm i.1, by rw [Finset.mem_map_equiv]; simp⟩
  invFun j := ⟨e j.1, by
    have h := j.2
    rw [Finset.mem_map_equiv] at h
    simpa using h⟩
  left_inv i := by ext; simp
  right_inv j := by ext; simp

/-- `Finset.map_erase`, in the shape needed for the term-by-term comparison of the differentials. -/
theorem hAB (e : ι ≃ ι') (q : ℕ) (T : {S : Finset ι' // S.card = q + 1 + 1}) (i : ↥T.1) :
    ((fse (e : ι ≃ ι') q).symm ⟨T.1.erase i.1,
        by rw [Finset.card_erase_of_mem i.2]; omega⟩).1
      = ((fse (e : ι ≃ ι') (q+1)).symm T).1.erase ((attachEquiv (e : ι ≃ ι') T.1 i).1) :=
  Finset.map_erase (Equiv.toEmbedding e.symm) T.1 i.1

/-- Reindexing a sum over the attached elements of the image finset. -/
theorem sum_attach_reindex (e : ι ≃ ι') (q : ℕ) (T : {S : Finset ι' // S.card = q + 1})
    (M : Type*) [AddCommMonoid M] (g : ↥(((fse (e : ι ≃ ι') q).symm T).1) → M) :
    ∑ j ∈ (((fse (e : ι ≃ ι') q).symm T).1).attach, g j
      = ∑ i ∈ T.1.attach, g (attachEquiv (e : ι ≃ ι') T.1 i) := by
  simp only [Finset.attach_eq_univ]
  exact (Equiv.sum_comp (attachEquiv (e : ι ≃ ι') T.1)
    (fun i : ↥(((fse (e : ι ≃ ι') q).symm T).1) => g i)).symm

end Reindex

/-! ## The differential is compatible with the reindexing -/

section Differential

variable {X : Type v} [TopologicalSpace X] {A : Type w} [CommRing A]
variable {ι : Type uι} {ι' : Type uι'} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [Fintype ι'] [DecidableEq ι'] [LinearOrder ι']

set_option maxHeartbeats 2000000 in
/-- **The `T`-component of the compatibility of the alternating Čech differential with the
reindexing.**  Both sides are alternating sums over the elements of `T`; the two sums are matched by
`sum_attach_reindex` and the individual terms agree because the corresponding restriction maps have
the same source and target (morphisms of the category of opens form a subsingleton) and the signs
agree by `sign_eq`. -/
theorem altCechDiff_reindex_termwise (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (e : ι ≃o ι') (U : ι → TopologicalSpace.Opens X) (q : ℕ) (x : AltCechTerm P U q)
    (T : {S : Finset ι' // S.card = q + 1 + 1}) :
    (altCechDiff P (U ∘ ⇑e.symm) q ((termEquiv P e U q) x)) T
      = (termEquiv P e U (q+1) ((altCechDiff P U q) x)) T := by
  rw [altCechDiff, LinearMap.pi_apply]
  rw [termEquiv_apply]
  rw [altCechDiff, LinearMap.pi_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [map_sum]
  rw [sum_attach_reindex (e : ι ≃ ι') (q+1) T]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  rw [termEquiv_apply]
  have hx : x (⟨(((fse (e : ι ≃ ι') (q+1)).symm T).1).erase
          (((attachEquiv (e : ι ≃ ι') T.1) i).1),
        by rw [show ((fse (e : ι ≃ ι') (q+1)).symm T).1
              = Finset.map (Equiv.toEmbedding (Equiv.symm (e : ι ≃ ι'))) T.1 from rfl,
            Finset.card_erase_of_mem ((attachEquiv (e : ι ≃ ι') T.1) i).2,
            Finset.card_map]; omega⟩ : {S : Finset ι // S.card = q+1})
      = Pcast P (congrArg (fun s : Finset ι => s.inf U) (hAB (e : ι ≃ ι') q T i))
          (x ((fse (e : ι ≃ ι') q).symm ⟨T.1.erase i.1,
            by rw [Finset.card_erase_of_mem i.2]; omega⟩)) :=
    Pcast_index_eq P _ _ (hAB (e : ι ≃ ι') q T i) U x
  rw [hx]
  simp only [Pcast]
  rw [Pmap_comp_apply]
  rw [Pmap_comp_apply]
  rw [Pmap_comp_apply]
  rw [sign_eq e T.1 i.1]
  congr 1

/-- **The alternating Čech differential is natural under the reindexing**: the reindexing of terms
is a chain map. -/
theorem altCechDiff_termEquiv_comp (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (e : ι ≃o ι') (U : ι → TopologicalSpace.Opens X) (q : ℕ) :
    (altCechDiff P (U ∘ ⇑e.symm) q).comp (termEquiv P e U q).toLinearMap
      = (termEquiv P e U (q+1)).toLinearMap.comp (altCechDiff P U q) := by
  apply LinearMap.ext; intro x
  funext T
  change (altCechDiff P (U ∘ ⇑e.symm) q) ((termEquiv P e U q) x) T
      = (termEquiv P e U (q+1)) ((altCechDiff P U q) x) T
  exact altCechDiff_reindex_termwise P e U q x T

end Differential

/-! ## The isomorphism of cochain complexes -/

section Iso

variable {X : Type v} [TopologicalSpace X] {A : Type w} [CommRing A]
variable {ι : Type uι} {ι' : Type uι'} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [Fintype ι'] [DecidableEq ι'] [LinearOrder ι']

/-- **The alternating Čech complex is invariant under an order-isomorphic reindexing of the family
of opens.** -/
theorem altCech_iso_of_orderIso
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{max uι uι' uMod, w} A) (e : ι ≃o ι')
    (U : ι → TopologicalSpace.Opens X) :
    Nonempty (altCech P U ≅ altCech P (U ∘ ⇑e.symm)) :=
  ⟨HomologicalComplex.Hom.isoOfComponents (fun q => LinearEquiv.toModuleIso (termEquiv P e U q))
    (by
      intro i j hij
      rw [ComplexShape.up_Rel] at hij
      subst hij
      rw [LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_hom]
      simp only [altCech, CochainComplex.of_d]
      rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, altCechDiff_termEquiv_comp])⟩

end Iso

/-! ## The `ULift` reindexing -/

/-- The order isomorphism between `ULift (Fin n)` and `Fin n` given by `ULift.down`; it is the
reindexing under which the `ULift`-indexed covers of the frozen F1 statement are `Fin n`-indexed. -/
noncomputable def uliftOrderIso (n : ℕ) : ULift.{u} (Fin n) ≃o Fin n where
  toEquiv := Equiv.ulift
  map_rel_iff' := by intro a b; rfl

theorem altCech_reindex_ulift {X : AlgebraicGeometry.Scheme.{u}} {A : Type u} [CommRing A] {n : ℕ}
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat.{u, u} A))
    (U : ULift.{u} (Fin n) → TopologicalSpace.Opens X) :
    Nonempty (Work.DSCOH.altCech P U ≅ Work.DSCOH.altCech P (fun k : Fin n => U ⟨k⟩)) :=
  altCech_iso_of_orderIso P (uliftOrderIso.{u} n) U

end Work.DSCOH
