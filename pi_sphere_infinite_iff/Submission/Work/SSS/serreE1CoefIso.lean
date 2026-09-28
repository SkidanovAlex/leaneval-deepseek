import Mathlib
import Submission.Work.SSS.serreE1Defs
import Submission.Work.SSS.TensorFG
import Submission.Work.SSS.tensorComplexIsoExpTens
import Submission.Work.SSS.normalizedCoeffIso

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

/-- The simplex of `X` underlying an element `y` of `nIndex X d`. -/
def nIndexBase (X : SSet.{0}) {d : ℕ} (y : nIndex X d) : X _⦋d⦌ :=
  (y.1.toS.cast y.2).simplex

/-- The simplex `nIndexBase X y` is nondegenerate. -/
lemma nIndexBase_mem (X : SSet.{0}) {d : ℕ} (y : nIndex X d) :
    nIndexBase X y ∈ X.nonDegenerate d :=
  (y.1.cast y.2).nonDegenerate

/-- The canonical bijection between the nondegenerate `d`-simplices of `X` and the elements of
`nIndex X d` (the nondegenerate simplices of `X` of dimension `d`). -/
noncomputable def nIndexEquiv (X : SSet.{0}) (d : ℕ) : X.nonDegenerate d ≃ nIndex X d where
  toFun x := ⟨SSet.N.mk x.1 x.2, rfl⟩
  invFun y := ⟨nIndexBase X y, nIndexBase_mem X y⟩
  left_inv x := by
    apply Subtype.ext
    show nIndexBase X (⟨SSet.N.mk x.1 x.2, rfl⟩ : nIndex X d) = x.1
    rfl
  right_inv y := by
    apply Subtype.ext
    show SSet.N.mk (nIndexBase X y) ((y.1.cast y.2).nonDegenerate) = y.1
    rw [show SSet.N.mk (nIndexBase X y) ((y.1.cast y.2).nonDegenerate) = y.1.cast y.2 from rfl,
      SSet.N.cast_eq_self]

/-- The `d`-th term of the normalized chain complex of `X` with coefficients in `M` is the
coproduct of copies of `M` indexed by the nondegenerate `d`-simplices of `X`
(Mathlib's `SSet.isColimitCofanNormalizedChainComplex`). -/
noncomputable def normalizedChainComplexCoprodIso (X : SSet.{0}) (M : ModuleCat ℤ) (d : ℕ) :
    (∐ (fun _ : X.nonDegenerate d => M)) ≅ (X.normalizedChainComplex M).X d := by
  let F : X.nonDegenerate d → ModuleCat ℤ := fun _ => M
  let c₂ : Cofan F := Cofan.mk (∐ F) (Sigma.ι F)
  have h₂ : IsColimit c₂ := coproductIsCoproduct F
  exact IsColimit.coconePointUniqueUpToIso (F := Discrete.functor F) (s := c₂)
    (t := X.cofanNormalizedChainComplex M d) h₂
    (X.isColimitCofanNormalizedChainComplex M d)

/-- Reindexing a coproduct along a bijection of the index types. -/
lemma isIso_sigma_map'_of_equiv {C : Type*} [Category* C] {α β : Type} (e : α ≃ β) (M : C)
    [HasCoproduct (fun _ : α => M)] [HasCoproduct (fun _ : β => M)] :
    IsIso (Sigma.map' (g := fun _ : α => M) (f := fun _ : β => M) e (fun _ => 𝟙 M)) := by
  refine ⟨Sigma.map' (g := fun _ : β => M) (f := fun _ : α => M) e.symm (fun _ => 𝟙 M),
    ?_, ?_⟩
  · apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, Sigma.ι_comp_map', Category.assoc, Sigma.ι_comp_map']
    simp [e.symm_apply_apply]
  · apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, Sigma.ι_comp_map', Category.assoc, Sigma.ι_comp_map']
    simp [e.apply_symm_apply]

/-- The coproduct over the nondegenerate `d`-simplices of `X` is the coproduct over `nIndex X d`,
because the two index types are canonically identified. -/
noncomputable def coprodReindexIso (X : SSet.{0}) (d : ℕ) (M : ModuleCat ℤ) :
    (∐ (fun _ : X.nonDegenerate d => M)) ≅ (∐ (fun _ : nIndex X d => M)) :=
  @asIso _ _ _ _
    (Sigma.map' (g := fun _ : X.nonDegenerate d => M) (f := fun _ : nIndex X d => M)
      (nIndexEquiv X d) (fun _ => 𝟙 M))
    (isIso_sigma_map'_of_equiv (nIndexEquiv X d) M)

/-- **The degreewise description of `N_*(X) ⊗ M`.**  For a simplicial set `X` and a `ℤ`-module `M`,
the `d`-th term of the tensor product of the normalized chain complex of `X` with `M` (placed in
degree `0`) is the coproduct, over the nondegenerate `d`-simplices of `X`, of copies of `M`.

Indeed `(N_*(X) ⊗ M)_d ≅ N_d(X) ⊗ M` (`Work.SSS.tensorComplexIsoExpTens`,
`Work.SSS.expTens_X`) and `N_d(X)` is the coproduct of copies of `ℤ` indexed by the nondegenerate
`d`-simplices of `X` (Mathlib's `SSet.isColimitCofanNormalizedChainComplex`, via
`Work.SSS.nIndex`), while tensoring with `M` preserves coproducts (`ModuleCat ℤ` is closed
monoidal) and `ℤ ⊗ M ≅ M`.

This is the last step of the degreewise identification of the E¹ page of the Serre spectral
sequence with `N_*(B) ⊗ H_t(F)` (`Work.SSS.serreE1`).

Do NOT use `sorry`, `axiom` or `admit`. -/
theorem serreE1CoefIso (X : SSet.{0}) (M : ModuleCat ℤ) (d : ℕ) :
    Nonempty ((∐ (fun _ : Work.SSS.nIndex X d => M)) ≅
      (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).X d) := by
  refine ⟨?_⟩
  -- `(tensorComplex K M).X d ≅ (expTens K M).X d`
  have e₁ : (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).X d ≅
      (Work.SSS.expTens (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).X d :=
    asIso ((Work.SSS.tensorComplexIsoExpTens
      (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).some.hom.f d)
  -- `(X.normalizedChainComplex M).X d ≅ (expTens K M).X d`
  have e₂ : (X.normalizedChainComplex M).X d ≅
      (Work.SSS.expTens (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).X d :=
    asIso ((Work.SSS.normalizedCoeffIso X M).some.hom.f d)
  -- `∐_{X.nonDegenerate d} M ≅ (X.normalizedChainComplex M).X d`
  have e₃ := normalizedChainComplexCoprodIso X M d
  -- `∐_{X.nonDegenerate d} M ≅ ∐_{nIndex X d} M`
  have e₄ := coprodReindexIso X d M
  exact e₄.symm ≪≫ e₃ ≪≫ e₂ ≪≫ e₁.symm

end

end Work.SSS
