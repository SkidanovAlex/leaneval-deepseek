import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.TensorFG
import Submission.Work.SSSR.tensorComplexIsoExpTens
import Submission.Work.SSSR.normalizedCoeffIso
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

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
noncomputable def normalizedChainComplexCoprodIso (X : SSet.{0}) (M : ModuleCat R) (d : ℕ) :
    (∐ (fun _ : X.nonDegenerate d => M)) ≅ (X.normalizedChainComplex M).X d := by
  let F : X.nonDegenerate d → ModuleCat R := fun _ => M
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
noncomputable def coprodReindexIso (X : SSet.{0}) (d : ℕ) (M : ModuleCat R) :
    (∐ (fun _ : X.nonDegenerate d => M)) ≅ (∐ (fun _ : nIndex X d => M)) :=
  @asIso _ _ _ _
    (Sigma.map' (g := fun _ : X.nonDegenerate d => M) (f := fun _ : nIndex X d => M)
      (nIndexEquiv X d) (fun _ => 𝟙 M))
    (isIso_sigma_map'_of_equiv (nIndexEquiv X d) M)

end

end Work.SSSR
