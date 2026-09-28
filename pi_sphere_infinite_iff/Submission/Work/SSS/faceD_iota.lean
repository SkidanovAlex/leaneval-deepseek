import Mathlib
import Submission.Work.SSS.serreE1CruxDefs

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

attribute [local instance] Classical.propDecidable

/-! ## Components of the reindexing isomorphism

`Work.SSS.coprodReindexIso X d M` is `asIso (Sigma.map' (nIndexEquiv X d) (fun _ => 𝟙 M))`, so on
the coprojections it is the reindexing `Sigma.ι _ x ↦ Sigma.ι _ (nIndexEquiv X d x)` in the forward
direction and `Sigma.ι _ y ↦ Sigma.ι _ ((nIndexEquiv X d).symm y)` in the backward direction. -/

/-- The `x`-component of the reindexing isomorphism, in the forward direction. -/
lemma coprodReindexIso_hom_ι (X : SSet.{0}) (d : ℕ) (M : ModuleCat ℤ)
    (x : X.nonDegenerate d) :
    Sigma.ι (fun _ : X.nonDegenerate d => M) x ≫ (coprodReindexIso X d M).hom
      = Sigma.ι (fun _ : nIndex X d => M) (nIndexEquiv X d x) := by
  rw [Work.SSS.coprodReindexIso]
  change Sigma.ι (fun _ : X.nonDegenerate d => M) x ≫
      Sigma.map' (g := fun _ : X.nonDegenerate d => M) (f := fun _ : nIndex X d => M)
        (nIndexEquiv X d) (fun _ => 𝟙 M)
    = Sigma.ι (fun _ : nIndex X d => M) (nIndexEquiv X d x)
  rw [Sigma.ι_comp_map']
  simp

/-- The `y`-component of the reindexing isomorphism, in the backward direction. -/
lemma coprodReindexIso_inv_ι (X : SSet.{0}) (d : ℕ) (M : ModuleCat ℤ) (y : nIndex X d) :
    Sigma.ι (fun _ : nIndex X d => M) y ≫ (coprodReindexIso X d M).inv
      = Sigma.ι (fun _ : X.nonDegenerate d => M) ((nIndexEquiv X d).symm y) := by
  have h1 : Sigma.ι (fun _ : X.nonDegenerate d => M) ((nIndexEquiv X d).symm y)
      ≫ (coprodReindexIso X d M).hom = Sigma.ι (fun _ : nIndex X d => M) y := by
    rw [coprodReindexIso_hom_ι, Equiv.apply_symm_apply]
  rw [← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inverse of `nIndexEquiv X d` is given by the underlying simplex of an `nIndex` element
(`def`-level equality: `(nIndexEquiv X d).symm` is `nIndexEquiv X d`'s `invFun`). -/
lemma nIndexEquiv_symm_apply (X : SSet.{0}) (d : ℕ) (y : nIndex X d) :
    (nIndexEquiv X d).symm y = ⟨nIndexBase X y, nIndexBase_mem X y⟩ := by
  rw [nIndexEquiv]
  rfl

/-- The `σ`-component of the alternating-face differential `Work.SSS.faceD'` on the coproduct of
copies of `M` indexed by `Work.SSS.nIndex X j`: it is the alternating sum of the coprojections of
the faces, a degenerate face contributing `0`.

Route: `Work.SSS.coprodReindexIso X d M` is `asIso (Sigma.map' (nIndexEquiv X d) (fun _ => 𝟙 M))`,
so `Sigma.ι σ ≫ (coprodReindexIso X (j+1) M).inv = Sigma.ι (nIndexEquiv X (j+1)).symm σ` by
`Sigma.ι_comp_map'`, and `(nIndexEquiv X (j+1)).symm σ = ⟨nIndexBase X σ, nIndexBase_mem X σ⟩` (a
`def`-level equality); then apply the proved `Work.SSS.faceD_ι` and use
`Sigma.ι _ ≫ Sigma.map' (nIndexEquiv X j) (fun _ => 𝟙 M) = Sigma.ι _` again. -/
theorem faceD_iota (X : SSet.{0}) (M : ModuleCat ℤ) (j : ℕ) (σ : Work.SSS.nIndex X (j+1)) :
    Sigma.ι (fun _ : Work.SSS.nIndex X (j+1) => M) σ ≫ Work.SSS.faceD' X M j =
      ∑ i : Fin (j+2), (-1 : ℤ)^((i:ℕ)) •
        (if h : X.δ i (Work.SSS.nIndexBase X σ) ∈ X.nonDegenerate j then
          Sigma.ι (fun _ : Work.SSS.nIndex X j => M)
            (Work.SSS.nIndexEquiv X j ⟨X.δ i (Work.SSS.nIndexBase X σ), h⟩)
         else 0) := by
  -- the `σ`-component of the reindexing isomorphism at level `j+1`
  have hfirst : Sigma.ι (fun _ : nIndex X (j+1) => M) σ ≫ (coprodReindexIso X (j+1) M).inv
      = Sigma.ι (fun _ : X.nonDegenerate (j+1) => M)
          ⟨nIndexBase X σ, nIndexBase_mem X σ⟩ := by
    rw [coprodReindexIso_inv_ι, nIndexEquiv_symm_apply]
  -- unfold `faceD'` and move the `σ`-component through the reindexing
  rw [Work.SSS.faceD']
  rw [← Category.assoc, hfirst, ← Category.assoc]
  -- apply the explicit face differential in the `nonDegenerate` coordinates
  rw [Work.SSS.faceD_ι]
  -- distribute the composition over the alternating sum
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp]
  congr 1
  split_ifs with h
  · rw [coprodReindexIso_hom_ι]
  · rw [zero_comp]

end Work.SSS
