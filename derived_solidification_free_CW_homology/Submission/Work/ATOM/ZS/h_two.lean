import Mathlib
import Submission.Work.ATOM.ZS.NullSeqMaps

namespace Work.ATOM.ZS

open CategoryTheory Limits MonoidalCategory LightCondensed LightProfinite MonoidalClosed
open OnePoint

/-!
# The identity `h₂` of the null-sequence scheme for `ℤ̃[S]`

The proof goes through the `0`-slice `x ↦ e₀ ⊗ x`:

* `hslice`: `(e₀ ▷ ℤ[S]) ≫ F = λ_ ℤ[S] ≫ qred`, i.e. on the slice `k = 0` the map `F` of
  REFS/03 §1 is the quotient map `ℤ[S] ⟶ ℤ̃[S]`;
* `hbig`: `sBig ≫ F = qred` (the unitor `λ_ ℤ[S]` cancels `(λ_ ℤ[S]).inv`);
* `hq`: `sHat ≫ F = qred` (the correction `1 - aug ≫ [s₀]` is killed by `qred`);
* finally cancel the epimorphism `qred` in `qred ≫ s ≫ F = sHat ≫ F = qred`.

The comparison with `F` itself is made through its specification `Work.ATOM.F_spec`
(`EA S ≫ F = Fsection`), i.e. `F` on the generator `(k,x)` of `P ⊗ ℤ[S]` is
`[x] - [ẽ(k,x)]`, together with the naturality of `Work.ATOM.zfreeTensorIso`.
-/

section Helpers

variable (S : LightProfinite.{0}) [Infinite S]

/-- On the slice `k = 0`, the projection to the second factor agrees with the left unitor. -/
private lemma zeroSlice_pr₂N :
    MonoidalCategory.whiskerRight (Work.ATOM.ptAt
      (S := LightProfinite.NatUnionInfty) (((0:ℕ):ℕ∪{∞}))) S ≫ Work.ATOM.pr₂N S
      = (λ_ S).hom := by
  apply ConcreteCategory.hom_ext; intro p; rfl

/-- On the slice `k = 0`, the map `ẽ` is the constant map at `s₀`. -/
private lemma zeroSlice_ePred :
    MonoidalCategory.whiskerRight (Work.ATOM.ptAt
      (S := LightProfinite.NatUnionInfty) (((0:ℕ):ℕ∪{∞}))) S ≫ Work.ATOM.ePred S
      = Work.ATOM.toPt (Work.ATOM.pt ⊗ S)
        ≫ Work.ATOM.ptAt (S := S) (Work.ATOM.levelData S).s₀ := by
  apply ConcreteCategory.hom_ext; intro p; rfl

/-- `F` on the `0`-slice is the quotient map `ℤ[S] ⟶ ℤ̃[S]`. -/
private lemma zmap_zeroSlice_Fsection :
    Work.ATOM.zmap (MonoidalCategory.whiskerRight (Work.ATOM.ptAt
      (S := LightProfinite.NatUnionInfty) (((0:ℕ):ℕ∪{∞}))) S) ≫ Work.ATOM.Fsection S
      = Work.ATOM.zmap (λ_ S).hom ≫ Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  rw [Work.ATOM.Fsection, ← Category.assoc, Preadditive.comp_sub,
      ← Work.ATOM.zmap_comp_zfree, ← Work.ATOM.zmap_comp_zfree, zeroSlice_pr₂N S,
      zeroSlice_ePred S, Work.ATOM.zmap_comp_zfree, Preadditive.sub_comp, Category.assoc,
      cokernel.condition, comp_zero, sub_zero]

/-- The unitality of the monoidal structure of `ℤ[-]`: the `0`-slice is the left unitor. -/
private lemma unitor_coherence :
    (Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S) ≫ (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom
      ≫ Work.ATOM.zmap (λ_ S).hom = (λ_ (Work.ATOM.zfree S)).hom := by
  exact (Functor.LaxMonoidal.left_unitality
    (F := lightProfiniteToLightCondSet ⋙ free ℤ) S).symm

/-- The identification `ℤ[(ℕ∪∞) × S] ≅ ℤ[ℕ∪∞] ⊗ ℤ[S]` intertwines `P_proj ▷ ℤ[S]` with `EA`. -/
private lemma zfreeTensorIso_hom_EA :
    (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).hom ≫ Work.ATOM.EA S
      = LightCondensed.P_proj ▷ Work.ATOM.zfree S := by
  rw [Work.ATOM.EA, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- `P_proj ▷ ℤ[S]` followed by `F` is `Fsection` up to the comparison isomorphism. -/
private lemma P_proj_tensor_F :
    (LightCondensed.P_proj ▷ Work.ATOM.zfree S) ≫ Work.ATOM.F S
      = (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).hom
        ≫ Work.ATOM.Fsection S := by
  rw [← zfreeTensorIso_hom_EA S, Category.assoc, Work.ATOM.F_spec S]

/-- Naturality of the comparison isomorphism at the `0`-inclusion `* = {0} ⊆ ℕ∪{∞}`. -/
private lemma zmap_zeroSlice_zfreeTensorIso :
    (Work.ATOM.zmap (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty) (((0:ℕ):ℕ∪{∞})))
        ▷ Work.ATOM.zfree S) ≫ (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).hom
      = (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom
        ≫ Work.ATOM.zmap (MonoidalCategory.whiskerRight (Work.ATOM.ptAt
            (S := LightProfinite.NatUnionInfty) (((0:ℕ):ℕ∪{∞}))) S) := by
  have h := Work.ATOM.zfreeTensorIso_natural (X := Work.ATOM.pt)
      (X' := LightProfinite.NatUnionInfty) (Y := S) (Y' := S)
      (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty) (((0:ℕ):ℕ∪{∞}))) (𝟙 S)
  simpa [Work.ATOM.zmap_id_zfree] using h

/-- The previous naturality, followed by `Fsection`. -/
private lemma zmap_zeroSlice_zfreeTensorIso_Fsection :
    (Work.ATOM.zmap (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty) (((0:ℕ):ℕ∪{∞})))
        ▷ Work.ATOM.zfree S) ≫ (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).hom
        ≫ Work.ATOM.Fsection S
      = (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom
        ≫ Work.ATOM.zmap (MonoidalCategory.whiskerRight (Work.ATOM.ptAt
            (S := LightProfinite.NatUnionInfty) (((0:ℕ):ℕ∪{∞}))) S) ≫ Work.ATOM.Fsection S := by
  rw [← Category.assoc, zmap_zeroSlice_zfreeTensorIso S, Category.assoc]

/-- **The `0`-slice identity**: `(e₀ ▷ ℤ[S]) ≫ F = λ_ ℤ[S] ≫ qred`. -/
private lemma hslice :
    (Work.ATOM.e0 ▷ Work.ATOM.zfree S) ≫ Work.ATOM.F S
      = (λ_ (Work.ATOM.zfree S)).hom ≫ Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  have hc' : ((Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S) ≫
        (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom) ≫ Work.ATOM.zmap (λ_ S).hom
      = (λ_ (Work.ATOM.zfree S)).hom := by
    rw [Category.assoc]; exact unitor_coherence S
  calc (Work.ATOM.e0 ▷ Work.ATOM.zfree S) ≫ Work.ATOM.F S
      = (Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S)
          ≫ (Work.ATOM.zmap (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty)
              (((0:ℕ):ℕ∪{∞}))) ▷ Work.ATOM.zfree S)
          ≫ (LightCondensed.P_proj ▷ Work.ATOM.zfree S) ≫ Work.ATOM.F S := by
          simp only [Work.ATOM.e0, MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = (Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S)
          ≫ (Work.ATOM.zmap (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty)
              (((0:ℕ):ℕ∪{∞}))) ▷ Work.ATOM.zfree S)
          ≫ (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).hom
          ≫ Work.ATOM.Fsection S := by
          rw [P_proj_tensor_F S]
    _ = (Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S)
          ≫ (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom
          ≫ Work.ATOM.zmap (MonoidalCategory.whiskerRight (Work.ATOM.ptAt
              (S := LightProfinite.NatUnionInfty) (((0:ℕ):ℕ∪{∞}))) S)
          ≫ Work.ATOM.Fsection S := by
          rw [zmap_zeroSlice_zfreeTensorIso_Fsection S]
    _ = (Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S)
          ≫ (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom ≫ Work.ATOM.zmap (λ_ S).hom
          ≫ Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
          rw [zmap_zeroSlice_Fsection S]
    _ = (λ_ (Work.ATOM.zfree S)).hom ≫ Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
          rw [← Category.assoc, ← Category.assoc, hc']

/-- `sBig` followed by `F` is the quotient map `ℤ[S] ⟶ ℤ̃[S]`. -/
private lemma sBig_F :
    Work.ATOM.sBig S ≫ Work.ATOM.F S
      = Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  rw [Work.ATOM.sBig, Category.assoc, hslice S, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- `sHat` followed by `F` is the quotient map `ℤ[S] ⟶ ℤ̃[S]`. -/
private lemma sHat_F :
    Work.ATOM.sHat S ≫ Work.ATOM.F S
      = Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  rw [Work.ATOM.sHat, Category.assoc, sBig_F S, Preadditive.sub_comp, Category.id_comp,
    Category.assoc, cokernel.condition, comp_zero, sub_zero]

end Helpers

/-- **Identity `h₂` of REFS/03 §1**: `s ≫ F = 𝟙 ℤ̃[S]`, i.e. `F ∘ s = id`.
`qred ≫ s = sHat` (`Work.ATOM.s_spec`), and `sHat ≫ F = qred` because
`F(sBig(x)) = F(0,x) = [x]` while the correction `aug ≫ [s₀]` is killed by `qred`
(`F(0,s₀) = 0` in `ℤ̃[S]`); then cancel the epimorphism `qred`.
The computation of `F` on the `0`-slice is made through its specification
`Work.ATOM.F_spec` (`EA S ≫ F = Fsection`) and the naturality of the comparison
isomorphism `Work.ATOM.zfreeTensorIso`. -/
theorem h_two (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.s S ≫ Work.ATOM.F S = 𝟙 (Work.ATOM.zred S (Work.ATOM.levelData S).s₀) := by
  apply (cancel_epi (Work.ATOM.qred S (Work.ATOM.levelData S).s₀)).mp
  rw [← Category.assoc, Work.ATOM.s_spec S, sHat_F S, Category.comp_id]

end Work.ATOM.ZS
