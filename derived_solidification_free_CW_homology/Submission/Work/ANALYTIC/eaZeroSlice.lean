import Mathlib
import Submission.Work.ANALYTIC.towerFEAsetup
import Submission.Work.ANALYTIC.EA_shift
import Submission.Work.ANALYTIC.unitor_zfreeTensorIso

/-!
# `Work.ANALYTIC.EAZeroSlice`: the `EA`-coherence of the zero slice

`Work.ANALYTIC.EAZeroSlice` is the identity

```
(λ_ ℤ[S])⁻¹ ≫ (e₀ ▷ ℤ[S]) = zmap (zeroSlice S) ≫ EA S
```

in `LightCondAb`, where

* `zeroSlice S = (λ_ S)⁻¹ ≫ (ptAt 0 ▷ S) : S ⟶ (ℕ∪{∞}) × S` is the slice `s ↦ (0,s)`;
* `EA S : ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]` is the quotient killing `{∞} × S`;
* `e₀ : 𝟙_ ⟶ P` is the point `e₀` of `P`.

Mathematically: the class in `P ⊗ ℤ[S]` of the generator `e_{(0,s)}` of `ℤ[(ℕ∪{∞}) × S]` is
`e₀ ⊗ e_s`.

The proof is pure monoidal bookkeeping, with no input about `S`:

* `Work.ANALYTIC.unitor_zfreeTensorIso` (the `left_unitality_inv` coherence of the lax monoidal
  functor `ℤ[-]`) identifies `(λ_ ℤ[S])⁻¹ ≫ (ε ▷ ℤ[S])` with `zmap ((λ_ S)⁻¹) ≫ μ⁻¹`, where
  `ε = unitIso` and `μ = zfreeTensorIso`;
* `Work.ANALYTIC.zmap_whiskerRight_zfreeTensorIso` (naturality of the tensorator `μ` in its first
  variable) moves `zmap (ptAt 0 ▷ S)` past `μ⁻¹`;
* `EA` is by definition `μ⁻¹ ≫ (P_proj ▷ ℤ[S])` and `zmap` is a functor, so
  `zmap (zeroSlice S) = zmap ((λ_ S)⁻¹) ≫ zmap (ptAt 0 ▷ S)`.
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

/-- The point `0` of `ℕ∪{∞}`: the map `* ⟶ ℕ∪{∞}` used in the zero slice. -/
private abbrev zeroPt : Work.ATOM.pt ⟶ LightProfinite.NatUnionInfty :=
  Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty) (OnePoint.some 0)

/-- The point `e₀` of `P`, written as `unitIso` followed by `zmap (ptAt 0) ≫ P_proj`, is the
point `Work.ANALYTIC.ePointZ 0` of `P`. -/
private theorem zeroPt_ePointZ :
    Work.ATOM.unitIso.hom ≫ (Work.ATOM.zmap zeroPt ≫ LightCondensed.P_proj)
      = Work.ANALYTIC.ePointZ 0 := rfl

theorem eaZeroSlice : Work.ANALYTIC.EAZeroSlice := by
  intro S
  -- `(λ_ ℤ[S])⁻¹ ≫ (ε ▷ ℤ[S]) = zmap ((λ_ S)⁻¹) ≫ μ⁻¹`: the `left_unitality_inv` coherence.
  have h1 : (λ_ (Work.ATOM.zfree S)).inv ≫ (Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S)
      = Work.ATOM.zmap (λ_ S).inv ≫ (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).inv := by
    have h := Work.ANALYTIC.unitor_zfreeTensorIso S
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- The whiskering of the point `e₀ = ε ≫ zmap (ptAt 0) ≫ P_proj`.
  have h4 : (Work.ANALYTIC.ePointZ 0 ▷ Work.ATOM.zfree S)
      = (Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S)
        ≫ (Work.ATOM.zmap zeroPt ▷ Work.ATOM.zfree S)
        ≫ (LightCondensed.P_proj ▷ Work.ATOM.zfree S) := by
    rw [← zeroPt_ePointZ]
    simp only [MonoidalCategory.comp_whiskerRight]
  -- Naturality of `μ` in the first variable, in inverse form.
  have h3 : Work.ATOM.zmap (zeroPt ▷ S)
        ≫ (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).inv
      = (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).inv
        ≫ (Work.ATOM.zmap zeroPt ▷ Work.ATOM.zfree S) := by
    rw [Iso.comp_inv_eq]
    rw [Category.assoc, Work.ANALYTIC.zmap_whiskerRight_zfreeTensorIso (X := Work.ATOM.pt)
      (X' := LightProfinite.NatUnionInfty) (Y := S) zeroPt]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  -- `zmap` is a functor, so it turns `zeroSlice` into a composite.
  have h2 : Work.ATOM.zmap (Work.ANALYTIC.zeroSlice S)
      = Work.ATOM.zmap (λ_ S).inv ≫ Work.ATOM.zmap (zeroPt ▷ S) := by
    rw [Work.ANALYTIC.zeroSlice, Work.ATOM.zmap_comp_zfree]
  calc (λ_ (Work.ATOM.zfree S)).inv ≫ (Work.ANALYTIC.ePointZ 0 ▷ Work.ATOM.zfree S)
      = ((λ_ (Work.ATOM.zfree S)).inv ≫ (Work.ATOM.unitIso.hom ▷ Work.ATOM.zfree S))
          ≫ (Work.ATOM.zmap zeroPt ▷ Work.ATOM.zfree S)
          ≫ (LightCondensed.P_proj ▷ Work.ATOM.zfree S) := by
        rw [h4]; simp only [Category.assoc]
    _ = (Work.ATOM.zmap (λ_ S).inv ≫ (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).inv)
          ≫ (Work.ATOM.zmap zeroPt ▷ Work.ATOM.zfree S)
          ≫ (LightCondensed.P_proj ▷ Work.ATOM.zfree S) := by
        rw [h1]
    _ = Work.ATOM.zmap (λ_ S).inv
          ≫ ((Work.ATOM.zfreeTensorIso Work.ATOM.pt S).inv
              ≫ (Work.ATOM.zmap zeroPt ▷ Work.ATOM.zfree S))
          ≫ (LightCondensed.P_proj ▷ Work.ATOM.zfree S) := by
        simp only [Category.assoc]
    _ = Work.ATOM.zmap (λ_ S).inv
          ≫ (Work.ATOM.zmap (zeroPt ▷ S)
              ≫ (Work.ATOM.zfreeTensorIso LightProfinite.NatUnionInfty S).inv)
          ≫ (LightCondensed.P_proj ▷ Work.ATOM.zfree S) := by
        rw [← h3]
    _ = Work.ATOM.zmap (Work.ANALYTIC.zeroSlice S) ≫ Work.ATOM.EA S := by
        rw [h2, Work.ATOM.EA]; simp only [Category.assoc]

end Work.ANALYTIC
