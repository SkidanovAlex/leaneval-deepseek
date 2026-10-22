import Mathlib
import Submission.Work.ATOM.ZS.Topo.Maps

namespace Work.ATOM.ZS

open CategoryTheory MonoidalCategory LightCondensed

/-- The map `ι ▷ S : pt ⊗ S ⟶ (ℕ∪{∞}) ⊗ S` is the inclusion of the "slice at infinity":
concretely `p ↦ (∞, p.2)`.

This is a pointwise computation: `LightProfinite` carries the cartesian monoidal structure (so `⊗`
is the product of light profinite sets), and the two facets of `ι ▷ S` are computed by
`CartesianMonoidalCategory.whiskerRight_fst` / `_snd`, which say that the first coordinate of
`(ι ▷ S) p` is `ι p.1 = ∞` and the second is `p.2`. -/
lemma whiskerRight_ι_apply (S : LightProfinite.{0}) (p : ↥((LightProfinite.of PUnit.{1}) ⊗ S)) :
    (MonoidalCategory.whiskerRight LightCondensed.ι S) p =
      Work.ATOM.mkNS S OnePoint.infty p.2 := by
  refine Prod.ext ?_ ?_
  · have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst LightCondensed.ι S) p
    rw [ConcreteCategory.comp_apply] at h
    exact h
  · have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd LightCondensed.ι S) p
    rw [ConcreteCategory.comp_apply] at h
    exact h

/-- **`pr₂` and `ẽ` agree on the slice `{∞} × S`.**  Both composites
`whiskerRight ι S ≫ pr₂N` and `whiskerRight ι S ≫ ePred` send `p` to `p.2`, because
`ẽ(∞,x) = x` (`Work.ATOM.ePred_infty`) while `pr₂N` is the second projection. -/
lemma whiskerRight_ι_comp_ePred_eq_pr₂N (S : LightProfinite.{0}) [Infinite S] :
    MonoidalCategory.whiskerRight LightCondensed.ι S ≫ Work.ATOM.ePred S =
      MonoidalCategory.whiskerRight LightCondensed.ι S ≫ Work.ATOM.pr₂N S := by
  apply ConcreteCategory.hom_ext
  intro p
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [whiskerRight_ι_apply S p, Work.ATOM.ePred_infty]
  rfl

/-- **The vanishing of `[pr₂] − [ẽ]` on `{∞} × S`.**  The section
`(k,x) ↦ [x] - [ẽ(k,x)]` of `ℤ[S]` over `(ℕ∪{∞}) × S` vanishes on `{∞} × S` (there `ẽ(∞,x) = x`),
so it descends along `Work.ATOM.EA S` to the morphism `F : P ⊗ ℤ[S] ⟶ ℤ̃[S]` of REFS/03 §1.
Route: `Work.ATOM.ePred_infty` computes `whiskerRight ι S ≫ ePred = pr₂`-composite, so the
composite with `zmap` is `0`; use `ConcreteCategory.hom_ext`. -/
theorem F_vanishing (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S) ≫
      ((Work.ATOM.zmap (Work.ATOM.pr₂N S) - Work.ATOM.zmap (Work.ATOM.ePred S)) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀) = 0 := by
  have hA := whiskerRight_ι_comp_ePred_eq_pr₂N S
  -- `zmap` is functorial, so the outer composite vanishes before `qred` is applied.
  have h0 : Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S) ≫
      (Work.ATOM.zmap (Work.ATOM.pr₂N S) - Work.ATOM.zmap (Work.ATOM.ePred S)) = 0 := by
    rw [Preadditive.comp_sub, ← Functor.map_comp, ← Functor.map_comp, hA, sub_self]
  rw [← Category.assoc, h0, Limits.zero_comp]

end Work.ATOM.ZS
