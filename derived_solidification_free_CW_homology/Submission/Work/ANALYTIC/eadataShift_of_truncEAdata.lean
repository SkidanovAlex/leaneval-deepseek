import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.EA_shift
import Submission.Work.ATOM.zmap_ext_of_closed_cover
import Submission.Work.ANALYTIC.towerFEAsetup

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! # The `EA`-form of the `S`-point of `T ≫ F`

This file proves `Work.ANALYTIC.eadataShift_of_truncEAdata`: if `F : P ⊗ ∏^bnd ℤ ⟶ ∏^bnd ℤ` has
the truncations as its null family (`Work.ANALYTIC.IsTruncEAdata F`), then applying `EA S` to the
`S`-point of `F` precomposed with `(1 - S) ⊗ id` gives the morphism classified by the element
`(m,(k,s)) ↦ x_m(s)·[k = m]`.

The two auxiliary ingredients are

* `Work.ANALYTIC.homFreeEquiv_sub'`: additivity of the classification `ℤ[S] ⟶ M ≃ M(S)` for
  differences (needed because `EA_shift` rewrites `EA S ≫ (1 - S)⊗id` as `(𝟙 - ℤ[shift]) ≫ EA S`);
* `Work.ANALYTIC.truncDataElem_sub_shift`: the purely element-theoretic identity comparing the
  truncation data with its shift-pullback. -/

/-! ## Additivity of `homFreeEquiv` for differences -/

/-- The classification `Hom(ℤ[S], M) ≃ M(S)` of `Work.ATOM.homFreeEquiv` commutes with
subtraction (the `Work.ATOM`-flavoured companion of `Work.ANALYTIC.freeHomEquiv_add`). -/
theorem homFreeEquiv_sub' (S : LightProfinite.{0}) (A : LightCondAb)
    (a b : Work.ATOM.zfree S ⟶ A) :
    Work.ATOM.homFreeEquiv S A (a - b)
      = Work.ATOM.homFreeEquiv S A a - Work.ATOM.homFreeEquiv S A b := by
  have h : a - b = a + (-1 : ℤ) • b := by rw [neg_one_zsmul, sub_eq_add_neg]
  rw [h, homFreeEquiv_add', homFreeEquiv_zsmul', neg_one_zsmul, sub_eq_add_neg]

/-! ## The element identity: the truncation data vs. its shift-pullback -/

/-- **The element identity behind `EA_shift` on the truncation data.**

For `x ∈ ∏^bnd ℤ(S)`, the difference of the truncation data `truncDataElem S x` (whose `m`-th
component is `(k,s) ↦ x_m(s)·(1 - ∏_{i≤m}(1 - δ_i(k)))`, i.e. `x_m(s)·[k ≤ m]`) and its pullback
along `LightProfinite.shift ▷ S : (ℕ∪{∞}) × S ⟶ (ℕ∪{∞}) × S`, `(k,s) ↦ (k+1,s)`, is the element
`coordTimesDeltaAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S)`, whose `m`-th component is
`(k,s) ↦ x_m(s)·[k = m]`.

The pointwise content is the identity
`(1 - ∏_{i≤m}(1 - δ_i(k))) - (1 - ∏_{i≤m}(1 - δ_i(k+1))) = deltaFun m k` for `k : ℕ` (and `0` for
`k = ∞`): the product `∏_{i≤m}(1 - δ_i(k))` is `0` when `k ≤ m` and `1` otherwise. -/
theorem truncDataElem_sub_shift (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    truncDataElem S x -
        boundedSeq.obj.map (LightProfinite.shift ▷ S).op (truncDataElem S x)
      = coordTimesDeltaAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S) := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  -- evaluate both sides on the `m`-th component at the point `p`
  rw [show ((truncDataElem S x -
        boundedSeq.obj.map (LightProfinite.shift ▷ S).op
          (truncDataElem S x)).1 m) p
      = ((truncDataElem S x).1 m) p
        - ((boundedSeq.obj.map (LightProfinite.shift ▷ S).op
            (truncDataElem S x)).1 m) p
      from map_sub (evHomBS ((ℕ∪{∞}) ⊗ S) m p) _ _]
  rw [boundedSeq_map_apply, truncDataElem_val, truncDataElem_val,
    show (LightProfinite.shift ▷ S) p = (LightProfinite.shift p.1, p.2) from rfl]
  rw [show (coordTimesDeltaAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S)).1 m p
      = (x.1 m) p.2 * deltaFun m p.1 from rfl]
  rw [← mul_sub]
  congr 1
  -- the arithmetic core: `(1 - P k) - (1 - P (k+1)) = δ_m k`
  have hp : ∀ j : ℕ, (∏ i ∈ Finset.range (m+1),
      (1 - deltaFun i ((j : ℕ) : OnePoint ℕ))) = if j ≤ m then 0 else 1 := by
    intro j
    by_cases hk : j ≤ m
    · rw [if_pos hk]
      refine Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) ?_
      rw [deltaFun_at]
      ring
    · rw [if_neg hk]
      refine Finset.prod_eq_one (fun i hi => ?_)
      have hik : i ≠ j := by
        have := Finset.mem_range.mp hi
        omega
      rw [deltaFun_eq, if_neg (fun h => hik (OnePoint.coe_eq_coe.mp h).symm), sub_zero]
  have hpinf : (∏ i ∈ Finset.range (m+1),
      (1 - deltaFun i (∞ : OnePoint ℕ))) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [deltaFun_infty]
    ring
  have hsinf : LightProfinite.shift (∞ : OnePoint ℕ) = (∞ : OnePoint ℕ) := rfl
  have hssome : ∀ k : ℕ,
      LightProfinite.shift ((k : ℕ) : OnePoint ℕ) = ((k+1 : ℕ) : OnePoint ℕ) := fun k => rfl
  refine OnePoint.rec ?_ ?_ p.1
  · rw [hpinf, hsinf, hpinf, deltaFun_infty]
    ring
  · intro k
    rw [hssome k, hp k, hp (k+1), deltaFun_eq]
    by_cases hkm : k = m
    · subst hkm
      rw [if_pos (le_refl k), if_neg (by omega : ¬ k + 1 ≤ k),
        if_pos (OnePoint.coe_eq_coe.mpr rfl)]
      ring
    · have hne : ¬ ((k : OnePoint ℕ) = (m : OnePoint ℕ)) :=
        fun h => hkm (OnePoint.coe_eq_coe.mp h)
      rw [if_neg hne]
      by_cases h : k ≤ m
      · have h2 : k + 1 ≤ m := by omega
        rw [if_pos h, if_pos h2]; ring
      · rw [if_neg h, if_neg (by omega : ¬ k + 1 ≤ m)]; ring

/-! ## The main theorem -/

/-- **The `EA`-form of the `S`-point of `T ≫ F`.**  If `F`'s null family is the truncations
(`Work.ANALYTIC.IsTruncEAdata F`), then applying `EA S` to the `S`-point `θF_S(x)` precomposed with
`oneMinusShift ▷ ℤ[S]` gives the morphism classified by
`Work.ANALYTIC.coordTimesDeltaAt ((ℕ∪∞) ⊗ S) (pullbackX S x) (fstNS S)`, i.e. the element with
`m`-th component `(k,s) ↦ x_m(s)·[k = m]`.

Proof ingredients: `Work.ANALYTIC.EA_shift` (proved, in `Submission.Work.ANALYTIC.EA_shift`) turns
`EA S ≫ (oneMinusShift ▷ ℤ[S])` into `(𝟙 - zmap (shift ▷ S)) ≫ EA S`; `IsTruncEAdata` identifies
`EA S ≫ θF_S(x)` with the morphism classified by `truncDataElem S x`; naturality of `homFreeEquiv`
(`Work.ATOM.homFreeEquiv_zmap`, `Work.ANALYTIC.freeHomEquiv_naturality`) turns `(zmap (shift ▷ S))`
into the pullback of the element along `shift ▷ S`; then the pointwise identity
`(1 - ∏_{i≤m}(1-δ_i(k))) - (1 - ∏_{i≤m}(1-δ_i(k+1))) = deltaFun m k` (`k = ∞` giving `0`)
identifies the difference with `coordTimesDeltaAt`'s coefficient, and `pullbackX S x` is the
pullback of `x` under the second projection.  Both sides are morphisms `ℤ[(ℕ∪∞) × S] ⟶ ∏^bnd ℤ`,
so it suffices to compare the classified elements pointwise (or to go through
`Work.ATOM.homFreeEquiv`). -/
theorem eadataShift_of_truncEAdata
    (F : Work.ATOM.tmul LightCondensed.P Work.ANALYTIC.boundedSeq ⟶
      Work.ANALYTIC.boundedSeq)
    (hF : Work.ANALYTIC.IsTruncEAdata F) : Work.ANALYTIC.EAdataShift F := by
  intro S x
  -- Step 1: `EA_shift` moves `(1 - S) ⊗ id` past `EA S`, then `IsTruncEAdata` classifies
  -- `EA S ≫ θF_S(x)`.
  have h1 : Work.ATOM.EA S ≫
      (MonoidalCategory.whiskerRight LightCondensed.oneMinusShift (Work.ATOM.zfree S) ≫
        LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S
          ((MonoidalClosed.curry F).hom.app (Opposite.op S) x))
      = (𝟙 (Work.ATOM.zfree (Work.ATOM.NS S)) -
          Work.ATOM.zmap (LightProfinite.shift ▷ S)) ≫
        (Work.ATOM.EA S ≫
          LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S
            ((MonoidalClosed.curry F).hom.app (Opposite.op S) x)) := by
    rw [← Category.assoc, Work.ANALYTIC.EA_shift S, Category.assoc]
  rw [h1, hF S x]
  -- Step 2: compare the classified elements.
  apply (Work.ATOM.homFreeEquiv (Work.ATOM.NS S) boundedSeq).injective
  rw [Preadditive.sub_comp, Category.id_comp, homFreeEquiv_sub', Work.ATOM.homFreeEquiv_zmap,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  -- Step 3: the element identity.
  exact truncDataElem_sub_shift S x

end

end Work.ANALYTIC
