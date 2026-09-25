/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleNorm

/-!
# The content of a principal idèle is one

The **content** `|x|` of an idèle `x` of a number field `K` is the product of the normalized
local absolute values of its components (`NK.GlobalCFT.Idele.abs`).  For the principal idèle
`(k)ᵥ` attached to `k ∈ Kˣ` this product is the product formula
`∏_v |k|_v = 1`, so the diagonal embedding `Kˣ → 𝕀 K` lands in the subgroup `𝕀¹ K` of idèles
of content `1`.

The main work is bookkeeping: `Place K` is the disjoint union of the archimedean places
`InfinitePlace K` and the nonarchimedean places `HeightOneSpectrum (𝓞 K)`, and the `finprod`
over a sum type has to be split into the `finprod` over the two summands
(`finprod_sum_of_finiteSupport`, `finprod_place`).  After that the two factors are respectively
`∏_w w k ^ w.mult` (Mathlib's `InfinitePlace.prod_eq_abs_norm`) and
`∏ᶠ_w w k` (Mathlib's `FinitePlace.prod_eq_inv_abs_norm`), whose product is one by
`NumberField.prod_abs_eq_one`.

## Main results

* `NK.GlobalCFT.IdeleNorm.globalCFT_abs_principalIdele`: `|(k)ᵥ| = 1` for every `k ∈ Kˣ`.
-/

set_option autoImplicit false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.IdeleNorm

/-- The product over a sum type of a function with finite multiplicative support splits as the
product of the products over the two summands. -/
theorem finprod_sum_of_finiteSupport {α β M : Type*} [CommMonoid M] (f : α ⊕ β → M)
    (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ x, f x = (∏ᶠ a, f (Sum.inl a)) * ∏ᶠ b, f (Sum.inr b) := by
  have hd : Disjoint (Set.range (Sum.inl : α → α ⊕ β)) (Set.range (Sum.inr : β → α ⊕ β)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact Sum.inl_ne_inr hb.symm
  have h := finprod_mem_union' (f := f) hd
      (hf.subset Set.inter_subset_right) (hf.subset Set.inter_subset_right)
  rw [Set.range_inl_union_range_inr, finprod_mem_univ] at h
  rw [finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective] at h
  exact h

/-- The places of a number field are the disjoint union of the archimedean and the
nonarchimedean places, so a `finprod` over the places splits accordingly. -/
theorem finprod_place {K : Type*} [Field K] [NumberField K] {M : Type*} [CommMonoid M]
    (f : Place K → M) (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ v : Place K, f v =
      (∏ᶠ w : InfinitePlace K, f (Place.ofInfinite w)) *
      ∏ᶠ q : HeightOneSpectrum (𝓞 K), f (Place.ofFinite q) :=
  finprod_sum_of_finiteSupport f hf

/-- **The content of a principal idèle is `1`**: the diagonal embedding `Kˣ → 𝕀 K` lands in the
subgroup `𝕀¹ K` of idèles of content one.  This is the product formula for number fields. -/
theorem globalCFT_abs_principalIdele {K : Type*} [Field K] [NumberField K] (x : Kˣ) :
    NK.GlobalCFT.Idele.abs K (NK.GlobalCFT.Idele.principalIdele K x) = 1 := by
  rw [Idele.abs_apply]
  set g : Place K → ℝˣ := fun v => Idele.localAbs K v (Idele.principalIdele K x v)
  have hg : (Function.mulSupport g).Finite := by
    have h := Idele.localAbs_eq_one_eventually (Idele.principalIdele K x)
    rw [Filter.eventually_cofinite] at h
    simpa [g, Function.mulSupport] using h
  have hgR : (Function.mulSupport (fun v : Place K => ((g v : ℝˣ) : ℝ))).Finite := by
    refine hg.subset ?_
    intro v hv
    simp only [Function.mem_mulSupport] at hv ⊢
    intro h
    exact hv (by rw [h]; rfl)
  have hinf : ∀ w : InfinitePlace K,
      ((g (Place.ofInfinite w) : ℝˣ) : ℝ) = w (x : K) ^ w.mult := by
    intro w
    rw [show g (Place.ofInfinite w) =
        Idele.localAbs K (Place.ofInfinite w) (Idele.principalIdele K x (Place.ofInfinite w))
        from rfl]
    rw [Idele.principalIdele_apply, Idele.localAbs_ofInfinite]
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    congr 1
    simpa [NumberField.InfinitePlace.Completion.algebraMap_apply] using
      (NumberField.InfinitePlace.Completion.norm_coe (v := w) (WithAbs.toAbs w.1 (x : K)))
  have hfin : ∀ q : HeightOneSpectrum (𝓞 K),
      ((g (Place.ofFinite q) : ℝˣ) : ℝ) =
        NumberField.HeightOneSpectrum.adicAbv K q (x : K) := by
    intro q
    rw [show g (Place.ofFinite q) =
        Idele.localAbs K (Place.ofFinite q) (Idele.principalIdele K x (Place.ofFinite q))
        from rfl]
    rw [Idele.principalIdele_apply, Idele.localAbs_ofFinite]
    simp only [Units.val_mk0, Units.coe_map]
    change ‖(algebraMap K (q.adicCompletion K) (x : K))‖ =
      NumberField.HeightOneSpectrum.adicAbv K q (x : K)
    rw [NumberField.FinitePlace.norm_def,
      Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
    rfl
  have hfinprod : (∏ᶠ q : HeightOneSpectrum (𝓞 K),
        NumberField.HeightOneSpectrum.adicAbv K q (x : K))
      = ∏ᶠ w : FinitePlace K, w (x : K) := by
    rw [← finprod_comp_equiv (NumberField.FinitePlace.equivHeightOneSpectrum)
        (f := fun q : HeightOneSpectrum (𝓞 K) =>
          NumberField.HeightOneSpectrum.adicAbv K q (x : K))]
    refine finprod_congr (fun w => ?_)
    rw [NumberField.FinitePlace.equivHeightOneSpectrum_apply,
      ← NumberField.FinitePlace.norm_embedding (v := FinitePlace.maximalIdeal w) (x := (x : K)),
      NumberField.FinitePlace.norm_embedding_eq]
  apply Units.ext
  rw [Units.val_one]
  rw [show ((finprod g : ℝˣ) : ℝ) = ∏ᶠ (i : Place K), ((g i : ℝˣ) : ℝ) from
    MonoidHom.map_finprod_of_preimage_one (Units.coeHom ℝ) (fun y hy => Units.ext hy) g]
  rw [finprod_place (f := fun v : Place K => ((g v : ℝˣ) : ℝ)) hgR]
  rw [finprod_congr hinf, finprod_congr hfin]
  rw [finprod_eq_prod_of_fintype, hfinprod]
  exact NumberField.prod_abs_eq_one (Units.ne_zero x)

end NK.GlobalCFT.IdeleNorm
