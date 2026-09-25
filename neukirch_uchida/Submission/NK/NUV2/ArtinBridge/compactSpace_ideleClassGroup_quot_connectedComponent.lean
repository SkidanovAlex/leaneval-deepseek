/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup

/-!
# `C_K ⧸ C_K⁰` is compact

For a number field `K` the idèle class group `C_K = 𝕀 K ⧸ Kˣ` is *not* compact: the content
`|·| : C_K →* ℝˣ` is unbounded.  But the connected component of the identity `C_K⁰` contains the
whole archimedean direction: for every infinite place `w` of `K` and every `r > 0` the idèle which
is `c` at `w` (an element of `w.Completionˣ` with `‖c‖ = r`) and `1` everywhere else has

* content `|·| = r^{w.mult}`, and
* class in the connected component `C_K⁰`, because `r ↦ mk (scaleIdele w cᵣ)` is a continuous map
  from the connected space `{r : ℝ // 0 < r}` whose value at `r = 1` is `1`.

Consequently `|C_K⁰| = ℝ_{>0} = |C_K|` and therefore

`C_K = ker |·| ⊔ C_K⁰ = C¹_K · C_K⁰`,

so `C_K ⧸ C_K⁰` is a continuous image of the **compact** norm-one idèle class group
`C¹_K = ker |·|` (`globalCFT_compactSpace_normOneClassGroup`), hence compact.

## Main result

* `NK.NUV2.ArtinBridge.compactSpace_ideleClassGroup_quot_connectedComponent`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open Classical

noncomputable section

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT

/-! ## Generalities: a quotient of a compact subgroup -/

/-- If a topological abelian group is the product of a compact subgroup `K` and a subgroup `H`,
then the quotient `G ⧸ H` is compact: it is a continuous image of `K`. -/
theorem compactSpace_quotient_of_sup_eq_top {G : Type*} [CommGroup G] [TopologicalSpace G]
    (H K : Subgroup G) [CompactSpace K] (h : K ⊔ H = ⊤) : CompactSpace (G ⧸ H) := by
  have hsurj : Function.Surjective (fun k : K => (QuotientGroup.mk (k : G) : G ⧸ H)) := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨k, hk, hh, hhh, hkheq⟩ := Subgroup.mem_sup.mp (h ▸ Subgroup.mem_top g)
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [← hkheq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff hh).mpr hhh, mul_one]
  rw [← isCompact_univ_iff]
  have hrange : (Set.univ : Set (G ⧸ H)) = Set.range (fun k : K => (QuotientGroup.mk (k : G))) := by
    rw [eq_comm]
    exact Set.eq_univ_of_forall fun z => by obtain ⟨k, hk⟩ := hsurj z; exact ⟨k, hk⟩
  have hcont : Continuous (fun k : K => (QuotientGroup.mk (k : G) : G ⧸ H)) :=
    QuotientGroup.continuous_mk.comp continuous_subtype_val
  rw [hrange, ← Set.image_univ]
  exact (isCompact_univ_iff.mpr (inferInstance : CompactSpace K)).image hcont

namespace ConnectedComponent

variable {K : Type*} [Field K] [NumberField K]

/-! ## Positivity of the content -/

/-- Every local absolute value is strictly positive as a real number. -/
lemma localAbs_pos (v : Place K) (y : (Place.localField K v)ˣ) :
    0 < ((Idele.localAbs K v y : ℝˣ) : ℝ) := by
  cases v with
  | inl w =>
    rw [Idele.localAbs_ofInfinite]
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact pow_pos (norm_pos_iff.mpr (Units.ne_zero y)) _
  | inr q =>
    rw [Idele.localAbs_ofFinite]
    rw [Units.val_mk0]
    exact norm_pos_iff.mpr (Units.ne_zero y)

/-- The content of an idèle is strictly positive. -/
lemma idele_abs_pos (x : Idele K) : 0 < ((Idele.abs K x : ℝˣ) : ℝ) := by
  have hs : (Function.mulSupport (fun v : Place K => Idele.localAbs K v (x v))).Finite :=
    Filter.eventually_cofinite.mp (Idele.localAbs_eq_one_eventually x)
  have hprod : ((Idele.abs K x : ℝˣ) : ℝ)
      = ∏ v ∈ hs.toFinset, ((Idele.localAbs K v (x v) : ℝˣ) : ℝ) := by
    rw [Idele.abs_apply, finprod_eq_prod_of_mulSupport_subset_of_finite _ (fun v hv => hv) hs]
    exact map_prod (Units.coeHom ℝ) _ _
  rw [hprod]
  exact Finset.prod_pos (fun v _ => localAbs_pos v (x v))

/-- The content of an idèle class is strictly positive. -/
lemma class_abs_pos (x : IdeleClassGroup K) : 0 < ((IdeleClassGroup.abs K x : ℝˣ) : ℝ) := by
  obtain ⟨x₀, rfl⟩ := IdeleClassGroup.mk_surjective K x
  rw [IdeleClassGroup.abs_mk]
  exact idele_abs_pos x₀

/-! ## Units of an archimedean completion with prescribed norm -/

/-- An element of the completion `w.Completion` of `K` at the infinite place `w` whose norm is
`|r|`.  At a real place it is the image of `r` under the identification `w.Completion ≃ᵢ ℝ`, at a
complex place the image of the real number `r` under `w.Completion ≃ᵢ ℂ`. -/
noncomputable def scalePoint (w : InfinitePlace K) (r : ℝ) : w.Completion :=
  if h : w.IsReal then
    (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm r
  else
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm ((r : ℝ) : ℂ)

lemma norm_scalePoint (w : InfinitePlace K) (r : ℝ) : ‖scalePoint (K := K) w r‖ = |r| := by
  rw [scalePoint]
  by_cases h : w.IsReal
  · rw [dif_pos h]
    have h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal h) (0 : w.Completion) = 0 := by
      change (InfinitePlace.Completion.ringEquivRealOfIsReal h) 0 = 0
      exact map_zero _
    have hs0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm (0 : ℝ) = 0 :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal h).injective
        (by rw [IsometryEquiv.apply_symm_apply, h0])
    rw [← Real.norm_eq_abs]
    exact Isometry.norm_map_of_map_zero
      ((InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm).isometry_toFun hs0 r
  · rw [dif_neg h]
    set e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp h) with he
    have h0 : e (0 : w.Completion) = 0 := by
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp h)) 0 = 0
      exact map_zero _
    have hs0 : e.symm (0 : ℂ) = 0 := e.injective (by rw [IsometryEquiv.apply_symm_apply, h0])
    have hnorm := Isometry.norm_map_of_map_zero e.symm.isometry_toFun hs0 ((r : ℝ) : ℂ)
    calc ‖e.symm ((r : ℝ) : ℂ)‖ = ‖((r : ℝ) : ℂ)‖ := hnorm
      _ = |r| := RCLike.norm_ofReal r

lemma scalePoint_one (w : InfinitePlace K) : scalePoint (K := K) w 1 = 1 := by
  rw [scalePoint]
  by_cases h : w.IsReal
  · rw [dif_pos h]
    change (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm (1 : ℝ) = 1
    exact map_one _
  · rw [dif_neg h]
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm ((1 : ℝ) : ℂ) = 1
    rw [show ((1 : ℝ) : ℂ) = 1 from Complex.ofReal_one]
    exact map_one _

lemma continuous_scalePoint (w : InfinitePlace K) : Continuous (scalePoint (K := K) w) := by
  by_cases h : w.IsReal
  · have hfun : scalePoint (K := K) w = fun r : ℝ =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm r := by
      funext r; rw [scalePoint, dif_pos h]
    rw [hfun]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm.continuous
  · have hfun : scalePoint (K := K) w = fun r : ℝ =>
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm ((r : ℝ) : ℂ) := by
      funext r; rw [scalePoint, dif_neg h]
    rw [hfun]
    exact ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm.continuous).comp Complex.continuous_ofReal

/-- The unit of `w.Completionˣ` with underlying element `scalePoint w r`. -/
noncomputable def scaleUnit (w : InfinitePlace K) (r : ℝ) (hr : r ≠ 0) : w.Completionˣ :=
  Units.mk0 (scalePoint (K := K) w r)
    (by rw [← norm_ne_zero_iff, norm_scalePoint, abs_ne_zero]; exact hr)

lemma val_scaleUnit (w : InfinitePlace K) (r : ℝ) (hr : r ≠ 0) :
    ((scaleUnit (K := K) w r hr : w.Completionˣ) : w.Completion) = scalePoint (K := K) w r :=
  Units.val_mk0 _

lemma norm_scaleUnit (w : InfinitePlace K) (r : ℝ) (hr : r ≠ 0) :
    ‖((scaleUnit (K := K) w r hr : w.Completionˣ) : w.Completion)‖ = |r| := by
  rw [val_scaleUnit, norm_scalePoint]

lemma scaleUnit_one (w : InfinitePlace K) (hr : (1 : ℝ) ≠ 0) :
    scaleUnit (K := K) w 1 hr = 1 := by
  apply Units.ext
  rw [val_scaleUnit, scalePoint_one, Units.val_one]

lemma continuous_scaleUnit (w : InfinitePlace K) :
    Continuous (fun r : {r : ℝ // 0 < r} =>
      scaleUnit (K := K) w (r : ℝ) (ne_of_gt r.2)) := by
  rw [Units.continuous_iff]
  constructor
  · have h1 : (Units.val ∘ fun r : {r : ℝ // 0 < r} =>
        scaleUnit (K := K) w (r : ℝ) (ne_of_gt r.2))
        = (fun r : {r : ℝ // 0 < r} => scalePoint (K := K) w (r : ℝ)) := by
      funext r; rw [Function.comp_apply, val_scaleUnit]
    rw [h1]
    exact (continuous_scalePoint w).comp continuous_subtype_val
  · have h1 : (fun r : {r : ℝ // 0 < r} =>
        ↑((scaleUnit (K := K) w (r : ℝ) (ne_of_gt r.2))⁻¹ : w.Completionˣ))
        = (fun r : {r : ℝ // 0 < r} => (scalePoint (K := K) w (r : ℝ))⁻¹) := by
      funext r; rw [Units.val_inv_eq_inv_val, val_scaleUnit]
    rw [h1]
    refine Continuous.inv₀ ((continuous_scalePoint w).comp continuous_subtype_val) (fun r => ?_)
    rw [← norm_ne_zero_iff, norm_scalePoint, abs_ne_zero]
    exact ne_of_gt r.2

/-! ## The idèle which is non-trivial at a single archimedean place -/

/-- The idèle which equals `c` at the infinite place `w` and `1` at every other place, as an
element of the restricted product. -/
noncomputable def scaleIdeleFun (w : InfinitePlace K) (c : w.Completionˣ) :
    Πʳ v : Place K, [(Place.localField K v)ˣ, (Place.localUnits K v : Set ((Place.localField K v)ˣ))] :=
  RestrictedProduct.structureMap (fun v : Place K => (Place.localField K v)ˣ)
    (fun v : Place K => (Place.localUnits K v : Set ((Place.localField K v)ˣ))) Filter.cofinite
    (Function.update (fun v : Place K => (1 : ↥(Place.localUnits K v)))
      (Place.ofInfinite w)
      (⟨c, Place.mem_localUnits_ofInfinite⟩ : ↥(Place.localUnits K (Place.ofInfinite w))))

/-- The same idèle, as an element of the idèle group. -/
noncomputable def scaleIdele (w : InfinitePlace K) (c : w.Completionˣ) : Idele K :=
  scaleIdeleFun (K := K) w c

lemma scaleIdeleFun_apply_ofInfinite (w : InfinitePlace K) (c : w.Completionˣ) :
    scaleIdeleFun (K := K) w c (Place.ofInfinite w) = c := by
  rw [scaleIdeleFun, RestrictedProduct.structureMap_apply]
  show (↑(Function.update (fun v : Place K => (1 : ↥(Place.localUnits K v))) (Place.ofInfinite w)
    (⟨c, Place.mem_localUnits_ofInfinite⟩ : ↥(Place.localUnits K (Place.ofInfinite w)))
      (Place.ofInfinite w)) : (Place.localField K (Place.ofInfinite w))ˣ) = c
  rw [Function.update_self]

lemma scaleIdeleFun_apply_of_ne (w : InfinitePlace K) (c : w.Completionˣ)
    {v : Place K} (hv : v ≠ Place.ofInfinite w) :
    scaleIdeleFun (K := K) w c v = 1 := by
  rw [scaleIdeleFun, RestrictedProduct.structureMap_apply]
  show (↑(Function.update (fun v : Place K => (1 : ↥(Place.localUnits K v))) (Place.ofInfinite w)
    (⟨c, Place.mem_localUnits_ofInfinite⟩ : ↥(Place.localUnits K (Place.ofInfinite w))) v)
    : (Place.localField K v)ˣ) = 1
  rw [Function.update_of_ne hv]
  exact Subgroup.coe_one _

lemma scaleIdele_apply_ofInfinite (w : InfinitePlace K) (c : w.Completionˣ) :
    (scaleIdele (K := K) w c : Idele K) (Place.ofInfinite w) = c := by
  change scaleIdeleFun (K := K) w c (Place.ofInfinite w) = c
  exact scaleIdeleFun_apply_ofInfinite w c

lemma scaleIdele_apply_of_ne (w : InfinitePlace K) (c : w.Completionˣ)
    {v : Place K} (hv : v ≠ Place.ofInfinite w) :
    (scaleIdele (K := K) w c : Idele K) v = 1 := by
  change scaleIdeleFun (K := K) w c v = 1
  exact scaleIdeleFun_apply_of_ne w c hv

lemma scaleIdeleFun_one (w : InfinitePlace K) : scaleIdeleFun (K := K) w 1 = 1 := by
  ext v
  by_cases hv : v = Place.ofInfinite w
  · subst hv
    rw [scaleIdeleFun_apply_ofInfinite, RestrictedProduct.one_apply]
  · rw [scaleIdeleFun_apply_of_ne w 1 hv, RestrictedProduct.one_apply]

lemma scaleIdele_one (w : InfinitePlace K) : scaleIdele (K := K) w 1 = 1 := by
  change scaleIdeleFun (K := K) w 1 = 1
  exact scaleIdeleFun_one w

lemma abs_scaleIdele (w : InfinitePlace K) (c : w.Completionˣ) :
    Idele.abs K (scaleIdele (K := K) w c) = Idele.localAbs K (Place.ofInfinite w) c := by
  have h := Idele.abs_apply (K := K) (scaleIdele (K := K) w c)
  rw [h]
  rw [finprod_eq_single (fun v => Idele.localAbs K v ((scaleIdele (K := K) w c : Idele K) v))
    (Place.ofInfinite w)]
  · rw [scaleIdele_apply_ofInfinite]
  · intro v hv
    rw [scaleIdele_apply_of_ne w c hv, map_one]

lemma continuous_scaleIdeleFun (w : InfinitePlace K) : Continuous (scaleIdeleFun (K := K) w) := by
  have hg : Continuous (fun c : w.Completionˣ =>
      (⟨c, Place.mem_localUnits_ofInfinite⟩ :
        ↥(Place.localUnits K (Place.ofInfinite w)))) :=
    continuous_id.subtype_mk _
  have hg' : Continuous (fun c : w.Completionˣ =>
      Function.update (fun v : Place K => (1 : ↥(Place.localUnits K v))) (Place.ofInfinite w)
        (⟨c, Place.mem_localUnits_ofInfinite⟩ :
          ↥(Place.localUnits K (Place.ofInfinite w)))) :=
    continuous_const.update _ hg
  have hfun : scaleIdeleFun (K := K) w = fun c : w.Completionˣ =>
      RestrictedProduct.structureMap (fun v : Place K => (Place.localField K v)ˣ)
        (fun v : Place K => (Place.localUnits K v : Set ((Place.localField K v)ˣ))) Filter.cofinite
        (Function.update (fun v : Place K => (1 : ↥(Place.localUnits K v))) (Place.ofInfinite w)
          (⟨c, Place.mem_localUnits_ofInfinite⟩ :
            ↥(Place.localUnits K (Place.ofInfinite w)))) := rfl
  rw [hfun]
  exact (RestrictedProduct.isEmbedding_structureMap (R := fun v : Place K => (Place.localField K v)ˣ)
    (A := fun v : Place K => (Place.localUnits K v : Set ((Place.localField K v)ˣ)))
    (𝓕 := Filter.cofinite)).continuous.comp hg'

lemma continuous_scaleIdele (w : InfinitePlace K) : Continuous (scaleIdele (K := K) w) := by
  change Continuous (scaleIdeleFun (K := K) w)
  exact continuous_scaleIdeleFun w

/-! ## The content of the scaled idèle -/

lemma abs_scaleUnit (w : InfinitePlace K) (r : ℝ) (hr : 0 < r) :
    IdeleClassGroup.abs K
        (IdeleClassGroup.mk K (scaleIdele (K := K) w (scaleUnit (K := K) w r (ne_of_gt hr))))
      = Units.mk0 (r ^ w.mult) (pow_ne_zero _ (ne_of_gt hr)) := by
  have h1 := IdeleClassGroup.abs_mk (K := K)
    (scaleIdele (K := K) w (scaleUnit (K := K) w r (ne_of_gt hr)))
  rw [h1, abs_scaleIdele, Idele.localAbs_ofInfinite]
  refine Units.ext ?_
  have hn : ‖((scaleUnit (K := K) w r (ne_of_gt hr) : w.Completionˣ) : w.Completion)‖ = r := by
    rw [norm_scaleUnit]; exact abs_of_pos hr
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, hn]

/-! ## The scaled idèle lies in the connected component -/

lemma mk_scaleUnit_mem_connectedComponentOfOne (w : InfinitePlace K) (r : ℝ) (hr : 0 < r) :
    IdeleClassGroup.mk K (scaleIdele (K := K) w (scaleUnit (K := K) w r (ne_of_gt hr)))
      ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K) := by
  have hmk : Continuous (IdeleClassGroup.mk K) := by
    change Continuous (QuotientGroup.mk' (Idele.principalSubgroup K))
    rw [QuotientGroup.coe_mk']
    exact QuotientGroup.continuous_mk
  have hcont : Continuous (fun s : {s : ℝ // 0 < s} =>
      IdeleClassGroup.mk K (scaleIdele (K := K) w (scaleUnit (K := K) w (s : ℝ) (ne_of_gt s.2)))) :=
    hmk.comp ((continuous_scaleIdele w).comp (continuous_scaleUnit w))
  haveI : PreconnectedSpace {s : ℝ // 0 < s} :=
    isPreconnected_iff_preconnectedSpace.mp (isPreconnected_Ioi (a := (0 : ℝ)))
  have hpre : IsPreconnected (Set.range (fun s : {s : ℝ // 0 < s} =>
      IdeleClassGroup.mk K (scaleIdele (K := K) w (scaleUnit (K := K) w (s : ℝ) (ne_of_gt s.2))))) :=
    isPreconnected_range hcont
  have hone : (1 : IdeleClassGroup K) ∈ Set.range (fun s : {s : ℝ // 0 < s} =>
      IdeleClassGroup.mk K (scaleIdele (K := K) w (scaleUnit (K := K) w (s : ℝ) (ne_of_gt s.2)))) := by
    refine ⟨⟨1, one_pos⟩, ?_⟩
    show IdeleClassGroup.mk K (scaleIdele (K := K) w (scaleUnit (K := K) w 1 one_ne_zero)) = 1
    rw [scaleUnit_one, scaleIdele_one, map_one]
  exact hpre.subset_connectedComponent hone ⟨⟨r, hr⟩, rfl⟩

/-! ## Decomposition of `C_K` -/

/-- Every class in `C_K` differs from an element of the connected component `C_K⁰` by an element
of `ker |·| = C¹_K`. -/
lemma exists_mem_connectedComponentOfOne_abs_eq (x : IdeleClassGroup K) :
    ∃ g ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K),
      IdeleClassGroup.abs K g = IdeleClassGroup.abs K x := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  set R : ℝ := ((IdeleClassGroup.abs K x : ℝˣ) : ℝ) with hR
  have hRpos : 0 < R := class_abs_pos x
  have hmul : w.mult = 1 ∨ w.mult = 2 := by
    rcases InfinitePlace.isReal_or_isComplex w with h | h
    · exact Or.inl (InfinitePlace.IsReal.mult_eq_one h)
    · exact Or.inr (InfinitePlace.IsComplex.mult_eq_two h)
  obtain ⟨r, hr, hrm⟩ : ∃ r : ℝ, 0 < r ∧ r ^ w.mult = R := by
    rcases hmul with h | h
    · exact ⟨R, hRpos, by rw [h, pow_one]⟩
    · exact ⟨Real.sqrt R, Real.sqrt_pos.mpr hRpos, by rw [h, Real.sq_sqrt (le_of_lt hRpos)]⟩
  refine ⟨IdeleClassGroup.mk K (scaleIdele (K := K) w (scaleUnit (K := K) w r (ne_of_gt hr))),
    mk_scaleUnit_mem_connectedComponentOfOne w r hr, ?_⟩
  rw [abs_scaleUnit w r hr]
  refine Units.ext ?_
  rw [Units.val_mk0]
  exact hrm.trans hR

/-- **`C_K` is generated by its connected component and the norm-one part.** -/
lemma sup_ker_abs_connectedComponentOfOne :
    (IdeleClassGroup.abs K).ker ⊔ Subgroup.connectedComponentOfOne (IdeleClassGroup K) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, hg, hgabs⟩ := exists_mem_connectedComponentOfOne_abs_eq x
  have hmem : x * g⁻¹ ∈ (IdeleClassGroup.abs K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgabs, mul_inv_cancel]
  have hx : x = (x * g⁻¹) * g := by group
  rw [hx]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hg)

/-! ## The norm-one part is compact -/

/-- The kernel of the content is compact: it is a continuous image of the compact norm-one idèle
class group `C¹_K`. -/
lemma compactSpace_ker_abs : CompactSpace ↥((IdeleClassGroup.abs K).ker) := by
  haveI hcomp : CompactSpace
      (Idele.normOne K ⧸ (Idele.principalSubgroup K).subgroupOf (Idele.normOne K)) :=
    IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup (K := K)
  have hmk : Continuous (IdeleClassGroup.mk K) := by
    change Continuous (QuotientGroup.mk' (Idele.principalSubgroup K))
    rw [QuotientGroup.coe_mk']
    exact QuotientGroup.continuous_mk
  let f : Idele.normOne K →* ↥((IdeleClassGroup.abs K).ker) :=
    { toFun := fun y => ⟨IdeleClassGroup.mk K (y : Idele K), by
        rw [MonoidHom.mem_ker, IdeleClassGroup.abs_mk]
        exact Idele.mem_normOne.mp y.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul] }
  have hf : Continuous ⇑f :=
    Continuous.subtype_mk (hmk.comp continuous_subtype_val) (fun y => by
      show IdeleClassGroup.abs K (IdeleClassGroup.mk K (y : Idele K)) = 1
      rw [IdeleClassGroup.abs_mk]
      exact Idele.mem_normOne.mp y.2)
  have hker : (Idele.principalSubgroup K).subgroupOf (Idele.normOne K) ≤ f.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show IdeleClassGroup.mk K (y : Idele K) = 1
    obtain ⟨k, hk⟩ := Idele.mem_principalSubgroup.mp (Subgroup.mem_subgroupOf.mp hy)
    rw [← hk, IdeleClassGroup.mk_apply, QuotientGroup.eq_one_iff]
    exact Idele.mem_principalSubgroup.mpr ⟨k, rfl⟩
  let F : (Idele.normOne K ⧸ (Idele.principalSubgroup K).subgroupOf (Idele.normOne K)) →*
      ↥((IdeleClassGroup.abs K).ker) :=
    QuotientGroup.lift _ f hker
  have hF : Continuous ⇑F := by
    rw [(QuotientGroup.isQuotientMap_mk
      ((Idele.principalSubgroup K).subgroupOf (Idele.normOne K))).continuous_iff]
    have heq : (⇑F ∘ QuotientGroup.mk) = ⇑f := by
      funext y
      exact QuotientGroup.lift_mk' _ hker y
    rw [heq]
    exact hf
  have hsurj : Function.Surjective ⇑F := by
    intro h
    obtain ⟨x₀, hx₀⟩ := IdeleClassGroup.mk_surjective K (h : IdeleClassGroup K)
    have hx₀' : x₀ ∈ Idele.normOne K := by
      rw [Idele.mem_normOne, ← IdeleClassGroup.abs_mk (K := K) x₀, hx₀]
      exact MonoidHom.mem_ker.mp h.2
    refine ⟨QuotientGroup.mk (⟨x₀, hx₀'⟩ : Idele.normOne K), ?_⟩
    apply Subtype.ext
    rw [QuotientGroup.lift_mk' _ hker]
    exact hx₀
  rw [← isCompact_univ_iff]
  have hrange : (Set.univ : Set ↥((IdeleClassGroup.abs K).ker)) = ⇑F '' Set.univ := by
    rw [Set.image_univ, eq_comm]
    exact Set.eq_univ_of_forall fun z => by
      obtain ⟨y, hy⟩ := hsurj z
      exact ⟨y, hy⟩
  rw [hrange]
  exact (isCompact_univ_iff.mpr (inferInstance : CompactSpace
    (Idele.normOne K ⧸ (Idele.principalSubgroup K).subgroupOf (Idele.normOne K)))).image hF

end ConnectedComponent

theorem compactSpace_ideleClassGroup_quot_connectedComponent {K : Type*} [Field K] [NumberField K] :
    CompactSpace (NK.GlobalCFT.IdeleClassGroup K ⧸
      Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K)) := by
  haveI := ConnectedComponent.compactSpace_ker_abs (K := K)
  exact compactSpace_quotient_of_sup_eq_top
    (Subgroup.connectedComponentOfOne (IdeleClassGroup K)) ((IdeleClassGroup.abs K).ker)
    (ConnectedComponent.sup_ker_abs_connectedComponentOfOne (K := K))

end NK.NUV2.ArtinBridge
