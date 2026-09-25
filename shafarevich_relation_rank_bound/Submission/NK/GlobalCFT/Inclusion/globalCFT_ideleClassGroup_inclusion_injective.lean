/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.FieldTheory.Galois.iSup_decompositionSubgroup_eq_top
import Submission.NK.GlobalCFT.Norm.NormTransAux
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective

/-!
# Injectivity of the inclusion of idèle class groups

For a finite extension `L / K` of number fields and a monoid homomorphism `phi : 𝕀 K →* 𝕀 L`
whose `w`-component is the local embedding `K_{u w}ˣ →* L_wˣ`, the induced map on idèle class
groups `C_K →* C_L` is **injective**.

The mathematical content is the standard fact that the inclusion `C_K → C_L` has trivial
kernel: if an idèle `x` of `K` becomes principal in `L`, then it is already principal in `K`.
Writing `phi x = (y)` for `y ∈ Lˣ`, this reduces to the "local global" statement

  `y ∈ Lˣ` lies in the image of every local field `K_v` inside `L_w` (for all places `v`, `w | v`)
  only if `y ∈ Kˣ`,

which is proved as `globalCFT_mem_base_of_localUnits` below via Čebotarev's theorem in the form of
`NK.FieldTheory.Galois.iSup_decompositionSubgroup_eq_top` ("the decomposition subgroups of a
finite Galois extension of number fields generate the Galois group"): passing to the normal
closure `N` of `L / K`, every decomposition subgroup `D_w ⊆ Gal(N/K)` fixes the image of `y` in
`N` (because `y ∈ K_v` inside `N_w` and `D_w ≅ Gal(N_w/K_v)` acts by `K_v`-algebra
automorphisms), hence so does all of `Gal(N/K)`, and `y ∈ K` follows from the Galois
correspondence.

## Main result

* `NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Inclusion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The local algebra map `K_vˣ →* L_wˣ` does not depend on the proof of `LiesOver`. -/
theorem globalCFT_localAlgebraMapUnits_congr (w : Place L) (v : Place K)
    (h h' : Place.LiesOver w v) :
    Place.localAlgebraMapUnits w v h = Place.localAlgebraMapUnits w v h' := rfl

/-- At an archimedean place the local algebra map on unit groups is `Units.map` of the
canonical ring homomorphism `K_v →+* L_w` of completions. -/
theorem globalCFT_localAlgebraMapUnits_ofInfinite (w : InfinitePlace L) (v : InfinitePlace K)
    [hwv : w.LiesOver v] (h : Place.LiesOver (Place.ofInfinite w) (Place.ofInfinite v)) :
    Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v) h =
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom := by
  rw [globalCFT_localAlgebraMapUnits_congr (Place.ofInfinite w) (Place.ofInfinite v) h
    (Place.liesOver_ofInfinite hwv)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hwv]

/-- At a nonarchimedean place the local algebra map on unit groups is `Units.map` of the adic
completion map `K_Q →+* L_q`. -/
theorem globalCFT_localAlgebraMapUnits_ofFinite (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) [hqQ : q.asIdeal.LiesOver Q.asIdeal]
    (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q)) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) h =
      Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom := by
  rw [globalCFT_localAlgebraMapUnits_congr (Place.ofFinite q) (Place.ofFinite Q) h
    (Place.liesOver_ofFinite hqQ)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hqQ]

/-- **The local algebra map is injective.**  If `w` lies over `v` then the two places are of
the same kind (both archimedean or both nonarchimedean) and the local map is `Units.map` of an
injective ring homomorphism of fields, hence injective. -/
theorem globalCFT_localAlgebraMapUnits_injective {w : Place L} {v : Place K}
    (h : Place.LiesOver w v) :
    Function.Injective (Place.localAlgebraMapUnits w v h) := by
  rcases (Place.liesOver_iff w v).mp h with ⟨w', v', hw, hv, hL⟩ | ⟨q, Q, hw, hv, hL⟩
  · subst hw; subst hv
    haveI := hL
    rw [globalCFT_localAlgebraMapUnits_ofInfinite (w := w') (v := v') h]
    exact Units.map_injective (RingHom.injective _)
  · subst hw; subst hv
    haveI := hL
    rw [globalCFT_localAlgebraMapUnits_ofFinite (q := q) (Q := Q) h]
    exact Units.map_injective (RingHom.injective _)

end NK.GlobalCFT.Inclusion

namespace NK.GlobalCFT.Inclusion

variable {K N : Type*} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- **The decomposition group fixes the embedded copy of `K_p`.**  If `y : N` has its image in
`N_w` inside the image of `K_p`, then every element of the decomposition subgroup of `w` fixes
`y`: the decomposition group acts on `N_w` by `K_p`-algebra automorphisms. -/
theorem globalCFT_fixed_of_mem_range_adicCompletionMap
    (p : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 N))
    (hw : w.asIdeal.LiesOver p.asIdeal)
    (y : N) (hy : algebraMap N (w.adicCompletion N) y ∈
      Set.range (Commons.RingTheory.Henselian.adicCompletionMap p w hw))
    (σ : NK.FieldTheory.Galois.decompSubgroup (K := K) w) : σ.1 y = y := by
  obtain ⟨t, ht⟩ := hy
  have ht0 : Commons.RingTheory.Henselian.adicCompletionMap p w hw t =
      (y : w.adicCompletion N) := by
    simpa [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] using ht
  have h1 : Submission.NeukirchUchida.Local.decompositionToAdicCompletion (K := K) w σ
      (y : w.adicCompletion N) = (σ.1 y : w.adicCompletion N) :=
    Submission.NeukirchUchida.Local.decompositionToAdicCompletion_coe (K := K) w σ y
  have h2 : Submission.NeukirchUchida.Local.decompositionToAdicCompletion (K := K) w σ
      (Commons.RingTheory.Henselian.adicCompletionMap p w hw t) =
      Commons.RingTheory.Henselian.adicCompletionMap p w hw t :=
    Submission.NeukirchUchida.Local.decompositionToAdicCompletion_adicCompletionMap p w hw σ t
  have h3 : (σ.1 y : w.adicCompletion N) = (y : w.adicCompletion N) := by
    rw [← h1, ← ht0, h2]
  simpa using Submission.NeukirchUchida.Local.injective_algebraMap_adicCompletion w h3

end NK.GlobalCFT.Inclusion

namespace NK.GlobalCFT.Inclusion

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

/-- The adic completion map is compatible with the algebra maps along a tower
`K → L → M`. -/
theorem globalCFT_adicCompletionMap_algebraMap
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : K) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq
        (algebraMap K (Q.adicCompletion K) x) =
      algebraMap L (q.adicCompletion L) (algebraMap K L x) := by
  have h1 : algebraMap K (Q.adicCompletion K) x = (x : Q.adicCompletion K) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  have h2 : (algebraMap K L x : q.adicCompletion L) =
      algebraMap L (q.adicCompletion L) (algebraMap K L x) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  rw [h1, ← h2, Commons.RingTheory.Henselian.adicCompletionMap_apply]

/-- **The local condition transfers along a tower.**  If the image of `y ∈ Lˣ` in `L_q` lies in
the image of `K_p`, then the image of `y` in `M_r` lies in the image of `K_p`, for every prime
`r` of `M` over `q`. -/
theorem globalCFT_mem_range_adicCompletionMap_comp
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) (r : HeightOneSpectrum (𝓞 M))
    (hpq : q.asIdeal.LiesOver p.asIdeal) (hqr : r.asIdeal.LiesOver q.asIdeal)
    (hpr : r.asIdeal.LiesOver p.asIdeal)
    (y : Lˣ)
    (hy : Units.map (algebraMap L (q.adicCompletion L)) y ∈
      Set.range (Units.map
        (Commons.RingTheory.Henselian.adicCompletionMap p q hpq).toMonoidHom)) :
    Units.map (algebraMap M (r.adicCompletion M)) (Units.map (algebraMap L M).toMonoidHom y) ∈
      Set.range (Units.map
        (Commons.RingTheory.Henselian.adicCompletionMap p r hpr).toMonoidHom) := by
  obtain ⟨t, ht⟩ := hy
  refine ⟨t, ?_⟩
  have ht' : Commons.RingTheory.Henselian.adicCompletionMap p q hpq (t : p.adicCompletion K) =
      algebraMap L (q.adicCompletion L) (y : L) := by
    have h := congrArg (fun u : (q.adicCompletion L)ˣ => (u : q.adicCompletion L)) ht
    simpa using h
  apply Units.ext
  simp only [Units.coe_map]
  calc Commons.RingTheory.Henselian.adicCompletionMap p r hpr (t : p.adicCompletion K)
      = (Commons.RingTheory.Henselian.adicCompletionMap q r hqr).comp
          (Commons.RingTheory.Henselian.adicCompletionMap p q hpq)
            (t : p.adicCompletion K) := by
        rw [Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp
          (K := K) (L := L) (M := M) p q r hpq hqr hpr]
    _ = Commons.RingTheory.Henselian.adicCompletionMap q r hqr
          (Commons.RingTheory.Henselian.adicCompletionMap p q hpq (t : p.adicCompletion K)) := rfl
    _ = Commons.RingTheory.Henselian.adicCompletionMap q r hqr
          (algebraMap L (q.adicCompletion L) (y : L)) := by rw [ht']
    _ = algebraMap M (r.adicCompletion M) (algebraMap L M (y : L)) :=
        globalCFT_adicCompletionMap_algebraMap q r hqr (y : L)

end NK.GlobalCFT.Inclusion

namespace NK.GlobalCFT.Inclusion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **A global unit which is locally in the base field is in the base field.**  If `y ∈ Lˣ` has
its image in `L_w` inside the embedded copy of `K_v` for every place `w` of `L` over every place
`v` of `K`, then `y` is the image of a unit of `K`.

We pass to the normal closure `N` of `L/K`.  Every decomposition subgroup `D_w ≤ Gal(N/K)` fixes
the image `y'` of `y` in `N`, because `y' ∈ K_p` inside `N_w` and `D_w` acts on `N_w` by
`K_p`-algebra automorphisms (`globalCFT_fixed_of_mem_range_adicCompletionMap`).  Since the
decomposition subgroups generate `Gal(N/K)` (`NK.FieldTheory.Galois.iSup_decompositionSubgroup_eq_top`),
all of `Gal(N/K)` fixes `y'`, so `y'` lies in the base field by
`IsGalois.mem_range_algebraMap_iff_fixed`. -/
theorem globalCFT_mem_base_of_localUnits
    (y : Lˣ)
    (h : ∀ (v : Place K) (w : Place L) (hwv : Place.LiesOver w v),
      ∃ t : (Place.localField K v)ˣ,
        Place.localAlgebraMapUnits w v hwv t =
          Units.map (algebraMap L (Place.localField L w)) y) :
    ∃ a : Kˣ, Units.map (algebraMap K L).toMonoidHom a = y := by
  classical
  let Ω := AlgebraicClosure L
  let N : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  haveI hAlgL : Algebra.IsAlgebraic L Ω := inferInstance
  haveI hAlgK : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans (R := K) (S := L) (A := Ω)
  haveI hNormK : Normal K Ω :=
    { isAlgebraic := fun x => hAlgK.isAlgebraic x
      splits' := fun x => IsAlgClosed.splits _ }
  haveI hNormN : Normal K ↥N := inferInstance
  haveI hfdN : FiniteDimensional K ↥N := inferInstance
  haveI hNFN : NumberField ↥N :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := Ω) N
  haveI hGalN : IsGalois K ↥N :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero (F := K) (E := ↥N)
  have hyN : algebraMap L Ω (y : L) ∈ N := by
    have hle : (IsScalarTower.toAlgHom K L Ω).fieldRange ≤ N :=
      AlgHom.fieldRange_le_normalClosure _
    have hmem : algebraMap L Ω (y : L) ∈ (IsScalarTower.toAlgHom K L Ω).fieldRange :=
      ⟨(y : L), rfl⟩
    exact hle hmem
  let y' : ↥N := ⟨algebraMap L Ω (y : L), hyN⟩
  have hloc : ∀ (w : HeightOneSpectrum (𝓞 ↥N)) (σ : ↥N ≃ₐ[K] ↥N),
      σ ∈ NK.FieldTheory.Galois.decompSubgroup (K := K) w → σ • y' = y' := by
    intro w σ hσ
    set p : HeightOneSpectrum (𝓞 K) := IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w with hp
    set wL : HeightOneSpectrum (𝓞 L) := IsDedekindDomain.HeightOneSpectrum.under (𝓞 L) w with hwL
    have hwNp : w.asIdeal.LiesOver p.asIdeal := by
      rw [hp, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact Ideal.over_under w.asIdeal
    have hwLw : w.asIdeal.LiesOver wL.asIdeal := by
      rw [hwL, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact Ideal.over_under w.asIdeal
    have hwLp : wL.asIdeal.LiesOver p.asIdeal := by
      rw [hwL, hp, IsDedekindDomain.HeightOneSpectrum.under_asIdeal,
        IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      refine ⟨?_⟩
      rw [Ideal.under_under]
    obtain ⟨t, ht⟩ := h (Place.ofFinite p) (Place.ofFinite wL) (Place.liesOver_ofFinite hwLp)
    have htl : Units.map (algebraMap L (wL.adicCompletion L)) y ∈
        Set.range (Units.map
          (Commons.RingTheory.Henselian.adicCompletionMap p wL hwLp).toMonoidHom) := by
      refine ⟨t, ?_⟩
      have ht' : Place.localAlgebraMapUnits (Place.ofFinite wL) (Place.ofFinite p)
          (Place.liesOver_ofFinite hwLp) t =
          Units.map (algebraMap L (wL.adicCompletion L)) y := ht
      rw [globalCFT_localAlgebraMapUnits_ofFinite (q := wL) (Q := p)
        (h := Place.liesOver_ofFinite hwLp)] at ht'
      exact ht'
    obtain ⟨s, hs⟩ := globalCFT_mem_range_adicCompletionMap_comp p wL w hwLp hwLw hwNp y htl
    have hrange : algebraMap ↥N (w.adicCompletion ↥N) y' ∈ Set.range
        (Commons.RingTheory.Henselian.adicCompletionMap p w hwNp) := by
      obtain ⟨s, hs⟩ := globalCFT_mem_range_adicCompletionMap_comp p wL w hwLp hwLw hwNp y htl
      refine ⟨(s : p.adicCompletion K), ?_⟩
      have hyy : ((Units.map (algebraMap L ↥N) y : (↥N)ˣ) : ↥N) = y' := by
        rw [Units.coe_map]
        rfl
      have h1 : Commons.RingTheory.Henselian.adicCompletionMap p w hwNp
            (s : p.adicCompletion K) =
          algebraMap ↥N (w.adicCompletion ↥N)
            ((Units.map (algebraMap L ↥N) y : (↥N)ˣ) : ↥N) := by
        have h := congrArg (fun u : (w.adicCompletion ↥N)ˣ => (u : w.adicCompletion ↥N)) hs
        simpa using h
      rw [h1, hyy]
    have hfix := globalCFT_fixed_of_mem_range_adicCompletionMap p w hwNp y' hrange ⟨σ, hσ⟩
    simpa using hfix
  have htop := NK.FieldTheory.Galois.iSup_decompositionSubgroup_eq_top (K := K) (L := ↥N)
  have hstab : (⊤ : Subgroup (↥N ≃ₐ[K] ↥N)) ≤ MulAction.stabilizer (↥N ≃ₐ[K] ↥N) y' := by
    rw [← htop]
    apply iSup_le
    intro w σ hσ
    rw [MulAction.mem_stabilizer_iff]
    exact hloc w σ hσ
  have hfix : ∀ σ : ↥N ≃ₐ[K] ↥N, σ y' = y' := by
    intro σ
    have h2 := hstab (Subgroup.mem_top σ)
    rw [MulAction.mem_stabilizer_iff] at h2
    exact h2
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed y').mpr hfix
  have ha0 : a ≠ 0 := by
    intro h0
    have hzero : y' = 0 := by rw [← ha, h0, map_zero]
    have h0' : algebraMap L Ω (y : L) = 0 := by
      have := congrArg (fun z : ↥N => (z : Ω)) hzero
      simpa [y'] using this
    exact (Units.ne_zero y) ((algebraMap L Ω).injective (by simpa using h0'))
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  simp only [Units.coe_map]
  have hay : algebraMap K L a = (y : L) := by
    apply (algebraMap L Ω).injective
    calc algebraMap L Ω (algebraMap K L a)
        = algebraMap K Ω a := (IsScalarTower.algebraMap_apply K L Ω a).symm
      _ = algebraMap ↥N Ω (algebraMap K ↥N a) := (IsScalarTower.algebraMap_apply K ↥N Ω a).symm
      _ = algebraMap ↥N Ω y' := by rw [ha]
      _ = algebraMap L Ω (y : L) := rfl
  exact hay

end NK.GlobalCFT.Inclusion

namespace NK.GlobalCFT.Inclusion

/-- Every place of `K` has a place of `L` above it. -/
theorem exists_place_liesOver {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (v : Place K) :
    ∃ w : Place L, Place.LiesOver w v := by
  rcases v with v' | Q
  · obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v' :=
      InfinitePlace.comap_surjective (k := K) (K := L) v'
    exact ⟨Place.ofInfinite w,
      Place.liesOver_ofInfinite ((NK.GlobalCFT.Norm.liesOver_iff_comap_eq w v').mpr hw)⟩
  · obtain ⟨q, hq⟩ : ∃ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver Q
    exact ⟨Place.ofFinite q, Place.liesOver_ofFinite hq⟩

theorem globalCFT_principalIdele_localAlgebraMapUnits {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (a : Kˣ) (w : Place L) :
    Place.localAlgebraMapUnits w (u w) (hu w) ((Idele.principalIdele K a) (u w)) =
      Units.map (algebraMap L (Place.localField L w))
        (Units.map (algebraMap K L).toMonoidHom a) := by
  have h := congrArg (fun z : 𝕀[L] => z w)
    (globalCFT_ideleInclusion_principalIdele u hu φ hφ a)
  simpa [hφ (Idele.principalIdele K a) w, Idele.principalIdele_apply] using h

theorem globalCFT_ideleClassGroup_inclusion_injective {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (ψ : C[K] →* C[L])
    (hψ : ∀ x : 𝕀[K], ψ (IdeleClassGroup.mk K x) = IdeleClassGroup.mk L (φ x)) :
    Function.Injective ψ := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro q hq
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K q
  rw [MonoidHom.mem_ker, hψ x] at hq
  have hmem : φ x ∈ Idele.principalSubgroup L := (QuotientGroup.eq_one_iff (φ x)).mp hq
  obtain ⟨y, hy⟩ := Idele.mem_principalSubgroup.mp hmem
  have hloc : ∀ (v : Place K) (w : Place L) (hwv : Place.LiesOver w v),
      ∃ t : (Place.localField K v)ˣ,
        Place.localAlgebraMapUnits w v hwv t =
          Units.map (algebraMap L (Place.localField L w)) y := by
    intro v w hwv
    have huw : u w = v := globalCFT_liesOver_unique (hu w) hwv
    subst huw
    refine ⟨x (u w), ?_⟩
    have h1 : Place.localAlgebraMapUnits w (u w) hwv (x (u w)) =
        Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)) :=
      DFunLike.congr_fun (globalCFT_localAlgebraMapUnits_congr w (u w) hwv (hu w)) (x (u w))
    rw [h1, ← hφ x w, ← hy]
    exact Idele.principalIdele_apply y w
  obtain ⟨a, ha⟩ := globalCFT_mem_base_of_localUnits y hloc
  have hx : x = Idele.principalIdele K a := by
    apply Idele.ext
    intro v
    obtain ⟨w, hwv⟩ : ∃ w : Place L, Place.LiesOver w v := exists_place_liesOver v
    have huw : u w = v := globalCFT_liesOver_unique (hu w) hwv
    subst huw
    apply globalCFT_localAlgebraMapUnits_injective (hu w)
    rw [← hφ x w, ← hy, Idele.principalIdele_apply,
      globalCFT_principalIdele_localAlgebraMapUnits u hu φ hφ a w, ha]
  rw [hx]
  exact (QuotientGroup.eq_one_iff (Idele.principalIdele K a)).mpr ⟨a, rfl⟩

end NK.GlobalCFT.Inclusion
