import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.NUV2.ARL.unifUnit_pow_mem_localNormSubgroup
import Submission.Work.SSGRoute.ZDataMup.onePlace_mem_normImage_of_mem_sup_abelian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the local factors of the abelian Artin map
(the part of `Submission.Work.SSGRoute.ZDataMup.localFactor_productFormula_abelian` that does NOT
depend on the conductor drop / Frobenius normalisation input).

This module is split off so that it can be imported by modules that are in the dependency cone of
the crux (`frob_eq_ideleArtin_unramified_abelian`): importing
`Submission.Work.SSGRoute.ZDataMup.localFactor_productFormula_abelian` itself from there creates an
import cycle.  Nothing here depends on the crux.
-/

namespace Work.SSGRoute.ZDataMup

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {K : Type} [Field K] [NumberField K]

/-! ## Local norms, componentwise -/

theorem mem_normImage_iff_forall_mem_localNormSubgroup {L : Type} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (y : NK.GlobalCFT.Idele K) :
    y ∈ NK.GlobalCFT.Idele.normImage K L ↔
      ∀ v : NK.GlobalCFT.Place K,
        y v ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional]
  exact ⟨fun h v => by
      obtain ⟨z, hz⟩ := h v
      rw [hz]
      exact NK.CFTLib.IdeleHasse.normIdeleFun_mem_localNormSubgroup (K := K) (L := L) z v,
    fun h v =>
      NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) (h v)⟩

/-- The components of a finite product of idèles. -/
theorem Idele_prod_apply {ι : Type*} (s : Finset ι)
    (f : ι → NK.GlobalCFT.Idele K) (v : NK.GlobalCFT.Place K) :
    (∏ i ∈ s, f i) v = ∏ i ∈ s, (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; rfl
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, NK.GlobalCFT.Idele.mul_apply, ih]

/-! ## The one-place idèles inside a finite product -/

/-- Insertion rule for `cprod`, in the double-product form in which `cprod` is defined. -/
theorem cprod_insert {G : Type} [Group G] (hcomm : ∀ x y : G, x * y = y * x) {ι : Type*}
    [DecidableEq ι] {s : Finset ι} {a : ι} (ha : a ∉ s) (f : ι → G) :
    NK.CFTLib.IdeleHasse.cprod hcomm (insert a s) f = f a * NK.CFTLib.IdeleHasse.cprod hcomm s f := by
  classical
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold NK.CFTLib.IdeleHasse.cprod
  rw [Finset.prod_insert ha]

/-- A monoid homomorphism takes a finite product of one-place idèles to the `cprod` of its
values. -/
theorem map_prod_onePlace {G : Type} [Group G] (hcomm : ∀ x y : G, x * y = y * x)
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Ψ : NK.GlobalCFT.Idele K →* G) (s : Finset (NK.GlobalCFT.Place K))
    (b : (v : NK.GlobalCFT.Place K) → (NK.GlobalCFT.Place.localField K v)ˣ) :
    Ψ (∏ v ∈ s, NK.HassePrinciple.onePlace v (b v)) =
      NK.CFTLib.IdeleHasse.cprod hcomm s
        (fun v => Ψ (NK.HassePrinciple.onePlace v (b v))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, map_one,
        NK.CFTLib.IdeleHasse.cprod_eq_one hcomm (fun i hi => by simp at hi)]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, map_mul, ih, cprod_insert hcomm ha]

/-- The `v`-component of a principal idèle is the image of the element in the completion. -/
theorem principalIdele_apply_eq_localImageAt (x : Kˣ) (v : NK.GlobalCFT.Place K) :
    (NK.GlobalCFT.Idele.principalIdele K x) v = NK.CFTLib.IdeleHasse.localImageAt v x := by
  rw [NK.CFTLib.IdeleHasse.localImageAt, NK.GlobalCFT.Idele.principalIdele_apply]
  rfl


theorem onePlace_hilbertReciprocity_abelian {L : Type} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) (x : Kˣ) (v₀ : NK.GlobalCFT.Place K)
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) :
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ := by
  exact hilbertReciprocity_abelian (K := K) (L := L) hcomm (x := x) (v₀ := v₀) h

/-- **Local faithfulness of the abelian Artin map at one place**, from the "one place omitted" form
of Hilbert reciprocity: a one-place idèle which lies in `N_{L/K}𝕀_L · Kˣ` already lies in
`N_{L/K}𝕀_L` (Milne, *CFT*, V.5.3(a)).  This is the abelian generalisation of
`NK.CFTLib.IdeleHasse.localFaithful_onePlace`, with the same reduction: writing
`onePlace v a = n · ρ(x)` with `n` an idèle-norm and `x ∈ Kˣ`, every component of `ρ(x)` away from
`v` is the inverse of a component of `n`, hence a local norm there, so Hilbert reciprocity gives
`x_v ∈ N_v`; then `ρ(x) ∈ N_{L/K}𝕀_L` and `onePlace v a = n · ρ(x)` is an idèle-norm. -/
theorem localFaithful_abelian {L : Type} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    {v : NK.GlobalCFT.Place K} {a : (NK.GlobalCFT.Place.localField K v)ˣ}
    (h : NK.HassePrinciple.onePlace v a ∈
      NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K) :
    NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L := by
  classical
  obtain ⟨n, hn, p, hp, hnp⟩ := Subgroup.mem_sup.mp h
  obtain ⟨x, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hp
  -- `n * principalIdele K x = onePlace v a`, so in the forward direction:
  have hmain : NK.HassePrinciple.onePlace v a = n * NK.GlobalCFT.Idele.principalIdele K x :=
    hnp.symm
  have hn_mem : ∀ u : NK.GlobalCFT.Place K,
      n u ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) u :=
    (mem_normImage_iff_forall_mem_localNormSubgroup (K := K) (L := L) n).mp hn
  have hx : ∀ u : NK.GlobalCFT.Place K, u ≠ v →
      NK.CFTLib.IdeleHasse.localImageAt u x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) u := by
    intro u hu
    have h1 : n u * NK.CFTLib.IdeleHasse.localImageAt u x = 1 := by
      have h2 : (NK.HassePrinciple.onePlace v a) u = 1 :=
        NK.HassePrinciple.onePlace_apply_ne hu a
      rw [hmain, NK.GlobalCFT.Idele.mul_apply, principalIdele_apply_eq_localImageAt] at h2
      exact h2
    have h3 : NK.CFTLib.IdeleHasse.localImageAt u x = (n u)⁻¹ :=
      (inv_eq_of_mul_eq_one_right h1).symm
    rw [h3]
    exact Subgroup.inv_mem _ (hn_mem u)
  have hv : NK.CFTLib.IdeleHasse.localImageAt v x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v :=
    onePlace_hilbertReciprocity_abelian (K := K) (L := L) hcomm x v hx
  have hρ : NK.GlobalCFT.Idele.principalIdele K x ∈ NK.GlobalCFT.Idele.normImage K L := by
    rw [mem_normImage_iff_forall_mem_localNormSubgroup]
    intro u
    rw [principalIdele_apply_eq_localImageAt]
    by_cases hu : u = v
    · rw [hu]; exact hv
    · exact hx u hu
  rw [hmain]
  exact mul_mem hn hρ

/-! ## The product formula -/

/-- **The product formula for the local factors `θ_v = Φ ∘ onePlace_v`.** -/
theorem cprod_localFactor_eq_one {L : Type} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L))
    (hprin : ∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1)
    (hnorm : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (x : Kˣ) (s : Finset (NK.GlobalCFT.Place K))
    (hs : ∀ v, v ∉ s →
      Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) :
    NK.CFTLib.IdeleHasse.cprod hcomm s
      (fun v => Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x))) = 1 := by
  classical
  have hsame : ∀ v : NK.GlobalCFT.Place K,
      (NK.GlobalCFT.Idele.principalIdele K x) v = NK.CFTLib.IdeleHasse.localImageAt v x := by
    intro v
    rw [NK.CFTLib.IdeleHasse.localImageAt, NK.GlobalCFT.Idele.principalIdele_apply]
    rfl
  set T : Finset (NK.GlobalCFT.Place K) :=
    (((Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
        (K := K) (L := L)).toFinset.image
      (fun q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) =>
        NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L
          (NK.GlobalCFT.Place.ofFinite q))
      ∪ Finset.univ.image (NK.GlobalCFT.Place.ofInfinite (K := K)))
      ∪ (Filter.eventually_cofinite.mp (NK.GlobalCFT.Idele.principalIdele K x).2).toFinset)
      ∪ s with hT
  have hsT : s ⊆ T := fun _ hx => Finset.mem_union_right _ hx
  -- the complementary idèle
  set w : NK.GlobalCFT.Idele K :=
    NK.GlobalCFT.Idele.principalIdele K x *
      (∏ v ∈ T, NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x))⁻¹ with hw
  -- the finite product over `T`, evaluated at a place
  have hprod_eval : ∀ v : NK.GlobalCFT.Place K,
      (∏ u ∈ T, NK.HassePrinciple.onePlace u (NK.CFTLib.IdeleHasse.localImageAt u x)) v =
        ∏ u ∈ T, (NK.HassePrinciple.onePlace u (NK.CFTLib.IdeleHasse.localImageAt u x)) v :=
    fun v => Idele_prod_apply (K := K) T
      (fun u => NK.HassePrinciple.onePlace u (NK.CFTLib.IdeleHasse.localImageAt u x)) v
  have hsingle : ∀ v ∈ T,
      (∏ u ∈ T, (NK.HassePrinciple.onePlace u (NK.CFTLib.IdeleHasse.localImageAt u x)) v) =
        NK.CFTLib.IdeleHasse.localImageAt v x := by
    intro v hv
    rw [Finset.prod_eq_single_of_mem v hv (fun b hb hbne => by
      rw [NK.HassePrinciple.onePlace_apply_ne (fun h => hbne h.symm)])]
    exact NK.HassePrinciple.onePlace_apply_self v _
  have hnone : ∀ v, v ∉ T →
      (∏ u ∈ T, (NK.HassePrinciple.onePlace u (NK.CFTLib.IdeleHasse.localImageAt u x)) v) = 1 := by
    intro v hv
    exact Finset.prod_eq_one (fun b hb => by
      rw [NK.HassePrinciple.onePlace_apply_ne (fun (h : v = b) => hv (h.symm ▸ hb))])
  -- components of `w`
  have hcomp : ∀ v, w v = if v ∈ T then 1 else NK.CFTLib.IdeleHasse.localImageAt v x := by
    intro v
    rw [hw, NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply,
      NK.GlobalCFT.Idele.principalIdele_apply, hprod_eval v]
    by_cases hv : v ∈ T
    · rw [if_pos hv, hsingle v hv,
        show NK.CFTLib.IdeleHasse.localImageAt v x =
          Units.map (algebraMap K (NK.GlobalCFT.Place.localField K v)) x from rfl, mul_inv_cancel]
    · rw [if_neg hv, hnone v hv, inv_one, mul_one, NK.CFTLib.IdeleHasse.localImageAt]
      rfl
  have hwmem : w ∈ NK.GlobalCFT.Idele.normImage K L := by
    rw [mem_normImage_iff_forall_mem_localNormSubgroup]
    intro v
    rw [hcomp v]
    by_cases hv : v ∈ T
    · rw [if_pos hv]; exact Subgroup.one_mem _
    · rw [if_neg hv]
      have hfin : NK.GlobalCFT.Place.IsFinite v := by
        by_contra hinf
        obtain ⟨w₀, rfl⟩ := NK.GlobalCFT.Place.isInfinite_iff.mp (Classical.not_not.mp hinf)
        exact hv (by
          rw [hT]
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ w₀)))))
      obtain ⟨Q, rfl⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hfin
      have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
        intro q hq
        by_contra hne
        refine hv (by
          rw [hT, ← NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_eq_of_liesOver
            (NK.GlobalCFT.Place.liesOver_ofFinite hq)]
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨q, (Set.Finite.mem_toFinset _).mpr hne, rfl⟩))))
      have hunit : (NK.GlobalCFT.Idele.principalIdele K x) (NK.GlobalCFT.Place.ofFinite Q) ∈
          NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) := by
        by_contra hnot
        exact hv (by
          rw [hT]
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            ((Set.Finite.mem_toFinset _).mpr hnot)))
      rw [hsame (NK.GlobalCFT.Place.ofFinite Q)] at hunit
      exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
        (K := K) (L := L) Q hunr hunit
  have hΦw : Φ w = 1 := by
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hwmem
    rw [show w = NK.GlobalCFT.Idele.normIdeleHom K L y from
      NK.GlobalCFT.Idele.ext fun v => hy v]
    exact hnorm y
  have hprod :
      Φ (∏ v ∈ T, NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1 := by
    have h1 : Φ (NK.GlobalCFT.Idele.principalIdele K x) =
        Φ w * Φ (∏ v ∈ T, NK.HassePrinciple.onePlace v
          (NK.CFTLib.IdeleHasse.localImageAt v x)) := by
      rw [hw, map_mul, map_inv]
      group
    rw [hprin x, hΦw, one_mul] at h1
    exact h1.symm
  have hmap := map_prod_onePlace (K := K) (L := L) hcomm Φ T
    (fun v => NK.CFTLib.IdeleHasse.localImageAt v x)
  rw [NK.CFTLib.IdeleHasse.cprod_subset hcomm hsT (fun v _ hvs => hs v hvs), ← hmap, hprod]


end Work.SSGRoute.ZDataMup
