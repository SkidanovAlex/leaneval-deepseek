import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.Work.SSGRoute.ZDataMup.localFactorProductFormulaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The product formula for the local factors, commutative target

This is the commutative-target form of the product formula
`Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one`: for a homomorphism `Ψ` from the idèles of `K`
into a *commutative monoid* which kills principal idèles and idèlic norms from a finite Galois
extension `L/K`, and a global element `x ∈ Kˣ` whose local factors vanish outside a finite set of
places `s`, the product of the local factors over `s` is `1`.

The only difference from the group-valued version is that the target is allowed to be a
*monoid* (`Multiplicative (ZMod p)` is not a group when `p` is prime, since `0` is not
invertible); the argument is rearranged so that no inverse in the target is ever needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.GrunwaldEscapeCore

variable {K : Type} [Field K] [NumberField K]

/-- A monoid homomorphism into a commutative monoid takes a finite product of one-place idèles to
the product of its values. -/
theorem map_prod_onePlace_comm {G : Type} [CommMonoid G]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Ψ : NK.GlobalCFT.Idele K →* G) (s : Finset (NK.GlobalCFT.Place K))
    (b : (v : NK.GlobalCFT.Place K) → (NK.GlobalCFT.Place.localField K v)ˣ) :
    Ψ (∏ v ∈ s, NK.HassePrinciple.onePlace v (b v)) =
      ∏ v ∈ s, Ψ (NK.HassePrinciple.onePlace v (b v)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, map_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, ih]

/-- **The product formula for the local factors, commutative-monoid target.** -/
theorem prod_localFactor_eq_one_of_comm_aux {G : Type} [CommMonoid G]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Ψ : NK.GlobalCFT.Idele K →* G)
    (hprin : ∀ x : Kˣ, Ψ (NK.GlobalCFT.Idele.principalIdele K x) = 1)
    (hnorm : ∀ y : NK.GlobalCFT.Idele L, Ψ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (x : Kˣ) (s : Finset (NK.GlobalCFT.Place K))
    (hs : ∀ v, v ∉ s →
      Ψ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) :
    ∏ v ∈ s, Ψ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1 := by
  classical
  have hsame : ∀ v : NK.GlobalCFT.Place K,
      (NK.GlobalCFT.Idele.principalIdele K x) v = NK.CFTLib.IdeleHasse.localImageAt v x :=
    fun v => Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt x v
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
    fun v => Work.SSGRoute.ZDataMup.Idele_prod_apply (K := K) T
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
    rw [Work.SSGRoute.ZDataMup.mem_normImage_iff_forall_mem_localNormSubgroup]
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
  have hΨw : Ψ w = 1 := by
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hwmem
    rw [show w = NK.GlobalCFT.Idele.normIdeleHom K L y from
      NK.GlobalCFT.Idele.ext fun v => hy v]
    exact hnorm y
  have hprod :
      Ψ (∏ v ∈ T, NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1 := by
    have h1 : Ψ w * Ψ (∏ v ∈ T, NK.HassePrinciple.onePlace v
        (NK.CFTLib.IdeleHasse.localImageAt v x)) = Ψ (NK.GlobalCFT.Idele.principalIdele K x) := by
      rw [← map_mul, hw]
      congr 1
      group
    rw [hΨw, hprin x, one_mul] at h1
    exact h1
  have hmap := map_prod_onePlace_comm (K := K) (L := L) Ψ T
    (fun v => NK.CFTLib.IdeleHasse.localImageAt v x)
  rw [Finset.prod_subset hsT (fun v _ hvs => hs v hvs), ← hmap, hprod]

theorem prod_localFactor_eq_one_of_comm
    (p : ℕ) [Fact p.Prime] {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Ψ : NK.GlobalCFT.Idele K →* Multiplicative (ZMod p))
    (hprin : ∀ x : Kˣ, Ψ (NK.GlobalCFT.Idele.principalIdele K x) = 1)
    (hnorm : ∀ y : NK.GlobalCFT.Idele L, Ψ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (x : Kˣ) (s : Finset (NK.GlobalCFT.Place K))
    (hs : ∀ v, v ∉ s →
      Ψ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) :
    ∏ v ∈ s, Ψ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1 :=
  prod_localFactor_eq_one_of_comm_aux (K := K) (L := L) Ψ hprin hnorm x s hs

end Work.GrunwaldEscapeCore
