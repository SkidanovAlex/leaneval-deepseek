import Mathlib
import Submission.Work.SSGRoute.SSGStage.archimedeanLocalDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.SSGStage

open CategoryTheory SSGRoute.PTExt

/-- **The archimedean local `Ext²` vanishes on odd-primary coefficients.**  For an odd prime `p`
(`p ≠ 2`), a finite `p`-torsion representation `X` of `Gal(K/k)` and an infinite place `w` of `K`,
the local `Ext²`-group `Ext²_{D_w}(X|, K_wˣ)` at the decomposition group `D_w` of `w` is a
subsingleton.

Reason: `D_w` is trivial (then apply `PT.subsingleton_ext2_of_subsingleton`) or `w` is a *complex*
place, where `K_w = ℂ`, its unit group is divisible
(`Work.SSGRoute.SSGStage.localUnitsK_divisible_of_isComplex`), and the divisible-coefficient
dictionary (`Work.SSGRoute.ext_two_iso_divisible_cohomology`) identifies the group with
`H²(D_w, Hom_ℤ(X, ℂˣ))`; since `D_w` has order at most `2`, `Hom_ℤ(X, ℂˣ)` is `p`-torsion with
finite `p`-torsion (`Work.SSGRoute.SSGStage.finite_ptorsion_additive` +
`finite_ptorsion_localUnits_of_isComplex`), so `2` acts bijectively on it
(`two_smul_bijective_coeffLinearMap_of_ptorsion_finite`) and the `H²` vanishes via
`Work.GroupCohomology.Z2_le_B2_of_card_smul_bijective` / `subsingleton_H2_of_Z2_le_B2`. -/
theorem archimedeanLocalExt2Subsingleton (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k K : Type)
    [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite X.V]
    (hX : ∀ x : X.V, p • x = 0) (w : NumberField.InfinitePlace K) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)).subtype X)
      (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)) 2) := by
  classical
  -- The decomposition group of the infinite place `ofInfinite w` is the stabiliser of `w`.
  have hDstab : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)
      = MulAction.stabilizer (K ≃ₐ[k] K) w :=
    decompK_ofInfinite_eq_stabilizer (k := k) (K := K) w
  by_cases hbot : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) = ⊥
  · -- Case 1: the decomposition group is trivial, so `ℤ[D_w] = ℤ` and `Ext² = 0`.
    haveI : Subsingleton ↥(SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)) := by
      rw [hbot]; infer_instance
    haveI : Module.Finite ℤ (Rep.res (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype X).V :=
      Work.SSGRoute.PT.module_finite_int_of_finite (G := K ≃ₐ[k] K) X
    exact Work.SSGRoute.PT.subsingleton_ext2_of_subsingleton _ _
  · -- Case 2: a nontrivial decomposition group forces `w` to be a complex place.
    have hw : w.IsComplex := isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := K) hbot
    set D : Subgroup (K ≃ₐ[k] K) :=
      SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) with hD
    set N := SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)
      with hN
    -- The local units at a complex infinite place are divisible.
    have hdiv : ∀ n : ℕ, 0 < n → ∀ y : N.V, ∃ x : N.V, n • x = y :=
      localUnitsK_divisible_of_isComplex (k := k) (K := K) hw
    -- The divisible-coefficient dictionary identifies `Ext²` with `H²(D_w, Hom_ℤ(X|, K_wˣ))`.
    obtain ⟨e⟩ := Work.SSGRoute.ext_two_iso_divisible_cohomology D (Rep.res D.subtype X) N hdiv
    -- The place `w` is ramified in `k`, hence `|D_w| = 2`.
    have hnu : ¬ NumberField.InfinitePlace.IsUnramified k w := fun hunr =>
      hbot (by rw [hDstab]
               exact (NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot).mp hunr)
    have hcard : Nat.card ↥D = 2 := by
      rw [show D = MulAction.stabilizer (K ≃ₐ[k] K) w from hDstab]
      exact (NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two).mp hnu
    haveI : Fintype ↥D := Fintype.ofFinite _
    have hcardF : Fintype.card ↥D = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
    -- The `p`-torsion of the local units is finite, and `p` is odd.
    have hfinN : Finite {y : N.V // p • y = 0} := by
      have h := finite_ptorsion_additive p
        (finite_ptorsion_localUnits_of_isComplex (k := k) (K := K) hw p)
      exact h
    -- Hence doubling is bijective on the coefficient module `Hom_ℤ(X|, K_wˣ)`.
    have hbij2 : Function.Bijective
        (fun φ : (Rep.res D.subtype X).V →ₗ[SSGRoute.PTExt.Coeff] N.V => φ + φ) :=
      two_smul_bijective_coeffLinearMap_of_ptorsion_finite p hp2 hfinN
        (fun x : (Rep.res D.subtype X).V => hX x)
    have hbij : Function.Bijective
        (fun a : (Rep.res D.subtype X).V →ₗ[SSGRoute.PTExt.Coeff] N.V =>
          Fintype.card ↥D • a) := by
      rw [hcardF]
      simpa only [two_nsmul] using hbij2
    -- The averaging argument kills `H²(D_w, Hom_ℤ(X|, K_wˣ))`.
    have hH2 : Subsingleton (Work.GroupCohomology.H2 ↥D
        ((Rep.res D.subtype X).V →ₗ[SSGRoute.PTExt.Coeff] N.V)) :=
      subsingleton_H2_of_Z2_le_B2 (Work.GroupCohomology.Z2_le_B2_of_card_smul_bijective hbij)
    exact ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩

end Work.SSGRoute.SSGStage
