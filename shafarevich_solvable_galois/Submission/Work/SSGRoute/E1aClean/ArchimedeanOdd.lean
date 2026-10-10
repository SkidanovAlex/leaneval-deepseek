import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.SSGStage.archimedeanLocalDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean local `Ext²` at odd-primary coefficients

For an odd prime `p` (`p ≠ 2`) and a finite `p`-torsion representation `X` of `Gal(K/k)`, the local
group `Ext²_{D_w}(X|, K_wˣ)` at an infinite place `w` of `K` is a subsingleton.  This is proved by
the two cases of the archimedean decomposition group:

* `D_w = ⊥`: the group ring is `ℤ`, the first variable is a finitely generated `ℤ`-module, and
  `Ext² = 0` (`PT.subsingleton_ext2_of_subsingleton`);
* `D_w ≠ ⊥`: then `w` is a complex place (`isComplex_of_decompK_ofInfinite_ne_bot`), so the local
  units are divisible (`localUnitsK_divisible_of_isComplex`) and the divisible-coefficient
  dictionary `ext_two_iso_divisible_cohomology` identifies `Ext²` with
  `H²(D_w, Hom_ℤ(X|, ℂˣ))`.  The coefficient module is `p`-torsion (`p` odd), hence `2` acts
  bijectively on it; since `|D_w| = 2` at a ramified infinite place
  (`NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two`), the averaging argument
  `H2_subsingleton_of_card_smul_bijective` kills the `H²`.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

open scoped TensorProduct

/-- **The archimedean local `Ext²` vanishes on odd-primary coefficients.** -/
theorem archimedeanExt2Subsingleton (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k K : Type)
    [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite X.V]
    (hX : ∀ x : X.V, p • x = 0) (w : NumberField.InfinitePlace K) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)).subtype X)
      (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)) 2) := by
  classical
  haveI : Module.Finite ℤ X.V := Work.SSGRoute.PT.module_finite_int_of_finite (G := K ≃ₐ[k] K) X
  have hDstab : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)
      = MulAction.stabilizer (K ≃ₐ[k] K) w :=
    Work.SSGRoute.SSGStage.decompK_ofInfinite_eq_stabilizer (k := k) (K := K) w
  by_cases hbot : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) = ⊥
  · -- the decomposition group is trivial
    let D := SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)
    haveI : Subsingleton ↥D := by
      rw [show D = ⊥ from hbot]
      infer_instance
    haveI : Module.Finite ℤ (Rep.res (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype X).V := ‹Module.Finite ℤ X.V›
    exact Work.SSGRoute.PT.subsingleton_ext2_of_subsingleton
      (Rep.res (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype X)
      (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w))
  · -- nontrivial decomposition group: the place is complex
    have hw : w.IsComplex :=
      Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := K) hbot
    set D : Subgroup (K ≃ₐ[k] K) :=
      SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) with hD
    set N := SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)
      with hN
    have hdiv : ∀ n : ℕ, 0 < n → ∀ y : N.V, ∃ x : N.V, n • x = y :=
      Work.SSGRoute.SSGStage.localUnitsK_divisible_of_isComplex (k := k) (K := K) hw
    obtain ⟨e⟩ := Work.SSGRoute.ext_two_iso_divisible_cohomology D
      (Rep.res D.subtype X) N hdiv
    -- the order of `D` is `2`
    have hnu : ¬ NumberField.InfinitePlace.IsUnramified k w := fun hunr =>
      hbot (by
        rw [hDstab]
        exact (NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot).mp hunr)
    have hcard : Nat.card ↥D = 2 := by
      rw [show D = MulAction.stabilizer (K ≃ₐ[k] K) w from hDstab]
      exact (NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two).mp hnu
    haveI : Fintype ↥D := Fintype.ofFinite _
    have hcardF : Fintype.card ↥D = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
    -- the coefficient module: `2` acts bijectively on it
    have hfinN : Finite {y : N.V // p • y = 0} := by
      have h := Work.SSGRoute.SSGStage.finite_ptorsion_additive p
        (Work.SSGRoute.SSGStage.finite_ptorsion_localUnits_of_isComplex (k := k) (K := K) hw p)
      exact h
    have hbij2 : Function.Bijective
        (fun φ : (Rep.res D.subtype X).V →ₗ[SSGRoute.PTExt.Coeff] N.V => φ + φ) :=
      Work.SSGRoute.SSGStage.two_smul_bijective_coeffLinearMap_of_ptorsion_finite
        p hp2 hfinN (fun x : (Rep.res D.subtype X).V => hX x)
    have hbij : Function.Bijective
        (fun a : (Rep.res D.subtype X).V →ₗ[SSGRoute.PTExt.Coeff] N.V =>
          Fintype.card ↥D • a) := by
      rw [hcardF]
      simpa only [two_nsmul] using hbij2
    have hH2 : Subsingleton (Work.GroupCohomology.H2 ↥D
        ((Rep.res D.subtype X).V →ₗ[SSGRoute.PTExt.Coeff] N.V)) :=
      Work.GroupCohomology.H2_subsingleton_of_card_smul_bijective hbij
    exact ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩

end Work.SSGRoute.E1aClean
