import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.ArchLocPrep
import Submission.Work.SSGRoute.SSGStage.archimedeanLocalDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean local `Ext¹` at odd-primary coefficients

For an odd prime `p` (`p ≠ 2`) and a finite `p`-torsion representation `X` of `Gal(K/k)`, the local
group `Ext¹_{D_w}(X|, K_wˣ)` at a *nonsplit* infinite place `w` of `K` (i.e. `D_w ≠ ⊥`) is a
subsingleton.

The route is the degree-one analogue of `Work.SSGRoute.E1aClean.archimedeanExt2Subsingleton`:

* `D_w ≠ ⊥` forces `w` to be complex (`isComplex_of_decompK_ofInfinite_ne_bot`), so the local
  field is `K_w = ℂ` and its unit group `ℂˣ` is divisible
  (`localUnitsK_divisible_of_isComplex`);
* the divisible-coefficient dictionary `ext_one_iso_divisible_cohomology` identifies
  `Ext¹_{D_w}(X|, K_wˣ)` with `Ext¹_{D_w}(ℤ, Hom_ℤ(X|, ℂˣ)) = H¹(D_w, Hom_ℤ(X|, ℂˣ))`
  (`ArchLocPrep.ext_one_homRep_iso_H1`);
* the coefficient module `Hom_ℤ(X|, ℂˣ)` is `p`-torsion (`X` is `p`-torsion), and since `p ≠ 2`
  multiplication by `2` is a bijection of it
  (`two_smul_bijective_coeffLinearMap_of_ptorsion_finite`, using `Finite X.V` and the finiteness of
  the `p`-torsion of `ℂˣ`);
* `Nat.card D_w = 2` at a ramified infinite place
  (`NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two`), so the averaging
  argument `H1_subsingleton_of_card_smul_bijective` kills the `H¹`.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt

/-- **The archimedean local `Ext¹` vanishes on odd-primary coefficients at a nonsplit place.** -/
theorem archimedeanLocalExt1Subsingleton_of_ne_bot (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k K : Type)
    [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite X.V]
    (hX : ∀ x : X.V, p • x = 0) (w : NumberField.InfinitePlace K)
    (hne : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≠ ⊥) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)).subtype X)
      (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)) 1) := by
  classical
  set D : Subgroup (K ≃ₐ[k] K) :=
    SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) with hDs
  set N := SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w) with hNs
  -- the place is complex, so the local units are divisible
  have hw : w.IsComplex :=
    Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := K) hne
  have hdiv : ∀ n : ℕ, 0 < n → ∀ y : N.V, ∃ x : N.V, n • x = y :=
    Work.SSGRoute.SSGStage.localUnitsK_divisible_of_isComplex (k := k) (K := K) hw
  -- the divisible-coefficient dictionary, degree one
  obtain ⟨e⟩ := Work.SSGRoute.ext_one_iso_divisible_cohomology D (Rep.res D.subtype X) N hdiv
  obtain ⟨e2⟩ := Work.SSGRoute.ArchDictionary.ext_one_homRep_iso_H1 D (Rep.res D.subtype X) N
  -- the coefficient module `Hom(X|, K_wˣ)` is `p`-torsion and `2` acts bijectively on it
  have hfinN : Finite {y : N.V // p • y = 0} := by
    have h := Work.SSGRoute.SSGStage.finite_ptorsion_additive p
      (Work.SSGRoute.SSGStage.finite_ptorsion_localUnits_of_isComplex (k := k) (K := K) hw p)
    exact h
  have hbij2 : Function.Bijective
      (fun φ : (Rep.res D.subtype X).V →ₗ[SSGRoute.PTExt.Coeff] N.V => φ + φ) :=
    Work.SSGRoute.SSGStage.two_smul_bijective_coeffLinearMap_of_ptorsion_finite p hp2 hfinN
      (fun x : (Rep.res D.subtype X).V => hX x)
  -- the order of `D` is `2`
  have hDst : D = MulAction.stabilizer (K ≃ₐ[k] K) w := by
    rw [hDs]
    exact Work.SSGRoute.SSGStage.decompK_ofInfinite_eq_stabilizer (k := k) (K := K) w
  have hnu : ¬ NumberField.InfinitePlace.IsUnramified k w := fun hunr =>
    hne (by
      show D = ⊥
      rw [hDst]
      exact (NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot).mp hunr)
  have hcard : Nat.card ↥D = 2 := by
    rw [hDst]
    exact (NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two).mp hnu
  haveI : Fintype ↥D := Fintype.ofFinite _
  have hcardF : Fintype.card ↥D = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hbij : Function.Bijective
      (fun a : (Rep.res D.subtype X).V →ₗ[SSGRoute.PTExt.Coeff] N.V => Fintype.card ↥D • a) := by
    rw [hcardF]
    simpa only [two_nsmul] using hbij2
  haveI : Subsingleton (Work.GroupCohomology.H1 ↥D
      ((Rep.res D.subtype X).V →ₗ[SSGRoute.PTExt.Coeff] N.V)) :=
    Work.GroupCohomology.H1_subsingleton_of_card_smul_bijective hbij
  exact ⟨fun a b => e.injective (e2.injective (Subsingleton.elim (e2 (e a)) (e2 (e b))))⟩

end Work.SSGRoute.ArchDictionary
