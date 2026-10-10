import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.Sha2Lib.inertia_lift_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia subgroup at a place maps onto the inertia subgroup below

For a tower `k ⊆ K ⊆ L` of number fields with `K/k`, `L/k` and `L/K` finite Galois, and a nonzero
prime `q'` of `𝓞 L` lying over `q` in `𝓞 K`:

  `(I_{q'}(L/k)).map (galRes k K ↥L) = I_q(K/k)`,

i.e. the restriction map sends the inertia subgroup of `q'` **onto** the inertia subgroup of `q`.

Both inclusions are already available elementwise on disk:

* `⊆` is `Work.SSGRoute.E9Nodes.e9_inertia_restrict` (an inertial element restricts to an inertial
  element), combined with the dictionary `Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia`
  between `IsInertiaAt` and membership in `Ideal.inertia`;
* `⊇` is `Work.SSGRoute.Sha2Lib.inertia_lift_restrict` (every inertial element at `q` lifts to one
  at `q'`).

This packaging is what the level-existence statement `exists_indNormal_level_and_section` needs: it
supplies the hypothesis `K₁.map π = I` of
`Work.SSGRoute.Sha2Lib.exists_splitting_agreeing_on_subgroup` when applied with
`I := I_{q'}(L/k)` (the inertia of the level at `q'`), `K₁ :=` its image in `Gal(K/k)` — the
splitting `s : Gal(K/k) →* Gal(L/k)` with `s(I_q) ⊆ I_{q'}` produced there is exactly what makes
the coordinate `coordKer k K Ω L s hs` vanish on the inertia at `q'`.
-/

namespace Work.Sha2Lib

open CategoryTheory SSGRoute.PTExt

/-- The algebra map of a field into a `K`-algebra is injective. -/
private lemma algebraMap_injective_of_field {K L : Type} [Field K] [Field L] [Algebra K L] :
    Function.Injective (algebraMap K L) := by
  intro a b h
  by_contra hab
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hunit : IsUnit (a - b) := (isUnit_iff_ne_zero).mpr hne
  have h0 : algebraMap K L (a - b) = 0 := by rw [map_sub, h, sub_self]
  have h1 : IsUnit (algebraMap K L (a - b)) := hunit.map (algebraMap K L)
  rw [h0] at h1
  exact one_ne_zero (isUnit_zero_iff.mp h1).symm

theorem inertia_map_galRes_eq {k K L : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [Field L] [NumberField L] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k K] [FiniteDimensional k L]
    [FiniteDimensional K L] [IsGalois k K] [IsGalois k L] [IsGalois K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q'.asIdeal.LiesOver q.asIdeal) :
    (Ideal.inertia (L ≃ₐ[k] L) q'.asIdeal).map (SSGRoute.PTExt.galRes k K L)
      = Ideal.inertia (K ≃ₐ[k] K) q.asIdeal := by
  refine le_antisymm ?_ ?_
  · -- restriction of an inertial element is inertial
    intro τ hτ
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hτ
    have hγi : SSGRoute.PTExt.IsInertiaAt q' γ :=
      (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := L) q' γ).mpr hγ
    have hres : SSGRoute.PTExt.IsInertiaAt q (SSGRoute.PTExt.galRes k K L γ) :=
      Work.SSGRoute.E9Nodes.e9_inertia_restrict k K L q q' hq γ
        (SSGRoute.PTExt.galRes k K L γ)
        (fun x => (AlgEquiv.restrictNormal_commutes γ K x).symm) hγi
    exact (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := K) q _).mp hres
  · -- every inertial element at `q` lifts to an inertial element at `q'`
    intro τ hτ
    have hτi : SSGRoute.PTExt.IsInertiaAt q τ :=
      (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := K) q τ).mpr hτ
    obtain ⟨γ, hγi, hγres⟩ :=
      Work.SSGRoute.Sha2Lib.inertia_lift_restrict k K L q q' hq τ hτi
    refine Subgroup.mem_map.mpr ⟨γ, ?_, ?_⟩
    · exact (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := L) q' γ).mp hγi
    · apply AlgEquiv.ext
      intro x
      refine algebraMap_injective_of_field (K := K) (L := L) ?_
      show (algebraMap K L) ((γ.restrictNormal K) x) = (algebraMap K L) (τ x)
      rw [AlgEquiv.restrictNormal_commutes γ K x, hγres x]

end Work.Sha2Lib
