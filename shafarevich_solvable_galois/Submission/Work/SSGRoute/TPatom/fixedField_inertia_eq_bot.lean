import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
import Submission.Work.Sha2Lib.inertia_map_galRes_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia group of the fixed field of `N` is trivial when `N` contains the inertia

Let `k ⊆ K` be a finite Galois extension of number fields, `N ⊴ Gal(K/k)` a normal subgroup and
`L = K^N` the fixed field.  For a nonzero prime `q` of `𝓞 K` and a nonzero prime `u` of `𝓞 L` below
it, with the hypothesis that every inertia element of `q` in `Gal(K/k)` lies in `N`
(`hNI : ∀ σ, IsInertiaAt q σ → σ ∈ N`), the inertia group of `u` in `Gal(L/k)` is trivial.

The proof is a two-line application of the surjectivity of restriction on inertia groups
(`Work.Sha2Lib.inertia_map_galRes_eq`): the restriction map
`Gal(K/k) →* Gal(L/k)` sends the inertia group of `q` **onto** the inertia group of `u`; but its
kernel is `Gal(K/L) = N` (the fixing subgroup of `L = K^N`), and `I_q ≤ N` by hypothesis, so the
image is trivial.
-/

namespace Work.SSGRoute.TPatom

open NumberField

theorem fixedField_inertia_eq_bot {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers
      ↥(IntermediateField.fixedField N)))
    (hu : q.asIdeal.LiesOver u.asIdeal)
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (τ : ↥(IntermediateField.fixedField N) ≃ₐ[k] ↥(IntermediateField.fixedField N))
    (hτ : SSGRoute.PTExt.IsInertiaAt u τ) :
    τ = 1 := by
  -- The restriction of the inertia of `q` to `L = K^N` is the inertia of `u`.
  have hmap := Work.Sha2Lib.inertia_map_galRes_eq (k := k)
    (K := ↥(IntermediateField.fixedField N)) (L := K) u q hu
  -- The inertia of `q` is contained in the kernel of the restriction `Gal(K/k) →* Gal(L/k)`,
  -- because that kernel is the fixing subgroup of `L`, i.e. `N`, and the inertia of `q` lies in
  -- `N` by hypothesis.
  have hle : Ideal.inertia (K ≃ₐ[k] K) q.asIdeal ≤
      (SSGRoute.PTExt.galRes k ↥(IntermediateField.fixedField N) K).ker := by
    intro σ hσ
    have hσi : SSGRoute.PTExt.IsInertiaAt q σ :=
      (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := K) q σ).mpr hσ
    have hN : σ ∈ N := hNI σ hσi
    have hfix : σ ∈ (IntermediateField.fixedField N).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_fixedField N]
      exact hN
    rw [← IntermediateField.restrictNormalHom_ker (K := k) (L := K)
      (IntermediateField.fixedField N)] at hfix
    exact hfix
  -- Hence the inertia of `u` is trivial.
  have hIu : Ideal.inertia
      (↥(IntermediateField.fixedField N) ≃ₐ[k] ↥(IntermediateField.fixedField N)) u.asIdeal = ⊥ := by
    rw [← hmap]
    exact (Subgroup.map_eq_bot_iff _).mpr hle
  -- Every inertial element of `u` is therefore trivial.
  have hmem : τ ∈ Ideal.inertia
      (↥(IntermediateField.fixedField N) ≃ₐ[k] ↥(IntermediateField.fixedField N)) u.asIdeal :=
    (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k)
      (K := ↥(IntermediateField.fixedField N)) u τ).mp hτ
  rw [hIu] at hmem
  exact Subgroup.mem_bot.mp hmem

end Work.SSGRoute.TPatom
