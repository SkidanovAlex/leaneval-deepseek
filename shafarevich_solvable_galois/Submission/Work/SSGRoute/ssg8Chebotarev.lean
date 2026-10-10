import Mathlib.NumberTheory.NumberField.DirichletDensity
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Čebotarev over an arbitrary number field base (for the Grünwald-with-escape node)

This module isolates the *arithmetic* Čebotarev input used by the `N2` node
(`Work.SSGRoute.grunwald_escape_relative_ssg8`): the density theorem over an arbitrary number
field base, assembled from the proved Hecke input (`NK.NUV2.heckeInput_proved`) and the proved
ideal-theoretic Artin reciprocity law (`NK.CFTLib.artinReciprocityIdeal_proved`), together with
its existence form (a prescribed Frobenius element outside a prescribed finite set of primes).

* `chebotarev_density_general`: for a finite Galois extension `N/K` of number fields and
  `σ : Gal(N/K)`, the primes of `K` at which `σ` is a Frobenius element have Dirichlet density
  `1/|C_{Gal(N/K)}(σ)|` (the Deuring transfer reduces this to the abelian case, which the Hecke
  input and the ideal-theoretic reciprocity law supply).
* `exists_isFrobAtPrime_notMem_density`: the existence form — this is the form in which the
  Grünwald-with-escape proof chooses its escape prime.
-/

namespace Work.SSGRoute

open scoped Pointwise

/-- **Čebotarev's density theorem over an arbitrary number field base.**  For a finite Galois
extension `N/K` of number fields and `σ : Gal(N/K)`, the primes of `K` at which `σ` is a Frobenius
element have Dirichlet density `1/|C_{Gal(N/K)}(σ)|`. -/
theorem chebotarev_density_general : NK.ChebotarevGeneral.ChebotarevDensity :=
  NK.ChebotarevGeneral.chebotarevDensity_of_abelian
    (NK.NUV2.abelianChebotarevDensity_of_freeInputs NK.NUV2.heckeInput_proved
      (NK.NUV2.artinFrobeniusInputFree_of_artinReciprocityIdeal
        NK.CFTLib.artinReciprocityIdeal_proved))

/-- **Čebotarev with a finite set of primes avoided.**  For a finite normal level `M` of an
`k`-algebra `Ω` and every `k`-automorphism `g` of `M`, there is a prime of `k` outside any
prescribed finite set of primes at which `g` is an arithmetic Frobenius element.

This is the form of Čebotarev needed to choose the escape place of Grünwald-with-escape. -/
theorem exists_isFrobAtPrime_notMem_density
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (Bad : Set (NK.Chebotarev.PrimeIdeal k)) (hBad : Bad.Finite)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    (g : (↥M) ≃ₐ[k] (↥M)) :
    ∃ p : NK.Chebotarev.PrimeIdeal k, p ∉ Bad ∧
      NK.Chebotarev.IsFrobAtPrime (K := k) (L := ↥M) p g := by
  classical
  haveI hgal : IsGalois k ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  have hdens : NumberField.Set.HasDirichletDensity
      (NK.ChebotarevGeneral.frobSet (K := k) (N := ↥M) g)
      (NK.ChebotarevGeneral.frobDensity (K := k) (N := ↥M) g) :=
    chebotarev_density_general k ↥M g
  haveI : Nonempty ↥(Subgroup.centralizer ({g} : Set (↥M ≃ₐ[k] ↥M))) :=
    ⟨1, Subgroup.one_mem _⟩
  have hpos : 0 < NK.ChebotarevGeneral.frobDensity (K := k) (N := ↥M) g := by
    rw [NK.ChebotarevGeneral.frobDensity]
    refine one_div_pos.mpr ?_
    exact_mod_cast Nat.card_pos
  by_contra hcon
  push_neg at hcon
  have hsub : NK.ChebotarevGeneral.frobSet (K := k) (N := ↥M) g ⊆ Bad := by
    intro p hp
    by_contra hpBad
    exact hcon p hpBad hp
  have hzn : NumberField.Set.HasDirichletDensity
      (NK.ChebotarevGeneral.frobSet (K := k) (N := ↥M) g) 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset
      (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite hBad) hsub
  rw [NumberField.Set.HasDirichletDensity] at hdens hzn
  exact absurd (tendsto_nhds_unique hdens hzn) hpos.ne'

end Work.SSGRoute
