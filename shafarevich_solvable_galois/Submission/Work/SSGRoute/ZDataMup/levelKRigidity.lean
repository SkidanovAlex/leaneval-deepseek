import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.stabilizer_eq_implies_conj
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Rigidity of finite places: the level-`K` decomposition group determines the place

This is the strengthened form of
`Work.SSGRoute.ZDataMup.ArtinUniqueness.stabilizer_eq_implies_conj`: not merely are two finite
places with the same level-`K` decomposition group `G_K`-conjugate, they are *equal*.  The proof
is the one already contained in that lemma (distinct places over finite primes of a number field
have trivially intersecting decomposition groups, while decomposition groups over finite primes are
nontrivial), stated here in the form the wiring consumes.

Consequence: the level-`K` local group `H_A = decomp k A ⊓ K.fixingSubgroup` is an *injective*
function of the place `A`, so a family of local data indexed by the subgroups `H_A` may be defined
by choosing, for each `H` of the form `H_A`, a witness place — the resulting value does not depend
on the witness.

This module is `sorry`-free and imports nothing from the pairing gate, so that the assembly lemmas
built on it cannot inherit the gate's `sorryAx`.
-/

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

/-- A finite place over `k` is a finite place over `↥K` (if `A` contains all of `↥K`, then it
contains all of `k`). -/
theorem isFinPlace_comap_levelK {k K : Type} [Field k] [NumberField k] [Field K] [Algebra k K]
    {Ω : Type} [Field Ω] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    A.comap (algebraMap K Ω) ≠ ⊤ := by
  intro h
  refine hA ?_
  refine SetLike.ext fun x => ?_
  rw [ValuationSubring.mem_comap]
  constructor
  · intro _; trivial
  · intro _
    have h1 : algebraMap k K x ∈ A.comap (algebraMap K Ω) := by
      rw [h]; trivial
    rw [ValuationSubring.mem_comap] at h1
    rwa [IsScalarTower.algebraMap_apply k K Ω]

/-- **A finite place is determined by its level-`K` decomposition group.**

If two finite places `A`, `A'` of `Ω` over `k` cut down to the same subgroup
`decomp k A ⊓ K.fixingSubgroup = decomp k A' ⊓ K.fixingSubgroup` of `Gal(Ω/k)`, then `A = A'`. -/
theorem decomp_inf_fixingSubgroup_eq_imp_eq (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsSepClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A A' : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hA' : SSGRoute.IsFinPlace k A')
    (h : SSGRoute.decomp k A ⊓ K.fixingSubgroup = SSGRoute.decomp k A' ⊓ K.fixingSubgroup) :
    A = A' := by
  classical
  -- `↥K` is again a number field, and `Ω` is a separable closure of it
  haveI hNFK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI hSepK : IsSepClosure ↥K Ω := by
    have : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- a finite place over `k` is a finite place over `↥K`
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ :=
    isFinPlace_comap_levelK (k := k) (K := ↥K) A hA
  have hAK' : A'.comap (algebraMap ↥K Ω) ≠ ⊤ :=
    isFinPlace_comap_levelK (k := k) (K := ↥K) A' hA'
  -- transport the hypothesis to `Gal(Ω/↥K)`
  have hD : SSGRoute.decomp ↥K A = SSGRoute.decomp ↥K A' := by
    ext σ
    rw [Work.SSGRoute.ZDataMup.ArtinUniqueness.mem_decomp_levelK_iff_mem_inf k Ω K A σ,
      Work.SSGRoute.ZDataMup.ArtinUniqueness.mem_decomp_levelK_iff_mem_inf k Ω K A' σ, h]
  -- two distinct places over finite primes have trivially intersecting decomposition groups, while
  -- a decomposition group over a finite prime is nontrivial
  by_contra hne
  have hbot : SSGRoute.decomp ↥K A ⊓ SSGRoute.decomp ↥K A' = ⊥ :=
    Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne hne hAK hAK'
  rw [← hD, inf_idem] at hbot
  obtain ⟨σ, hσne, hσA⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top A hAK
  have hσmem : σ ∈ SSGRoute.decomp ↥K A :=
    (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer A σ).mp hσA
  rw [hbot] at hσmem
  exact hσne (Subgroup.mem_bot.mp hσmem)

end Work.SSGRoute.ZDataMup
