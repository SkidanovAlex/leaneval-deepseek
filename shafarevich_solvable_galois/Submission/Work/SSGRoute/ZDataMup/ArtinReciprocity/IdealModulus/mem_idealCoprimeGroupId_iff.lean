import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `I(𝔪)`: the group of fractional ideals coprime to an ideal modulus `𝔪`

`NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪` is defined in `Defs.lean` as the
*subgroup generated* by the prime ideals `𝔭` with `¬ DvdPrime 𝔪 𝔭`, while `FracCoprimeId 𝔪 A` is
the *property* of having no prime factor dividing `𝔪` (vanishing `count` at every height-one prime
containing `𝔪`).  This module proves that the two agree:

`A ∈ idealCoprimeGroupId 𝔪 ↔ FracCoprimeId 𝔪 A`.

This is the exact ideal-modulus analogue of `mem_idealCoprimeGroup_iff` for a natural-number
modulus; the two directions are the two halves of the unique factorisation of a fractional ideal
of a Dedekind domain as a finitely supported product `∏_𝔭 𝔭 ^ (count K 𝔭 A)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

theorem mem_idealCoprimeGroupId_iff {K : Type} [Field K] [NumberField K]
    (𝔪 : Ideal (NumberField.RingOfIntegers K))
    (A : NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
    A ∈ NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪 ↔
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 A := by
  classical
  constructor
  · -- The generators of `I(𝔪)` are coprime to `𝔪`, and the coprime fractional ideals form a
    -- subgroup, so the whole of `I(𝔪)` consists of them.
    intro h
    exact NK.CFTLib.ArtinReciprocityIdeal.fracCoprimeId_of_mem_idealCoprimeGroupId h
  · -- Conversely, `A` is the finitely supported product of the prime powers `𝔭 ^ (count 𝔭 A)`;
    -- every factor with `DvdPrime 𝔪 𝔭` has exponent `0`, and every other factor is a generator.
    intro hA
    set e : HeightOneSpectrum (𝓞 K) → ℤ :=
      fun 𝔭 => FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K) with he
    set u : HeightOneSpectrum (𝓞 K) → NK.CFTLib.ArtinReciprocityIdeal.Frac K :=
      fun 𝔭 => NK.CFTLib.ArtinReciprocityIdeal.idealUnit 𝔭.asIdeal 𝔭.ne_bot with hu
    have hfin : Function.HasFiniteMulSupport fun 𝔭 : HeightOneSpectrum (𝓞 K) => u 𝔭 ^ e 𝔭 := by
      have hcount : {𝔭 : HeightOneSpectrum (𝓞 K) | e 𝔭 ≠ 0}.Finite := by
        have h1 := Filter.eventually_cofinite.mp
          (FractionalIdeal.finite_factors (K := K) (A : FractionalIdeal (𝓞 K)⁰ K))
        simpa [he] using h1
      exact hcount.subset fun 𝔭 h𝔭 he0 =>
        h𝔭 (by show u 𝔭 ^ e 𝔭 = 1; rw [he0, zpow_zero])
    have hmem : ∀ 𝔭, u 𝔭 ^ e 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪 := by
      intro 𝔭
      by_cases h𝔭 : NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭
      · have h0 : e 𝔭 = 0 := hA 𝔭 h𝔭
        rw [h0, zpow_zero]
        exact Subgroup.one_mem _
      · have hgen : u 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪 := by
          rw [NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId]
          exact Subgroup.subset_closure ⟨𝔭, h𝔭, rfl⟩
        exact Subgroup.zpow_mem _ hgen (e 𝔭)
    have hprod : (∏ᶠ 𝔭, u 𝔭 ^ e 𝔭) ∈
        NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪 :=
      finprod_induction (fun x => x ∈ NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪)
        (Subgroup.one_mem _) (fun _ _ hx hy => Subgroup.mul_mem _ hx hy) hmem
    have hAeq : A = ∏ᶠ 𝔭, u 𝔭 ^ e 𝔭 := by
      apply Units.ext
      change (A : FractionalIdeal (𝓞 K)⁰ K) =
        (Units.coeHom (FractionalIdeal (𝓞 K)⁰ K)) (∏ᶠ 𝔭, u 𝔭 ^ e 𝔭)
      rw [MonoidHom.map_finprod (Units.coeHom (FractionalIdeal (𝓞 K)⁰ K)) hfin,
        ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
          (I := (A : FractionalIdeal (𝓞 K)⁰ K)) A.ne_zero]
      refine finprod_congr fun 𝔭 => ?_
      simp [u, e, NK.CFTLib.ArtinReciprocityIdeal.idealUnit]
    rw [hAeq]
    exact hprod

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
