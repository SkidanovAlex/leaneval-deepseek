import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.Imports
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.conductorDrop_ramifiedSupport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local–global Artin map of a cyclic extension kills the principal idèles

For a finite cyclic extension `L / K` of number fields we produce a monoid homomorphism

  `Φ : 𝕀[K] →* Gal(L/K)`

which

* kills the principal idèles `Kˣ`,
* kills the idèlic norms `N_{L/K} 𝕀[L]`,
* is surjective, and
* is Frobenius-normalised: `Φ (ideleOfPrime K Q) = Frob_Q` for **every** prime `Q`
  unramified in `L / K` (Milne, *CFT*, VII.8.1 with the normalisation of V.5.3(a)).

`Φ` is realised as the idèlic Artin map `NK.CFTLib.Arl.ideleArtin` attached to the congruence
datum `(m, U, hadj)` supplied by the ideal-theoretic reciprocity law at a modulus `m`
(`NK.CFTLib.artinReciprocityIdeal_proved`), as packaged by
`NK.CFTLib.Arl.exists_monoidHom_ideleArtin`: that construction kills the principal idèles and the
idèlic norms and is Frobenius-normalised at the primes not dividing `(m)` by design.

The only arithmetic input is the Frobenius normalisation at an unramified prime `Q` **dividing**
the modulus, i.e. the classical fact that the conductor of an abelian extension is supported on
the ramified primes (Neukirch, *ANT*, V.6.1; Lang, *ANT*, X §4), here
`Work.SSGRoute.ZDataMup.ArtinReciprocity.conductorDrop_ramifiedSupport`.  Concretely: with
`b := adjust U hadj (ideleOfPrime K Q)` one has
`ideleArtin (ideleOfPrime K Q) = artinSym (Q · (b)) = Frob_Q · artinSym ((b))`, and `b ≡ 1`
modulo `m` at every *ramified* prime dividing `(m)` (at `Q` itself the component of
`ideleOfPrime K Q` is the uniformiser, so `b` has a pole there), so the conductor drop gives
`artinSym ((b)) = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

open NK.GlobalCFT

/-- **The local–global Artin map of a cyclic extension kills the principal idèles**
(Milne, *CFT*, VII.8.1(a), in the ideal-theoretic formulation of the `ZDataMup` lane). -/
theorem exists_localGlobalArtinMap_kills_principal_cyclic {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective Φ ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  -- commutativity of `Gal(L/K)` from cyclicity
  have hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a := by
    intro a b
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
    obtain ⟨m₁, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨m₂, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    rw [← zpow_add, ← zpow_add, add_comm m₁ m₂]
  -- the ideal-theoretic reciprocity law at a modulus `m`
  obtain ⟨m, hm, hramIn, hprincIn⟩ := NK.CFTLib.artinReciprocityIdeal_proved K L hcomm
  -- the congruence subgroup of modulus `m`, with an adjustment
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  -- the idèlic Artin map
  obtain ⟨art, hagree, hprincipal, hgood, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hramIn hprincIn
      U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  -- ## it kills the idèlic norms
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm hramIn
      hprincIn U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm z
    exact ⟨d, hUeq ▸ hd⟩
  -- ## Frobenius normalisation at *every* unramified prime
  have hfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      art (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    intro Q hunr
    by_cases hmem : (m : NumberField.RingOfIntegers K) ∈ Q.asIdeal
    · -- the conductor drop: an unramified prime dividing the modulus
      rw [hagree]
      set b : Kˣ := NK.CFTLib.Arl.adjust U hadj (NK.HeckeL.ideleOfPrime K Q) with hbdef
      have hspec : NK.HeckeL.ideleOfPrime K Q *
          NK.GlobalCFT.Idele.principalIdele K b ∈ U := NK.CFTLib.Arl.adjust_spec U hadj _
      have hcongU :=
        (hU.1 (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)).mp hspec
      have hQunrIn : Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1 := by
        obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
        rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
          (B := NumberField.RingOfIntegers L) Q.asIdeal P.asIdeal (Gal(L/K))]
        exact hunr P hP
      have hcomp : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          𝔮 ≠ Q →
          (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)
              (NK.GlobalCFT.Place.ofFinite 𝔮)
            = Units.map (algebraMap K (𝔮.adicCompletion K)).toMonoidHom b := by
        intro 𝔮 h𝔮
        rw [NK.GlobalCFT.Idele.mul_apply,
          NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofFinite_ne_exists h𝔮, one_mul,
          NK.GlobalCFT.Idele.principalIdele_apply]
        rfl
      have hcompInf : ∀ w : NumberField.InfinitePlace K,
          (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)
              (NK.GlobalCFT.Place.ofInfinite w)
            = Units.map (algebraMap K w.Completion).toMonoidHom b := by
        intro w
        rw [NK.GlobalCFT.Idele.mul_apply,
          NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofInfinite, one_mul,
          NK.GlobalCFT.Idele.principalIdele_apply]
        rfl
      have hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
          Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
          Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
            ≤ Valued.v ((m : ℕ) : 𝔮.adicCompletion K) := by
        intro 𝔮 h𝔮 hram𝔮
        have h𝔮Q : 𝔮 ≠ Q := by
          intro h
          subst h
          exact hram𝔮 hQunrIn
        have hval := (hcongU.1 𝔮 h𝔮)
        rw [hcomp 𝔮 h𝔮Q] at hval
        simpa using hval
      have hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
          0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
                (algebraMap K w.Completion ((b : Kˣ) : K)) := by
        intro w hw
        have hval := (hcongU.2 w) hw
        rw [hcompInf w] at hval
        simpa using hval
      have hb1 : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            ((b : Kˣ) : K)) = 1 :=
        conductorDrop_ramifiedSupport (K := K) (L := L) hcomm m hm hramIn hprincIn b hcong hpos
      have hA : ((Q.asIdeal : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ≠ 0 :=
        FractionalIdeal.coeIdeal_ne_zero.mpr Q.ne_bot
      have hB : FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) ((b : Kˣ) : K) ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)
      show NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
          (Idele.idealOf (NK.HeckeL.ideleOfPrime K Q *
            NK.GlobalCFT.Idele.principalIdele K b))
        = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q
      rw [Idele.idealOf_mul, NK.CFTLib.Arl.idealOf_ideleOfPrime,
        Idele.idealOf_principalIdele,
        NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm hA hB, hb1, mul_one,
        NK.CFTLib.Arl.artinSym_prime]
    · exact hgood Q hmem
  exact ⟨art, hprincipal, hnorm, hsurj, hfrob⟩

end Work.SSGRoute.ZDataMup.ArtinReciprocity
