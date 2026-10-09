import Mathlib
import Submission.Work.SSGRoute.ZDataMup.localFactor_ramified_eq_one
import Submission.Work.SSGRoute.ZDataMup.weakApprox_pos_numberField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local factor at a ramified prime kills the modulus congruence subgroup

Let `L / K` be a finite abelian Galois extension of number fields, `m > 0` a modulus whose primes
`∤ (m)` are unramified in `L` and which satisfies the ideal-theoretic reciprocity law (`hram`,
`hprinc`), and let `Φ : 𝕀_K →* Gal(L/K)` be a homomorphism killing the principal idèles, killing the
idèlic norms, and taking the value `Frob_Q` at the idèle of every prime `Q ∤ (m)`.

Then the local factor `Φ ∘ onePlace_𝔭` at a prime `𝔭 | (m)` is trivial on the congruence subgroup
`1 + 𝔭^{v_𝔭(m)}`: for `x ∈ K_𝔭ˣ` with `|x - 1|_𝔭 ≤ |m|_𝔭` one has `Φ (onePlace 𝔭 x) = 1`.

The argument is exactly that of `localFactor_ramified_eq_one`, but the Frobenius normalisation `hF`
is stated here at the primes `∤ (m)` rather than at the unramified primes (the two are equivalent
at the primes used by the proof, which are precisely the primes `∤ (m)`).

`Φ` and the canonical idèlic Artin map `art` of the congruence datum `(m, U)` agree by
`ideleHom_eq_of_frobAtPrime_of_notMem` (both kill the principal idèles and the idèlic norms, and
match at every prime `∤ (m)`, the Frobenius elements at which generate `Gal(L/K)`).  Then
`|x - 1|_𝔭 ≤ |m|_𝔭` makes `x` a unit and `onePlace 𝔭 x` a member of the congruence subgroup `U`,
so that `ideleArtin_onePlace_eq_artinSym_idealOf` computes the canonical map as the Artin symbol of
the trivial fractional ideal, which is `1`.
-/

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

theorem onePlace_congruenceUnit_eq_one_of_artinKillsPrincipal {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    {Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L)}
    (hprin : ∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1)
    (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hF : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔭 : (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal)
    (x : (𝔭.adicCompletion K)ˣ)
    (hx : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            ((x : 𝔭.adicCompletion K) - 1)
          ≤ Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((m : ℕ) : 𝔭.adicCompletion K))) :
    Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) x) = 1 := by
  classical
  -- ## The `𝔭`-adic value of (the image of) `m` is `< 1`
  have hlt : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : 𝔭.adicCompletion K)) < 1 := by
    rw [show ((m : ℕ) : 𝔭.adicCompletion K) = ((m : K) : 𝔭.adicCompletion K)
          from (map_natCast (algebraMap K (𝔭.adicCompletion K)) m).symm]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [← map_natCast (algebraMap (𝓞 K) K) m]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem 𝔭 (m : 𝓞 K)).mpr h𝔭
  -- ## `x` is a local unit at `𝔭`
  have hval : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((x : 𝔭.adicCompletion K)) = 1 := by
    have hxle : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((x : 𝔭.adicCompletion K) - 1) < 1 := lt_of_le_of_lt hx hlt
    have hle1 : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((x : 𝔭.adicCompletion K)) ≤ 1 := by
      have h := Commons.NumberTheory.NumberField.Completion.val_add_le_max 𝔭
        ((x : 𝔭.adicCompletion K) - 1) 1
      rw [sub_add_cancel, map_one] at h
      exact h.trans (max_le (le_of_lt hxle) le_rfl)
    have hge1 : (1 : WithZero (Multiplicative ℤ)) ≤
        Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((x : 𝔭.adicCompletion K)) := by
      have h := Commons.NumberTheory.NumberField.Completion.val_add_le_max 𝔭
        ((x : 𝔭.adicCompletion K)) (1 - (x : 𝔭.adicCompletion K))
      rw [show (x : 𝔭.adicCompletion K) + (1 - (x : 𝔭.adicCompletion K)) = 1 from by ring] at h
      rw [map_one] at h
      have hneg : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (1 - (x : 𝔭.adicCompletion K)) = Valued.v (R := 𝔭.adicCompletion K)
            (Γ₀ := WithZero (Multiplicative ℤ)) ((x : 𝔭.adicCompletion K) - 1) := by
        rw [show (1 : 𝔭.adicCompletion K) - (x : 𝔭.adicCompletion K)
              = -((x : 𝔭.adicCompletion K) - 1) from by ring]
        exact Valuation.map_neg _ _
      rw [hneg] at h
      rcases le_max_iff.mp h with h' | h'
      · exact h'
      · exact absurd h' (not_le.mpr hxle)
    exact le_antisymm hle1 hge1
  -- ## The congruence subgroup of modulus `m` and its canonical Artin map
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust (K := K) m hm
  obtain ⟨art, hart, hPart, hNart, hSart, hFart⟩ :=
    exists_ideleHom_ideleArtin_of_congruence_data (K := K) (L := L) hcomm m hm hram hprinc U hU hadj
  -- ## `Φ` is surjective (the Frobenius elements at the primes `∤ (m)` generate)
  have hSΦ : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top]
    refine NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem (K := K) (L := L)
      (NK.CFTLib.Arl.primesDividing (K := K) m hm) Φ.range ?_
    intro p hp σ hσ
    have hmp : (m : 𝓞 K) ∉ p.asIdeal :=
      fun h => hp ((NK.CFTLib.Arl.mem_primesDividing (K := K) m hm p).mpr h)
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p :=
      isUnramifiedIn_of_ramificationIdxIn_eq_one (K := K) (L := L) p (hram p hmp)
    refine ⟨NK.HeckeL.ideleOfPrime K p, ?_⟩
    rw [hF p hmp]
    exact (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p hunr σ).mp hσ
  -- ## `Φ` agrees with the canonical Artin map
  have hΦart : Φ = art :=
    ideleHom_eq_of_frobAtPrime_of_notMem (K := K) (L := L) hcomm
      (NK.CFTLib.Arl.primesDividing (K := K) m hm)
      (fun p hp => hram p (fun h =>
        hp ((NK.CFTLib.Arl.mem_primesDividing (K := K) m hm p).mpr h)))
      Φ art hprin hN hSΦ
      (fun p hp => hF p (fun h =>
        hp ((NK.CFTLib.Arl.mem_primesDividing (K := K) m hm p).mpr h)))
      hPart hNart hSart
      (fun p hp => hFart p (fun h =>
        hp ((NK.CFTLib.Arl.mem_primesDividing (K := K) m hm p).mpr h)))
  rw [hΦart]
  -- ## The crux of the canonical construction, from the reciprocity law `hprinc`
  have hstep : ∀ b : Kˣ, NK.GlobalCFT.Idele.principalIdele K b ∈ U →
      NK.CFTLib.Arl.artinSym hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (b : K)) = 1 :=
    fun b hb => NK.CFTLib.Arl.artinSym_spanSingleton_eq_one (K := K) (L := L) hcomm m hm hram
      hprinc b ((hU.2 b).mp hb).1 ((hU.2 b).mp hb).2
  -- ## `onePlace 𝔭 x` lies in the congruence subgroup
  have hUone : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) x ∈ U := by
    rw [hU.1]
    refine ⟨?_, ?_⟩
    · intro 𝔮 h𝔮
      by_cases hq : 𝔮 = 𝔭
      · subst hq
        rw [NK.HassePrinciple.onePlace_apply_self]
        exact hx
      · rw [NK.HassePrinciple.onePlace_apply_ne
          (fun h => hq (NK.GlobalCFT.Place.ofFinite_inj.mp h))]
        simp
    · intro w
      rw [NK.HassePrinciple.onePlace_apply_ne (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w 𝔭)]
      intro hw
      simp
  -- ## The fractional ideal of `onePlace 𝔭 x` is trivial
  have hidealOf : NK.GlobalCFT.Idele.idealOf
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) x) = 1 := by
    rw [NK.GlobalCFT.Idele.idealOf_eq_one_iff, NK.GlobalCFT.Idele.mem_integralIdeles]
    intro v hv
    obtain ⟨q, rfl⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hv
    by_cases hq : q = 𝔭
    · subst hq
      rw [NK.HassePrinciple.onePlace_apply_self]
      rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
      exact hval
    · rw [NK.HassePrinciple.onePlace_apply_ne
        (fun h => hq (NK.GlobalCFT.Place.ofFinite_inj.mp h))]
      exact Subgroup.one_mem _
  rw [hart]
  rw [NK.CFTLib.Existence.ideleArtin_onePlace_eq_artinSym_idealOf (K := K) (L := L) hcomm U hadj
    hstep 𝔭 x hUone]
  rw [hidealOf]
  exact NK.CFTLib.Arl.artinSym_one hcomm

end Work.SSGRoute.ZDataMup.ArtinReciprocity
