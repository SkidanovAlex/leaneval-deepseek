import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Existence.artinSym_spanSingleton_eq_one_of_totallyPositive_of_isUnramifiedAtFinite
import Submission.NK.CFTLib.Existence.normIdeleHom_congruenceSubgroup_le
import Submission.NK.CFTLib.NormPrincipal.dvd_expUnit_of_eq_normIdeleFun
import Submission.NK.CFTLib.integralIdelesLeNormImage
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormGroup.Basic

/-! Guidance from the project lead (the requester):

# Guidance: the splitting law (Milne V.5.3(a) ideal form)

For unramified abelian `L/K` and a prime `v`: if the class of the prime idèle `π_v`
(`NK.HeckeL.ideleOfPrime`) lies in `N_{L/K} C_L`, then `v` splits (inertia degree `1`).

## This file

The idèlic Artin map `art : 𝕀 K →* Gal(L/K)` attached to the ideal-theoretic reciprocity law
`NK.CFTLib.ArtinReciprocityIdeal` (`NK.CFTLib.Arl.exists_monoidHom_ideleArtin`) kills the
principal idèles and the idèlic norms, and it carries the idèle of an unramified prime to its
Frobenius.  The latter is the classical *prime–Frobenius compatibility* of the Artin map; for a
prime `𝔭` with `(m) ∉ 𝔭` it is immediate from the definition of `art`, and for `𝔭 | (m)` it uses
the fact that the Artin symbol of the *adjustment* `b` of `π_𝔭` is trivial: `b` is a unit
congruent to `1` modulo `(m)` at every *ramified* prime (the component of `π_𝔭` there is `1`
because `𝔭` is assumed unramified), and the Frobenius normalisation at the primes dividing the
modulus is exactly the statement that the conductor is supported on the ramified primes
(`NK.CFTLib.Existence.artinSym_spanSingleton_eq_one_of_totallyPositive_of_isUnramifiedAtFinite`,
which specialises the general statement to an extension that is unramified at every finite place).

Once the Artin map carries `π_v` to `Frob_v`, the splitting law is immediate: the hypothesis
`[π_v] ∈ N_{L/K}C_L` means that `π_v = (a) · N(y)` with `a ∈ Kˣ` and `y ∈ 𝕀 L`, so
`art π_v = art (a) · art (N y) = 1`; hence `Frob_v = 1`, and the order of the Frobenius at an
unramified prime is the inertia degree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT NK.CFTLib.Arl

/-- **The Frobenius normalisation of the idèlic Artin map at an unramified prime dividing the
modulus.**

If `𝔭` is an unramified prime of `K` with `(m) ⊆ 𝔭`, then the idèlic Artin map attached to a
congruence subgroup of modulus `m` sends `ideleOfPrime K 𝔭` to `frobAtPrime 𝔭`.

The proof follows `NK.CFTLib.Existence.frobAtPrime_eq_ideleArtin_of_mem`
(`Submission/Work/CFTLib/Existence/idelic_artin_of_arl.lean`), except that the Artin symbol of
the adjustment `b` is killed by the *unramified* Frobenius-normalisation hypothesis
`artinSym_spanSingleton_eq_one_of_totallyPositive_of_isUnramifiedAtFinite` rather than by the
general (congruence at the ramified primes) form. -/
theorem frobAtPrime_eq_ideleArtin_of_mem_of_unramified {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (hARL : NK.CFTLib.ArtinReciprocityIdeal)
    (hunr : differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunr𝔭 : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      Q.asIdeal.LiesOver 𝔭.asIdeal →
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hmem : (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal) :
    NK.CFTLib.Arl.ideleArtin (K := K) (L := L) hcomm U hadj
      (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime 𝔭 := by
  classical
  set b : Kˣ := NK.CFTLib.Arl.adjust U hadj (NK.HeckeL.ideleOfPrime K 𝔭) with hbdef
  have hspec : NK.HeckeL.ideleOfPrime K 𝔭 * Idele.principalIdele K b ∈ U :=
    NK.CFTLib.Arl.adjust_spec U hadj _
  obtain ⟨-, hposU⟩ := (hU.1 (NK.HeckeL.ideleOfPrime K 𝔭 * Idele.principalIdele K b)).mp hspec
  -- the adjustment is totally positive
  have hposb : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap K w.Completion (b : K)) := by
    intro w hw
    have hcomp : (NK.HeckeL.ideleOfPrime K 𝔭 * Idele.principalIdele K b)
        (Place.ofInfinite w)
        = Units.map (algebraMap K w.Completion : K →* w.Completion) b := by
      rw [Idele.mul_apply, Idele.principalIdele_apply]
      have : NK.HeckeL.ideleOfPrime K 𝔭 (Place.ofInfinite w) = 1 := rfl
      rw [this, one_mul]
    have h1 := hposU w hw
    rw [hcomp] at h1
    simpa using h1
  -- the Artin symbol of the adjustment is trivial
  have hb1 : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) = 1 :=
    artinSym_spanSingleton_eq_one_of_totallyPositive_of_isUnramifiedAtFinite
      (K := K) (L := L) hARL hunr hcomm b hposb
  have hA : (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr 𝔭.ne_bot
  have hB : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)
  show NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (Idele.idealOf (NK.HeckeL.ideleOfPrime K 𝔭 * Idele.principalIdele K b))
    = NK.Chebotarev.frobAtPrime 𝔭
  rw [Idele.idealOf_mul, NK.CFTLib.Arl.idealOf_ideleOfPrime, Idele.idealOf_principalIdele,
    NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm hA hB, hb1, mul_one,
    NK.CFTLib.Arl.artinSym_prime]


theorem splitting_of_normClass (hARL : NK.CFTLib.ArtinReciprocityIdeal) :
    ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
      (hunr : differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤),
      ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K v) ∈
          NK.GlobalCFT.Idele.normClassSubgroup K L →
        Ideal.inertiaDegIn v.asIdeal (NumberField.RingOfIntegers L) = 1 := by
  intro K L _ _ _ _ _ _ _ _ hunr v hmem
  classical
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  obtain ⟨m, hm, hram, hprinc⟩ := hARL K L hcomm
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  obtain ⟨art, hAgree, hPrin, hFrob, -⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin hcomm m hm hram hprinc U hU hadj
  -- the Artin map kills the idèlic norms
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hadjN : ∀ y : Idele L, ∃ d : Lˣ,
      Idele.normIdeleHom K L (y * Idele.principalIdele L d) ∈ U := by
    intro y
    obtain ⟨UL, hUL, hadjL⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust L m hm
    have hULeq : UL = NK.CFTLib.Arl.congruenceSubgroup L m :=
      SetLike.ext fun x => (hUL.1 x).trans Iff.rfl
    obtain ⟨d, hd⟩ := hadjL y
    refine ⟨d, ?_⟩
    rw [hUeq]
    have hd' : y * Idele.principalIdele L d ∈ NK.CFTLib.Arl.congruenceSubgroup L m := by
      rw [← hULeq]; exact hd
    exact NK.CFTLib.Arl.normIdeleHom_mem_congruenceSubgroup (K := K) (L := L) m hm hd'
  have hNorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hAgree]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin hcomm m hm hram hprinc U hU hadj
      hadjN y
  -- hypothesis: the class of `π_v` is a norm class: `π_v = N(y) * (a)`
  have hkill : art (NK.HeckeL.ideleOfPrime K v) = 1 := by
    obtain ⟨w, hw, hwmk⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hw
    have hw' : w = Idele.normIdeleHom K L y :=
      Idele.ext fun p => by rw [hy p, Idele.normIdeleHom_apply]
    have hclass : w⁻¹ * NK.HeckeL.ideleOfPrime K v ∈ Idele.principalSubgroup K := by
      rw [← IdeleClassGroup.mk_eq_mk_iff, hwmk]
    obtain ⟨a, ha⟩ := Idele.mem_principalSubgroup.mp hclass
    have hdecomp : NK.HeckeL.ideleOfPrime K v
        = Idele.normIdeleHom K L y * Idele.principalIdele K a := by
      rw [hw'] at ha
      have h2 : Idele.normIdeleHom K L y * Idele.principalIdele K a
          = NK.HeckeL.ideleOfPrime K v := by
        rw [ha, mul_inv_cancel_left]
      exact h2.symm
    calc art (NK.HeckeL.ideleOfPrime K v)
        = art (Idele.normIdeleHom K L y * Idele.principalIdele K a) := by rw [hdecomp]
      _ = art (Idele.normIdeleHom K L y) * art (Idele.principalIdele K a) := map_mul art _ _
      _ = 1 := by rw [hNorm y, hPrin a, mul_one]
  -- the Frobenius normalisation at `v`
  have hFrobv : art (NK.HeckeL.ideleOfPrime K v) = NK.Chebotarev.frobAtPrime v := by
    by_cases hv : (m : 𝓞 K) ∈ v.asIdeal
    · rw [hAgree]
      exact frobAtPrime_eq_ideleArtin_of_mem_of_unramified hARL hunr hcomm m hm hram hprinc U hU
        hadj v (fun Q _ => NK.CFTLib.ramificationIdx_eq_one_of_differentIdeal_eq_top hunr Q) hv
    · exact hFrob v hv
  -- conclude
  have hfrob : NK.Chebotarev.frobAtPrime v = 1 := hFrobv.symm.trans hkill
  obtain ⟨Q, hQ⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) v
  haveI : Q.asIdeal.LiesOver v.asIdeal := hQ
  letI : MulSemiringAction (L ≃ₐ[K] L) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  rw [Ideal.inertiaDegIn_eq_inertiaDeg (A := 𝓞 K) (B := 𝓞 L) v.asIdeal Q.asIdeal (L ≃ₐ[K] L)]
  have horder := NK.CFTLib.ArtinReciprocityIdeal.orderOf_frobAtPrime_eq_inertiaDeg v Q hQ
    (fun P _ => NK.CFTLib.ramificationIdx_eq_one_of_differentIdeal_eq_top hunr P)
  rw [hfrob, orderOf_one] at horder
  exact horder.symm

end NK.CFTLib.Existence
