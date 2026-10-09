import Mathlib
import Submission.Work.SSGRoute.ZDataMup.CycleAux
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèlic Artin map of a cycle, and the product form of Hilbert reciprocity

This module builds the *global Artin map* of a finite Galois extension `L/K` of number fields out of
the congruence subgroup `Cycle.congrSubgroup c` of a **cycle** `c` (`CycleCongr.lean`) — an ideal
modulus, which unlike a natural-number modulus can be supported exactly on the ramified primes.

The three inputs are the adjustment of idèles and of idèlic norms by principal idèles
(`Cycle.exists_adjust`, `Cycle.exists_norm_adjust`), the vanishing of the Artin symbol on the
congruence-`1` idèlic norms (`Cycle.artinSym_idealOf_normIdeleHom_eq_one`) and the reciprocity law
in the form `Crux`: the Artin symbol of the principal ideal of a unit lying in the congruence
subgroup is trivial.  The latter is the *conductor drop* (`Cycle`-form of Neukirch V.6.1 /
Milne CFT VII.8.1(a)).

The output is a monoid homomorphism `𝕀 K →* Gal(L/K)` killing the principal idèles and the idèlic
norms and sending the idèle of a prime `Q ∉ c.supp` to the Frobenius at `Q`; in particular, if `c`
contains every ramified prime, it is Frobenius-normalised at *every* unramified prime — which is
the product form of Hilbert reciprocity (Milne, *CFT*, Theorem 8.1(a)).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain
open NK.GlobalCFT

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.CFTLib.Arl

namespace Cycle

variable {K : Type*} [Field K] [NumberField K]
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- `IsUnramifiedIn` (the form in which unramifiedness is stated at the target) is the
ideal-theoretic form of unramifiedness used by the reciprocity machinery. -/
theorem isUnramified_of_isUnramifiedIn (Q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (hQ : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q :=
  fun P hP => hQ P hP

/-- **The idèlic Artin map of a cycle.**  Let `L/K` be a finite Galois extension of number fields
and `c` a cycle of `K`.  Given the adjustment of idèles and of idèlic norms by principal idèles
into `Cycle.congrSubgroup c`, the triviality of the Artin symbol of the ideal of a congruence-`1`
idèlic norm, and the `Crux` (the Artin symbol of the principal ideal of a unit of the congruence
subgroup is trivial), there is `Φ : 𝕀 K →* Gal(L/K)` killing the principal idèles and the idèlic
norms and Frobenius-normalised at every prime outside `c`. -/
theorem exists_monoidHom_congrSubgroup [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) (c : Cycle K)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p → p ∈ c.supp)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (hhyp : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm c.congrSubgroup) :
    ∃ Φ : Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        Q ∉ c.supp →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  have hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ c.congrSubgroup :=
    Cycle.exists_adjust (K := K) c hlev
  have hadjN : ∀ y : Idele L, ∃ d : Lˣ,
      Idele.normIdeleHom K L (y * Idele.principalIdele L d) ∈ c.congrSubgroup :=
    Cycle.exists_norm_adjust (K := K) (L := L) c hlev
  have hnormId : ∀ w : Idele L, Idele.normIdeleHom K L w ∈ c.congrSubgroup →
      NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (Idele.idealOf (Idele.normIdeleHom K L w)) = 1 :=
    fun w hw => Cycle.artinSym_idealOf_normIdeleHom_eq_one (K := K) (L := L) hcomm c hram w hw
  let art : Idele K →* (L ≃ₐ[K] L) :=
    { toFun := NK.CFTLib.Arl.ideleArtin hcomm c.congrSubgroup hadj
      map_one' := NK.CFTLib.Arl.ideleArtin_one hcomm c.congrSubgroup hadj hhyp
      map_mul' := NK.CFTLib.Arl.ideleArtin_mul hcomm c.congrSubgroup hadj hhyp }
  have hprincipal : ∀ a : Kˣ, art (Idele.principalIdele K a) = 1 :=
    fun a => NK.CFTLib.Arl.ideleArtin_principal hcomm c.congrSubgroup hadj hhyp a
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    obtain ⟨e, he⟩ := hadjN y
    have hb : Idele.normIdeleHom K L y
        * Idele.principalIdele K (NK.CFTLib.Arl.adjust c.congrSubgroup hadj (Idele.normIdeleHom K L y))
        ∈ c.congrSubgroup :=
      NK.CFTLib.Arl.adjust_spec c.congrSubgroup hadj _
    set e' : Kˣ := NK.CFTLib.Arl.adjust c.congrSubgroup hadj (Idele.normIdeleHom K L y)
      * (Units.map (Algebra.norm K) e)⁻¹ with he'
    have hid : Idele.normIdeleHom K L y
          * Idele.principalIdele K (NK.CFTLib.Arl.adjust c.congrSubgroup hadj
              (Idele.normIdeleHom K L y))
        = Idele.normIdeleHom K L (y * Idele.principalIdele L e) * Idele.principalIdele K e' := by
      rw [map_mul, Idele.normIdeleHom_principalIdele, he', map_mul, map_inv]
      rw [mul_assoc,
        mul_left_comm (Idele.principalIdele K (Units.map (Algebra.norm K) e))
          (Idele.principalIdele K (NK.CFTLib.Arl.adjust c.congrSubgroup hadj
            (Idele.normIdeleHom K L y))),
        mul_inv_cancel, mul_one]
    have he'U : Idele.principalIdele K e' ∈ c.congrSubgroup := by
      have h1 : (Idele.normIdeleHom K L y
          * Idele.principalIdele K (NK.CFTLib.Arl.adjust c.congrSubgroup hadj
              (Idele.normIdeleHom K L y)))
          * (Idele.normIdeleHom K L (y * Idele.principalIdele L e))⁻¹ ∈ c.congrSubgroup :=
        c.congrSubgroup.mul_mem hb (c.congrSubgroup.inv_mem he)
      have h2 : (Idele.normIdeleHom K L y
          * Idele.principalIdele K (NK.CFTLib.Arl.adjust c.congrSubgroup hadj
              (Idele.normIdeleHom K L y)))
          * (Idele.normIdeleHom K L (y * Idele.principalIdele L e))⁻¹
          = Idele.principalIdele K e' := by
        rw [hid]
        rw [mul_comm (Idele.normIdeleHom K L (y * Idele.principalIdele L e))
            (Idele.principalIdele K e'), mul_assoc, mul_inv_cancel, mul_one]
      rwa [h2] at h1
    have hkey : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (Idele.idealOf (Idele.normIdeleHom K L (y * Idele.principalIdele L e))) = 1 :=
      hnormId _ he
    show NK.CFTLib.Arl.ideleArtin hcomm c.congrSubgroup hadj (Idele.normIdeleHom K L y) = 1
    calc NK.CFTLib.Arl.ideleArtin hcomm c.congrSubgroup hadj (Idele.normIdeleHom K L y)
        = NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
            (Idele.idealOf (Idele.normIdeleHom K L y
              * Idele.principalIdele K (NK.CFTLib.Arl.adjust c.congrSubgroup hadj
                  (Idele.normIdeleHom K L y)))) := rfl
      _ = NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
            (Idele.idealOf (Idele.normIdeleHom K L (y * Idele.principalIdele L e))
              * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (e' : K)) := by
          rw [hid, Idele.idealOf_mul, Idele.idealOf_principalIdele]
      _ = NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
            (Idele.idealOf (Idele.normIdeleHom K L (y * Idele.principalIdele L e)))
          * NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (e' : K)) :=
          NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm (Idele.idealOf_ne_zero _)
            (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero e'))
      _ = 1 := by rw [hkey, hhyp e' he'U, mul_one]
  have hfrob : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Q ∉ c.supp →
      art (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    intro Q hQ
    show NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (Idele.idealOf (NK.HeckeL.ideleOfPrime K Q *
        Idele.principalIdele K (NK.CFTLib.Arl.adjust c.congrSubgroup hadj
          (NK.HeckeL.ideleOfPrime K Q)))) = _
    have hQU : NK.HeckeL.ideleOfPrime K Q ∈ c.congrSubgroup :=
      Cycle.ideleOfPrime_mem_congrSubgroup c Q hQ
    have hbU : Idele.principalIdele K (NK.CFTLib.Arl.adjust c.congrSubgroup hadj
        (NK.HeckeL.ideleOfPrime K Q)) ∈ c.congrSubgroup := by
      have h2 := NK.CFTLib.Arl.adjust_spec c.congrSubgroup hadj (NK.HeckeL.ideleOfPrime K Q)
      have h3 := c.congrSubgroup.mul_mem (c.congrSubgroup.inv_mem hQU) h2
      rwa [inv_mul_cancel_left] at h3
    have hA : (Q.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr Q.ne_bot
    have hB : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        ((NK.CFTLib.Arl.adjust c.congrSubgroup hadj (NK.HeckeL.ideleOfPrime K Q) : Kˣ) : K) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)
    rw [Idele.idealOf_mul, NK.CFTLib.Arl.idealOf_ideleOfPrime, Idele.idealOf_principalIdele,
      NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm hA hB, hhyp _ hbU, mul_one,
      NK.CFTLib.Arl.artinSym_prime]
  exact ⟨art, hprincipal, hnorm, hfrob⟩


/-- **Hilbert reciprocity in the product form from the conductor drop at a cycle.**  Let `L/K` be a
finite cyclic extension of number fields and `c` a cycle of `K` which contains *exactly* the primes
ramified in `L/K`.  If the ideal-theoretic Artin symbol kills every principal ideal `(b)` with
`b ≡ 1 mod* c` and `b` totally positive (`hdrop`, the conductor drop), then there is
`Φ : 𝕀 K →* Gal(L/K)` killing the principal idèles and the idèlic norms and Frobenius-normalised at
*every* unramified prime. -/
theorem localGlobalMap_productFormula_of_cycleDrop [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (c : Cycle K)
    (hram : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q → Q ∈ c.supp)
    (hsupp : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Q ∈ c.supp → ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (hdrop : ∀ b : Kˣ, c.CongrOne b →
      NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (b : K)) = 1) :
    ∃ Φ : Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  have hhyp : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm c.congrSubgroup := fun b hb =>
    hdrop b ((Cycle.principalIdele_mem_congrSubgroup_iff (K := K) (c := c) hlev b).mp hb)
  obtain ⟨Φ, h1, h2, h3⟩ := Cycle.exists_monoidHom_congrSubgroup hcomm c hram hlev hhyp
  refine ⟨Φ, h1, h2, fun Q hunr => h3 Q (fun hQ => ?_)⟩
  exact hsupp Q hQ (Cycle.isUnramified_of_isUnramifiedIn (K := K) (L := L) Q hunr)

end Cycle

end Work.SSGRoute.ZDataMup
