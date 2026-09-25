import Mathlib
import Submission.NK.NUV2.ARL.unifUnit_pow_mem_localNormSubgroup
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional
import Submission.NK.CFTLib.HR.Basic
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension

/-!
# Hilbert reciprocity for cyclotomic extensions at an unramified finite place

Let `L = K(ζ_q)` (`q` a prime), `Q` a finite place of `K` with `q ∉ Q`, and `b ∈ Kˣ` a local norm
at every place `v ≠ Q`.  Then `b` is a local norm at `Q` as well.

This is step **L3** (finite unramified case) of the design in
`Submission/Work/CFTLib/HR/STATUS.md` for Hilbert reciprocity `NK.CFTLib.HilbertReciprocityOnePlace`:
the "one place omitted" statement for the cyclotomic levels, whose global input is the *proved*
cyclotomic reciprocity law `NK.CFTLib.ARL.artinReciprocity_cyclotomic`.

## Proof

The modulus `m = q` is used (not `q · |N(𝔡)|`): the primes of `K` ramifying in `K(ζ_q)/K` divide
`(q)` (`NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`), so the ideal-theoretic reciprocity law
at `q` (`artinReciprocity_cyclotomic`) together with `exists_monoidHom_ideleArtin` produces an
idèlic Artin map `art : 𝕀_K →* Gal(L/K)` which

* kills the principal idèles `Kˣ` and the idèle norms `N_{L/K}𝕀_L`,
* carries `ideleOfPrime K 𝔭` to `frobAtPrime 𝔭` for **every** `𝔭` with `q ∉ 𝔭` — in particular at
  `Q`, since `q ∉ Q` (this is exactly why the modulus `q`, rather than a multiple of `q` containing
  the prime below `Q`'s residue characteristic, is used here).

Then `z := P(b) · (onePlace Q b_Q)⁻¹` is `b` away from `Q` and `1` at `Q`, hence an idèle norm by
the local–global principle, so `art (onePlace Q b_Q) = art (P(b)) = 1`; and the local kernel
computation `NK.NUV2.ARL.mem_localNormSubgroup_of_onePlace_mem_ker` (which rests on the
description `N_Q = {b | f(q|Q) ∣ v_Q(b)}` of the local norm group of an *unramified* local
extension) turns that into `b_Q ∈ N_Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ARL

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The idèlic Artin map of a cyclotomic prime level, with its congruence subgroup and
adjustment exposed.**

For `L = K(ζ_q)` (`q` prime) this provides the congruence subgroup `U` of modulus `q`, an adjustment
function, and the induced homomorphism `art = ideleArtin hcomm U hadj` together with the four
structural clauses.  Exposing `U`/`hadj` lets a caller evaluate `art` at *any* admissible multiplier
through `NK.NUV2.ARL.ideleArtin_eq_artinSym_of_mem` (used, e.g., to compute the archimedean value
`art (onePlace w (-1))`, see `Submission/Work/NUV2/ARL/NOTES_unifUnit_pow_mem_localNormSubgroup.md`). -/
theorem exists_artin_of_cyclotomic_prime_with_adjust (q : ℕ) [Fact q.Prime]
    [IsCyclotomicExtension {q} K L] :
    ∃ (U : Subgroup (Idele K))
      (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U)
      (art : Idele K →* Gal(L/K)),
      (∀ x : Idele K, art x
        = NK.CFTLib.Arl.ideleArtin (NK.CFTLib.HR.hcomm_of_isCyclotomic (K := K) (L := L) q)
            U hadj x) ∧
      (∀ a : Kˣ, art (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1) ∧
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ∧
      Function.Surjective art := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a :=
    NK.CFTLib.HR.hcomm_of_isCyclotomic (K := K) (L := L) q
  have hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal P.asIdeal
      (Gal(L/K))]
    exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := q) 𝔭 h𝔭 P hP
  have hprinc : NK.CFTLib.artinKillsPrincipal K L q :=
    fun a ha hpos s e σ hs hfac hfrob =>
      NK.CFTLib.ARL.artinReciprocity_cyclotomic K L q a ha hpos s e σ hs hfac hfrob
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K q hqpos
  obtain ⟨art, hagree, hprin, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm q hqpos hram hprinc
      U hU hadj
  refine ⟨U, hadj, art, ?_, hprin, ?_, hfrob, hsurj⟩
  · intro x
    rw [hagree]
  · intro y
    rw [hagree]
    have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K q :=
      SetLike.ext fun x => (hU.1 x).trans Iff.rfl
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm q hqpos hram
      hprinc U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L q hqpos z
    exact ⟨d, hUeq ▸ hd⟩

/-- **The idèlic Artin map of a cyclotomic prime level, at the modulus `q`.**

For `L = K(ζ_q)` (`q` prime) there is an idèlic Artin map `𝕀 K →* Gal(L/K)` killing the principal
idèles `Kˣ` and the idèle norms `N_{L/K}𝕀_L`, carrying `ideleOfPrime K 𝔭` to `frobAtPrime 𝔭` for
**every** prime `𝔭` with `q ∉ 𝔭`, and surjective.

Compared with `NK.CFTLib.HR.exists_artin_of_cyclotomic` (which uses the modulus
`q · |N(𝔡_{L/K})|` and therefore only knows the Frobenius normalisation at the primes `𝔭` not
dividing `(q · |N(𝔡)|)`), the modulus `q` is legitimate here because the primes of `K` ramifying in
`K(ζ_q)/K` all divide `(q)` (`NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`).  Consequently the
Frobenius normalisation is available at *every* prime `𝔭 ∤ (q)` — in particular at any unramified
`𝔭` whose residue characteristic differs from `q`, which is exactly the case needed in step L3 of
`Submission/Work/CFTLib/HR/STATUS.md`. -/
theorem exists_artin_of_cyclotomic_prime (q : ℕ) [Fact q.Prime]
    [IsCyclotomicExtension {q} K L] :
    ∃ art : Idele K →* Gal(L/K),
      (∀ a : Kˣ, art (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1) ∧
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ∧
      Function.Surjective art := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a :=
    NK.CFTLib.HR.hcomm_of_isCyclotomic (K := K) (L := L) q
  have hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal P.asIdeal
      (Gal(L/K))]
    exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := q) 𝔭 h𝔭 P hP
  have hprinc : NK.CFTLib.artinKillsPrincipal K L q :=
    fun a ha hpos s e σ hs hfac hfrob =>
      NK.CFTLib.ARL.artinReciprocity_cyclotomic K L q a ha hpos s e σ hs hfac hfrob
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K q hqpos
  obtain ⟨art, hagree, hprin, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm q hqpos hram hprinc
      U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K q :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm q hqpos hram
      hprinc U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L q hqpos z
    exact ⟨d, hUeq ▸ hd⟩
  exact ⟨art, hprin, hnorm, hfrob, hsurj⟩

/-- **Hilbert reciprocity for a cyclotomic prime level at an unramified finite place.**

For `L = K(ζ_q)` (`q` prime) and a finite place `Q` of `K` with `q ∉ Q`, a global element
`b ∈ Kˣ` which is a local norm at every place `v ≠ Q` is a local norm at `Q`. -/
theorem localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified
    (q : ℕ) [Fact q.Prime] [IsCyclotomicExtension {q} K L]
    (Q : HeightOneSpectrum (𝓞 K)) (hqQ : (q : 𝓞 K) ∉ Q.asIdeal) (b : Kˣ)
    (h : ∀ v : Place K, v ≠ Place.ofFinite Q →
      NK.CFTLib.localImageHom v b ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) :
    NK.CFTLib.localImageHom (Place.ofFinite Q) b ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  haveI : IsMulCommutative (Gal(L/K)) :=
    IsMulCommutative.of_comm (NK.CFTLib.HR.hcomm_of_isCyclotomic (K := K) (L := L) q)
  -- `K(ζ_q)/K` is unramified at every prime not dividing `q`
  have hunrHecke : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q :=
    NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := q) Q hqQ
  -- an idèlic Artin map at the modulus `q`
  obtain ⟨art, hprin, hnorm, hfrob, -⟩ := exists_artin_of_cyclotomic_prime (K := K) (L := L) q
  -- the Frobenius normalisation at `Q`
  have hfrobQ : art (NK.HeckeL.ideleOfPrime K Q) =
      NK.Chebotarev.frobAtPrime (K := K) (L := L) Q :=
    hfrob Q hqQ
  -- `z := P(b) · (onePlace Q b_Q)⁻¹` is an idèle norm
  set bQ : (Q.adicCompletion K)ˣ := NK.CFTLib.localImageHom (Place.ofFinite Q) b with hbQ
  set z : Idele K := Idele.principalIdele K b *
    (NK.HassePrinciple.onePlace (Place.ofFinite Q) bQ)⁻¹ with hz
  have hzmem : z ∈ Idele.normImage K L := by
    rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional]
    intro v
    by_cases hv : v = Place.ofFinite Q
    · subst hv
      refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      have hbQeq : (Idele.principalIdele K b) (Place.ofFinite Q) = bQ := by
        rw [hbQ, NK.CFTLib.localImageHom_apply, Idele.principalIdele_apply]
        rfl
      rw [hz, Idele.mul_apply, Idele.inv_apply, NK.HassePrinciple.onePlace_apply_self,
        hbQeq, mul_inv_cancel]
      exact Subgroup.one_mem _
    · refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      rw [hz, Idele.mul_apply, Idele.inv_apply, NK.HassePrinciple.onePlace_apply_ne hv,
        inv_one, mul_one, Idele.principalIdele_apply]
      exact h v hv
  -- hence `art (onePlace Q b_Q) = 1`
  obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hzmem
  have hzy : z = Idele.normIdeleHom K L y := by
    ext v
    rw [Idele.normIdeleHom_apply]
    exact congrArg Units.val (hy v)
  have hz1 : art z = 1 := by
    rw [hzy]
    exact hnorm y
  have hQ1 : art (NK.HassePrinciple.onePlace (Place.ofFinite Q) bQ) = 1 := by
    have h2 : art z = (art (NK.HassePrinciple.onePlace (Place.ofFinite Q) bQ))⁻¹ := by
      rw [hz, map_mul, map_inv, hprin b, one_mul]
    rw [hz1] at h2
    exact inv_eq_one.mp h2.symm
  -- the local kernel computation at the unramified place `Q`
  exact mem_localNormSubgroup_of_onePlace_mem_ker (K := K) (L := L) Q hunrHecke art hnorm hfrobQ hQ1

end NK.NUV2.ARL
