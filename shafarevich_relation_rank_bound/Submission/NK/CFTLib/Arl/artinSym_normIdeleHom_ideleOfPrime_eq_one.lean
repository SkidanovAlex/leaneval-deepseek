import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.normIdeleHom_ideleOfPrime_div_mem_integralIdeles
import Submission.NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg
import Submission.NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver

/-!
# The Artin symbol kills the idèlic norm of a prime idèle

Let `L / K` be a finite abelian Galois extension of number fields and `𝔓` a prime of `𝓞 L`
which is unramified over `𝓞 K`.  Then the idèlic norm `N_{L/K}(ideleOfPrime L 𝔓)` has
fractional ideal `𝔭 ^ f`, where `𝔭` is the prime of `𝓞 K` below `𝔓` and `f = f(𝔓 | 𝔭)` is the
inertia degree; and since the Frobenius element at `𝔭` has order `f`, the Artin symbol of that
fractional ideal is trivial.

This is the elementary ("Milne's remark") half of "the Artin map kills norms": the norm of a
prime idèle at an unramified prime lies in the kernel of the Artin symbol.

The auxiliary lemma `exp_normIdeleHom_eq_sum_aux` is a universe-polymorphic copy of
`NK.CFTLib.exp_normIdeleHom_eq_sum'` (which is monomorphic at `Type 0` because of the
`set_option autoImplicit false` in its file).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Classical
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

open NK.GlobalCFT

/-- **The `Q`-adic exponent of the idèlic norm** (universe-polymorphic version of
`NK.CFTLib.exp_normIdeleHom_eq_sum'`): for a finite extension of number fields `K / F`, an
idèle `z` of `K` and a finite place `Q` of `F`, the `Q`-adic exponent of the idèlic norm is the
inertia-degree weighted sum of the exponents of `z` above `Q`. -/
theorem exp_normIdeleHom_eq_sum_aux (F K : Type*) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] (z : Idele K)
    (Q : HeightOneSpectrum (𝓞 F)) :
    Idele.exp Q (Idele.normIdeleHom F K z) =
      ∑ q ∈ Place.primesOverFinite (K := F) (L := K) Q,
        (q.asIdeal.inertiaDeg (𝓞 F) : ℤ) * Idele.exp q z := by
  classical
  have hz : ∀ q : HeightOneSpectrum (𝓞 K),
      Valued.v (z (Place.ofFinite q) : q.adicCompletion K) ≠ 0 :=
    fun q => (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  have hval : Valued.v ((Idele.normIdeleHom F K z) (Place.ofFinite Q) : Q.adicCompletion F)
      = ∏ q ∈ Place.primesOverFinite (K := F) (L := K) Q,
          (Valued.v (z (Place.ofFinite q) : q.adicCompletion K)) ^
            (q.asIdeal.inertiaDeg (𝓞 F)) := by
    rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofFinite, Units.coe_prod, map_prod]
    trans ∏ x ∈ (Place.primesOverFinite (K := F) (L := K) Q).attach,
        (Valued.v (z (Place.ofFinite (x : HeightOneSpectrum (𝓞 K))) :
          (x : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ^
          ((x : HeightOneSpectrum (𝓞 K)).asIdeal.inertiaDeg (𝓞 F))
    · exact Finset.prod_congr rfl (fun (x : {q : HeightOneSpectrum (𝓞 K) //
          q ∈ Place.primesOverFinite (K := F) (L := K) Q}) _ =>
        val_localNormFinite Q x.1
          ((Place.mem_primesOverFinite (K := F) (L := K) (Q := Q) (q := x.1)).mp x.2)
          (z (Place.ofFinite x.1)))
    · exact Finset.prod_attach (Place.primesOverFinite (K := F) (L := K) Q)
        (fun q => (Valued.v (z (Place.ofFinite q) : q.adicCompletion K)) ^
          (q.asIdeal.inertiaDeg (𝓞 F)))
  conv_lhs => rw [Idele.exp_def]
  rw [hval]
  rw [withZero_log_prod (fun q _ => pow_ne_zero _ (hz q))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [WithZero.log_pow, Idele.exp_def]
  ring

theorem artinSym_normIdeleHom_ideleOfPrime_eq_one {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (𝔓 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hunr : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔓.asIdeal.LiesOver 𝔭.asIdeal →
        𝔓.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (NK.GlobalCFT.Idele.idealOf
        (NK.GlobalCFT.Idele.normIdeleHom K L (NK.HeckeL.ideleOfPrime L 𝔓))) = 1 := by
  classical
  -- The prime of `𝓞 K` below `𝔓`.
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) 𝔓
  have hLies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal :=
    Ideal.LiesOver.mk (by
      rw [show 𝔭.asIdeal = Ideal.under (𝓞 K) 𝔓.asIdeal from rfl])
  -- Every prime of `𝓞 L` above `𝔭` is unramified over `𝓞 K` (Galois conjugates of `𝔓`).
  have hunr𝔭 : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      P.asIdeal.LiesOver 𝔭.asIdeal →
        P.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro P hP
    haveI : P.asIdeal.IsPrime := P.isPrime
    haveI : P.asIdeal.LiesOver 𝔭.asIdeal := hP
    haveI : 𝔓.asIdeal.IsPrime := 𝔓.isPrime
    haveI : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := hLies
    rw [Ideal.ramificationIdx_eq_of_isGaloisGroup (A := 𝓞 K) (B := 𝓞 L)
      𝔭.asIdeal P.asIdeal 𝔓.asIdeal (L ≃ₐ[K] L)]
    exact hunr 𝔭 hLies
  -- The chosen Frobenius at `𝔭` has order the inertia degree of `𝔓`.
  obtain ⟨P, hP, hPFrob⟩ := NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm 𝔭 hunr𝔭
  have hfrob𝔓 : NK.Chebotarev.IsFrobAt 𝔓 (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) :=
    isFrobAt_of_isFrobAt_any_primeOver hcomm hP hLies hPFrob
  have horder : orderOf (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
      = 𝔓.asIdeal.inertiaDeg (𝓞 K) :=
    NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg hLies (hunr 𝔭 hLies) hfrob𝔓
  have hpow : (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
      ^ ((𝔓.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← horder, pow_orderOf_eq_one]
  -- The fractional ideal of the norm idèle is the `f`-th power of `𝔭`.
  have hexps : exps (Idele.idealOf (Idele.normIdeleHom K L (NK.HeckeL.ideleOfPrime L 𝔓)))
      = Finsupp.single 𝔭 ((𝔓.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℤ) := by
    ext Q
    rw [exps_apply, Idele.count_idealOf, exp_normIdeleHom_eq_sum_aux K L
      (NK.HeckeL.ideleOfPrime L 𝔓) Q]
    have hsum : ∀ x : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
        Idele.exp x (NK.HeckeL.ideleOfPrime L 𝔓) = (if x = 𝔓 then (1 : ℤ) else 0) := by
      intro x
      unfold NK.HeckeL.ideleOfPrime
      exact IdeleClassGroup.exp_ideleOfFun _ _ x
    simp only [hsum, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    by_cases hQ : Q = 𝔭
    · subst hQ
      rw [if_pos (Place.mem_primesOverFinite.mpr hLies), Finsupp.single_eq_same]
    · have hnotmem : 𝔓 ∉ Place.primesOverFinite Q := by
        intro hmem
        exact hQ (IsDedekindDomain.HeightOneSpectrum.ext (by
          rw [(Place.mem_primesOverFinite.mp hmem).over, hLies.over]))
      rw [if_neg hnotmem, Finsupp.single_eq_of_ne hQ]
  -- Evaluate the Artin symbol of the `f`-th power of `𝔭`.
  letI := galCommMonoid hcomm
  unfold artinSym
  rw [hexps, Finsupp.prod_single_index (h := fun (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (e : ℤ) => (NK.Chebotarev.frobAtPrime (K := K) (L := L) q) ^ e)
    (show (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ (0 : ℤ) = 1 from zpow_zero _)]
  exact hpow

end NK.CFTLib.Arl
