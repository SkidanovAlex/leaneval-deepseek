import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_finset_isBoundedIntegral
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Q`-adic exponent of the idèlic norm

For a finite extension `K / F` of number fields and an idèle `z` of `K`, the exponent of the
idèlic norm `N_{K/F} z` at a finite place `Q` of `F` is the sum of the exponents of `z` at the
primes `q` of `K` above `Q`, weighted by the inertia degrees:

`exp_Q (N z) = ∑_{q | Q} f(q/Q) · exp_q z`.

This is the idèlic form of the valuation formula `v_Q(N_{K_q/F_Q} x) = v_q(x)^{f(q/Q)}`; the
unramified hypothesis asked for in the statement is not needed (ramification affects `v_q(x)`
only through the exponent `e` in `v_{F_Q}(π) = v_{K_q}(x)^e`, which enters the formula through the
*fixed* normalisation at `Q`).

## Main results

* `NK.CFTLib.withZero_log_prod`: the logarithm of a finite product in `ℤᵐ⁰`.
* `NK.CFTLib.val_localNormFinite`: the local norm multiplies valuations by the inertia degree.
* `NK.CFTLib.exp_normIdeleHom_eq_sum`: the main formula.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

/-- The logarithm of a finite product in `WithZero (Multiplicative M)`, the factors being
nonzero: `log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i)`. -/
theorem withZero_log_prod {ι M : Type*} [AddCommMonoid M] {s : Finset ι}
    {f : ι → WithZero (Multiplicative M)} (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).log = ∑ i ∈ s, (f i).log := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        WithZero.log_mul hfa (Finset.prod_ne_zero_iff.mpr hfs), ih hfs]

/-- The local norm `N_{L_q/K_Q}` multiplies valuations by the inertia degree `f(q/Q)`:
`v_Q(N x) = v_q(x) ^ f(q/Q)`. -/
theorem val_localNormFinite {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (y : (q.adicCompletion L)ˣ) :
    Valued.v (Place.localNormFinite q Q hq y : Q.adicCompletion K) =
      (Valued.v (y : q.adicCompletion L)) ^ (q.asIdeal.inertiaDeg (𝓞 K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  rw [show Place.localNormFinite q Q hq =
    Units.map (Algebra.norm (Q.adicCompletion K)) from rfl]
  exact Norm.globalCFT_val_norm_adicCompletion_eq_pow_inertiaDeg Q q hq y

/-- **The exponent of the idèlic norm at a finite place.**  For a finite extension of number
fields `K / F`, an idèle `z` of `K` and a finite place `Q` of `F`, the `Q`-adic exponent of the
idèlic norm is the inertia-degree weighted sum of the exponents of `z` above `Q`. -/
theorem exp_normIdeleHom_eq_sum (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (hunr : ∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        q.asIdeal.LiesOver Q.asIdeal → q.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1)
    (z : NK.GlobalCFT.Idele K) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    NK.GlobalCFT.Idele.exp Q (NK.GlobalCFT.Idele.normIdeleHom F K z) =
      ∑ q ∈ NK.GlobalCFT.Place.primesOverFinite (K := F) (L := K) Q,
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) * NK.GlobalCFT.Idele.exp q z := by
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

end NK.CFTLib
