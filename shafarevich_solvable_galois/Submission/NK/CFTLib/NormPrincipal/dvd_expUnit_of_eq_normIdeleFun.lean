import Mathlib
import Submission.NK.CFTLib.normPrincipalDefs
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.Norm
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia degree divides `expUnit` of an element whose principal idèle is a norm

Let `K / F` be a finite Galois extension of number fields.  For a finite place `Q` of `F`, an
element `x : Fˣ` and an idèle `y : 𝕀 K`, the component at `Q` of the principal idèle of `x`
coincides with the component at `Q` of the norm idèle of `y`:

`(x)_Q = ∏_{q | Q} N_{K_q/F_Q}(y_q)`.

The main result of this file, `NK.CFTLib.NormPrincipal.dvd_expUnit_of_eq_normIdeleFun`, is
the local consequence: the inertia degree `f(Q) = [𝒪_K/q : 𝒪_F/Q]` (the same for all `q | Q`,
since the extension is Galois) divides the `Q`-adic valuation `expUnit Q x` of `x`.

The proof has three ingredients:

* `finVal_principalIdele` identifies `finVal F Q` of the principal idèle of `x` with
  `expUnit Q x` (`NK.CFTLib.normPrincipalDefs`);
* `finVal_prod` turns the `finVal` of the product over the primes `q | Q` into a sum;
* the local computation `finVal_localNormFinite` below: the valuation of the local norm of a
  unit is the inertia degree times the valuation, which is the standard fact
  `v_Q(N_{K_q/F_Q} z) = f(q|Q) · v_q(z)`, available in the workspace as
  `Commons.NumberTheory.NumberField.Completion.val_norm_units_adicCompletion_eq_pow_inertiaDeg`.

The last remaining bookkeeping step is that the "in" version of the inertia degree used in the
statement agrees with `Ideal.inertiaDeg (𝓞 F)` for a prime lying over `Q`, which is
`Ideal.inertiaDegIn_eq_inertiaDeg` (all primes over `Q` are conjugate because `K/F` is Galois).
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.NormPrincipal

/-- **The valuation of a local norm.**  For a finite Galois extension `K / F` of number fields, a
finite place `Q` of `F`, a place `q` of `K` lying over `Q` and a unit `z` of the local field
`K_q`, the `Q`-adic valuation of the local norm `N_{K_q/F_Q}(z)` (in additive coordinates
`NK.CFTLib.finVal`) is the inertia degree `f(q | Q)` times the `q`-adic valuation of `z`.

Equivalently, in the usual normalization `v_Q(N z) = (v_q z)^f`. -/
theorem finVal_localNormFinite {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (z : (q.adicCompletion K)ˣ) :
    NK.CFTLib.finVal F Q (NK.GlobalCFT.Place.localNormFinite q Q hq z) =
      (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) : ℤ) *
        NK.CFTLib.finVal K q z := by
  letI : Algebra (Q.adicCompletion F) (q.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have hh := Commons.NumberTheory.NumberField.Completion.val_norm_units_adicCompletion_eq_pow_inertiaDeg
    Q q hq z
  rw [NK.CFTLib.finVal, NK.CFTLib.finVal]
  rw [show ((NK.GlobalCFT.Place.localNormFinite q Q hq z : (Q.adicCompletion F)ˣ) :
      Q.adicCompletion F) = Algebra.norm (Q.adicCompletion F) (z : q.adicCompletion K) from rfl]
  rw [hh, WithZero.log_pow]
  ring

/-- **The inertia degree of a prime over `Q` is the common inertia degree `f(Q)`.**  For a finite
Galois extension `K / F` of number fields and a prime `q` of `𝒪_K` lying over the prime `Q` of
`𝒪_F`, `Ideal.inertiaDegIn Q (𝒪_K) = Ideal.inertiaDeg q (𝒪_F)`. -/
theorem inertiaDegIn_eq_inertiaDeg_of_liesOver {F K : Type} [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Ideal.inertiaDegIn Q.asIdeal (NumberField.RingOfIntegers K) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) := by
  letI : MulSemiringAction (K ≃ₐ[F] K) (NumberField.RingOfIntegers K) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers F) F K
      (NumberField.RingOfIntegers K)
  haveI : IsGaloisGroup (K ≃ₐ[F] K) (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers K) :=
    IsGaloisGroup.of_isFractionRing (K ≃ₐ[F] K) (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers K) F K
  exact Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers F)
    (B := NumberField.RingOfIntegers K) Q.asIdeal q.asIdeal (K ≃ₐ[F] K)

theorem dvd_expUnit_of_eq_normIdeleFun
    {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (x : Fˣ) (y : NK.GlobalCFT.Idele K)
    (h : (NK.GlobalCFT.Idele.principalIdele F x)
        (NK.GlobalCFT.Place.ofFinite Q) =
      (NK.GlobalCFT.Idele.normIdeleFun F K y) (NK.GlobalCFT.Place.ofFinite Q)) :
    (Ideal.inertiaDegIn Q.asIdeal (NumberField.RingOfIntegers K) : ℤ) ∣
      NK.GlobalCFTdeep.expUnit Q x := by
  classical
  -- the component of the principal idèle of `x` at `Q` has valuation `expUnit Q x`
  have hfin : NK.GlobalCFTdeep.expUnit Q x =
      NK.CFTLib.finVal F Q ((NK.GlobalCFT.Idele.normIdeleFun F K y)
        (NK.GlobalCFT.Place.ofFinite Q)) := by
    rw [← NK.CFTLib.finVal_principalIdele (K := K) Q x]
    exact congrArg (NK.CFTLib.finVal F Q) h
  rw [hfin]
  -- the norm component is the product of the local norms over the primes `q | Q`
  simp only [NK.GlobalCFT.Idele.normIdeleFun_ofFinite]
  rw [NK.CFTLib.finVal_prod]
  -- each summand is divisible by the inertia degree
  refine Finset.dvd_sum (fun q' _ => ?_)
  have hq' : q'.1.asIdeal.LiesOver Q.asIdeal :=
    (NK.GlobalCFT.Place.mem_primesOverFinite (K := F) (L := K) (Q := Q) (q := q'.1)).mp q'.2
  rw [finVal_localNormFinite Q q'.1 hq' (y (NK.GlobalCFT.Place.ofFinite q'.1)),
    ← inertiaDegIn_eq_inertiaDeg_of_liesOver Q q'.1 hq']
  exact dvd_mul_right _ _

end NK.CFTLib.NormPrincipal
