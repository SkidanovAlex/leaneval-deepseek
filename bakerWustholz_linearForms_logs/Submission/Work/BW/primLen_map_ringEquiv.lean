import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

/-!
# `primLen` is invariant under a ring automorphism

`primLen I p` (`DefsMult.lean`) is the length of the local ring `(R/I)_p` (and `0` when `p` is
not prime). This file proves that it is invariant under a ring automorphism `e : R ≃+* R`:

  `primLen (I.map e) (p.map e) = primLen I p`.

The proof is assembled from three independent pieces, all proved below:

* `moduleLength_ringEquiv` : the length of a module is invariant under a semilinear additive
  equivalence `f : M ≃+ N` over a ring equivalence `φ : R ≃+* S` (i.e. `f (r • m) = φ r • f m`).
  This is proved by transporting the lattice of submodules along `f` and using that
  `Module.length` is the Krull dimension of the submodule lattice (`Module.coe_length`).
* `moduleLength_quotient_ringEquiv` : if `J = I.map φ` for a ring equivalence `φ : R ≃+* S`, then
  the quotients `R ⧸ I` and `S ⧸ J` have the same length as modules over their respective rings
  (`Ideal.quotientEquiv` provides the semilinear equivalence).
* `atPrime_map_ringEquiv` : a ring automorphism `e` induces a ring equivalence
  `Localization.AtPrime (p.map e) ≃+* Localization.AtPrime p` sending `algebraMap r` to
  `algebraMap (e.symm r)` (`IsLocalization.ringEquivOfRingEquiv`).

Feeding the localization equivalence into the second piece (after transporting the extended
ideal along it, `Ideal.map_map` plus `Ideal.map_of_equiv`) gives the prime case of the target;
the remaining (non-prime) case is vacuous since `p.map e` is prime iff `p` is prime.
-/

namespace Work.BW

/-- **Length is invariant under a semilinear additive equivalence.** If `φ : R ≃+* S` is a ring
equivalence and `f : M ≃+ N` is an additive equivalence with `f (r • m) = φ r • f m`, then `M`
and `N` have the same length over `R` and `S` respectively. -/
theorem moduleLength_ringEquiv {R S : Type*} [Ring R] [Ring S]
    {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module S N]
    (φ : R ≃+* S) (f : M ≃+ N) (hf : ∀ (r : R) (m : M), f (r • m) = φ r • f m) :
    Module.length R M = Module.length S N := by
  let F : M →ₛₗ[(φ : R →+* S)] N := { toFun := f, map_add' := f.map_add, map_smul' := hf }
  haveI : RingHomSurjective (φ : R →+* S) := ⟨φ.surjective⟩
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective F f.bijective)]

/-- **Lengths of quotients by corresponding ideals under a ring equivalence.** If `φ : R ≃+* S`
is a ring equivalence and `J = I.map φ`, then `R ⧸ I` (as an `R`-module) and `S ⧸ J` (as an
`S`-module) have the same length. -/
theorem moduleLength_quotient_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (φ : R ≃+* S)
    (I : Ideal R) (J : Ideal S) (h : J = Ideal.map (φ : R →+* S) I) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) := by
  refine moduleLength_ringEquiv φ (Ideal.quotientEquiv I J φ h).toAddEquiv (fun r x => ?_)
  show Ideal.quotientEquiv I J φ h (r • x) = φ r • Ideal.quotientEquiv I J φ h x
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

/-- **Localization at a prime ideal transported along a ring automorphism.** For `e : R ≃+* R`
and a prime ideal `p`, the localizations at `p` and at `p.map e` are isomorphic, and the
isomorphism sends `algebraMap r` to `algebraMap (e.symm r)`. -/
theorem atPrime_map_ringEquiv {R : Type*} [CommRing R] (e : R ≃+* R) (p : Ideal R)
    [p.IsPrime] [(Ideal.map (e : R →+* R) p).IsPrime] :
    ∃ φ : Localization.AtPrime (Ideal.map (e : R →+* R) p) ≃+* Localization.AtPrime p,
      ∀ x : R, φ (algebraMap R (Localization.AtPrime (Ideal.map (e : R →+* R) p)) x)
        = algebraMap R (Localization.AtPrime p) (e.symm x) := by
  have hM : Submonoid.map e.symm.toMonoidHom (Ideal.primeCompl (Ideal.map (e : R →+* R) p))
      = Ideal.primeCompl p := by
    show Submonoid.map (e.symm : R ≃+* R) (Ideal.primeCompl (Ideal.map (e : R →+* R) p))
      = Ideal.primeCompl p
    ext x
    rw [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩ hx
      exact hy ((Ideal.symm_apply_mem_of_equiv_iff (f := e) (I := p) (y := y)).mp
        (by rw [hyx]; exact hx))
    · intro hx
      refine ⟨e x, ?_, e.symm_apply_apply x⟩
      intro hm
      exact hx (by simpa using
        (Ideal.symm_apply_mem_of_equiv_iff (f := e) (I := p) (y := e x)).mpr hm)
  refine ⟨IsLocalization.ringEquivOfRingEquiv _ _ (e.symm) hM, fun x => ?_⟩
  exact IsLocalization.ringEquivOfRingEquiv_eq hM x

/-- `primLen` (the length of the local ring `(R/I)_p`, `DefsMult.lean`) is invariant under a ring
automorphism: for `e : R ≃+* R`, `I' = I.map e`, `p' = p.map e` the rings `R/I` and `R/I'` are
isomorphic and this iso carries `p` to `p'`, so the two localizations at the corresponding primes
are isomorphic and the lengths of the localized quotients agree. -/
theorem primLen_map_ringEquiv {R : Type*} [CommRing R] (e : R ≃+* R) (I p : Ideal R) :
    primLen (Ideal.map (e : R →+* R) I) (Ideal.map (e : R →+* R) p) = primLen I p := by
  classical
  have hker : RingHom.ker (e : R →+* R) ≤ p := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx' : x = 0 := e.injective (by simpa using hx)
    rw [hx']; exact p.zero_mem
  have hcomap : Ideal.comap (e : R →+* R) (Ideal.map (e : R →+* R) p) = p := by
    rw [Ideal.comap_map_of_surjective' (f := (e : R →+* R)) e.surjective p, sup_eq_left.mpr hker]
  by_cases hp : p.IsPrime
  · haveI : p.IsPrime := hp
    have hp' : (Ideal.map (e : R →+* R) p).IsPrime :=
      Ideal.map_isPrime_of_surjective (f := (e : R →+* R)) e.surjective hker
    haveI : (Ideal.map (e : R →+* R) p).IsPrime := hp'
    rw [primLen, primLen, dite_eq_left hp', dite_eq_left hp]
    obtain ⟨φ, hφ⟩ := atPrime_map_ringEquiv (R := R) e p
    have hcomp : (φ : Localization.AtPrime (Ideal.map (e : R →+* R) p) →+*
          Localization.AtPrime p).comp
        (algebraMap R (Localization.AtPrime (Ideal.map (e : R →+* R) p)))
        = (algebraMap R (Localization.AtPrime p)).comp (e.symm : R →+* R) := by
      ext x
      simp only [RingHom.comp_apply]
      exact hφ x
    have hideal : Ideal.map (φ : Localization.AtPrime (Ideal.map (e : R →+* R) p) →+*
          Localization.AtPrime p)
        (Ideal.map (algebraMap R (Localization.AtPrime (Ideal.map (e : R →+* R) p)))
          (Ideal.map (e : R →+* R) I))
        = Ideal.map (algebraMap R (Localization.AtPrime p)) I := by
      rw [Ideal.map_map, hcomp, ← Ideal.map_map, Ideal.map_of_equiv e]
    exact moduleLength_quotient_ringEquiv φ _ _ hideal.symm
  · have hp' : ¬ (Ideal.map (e : R →+* R) p).IsPrime := by
      intro h
      haveI := h
      have h2 := Ideal.comap_isPrime (f := (e : R →+* R)) (Ideal.map (e : R →+* R) p)
      rw [hcomap] at h2
      exact hp h2
    rw [primLen, primLen, dite_eq_right hp', dite_eq_right hp]

end Work.BW
