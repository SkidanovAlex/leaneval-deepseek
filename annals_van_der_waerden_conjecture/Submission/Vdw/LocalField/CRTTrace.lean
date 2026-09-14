import Mathlib
import Submission.Vdw.LocalField.WildTrace
import Submission.Vdw.LocalField.TraceQuotient
import Submission.Commons.RingTheory.LocalRing.isLocalRing_quotient_int_pow

open scoped NumberField WithZero Topology
open IsDedekindDomain
open IsLocalRing
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# CRTTrace — the CRT trace decomposition at level `n` (S1 gate, step (e1))

With the level-`n` CRT splitting `F := 𝓞K ⧸ (p^n)𝓞K ≅ A × B`,
`A := 𝓞K ⧸ P^(e·n)`, `B := 𝓞K ⧸ Q^n` over `R := ℤ ⧸ (p^n)`
(`WildTrace.crt_ramified_quotient_iso`), the trace over `R` decomposes
additively over the CRT factors, and on the P-factor equals the reduction of
the integer trace:

* `Q_ne_bot_of_split` — the coprime factor `Q` of a genuine split is nonzero;
* **`crt_trace_identity`** — for `y ∈ Q^n` (so its `B`-class vanishes),
  `Tr_R(A)(mk_A y) = mk_R (Tr_ℤ y)`.  The proof assembles, inside the
  theorem body with local instances (the pattern of
  `WildTrace.module_free_quotientRamIdxPow`), the R-algebra equivalence
  `e : F ≃ₐ[R] A×B` and the freeness instances that `Algebra.trace_prod_apply`
  needs, then chains:
  `Tr_R(A)(mk_A y) = Tr_R(A)(mk_A y) + Tr_R(B)(mk_B y)`
  (since `mk_B y = 0`), `= Tr_R(A×B)(mk_A y, mk_B y)` (`trace_prod_apply`),
  `= Tr_R(A×B)(e (mk_F y))` (`crt_ramified_quotient_iso_mk`),
  `= Tr_R(F)(mk_F y)` (`trace_eq_of_algEquiv`),
  `= mk_R(Tr_ℤ y)` (`trace_quotient_int_pow`).

This is step (e1) of the S1-gate programme (Roadmap Session-130): it makes
the level-`(k+1)` wild trace of an element of `Q^(k+1)` computable as the
reduction of its integer trace, feeding the wild-witness construction
(`wild_count_le_of_wild_witness`) for `k := padicValNat p (P.ramificationIdx ℤ)`.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The coprime factor `Q` of a genuine split `(p)·𝓞K = P^e·Q` is nonzero
(the split ideal `(p)·𝓞K` is nonzero and `P^e ≠ ⊥`). -/
lemma Q_ne_bot_of_split (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsPrime] (Q : Ideal (𝓞 K))
    (hspl : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) =
      P ^ P.ramificationIdx ℤ * Q) :
    Q ≠ ⊥ := by
  classical
  intro hQ
  have hpK : ((p : ℕ) : 𝓞 K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  have hleft : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    intro hb
    have hmem0 : ((p : ℕ) : 𝓞 K) ∈ (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) := by
      have hm : (p : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) := Submodule.mem_span_singleton_self (p : ℤ)
      have hmap : algebraMap ℤ (𝓞 K) (p : ℤ) ∈
          (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) :=
        Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 K)) hm
      simpa using hmap
    have hz : ((p : ℕ) : 𝓞 K) = 0 := by
      rw [hb] at hmem0
      exact Ideal.mem_bot.mp hmem0
    exact hpK hz
  have hright : P ^ P.ramificationIdx ℤ * Q = ⊥ := by
    rw [hQ, Ideal.mul_bot]
  exact hleft (by rw [hspl, hright])

/-- **CRT trace identity (level `n`, step (e1))**: for `y ∈ Q^n` the trace
over `R := ℤ/(p^n)` of the `P^(e·n)`-class of `y` equals the reduction of
the integer trace of `y`.  The `B`-class of such a `y` vanishes, so the CRT
decomposition `F ≅ A×B` collapses the trace to the `A`-factor. -/
theorem crt_trace_identity (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (Q : Ideal (𝓞 K)) (hsup : P ⊔ Q = ⊤)
    (hspl : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) =
      P ^ P.ramificationIdx ℤ * Q)
    (n : ℕ) (hn : 0 < n) (y : 𝓞 K) (hyQ : y ∈ Q ^ n) :
    Algebra.trace (ℤ ⧸ (pPowIdeal p n)) ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n))
        (Ideal.Quotient.mk (P ^ (P.ramificationIdx ℤ * n)) y) =
      Ideal.Quotient.mk (pPowIdeal p n) (Algebra.intTrace ℤ (𝓞 K) y) := by
  classical
  let R := ℤ ⧸ (pPowIdeal p n)
  let A := (𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n)
  let B := (𝓞 K) ⧸ Q ^ n
  let F := (𝓞 K) ⧸ (fullQuotIdeal p n)
  haveI : P.IsPrime := (inferInstance : P.IsMaximal).isPrime
  letI : Algebra R F := instAlgebraQuotientIntPow p n
  letI : Algebra R A := instAlgebraQuotientRamIdxPow p P n
  letI : Algebra R B := RingHom.toAlgebra (quotientMap_int_pow_Q p P Q hspl n)
  let eRing := crt_ramified_quotient_iso p P Q hsup hspl n
  have hcomm : ∀ x : R, eRing (algebraMap R F x) = algebraMap R (A × B) x := by
    intro x
    rcases Ideal.Quotient.mk_surjective (I := pPowIdeal p n) x with ⟨z, hz⟩
    rw [← hz]
    calc
      eRing (algebraMap R F (Ideal.Quotient.mk (pPowIdeal p n) z))
          = eRing (Ideal.Quotient.mk (fullQuotIdeal p n) (algebraMap ℤ (𝓞 K) z)) := by
            rw [algebraMap_quotientIntPow_apply p n z]
      _ = (Ideal.Quotient.mk (P ^ (P.ramificationIdx ℤ * n)) (algebraMap ℤ (𝓞 K) z),
           Ideal.Quotient.mk (Q ^ n) (algebraMap ℤ (𝓞 K) z)) := by
            exact crt_ramified_quotient_iso_mk p P Q hsup hspl n (algebraMap ℤ (𝓞 K) z)
      _ = algebraMap R (A × B) (Ideal.Quotient.mk (pPowIdeal p n) z) := by
            apply Prod.ext
            · simp [quotientMap_int_pow, quotientMap_int_pow_Q]
            · simp [quotientMap_int_pow, quotientMap_int_pow_Q]
  let e : F ≃ₐ[R] (A × B) :=
    AlgEquiv.ofRingEquiv (R := R) (A₁ := F) (A₂ := A × B) (f := eRing) hcomm
  -- freeness instances needed by `Algebra.trace_prod_apply`
  letI : Module.Free R F := module_free_quotient_int_pow p n
  letI : Module.Projective R F := inferInstance
  haveI : Module.Finite R A := module_finite_quotientRamIdxPow p P n
  haveI : Module.Free R A := module_free_quotientRamIdxPow p P Q hsup hspl n hn
  have hQ : Q ≠ ⊥ := Q_ne_bot_of_split p P Q hspl
  haveI : Finite B := finite_quotient_Qpow p P Q hspl n hQ
  haveI : Module.Finite R B := Module.Finite.of_finite
  let iB : B →ₗ[R] F :=
    ((e.symm : (A × B) ≃ₐ[R] F).toLinearMap).comp (LinearMap.inr R A B)
  let sB : F →ₗ[R] B :=
    (LinearMap.snd R A B).comp ((e : F →ₐ[R] (A × B)).toLinearMap)
  have hsplitB : sB ∘ₗ iB = LinearMap.id := by
    ext b
    change LinearMap.snd R A B (e ((e.symm : (A × B) ≃ₐ[R] F) (LinearMap.inr R A B b))) = b
    rw [show e ((e.symm : (A × B) ≃ₐ[R] F) (LinearMap.inr R A B b)) = LinearMap.inr R A B b by
      exact AlgEquiv.apply_symm_apply e (LinearMap.inr R A B b)]
    simp
  haveI : Module.Projective R B := Module.Projective.of_split iB sB hsplitB
  haveI : Module.Flat R B := inferInstance
  haveI : IsLocalRing R := Commons.RingTheory.LocalRing.isLocalRing_quotient_int_pow p n hn
  haveI : Module.Free R B := Module.free_of_flat_of_isLocalRing (R := R) (P := B)
  -- main computation
  let mk_A : 𝓞 K → A := Ideal.Quotient.mk (P ^ (P.ramificationIdx ℤ * n))
  let mk_B : 𝓞 K → B := Ideal.Quotient.mk (Q ^ n)
  let mk_F : 𝓞 K → F := Ideal.Quotient.mk (fullQuotIdeal p n)
  have hpair : e (mk_F y) = (mk_A y, mk_B y) := by
    simpa [e, mk_A, mk_B, mk_F] using (crt_ramified_quotient_iso_mk p P Q hsup hspl n y)
  have hmkB : mk_B y = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hyQ
  calc
    Algebra.trace R A (mk_A y)
        = Algebra.trace R A (mk_A y) + Algebra.trace R B (mk_B y) := by
            rw [hmkB]
            simp
    _ = Algebra.trace R (A × B) (mk_A y, mk_B y) := by
            exact (Algebra.trace_prod_apply (R := R) (S := A) (T := B) (x := (mk_A y, mk_B y))).symm
    _ = Algebra.trace R (A × B) (e (mk_F y)) := by
            rw [← hpair]
    _ = Algebra.trace R F (mk_F y) := by
            exact (Algebra.trace_eq_of_algEquiv (A := R) (B := F) (C := A × B) e (mk_F y))
    _ = Ideal.Quotient.mk (pPowIdeal p n) (Algebra.intTrace ℤ (𝓞 K) y) := by
            exact (trace_quotient_int_pow (p := p) n y)


end
end Submission.Vdw.LocalField
