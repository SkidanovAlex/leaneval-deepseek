import Mathlib
import Mathlib.NumberTheory.Padics.PadicNumbers
import Submission.Vdw.LocalField.Completion
import Submission.Commons.NumberTheory.NumberField.ideal_valuation_rat_pow_of_liesOver
import Submission.Commons.NumberTheory.NumberField.withVal_algebraMap_uniformContinuous
import Submission.Commons.NumberTheory.NumberField.adicCompletion_algebra_exists

open scoped NumberField
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (stone 2): the `ℚ_p`-base and the completion tower

With `K_P := Completion.kpAdic p P` in the graph (stone 1), this module names
the base: `qprime p : HeightOneSpectrum ℤ` (the height-one prime `(p)` of
`ℤ`) and `QpAdic p := (qprime p).adicCompletion ℚ`, the completion of `ℚ` at
`p` — `ℚ_[p]`-equivalent via
`Rat.HeightOneSpectrum.adicCompletion.padicEquiv` (whose codomain is
`ℚ_[primesEquiv (qprime p)]`, defeq-reducible to `ℚ_[p]` by the
proof-irrelevance of the prime witness).

**Goal (recorded): the `ℚ_p`-algebra structure on `K_P`.**  For a maximal
ideal `P | (p)` the field embedding `ℚ ↪ K` is continuous for the `(p)`-adic
and `P`-adic valuations (compatibility `P | (p)`), so the uniform-space
completion functor extends it to a continuous `ℚ`-algebra map
`ℚ̂_{(p)} → K̂_P`, i.e. (after `padicEquiv`) `Algebra ℚ_[p] (kpAdic p P)`.
Mathlib provides the *field*-algebra instances (`Algebra ℚ (QpAdic p)`,
`Algebra ℚ (kpAdic p P)`, `Algebra K (kpAdic p P)`, verified below) but not
the completed-base algebra (the finite-place `LiesOver` tower
`NumberField/Completion/FinitePlace.lean` assumes it as a hypothesis).  The
missing lemma — uniform continuity of `algebraMap ℚ K` w.r.t. the
`(qprime p)`- and `(kprime p P)`-adic uniformities — is the next sub-stone
(needs the rational-valued compatibility `v_P(x) = e_P·v_p(x)` on `x ∈ ℚ`).
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

/-- The height-one prime ideal `(p)` of `ℤ`. -/
noncomputable def qprime (p : ℕ) [Fact (Nat.Prime p)] :
    IsDedekindDomain.HeightOneSpectrum ℤ := by
  classical
  have hpZ : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := by
    intro hz
    have hp0 : (p : ℤ) = 0 := (Ideal.span_singleton_eq_bot.mp hz)
    exact (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)) (by omega)
  exact IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime hpZ (by infer_instance))

/-- The completion of `ℚ` at the prime `p` (the `p`-adic numbers, up to the
`padicEquiv` identification with `ℚ_[p]`). -/
abbrev QpAdic (p : ℕ) [Fact (Nat.Prime p)] : Type :=
  (qprime p).adicCompletion ℚ

variable {K : Type u} [Field K] [NumberField K]

/-- `K` is dense in its completion `K_P`. -/
theorem kpAdic_denseRange_algebraMap (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    DenseRange (algebraMap K (kpAdic p P)) := by
  simpa [kpAdic] using
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) (v := kprime p P))

/- Structural instances (verified by compilation in the development):
`Field (QpAdic p)`, `Algebra ℚ (QpAdic p)`, `Algebra ℚ (kpAdic p P)`,
`Algebra K (kpAdic p P)`, `Algebra ℤ (kpInt p P)` — all synthesized by
Mathlib's `adicCompletion` machinery.  The canonical maps are the dense
embeddings `algebraMap ℚ (QpAdic p)` (resp. `algebraMap K (kpAdic p P)`),
with the scalar tower `ℚ → K → K_P`. -/

/-- **Valuation compatibility (local form).**  For a maximal ideal `P` over
`(p)` with ramification index `e`, the `P`-adic valuation of a rational `x`
(viewed in `K`) equals the `e`-th power of its `(p)`-adic valuation:
`v_P(x) = (v_p x)^e` in `ℤᵐ⁰`.  (Fleet L92:
`Commons.NumberTheory.NumberField.ideal_valuation_rat_pow_of_liesOver`,
instantiated at `kprime p P` and `qprime p`.)  This is the content of the
uniform-continuity lemma for `algebraMap ℚ K`. -/
theorem valuation_rat_pow_ramificationIdx (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : ℚ) :
    (kprime p P).valuation K (x : K) =
      ((qprime p).valuation ℚ x) ^ P.ramificationIdx ℤ := by
  classical
  have hV : (kprime p P).asIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa [kprime] using (‹P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))› : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
  have hv : (qprime p).asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    rfl
  simpa [kprime_asIdeal] using
    (Commons.NumberTheory.NumberField.ideal_valuation_rat_pow_of_liesOver
      (K := K) (p := p) (V := kprime p P) hV (v := qprime p) hv x)

/-- **Uniform continuity of `algebraMap ℚ K` (local form).**  Between the
`(p)`-adic uniform structure on ℚ and the `P`-adic uniform structure on K
(the `WithVal`-valued types), the rational-algebra map is uniformly
continuous — the completion-functoriality input (fleet L93:
`withVal_algebraMap_uniformContinuous`, instantiated at `kprime p P` /
`qprime p`). -/
theorem withVal_algebraMap_uniformContinuous_rat (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    UniformContinuous
      (fun x : WithVal ((qprime p).valuation ℚ) =>
        WithVal.toVal ((kprime p P).valuation K) (algebraMap ℚ K (WithVal.ofVal x))) := by
  classical
  have hV : (kprime p P).asIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa [kprime] using (‹P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))› : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
  have hv : (qprime p).asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    rfl
  simpa [kprime, qprime] using
    (Commons.NumberTheory.NumberField.withVal_algebraMap_uniformContinuous
      (K := K) (p := p) (V := kprime p P) hV (v := qprime p) hv)

/-- **The `ℚ_p`-algebra structure on `K_P` exists (stone 2 complete).**
`Nonempty (Algebra (QpAdic p) (kpAdic p P))` — the `P`-adic completion of the
number field `K` is a `ℚ_p`-algebra (fleet L95:
`adicCompletion_algebra_exists`, instantiated at `kprime p P` / `qprime p`).
Transport to `Algebra ℚ_[p] (kpAdic p P)` via `padicEquiv` when the trace
identity needs the `Padic`-spelled scalars. -/
theorem kpAdic_algebra_qp_exists (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Nonempty (Algebra (QpAdic p) (kpAdic p P)) := by
  classical
  have hV : (kprime p P).asIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa [kprime] using (‹P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))› : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
  have hv : (qprime p).asIdeal = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    rfl
  simpa [QpAdic, kpAdic] using
    (Commons.NumberTheory.NumberField.adicCompletion_algebra_exists
      (K := K) (p := p) (V := kprime p P) hV (v := qprime p) hv)

end
end Submission.Vdw.LocalField
