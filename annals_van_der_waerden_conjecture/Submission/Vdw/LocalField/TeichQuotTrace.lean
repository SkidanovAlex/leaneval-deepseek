import Mathlib
import Submission.Vdw.LocalField.WildGenerator
import Submission.Commons.RingTheory.Trace.trace_isFractionRing
import Submission.Commons.RingTheory.Trace.trace_quotient_mk

/-!
# TeichQuotTrace — the trace of the Teichmüller generator in the local quotient

Continues `WildGenerator` (`p | f ∧ p | e` wild witness).  Two theorems:

* **`teich_localTrace_int`** — the `QpInt`-level local trace of the Teichmüller
  generator: `Algebra.trace (QpInt p) (kpInt p P) (teich p P α) =
  e • (-(g.nextCoeff))`.  From the fraction-field trace bridge
  `Commons.RingTheory.Trace.trace_isFractionRing` (trace over the fraction
  fields is the coercion of the trace over the rings) + `teich_localTrace_eq`
  (trace over `QpAdic`/`kpAdic`) + injectivity of `QpInt → QpAdic`.

* **`teich_quotTrace_ne_zero`** — the trace of the CLASS of `ζ` in the local
  quotient `kpInt ⧸ (p^n)kpInt` over `QpInt ⧸ (p^n)` is nonzero at the
  critical level `n = v_p(e) + 1`.  From
  `Commons.RingTheory.Trace.trace_quotient_mk` (trace over the quotient is the
  reduction of the trace) + `teich_localTrace_int` + `teich_localTrace_not_dvd`
  (the unit's exact `p`-adic order).

Together with the global↔local quotient identification
(`globalLocal_quotientIso`, `𝓞K ⧸ P^(e·n) ≃+* kpInt ⧸ (p^n)`) and the
approximation `𝓞K → kpInt ⧸ (p^n)` (`quotientToKpInt_surjective`), this
produces the element `z : 𝓞K` whose class trace in `𝓞K ⧸ P^(e(k+1))` over
`ℤ/(p^{k+1})` is nonzero — the input of
`WildWitnessReduction.exists_wild_witness_of_nonzero_trace`.

Axioms of both: propext / Classical.choice / Quot.sound only.
-/

open scoped NumberField WithZero Valued
open Classical
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Submission.Vdw.LocalField
noncomputable section
universe u
variable {K : Type u} [Field K] [NumberField K]


theorem teich_localTrace_int (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Algebra.trace (QpInt p) (kpInt p P) (teich p P α) =
      P.ramificationIdx ℤ • (-(teichMinpolyInt p P α).nextCoeff) := by
  haveI hst1 : IsScalarTower (QpInt p) (kpInt p P) (kpAdic p P) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rfl
  haveI hst2 : IsScalarTower (QpInt p) (QpAdic p) (kpAdic p P) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rfl
  have hfr := Commons.RingTheory.Trace.trace_isFractionRing
    (R := QpInt p) (S := kpInt p P) (K := QpAdic p) (L := kpAdic p P) (x := teich p P α)
  have hcoe : (algebraMap (kpInt p P) (kpAdic p P) (teich p P α)) =
      algebraMap (Wk p P α) (kpAdic p P) (zetaW p P α) := rfl
  rw [hcoe, teich_localTrace_eq p P hα hgen] at hfr
  have hinj : Function.Injective (algebraMap (QpInt p) (QpAdic p)) := IsFractionRing.injective _ _
  apply hinj
  rw [← hfr, map_nsmul]
  rfl

/-- The trace of the class of ζ in `kpInt ⧸ (p^n)kpInt` over `QpInt ⧸ (p^n)`
is nonzero at level `n = v_p(e) + 1`. -/
theorem teich_quotTrace_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (n : ℕ) (hn : n = padicValNat p (P.ramificationIdx ℤ) + 1)
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (htr : Algebra.trace (ZMod p) (kap p P) α ≠ 0) :
    Algebra.trace (QpInt p ⧸ (Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))))
        (kpInt p P ⧸ ((Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))).map
          (algebraMap (QpInt p) (kpInt p P))))
        (Ideal.Quotient.mk _ (teich p P α)) ≠ 0 := by
  set I : Ideal (QpInt p) :=
    Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p)) with hI
  have hq := Commons.RingTheory.Trace.trace_quotient_mk
    (R := QpInt p) (S := kpInt p P) I (teich p P α)
  rw [hq, teich_localTrace_int p P hα hgen]
  -- goal: mk I (e • t) ≠ 0
  intro h0
  rw [Ideal.Quotient.eq_zero_iff_mem] at h0
  refine teich_localTrace_not_dvd p P hα hgen htr ?_
  rw [hI, hn] at h0
  rwa [nsmul_eq_mul] at h0

end
end Submission.Vdw.LocalField
