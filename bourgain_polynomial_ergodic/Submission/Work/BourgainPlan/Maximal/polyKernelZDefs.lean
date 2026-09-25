import Mathlib
import Submission.Work.BourgainPlan.Maximal.memlp_discAvgZC
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

/-!
# The `ℤ`-indexed density kernel of the polynomial average (arbitrary `P`, no sign hypothesis)

The corpus's density kernel `Submission.polyKernel P N j` counts the preimages of `j : ℕ` under
`(P.eval ·).toNat`, so the multiplier identity of the average
`discAvgZC P N g m = N⁻¹ Σ_{i<N} g (m + P.eval i)` requires the sign hypothesis
`NonnegOnNat P` (`Work.BourgainPlan.Maximal.ftLp_discAvgZC`).  The KMSZ §6.3 model realisation, on
the other hand, needs the identity for the *arbitrary* integer polynomial `P` of
`KMSZMajorArcStatement`.

This module supplies the correct object: the `ℤ`-indexed density kernel

`polyKernelZ P N j = N⁻¹ · #{i < N : P.eval i = j}`,

which is defined for every `P` (the shift `j` is an integer, so no `toNat` conversion is needed),
has finite support `[-polySupportZ, polySupportZ]`, and whose symbol
`Σ_j polyKernelZ P N j · e^{2πi j ξ} = N⁻¹ Σ_{i<N} e^{2πi ξ P(i)} = polyWeylKernel P N ξ` is the
Weyl kernel itself.  The multiplier identity
`ftLp (discAvgZC P N g) = khatZMult P N • ftLp g` is `ftLp_discAvgZC_z` (delegated).

The conjugate convention: `opMul (Σ_j c j • fourierLp (-j)) g n = Σ_j c j · g (n + j)`, so
`khatZMult` is the multiplier of the *forward* shift average `g ↦ Σ_j k(j) g (· + j)` — the same
convention as `khatMult` (`khatMult_coeFn` shows that its class is `conj ∘ khatCircle`).
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The `ℤ`-indexed density kernel** of the polynomial average:
`polyKernelZ P N j = N⁻¹ · #{i < N : P.eval i = j}`.  Unlike `Submission.polyKernel`, this is
defined for every integer polynomial (no `.toNat` conversion). -/
def polyKernelZ (P : Polynomial ℤ) (N : ℕ) (j : ℤ) : ℝ :=
  (N : ℝ)⁻¹ * (((Finset.range N).filter (fun i : ℕ => P.eval (i : ℤ) = j)).card : ℝ)

/-- A support bound for `polyKernelZ`: a strict upper bound for `|P.eval i|`, `i < N`. -/
def polySupportZ (P : Polynomial ℤ) (N : ℕ) : ℕ :=
  ((Finset.range N).image (fun i : ℕ => (P.eval (i : ℤ)).natAbs)).sup id + 1

/-- Every value `P.eval i`, `i < N`, has absolute value strictly below `polySupportZ P N`. -/
theorem eval_natAbs_lt_polySupportZ (P : Polynomial ℤ) (N : ℕ) (i : ℕ) (hi : i ∈ Finset.range N) :
    (P.eval (i : ℤ)).natAbs < polySupportZ P N := by
  unfold polySupportZ
  have hmem : (P.eval (i : ℤ)).natAbs ∈
      (Finset.range N).image (fun i : ℕ => (P.eval (i : ℤ)).natAbs) :=
    Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have := Finset.le_sup (f := id) hmem
  simp only [id_eq] at this
  omega

/-- The density kernel vanishes outside the support interval. -/
theorem polyKernelZ_eq_zero_of_polySupportZ_le_natAbs {P : Polynomial ℤ} {N : ℕ} {j : ℤ}
    (hj : polySupportZ P N ≤ j.natAbs) : polyKernelZ P N j = 0 := by
  unfold polyKernelZ
  have hcard : ((Finset.range N).filter (fun i : ℕ => P.eval (i : ℤ) = j)).card = 0 := by
    refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun i hi => ?_)
    obtain ⟨hiN, hij⟩ := Finset.mem_filter.mp hi
    have := eval_natAbs_lt_polySupportZ P N i hiN
    rw [hij] at this
    omega
  rw [hcard]
  simp


/-- **The symbol of the polynomial density average for an arbitrary integer polynomial**, as an
`L^∞(𝕋)`-class: `Σ_{|j| ≤ polySupportZ} polyKernelZ P N j • \bar e_j`.  It is the `ℤ`-indexed
counterpart of `khatMult` (which needs `NonnegOnNat P`). -/
def khatZMult (P : Polynomial ℤ) (N : ℕ) :
    Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)) :=
  ∑ j ∈ Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N),
    (polyKernelZ P N j : ℂ) • fourierLp (T := 1) (p := ⊤) (-j)

end

end Work.BourgainPlan.Maximal
