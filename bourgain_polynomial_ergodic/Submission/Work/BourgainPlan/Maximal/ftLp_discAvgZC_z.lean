import Mathlib
import Submission.Work.BourgainPlan.Maximal.polyKernelZDefs
import Submission.Work.BourgainPlan.Maximal.khatMult
import Submission.Work.BourgainPlan.IonescuWainger.OpMulLinear

/-!
# The multiplier identity of the `ℤ`-indexed polynomial density average

This file proves `ftLp_discAvgZC_z`: for an **arbitrary** integer polynomial `P` (no sign
hypothesis), the density average `discAvgZC P N g m = N⁻¹ Σ_{i<N} g (m + P.eval i)` acts on
`ℓ²(ℤ) ≅ L²(𝕋)` as the Fourier multiplier with symbol `khatZMult P N`, i.e.

`𝓕 (discAvgZC P N g) = khatZMult P N • 𝓕 g`.

The proof is the `ℤ`-indexed counterpart of the proof of `ftLp_discAvgZC` (which requires
`NonnegOnNat P`), with `polyKernelZ` in place of the `ℕ`-indexed `polyKernel`:

* `discAvgZC_eq_kernelZ_sum`: the average is the finite fibre sum
  `Σ_{|j| ≤ polySupportZ P N} k_N(j) · g (· + j)` over the `ℤ`-indexed density kernel;
* `smul_finsetSum_int`: the multiplier with the sum symbol `Σ_j c_j • ψ_j` is `Σ_j c_j • (ψ_j ·)`;
* `opMul_fourierLp_neg` (`Maximal/khatMult.lean`): the multiplier with symbol
  `\bar e_j = fourierLp (-j)` is the shift `g ↦ g (· + j)`.
-/

namespace Work.BourgainPlan.Maximal

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

noncomputable section

open Work.BourgainPlan.IonescuWainger

/-- **The multiplier distributes over a finite sum of symbols**, for an arbitrary index type:
for `ψ_j ∈ L^∞(𝕋)` and `v ∈ L²(𝕋)`, the multiplier with symbol `Σ_j c_j • ψ_j` is
`Σ_j c_j • (ψ_j · v)`.  This is the general-index form of `Work.BourgainPlan.Maximal.smul_finsetSum`
(the `ℤ`-indexed sum of `khatZMult` needs it), i.e. the finite-sum form of `Lp.smul_add` together
with `Lp.smul_assoc`. -/
lemma smul_finsetSum_int {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (ψ : ι → Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
    (∑ j ∈ s, c j • ψ j) • v = ∑ j ∈ s, c j • (ψ j • v) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, MeasureTheory.Lp.smul_add, ih,
      MeasureTheory.Lp.smul_assoc]

/-- **The `ℤ`-density average as a fibre sum**: `A_N g (m) = Σ_j k_N(j) · g (m + j)`, summed
over the support `[-polySupportZ P N, polySupportZ P N]` of the `ℤ`-indexed density kernel.  This
is the general-`P` counterpart of `discAvgZC_eq_kernel_sum`: the fibre identity
`Finset.sum_fiberwise_of_maps_to` applied to `i ↦ P.eval i` on `{0, …, N-1}`, all of whose values
lie in the support interval (`eval_natAbs_lt_polySupportZ`). -/
lemma discAvgZC_eq_kernelZ_sum (P : Polynomial ℤ) (N : ℕ) (g : ℤ → ℂ) (m : ℤ) :
    discAvgZC P N g m
      = ∑ j ∈ Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N),
          (polyKernelZ P N j : ℂ) * g (m + j) := by
  have hfib := Finset.sum_fiberwise_of_maps_to
      (s := Finset.range N) (t := Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N))
      (g := fun i : ℕ => P.eval (i : ℤ))
      (fun i hi => Finset.mem_Icc.mpr (by
        have h := eval_natAbs_lt_polySupportZ P N i hi
        omega))
      (fun i : ℕ => ((N : ℂ)⁻¹) * g (m + P.eval (i : ℤ)))
  unfold discAvgZC polyKernelZ
  rw [Finset.mul_sum, ← hfib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- **The coefficients of the multiplier `opMul (khatZMult P N)`**: the `n`-th coefficient of
`opMul (khatZMult P N) g hg` is the kernel sum `Σ_j k_N(j) · g (n + j)`, i.e. the density average
`discAvgZC P N g n`. -/
lemma opMul_khatZMult_apply (P : Polynomial ℤ)
    (N : ℕ) (g : ℤ → ℂ) (hg : Memℓp g 2) (n : ℤ) :
    opMul (khatZMult P N) g hg n
      = ∑ j ∈ Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N),
          (polyKernelZ P N j : ℂ) * g (n + j) := by
  rw [opMul_apply]
  show inner ℂ (fourierBasis (T := 1) n)
      ((∑ j ∈ Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N),
          (polyKernelZ P N j : ℂ) • fourierLp (T := 1) (p := ⊤) (-j))
        • ftLp g hg)
    = ∑ j ∈ Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N),
        (polyKernelZ P N j : ℂ) * g (n + j)
  rw [smul_finsetSum_int]
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [inner_smul_right]
  congr 1
  show inner ℂ (fourierBasis (T := 1) n)
      (opMulLp (fourierLp (T := 1) (p := ⊤) (-j)) g hg) = g (n + j)
  rw [← opMul_apply]
  exact congrFun (opMul_fourierLp_neg j g hg) n

/-- The `ℓ²(ℤ) ≅ L²(𝕋)` multiplier identity of the polynomial density average for an *arbitrary* integer polynomial `P` (no sign hypothesis): with the `ℤ`-indexed density kernel `polyKernelZ` and its symbol `khatZMult`, `𝓕 (discAvgZC P N g) = khatZMult P N • 𝓕 g`.  This is the general-`P` counterpart of `Work.BourgainPlan.Maximal.ftLp_discAvgZC`, which requires `Submission.BourgainPlan.NonnegOnNat P` because its kernel is `ℕ`-indexed via `toNat`. -/
theorem ftLp_discAvgZC_z (P : Polynomial ℤ) (N : ℕ) (g : ℤ → ℂ) (hg : Memℓp g 2)
    (hX : Memℓp (Work.BourgainPlan.Maximal.discAvgZC P N g) 2) :
    Work.BourgainPlan.IonescuWainger.ftLp (Work.BourgainPlan.Maximal.discAvgZC P N g) hX
      = Work.BourgainPlan.Maximal.khatZMult P N
          • Work.BourgainPlan.IonescuWainger.ftLp g hg := by
  have hop : opMul (khatZMult P N) g hg = discAvgZC P N g := by
    funext n
    rw [opMul_khatZMult_apply P N g hg n, discAvgZC_eq_kernelZ_sum P N g n]
  exact (ftLp_congr_memℓp hop.symm hX (opMul_memℓp (khatZMult P N) g hg)).trans
    (ftLp_opMul (khatZMult P N) g hg)

end

end Work.BourgainPlan.Maximal
