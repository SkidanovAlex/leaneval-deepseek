import Mathlib
import Submission.Vdw.LocalField.WildTrace

open scoped NumberField WithZero Topology
open IsDedekindDomain
open IsLocalRing

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# TraceQuotient — trace reduction at the full `(p^n)`-quotient

With the freeness of the full quotient `F := 𝓞K ⧸ (p^n)𝓞K` over
`R := ℤ ⧸ (p^n)` (`WildTrace.full_quotient_basis`), the trace over `R` of
the class of `x` is the reduction of the integer trace of `x`
(`trace_quotient_int_pow`), via the entrywise identification of the
multiplication matrices:

* `full_quotient_basis_repr` — the coordinates of the reduced basis: the
  `R`-representation of the class of `x` is the reduction of the `ℤ`-
  representation (`b.repr (mk x) = mk_pow ∘ b₀.repr x`);
* `full_quotient_leftMulMatrix_entry` — entrywise: the matrix of
  multiplication by `mk x` on the quotient equals the reduction of the
  matrix of multiplication by `x` on `𝓞K`;
* **`trace_quotient_int_pow`** — `Tr_{ℤ/(p^n)}(𝓞K ⧸ (p^n)𝓞K)(mk x) =
  mk (Tr_{ℤ} x)` (`Algebra.intTrace`).

This is the level-`n` analogue of Mathlib's
`Algebra.trace_quotient_eq_of_isDedekindDomain` (which covers only the
maximal-ideal / `n = 1` case).  It feeds the CRT trace decomposition of the
level-`(k+1)` wild trace (the S1 gate).  Axioms of every statement:
propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

lemma full_quotient_basis_repr (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (x : 𝓞 K) :
    (full_quotient_basis p n).repr (Ideal.Quotient.mk (fullQuotIdeal p n) x) =
      Finsupp.equivFunOnFinite.symm
        (fun i : Fin (Module.finrank ℤ (𝓞 K)) =>
          Ideal.Quotient.mk (pPowIdeal p n) ((Module.finBasis ℤ (𝓞 K)).repr x i)) := by
  classical
  let b0 : Module.Basis (Fin (Module.finrank ℤ (𝓞 K))) ℤ (𝓞 K) := Module.finBasis ℤ (𝓞 K)
  let b : Module.Basis (Fin (Module.finrank ℤ (𝓞 K))) (ℤ ⧸ (pPowIdeal p n))
      ((𝓞 K) ⧸ (fullQuotIdeal p n)) := full_quotient_basis p n
  let c : Fin (Module.finrank ℤ (𝓞 K)) → ℤ ⧸ (pPowIdeal p n) :=
    fun i => Ideal.Quotient.mk (pPowIdeal p n) (b0.repr x i)
  have hz : Ideal.Quotient.mk (fullQuotIdeal p n) x = ∑ i : Fin (Module.finrank ℤ (𝓞 K)), c i • b i := by
    calc
      Ideal.Quotient.mk (fullQuotIdeal p n) x
          = Ideal.Quotient.mk (fullQuotIdeal p n) (∑ i : Fin (Module.finrank ℤ (𝓞 K)), (b0.repr x) i • b0 i) := by
            congr 1
            exact (b0.sum_repr x).symm
      _ = ∑ i : Fin (Module.finrank ℤ (𝓞 K)), (Ideal.Quotient.mk (pPowIdeal p n) ((b0.repr x) i)) •
            (Ideal.Quotient.mk (fullQuotIdeal p n) (b0 i)) := by
            rw [map_sum]
            refine Finset.sum_congr rfl (fun i hi => ?_)
            exact (smul_quotientIntPow_mk (p := p) n ((b0.repr x) i) (b0 i)).symm
      _ = ∑ i : Fin (Module.finrank ℤ (𝓞 K)), c i • b i := by
            refine Finset.sum_congr rfl (fun i hi => ?_)
            congr 2
            dsimp [b, full_quotient_basis]
            rw [Module.Basis.mk_apply]
  calc
    b.repr (Ideal.Quotient.mk (fullQuotIdeal p n) x) = b.repr (∑ i : Fin (Module.finrank ℤ (𝓞 K)), c i • b i) := by rw [hz]
    _ = ∑ i : Fin (Module.finrank ℤ (𝓞 K)), c i • b.repr (b i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [map_smul]
    _ = ∑ i : Fin (Module.finrank ℤ (𝓞 K)), c i • (Finsupp.single i (1 : ℤ ⧸ (pPowIdeal p n))) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          congr 1
          exact (b.repr_self i)
    _ = Finsupp.equivFunOnFinite.symm c := by
          rw [Finsupp.equivFunOnFinite_symm_eq_sum]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          ext a
          by_cases ha : a = i <;> simp [ha]

/-- The matrix of multiplication on the quotient equals the reduction of the
matrix on `𝓞K`, entrywise. -/
lemma full_quotient_leftMulMatrix_entry (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (x : 𝓞 K)
    (i j : Fin (Module.finrank ℤ (𝓞 K))) :
    Algebra.leftMulMatrix (full_quotient_basis p n)
        (Ideal.Quotient.mk (fullQuotIdeal p n) x) i j =
      Ideal.Quotient.mk (pPowIdeal p n)
        (Algebra.leftMulMatrix (Module.finBasis ℤ (𝓞 K)) x i j) := by
  classical
  let R := ℤ ⧸ (pPowIdeal p n)
  let A := (𝓞 K) ⧸ (fullQuotIdeal p n)
  let b0 : Module.Basis (Fin (Module.finrank ℤ (𝓞 K))) ℤ (𝓞 K) := Module.finBasis ℤ (𝓞 K)
  let b : Module.Basis (Fin (Module.finrank ℤ (𝓞 K))) R A := full_quotient_basis p n
  let q : (𝓞 K) →+* A := Ideal.Quotient.mk (fullQuotIdeal p n)
  let π : ℤ →+* R := Ideal.Quotient.mk (pPowIdeal p n)
  rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
      LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  change b.repr (Algebra.lmul R A (q x) (b j)) i = π (b0.repr (Algebra.lmul ℤ (𝓞 K) x (b0 j)) i)
  have hbj : b j = q ((Module.finBasis ℤ (𝓞 K)) j) := by
    dsimp [b, full_quotient_basis]
    rw [Module.Basis.mk_apply]
  have hq : q x * q ((Module.finBasis ℤ (𝓞 K)) j) =
      q (x * (Module.finBasis ℤ (𝓞 K)) j) := (map_mul q x _).symm
  calc
    b.repr (Algebra.lmul R A (q x) (b j)) i
        = b.repr (q x * b j) i := by rfl
    _ = b.repr (q (x * (Module.finBasis ℤ (𝓞 K)) j)) i := by
          rw [hbj, ← map_mul q x ((Module.finBasis ℤ (𝓞 K)) j)]
    _ = π (b0.repr (x * (Module.finBasis ℤ (𝓞 K)) j) i) := by
          have hrepr := full_quotient_basis_repr (p := p) n (x * (Module.finBasis ℤ (𝓞 K)) j)
          have heval := congrArg (fun f : Fin (Module.finrank ℤ (𝓞 K)) →₀ (ℤ ⧸ (pPowIdeal p n)) => f i) hrepr
          simpa using heval
    _ = π (b0.repr (Algebra.lmul ℤ (𝓞 K) x (b0 j)) i) := by rfl

/-- **Trace reduction at the full quotient**: the trace over
`ℤ/(p^n)` of the quotient `𝓞K ⧸ (p^n)𝓞K` at the class of `x` is the
reduction of the integer trace of `x`. -/
theorem trace_quotient_int_pow (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (x : 𝓞 K) :
    Algebra.trace (ℤ ⧸ (pPowIdeal p n)) ((𝓞 K) ⧸ (fullQuotIdeal p n))
        (Ideal.Quotient.mk (fullQuotIdeal p n) x) =
      Ideal.Quotient.mk (pPowIdeal p n) (Algebra.intTrace ℤ (𝓞 K) x) := by
  classical
  let R := ℤ ⧸ (pPowIdeal p n)
  let A := (𝓞 K) ⧸ (fullQuotIdeal p n)
  let b0 : Module.Basis (Fin (Module.finrank ℤ (𝓞 K))) ℤ (𝓞 K) := Module.finBasis ℤ (𝓞 K)
  let b : Module.Basis (Fin (Module.finrank ℤ (𝓞 K))) R A := full_quotient_basis p n
  let π : ℤ →+* R := Ideal.Quotient.mk (pPowIdeal p n)
  rw [Algebra.intTrace_eq_trace]
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b0]
  rw [AddMonoidHom.map_trace π (Algebra.leftMulMatrix (Module.finBasis ℤ (𝓞 K)) x)]
  congr 1
  ext i j
  rw [Matrix.map_apply]
  exact full_quotient_leftMulMatrix_entry (p := p) n x i j

