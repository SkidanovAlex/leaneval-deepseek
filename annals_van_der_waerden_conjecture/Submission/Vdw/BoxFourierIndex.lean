import Mathlib
import Submission.Vdw.FourierWeight
import Submission.Vdw.ResidueIndex
import Submission.Vdw.BoxFourier

open Polynomial Finset

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The per-prime Fourier bound for the index conditions (§4, applied)

The Fourier counting bound `ncard_box_residue_le_fourier_bound` counts integer
coefficient vectors in `(BddInt H)^m` whose reduction lies in a given set `T` of
residue vectors.  This module connects it to the project's Case-I per-prime
atom: the residue set is the set of coefficient vectors whose monic polynomial
`X^n + Σᵢ vᵢ Xⁱ` has index `≥ k` (`indexClass`, `ResidueIndex.lean`), and the
box polynomials correspond bijectively to their trailing coefficient vectors
(`boxEquivBddVec`, from `coeffVec`/`polyOfVec` of `Counting.lean`).

The result is the per-prime bound

    `#{f ∈ Box n H : index (f mod p) ≥ k} ≤
       |T_{p,k}|·(2H+1)^n/p^n + M/p^n·(5(p + 2H+1)(1 + log p))^n`

with `T_{p,k}` the index-`≥ k` residue set and `M` a bound for its Fourier
coefficients on the nonzero frequencies (the paper's `M(Ψ)`, Proposition
`ftgen2`).  Since `|T_{p,k}| = O(p^{n-k})`, this gives the shape
`O(H^n/p^k + M·p^{-n}(p log p)^n)` valid in the regime `H < p` where the
elementary per-coordinate bound `((2H+1)/p + 1)^n` loses.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

theorem polyOfVec_coeffVec (n H : ℕ) (f : ↥(Box n H)) :
    polyOfVec n H (coeffVec f) = f.1 := by
  refine Polynomial.ext (fun j => ?_)
  rcases lt_trichotomy j n with h | h | h
  · rw [coeff_polyOfVec_lt n H (coeffVec f) h]
    rfl
  · rw [h, coeff_polyOfVec_n n H (coeffVec f)]
    have h2 : f.1.coeff n = 1 := by
      calc f.1.coeff n = f.1.coeff f.1.natDegree := by
            rw [Polynomial.natDegree_eq_of_degree_eq_some f.2.2.1]
        _ = 1 := f.2.1.coeff_natDegree
    rw [h2]
  · have hlt : f.1.natDegree < j := by
      rw [Polynomial.natDegree_eq_of_degree_eq_some f.2.2.1]
      exact h
    rw [coeff_polyOfVec_gt n H (coeffVec f) h, Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

theorem coeffVec_polyOfVecBox (n H : ℕ) (v : BddVec n H) :
    coeffVec (polyOfVecBox n H v) = v := by
  funext i
  exact Subtype.ext (coeff_polyOfVec_lt n H v i.2)

/-- **The box is the coefficient-vector box**: a monic degree-`n` polynomial
with `|coeff i| ≤ H` is determined by, and determined by, its trailing
coefficient vector. -/
noncomputable def boxEquivBddVec (n H : ℕ) : ↥(Box n H) ≃ BddVec n H where
  toFun := coeffVec
  invFun := polyOfVecBox n H
  left_inv f := Subtype.ext (polyOfVec_coeffVec n H f)
  right_inv v := coeffVec_polyOfVecBox n H v

/-- The set of residue vectors whose monic polynomial `X^n + Σᵢ vᵢ Xⁱ` has
index `≥ k` (`indexClass`), as a Finset. -/
noncomputable def indexClassFinset (p : ℕ) [Fact (Nat.Prime p)] (n k : ℕ) :
    Finset (Fin n → ZMod p) := by
  classical
  exact Finset.univ.filter (fun v => indexClass (F := ZMod p) n k v)

/-- **The per-prime Fourier bound for the index conditions**: the number of box
polynomials whose reduction mod `p` has index `≥ k` is at most the trivial
density plus the Fourier error term, where `M` bounds the Fourier coefficients
of the index-`≥ k` residue set on the nonzero frequencies. -/
theorem box_index_fourier_le (p : ℕ) [Fact (Nat.Prime p)] (n H k : ℕ) (M : ℝ)
    (hM : 0 ≤ M)
    (h : ∀ a : Fin n → ZMod p, a ≠ 0 →
      ‖∑ v ∈ indexClassFinset p n k, ZMod.stdAddChar (∑ i, a i * v i)‖ ≤ M) :
    (Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f} : ℝ)
      ≤ ((indexClassFinset p n k).card : ℝ) * ((2 * H + 1 : ℕ) : ℝ) ^ n / (p : ℝ) ^ n
        + M / (p : ℝ) ^ n *
            (5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p)) ^ n := by
  classical
  have hcard : Nat.card {f : ↥(Box n H) // k ≤ boxIndex p n H f}
      = Nat.card {z : BddVec n H //
          (fun i => ((z i : ℤ) : ZMod p)) ∈ indexClassFinset p n k} := by
    refine Nat.card_congr ((boxEquivBddVec n H).subtypeEquiv ?_)
    intro f
    change k ≤ boxIndex p n H f ↔
      (fun i => (((coeffVec f) i : ℤ) : ZMod p)) ∈ indexClassFinset p n k
    have hres : (fun i => (((coeffVec f) i : ℤ) : ZMod p)) = boxResidue n H p f := rfl
    rw [hres, indexClassFinset, Finset.mem_filter]
    exact ⟨fun hf => ⟨Finset.mem_univ _, (boxIndex_iff_indexClass p n H k f).mp hf⟩,
      fun hf => (boxIndex_iff_indexClass p n H k f).mpr hf.2⟩
  rw [hcard]
  exact ncard_box_residue_le_fourier_bound p n H (indexClassFinset p n k) M hM h

end

end Submission.Vdw
