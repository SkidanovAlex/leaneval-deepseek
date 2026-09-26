/-
# Small decompositions of the propagation error at a neighbour, odd weight

For an **odd** weight `k` the CKMRV propagation argument (Proposition 3.2(1)) runs on the six
elements `MpElem i = ofSL (Mp i)`, `Mp = (I, T⁻¹, STS, S, ST⁻¹, TS)`, reducing the group algebra
`R = ℂ[SL(2,ℤ)]` modulo the odd-weight defect ideal

  `𝓘_odd = (T-I)²R + S (T-I)²R + (1+z)R`   (`z = -I`, `Work.Asymptotics.idealIOdd`).

The error of that reduction at `γ` and row `i` is

  `rowDiffOdd γ i = MpElem i * ofSL γ - ∑_j σ(γ)_{ij} MpElem j ∈ 𝓘_odd`
  (`Work.Asymptotics.PropagateCarriesOdd`).

The point of this file is the paper's "it is straightforward to check" (proof of Prop. 3.2(1)):
for every **neighbour** `ν` of the fundamental domain and every row `i`, the error can be
written with only two *monomial* carries:

  `rowDiffOdd ν i = (T-I)² A + S (T-I)² B + w`,   `w ∈ augIdealOdd`,   `A, B` monomial or 0.

Since a monomial carries acts on a function by a single translate, this is exactly the input
that makes the propagation relation `slash k (rowDiffOdd ν i) f = slash k A h₁ + slash k B h₂`
readable off the six translates `f|Mp_j` and the two defects (`Work.Asymptotics.slash_carry_odd`).

## Contents

* `rowDiffOdd_eq_of_decomp` : given that the six `MpElem`-classes span `R ⧸ 𝓘_odd`
  (`Work.Asymptotics.spanning_Mp_idealIOdd`) and that they are linearly independent there
  (`Work.Asymptotics.spMpSpan_inf_idealIOdd`), the element `u ∈ spMpSpan` occurring in the
  congruence `ofSL (Mp i * γ) ≡ u (mod 𝓘_odd)` is *unique*; hence the error is
  `ofSL (Mp i * γ) - u` for any such `u`.
* `small_decomp_neighbor_odd` : the decomposition with monomial carries.
-/
import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.PropagateCarriesOdd
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.exists_sigma_odd
import Submission.Work.Asymptotics.spanning_Mp_idealIOdd
import Submission.Work.Asymptotics.spMpSpan_inf_idealIOdd
import Submission.Work.Asymptotics.neighbour_decomp

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics

open Work.Kernels

/-- If `u ∈ spMpSpan` and `ofSL (Mp i * γ) - u ∈ 𝓘_odd`, then `u` is exactly the `σ`-row of
`γ`: the propagation error is `ofSL (Mp i * γ) - u`.  This uses the uniqueness of the
`spMpSpan`-part of the congruence, i.e. that the six `MpElem j` are linearly independent
modulo `𝓘_odd` (`Work.Asymptotics.spMpSpan_inf_idealIOdd`). -/
theorem rowDiffOdd_eq_of_decomp {γ : SL(2,ℤ)} (i : Fin 6) {u : R}
    (hu : u ∈ spMpSpan) (h : ofSL (Mp i * γ) - u ∈ idealIOdd) :
    rowDiffOdd γ i = ofSL (Mp i * γ) - u := by
  have hmem : rowDiffOdd γ i - (ofSL (Mp i * γ) - u) ∈ spMpSpan ⊓ idealIOdd := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · -- the `spMpSpan` part
      have hsplit : rowDiffOdd γ i
          = ofSL (Mp i * γ) - ∑ j, (sigmaHom γ) i j • MpElem j := by
        rw [rowDiffOdd, show (MpElem i : R) = ofSL (Mp i) from rfl, ← ofSL_mul]
      rw [hsplit]
      have hsum : (∑ j, (sigmaHom γ) i j • MpElem j) ∈ spMpSpan :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨j, rfl⟩)
      have : (ofSL (Mp i * γ) - ∑ j, (sigmaHom γ) i j • MpElem j) - (ofSL (Mp i * γ) - u)
          = u - ∑ j, (sigmaHom γ) i j • MpElem j := by abel
      rw [this]
      exact Submodule.sub_mem _ hu hsum
    · -- the ideal part
      rw [show rowDiffOdd γ i - (ofSL (Mp i * γ) - u)
          = rowDiffOdd γ i + -(ofSL (Mp i * γ) - u) from by abel]
      exact idealIOdd.add_mem (rowDiffOdd_mem_idealIOdd γ i) (idealIOdd.neg_mem h)
  have hzero : rowDiffOdd γ i - (ofSL (Mp i * γ) - u) = 0 := by
    rw [spMpSpan_inf_idealIOdd] at hmem
    simpa using hmem
  exact sub_eq_zero.mp hzero

/-- The `ofSL (Mp i * γ) - u` occurring in the congruence lies in `𝓘_odd` whenever
`ofSL (Mp i * γ) = u + (T-1)^2 A + S (T-1)^2 B + w` with `w ∈ augIdealOdd`. -/
lemma sub_ofSL_sub_eq_mem_idealIOdd {γ : SL(2,ℤ)} {u A B w : R} {i : Fin 6}
    (hw : w ∈ augIdealOdd)
    (heq : ofSL (Mp i * γ) = u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w) :
    ofSL (Mp i * γ) - u ∈ idealIOdd := by
  have hA : (R_T - 1)^2 * A ∈ idealIOdd :=
    IdealI_le_idealIOdd (mem_span2.mpr ⟨A, 0, by rw [mul_zero, add_zero]⟩)
  have hB : R_S * (R_T - 1)^2 * B ∈ idealIOdd :=
    IdealI_le_idealIOdd (mem_span2.mpr ⟨0, B, by rw [mul_zero, zero_add]⟩)
  have hw' : w ∈ idealIOdd := augIdealOdd_le_idealIOdd hw
  rw [heq]
  have : u + (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w - u
      = (R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B + w := by abel
  rw [this]
  exact idealIOdd.add_mem (idealIOdd.add_mem hA hB) hw'

theorem small_decomp_neighbor_odd {ν : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hν : ν ∈ Work.Asymptotics.NeighborsP) (i : Fin 6) :
    ∃ (A B : Work.Kernels.R),
      (A = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ),
        A = c • Work.Asymptotics.ofSL γ) ∧
      (B = 0 ∨ ∃ (c : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ),
        B = c • Work.Asymptotics.ofSL γ) ∧
      Work.Asymptotics.rowDiffOdd ν i
        - ((Work.Kernels.R_T - 1) ^ 2 * A + Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2 * B)
        ∈ Work.Asymptotics.augIdealOdd := by
  obtain ⟨A, B, u, hu, hA, hB, w, hw, heq⟩ := neighbour_decomp ν hν i
  refine ⟨A, B, hA, hB, ?_⟩
  rw [rowDiffOdd_eq_of_decomp i hu (sub_ofSL_sub_eq_mem_idealIOdd hw heq)]
  have : ofSL (Mp i * ν) - u - ((R_T - 1)^2 * A + R_S * (R_T - 1)^2 * B) = w := by
    rw [heq]; abel
  rw [this]
  exact hw

end Work.Asymptotics
