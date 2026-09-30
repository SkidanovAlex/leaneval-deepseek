import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.minkowski_second_l1
import Submission.Work.BW.basis_reduction_l1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive). Route design: BW = Baker–Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# minkowski_basis — Minkowski II + BW L4 (p. 27–28); 3–5k lines, medium risk

**Claim.** Let the lattice `Ω = Aℤⁿ` have `det A ≠ 0`, and let `F(x) = ∑cᵢ|xᵢ|`. Then some basis
`AU` with `U ∈ GL_n(ℤ)` satisfies `∏ F(col_j) ≤ (n!)²/2^{n-1}·|det A|·∏cᵢ`.

**Proof.**
1. `vol{F<1} = 2ⁿ/(n!∏cᵢ)`.
2. Minkowski's second inequality `λ₁⋯λₙ·vol ≤ 2ⁿ det` gives `∏λ ≤ n!∏cᵢ|det A|`.
   * Mathlib has only the **first** convex-body result
     (`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`).
   * The second must be proved. Estermann's or Henk's short proof works, or Davenport's for
     general convex bodies.
3. BW L4 turns successive-minima vectors into a basis with `F(w₁) ≤ λ₁` and `F(w_j) ≤ jλ_j/2`.
   The argument (BW p. 28) is a nearest-integer reduction.

**Tightness.** The constant is exactly consumed at `r = n`: `κ'(n)κ(n) = C(n,d)` with
equality. So do not weaken `(n!)²/2^{n-1}`.

**Used by.** `kummer_reduction` (§9) and `group_reduction` (§10/§21, the primitive forms).
-/

namespace Work.BW

/-- Minkowski's second inequality for the weighted `ℓ¹` body `F(x) = ∑ cᵢ|xᵢ|` combined with BW
L4 (a basis with `F(w₁) ≤ λ₁`, `F(w_j) ≤ jλ_j/2`): the lattice `A ℤⁿ` has a basis
`A U` (`U ∈ GL_n(ℤ)`) with `∏_j F(col_j) ≤ (n!)²/2^{n-1} · |det A| · ∏ cᵢ`. -/
theorem minkowski_basis {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U.det ∧
      ∏ j, (∑ i, c i * |(((A * U) i j : ℤ) : ℝ)|) ≤
        ((n.factorial : ℝ) ^ 2 / 2 ^ (n - 1)) * |((A.det : ℤ) : ℝ)| * ∏ i, c i := by
  -- BW L4: reduce the successive-minima vectors to a basis of the lattice `A ℤⁿ`.
  obtain ⟨U, hU, hUbound⟩ := basis_reduction_l1 hn A hA c hc
  refine ⟨U, hU, ?_⟩
  -- Minkowski's second inequality (sharp form) for the weighted `ℓ¹` body.
  have hMink := minkowski_second_l1 hn A hA c hc
  have hcpos : (0 : ℝ) ≤ (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) := by positivity
  have hstep : (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) *
        ∏ j : Fin n, succMin (latOf A) (wl1 c) (j.1 + 1)
      ≤ (n.factorial : ℝ) / (2 : ℝ) ^ (n - 1) *
        ((n.factorial : ℝ) * |((A.det : ℤ) : ℝ)| * ∏ i, c i) :=
    mul_le_mul_of_nonneg_left hMink hcpos
  have hmain : ∏ j, (∑ i, c i * |(((A * U) i j : ℤ) : ℝ)|)
      ≤ ((n.factorial : ℝ) ^ 2 / (2 : ℝ) ^ (n - 1)) * |((A.det : ℤ) : ℝ)| * ∏ i, c i := by
    have h1 : ∏ j, (∑ i, c i * |(((A * U) i j : ℤ) : ℝ)|)
        = ∏ j : Fin n, wl1 c (fun i => (((A * U) i j : ℤ) : ℝ)) := rfl
    rw [h1]
    refine le_trans hUbound (le_trans hstep ?_)
    exact le_of_eq (by ring)
  exact hmain

end Work.BW
