import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.tailEntry_le
import Submission.Work.BoseRowQ2.tailIdentity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.tail_quad_le` — the quadratic form of the Schwartz tail matrix

The matrix `Tail N i j = Mc N i j − Σ_k Chat N k i * Chat N k j` is the difference between the
lattice `χ̂²`-kernel `Mc` and its truncation to the cube `[-N,N]³` (the lattice Parseval identity
`Work.BoseRowQ2.tailIdentity` identifies it with the dual-lattice tail
`Σ'_{m ∉ cube N} χ̂(vec(m−K_i))·χ̂(vec(m−K_j))`).  Because `χ̂` is Schwartz, every single entry of
`Tail` decays like `(2π(N+1) − L)^{-101}` on the momenta of interest
(`Work.BoseRowQ2.tailEntry_le`), and the quadratic form then obeys

    `Σ_{i,j} b_i b_j Tail N i j ≤ C · card(Lab N) / (2π(N+1) − L)^101 · Σ_i b_i²`,

the cardinality factor being the price of Cauchy–Schwarz (`∑|b_i| ≤ √card·‖b‖₂`).

## Structure

* `quad_form_le_of_entry` — the assembly: an entrywise bound `|Tail i j| ≤ C/R^101` (used only on
  the support of `b`) plus Cauchy–Schwarz for the double sum;
* `tail_quad_le` — the target, obtained by feeding in the tail identity and the entry bound.
-/

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Work.BoseRowQ2

open Work.BoseBoxFock

/-- **Cauchy–Schwarz assembly.**  If every entry of `Tail` is bounded by `C / R ^ 101` on the
support of `b` (`b i ≠ 0` and `b j ≠ 0`), then the quadratic form is bounded by
`C · card / R ^ 101 · Σ b i ^ 2`. -/
private lemma quad_form_le_of_entry {N : ℕ} {R C : ℝ} (hR : 0 < R) (hC0 : 0 ≤ C)
    (b : Lab N → ℝ)
    (hTail : ∀ i j : Lab N, b i ≠ 0 → b j ≠ 0 → |Tail N i j| ≤ C / R ^ 101) :
    (∑ i : Lab N, ∑ j : Lab N, b i * b j * Tail N i j)
      ≤ C * (Fintype.card (Lab N) : ℝ) / R ^ 101 * ∑ i : Lab N, b i ^ 2 := by
  have hcq : 0 ≤ C / R ^ 101 := div_nonneg hC0 (pow_nonneg hR.le 101)
  have hterm : ∀ i j : Lab N, b i * b j * Tail N i j ≤ |b i| * |b j| * (C / R ^ 101) := by
    intro i j
    by_cases hi : b i = 0
    · simp only [hi, zero_mul, abs_zero]
      positivity
    by_cases hj : b j = 0
    · simp only [hj, mul_zero, zero_mul, abs_zero]
      positivity
    · calc b i * b j * Tail N i j ≤ |b i * b j * Tail N i j| := le_abs_self _
        _ = |b i| * |b j| * |Tail N i j| := by rw [abs_mul, abs_mul]
        _ ≤ |b i| * |b j| * (C / R ^ 101) :=
            mul_le_mul_of_nonneg_left (hTail i j hi hj) (by positivity)
  have hstep1 : (∑ i : Lab N, ∑ j : Lab N, b i * b j * Tail N i j)
      ≤ ∑ i : Lab N, ∑ j : Lab N, |b i| * |b j| * (C / R ^ 101) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hstep2 : (∑ i : Lab N, ∑ j : Lab N, |b i| * |b j| * (C / R ^ 101))
      = (C / R ^ 101) * ((∑ i : Lab N, |b i|) * (∑ j : Lab N, |b j|)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hstep3 : (C / R ^ 101) * ((∑ i : Lab N, |b i|) * (∑ j : Lab N, |b j|))
      = (C / R ^ 101) * (∑ i : Lab N, |b i|) ^ 2 := by
    rw [← sq]
  have hcs : (∑ i : Lab N, |b i|) ^ 2
      ≤ (Fintype.card (Lab N) : ℝ) * ∑ i : Lab N, b i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Lab N)))
      (f := fun i => |b i|)
    simpa [Finset.card_univ, sq_abs] using h
  have hstep4 : (C / R ^ 101) * ((Fintype.card (Lab N) : ℝ) * ∑ i : Lab N, b i ^ 2)
      = C * (Fintype.card (Lab N) : ℝ) / R ^ 101 * ∑ i : Lab N, b i ^ 2 := by
    ring
  calc (∑ i : Lab N, ∑ j : Lab N, b i * b j * Tail N i j)
      ≤ ∑ i : Lab N, ∑ j : Lab N, |b i| * |b j| * (C / R ^ 101) := hstep1
    _ = (C / R ^ 101) * ((∑ i : Lab N, |b i|) * (∑ j : Lab N, |b j|)) := hstep2
    _ = (C / R ^ 101) * (∑ i : Lab N, |b i|) ^ 2 := hstep3
    _ ≤ (C / R ^ 101) * ((Fintype.card (Lab N) : ℝ) * ∑ i : Lab N, b i ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hcq
    _ = C * (Fintype.card (Lab N) : ℝ) / R ^ 101 * ∑ i : Lab N, b i ^ 2 := hstep4

theorem tail_quad_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (N : ℕ) (L : ℝ), 0 ≤ L →
      1 ≤ 2 * Real.pi * ((N : ℝ) + 1) - L →
      ∀ (b : Work.BoseBoxFock.Lab N → ℝ),
        (∀ i, b i ≠ 0 → ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N i)‖ ≤ L) →
      (∑ i : Work.BoseBoxFock.Lab N, ∑ j : Work.BoseBoxFock.Lab N,
          b i * b j * Work.BoseRowQ2.Tail N i j)
        ≤ D * (Fintype.card (Work.BoseBoxFock.Lab N) : ℝ)
            / (2 * Real.pi * ((N : ℝ) + 1) - L) ^ 101 * ∑ i : Work.BoseBoxFock.Lab N, b i ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := tailEntry_le
  refine ⟨C, hC0, ?_⟩
  intro N L hL hR1 b hb
  have hRpos : 0 < 2 * Real.pi * ((N : ℝ) + 1) - L := lt_of_lt_of_le zero_lt_one hR1
  exact quad_form_le_of_entry (N := N) (R := 2 * Real.pi * ((N : ℝ) + 1) - L) (C := C)
    hRpos hC0 b fun i j hi hj => by
      rw [tailIdentity N i j]
      exact hC N L hL hR1 (labVec N i) (labVec N j) (hb i hi) (hb j hj)

end Work.BoseRowQ2
