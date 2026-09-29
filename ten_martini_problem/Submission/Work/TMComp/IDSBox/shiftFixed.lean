/-
The **corrected** form of `Work.TMComp.IDSBox.shift`.

The requested statement is false: its third conjunct asks for
`∑ k, shiftVec φ i n k * conj (shiftVec φ j' n k) = 0` under the hypothesis `R ≤ |i - j'|`,
but `hsupp` only puts the support of `φ` inside `{m : |m| ≤ R - 1}`, a window of width
`2R - 1`.  Two such windows overlap as soon as `2R - 1 > |i - j'|`, which happens for
`R ≤ |i - j'| ≤ 2R - 2` whenever `R ≥ 2`; e.g. `R = 2`, `i = 0`, `j' = 2`,
`φ = (δ_{-1} + δ_1)/√2` gives sum `1/2 ≠ 0`.

Here the third conjunct carries the correct hypothesis `2 * R - 1 ≤ |i - j'|`; the first
two conjuncts are exactly as requested and are proved from

* `jbox_apply` (the box operator identity),
* `pot_shift_close` (the phase-shift estimate for the potential),
* `shiftVec_norm` (the shift is a unit vector),
* `shiftAux.shift_res_of`, `shiftAux.sum_window_res_le`, `shiftAux.shiftVec_orth'`.
-/
import Submission.Work.TMComp.IDSBox.jbox_apply
import Submission.Work.TMComp.IDSBox.pot_shift_close
import Submission.Work.TMComp.IDSBox.shiftVec_norm
import Submission.Work.TMComp.IDSBox.shiftAux

noncomputable section

open scoped BigOperators

namespace Work.TMComp.IDSBox

/-- The corrected `shift` lemma: identical to `Work.TMComp.IDSBox.shift` except that the
orthogonality hypothesis is the correct one, `2 * R - 1 ≤ |i - j'|`. -/
theorem shift_fixed (α lam E : ℝ) {R : ℕ} (φ : ℤ → ℂ)
    (hsupp : ∀ m : ℤ, R ≤ m.natAbs → φ m = 0)
    (hφ : (∑' m : ℤ, ‖φ m‖ ^ 2) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hres : (∑' m : ℤ, ‖Work.TMContract.amoAct α lam 0 φ m - (E : ℂ) * φ m‖ ^ 2) ≤ ε ^ 2)
    (θ : ℝ) (n : ℕ) (j : ℤ) (hj : (R : ℤ) ≤ j + 1) (hj2 : j + (R : ℤ) + 1 ≤ (n : ℤ))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hphase : Work.TMContract.fracDist (θ + (j : ℝ) * α) < δ) :
    (∑ k : Fin n, ‖(Matrix.mulVec (Work.TMComp.Jbox α lam θ n) (Work.TMComp.shiftVec φ j n)) k
        - (E : ℂ) * Work.TMComp.shiftVec φ j n k‖ ^ 2)
        ≤ (ε + 4 * Real.pi * |lam| * δ) ^ 2 ∧
    (∑ k : Fin n, ‖Work.TMComp.shiftVec φ j n k‖ ^ 2) = 1 ∧
    (∀ i j' : ℤ, i ≠ j' → 2 * (R : ℤ) - 1 ≤ |i - j'| →
      (∑ k : Fin n, Work.TMComp.shiftVec φ i n k
        * (starRingEnd ℂ) (Work.TMComp.shiftVec φ j' n k)) = 0) := by
  have hnorm : (∑ k : Fin n, ‖Work.TMComp.shiftVec φ j n k‖ ^ 2) = 1 :=
    shiftVec_norm φ hsupp hφ j n hj hj2
  refine ⟨?_, hnorm, ?_⟩
  · refine shift_res_of (R := R) φ α lam θ E δ ε j n hδ hε ?_ ?_ ?_ hnorm
    · intro k
      exact jbox_apply α lam θ E φ hsupp j n hj hj2 k
    · intro k
      exact pot_shift_close α lam θ δ hδ j (k : ℕ) hphase
    · exact sum_window_res_le hsupp α lam E ε j n hres
  · intro i j' _ hij
    exact shiftVec_orth' φ hsupp i j' n hij

end Work.TMComp.IDSBox
