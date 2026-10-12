import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.corpusBox_hatChi_sq_tail_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.corpusBox_hatChi_sq_tsum_le` — the `χ̂²`-tail as an infinite sum

The sibling `Work.BoseK15.corpusBox_hatChi_sq_tail_sum` bounds
`∑_{n ∈ S} χ̂(vec n)² ≤ C/R^101` for every *finite* set `S` of dual-lattice indices whose
momenta `vec n = 2πn` all have norm at least `R ≥ 1`.  Downstream (the low-momentum sums of
the `BoseBoxFock` chapter) one sums over the *whole* set of such indices, i.e. over the
subtype `{n : Fin 3 → ℤ // R ≤ ‖vec n‖}`; this module upgrades the finite bound to that
`tsum`.

The passage is the standard nonnegativity one.  The summand `χ̂(vec n)²` is a square, so
every finite partial sum is at most `C/R^101`; in `ℝ≥0∞` this reads
`∑' n, ofReal (χ̂(vec n)²) ≤ ofReal (C/R^101) < ⊤`, which both bounds the sum and exhibits
its finiteness; applying `ENNReal.toReal` (monotone, and `ofReal`-inverse on nonnegative
reals) transfers the bound back to the real `tsum`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

/-- **The `χ̂²`-tail of the corpus bump, as an infinite lattice sum.**  There is a constant
`C ≥ 0` with

    `∑'_{n : ℤ³, ‖2πn‖ ≥ R} χ̂(2πn)² ≤ C/R^101`      for every `R ≥ 1`

(so the tail decays faster than any fixed polynomial, here rate `101`). -/
theorem corpusBox_hatChi_sq_tsum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 1 ≤ R →
      (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
        (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n.val)) ^ 2) ≤ C / R ^ 101 := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseK15.corpusBox_hatChi_sq_tail_sum
  refine ⟨C, hC0, ?_⟩
  intro R hR
  set f : (Fin 3 → ℤ) → ℝ := fun n => (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2
  have hnn : ∀ n, 0 ≤ f n := fun n => sq_nonneg _
  have hB : 0 ≤ C / R ^ 101 := div_nonneg hC0 (by positivity)
  -- the finite partial sums over the subtype, transported to finite sets of lattice indices
  have hfin : ∀ s : Finset {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
      ∑ x ∈ s, f x.val ≤ C / R ^ 101 := by
    intro s
    have hS : ∀ n ∈ s.map (Function.Embedding.subtype (fun n : Fin 3 → ℤ => R ≤ ‖Work.BoseB4.vec n‖)),
        R ≤ ‖Work.BoseB4.vec n‖ := by
      intro n hn
      rw [Finset.mem_map] at hn
      obtain ⟨x, _hx, rfl⟩ := hn
      exact x.2
    have h1 := hC R (s.map (Function.Embedding.subtype (fun n : Fin 3 → ℤ => R ≤ ‖Work.BoseB4.vec n‖))) hR hS
    rw [Finset.sum_map] at h1
    exact h1
  -- the `ℝ≥0∞` version: `tsum` is the supremum of the finite partial sums
  have hENN : (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, ENNReal.ofReal (f n.val))
      ≤ ENNReal.ofReal (C / R ^ 101) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn n.val)]
    exact ENNReal.ofReal_le_ofReal (hfin s)
  have hsummand : ∀ n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
      ENNReal.ofReal (f n.val) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hne : (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, ENNReal.ofReal (f n.val)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN
  -- back to `ℝ`: `toReal` of the `ℝ≥0∞`-sum is the real `tsum`, and it is monotone
  have htoReal : (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
        ENNReal.ofReal (f n.val)).toReal
      = ∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, f n.val := by
    rw [ENNReal.tsum_toReal_eq hsummand]
    exact tsum_congr fun n => ENNReal.toReal_ofReal (hnn n.val)
  calc (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
        (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n.val)) ^ 2)
      = (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, f n.val) := rfl
    _ = (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, ENNReal.ofReal (f n.val)).toReal :=
        htoReal.symm
    _ ≤ (ENNReal.ofReal (C / R ^ 101)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
    _ = C / R ^ 101 := ENNReal.toReal_ofReal hB

end Work.BoseRowQ2
