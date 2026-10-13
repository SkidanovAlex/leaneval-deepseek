/-
  WilG4c — the `(T,r)`-jet norm versus operator norms.

  `WilkiesDesign.CG.tnorm r f x = Σ_{k ≤ r} ‖D^k f x‖ / k!`.  This file records the two
  conversions used by BNZ §§4, 5.4, 5.5: a single summand dominates the corresponding
  derivative (`NormJet`), and the factorial-versus-power comparison `m! ≤ r^m` that makes the
  diagonal rescaling of BNZ Lemma 4.1 (`T-less-Tr`) give norm `≤ 1` rather than `≤ m!`.
-/
import Submission.Work.WilG4c.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- One summand of the frozen `tnorm` dominates the `m`-th derivative: if `m ≤ r` then
`‖D^m f(x)‖ ≤ m! · tnorm r f x`.  (All summands of `tnorm` are nonnegative, so the `k = m`
summand alone proves it.) -/
theorem NormJet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r m : ℕ) (hm : m ≤ r)
    (f : E → ℝ) (x : E) : ‖iteratedFDeriv ℝ m f x‖ ≤ (m.factorial : ℝ) * tnorm r f x := by
  have hm' : m ∈ Finset.range (r + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  have hle : ‖iteratedFDeriv ℝ m f x‖ / (m.factorial : ℝ) ≤ tnorm r f x := by
    rw [tnorm]
    refine Finset.single_le_sum (s := Finset.range (r + 1))
      (f := fun k : ℕ => ‖iteratedFDeriv ℝ k f x‖ / (k.factorial : ℝ)) ?_ hm'
    intro k _
    exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  calc ‖iteratedFDeriv ℝ m f x‖
      = (m.factorial : ℝ) * (‖iteratedFDeriv ℝ m f x‖ / (m.factorial : ℝ)) := by
        field_simp
    _ ≤ (m.factorial : ℝ) * tnorm r f x := mul_le_mul_of_nonneg_left hle hfac.le

/-- `m! ≤ r^m` whenever `m ≤ r` and `1 ≤ r`.  This is the arithmetic that makes the diagonal
rescaling of BNZ Lemma 4.1 land exactly on `‖·‖ ≤ 1`. -/
theorem factorial_le_pow (m r : ℕ) (hm : m ≤ r) (hr : 1 ≤ r) : m.factorial ≤ r ^ m :=
  le_trans (Nat.factorial_le_pow m) (Nat.pow_le_pow_left hm m)

end Work.WilkG4c
