import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPCore.Flow.isCompact_fundamentalDomain
import Submission.Work.RPCore.Flow.periodic_Tk_int

/-!
# A continuous function that is `2π`-periodic in `q₂` and constant outside the slab is bounded
on every time-slab `{|t| ≤ B}`

Let `f : ℝ × PS → V` be continuous, invariant under the deck transformation `Tk 1` (the shift of
the angle `q₂` by `2π`), and equal to a fixed value `c` outside the slab
`{|q₁| + |p₁| + |p₂| > R}`.  Then `‖f‖` is bounded on `{|t| ≤ B}` for every `B`.

Proof.  Every point `z = (t, x)` can be shifted in the angle direction to the "fundamental domain"
`D = {|t| ≤ B, |q₁|+|p₁|+|p₂| ≤ R, 0 ≤ q₂ ≤ 2π}` without changing the value of `f`:  take
`k = ⌊q₂/(2π)⌋`, so that `z' = (t, Tk (-k) x)` has `q₂' = q₂ - 2πk ∈ [0, 2π]`, and use
`periodic_Tk_int`.  `D` is compact (`isCompact_fundamentalDomain`), so `‖f‖` is bounded on it by
continuity, giving `M₀`.  If `z` is inside the slab we are done with `M₀`; otherwise `f z = c` and
`‖f z‖ = ‖c‖`.  Hence `M = max M₀ ‖c‖` works.
-/

set_option autoImplicit false

namespace Work.RPCore.Flow

open Work.RPV

theorem bounded_of_periodic_of_eq_on_slab {V : Type*} [NormedAddCommGroup V]
    (f : ℝ × Work.RPV.PS → V) (hf : Continuous f)
    (hper : ∀ z, f (z.1, Work.RPV.Tk 1 z.2) = f z) {R : ℝ} {c : V}
    (hsupp : ∀ z, R < |z.2.1.1| + |z.2.2.1| + |z.2.2.2| → f z = c) (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ × Work.RPV.PS, |z.1| ≤ B → ‖f z‖ ≤ M := by
  -- `‖f‖` is bounded on the compact fundamental domain `D`.
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_fundamentalDomain B R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M₀ ‖c‖, le_trans (norm_nonneg c) (le_max_right _ _), ?_⟩
  intro z hz
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- shift the angle coordinate into `[0, 2π]`
  set k : ℤ := ⌊z.2.1.2 / (2 * Real.pi)⌋ with hk
  have hkle : (k : ℝ) * (2 * Real.pi) ≤ z.2.1.2 := by
    have h1 : (k : ℝ) ≤ z.2.1.2 / (2 * Real.pi) := by rw [hk]; exact Int.floor_le _
    have := mul_le_mul_of_nonneg_right h1 (le_of_lt hpi)
    rwa [div_mul_cancel₀ _ (ne_of_gt hpi)] at this
  have hklt : z.2.1.2 < ((k : ℝ) + 1) * (2 * Real.pi) := by
    have h1 : z.2.1.2 / (2 * Real.pi) < (k : ℝ) + 1 := by
      rw [hk]; exact Int.lt_floor_add_one _
    have := mul_lt_mul_of_pos_right h1 hpi
    rwa [div_mul_cancel₀ _ (ne_of_gt hpi)] at this
  have hq : (Tk (-k) z.2).1.2 = z.2.1.2 - 2 * Real.pi * (k : ℝ) := by
    show z.2.1.2 + 2 * Real.pi * ↑(-k) = z.2.1.2 - 2 * Real.pi * (k : ℝ)
    push_cast
    ring
  have hq0 : 0 ≤ (Tk (-k) z.2).1.2 := by
    rw [hq]; nlinarith [hkle]
  have hq1 : (Tk (-k) z.2).1.2 ≤ 2 * Real.pi := by
    rw [hq]; nlinarith [hklt]
  have hzf : f (z.1, Tk (-k) z.2) = f z := periodic_Tk_int f hper (-k) z.1 z.2
  rcases le_or_gt (|z.2.1.1| + |z.2.2.1| + |z.2.2.2|) R with hsle | hslt
  · -- the shifted point lies in the fundamental domain
    have hmem : (z.1, Tk (-k) z.2) ∈ {w : ℝ × Work.RPV.PS |
        |w.1| ≤ B ∧ |w.2.1.1| + |w.2.2.1| + |w.2.2.2| ≤ R ∧ 0 ≤ w.2.1.2 ∧
          w.2.1.2 ≤ 2 * Real.pi} := by
      refine ⟨hz, ?_, hq0, hq1⟩
      show |z.2.1.1| + |z.2.2.1| + |z.2.2.2| ≤ R
      exact hsle
    have h1 : ‖f z‖ ≤ M₀ := by
      rw [← hzf]
      exact hM₀ _ hmem
    exact le_trans h1 (le_max_left _ _)
  · -- outside the slab, `f` is the constant `c`
    have h1 : ‖f z‖ = ‖c‖ := by rw [hsupp z hslt]
    rw [h1]
    exact le_max_right _ _

end Work.RPCore.Flow
