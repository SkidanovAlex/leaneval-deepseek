import Mathlib

namespace NK.Reconstruct

open scoped Topology

/-- The reduction `ℤ_[p] → ZMod (p^n)` depends only on the residue class modulo `p^n`:
if `x - y ∈ (p^n)`, then `x` and `y` have the same image. -/
theorem toZModPow_eq_of_sub_mem_span {p : ℕ} [Fact p.Prime] (n : ℕ) {x y : ℤ_[p]}
    (h : x - y ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p])) :
    PadicInt.toZModPow (p := p) n x = PadicInt.toZModPow (p := p) n y := by
  show ((x.appr n : ℕ) : ZMod (p ^ n)) = ((y.appr n : ℕ) : ZMod (p ^ n))
  refine PadicInt.zmod_congr_of_sub_mem_span n x (x.appr n) (y.appr n)
    (PadicInt.appr_spec n x) ?_
  have hy := PadicInt.appr_spec n y
  have hsplit : x - (y.appr n : ℤ_[p]) = (x - y) + (y - (y.appr n : ℤ_[p])) := by ring
  rw [hsplit]
  exact Ideal.add_mem _ h hy

/-- The reduction `ℤ_[p] → ZMod (p^n)` is locally constant. -/
theorem isLocallyConstant_toZModPow (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) n) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨Metric.closedBall x ((p : ℝ) ^ (-(n : ℤ))), ?_, Metric.mem_closedBall_self (by positivity), ?_⟩
  · refine IsUltrametricDist.isOpen_closedBall x ?_
    exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  · intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    refine (toZModPow_eq_of_sub_mem_span (p := p) n ?_).symm
    have hmem : y - x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) n).mp hy
    simpa using neg_mem hmem

theorem continuous_toZModPow (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := p) n) :=
  (isLocallyConstant_toZModPow p n).continuous

end NK.Reconstruct
