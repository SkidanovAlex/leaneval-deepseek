import Mathlib

namespace Work.RPB1a

/-- The open "shell" `{w : ℂ | a < ‖w‖ ∧ ‖w‖ < b}` with `0 < a < b` is preconnected.

Proof sketch: it is the image of the convex (hence preconnected) open strip
`{ζ : ℂ | Real.log a < ζ.re ∧ ζ.re < Real.log b}` under the continuous map `Complex.exp`.
Membership: `‖Complex.exp ζ‖ = Real.exp ζ.re`, so `a < ‖exp ζ‖ ↔ log a < ζ.re` and
`‖exp ζ‖ < b ↔ ζ.re < log b` (using `Real.exp_log`, `Real.log_lt_log`, `Real.log_neg_iff`);
surjectivity on the shell: `ζ := Complex.log w` works, since `Complex.exp_log` and
`Complex.log_re`. -/
theorem isPreconnected_annulus_shell {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsPreconnected {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} := by
  have hb : 0 < b := lt_trans ha hab
  -- The open strip `log a < re < log b`; it is the preimage of the convex interval
  -- `(log a, log b)` under the `ℝ`-linear projection `Complex.reLm`, hence convex.
  set S : Set ℂ := {ζ : ℂ | Real.log a < ζ.re ∧ ζ.re < Real.log b} with hS
  have hconv : Convex ℝ S := by
    rw [hS]
    exact (convex_Ioo _ _).linear_preimage Complex.reLm
  -- `Complex.exp` maps the strip exactly onto the shell.
  have himage : Complex.exp '' S = {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} := by
    ext w
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      obtain ⟨h1, h2⟩ : Real.log a < ζ.re ∧ ζ.re < Real.log b := hζ
      rw [Set.mem_ofPred_eq, Complex.norm_exp]
      exact ⟨(Real.log_lt_iff_lt_exp ha).mp h1, (Real.lt_log_iff_exp_lt hb).mp h2⟩
    · intro hw
      obtain ⟨h1, h2⟩ := hw
      have hwpos : 0 < ‖w‖ := lt_trans ha h1
      have hwne : w ≠ 0 := norm_pos_iff.mp hwpos
      refine ⟨Complex.log w, ?_, Complex.exp_log hwne⟩
      rw [hS, Set.mem_ofPred_eq, Complex.log_re]
      exact ⟨Real.log_lt_log ha h1, Real.log_lt_log hwpos h2⟩
  -- A continuous image of a preconnected set is preconnected.
  have hpc : IsPreconnected (Complex.exp '' S) :=
    IsPreconnected.image hconv.isPreconnected Complex.exp Complex.continuous_exp.continuousOn
  rwa [himage] at hpc

end Work.RPB1a
