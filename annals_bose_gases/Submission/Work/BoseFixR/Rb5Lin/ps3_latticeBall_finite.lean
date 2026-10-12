import Mathlib.Analysis.Normed.Ring.Lemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.Rb5Lin

/-- The lattice ball `{m ∈ ℤ³ | ‖m‖ ≤ R}` is finite: it is contained in the product of the
integer intervals `[-⌈R⌉₊, ⌈R⌉₊]`, each of which is finite. -/
theorem ps3_latticeBall_finite (R : ℝ) :
    {m : Fin 3 → ℤ | ‖fun i : Fin 3 => (m i : ℝ)‖ ≤ R}.Finite := by
  by_cases hR : R < 0
  · -- for negative `R` the set is empty, since a norm is nonnegative
    refine Set.finite_empty.subset ?_
    intro m hm
    have hm' : ‖fun i : Fin 3 => (m i : ℝ)‖ ≤ R := hm
    have h0 : (0 : ℝ) ≤ ‖fun i : Fin 3 => (m i : ℝ)‖ := norm_nonneg _
    linarith
  · -- for `R ≥ 0` every coordinate is bounded by `⌈R⌉₊`, an integer bound
    refine (Set.Finite.pi' (fun _ =>
      (Set.finite_Icc (-(⌈R⌉₊ : ℤ)) (⌈R⌉₊ : ℤ)))).subset ?_
    intro m hm i
    have hm' : ‖fun j : Fin 3 => (m j : ℝ)‖ ≤ R := hm
    have h2 : R ≤ ((⌈R⌉₊ : ℤ) : ℝ) := by exact_mod_cast Nat.le_ceil R
    have h1 : |(m i : ℝ)| ≤ R := by
      have h := norm_le_pi_norm (fun j : Fin 3 => (m j : ℝ)) i
      have h' : ‖(m i : ℝ)‖ ≤ R := h.trans hm'
      simpa [Real.norm_eq_abs] using h'
    obtain ⟨hl, hu⟩ := abs_le.mp h1
    refine ⟨?_, ?_⟩
    · have h3 : -((⌈R⌉₊ : ℤ) : ℝ) ≤ (m i : ℝ) := by
        have : -(((⌈R⌉₊ : ℤ)) : ℝ) ≤ -R := by linarith
        linarith
      exact_mod_cast h3
    · exact_mod_cast (le_trans hu h2)

end Work.BoseFixR.Rb5Lin
