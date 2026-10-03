import Mathlib
import Submission.Work.F0Facts.Basic
import Submission.Work.F0Facts.RealOrbit
import Submission.Work.F0Facts.finv_iterate_tendsto

/-!
# The explicit Step 0 inverse orbit

`z₀ = 0`, `z₁ = -1`, `z_{j+2} = finv^j(ω)`: an inverse orbit of `0` for `f₀(z) = z + z²` which
converges to `0` and avoids the critical point `-1/2`.
-/

namespace Work.F0Facts

open MandelDim Filter Set Metric Topology
open scoped Topology

noncomputable section

/-- The explicit inverse orbit of Step 0. -/
def orbitZ : ℕ → ℂ
  | 0 => 0
  | 1 => -1
  | n + 2 => finv^[n] w3

@[simp] lemma orbitZ_zero : orbitZ 0 = 0 := rfl
@[simp] lemma orbitZ_one : orbitZ 1 = -1 := rfl
@[simp] lemma orbitZ_add_two (n : ℕ) : orbitZ (n + 2) = finv^[n] w3 := rfl

lemma finv_iterate_ne_zero (n : ℕ) : finv^[n] w3 ≠ 0 := by
  induction n with
  | zero => simpa using w3_ne_zero
  | succ n ih => rwa [Function.iterate_succ_apply', finv_ne_zero_iff]

lemma f0_comp_finv_iterate (n : ℕ) (y : ℂ) : f0^[n] (finv^[n] y) = y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    have h1 : finv^[n + 1] y = finv^[n] (finv y) := Function.iterate_succ_apply finv n y
    have h2 : f0^[n + 1] (finv^[n] (finv y)) = f0 (f0^[n] (finv^[n] (finv y))) :=
      Function.iterate_succ_apply' f0 n (finv^[n] (finv y))
    rw [h1, h2, ih (finv y)]
    exact f0_finv y

/-- The points of the orbit are not the critical point `-1/2`. -/
lemma orbitZ_ne_neg_half : ∀ j : ℕ, orbitZ j ≠ -1/2 := by
  intro j
  match j with
  | 0 => norm_num [orbitZ_zero]
  | 1 => norm_num [orbitZ_one]
  | n + 2 =>
    intro h
    have hcrit : (f0^[n] ((-1/2 : ℝ) : ℂ)).im = 0 := orbit_im_eq_zero (-1/2) n
    have h1 : f0^[n] (finv^[n] w3) = w3 := f0_comp_finv_iterate n w3
    rw [orbitZ_add_two] at h
    rw [h] at h1
    have h2 : ((-1/2 : ℝ) : ℂ) = (-1/2 : ℂ) := by norm_num
    rw [h2] at hcrit
    have : (f0^[n] (-1/2 : ℂ)).im = 0 := hcrit
    rw [h1] at this
    rw [w3_im] at this
    have := sqrt_three_pos
    linarith

lemma orbitZ_ne_zero : ∀ j : ℕ, 1 ≤ j → orbitZ j ≠ 0 := by
  intro j hj
  match j with
  | 0 => omega
  | 1 => norm_num [orbitZ_one]
  | n + 2 => exact finv_iterate_ne_zero n

lemma orbitZ_tendsto : Tendsto orbitZ atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ => finv^[n - 2] w3) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h := finv_iterate_tendsto
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N + 2, fun n hn => hN (n - 2) (by omega)⟩
  refine hshift.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp

lemma f0_orbitZ_succ (j : ℕ) : f0 (orbitZ (j + 1)) = orbitZ j := by
  cases j with
  | zero => norm_num [orbitZ_zero, orbitZ_one, f0_eq]
  | succ j =>
    cases j with
    | zero => simpa [orbitZ_one, orbitZ_add_two] using f0_w3
    | succ n =>
      show f0 (orbitZ (n + 3)) = orbitZ (n + 2)
      rw [show n + 3 = (n + 1) + 2 by omega, orbitZ_add_two, orbitZ_add_two]
      rw [show finv^[n + 1] w3 = finv (finv^[n] w3) from Function.iterate_succ_apply' finv n w3]
      exact f0_finv _

end
end Work.F0Facts
