import Mathlib

namespace Work.Pert.Ksub2

/-- **Shadowing of a pseudo-orbit of `f₀` by a true orbit of `f`.**

`y` is an orbit of `f₀` (on the first `n` steps) lying in `Z`, `a` starts within `η` of `y 0`,
`f` is `ε`-close to `f₀` on the `r`-neighbourhood `V` of `Z`, and `f₀` is `L`-Lipschitz on `V`.
Then the true orbit of `a` under `f` shadows `y` up to the accumulated error
`ε · Σ_{i<n} L^i + L^n · η`.  The hypothesis `hr` records exactly that all the intermediate
error bounds stay below the radius `r`, so that the orbit never leaves `V` (this is the
non-invariant-region form of the estimate). -/
theorem shadow_orbit_le {f f₀ : ℂ → ℂ} {Z V : Set ℂ} {y : ℕ → ℂ} {a : ℂ}
    {L ε η r : ℝ} (n : ℕ) (hL : 0 ≤ L)
    (hVr : ∀ z : ℂ, (∃ w ∈ Z, ‖z - w‖ ≤ r) → z ∈ V)
    (hLip : ∀ z ∈ V, ∀ z' ∈ V, ‖f₀ z - f₀ z'‖ ≤ L * ‖z - z'‖)
    (hclose : ∀ z ∈ V, ‖f z - f₀ z‖ ≤ ε)
    (hyZ : ∀ j, j ≤ n → y j ∈ Z) (hyrec : ∀ j, j < n → f₀ (y j) = y (j + 1))
    (ha : ‖a - y 0‖ ≤ η)
    (hr : ∀ j, j ≤ n → ε * ∑ i ∈ Finset.range j, L ^ i + L ^ j * η ≤ r) :
    ‖f^[n] a - y n‖ ≤ ε * ∑ i ∈ Finset.range n, L ^ i + L ^ n * η := by
  -- `0 ≤ r` is forced: `0 ≤ η` (from `ha`) and `η ≤ r` (from `hr` at `j = 0`).
  have hr_nonneg : 0 ≤ r := by
    have hη : 0 ≤ η := le_trans (norm_nonneg _) ha
    have h0 : η ≤ r := by simpa using hr 0 (Nat.zero_le n)
    linarith
  -- the geometric identity `Σ_{i<j+1} L^i = 1 + L · Σ_{i<j} L^i`
  have hsum : ∀ j : ℕ,
      (∑ i ∈ Finset.range (j+1), L^i) = 1 + L * (∑ i ∈ Finset.range j, L^i) := by
    intro j
    have hmul : L * (∑ i ∈ Finset.range j, L^i) = ∑ i ∈ Finset.range j, L^(i+1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => (pow_succ' L i).symm)
    rw [Finset.sum_range_succ', ← hmul, pow_zero, add_comm]
  -- the shadowing estimate, by induction on the step count
  have key : ∀ j, j ≤ n → ‖f^[j] a - y j‖ ≤ ε * ∑ i ∈ Finset.range j, L^i + L^j * η := by
    intro j
    induction j with
    | zero => intro _; simpa using ha
    | succ k ih =>
      intro hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hk' : k ≤ n := le_of_lt hkn
      have ihk := ih hk'
      -- both the current iterate and `y k` lie in `V`, where the estimates are available
      have hzV : f^[k] a ∈ V := hVr _ ⟨y k, hyZ k hk', le_trans ihk (hr k hk')⟩
      have hykV : y k ∈ V := hVr _ ⟨y k, hyZ k hk', by simpa using hr_nonneg⟩
      have hstep : ‖f (f^[k] a) - f₀ (y k)‖
          ≤ ε + L * (ε * ∑ i ∈ Finset.range k, L^i + L^k * η) := by
        calc ‖f (f^[k] a) - f₀ (y k)‖
            ≤ ‖f (f^[k] a) - f₀ (f^[k] a)‖ + ‖f₀ (f^[k] a) - f₀ (y k)‖ := by
                rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
                exact dist_triangle _ _ _
          _ ≤ ε + L * ‖f^[k] a - y k‖ := by
                linarith [hclose (f^[k] a) hzV, hLip (f^[k] a) hzV (y k) hykV]
          _ ≤ ε + L * (ε * ∑ i ∈ Finset.range k, L^i + L^k * η) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left ihk hL)
      calc ‖f^[k+1] a - y (k+1)‖
          = ‖f (f^[k] a) - f₀ (y k)‖ := by
              rw [Function.iterate_succ_apply', ← hyrec k hkn]
        _ ≤ ε + L * (ε * ∑ i ∈ Finset.range k, L^i + L^k * η) := hstep
        _ = ε * ∑ i ∈ Finset.range (k+1), L^i + L^(k+1) * η := by
              rw [hsum k, pow_succ]
              ring
  exact key n le_rfl

end Work.Pert.Ksub2
