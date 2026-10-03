import Mathlib
import Submission.Work.Pert.norm_iterate_sub_le

namespace Work.Pert.Ksub2

/-- Iterates of a self-map of `B` stay in `B`. -/
private lemma iterate_mem {α : Type*} {f : α → α} {B : Set α} (hmaps : ∀ z ∈ B, f z ∈ B) :
    ∀ n (z : α), z ∈ B → f^[n] z ∈ B := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    exact hmaps _ (ih z hz)

/-- Two-seed version of `Work.Pert.norm_iterate_sub_le`: if `f₀` is `L`-Lipschitz on a set `B`
invariant under both `f` and `f₀`, and `f` is `ε`-close to `f₀` on `B`, then the `n`-th iterates
started at *different* seeds `z, z₀ ∈ B` satisfy

`‖f^[n] z - f₀^[n] z₀‖ ≤ ‖z - z₀‖ * L^n + ε * Σ_{i<n} L^i`.

This is the telescoping estimate used to propagate a defect along an orbit when the perturbed and
unperturbed coordinates are anchored at different points (the `Φm` vs. `Φ₀` comparison of
`Ksub_phi_close_v2`, where the seeds differ by the pinning constant). -/
theorem iterate_two_seed {f f₀ : ℂ → ℂ} {B : Set ℂ} {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hmaps : ∀ z ∈ B, f z ∈ B) (hmaps₀ : ∀ z ∈ B, f₀ z ∈ B)
    (hLip : ∀ z ∈ B, ∀ z' ∈ B, ‖f₀ z - f₀ z'‖ ≤ L * ‖z - z'‖)
    (hclose : ∀ z ∈ B, ‖f z - f₀ z‖ ≤ ε) :
    ∀ n : ℕ, ∀ z ∈ B, ∀ z₀ ∈ B,
      ‖f^[n] z - f₀^[n] z₀‖ ≤ ‖z - z₀‖ * L ^ n + ε * ∑ i ∈ Finset.range n, L ^ i := by
  intro n
  induction n with
  | zero =>
    intro z hz z₀ hz₀
    simp
  | succ n ih =>
    intro z hz z₀ hz₀
    have hfz : f^[n] z ∈ B := iterate_mem hmaps n z hz
    have hf0z : f₀^[n] z₀ ∈ B := iterate_mem hmaps₀ n z₀ hz₀
    have hmul : L * (∑ i ∈ Finset.range n, L^i) = ∑ i ∈ Finset.range n, L^(i+1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => (pow_succ' L i).symm)
    have hsum : (∑ i ∈ Finset.range (n+1), L^i) = 1 + L * (∑ i ∈ Finset.range n, L^i) := by
      rw [Finset.sum_range_succ', ← hmul, pow_zero, add_comm]
    calc ‖f^[n+1] z - f₀^[n+1] z₀‖
        = ‖f (f^[n] z) - f₀ (f₀^[n] z₀)‖ := by
            rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      _ ≤ ‖f (f^[n] z) - f₀ (f^[n] z)‖ + ‖f₀ (f^[n] z) - f₀ (f₀^[n] z₀)‖ := by
            rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
            exact dist_triangle _ _ _
      _ ≤ ε + L * (‖z - z₀‖ * L^n + ε * ∑ i ∈ Finset.range n, L^i) := by
            gcongr
            · exact hclose _ hfz
            · calc ‖f₀ (f^[n] z) - f₀ (f₀^[n] z₀)‖ ≤ L * ‖f^[n] z - f₀^[n] z₀‖ := hLip _ hfz _ hf0z
                _ ≤ L * (‖z - z₀‖ * L^n + ε * ∑ i ∈ Finset.range n, L^i) :=
                    mul_le_mul_of_nonneg_left (ih z hz z₀ hz₀) hL
      _ = ‖z - z₀‖ * L^(n+1) + ε * ∑ i ∈ Finset.range (n+1), L^i := by
            rw [hsum, pow_succ]
            ring

end Work.Pert.Ksub2
