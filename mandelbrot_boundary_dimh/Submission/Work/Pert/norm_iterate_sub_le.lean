import Mathlib

namespace Work.Pert

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

/-- Two maps that are `ε`-close on a set `B` invariant under both, on which `f₀` is `L`-Lipschitz,
have iterates that are at most `ε · Σ_{i<n} L^i` apart on `B`.  (The engine of the propagation
step of `φ_close` along the Abel equation: `φ w = f^n (φ (w-n))` versus `d.φ w = f₀^n (d.φ (w-n))`.) -/
theorem norm_iterate_sub_le {f f₀ : ℂ → ℂ} {B : Set ℂ} {L ε : ℝ} (hL : 0 ≤ L)
    (hmaps : ∀ z ∈ B, f z ∈ B) (hmaps₀ : ∀ z ∈ B, f₀ z ∈ B)
    (hLip : ∀ z ∈ B, ∀ z' ∈ B, ‖f₀ z - f₀ z'‖ ≤ L * ‖z - z'‖)
    (hclose : ∀ z ∈ B, ‖f z - f₀ z‖ ≤ ε) :
    ∀ n : ℕ, ∀ z ∈ B, ‖f^[n] z - f₀^[n] z‖ ≤ ε * ∑ i ∈ Finset.range n, L ^ i := by
  intro n
  induction n with
  | zero => intro z hz; simp
  | succ n ih =>
    intro z hz
    have hfz : f^[n] z ∈ B := iterate_mem hmaps n z hz
    have hf0z : f₀^[n] z ∈ B := iterate_mem hmaps₀ n z hz
    have hmul : L * (∑ i ∈ Finset.range n, L^i) = ∑ i ∈ Finset.range n, L^(i+1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => (pow_succ' L i).symm)
    have hsum : (∑ i ∈ Finset.range (n+1), L^i) = 1 + L * (∑ i ∈ Finset.range n, L^i) := by
      rw [Finset.sum_range_succ', ← hmul, pow_zero, add_comm]
    calc ‖f^[n+1] z - f₀^[n+1] z‖
        = ‖f (f^[n] z) - f₀ (f₀^[n] z)‖ := by
            rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      _ ≤ ‖f (f^[n] z) - f₀ (f^[n] z)‖ + ‖f₀ (f^[n] z) - f₀ (f₀^[n] z)‖ := by
            rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
            exact dist_triangle _ _ _
      _ ≤ ε + L * (ε * ∑ i ∈ Finset.range n, L^i) := by
            gcongr
            · exact hclose _ hfz
            · calc ‖f₀ (f^[n] z) - f₀ (f₀^[n] z)‖ ≤ L * ‖f^[n] z - f₀^[n] z‖ := hLip _ hfz _ hf0z
                _ ≤ L * (ε * ∑ i ∈ Finset.range n, L^i) :=
                    mul_le_mul_of_nonneg_left (ih z hz) hL
      _ = ε * ∑ i ∈ Finset.range (n+1), L^i := by
            rw [hsum]; ring

end Work.Pert
