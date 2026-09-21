import Mathlib

/-!
# A fixed point theorem for weighted contractions

If `ω` is a "distance" on a complete metric space `α` which is equivalent to
the metric (`c * dist ≤ ω ≤ dist`), and `T` maps a closed nonempty set `B` into
itself, contracting `ω` with constant `κ < 1`, then `T` has a fixed point in
`B`.

This is the form of Banach's theorem used for the exponentially weighted
Volterra argument: `κ/c` need not be `< 1`, so the weighted contraction is
strictly stronger than an ordinary one.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Work.VolterraLong

theorem exists_fixedPoint_of_weighted_contraction {α : Type*} [MetricSpace α] [CompleteSpace α]
    (ω : α → α → ℝ) {c κ : ℝ} (hc : 0 < c) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hω_le : ∀ x y : α, ω x y ≤ dist x y)
    (hω_ge : ∀ x y : α, c * dist x y ≤ ω x y)
    {T : α → α} {B : Set α} (hB_closed : IsClosed B) (hB_ne : B.Nonempty)
    (hB : ∀ x ∈ B, T x ∈ B)
    (hcontr : ∀ x ∈ B, ∀ y ∈ B, ω (T x) (T y) ≤ κ * ω x y) :
    ∃ x ∈ B, T x = x := by
  obtain ⟨x₀, hx₀⟩ := hB_ne
  let u : ℕ → α := fun n => Nat.rec x₀ (fun _ y => T y) n
  have hu_zero : u 0 = x₀ := rfl
  have hu_succ : ∀ n, u (n + 1) = T (u n) := fun n => rfl
  have hu_mem : ∀ n, u n ∈ B := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => rw [hu_succ n]; exact hB _ ih
  have ha0 : 0 ≤ ω (u 0) (u 1) := by
    have := hω_ge (u 0) (u 1)
    nlinarith [dist_nonneg (x := u 0) (y := u 1)]
  have hgeo : ∀ n, ω (u n) (u (n + 1)) ≤ κ ^ n * ω (u 0) (u 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc ω (u (n + 1)) (u (n + 1 + 1))
          = ω (T (u n)) (T (u (n + 1))) := by rw [hu_succ n, hu_succ (n + 1)]
        _ ≤ κ * ω (u n) (u (n + 1)) := hcontr _ (hu_mem n) _ (hu_mem (n + 1))
        _ ≤ κ * (κ ^ n * ω (u 0) (u 1)) := mul_le_mul_of_nonneg_left ih hκ0
        _ = κ ^ (n + 1) * ω (u 0) (u 1) := by ring
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_geometric κ (ω (u 0) (u 1) / c) hκ1 (fun n => ?_)
    have h1 : c * dist (u n) (u (n + 1)) ≤ ω (u n) (u (n + 1)) := hω_ge _ _
    have h2 : ω (u n) (u (n + 1)) ≤ κ ^ n * ω (u 0) (u 1) := hgeo n
    have h3 : dist (u n) (u (n + 1)) ≤ ω (u n) (u (n + 1)) / c :=
      (le_div_iff₀ hc).mpr (by rw [mul_comm (dist _ _) c]; exact h1)
    calc dist (u n) (u (n + 1)) ≤ ω (u n) (u (n + 1)) / c := h3
      _ ≤ (κ ^ n * ω (u 0) (u 1)) / c := div_le_div_of_nonneg_right h2 hc.le
      _ = (ω (u 0) (u 1) / c) * κ ^ n := by ring
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxB : x ∈ B := hB_closed.mem_of_tendsto hx (Eventually.of_forall hu_mem)
  refine ⟨x, hxB, ?_⟩
  have hstep : ∀ n, dist (T (u n)) (T x) ≤ (κ / c) * dist (u n) x := by
    intro n
    have h1 : c * dist (T (u n)) (T x) ≤ ω (T (u n)) (T x) := hω_ge _ _
    have h2 : ω (T (u n)) (T x) ≤ κ * ω (u n) x := hcontr _ (hu_mem n) _ hxB
    have h3 : ω (u n) x ≤ dist (u n) x := hω_le _ _
    have h4 : c * dist (T (u n)) (T x) ≤ κ * dist (u n) x :=
      le_trans (le_trans h1 h2) (mul_le_mul_of_nonneg_left h3 hκ0)
    have h5 : dist (T (u n)) (T x) ≤ (κ * dist (u n) x) / c :=
      (le_div_iff₀ hc).mpr (by rw [mul_comm (dist _ _) c]; exact h4)
    calc dist (T (u n)) (T x) ≤ (κ * dist (u n) x) / c := h5
      _ = (κ / c) * dist (u n) x := by ring
  have hTlim : Tendsto (fun n => T (u n)) atTop (𝓝 (T x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Tendsto (fun n => dist (u n) x) atTop (𝓝 0) :=
      (tendsto_iff_dist_tendsto_zero).mp hx
    have hc0 : Tendsto (fun n => (κ / c) * dist (u n) x) atTop (𝓝 0) := by
      simpa using h0.const_mul (κ / c)
    exact squeeze_zero (fun n => dist_nonneg) (fun n => hstep n) hc0
  have hlim2 : Tendsto (fun n => u (n + 1)) atTop (𝓝 (T x)) := by
    simpa only [hu_succ] using hTlim
  have hlim3 : Tendsto (fun n => u (n + 1)) atTop (𝓝 x) :=
    hx.comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hlim2 hlim3

end Work.VolterraLong
