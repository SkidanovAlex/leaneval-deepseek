import Mathlib

namespace Work.Topology

/-- Two naturals whose real casts differ by less than one are equal. -/
lemma nat_eq_of_abs_sub_lt_one {a b : ℕ} (h : |(a : ℝ) - (b : ℝ)| < 1) : a = b := by
  have h1 : (a : ℝ) < (b : ℝ) + 1 := by
    have := (abs_lt.mp h).2; linarith
  have h2 : (b : ℝ) < (a : ℝ) + 1 := by
    have := (abs_lt.mp h).1; linarith
  have hle1 : a ≤ b := by
    have : (a : ℝ) < ((b + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp this)
  have hle2 : b ≤ a := by
    have : (b : ℝ) < ((a + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp this)
  exact le_antisymm hle1 hle2

theorem tendsto_invSucc_nat_eventually_const {u : ℕ → ℕ} {t : ℝ}
    (h : Filter.Tendsto (fun i : ℕ => ((u i : ℝ) + 1)⁻¹) Filter.atTop (nhds t)) (ht : t ≠ 0) :
    ∃ m : ℕ, t = ((m : ℝ) + 1)⁻¹ ∧ ∀ᶠ i in Filter.atTop, u i = m := by
  set w : ℕ → ℝ := fun i => (u i : ℝ) + 1 with hwdef
  -- Invert the limit: `w i = (u i : ℝ) + 1` tends to `t⁻¹`.
  have hw : Filter.Tendsto w Filter.atTop (nhds t⁻¹) := by
    have := h.inv₀ ht
    simpa [hwdef] using this
  -- Eventually `w i` lies in the ball of radius `1/4` about `t⁻¹`.
  have hev : ∀ᶠ i in Filter.atTop, dist (w i) (t⁻¹) < 1/4 := by
    have hb := hw.eventually (Metric.ball_mem_nhds (t⁻¹) (by norm_num : (0 : ℝ) < 1/4))
    simpa only [Metric.mem_ball] using hb
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  -- All the values `w i` for `i ≥ N` are within `1/2` of each other, so equal,
  -- whence `u` is eventually constant.
  have hconst : ∀ i ≥ N, u i = u N := by
    intro i hi
    have hd : dist (w i) (w N) < 1/2 := by
      have h1 := hN i hi
      have h2 := hN N le_rfl
      calc dist (w i) (w N) ≤ dist (w i) (t⁻¹) + dist (t⁻¹) (w N) := dist_triangle _ _ _
        _ < 1/4 + 1/4 := by rw [dist_comm (t⁻¹) (w N)]; linarith
        _ = 1/2 := by norm_num
    apply nat_eq_of_abs_sub_lt_one
    have hww : w i - w N = (u i : ℝ) - (u N : ℝ) := by simp only [hwdef]; ring
    have : |(u i : ℝ) - (u N : ℝ)| = dist (w i) (w N) := by
      rw [Real.dist_eq, ← hww]
    rw [this]; linarith
  -- The original sequence is eventually the constant `((u N : ℝ) + 1)⁻¹`,
  -- hence its limit `t` equals that constant.
  have heq : (fun i => ((u i : ℝ) + 1)⁻¹) =ᶠ[Filter.atTop] (fun _ => ((u N : ℝ) + 1)⁻¹) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, hconst⟩] with i hi
    simp [hi]
  have ht_eq : t = ((u N : ℝ) + 1)⁻¹ :=
    tendsto_nhds_unique (h.congr' heq) tendsto_const_nhds
  exact ⟨u N, ht_eq, Filter.eventually_atTop.mpr ⟨N, hconst⟩⟩

end Work.Topology
