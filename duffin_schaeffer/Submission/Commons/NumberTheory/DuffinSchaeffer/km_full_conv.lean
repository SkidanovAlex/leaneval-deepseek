import Mathlib.NumberTheory.WellApproximable

open Set Filter MeasureTheory
open scoped ENNReal Topology Pointwise

namespace Commons.NumberTheory.DuffinSchaeffer

private lemma ball_measure_le (δ : ℝ) (x : UnitAddCircle) :
    MeasureTheory.volume (Metric.ball x δ) ≤ ENNReal.ofReal (2 * δ) := by
  calc
    MeasureTheory.volume (Metric.ball x δ) ≤
        MeasureTheory.volume (Metric.closedBall x δ) :=
      measure_mono (μ := (volume : Measure UnitAddCircle)) Metric.ball_subset_closedBall
    _ = ENNReal.ofReal (min 1 (2 * δ)) := by
      simpa using (AddCircle.volume_closedBall (T := 1) (x := x) (ε := δ))
    _ ≤ ENNReal.ofReal (2 * δ) := by
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

private lemma volume_approx_pos_le (n : ℕ) (hn : 0 < n) (δ : ℝ) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle n δ) ≤
      (n.totient : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := by
  let F : Finset ℕ := Finset.filter (fun m : ℕ => n.Coprime m) (Finset.range n)
  have h_sub : approxAddOrderOf UnitAddCircle n δ ⊆
      ⋃ m ∈ F, Metric.ball (↑((m : ℝ) / n) : UnitAddCircle) δ := by
    intro x hx
    rw [UnitAddCircle.mem_approxAddOrderOf_iff hn] at hx
    rcases hx with ⟨m, hm_lt, hm_cop, hx⟩
    refine mem_iUnion₂.2 ⟨m, ?_, ?_⟩
    · simp [F, Finset.mem_filter, Finset.mem_range, hm_lt, Nat.coprime_iff_gcd_eq_one]
      rwa [Nat.gcd_comm n m]
    · simpa [Metric.mem_ball, dist_eq_norm] using hx
  calc
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle n δ) ≤
        MeasureTheory.volume (⋃ m ∈ F, Metric.ball (↑((m : ℝ) / n) : UnitAddCircle) δ) :=
      measure_mono (μ := (volume : Measure UnitAddCircle)) h_sub
    _ ≤ ∑ m ∈ F, MeasureTheory.volume (Metric.ball (↑((m : ℝ) / n) : UnitAddCircle) δ) :=
      MeasureTheory.measure_biUnion_finset_le F
        (fun m => Metric.ball (↑((m : ℝ) / n) : UnitAddCircle) δ)
    _ ≤ ∑ m ∈ F, ENNReal.ofReal (2 * δ) := by
      exact Finset.sum_le_sum fun m hm => ball_measure_le δ (↑((m : ℝ) / n) : UnitAddCircle)
    _ = (n.totient : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := by
      simp [F, Nat.totient, Finset.sum_const, nsmul_eq_mul]

private lemma totient_mul_ofReal_eq (n : ℕ) (δ : ℝ) :
    (n.totient : ℝ≥0∞) * ENNReal.ofReal (2 * δ) =
      ENNReal.ofReal (2 * (n.totient : ℝ) * δ) := by
  rw [show 2 * (n.totient : ℝ) * δ = 2 * ((n.totient : ℝ) * δ) by ring]
  conv_rhs => rw [ENNReal.ofReal_mul zero_le_two]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  simp only [ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_mul zero_le_two]
  rw [← mul_assoc]
  rw [mul_comm (↑n.totient : ℝ≥0∞) (ENNReal.ofReal (2 : ℝ))]
  rw [mul_assoc]

theorem km_full_conv (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (h : Summable fun n : ℕ => n.totient * δ n) :
    MeasureTheory.volume (addWellApproximable UnitAddCircle δ) = 0 := by
  have _hδ : ∀ n, 0 ≤ δ n := hδ
  let s : ℕ → Set UnitAddCircle := fun n => approxAddOrderOf UnitAddCircle n (δ n)
  let s' : ℕ → Set UnitAddCircle := fun n => s (n + 1)
  let g : ℕ → ℝ≥0∞ := fun n => (n.totient : ℝ≥0∞) * ENNReal.ofReal (2 * δ n)
  have hg_sum : ∑' n, g n ≠ ∞ := by
    have hf : Summable (fun n : ℕ => 2 * (n.totient : ℝ) * δ n) := by
      simpa [mul_assoc] using h.mul_left 2
    have hcong : (∑' n, g n) = ∑' n, ENNReal.ofReal (2 * (n.totient : ℝ) * δ n) := by
      refine tsum_congr fun n => ?_
      exact totient_mul_ofReal_eq n (δ n)
    rw [hcong]
    exact hf.tsum_ofReal_ne_top
  have hg_shift : ∑' n, g (n + 1) ≠ ∞ := by
    apply ne_top_of_le_ne_top hg_sum
    have h_inj : Function.Injective (fun n : ℕ => n + 1) := Nat.succ_injective
    exact ENNReal.tsum_comp_le_tsum_of_injective h_inj g
  have hs'_le : ∑' n, MeasureTheory.volume (s' n) ≤ ∑' n, g (n + 1) := by
    apply ENNReal.tsum_le_tsum
    intro n
    dsimp [s', s, g]
    exact volume_approx_pos_le (n + 1) n.succ_pos (δ (n + 1))
  have hs'_sum : ∑' n, MeasureTheory.volume (s' n) ≠ ∞ :=
    ne_top_of_le_ne_top hg_shift hs'_le
  have hlim' : MeasureTheory.volume (limsup s' atTop) = 0 :=
    MeasureTheory.measure_limsup_atTop_eq_zero hs'_sum
  have hlim_eq : limsup s' atTop = limsup s atTop := by
    dsimp [s']
    exact limsup_nat_add s 1
  have h_sub : addWellApproximable UnitAddCircle δ ⊆ limsup s atTop := by
    dsimp [s, addWellApproximable]
    simpa [blimsup_true] using
      (blimsup_mono (u := fun n : ℕ => approxAddOrderOf UnitAddCircle n (δ n))
        (f := atTop) (p := fun n : ℕ => 0 < n) (q := fun _ : ℕ => True) (by intro n _; trivial))
  have hle : MeasureTheory.volume (addWellApproximable UnitAddCircle δ) ≤ 0 := by
    calc
      MeasureTheory.volume (addWellApproximable UnitAddCircle δ) ≤
          MeasureTheory.volume (limsup s atTop) :=
        measure_mono (μ := (volume : Measure UnitAddCircle)) h_sub
      _ = MeasureTheory.volume (limsup s' atTop) := by rw [hlim_eq]
      _ = 0 := hlim'
  exact le_antisymm hle zero_le

end Commons.NumberTheory.DuffinSchaeffer