import Mathlib

set_option linter.unusedVariables false

open MeasureTheory intervalIntegral

namespace Work.C17g

/-! Auxiliary lemmas for `Work.C17g.iter_bound`.

`integral_norm_le_pow` is the elementary integral estimate
`‖∫₀¹ f‖ ≤ C / (m+1)` for a continuous `f` with `‖f t‖ ≤ C tᵐ` on `[0,1]`.

`Y_sub_integral` rewrites the difference of two consecutive Picard iterates as a single
integral of the linear part applied to `Y (n+1) - Y n` (linearity of the interval integral,
with the `b` terms cancelling). -/

private lemma integral_norm_le_pow {k : ℕ} {f : ℝ → (Fin k → ℂ)} {C : ℝ} {m : ℕ}
    (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (h : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖f t‖ ≤ C * t ^ m) :
    ‖∫ t in (0:ℝ)..1, f t‖ ≤ C / (m + 1) := by
  have hfi : IntervalIntegrable (fun t : ℝ => ‖f t‖) volume 0 1 :=
    hf.norm.intervalIntegrable_of_Icc zero_le_one
  have hgi : IntervalIntegrable (fun t : ℝ => C * t ^ m) volume 0 1 :=
    ((continuous_const.mul (continuous_id.pow m)).continuousOn).intervalIntegrable_of_Icc zero_le_one
  calc ‖∫ t in (0:ℝ)..1, f t‖ ≤ ∫ t in (0:ℝ)..1, ‖f t‖ := norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0:ℝ)..1, C * t ^ m := integral_mono_on zero_le_one hfi hgi h
    _ = C / (m + 1) := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        rw [one_pow, zero_pow (Nat.succ_ne_zero m), sub_zero, one_div, div_eq_mul_inv]

private lemma Y_sub_integral {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (z₀ : ℂ)
    (Y₀ : Fin k → ℂ) (Y : ℕ → ℂ → (Fin k → ℂ))
    (hrec : ∀ n z, Y (n+1) z = Y₀ + (z - z₀) • (∫ t in (0:ℝ)..1, fun i =>
        (∑ j, A (z₀ + t • (z - z₀)) i j * Y n (z₀ + t • (z - z₀)) j)
          + b (z₀ + t • (z - z₀)) i))
    {T : Set ℂ} (hrad : ∀ z ∈ T, ∀ t ∈ Set.Icc (0:ℝ) 1, z₀ + t • (z - z₀) ∈ T)
    (hAc : ∀ i j, ContinuousOn (fun z => A z i j) T) (hbc : ∀ i, ContinuousOn (fun z => b z i) T)
    (hYc : ∀ n, ∀ z ∈ T, ContinuousOn (fun t : ℝ => Y n (z₀ + t • (z - z₀))) (Set.Icc 0 1))
    (n : ℕ) (z : ℂ) (hz : z ∈ T) :
    Y (n+2) z - Y (n+1) z =
      (z - z₀) • ∫ t in (0:ℝ)..1, (fun i =>
        ∑ j, A (z₀ + t • (z - z₀)) i j *
          (Y (n+1) (z₀ + t • (z - z₀)) j - Y n (z₀ + t • (z - z₀)) j)) := by
  have hγ : ContinuousOn (fun t : ℝ => z₀ + t • (z - z₀)) (Set.Icc 0 1) := by
    exact continuousOn_const.add (continuousOn_id.smul continuousOn_const)
  have hmt : Set.MapsTo (fun t : ℝ => z₀ + t • (z - z₀)) (Set.Icc 0 1) T :=
    fun t ht => hrad z hz t ht
  have hcont : ∀ m : ℕ, ContinuousOn (fun t : ℝ => (fun i => (∑ j, A (z₀ + t • (z - z₀)) i j * Y m (z₀ + t • (z - z₀)) j) + b (z₀ + t • (z - z₀)) i)) (Set.Icc 0 1) := by
    intro m
    rw [continuousOn_pi]
    intro i
    have h1 : ContinuousOn (fun t : ℝ => ∑ j, A (z₀ + t • (z - z₀)) i j * Y m (z₀ + t • (z - z₀)) j) (Set.Icc 0 1) := by
      apply continuousOn_finsetSum
      intro j _
      exact ((hAc i j).comp hγ hmt).mul ((continuousOn_pi.mp (hYc m z hz)) j)
    exact h1.add ((hbc i).comp hγ hmt)
  have hInt_s := (hcont (n+1)).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hInt_n := (hcont n).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  rw [hrec (n+1) z, hrec n z, add_sub_add_left_eq_sub, ← smul_sub]
  rw [← intervalIntegral.integral_sub hInt_s hInt_n]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  ext i
  simp only [Pi.sub_apply]
  rw [add_sub_add_comm, sub_self, add_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem iter_bound {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (z₀ : ℂ)
    (Y₀ : Fin k → ℂ) (Y : ℕ → ℂ → (Fin k → ℂ))
    (hY0 : ∀ z, Y 0 z = Y₀)
    (hrec : ∀ n z, Y (n+1) z = Y₀ + (z - z₀) • (∫ t in (0:ℝ)..1, fun i =>
        (∑ j, A (z₀ + t • (z - z₀)) i j * Y n (z₀ + t • (z - z₀)) j)
          + b (z₀ + t • (z - z₀)) i))
    {T : Set ℂ} (hz₀T : z₀ ∈ T) (hrad : ∀ z ∈ T, ∀ t ∈ Set.Icc (0:ℝ) 1, z₀ + t • (z - z₀) ∈ T)
    (hAc : ∀ i j, ContinuousOn (fun z => A z i j) T) (hbc : ∀ i, ContinuousOn (fun z => b z i) T)
    (hYc : ∀ n, ∀ z ∈ T, ContinuousOn (fun t : ℝ => Y n (z₀ + t • (z - z₀))) (Set.Icc 0 1))
    {M C₀ : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀)
    (hAb : ∀ z ∈ T, ∀ x : Fin k → ℂ, ‖(fun i => ∑ j, A z i j * x j)‖ ≤ M * ‖x‖)
    (hb0 : ∀ z ∈ T, ‖(fun i => (∑ j, A z i j * Y₀ j) + b z i)‖ ≤ C₀) :
    ∀ n (z : ℂ), z ∈ T → ‖Y (n+1) z - Y n z‖ ≤ C₀ * M ^ n * ‖z - z₀‖ ^ (n+1) / Nat.factorial (n+1) := by
  have hγ : ∀ z : ℂ, z ∈ T → ContinuousOn (fun t : ℝ => z₀ + t • (z - z₀)) (Set.Icc 0 1) := fun z _ =>
    continuousOn_const.add (continuousOn_id.smul continuousOn_const)
  have hmt : ∀ z ∈ T, Set.MapsTo (fun t : ℝ => z₀ + t • (z - z₀)) (Set.Icc 0 1) T :=
    fun z hz t ht => hrad z hz t ht
  have hcont : ∀ (m : ℕ) (z : ℂ) (hz : z ∈ T),
      ContinuousOn (fun t : ℝ => (fun i => (∑ j, A (z₀ + t • (z - z₀)) i j * Y m (z₀ + t • (z - z₀)) j) + b (z₀ + t • (z - z₀)) i)) (Set.Icc 0 1) := by
    intro m z hz
    rw [continuousOn_pi]
    intro i
    have h1 : ContinuousOn (fun t : ℝ => ∑ j, A (z₀ + t • (z - z₀)) i j * Y m (z₀ + t • (z - z₀)) j) (Set.Icc 0 1) := by
      apply continuousOn_finsetSum
      intro j _
      exact ((hAc i j).comp (hγ z hz) (hmt z hz)).mul ((continuousOn_pi.mp (hYc m z hz)) j)
    exact h1.add ((hbc i).comp (hγ z hz) (hmt z hz))
  intro n
  induction n with
  | zero =>
    intro z hz
    have hb : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖(fun i => (∑ j, A (z₀ + t • (z - z₀)) i j * Y 0 (z₀ + t • (z - z₀)) j) + b (z₀ + t • (z - z₀)) i)‖ ≤ C₀ * t ^ 0 := by
      intro t ht
      rw [pow_zero, mul_one, hY0 (z₀ + t • (z - z₀))]
      exact hb0 _ (hrad z hz t ht)
    have hint : ‖∫ t in (0:ℝ)..1, (fun i => (∑ j, A (z₀ + t • (z - z₀)) i j * Y 0 (z₀ + t • (z - z₀)) j) + b (z₀ + t • (z - z₀)) i)‖ ≤ C₀ := by
      simpa using integral_norm_le_pow (hcont 0 z hz) hb
    rw [hrec 0 z, hY0 z, add_sub_cancel_left, norm_smul]
    calc ‖z - z₀‖ * ‖∫ t in (0:ℝ)..1, (fun i => (∑ j, A (z₀ + t • (z - z₀)) i j * Y 0 (z₀ + t • (z - z₀)) j) + b (z₀ + t • (z - z₀)) i)‖
        ≤ ‖z - z₀‖ * C₀ := mul_le_mul_of_nonneg_left hint (norm_nonneg _)
      _ = C₀ * M ^ 0 * ‖z - z₀‖ ^ (0+1) / Nat.factorial (0+1) := by
            rw [show (0:ℕ)+1 = 1 from rfl]
            rw [pow_zero, pow_one, Nat.factorial_one]
            ring
  | succ n ih =>
    intro z hz
    have hsub := Y_sub_integral A b z₀ Y₀ Y hrec hrad hAc hbc hYc n z hz
    have hHcont : ContinuousOn (fun t : ℝ => (fun i => ∑ j, A (z₀ + t • (z - z₀)) i j * (Y (n+1) (z₀ + t • (z - z₀)) j - Y n (z₀ + t • (z - z₀)) j))) (Set.Icc 0 1) := by
      rw [continuousOn_pi]
      intro i
      apply continuousOn_finsetSum
      intro j _
      exact ((hAc i j).comp (hγ z hz) (hmt z hz)).mul (((continuousOn_pi.mp (hYc (n+1) z hz)) j).sub ((continuousOn_pi.mp (hYc n z hz)) j))
    have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
        ‖(fun i => ∑ j, A (z₀ + t • (z - z₀)) i j * (Y (n+1) (z₀ + t • (z - z₀)) j - Y n (z₀ + t • (z - z₀)) j))‖
          ≤ (C₀ * M ^ (n+1) * ‖z - z₀‖ ^ (n+1) / Nat.factorial (n+1)) * t ^ (n+1) := by
      intro t ht
      have hw : z₀ + t • (z - z₀) ∈ T := hrad z hz t ht
      have hnorm : ‖(z₀ + t • (z - z₀)) - z₀‖ = t * ‖z - z₀‖ := by
        rw [add_sub_cancel_left, norm_smul]
        simp [abs_of_nonneg ht.1]
      calc ‖(fun i => ∑ j, A (z₀ + t • (z - z₀)) i j * (Y (n+1) (z₀ + t • (z - z₀)) j - Y n (z₀ + t • (z - z₀)) j))‖
          ≤ M * ‖Y (n+1) (z₀ + t • (z - z₀)) - Y n (z₀ + t • (z - z₀))‖ := hAb _ hw _
        _ ≤ M * (C₀ * M ^ n * ‖(z₀ + t • (z - z₀)) - z₀‖ ^ (n+1) / Nat.factorial (n+1)) :=
              mul_le_mul_of_nonneg_left (ih _ hw) hM
        _ = (C₀ * M ^ (n+1) * ‖z - z₀‖ ^ (n+1) / Nat.factorial (n+1)) * t ^ (n+1) := by
              rw [hnorm, mul_pow]; ring
    have hint := integral_norm_le_pow hHcont hpt
    rw [hsub, norm_smul]
    calc ‖z - z₀‖ * ‖∫ t in (0:ℝ)..1, (fun i => ∑ j, A (z₀ + t • (z - z₀)) i j * (Y (n+1) (z₀ + t • (z - z₀)) j - Y n (z₀ + t • (z - z₀)) j))‖
        ≤ ‖z - z₀‖ * ((C₀ * M ^ (n+1) * ‖z - z₀‖ ^ (n+1) / Nat.factorial (n+1)) / (↑(n+1) + 1)) :=
            mul_le_mul_of_nonneg_left hint (norm_nonneg _)
      _ = C₀ * M ^ (n+1) * ‖z - z₀‖ ^ (n+2) / Nat.factorial (n+2) := by
            have hfac : (Nat.factorial (n+2) : ℝ) = (↑(n+1) + 1) * ↑(Nat.factorial (n+1)) := by
              rw [show n+2 = (n+1)+1 from rfl, Nat.factorial_succ]
              push_cast
              ring
            have hpow : ‖z - z₀‖ ^ (n+2) = ‖z - z₀‖ ^ (n+1) * ‖z - z₀‖ := by
              rw [show n+2 = (n+1)+1 from rfl, pow_succ]
            rw [hfac, hpow]
            field_simp

end Work.C17g
