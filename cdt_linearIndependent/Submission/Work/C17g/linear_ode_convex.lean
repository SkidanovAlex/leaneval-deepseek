import Mathlib
import Submission.Work.C17g.segment_primitive
import Submission.Work.C17g.iter_bound
import Submission.Work.C17g.ode_bounds_compact
import Submission.Work.C17g.ode_integral_limit

/-! Guidance from the project lead (the requester):

# Holomorphic linear ODE on a convex open set (generic)
S is star-shaped w.r.t. z₀: Picard iteration along segments,
Y_{j+1}(z) = Y₀ + ∫₀¹ (A(z₀+t(z−z₀)) Y_j(z₀+t(z−z₀)) + b(…))·(z−z₀) dt;
the bound ‖Y_{j+1}−Y_j‖ ≤ C(M|z−z₀|)^j/j! gives convergence; each iterate is holomorphic
(parameter integrals), hence so is the limit; the limit satisfies the integral equation, hence
the differential equation (differentiate the integral equation in z).

This file formalises the theorem `Work.C17g.linear_ode_convex`.
-/

namespace Work.C17g

open Complex Metric MeasureTheory intervalIntegral Filter Topology
open scoped BigOperators

noncomputable section

variable {k : ℕ}

/-- The right-hand side of the linear system `X' = A(z)X + b(z)`. -/
def odeField (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (z : ℂ) (x : Fin k → ℂ) :
    Fin k → ℂ :=
  fun i => (∑ j, A z i j * x j) + b z i

/-- The Picard iterates for the linear system `X' = A(z)X + b(z)`, integrating along the straight
segment from `z₀` to `z`. -/
def iter (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (z₀ : ℂ) (Y₀ : Fin k → ℂ) :
    ℕ → ℂ → (Fin k → ℂ)
  | 0 => fun _ => Y₀
  | (n+1) => fun z => Y₀ + (z - z₀) •
      ∫ t in (0:ℝ)..1, odeField A b (z₀ + t • (z - z₀)) (iter A b z₀ Y₀ n (z₀ + t • (z - z₀)))

@[simp] lemma iter_zero (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (z₀ : ℂ)
    (Y₀ : Fin k → ℂ) (z : ℂ) : iter A b z₀ Y₀ 0 z = Y₀ := rfl

lemma iter_succ (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (z₀ : ℂ)
    (Y₀ : Fin k → ℂ) (n : ℕ) (z : ℂ) :
    iter A b z₀ Y₀ (n+1) z = Y₀ + (z - z₀) •
      ∫ t in (0:ℝ)..1,
        odeField A b (z₀ + t • (z - z₀)) (iter A b z₀ Y₀ n (z₀ + t • (z - z₀))) := rfl

/-- The limit function of the Picard iteration, defined as the sum of the series of differences. -/
def Ylim (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (z₀ : ℂ) (Y₀ : Fin k → ℂ) :
    ℂ → (Fin k → ℂ) :=
  fun w => Y₀ + ∑' n, (iter A b z₀ Y₀ (n+1) w - iter A b z₀ Y₀ n w)

section Componentwise

variable {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ} {S : Set ℂ}

lemma differentiableOn_A_apply (hA : DifferentiableOn ℂ A S) (i j : Fin k) :
    DifferentiableOn ℂ (fun z => A z i j) S := by
  have h1 : DifferentiableOn ℂ (fun z => A z i) S := (differentiableOn_pi.mp hA) i
  exact (differentiableOn_pi.mp h1) j

lemma differentiableOn_b_apply (hb : DifferentiableOn ℂ b S) (i : Fin k) :
    DifferentiableOn ℂ (fun z => b z i) S :=
  (differentiableOn_pi.mp hb) i

lemma continuousOn_A_apply (hA : DifferentiableOn ℂ A S) (i j : Fin k) :
    ContinuousOn (fun z => A z i j) S :=
  (differentiableOn_A_apply hA i j).continuousOn

lemma continuousOn_b_apply (hb : DifferentiableOn ℂ b S) (i : Fin k) :
    ContinuousOn (fun z => b z i) S :=
  (differentiableOn_b_apply hb i).continuousOn

end Componentwise

/-- The field `z ↦ A(z)X(z) + b(z)` is holomorphic when `A`, `b` and `X` are. -/
lemma differentiableOn_odeField {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ} {S : Set ℂ}
    {Y : ℂ → Fin k → ℂ} (hA : DifferentiableOn ℂ A S) (hb : DifferentiableOn ℂ b S)
    (hY : DifferentiableOn ℂ Y S) :
    DifferentiableOn ℂ (fun z => odeField A b z (Y z)) S := by
  have h : (fun z => odeField A b z (Y z)) = fun z => fun i => (∑ j, A z i j * Y z j) + b z i :=
    rfl
  rw [h]
  fun_prop

/-- **Every Picard iterate is holomorphic on `S`.** -/
lemma iter_holo {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ} {S : Set ℂ}
    (hS : Convex ℝ S) (hSo : IsOpen S) (hA : DifferentiableOn ℂ A S)
    (hb : DifferentiableOn ℂ b S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) (Y₀ : Fin k → ℂ) :
    ∀ n, DifferentiableOn ℂ (iter A b z₀ Y₀ n) S := by
  intro n
  induction n with
  | zero => exact differentiableOn_const (c := (Y₀ : Fin k → ℂ))
  | succ n ih =>
    have hfd : DifferentiableOn ℂ (fun z => odeField A b z (iter A b z₀ Y₀ n z)) S :=
      differentiableOn_odeField hA hb ih
    obtain ⟨hP, -⟩ := segment_primitive hS hSo hz₀ hfd
    have hstep : iter A b z₀ Y₀ (n+1) =
        fun z => Y₀ + (z - z₀) •
          ∫ t in (0:ℝ)..1,
            odeField A b (z₀ + t • (z - z₀)) (iter A b z₀ Y₀ n (z₀ + t • (z - z₀))) := by
      funext z
      rw [iter_succ]
    rw [hstep]
    exact hP.const_add Y₀

/-- **The local compact set attached to a point `z ∈ S`.**

For `z` in a convex open set `S` there is a compact set `T ⊆ S` containing `z₀` and a ball around
`z`, and closed under the contractions `w ↦ z₀ + t • (w - z₀)`, `t ∈ [0,1]`. -/
private lemma exists_localSet {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S) {z₀ : ℂ}
    (hz₀ : z₀ ∈ S) {z : ℂ} (hz : z ∈ S) :
    ∃ T : Set ℂ, IsCompact T ∧ T.Nonempty ∧ z₀ ∈ T ∧ z ∈ T ∧
      (∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ T) ∧ T ⊆ S ∧
      (∀ w ∈ T, ∀ t ∈ Set.Icc (0:ℝ) 1, z₀ + t • (w - z₀) ∈ T) := by
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp (hSo.mem_nhds hz)
  set ρ : ℝ := ε / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρle : ρ < ε := by rw [hρdef]; linarith
  have hρ0 : (0:ℝ) ≤ ρ := hρ.le
  refine ⟨(fun p : ℝ × ℂ => z₀ + p.1 • (p.2 - z₀)) '' (Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall z ρ),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isCompact_Icc.prod (isCompact_closedBall z ρ)).image (by fun_prop)
  · exact ⟨z₀, ⟨(0, z), ⟨⟨le_refl 0, zero_le_one⟩, mem_closedBall_self hρ0⟩, by simp⟩⟩
  · exact ⟨(0, z), ⟨⟨le_refl 0, zero_le_one⟩, mem_closedBall_self hρ0⟩, by simp⟩
  · exact ⟨(1, z), ⟨⟨zero_le_one, le_refl 1⟩, mem_closedBall_self hρ0⟩, by simp⟩
  · refine ⟨ρ, hρ, ?_⟩
    rintro w hw
    exact ⟨(1, w), ⟨⟨zero_le_one, le_refl 1⟩, Metric.ball_subset_closedBall hw⟩, by simp⟩
  · rintro w ⟨p, ⟨hp1, hp2⟩, rfl⟩
    have hmemS : p.2 ∈ S := hεS ((Metric.closedBall_subset_ball hρle) hp2)
    have hcombo := hS hz₀ hmemS (by linarith [hp1.2] : (0:ℝ) ≤ 1 - p.1) hp1.1
      (by ring : (1 - p.1) + p.1 = 1)
    have heq : (1 - p.1) • z₀ + p.1 • p.2 = z₀ + p.1 • (p.2 - z₀) := by module
    rwa [heq] at hcombo
  · rintro w ⟨p, ⟨hp1, hp2⟩, rfl⟩ t ht
    refine ⟨(t * p.1, p.2), ⟨⟨mul_nonneg ht.1 hp1.1, ?_⟩, hp2⟩, ?_⟩
    · calc t * p.1 ≤ 1 * 1 := mul_le_mul ht.2 hp1.2 (by linarith [hp1.1]) (by norm_num)
        _ = 1 := by ring
    · have hsub : z₀ + p.1 • (p.2 - z₀) - z₀ = p.1 • (p.2 - z₀) := by abel
      rw [hsub, smul_smul]

/-- Comparison of the terms of the Picard estimate with a summable majorant. -/
private lemma iter_term_le {C M R r : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hr : 0 ≤ r) (hrR : r ≤ R) (n : ℕ) :
    C * M ^ n * r ^ (n+1) / (Nat.factorial (n+1) : ℝ)
      ≤ C * R * (M * R) ^ n / (Nat.factorial n : ℝ) := by
  have h1 : C * M ^ n * r ^ (n+1) ≤ C * M ^ n * R ^ (n+1) := by
    have hpow : r ^ (n+1) ≤ R ^ (n+1) := pow_le_pow_left₀ hr hrR _
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have h2 : (0:ℝ) ≤ C * M ^ n * R ^ (n+1) := by positivity
  have h3 : (Nat.factorial n : ℝ) ≤ (Nat.factorial (n+1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  have hden : (0:ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hkey : C * M ^ n * R ^ (n+1) = C * R * (M * R) ^ n := by
    rw [pow_succ, mul_pow]; ring
  calc C * M ^ n * r ^ (n+1) / (Nat.factorial (n+1) : ℝ)
      ≤ C * M ^ n * R ^ (n+1) / (Nat.factorial (n+1) : ℝ) :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ C * M ^ n * R ^ (n+1) / (Nat.factorial n : ℝ) :=
        div_le_div_of_nonneg_left h2 hden h3
    _ = C * R * (M * R) ^ n / (Nat.factorial n : ℝ) := by rw [hkey]

/-- The summable majorant of the series of differences. -/
private lemma summable_majorant (C M R : ℝ) :
    Summable (fun m : ℕ => C * R * (M * R) ^ m / (Nat.factorial m : ℝ)) := by
  have h := (Real.summable_pow_div_factorial (M * R)).mul_left (C * R)
  simpa [mul_div_assoc] using h

/-- The local data (compact set, bounds, and the Picard estimate) attached to a point of `S`. -/
private structure OdeLocalData (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (z₀ : ℂ)
    (Y₀ : Fin k → ℂ) (S : Set ℂ) (z : ℂ) where
  T : Set ℂ
  M : ℝ
  C₀ : ℝ
  R : ℝ
  B : ℝ
  hT : IsCompact T
  hTne : T.Nonempty
  hz₀T : z₀ ∈ T
  hzT : z ∈ T
  ρ : ℝ
  hρ : 0 < ρ
  hball : Metric.ball z ρ ⊆ T
  hTS : T ⊆ S
  hrad : ∀ w ∈ T, ∀ t ∈ Set.Icc (0:ℝ) 1, z₀ + t • (w - z₀) ∈ T
  hM : 0 ≤ M
  hC₀ : 0 ≤ C₀
  hR : 0 ≤ R
  hB : 0 ≤ B
  hRbd : ∀ w ∈ T, ‖w - z₀‖ ≤ R
  hAb : ∀ w ∈ T, ∀ x : Fin k → ℂ, ‖(fun i => ∑ j, A w i j * x j)‖ ≤ M * ‖x‖
  hb0 : ∀ w ∈ T, ‖(fun i => (∑ j, A w i j * Y₀ j) + b w i)‖ ≤ C₀
  hbB : ∀ w ∈ T, ‖b w‖ ≤ B
  hest : ∀ n (w : ℂ), w ∈ T →
    ‖iter A b z₀ Y₀ (n+1) w - iter A b z₀ Y₀ n w‖
      ≤ C₀ * M ^ n * ‖w - z₀‖ ^ (n+1) / (Nat.factorial (n+1) : ℝ)
  hBiter : ∀ n (w : ℂ), w ∈ T → ‖iter A b z₀ Y₀ n w‖ ≤ B

/-- Construction of the local data at a point of `S`. -/
private lemma odeLocalData_exists {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ} {S : Set ℂ}
    (hS : Convex ℝ S) (hSo : IsOpen S) (hA : DifferentiableOn ℂ A S)
    (hb : DifferentiableOn ℂ b S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) (Y₀ : Fin k → ℂ) {z : ℂ}
    (hz : z ∈ S) : Nonempty (OdeLocalData A b z₀ Y₀ S z) := by
  obtain ⟨T, hT, hTne, hz₀T, hzT, ⟨ρ', hρ', hball'⟩, hTS, hrad⟩ :=
    exists_localSet hS hSo hz₀ hz
  have hAcT : ∀ i j, ContinuousOn (fun z => A z i j) T :=
    fun i j => (continuousOn_A_apply hA i j).mono hTS
  have hbcT : ∀ i, ContinuousOn (fun z => b z i) T :=
    fun i => (continuousOn_b_apply hb i).mono hTS
  obtain ⟨M, C₀, R, hM, hC₀, hRbd, hAb, hb0⟩ :=
    ode_bounds_compact A b z₀ Y₀ hT hTne hAcT hbcT
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hRbd z₀ hz₀T)
  have hYc : ∀ n, ∀ w ∈ T,
      ContinuousOn (fun t : ℝ => iter A b z₀ Y₀ n (z₀ + t • (w - z₀))) (Set.Icc 0 1) := by
    intro n w hw
    have hcontW : ContinuousOn (fun t : ℝ => z₀ + t • (w - z₀)) (Set.Icc 0 1) := by fun_prop
    exact ((iter_holo hS hSo hA hb hz₀ Y₀ n).continuousOn.mono hTS).comp hcontW
      (fun t ht => hrad w hw t ht)
  have hest : ∀ n (w : ℂ), w ∈ T →
      ‖iter A b z₀ Y₀ (n+1) w - iter A b z₀ Y₀ n w‖
        ≤ C₀ * M ^ n * ‖w - z₀‖ ^ (n+1) / (Nat.factorial (n+1) : ℝ) := fun n w hw =>
    iter_bound A b z₀ Y₀ (iter A b z₀ Y₀) (fun _ => rfl)
      (fun n z => iter_succ A b z₀ Y₀ n z)
      hz₀T hrad hAcT hbcT hYc hM hC₀ hAb hb0 n w hw
  have hsumm := summable_majorant C₀ M R
  set B : ℝ := ‖Y₀‖ + (∑' m, C₀ * R * (M * R) ^ m / (Nat.factorial m : ℝ)) + C₀ + M * ‖Y₀‖
    with hBdef
  have htsum0 : 0 ≤ ∑' m, C₀ * R * (M * R) ^ m / (Nat.factorial m : ℝ) :=
    tsum_nonneg (fun m => by positivity)
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hbB : ∀ w ∈ T, ‖b w‖ ≤ B := by
    intro w hw
    have hb_eq : b w = (fun i => (∑ j, A w i j * Y₀ j) + b w i) - (fun i => ∑ j, A w i j * Y₀ j) := by
      funext i; simp
    have h1 : ‖b w‖ ≤ ‖(fun i => (∑ j, A w i j * Y₀ j) + b w i)‖
        + ‖(fun i => ∑ j, A w i j * Y₀ j)‖ := by
      conv_lhs => rw [hb_eq]
      exact norm_sub_le _ _
    have h2 : ‖(fun i => (∑ j, A w i j * Y₀ j) + b w i)‖ ≤ C₀ := hb0 w hw
    have h4 : ‖(fun i => ∑ j, A w i j * Y₀ j)‖ ≤ M * ‖Y₀‖ := hAb w hw Y₀
    rw [hBdef]
    linarith [norm_nonneg Y₀, htsum0]
  have hBiter : ∀ n (w : ℂ), w ∈ T → ‖iter A b z₀ Y₀ n w‖ ≤ B := by
    intro n w hw
    have htele : iter A b z₀ Y₀ n w
        = Y₀ + ∑ k ∈ Finset.range n, (iter A b z₀ Y₀ (k+1) w - iter A b z₀ Y₀ k w) := by
      have h := Finset.eq_sum_range_sub (fun k => iter A b z₀ Y₀ k w) n
      simpa [iter_zero] using h
    have hstep : ∀ k ∈ Finset.range n,
        ‖iter A b z₀ Y₀ (k+1) w - iter A b z₀ Y₀ k w‖
          ≤ C₀ * R * (M * R) ^ k / (Nat.factorial k : ℝ) := fun k _ =>
      le_trans (hest k w hw) (iter_term_le hC₀ hM hR0 (norm_nonneg _) (hRbd w hw) k)
    have h2 : ∑ k ∈ Finset.range n, ‖iter A b z₀ Y₀ (k+1) w - iter A b z₀ Y₀ k w‖
        ≤ ∑ k ∈ Finset.range n, C₀ * R * (M * R) ^ k / (Nat.factorial k : ℝ) :=
      Finset.sum_le_sum hstep
    have h3 : ∑ k ∈ Finset.range n, C₀ * R * (M * R) ^ k / (Nat.factorial k : ℝ)
        ≤ ∑' m, C₀ * R * (M * R) ^ m / (Nat.factorial m : ℝ) :=
      hsumm.sum_le_tsum _ (fun k _ => by positivity)
    rw [htele]
    have h4 : ‖Y₀ + ∑ k ∈ Finset.range n, (iter A b z₀ Y₀ (k+1) w - iter A b z₀ Y₀ k w)‖
        ≤ ‖Y₀‖ + ∑ k ∈ Finset.range n, C₀ * R * (M * R) ^ k / (Nat.factorial k : ℝ) := by
      calc ‖Y₀ + ∑ k ∈ Finset.range n, (iter A b z₀ Y₀ (k+1) w - iter A b z₀ Y₀ k w)‖
          ≤ ‖Y₀‖ + ‖∑ k ∈ Finset.range n, (iter A b z₀ Y₀ (k+1) w - iter A b z₀ Y₀ k w)‖ :=
            norm_add_le _ _
        _ ≤ ‖Y₀‖ + ∑ k ∈ Finset.range n, ‖iter A b z₀ Y₀ (k+1) w - iter A b z₀ Y₀ k w‖ := by
            linarith [norm_sum_le (Finset.range n)
              (fun k => iter A b z₀ Y₀ (k+1) w - iter A b z₀ Y₀ k w)]
        _ ≤ ‖Y₀‖ + ∑ k ∈ Finset.range n, C₀ * R * (M * R) ^ k / (Nat.factorial k : ℝ) := by
            linarith
    rw [hBdef]
    linarith [hC₀, mul_nonneg hM (norm_nonneg Y₀)]
  exact ⟨⟨T, M, C₀, R, B, hT, hTne, hz₀T, hzT, ρ', hρ', hball', hTS, hrad, hM, hC₀, hR0, hB0,
    hRbd, hAb, hb0, hbB, hest, hBiter⟩⟩

/-- **The Picard iterates converge, at every point of the local set.** -/
private lemma iter_tendsto {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ} {z₀ : ℂ}
    {Y₀ : Fin k → ℂ} {S : Set ℂ} {z : ℂ} (D : OdeLocalData A b z₀ Y₀ S z) {w : ℂ}
    (hw : w ∈ D.T) :
    Tendsto (fun n => iter A b z₀ Y₀ n w) atTop (nhds (Ylim A b z₀ Y₀ w)) := by
  have hg : Summable (fun m : ℕ => D.C₀ * D.R * (D.M * D.R) ^ m / (Nat.factorial m : ℝ)) :=
    summable_majorant D.C₀ D.M D.R
  have hbd : ∀ m : ℕ, ‖iter A b z₀ Y₀ (m+1) w - iter A b z₀ Y₀ m w‖
      ≤ D.C₀ * D.R * (D.M * D.R) ^ m / (Nat.factorial m : ℝ) := fun m =>
    le_trans (D.hest m w hw) (iter_term_le D.hC₀ D.hM D.hR (norm_nonneg _) (D.hRbd w hw) m)
  have hs : Summable (fun m : ℕ => iter A b z₀ Y₀ (m+1) w - iter A b z₀ Y₀ m w) :=
    Summable.of_norm_bounded hg hbd
  have ht : Tendsto (fun n => ∑ m ∈ Finset.range n,
        (iter A b z₀ Y₀ (m+1) w - iter A b z₀ Y₀ m w)) atTop
      (nhds (∑' m, (iter A b z₀ Y₀ (m+1) w - iter A b z₀ Y₀ m w))) :=
    hs.hasSum.tendsto_sum_nat
  have htel : ∀ n : ℕ, ∑ m ∈ Finset.range n, (iter A b z₀ Y₀ (m+1) w - iter A b z₀ Y₀ m w)
      = iter A b z₀ Y₀ n w - Y₀ := by
    intro n
    have h := Finset.eq_sum_range_sub (fun m => iter A b z₀ Y₀ m w) n
    simp only [iter_zero] at h
    rw [h]; abel
  have h2 := ht.const_add Y₀
  have h3 : (fun n => Y₀ + ∑ m ∈ Finset.range n,
        (iter A b z₀ Y₀ (m+1) w - iter A b z₀ Y₀ m w)) = fun n => iter A b z₀ Y₀ n w := by
    funext n; rw [htel n]; abel
  rw [h3] at h2
  simpa [Ylim] using h2

/-- **The limit of the Picard iterates is holomorphic on `S`.** -/
private lemma Ylim_differentiableOn {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ}
    {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S) (hA : DifferentiableOn ℂ A S)
    (hb : DifferentiableOn ℂ b S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) (Y₀ : Fin k → ℂ) :
    DifferentiableOn ℂ (Ylim A b z₀ Y₀) S := by
  intro z hz
  obtain ⟨D⟩ := odeLocalData_exists hS hSo hA hb hz₀ Y₀ hz
  have hg : Summable (fun m : ℕ => D.C₀ * D.R * (D.M * D.R) ^ m / (Nat.factorial m : ℝ)) :=
    summable_majorant D.C₀ D.M D.R
  have hF : ∀ m : ℕ, DifferentiableOn ℂ
      (fun w => iter A b z₀ Y₀ (m+1) w - iter A b z₀ Y₀ m w) (Metric.ball z D.ρ) := fun m =>
    ((iter_holo hS hSo hA hb hz₀ Y₀ (m+1)).mono (D.hball.trans D.hTS)).sub
      ((iter_holo hS hSo hA hb hz₀ Y₀ m).mono (D.hball.trans D.hTS))
  have hle : ∀ m : ℕ, ∀ w ∈ Metric.ball z D.ρ,
      ‖iter A b z₀ Y₀ (m+1) w - iter A b z₀ Y₀ m w‖
        ≤ D.C₀ * D.R * (D.M * D.R) ^ m / (Nat.factorial m : ℝ) := fun m w hw =>
    le_trans (D.hest m w (D.hball hw))
      (iter_term_le D.hC₀ D.hM D.hR (norm_nonneg _) (D.hRbd w (D.hball hw)) m)
  have htsum := differentiableOn_tsum_of_summable_norm hg hF Metric.isOpen_ball hle
  exact ((htsum.const_add Y₀).differentiableAt (Metric.ball_mem_nhds z D.hρ)).differentiableWithinAt

/-- **The limit of the Picard iterates satisfies the integral equation.** -/
private lemma Ylim_integral_eq {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ} {S : Set ℂ}
    (hS : Convex ℝ S) (hSo : IsOpen S) (hA : DifferentiableOn ℂ A S)
    (hb : DifferentiableOn ℂ b S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) (Y₀ : Fin k → ℂ) {z : ℂ}
    (hz : z ∈ S) :
    Ylim A b z₀ Y₀ z = Y₀ + (z - z₀) •
      ∫ t in (0:ℝ)..1,
        odeField A b (z₀ + t • (z - z₀)) (Ylim A b z₀ Y₀ (z₀ + t • (z - z₀))) := by
  obtain ⟨D⟩ := odeLocalData_exists hS hSo hA hb hz₀ Y₀ hz
  have hAcT : ∀ i j, ContinuousOn (fun w => A w i j) D.T :=
    fun i j => (continuousOn_A_apply hA i j).mono D.hTS
  have hbcT : ∀ i, ContinuousOn (fun w => b w i) D.T :=
    fun i => (continuousOn_b_apply hb i).mono D.hTS
  have hYc : ∀ n, ContinuousOn (fun w => iter A b z₀ Y₀ n w) D.T :=
    fun n => (iter_holo hS hSo hA hb hz₀ Y₀ n).continuousOn.mono D.hTS
  have hint := ode_integral_limit A b z₀ D.hrad hAcT hbcT hYc (fun w hw => iter_tendsto D hw)
    D.hB D.hBiter D.hM D.hAb D.hbB z D.hzT
  have hLHS : Tendsto (fun n => iter A b z₀ Y₀ (n+1) z) atTop (nhds (Ylim A b z₀ Y₀ z)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (iter_tendsto D D.hzT)
  have hstep : (fun n => iter A b z₀ Y₀ (n+1) z) = fun n => Y₀ + (z - z₀) •
      ∫ t in (0:ℝ)..1,
        odeField A b (z₀ + t • (z - z₀)) (iter A b z₀ Y₀ n (z₀ + t • (z - z₀))) := by
    funext n; rw [iter_succ]
  rw [hstep] at hLHS
  have hRHS : Tendsto (fun n => Y₀ + (z - z₀) •
      ∫ t in (0:ℝ)..1,
        odeField A b (z₀ + t • (z - z₀)) (iter A b z₀ Y₀ n (z₀ + t • (z - z₀)))) atTop
      (nhds (Y₀ + (z - z₀) •
        ∫ t in (0:ℝ)..1,
          odeField A b (z₀ + t • (z - z₀)) (Ylim A b z₀ Y₀ (z₀ + t • (z - z₀))))) :=
    (hint.const_smul (z - z₀)).const_add Y₀
  exact tendsto_nhds_unique hLHS hRHS

/-- The limit of the Picard iterates takes the prescribed value at `z₀`. -/
private lemma Ylim_self {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ} {S : Set ℂ}
    (hS : Convex ℝ S) (hSo : IsOpen S) (hA : DifferentiableOn ℂ A S)
    (hb : DifferentiableOn ℂ b S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) (Y₀ : Fin k → ℂ) :
    Ylim A b z₀ Y₀ z₀ = Y₀ := by
  rw [Ylim_integral_eq hS hSo hA hb hz₀ Y₀ hz₀]
  simp

/-- The limit of the Picard iterates satisfies the linear system `Y' = A(z)Y + b(z)`. -/
private lemma Ylim_hasDerivAt {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ} {S : Set ℂ}
    (hS : Convex ℝ S) (hSo : IsOpen S) (hA : DifferentiableOn ℂ A S)
    (hb : DifferentiableOn ℂ b S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) (Y₀ : Fin k → ℂ) {z : ℂ}
    (hz : z ∈ S) :
    HasDerivAt (Ylim A b z₀ Y₀) (fun i => ∑ j, A z i j * Ylim A b z₀ Y₀ z j + b z i) z := by
  have hYholo := Ylim_differentiableOn hS hSo hA hb hz₀ Y₀
  have hfd : DifferentiableOn ℂ (fun w => odeField A b w (Ylim A b z₀ Y₀ w)) S :=
    differentiableOn_odeField hA hb hYholo
  obtain ⟨-, hderiv⟩ := segment_primitive hS hSo hz₀ hfd
  have hP := (hderiv z hz).const_add Y₀
  have heq : Ylim A b z₀ Y₀ =ᶠ[𝓝 z] (fun w => Y₀ + (w - z₀) •
      ∫ t in (0:ℝ)..1,
        odeField A b (z₀ + t • (w - z₀)) (Ylim A b z₀ Y₀ (z₀ + t • (w - z₀)))) := by
    filter_upwards [hSo.mem_nhds hz] with w hw
    exact Ylim_integral_eq hS hSo hA hb hz₀ Y₀ hw
  exact hP.congr_of_eventuallyEq heq

end

theorem linear_ode_convex {k : ℕ} {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S)
    (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (hA : DifferentiableOn ℂ A S) (hb : DifferentiableOn ℂ b S) (z₀ : ℂ) (hz₀ : z₀ ∈ S)
    (Y₀ : Fin k → ℂ) :
    ∃ Y : ℂ → Fin k → ℂ, DifferentiableOn ℂ Y S ∧ Y z₀ = Y₀ ∧
      ∀ z ∈ S, HasDerivAt Y (fun i => ∑ j, A z i j * Y z j + b z i) z := by
  exact ⟨Ylim A b z₀ Y₀, Ylim_differentiableOn hS hSo hA hb hz₀ Y₀,
    Ylim_self hS hSo hA hb hz₀ Y₀, fun z hz => Ylim_hasDerivAt hS hSo hA hb hz₀ Y₀ hz⟩

end Work.C17g
