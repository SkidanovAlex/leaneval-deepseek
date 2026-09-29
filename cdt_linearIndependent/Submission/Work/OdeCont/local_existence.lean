import Mathlib
import Submission.Work.OdeCont.defs
import Submission.Work.OdeCont.primitive_fundamental
import Submission.Work.OdeCont.iter_bound
import Submission.Work.OdeCont.tsum_uniform

noncomputable section
open scoped BigOperators
open scoped Topology
open MeasureTheory Filter Metric

namespace Work.OdeCont

lemma odeField_differentiableOn {k : ℕ} {s : Set ℂ}
    (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (X : ℂ → Fin k → ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s)
    (hb : ∀ i, DifferentiableOn ℂ (fun z => b z i) s)
    (hX : DifferentiableOn ℂ X s) :
    DifferentiableOn ℂ (fun w => odeField A b w (X w)) s := by
  rw [differentiableOn_pi]
  intro i
  have h1 : (fun w => odeField A b w (X w) i) =
      (fun w => (Finset.univ.sum (fun j => A w i j * X w j)) + b w i) := rfl
  rw [h1]
  apply DifferentiableOn.add
  · rw [show (fun w => ∑ j, A w i j * X w j)
        = ∑ j, (fun w => A w i j * X w j) by ext w; simp]
    apply DifferentiableOn.sum
    intro j _
    exact (hA i j).mul ((differentiableOn_pi.mp hX) j)
  · exact hb i

theorem iter_differentiable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : ℂ → V → V) (c z₀ : ℂ) (R : ℝ) (hz₀ : z₀ ∈ Metric.ball c R) (y : V)
    (hF : ∀ X : ℂ → V, DifferentiableOn ℂ X (Metric.ball c R) →
        DifferentiableOn ℂ (fun w => F w (X w)) (Metric.ball c R)) :
    (∀ n, DifferentiableOn ℂ (iter F z₀ y n) (Metric.ball c R)) ∧
      (∀ n z, z ∈ Metric.ball c R →
        HasDerivAt (iter F z₀ y (n+1)) (F z (iter F z₀ y n z)) z) := by
  have step : ∀ n, DifferentiableOn ℂ (iter F z₀ y n) (Metric.ball c R) →
      DifferentiableOn ℂ (iter F z₀ y (n+1)) (Metric.ball c R) ∧
      (∀ z ∈ Metric.ball c R, HasDerivAt (iter F z₀ y (n+1)) (F z (iter F z₀ y n z)) z) := by
    intro n hXn
    have hG : DifferentiableOn ℂ (fun w => F w (iter F z₀ y n w)) (Metric.ball c R) := hF _ hXn
    obtain ⟨g, hgz0, hgderiv⟩ := hG.isExactOn_ball.with_val_at z₀ 0
    have hftc : ∀ z ∈ Metric.ball c R, g z = ∫ t in (0:ℝ)..1,
        (z - z₀) • F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀))) := by
      intro z hz
      have h := primitive_fundamental g (fun w => F w (iter F z₀ y n w)) z₀ z
          (Metric.ball c R) (convex_ball c R) hz₀ hz hgderiv hG.continuousOn
      rw [hgz0, sub_zero] at h
      exact h
    have heq : ∀ z ∈ Metric.ball c R, iter F z₀ y (n+1) z = y + g z := by
      intro z hz
      rw [iter_succ, hftc z hz]
    constructor
    · exact ((differentiableOn_const y).add
        (fun x hx => (hgderiv x hx).differentiableAt.differentiableWithinAt)).congr
          (fun z hz => heq z hz)
    · intro z hz
      have hev : iter F z₀ y (n+1) =ᶠ[𝓝 z] (fun w => y + g w) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
        exact heq w hw
      exact ((hgderiv z hz).const_add y).congr_of_eventuallyEq hev
  have main : ∀ n, DifferentiableOn ℂ (iter F z₀ y n) (Metric.ball c R) := by
    intro n
    induction n with
    | zero =>
      change DifferentiableOn ℂ (fun _ : ℂ => y) (Metric.ball c R)
      exact differentiableOn_const y
    | succ n ih => exact (step n ih).1
  exact ⟨main, fun n z hz => (step n (main n)).2 z hz⟩

lemma exists_bound_data {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (c z₀ : ℂ) (R : ℝ)
    (hAc : ∀ i j, ContinuousOn (fun z => A z i j) (Metric.ball c R))
    (hbc : ∀ i, ContinuousOn (fun z => b z i) (Metric.ball c R))
    (y : Fin k → ℂ) (ρ : ℝ) (hρz : ‖z₀ - c‖ < ρ) (hρR : ρ < R) :
    ∃ K B D : ℝ, 0 ≤ K ∧ 0 ≤ B ∧ 0 ≤ D ∧
      (∀ z ∈ Metric.closedBall c ρ, ‖z - z₀‖ ≤ D) ∧
      (∀ w ∈ Metric.closedBall c ρ, ∀ x x' : Fin k → ℂ,
        ‖odeField A b w x - odeField A b w x'‖ ≤ K * ‖x - x'‖) ∧
      (∀ w ∈ Metric.closedBall c ρ, ‖odeField A b w y‖ ≤ B) := by
  have hKc : IsCompact (Metric.closedBall c ρ) := isCompact_closedBall c ρ
  have hsub : Metric.closedBall c ρ ⊆ Metric.ball c R := Metric.closedBall_subset_ball hρR
  have hz₀S : z₀ ∈ Metric.closedBall c ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_lt hρz
  have hcontA : ContinuousOn (fun w => ∑ i, ∑ j, ‖A w i j‖) (Metric.closedBall c ρ) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((hAc i j).mono hsub).norm
  obtain ⟨CA, hCA⟩ := hKc.exists_bound_of_continuousOn hcontA
  have hCA' : ∀ w ∈ Metric.closedBall c ρ, (∑ i, ∑ j, ‖A w i j‖) ≤ CA := by
    intro w hw
    have hnn : 0 ≤ ∑ i, ∑ j, ‖A w i j‖ :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
    simpa [Real.norm_of_nonneg hnn] using hCA w hw
  have hAle : ∀ w ∈ Metric.closedBall c ρ, ∀ i j, ‖A w i j‖ ≤ CA := by
    intro w hw i j
    have h1 : ‖A w i j‖ ≤ ∑ j', ‖A w i j'‖ :=
      Finset.single_le_sum (fun j' _ => norm_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ j', ‖A w i j'‖) ≤ ∑ i', ∑ j', ‖A w i' j'‖ :=
      Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => norm_nonneg _))
        (Finset.mem_univ i)
    exact h1.trans (h2.trans (hCA' w hw))
  have hCA0 : 0 ≤ CA := (norm_nonneg _).trans (hCA z₀ hz₀S)
  have hcontB : ContinuousOn (fun w => ∑ i, ‖b w i‖) (Metric.closedBall c ρ) := by
    apply continuousOn_finsetSum
    intro i _
    exact ((hbc i).mono hsub).norm
  obtain ⟨CB, hCB⟩ := hKc.exists_bound_of_continuousOn hcontB
  have hCB' : ∀ w ∈ Metric.closedBall c ρ, (∑ i, ‖b w i‖) ≤ CB := by
    intro w hw
    have hnn : 0 ≤ ∑ i, ‖b w i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    simpa [Real.norm_of_nonneg hnn] using hCB w hw
  have hBle : ∀ w ∈ Metric.closedBall c ρ, ∀ i, ‖b w i‖ ≤ CB := by
    intro w hw i
    exact (Finset.single_le_sum (fun i' _ => norm_nonneg _) (Finset.mem_univ i)).trans (hCB' w hw)
  have hCB0 : 0 ≤ CB := (norm_nonneg _).trans (hCB z₀ hz₀S)
  refine ⟨(k : ℝ) * CA, (k : ℝ) * CA * ‖y‖ + CB, ρ + ‖c - z₀‖,
    mul_nonneg (Nat.cast_nonneg k) hCA0,
    add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hCA0) (norm_nonneg y)) hCB0,
    add_nonneg (le_of_lt (lt_of_le_of_lt (norm_nonneg _) hρz)) (norm_nonneg _),
    ?_, ?_, ?_⟩
  · intro z hz
    have h1 : ‖z - z₀‖ ≤ ‖z - c‖ + ‖c - z₀‖ := by
      have h := norm_sub_le (z - c) (z₀ - c)
      rw [show (z - c) - (z₀ - c) = z - z₀ by ring, norm_sub_rev z₀ c] at h
      exact h
    have h2 : ‖z - c‖ ≤ ρ := by
      have := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm] at this
    linarith
  · intro w hw x x'
    have hsubst : odeField A b w x - odeField A b w x' =
        fun i => ∑ j, A w i j * (x j - x' j) := by
      ext i
      simp only [Pi.sub_apply, odeField]
      rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsubst]
    rw [pi_norm_le_iff_of_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hCA0) (norm_nonneg _))]
    intro i
    have hle : (∑ j, ‖A w i j‖ * ‖x j - x' j‖) ≤ (k : ℝ) * (CA * ‖x - x'‖) := by
      calc (∑ j, ‖A w i j‖ * ‖x j - x' j‖)
          ≤ ∑ j, CA * ‖x - x'‖ := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul (hAle w hw i j) (norm_le_pi_norm (x - x') j) (norm_nonneg _) hCA0
        _ = (k : ℝ) * (CA * ‖x - x'‖) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ‖∑ j, A w i j * (x j - x' j)‖
        ≤ ∑ j, ‖A w i j * (x j - x' j)‖ := norm_sum_le _ _
      _ = ∑ j, ‖A w i j‖ * ‖x j - x' j‖ := by simp only [norm_mul]
      _ ≤ (k : ℝ) * (CA * ‖x - x'‖) := hle
      _ = (k : ℝ) * CA * ‖x - x'‖ := by ring
  · intro w hw
    rw [pi_norm_le_iff_of_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hCA0) (norm_nonneg y)) hCB0)]
    intro i
    have hle : (∑ j, ‖A w i j‖ * ‖y j‖) ≤ (k : ℝ) * (CA * ‖y‖) := by
      calc (∑ j, ‖A w i j‖ * ‖y j‖)
          ≤ ∑ j, CA * ‖y‖ := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul (hAle w hw i j) (norm_le_pi_norm y j) (norm_nonneg _) hCA0
        _ = (k : ℝ) * (CA * ‖y‖) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ‖(∑ j, A w i j * y j) + b w i‖
        ≤ ‖∑ j, A w i j * y j‖ + ‖b w i‖ := norm_add_le _ _
      _ ≤ (∑ j, ‖A w i j * y j‖) + CB := add_le_add (norm_sum_le _ _) (hBle w hw i)
      _ = (∑ j, ‖A w i j‖ * ‖y j‖) + CB := by simp only [norm_mul]
      _ ≤ (k : ℝ) * (CA * ‖y‖) + CB := add_le_add hle le_rfl
      _ = (k : ℝ) * CA * ‖y‖ + CB := by ring

theorem local_existence {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (c z₀ : ℂ) (R : ℝ) (hR : 0 < R) (hz₀ : z₀ ∈ Metric.ball c R)
    (hA : ∀ i j : Fin k, DifferentiableOn ℂ (fun z : ℂ => A z i j) (Metric.ball c R))
    (hb : ∀ i : Fin k, DifferentiableOn ℂ (fun z : ℂ => b z i) (Metric.ball c R))
    (y : Fin k → ℂ) :
    ∃ X : ℂ → Fin k → ℂ, DifferentiableOn ℂ X (Metric.ball c R) ∧ X z₀ = y ∧
      ∀ z ∈ Metric.ball c R,
        HasDerivAt X (fun i => (Finset.univ.sum (fun j => A z i j * X z j)) + b z i) z := by
  classical
  let F : ℂ → (Fin k → ℂ) → (Fin k → ℂ) := fun w x => odeField A b w x
  have hF : ∀ X : ℂ → (Fin k → ℂ), DifferentiableOn ℂ X (Metric.ball c R) →
      DifferentiableOn ℂ (fun w => F w (X w)) (Metric.ball c R) := by
    intro X hX
    exact odeField_differentiableOn A b X hA hb hX
  obtain ⟨hXdiff, hXderiv⟩ := iter_differentiable F c z₀ R hz₀ y hF
  have hAc : ∀ i j, ContinuousOn (fun z => A z i j) (Metric.ball c R) :=
    fun i j => (hA i j).continuousOn
  have hbc : ∀ i, ContinuousOn (fun z => b z i) (Metric.ball c R) :=
    fun i => (hb i).continuousOn
  have hz₀norm : ‖z₀ - c‖ < R := by
    have h := hz₀
    rwa [Metric.mem_ball, dist_eq_norm] at h
  have per_rho : ∀ ρ : ℝ, ‖z₀ - c‖ < ρ → ρ < R →
      DifferentiableOn ℂ (iterLimit F z₀ y) (Metric.ball c ρ) ∧
      (∀ z ∈ Metric.ball c ρ, HasDerivAt (iterLimit F z₀ y) (F z (iterLimit F z₀ y z)) z) := by
    intro ρ hρz hρR
    obtain ⟨K, B, D, hK, hB, hD0, hD, hLip, hbase⟩ :=
      exists_bound_data A b c z₀ R hAc hbc y ρ hρz hρR
    have hS : Convex ℝ (Metric.closedBall c ρ) := convex_closedBall c ρ
    have hz₀S : z₀ ∈ Metric.closedBall c ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_of_lt hρz
    have hball_sub : Metric.ball c ρ ⊆ Metric.ball c R := Metric.ball_subset_ball (le_of_lt hρR)
    have hclosed_sub : Metric.closedBall c ρ ⊆ Metric.ball c R := Metric.closedBall_subset_ball hρR
    have hGcont : ∀ n, ContinuousOn (fun w => F w (iter F z₀ y n w)) (Metric.closedBall c ρ) := by
      intro n
      have h : DifferentiableOn ℂ (fun w => F w (iter F z₀ y n w)) (Metric.ball c R) :=
        hF _ (hXdiff n)
      exact h.continuousOn.mono hclosed_sub
    have hbound : ∀ n (z : ℂ), z ∈ Metric.closedBall c ρ →
        ‖iter F z₀ y (n+1) z - iter F z₀ y n z‖ ≤ (D * B) * K ^ n * ‖z - z₀‖ ^ n / (Nat.factorial n : ℝ) :=
      iter_bound F z₀ y (Metric.closedBall c ρ) K B D
        hK hB hD0 hS hz₀S hD hLip hbase hGcont
    have hstep : ∀ n z, z ∈ Metric.closedBall c ρ →
        ‖iter F z₀ y (n+1) z - iter F z₀ y n z‖ ≤ (D * B) * (K * D) ^ n / (Nat.factorial n : ℝ) := by
      intro n z hz
      have hpow : ‖z - z₀‖ ^ n ≤ D ^ n := pow_le_pow_left₀ (norm_nonneg _) (hD z hz) n
      have hmul : (D * B) * K ^ n * ‖z - z₀‖ ^ n ≤ (D * B) * K ^ n * D ^ n :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hD0 hB) (pow_nonneg hK n))
      calc ‖iter F z₀ y (n+1) z - iter F z₀ y n z‖
          ≤ (D * B) * K ^ n * ‖z - z₀‖ ^ n / (Nat.factorial n : ℝ) := hbound n z hz
        _ = ((D * B) * K ^ n * ‖z - z₀‖ ^ n) / (Nat.factorial n : ℝ) := by rw [mul_div_assoc]
        _ ≤ ((D * B) * K ^ n * D ^ n) / (Nat.factorial n : ℝ) := div_le_div_of_nonneg_right hmul (Nat.cast_nonneg _)
        _ = (D * B) * (K * D) ^ n / (Nat.factorial n : ℝ) := by rw [mul_pow]; ring
    have htu : TendstoUniformlyOn (iter F z₀ y) (iterLimit F z₀ y) atTop (Metric.closedBall c ρ) :=
      tsum_uniform (iter F z₀ y) (Metric.closedBall c ρ) (D * B) (K * D)
          (mul_nonneg hD0 hB) (mul_nonneg hK hD0) hstep
    have htuU : TendstoUniformlyOn (iter F z₀ y) (iterLimit F z₀ y) atTop (Metric.ball c ρ) :=
      htu.mono Metric.ball_subset_closedBall
    have hdiffU : DifferentiableOn ℂ (iterLimit F z₀ y) (Metric.ball c ρ) :=
      htuU.tendstoLocallyUniformlyOn.differentiableOn
        (Eventually.of_forall (fun n => (hXdiff n).mono hball_sub)) Metric.isOpen_ball
    refine ⟨hdiffU, ?_⟩
    intro z hz
    have hzR : z ∈ Metric.ball c R := hball_sub hz
    have hzS : z ∈ Metric.closedBall c ρ := Metric.ball_subset_closedBall hz
    -- series machinery
    have hu : Summable (fun n : ℕ => (D * B) * (K * D) ^ n / (Nat.factorial n : ℝ)) := by
      have h := (Real.summable_pow_div_factorial (K * D)).mul_left (D * B)
      simpa [mul_div_assoc] using h
    have hδdiff : ∀ n, DifferentiableOn ℂ
        (fun w => iter F z₀ y (n+1) w - iter F z₀ y n w) (Metric.ball c ρ) := by
      intro n
      exact ((hXdiff (n+1)).mono hball_sub).sub ((hXdiff n).mono hball_sub)
    have hfle : ∀ n (w : ℂ), w ∈ Metric.ball c ρ →
        ‖iter F z₀ y (n+1) w - iter F z₀ y n w‖ ≤ (D * B) * (K * D) ^ n / (Nat.factorial n : ℝ) :=
      fun n w hw => hstep n w (Metric.ball_subset_closedBall hw)
    have hHasSum := Complex.hasSum_deriv_of_summable_norm
        (u := fun n : ℕ => (D * B) * (K * D) ^ n / (Nat.factorial n : ℝ))
        (F := fun n w => iter F z₀ y (n+1) w - iter F z₀ y n w)
        hu hδdiff Metric.isOpen_ball hfle hz
    -- telescoping
    have hterm : ∀ n, deriv (fun w => iter F z₀ y (n+1) w - iter F z₀ y n w) z
        = Hz F z₀ y z (n+1) - Hz F z₀ y z n := by
      intro n
      cases n with
      | zero =>
        have hd : HasDerivAt (fun w => iter F z₀ y (0+1) w - iter F z₀ y 0 w)
            (F z (iter F z₀ y 0 z) - 0) z :=
          (hXderiv 0 z hzR).sub (hasDerivAt_const z (iter F z₀ y 0 z))
        rw [hd.deriv]
        simp
      | succ k =>
        have hd : HasDerivAt (fun w => iter F z₀ y (k+1+1) w - iter F z₀ y (k+1) w)
            (F z (iter F z₀ y (k+1) z) - F z (iter F z₀ y k z)) z :=
          (hXderiv (k+1) z hzR).sub (hXderiv k z hzR)
        rw [hd.deriv]
        simp
    have hps : ∀ N, (∑ n ∈ Finset.range N,
          deriv (fun w => iter F z₀ y (n+1) w - iter F z₀ y n w) z) = Hz F z₀ y z N := by
      intro N
      rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_range_sub]
      simp
    have hHzTendsto : Tendsto (Hz F z₀ y z) atTop (𝓝 (F z (iterLimit F z₀ y z))) := by
      have hconv : Tendsto (fun n => iter F z₀ y n z) atTop (𝓝 (iterLimit F z₀ y z)) :=
        htu.tendsto_at hzS
      have hFx : Tendsto (fun m => F z (iter F z₀ y m z)) atTop (𝓝 (F z (iterLimit F z₀ y z))) := by
        rw [Metric.tendsto_atTop] at hconv ⊢
        intro ε hε
        obtain ⟨N, hN⟩ := hconv (ε / (K + 1)) (by positivity)
        refine ⟨N, fun n hn => ?_⟩
        have h1 := hLip z hzS (iter F z₀ y n z) (iterLimit F z₀ y z)
        have h2 : ‖iter F z₀ y n z - iterLimit F z₀ y z‖ < ε / (K + 1) := by
          have := hN n hn
          rwa [dist_eq_norm] at this
        rw [dist_eq_norm]
        calc ‖F z (iter F z₀ y n z) - F z (iterLimit F z₀ y z)‖
            ≤ K * ‖iter F z₀ y n z - iterLimit F z₀ y z‖ := h1
          _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (le_of_lt h2) hK
          _ < ε := by
              have hK1 : (0:ℝ) < K + 1 := by linarith
              have hlt : K / (K + 1) < 1 := by
                rw [div_lt_one hK1]; linarith
              calc K * (ε / (K + 1)) = (K / (K + 1)) * ε := by ring
                _ < 1 * ε := mul_lt_mul_of_pos_right hlt hε
                _ = ε := one_mul ε
      have hpred : Tendsto (fun m : ℕ => m - 1) atTop atTop := by
        rw [Filter.tendsto_atTop]
        intro a
        filter_upwards [eventually_ge_atTop (a + 1)] with m hm
        omega
      have hshift : Tendsto (fun m => F z (iter F z₀ y (m - 1) z)) atTop
          (𝓝 (F z (iterLimit F z₀ y z))) := hFx.comp hpred
      have hev : (Hz F z₀ y z) =ᶠ[atTop] (fun m => F z (iter F z₀ y (m - 1) z)) := by
        filter_upwards [eventually_ge_atTop 1] with m hm
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        simp
      exact Tendsto.congr' hev.symm hshift
    have hpsT : Tendsto (fun N => ∑ n ∈ Finset.range N,
          deriv (fun w => iter F z₀ y (n+1) w - iter F z₀ y n w) z)
        atTop (𝓝 (F z (iterLimit F z₀ y z))) := by
      rw [show (fun N => ∑ n ∈ Finset.range N,
            deriv (fun w => iter F z₀ y (n+1) w - iter F z₀ y n w) z) = Hz F z₀ y z
          from funext hps]
      exact hHzTendsto
    have hderiv_eq : deriv (fun w => ∑' n, (iter F z₀ y (n+1) w - iter F z₀ y n w)) z
        = F z (iterLimit F z₀ y z) :=
      tendsto_nhds_unique hHasSum.tendsto_sum_nat hpsT
    have hderiv_lim : deriv (iterLimit F z₀ y) z
        = deriv (fun w => ∑' n, (iter F z₀ y (n+1) w - iter F z₀ y n w)) z := by
      rw [show iterLimit F z₀ y = fun w => y + ∑' n,
            (iter F z₀ y (n+1) w - iter F z₀ y n w) from by
        ext w; rw [iterLimit_apply]; simp]
      exact deriv_const_add y
    have hfinal : deriv (iterLimit F z₀ y) z = F z (iterLimit F z₀ y z) := by
      rw [hderiv_lim, hderiv_eq]
    rw [← hfinal]
    exact (hdiffU.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
  refine ⟨iterLimit F z₀ y, ?_, ?_, ?_⟩
  · intro z hz
    have hzR : z ∈ Metric.ball c R := hz
    have hzc : ‖z - c‖ < R := by
      have h := hz
      rwa [Metric.mem_ball, dist_eq_norm] at h
    have hmax : max ‖z₀ - c‖ ‖z - c‖ < R := max_lt hz₀norm hzc
    set ρ : ℝ := (max ‖z₀ - c‖ ‖z - c‖ + R) / 2 with hρdef
    have hρR : ρ < R := by rw [hρdef]; linarith
    have hρz0 : ‖z₀ - c‖ < ρ := by
      rw [hρdef]; linarith [le_max_left ‖z₀ - c‖ ‖z - c‖]
    have hρz : ‖z - c‖ < ρ := by
      rw [hρdef]; linarith [le_max_right ‖z₀ - c‖ ‖z - c‖]
    have hzρ : z ∈ Metric.ball c ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hρz
    exact ((per_rho ρ hρz0 hρR).1.differentiableAt
      (Metric.isOpen_ball.mem_nhds hzρ)).differentiableWithinAt
  · have hiter_z₀ : ∀ n, iter F z₀ y n z₀ = y := by
      intro n
      induction n with
      | zero => rfl
      | succ k ih => rw [iter_succ]; simp
    rw [iterLimit_apply, hiter_z₀ 0]
    have hzero : (fun n => iter F z₀ y (n+1) z₀ - iter F z₀ y n z₀)
        = fun _ => (0 : Fin k → ℂ) := by
      funext n; rw [hiter_z₀ (n+1), hiter_z₀ n, sub_self]
    rw [hzero, tsum_zero, add_zero]
  · intro z hz
    have hzc : ‖z - c‖ < R := by
      have h := hz
      rwa [Metric.mem_ball, dist_eq_norm] at h
    have hmax : max ‖z₀ - c‖ ‖z - c‖ < R := max_lt hz₀norm hzc
    set ρ : ℝ := (max ‖z₀ - c‖ ‖z - c‖ + R) / 2 with hρdef
    have hρR : ρ < R := by rw [hρdef]; linarith
    have hρz0 : ‖z₀ - c‖ < ρ := by
      rw [hρdef]; linarith [le_max_left ‖z₀ - c‖ ‖z - c‖]
    have hρz : ‖z - c‖ < ρ := by
      rw [hρdef]; linarith [le_max_right ‖z₀ - c‖ ‖z - c‖]
    have hzρ : z ∈ Metric.ball c ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hρz
    exact (per_rho ρ hρz0 hρR).2 z hzρ


end Work.OdeCont
