import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.czAux

namespace Work.CR.Flat.Cauchy.bmCz

open MeasureTheory Set Pointwise Filter
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

lemma eucNorm_smul_nonneg {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (x : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.eucNorm (c • x) = c * Work.CR.Flat.Cauchy.eucNorm x := by
  rw [Work.CR.Flat.Cauchy.eucNorm, Work.CR.Flat.Cauchy.eucNorm]
  have h1 : (∑ j, ‖(c • x) j‖ ^ 2) = c^2 * ∑ j, ‖x j‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc]
    ring
  rw [h1, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

lemma finrank_pi_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, Finset.sum_const]
  ring

lemma volume_eucBall_eq {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Fin n → ℂ)) (Work.CR.Flat.Cauchy.eucBall r)
      = ENNReal.ofReal (r ^ (2 * n)) * (volume : Measure (Fin n → ℂ)) (Work.CR.Flat.Cauchy.eucBall 1) := by
  have hset : Work.CR.Flat.Cauchy.eucBall (n := n) r = r • Work.CR.Flat.Cauchy.eucBall (n := n) 1 := by
    ext x
    simp only [Work.CR.Flat.Cauchy.mem_eucBall, Set.mem_smul_set]
    constructor
    · intro hx
      refine ⟨r⁻¹ • x, ?_, ?_⟩
      · rw [eucNorm_smul_nonneg (inv_nonneg.mpr hr.le)]
        rw [show r⁻¹ * Work.CR.Flat.Cauchy.eucNorm x = Work.CR.Flat.Cauchy.eucNorm x / r from by
          rw [div_eq_mul_inv, mul_comm]]
        rw [div_lt_one hr]; exact hx
      · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    · rintro ⟨y, hy, rfl⟩
      rw [eucNorm_smul_nonneg hr.le]; nlinarith [hr, hy]
  rw [hset, MeasureTheory.Measure.addHaar_smul, finrank_pi_complex,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ (2*n))]

lemma volume_real_eucBall_eq {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Fin n → ℂ)).real (Work.CR.Flat.Cauchy.eucBall r)
      = r ^ (2 * n) * (volume : Measure (Fin n → ℂ)).real (Work.CR.Flat.Cauchy.eucBall 1) := by
  have h := volume_eucBall_eq (n := n) hr
  have hfin : (volume : Measure (Fin n → ℂ)) (Work.CR.Flat.Cauchy.eucBall 1) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (Work.CR.Flat.Cauchy.eucBall_subset_ball (R:=1)))
      (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure (Fin n → ℂ)))))
  rw [MeasureTheory.Measure.real_def, h, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), MeasureTheory.Measure.real_def]

lemma volume_real_eucShell_le {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (volume : Measure (Fin n → ℂ)).real (Work.CR.Flat.Cauchy.eucShell a b)
      ≤ (2 * (n : ℝ)) * b ^ (2 * n - 1) * (b - a)
          * (volume : Measure (Fin n → ℂ)).real (Work.CR.Flat.Cauchy.eucBall 1) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsub : Work.CR.Flat.Cauchy.eucBall (n := n) a ⊆ Work.CR.Flat.Cauchy.eucBall (n := n) b :=
    fun x hx => lt_of_lt_of_le hx hab
  have hset : Work.CR.Flat.Cauchy.eucShell (n := n) a b
      = Work.CR.Flat.Cauchy.eucBall (n := n) b \ Work.CR.Flat.Cauchy.eucBall (n := n) a :=
    Work.CR.Flat.Cauchy.eucShell_eq_eucBall_diff
  have hbne : (volume : Measure (Fin n → ℂ)) (Work.CR.Flat.Cauchy.eucBall (n := n) b) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (Work.CR.Flat.Cauchy.eucBall_subset_ball (R:=b)))
      (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure (Fin n → ℂ)))))
  rw [hset, MeasureTheory.measureReal_sdiff hsub (Work.CR.Flat.Cauchy.measurableSet_eucBall a) hbne,
    volume_real_eucBall_eq hb, volume_real_eucBall_eq ha]
  have hpow : b ^ (2 * n) - a ^ (2 * n) ≤ (2 * (n:ℝ)) * b ^ (2*n-1) * (b - a) := by
    have h1 := abs_pow_sub_pow_le b a (2 * n)
    rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha.le hab _)), abs_of_nonneg (sub_nonneg.mpr hab),
      abs_of_nonneg (le_of_lt hb), abs_of_nonneg ha.le, max_eq_left hab] at h1
    rw [Nat.cast_mul] at h1
    calc b ^ (2*n) - a ^ (2*n) ≤ (b - a) * (2 * (n:ℝ)) * b ^ (2*n-1) := h1
      _ = (2 * (n:ℝ)) * b ^ (2*n-1) * (b-a) := by ring
  have hcoef : 0 ≤ (volume : Measure (Fin n → ℂ)).real (Work.CR.Flat.Cauchy.eucBall 1) :=
    MeasureTheory.measureReal_nonneg
  nlinarith [hpow, hcoef]

lemma norm_setIntegral_le_integral_norm {n : ℕ} (s : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ) :
    ‖∫ x in s, F x‖ ≤ ∫ x in s, ‖F x‖ := by
  simpa using MeasureTheory.norm_integral_le_integral_norm F (μ := (volume.restrict s))

lemma rpow_inv_natpow {x : ℝ} (hx : 0 < x) (k : ℕ) : (x ^ k)⁻¹ = x ^ (-(k:ℝ)) := by
  rw [← Real.rpow_natCast x k, Real.rpow_neg hx.le]

lemma eucNorm_add_le {n : ℕ} (x y : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.eucNorm (x + y)
      ≤ Work.CR.Flat.Cauchy.eucNorm x + Work.CR.Flat.Cauchy.eucNorm y := by
  have h := Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le (x + y) y
  rw [add_sub_cancel_right] at h
  have h2 := (abs_le.mp h).2
  linarith

lemma rpow_add_one_neg {x : ℝ} (hx : 0 < x) (a : ℝ) : x ^ (a - 1) = x ^ a * x ^ (-1 : ℝ) := by
  rw [sub_eq_add_neg, Real.rpow_add hx a (-1 : ℝ)]

lemma rpow_mul_rpow {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ y * x ^ z = x ^ (y + z) :=
  (Real.rpow_add hx y z).symm

lemma rpow_div_natpow {x : ℝ} (hx : 0 < x) (a : ℝ) (k : ℕ) :
    x ^ a / x ^ k = x ^ (a - (k:ℝ)) := by
  rw [div_eq_mul_inv, ← Real.rpow_natCast x k, ← Real.rpow_neg hx.le,
    ← Real.rpow_add hx, show a + -(k:ℝ) = a - (k:ℝ) from by ring]

lemma volume_real_eucBall_one_pos {n : ℕ} (hn : 0 < n) :
    0 < (volume : Measure (Fin n → ℂ)).real (Work.CR.Flat.Cauchy.eucBall 1) := by
  rw [MeasureTheory.Measure.real_def]
  refine ENNReal.toReal_pos ?_ ?_
  · have hsq : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hr : 0 < 1/(Real.sqrt (n:ℝ) + 1) := by positivity
    have hsub : Metric.ball (0:Fin n → ℂ) (1/(Real.sqrt (n:ℝ)+1))
        ⊆ Work.CR.Flat.Cauchy.eucBall (n:=n) 1 := by
      intro x hx
      rw [Metric.mem_ball, dist_zero_right] at hx
      rw [Work.CR.Flat.Cauchy.mem_eucBall]
      calc Work.CR.Flat.Cauchy.eucNorm x ≤ Real.sqrt (n:ℝ) * ‖x‖ :=
            Work.CR.Flat.Cauchy.bmCz.eucNorm_le_sqrt_mul_norm x
        _ < Real.sqrt (n:ℝ) * (1/(Real.sqrt (n:ℝ)+1)) := mul_lt_mul_of_pos_left hx hsq
        _ < 1 := by
            rw [mul_one_div, div_lt_one (by positivity)]
            linarith
    exact ne_of_gt (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 hr)
      (MeasureTheory.measure_mono hsub))
  · exact ne_of_lt (lt_of_le_of_lt
      (MeasureTheory.measure_mono (Work.CR.Flat.Cauchy.eucBall_subset_ball (R:=1)))
      (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure (Fin n → ℂ)))))

end Work.CR.Flat.Cauchy.bmCz

namespace Work.CR.Flat.Cauchy.bmCz

open MeasureTheory Set Pointwise Filter
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

theorem czDifferenceEstimate {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R) {Φ : (Fin n → ℂ) → ℂ}
    (hΦm : MeasureTheory.AEStronglyMeasurable Φ MeasureTheory.volume)
    {A : ℝ} (hA : 0 < A)
    (hP1 : ∀ x : Fin n → ℂ, x ≠ 0 →
      ‖Φ x‖ ≤ A / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n))
    (hP2 : ∀ x h : Fin n → ℂ,
      2 * Work.CR.Flat.Cauchy.eucNorm h ≤ Work.CR.Flat.Cauchy.eucNorm x →
      ‖Φ (x - h) - Φ x‖ ≤ A * Work.CR.Flat.Cauchy.eucNorm h
        / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n + 1))
    (hH2 : ∀ a b : ℝ, 0 < a → a < b →
      ∫ x in Work.CR.Flat.Cauchy.eucShell a b, Φ x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K → ∀ g : (Fin n → ℂ) → ℂ,
      (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      ∀ z z' : Fin n → ℂ,
        ‖(∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R), Φ x * (g (z + x) - g z))
            - (∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R),
                Φ x * (g (z' + x) - g z'))‖
          ≤ C * K * ‖z - z'‖ ^ α := by
  obtain ⟨Crad, hCradpos, hCrad⟩ := eucRadialBound hn (α - 2*(n:ℝ)) (by linarith)
  obtain ⟨Csh, hCshpos, hCsh⟩ := Work.CR.Flat.Cauchy.eucShell_integral_le_neg (n:=n) hn
      (s := α - 2*(n:ℝ) - 1) (by linarith)
  set V : ℝ := (volume : Measure (Fin n → ℂ)).real (Work.CR.Flat.Cauchy.eucBall (n:=n) 1) with hV
  have hVpos : 0 < V := volume_real_eucBall_one_pos hn
  set Bet : ℝ := max 1 ((2*R) ^ (1-α)) with hBet
  have hBetpos : 0 < Bet := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBet1 : 1 ≤ Bet := le_max_left _ _
  have h2Rpos : 0 < 2*R := by linarith
  set NearC : ℝ := 2*A*Crad*2^α with hNearC
  set T1 : ℝ := A*Csh*2^(α-1) with hT1
  set T2 : ℝ := (3/2)*A*Crad*3^α with hT2
  set T3 : ℝ := (3/2)*A*(2*R)^(α-2*(n:ℝ))*(2*(n:ℝ))*(4*R)^(2*n-1)*V*Bet with hT3
  set T4 : ℝ := A*V*2^α with hT4
  set T5 : ℝ := (3/2)*A*(4*R)^(α-2*(n:ℝ))*(2*(n:ℝ))*(6*R)^(2*n-1)*V*Bet with hT5
  have hNearCpos : 0 < NearC := by
    rw [hNearC]; have : (0:ℝ) < 2^α := Real.rpow_pos_of_pos (by norm_num) α
    positivity
  have hT1pos : 0 < T1 := by
    rw [hT1]; have : (0:ℝ) < 2^(α-1) := Real.rpow_pos_of_pos (by norm_num) (α-1); positivity
  have hT2pos : 0 < T2 := by
    rw [hT2]; have : (0:ℝ) < 3^α := Real.rpow_pos_of_pos (by norm_num) α; positivity
  have hT3pos : 0 < T3 := by
    rw [hT3]
    have h1 : (0:ℝ) < (2*R)^(α-2*(n:ℝ)) := Real.rpow_pos_of_pos h2Rpos _
    have h2 : (0:ℝ) < (4*R)^(2*n-1) := by positivity
    have h3 : (0:ℝ) < (2*(n:ℝ)) := by positivity
    positivity
  have hT4pos : 0 < T4 := by
    rw [hT4]; have : (0:ℝ) < 2^α := Real.rpow_pos_of_pos (by norm_num) α; positivity
  have hT5pos : 0 < T5 := by
    rw [hT5]
    have h1 : (0:ℝ) < (4*R)^(α-2*(n:ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have h2 : (0:ℝ) < (6*R)^(2*n-1) := by positivity
    have h3 : (0:ℝ) < (2*(n:ℝ)) := by positivity
    positivity
  set FarC : ℝ := T1+T2+T3+T4+T5 with hFarC
  have hFarCpos : 0 < FarC := by rw [hFarC]; positivity
  set BigC : ℝ := NearC + FarC with hBigC
  have hBigCpos : 0 < BigC := by rw [hBigC]; positivity
  have hsqpos : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  refine ⟨(Real.sqrt (n:ℝ))^α * BigC, by positivity, ?_⟩
  intro K hK g hg z z'
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x0
    show Tendsto g (𝓝 x0) (𝓝 (g x0))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => hg y x0) ?_
    have h1 : Continuous (fun y : Fin n → ℂ => K * ‖y - x0‖ ^ α) :=
      ((continuous_norm.comp (continuous_id.sub continuous_const)).rpow_const
        (fun _ => Or.inr hα.le)).const_mul K
    have h2 : (fun y : Fin n → ℂ => K * ‖y - x0‖ ^ α) x0 = 0 := by
      simp [Real.zero_rpow hα.ne']
    rw [← h2]; exact h1.continuousAt
  by_cases hzz : z = z'
  · subst hzz
    simp only [sub_self, norm_zero]
    rw [Real.zero_rpow hα.ne']
    simp
  have he_ne : z' - z ≠ 0 := by
    intro h; exact hzz (sub_eq_zero.mp h).symm
  set e : Fin n → ℂ := z' - z with he
  have he_ne' : e ≠ 0 := by rw [he]; exact he_ne
  set ρ : ℝ := Work.CR.Flat.Cauchy.eucNorm e with hρ
  have hρpos : 0 < ρ := by rw [hρ]; exact Work.CR.Flat.Cauchy.eucNorm_pos he_ne'
  have hz'e : z + e = z' := by rw [he]; abel
  have hH2' : ∀ a b : ℝ, 0 < a → a ≤ b → ∫ x in Work.CR.Flat.Cauchy.eucShell (n:=n) a b, Φ x = 0 := by
    intro a b ha hab
    rcases lt_or_eq_of_le hab with h | h
    · exact hH2 a b ha h
    · subst h
      have hempty : Work.CR.Flat.Cauchy.eucShell (n:=n) a a = ∅ := by
        ext x; simp only [Work.CR.Flat.Cauchy.mem_eucShell, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2; linarith
      rw [hempty]; simp
  set Ψ : (Fin n → ℂ) → ℂ := fun x => (g (z + x) - g z) - (g (z' + x) - g z') with hΨ
  set G : (Fin n → ℂ) → ℂ := fun y => g (z + y) - g z with hG
  set B : Set (Fin n → ℂ) := Work.CR.Flat.Cauchy.eucBall (n:=n) (4*R) with hB
  set N : Set (Fin n → ℂ) := Work.CR.Flat.Cauchy.eucBall (n:=n) (min (2*ρ) (4*R)) with hN
  set S : Set (Fin n → ℂ) := Work.CR.Flat.Cauchy.eucShell (n:=n) (2*ρ) (4*R) with hS
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hzpow : α - 2*(n:ℝ) ≠ 0 := by
    intro h; linarith
  -- integrability
  have hPt : ∀ x, ‖Φ x * Ψ x‖ ≤ 2*A*K * Work.CR.Flat.Cauchy.eucNorm x ^ (α - 2*(n:ℝ)) := by
    intro x
    have hzpow : α - 2*(n:ℝ) ≠ 0 := by
      have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      intro h; linarith
    by_cases hx : x = 0
    · subst hx
      simp [hΨ, Work.CR.Flat.Cauchy.eucNorm_zero, Real.zero_rpow hzpow]
    · have hxpos : 0 < Work.CR.Flat.Cauchy.eucNorm x := Work.CR.Flat.Cauchy.eucNorm_pos hx
      have hΨb : ‖Ψ x‖ ≤ 2*K*Work.CR.Flat.Cauchy.eucNorm x ^ α := by
        have h1 : ‖g (z+x) - g z‖ ≤ K * ‖x‖ ^ α := by
          have := hg (z+x) z; simpa using this
        have h2 : ‖g (z'+x) - g z'‖ ≤ K * ‖x‖ ^ α := by
          have := hg (z'+x) z'; simpa using this
        have h3 : ‖Ψ x‖ ≤ ‖g (z+x) - g z‖ + ‖g (z'+x) - g z'‖ := by
          simp only [hΨ]; exact norm_sub_le _ _
        have h4 : ‖x‖ ^ α ≤ Work.CR.Flat.Cauchy.eucNorm x ^ α :=
          Real.rpow_le_rpow (norm_nonneg x) (Work.CR.Flat.Cauchy.pi_norm_le_eucNorm x) hα.le
        calc ‖Ψ x‖ ≤ ‖g (z+x)-g z‖ + ‖g (z'+x)-g z'‖ := h3
          _ ≤ K*‖x‖^α + K*‖x‖^α := add_le_add h1 h2
          _ = 2*K*‖x‖^α := by ring
          _ ≤ 2*K*Work.CR.Flat.Cauchy.eucNorm x ^ α := by
              apply mul_le_mul_of_nonneg_left h4 (by positivity)
      calc ‖Φ x * Ψ x‖ = ‖Φ x‖ * ‖Ψ x‖ := norm_mul _ _
        _ ≤ (A / (Work.CR.Flat.Cauchy.eucNorm x)^(2*n)) * (2*K*Work.CR.Flat.Cauchy.eucNorm x ^ α) :=
            mul_le_mul (hP1 x hx) hΨb (norm_nonneg _) (div_nonneg hA.le (by positivity))
        _ = 2*A*K * (Work.CR.Flat.Cauchy.eucNorm x ^ α / (Work.CR.Flat.Cauchy.eucNorm x)^(2*n)) := by ring
        _ = 2*A*K * Work.CR.Flat.Cauchy.eucNorm x ^ (α - 2*(n:ℝ)) := by
            rw [rpow_div_natpow hxpos α (2*n),
              show ((2*n:ℕ):ℝ) = 2*(n:ℝ) from by push_cast; ring]
  have hIntB : IntegrableOn (fun x => Φ x * Ψ x) B volume := by
    have hmaj : IntegrableOn (fun x => 2*A*K * Work.CR.Flat.Cauchy.eucNorm x ^ (α - 2*(n:ℝ))) B volume :=
      MeasureTheory.Integrable.const_mul (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_ball hn (by linarith) (4*R)) _
    refine hmaj.mono' ?_ ?_
    · refine (hΦm.mono_measure Measure.restrict_le_self).mul ?_
      simp only [hΨ]
      refine AEStronglyMeasurable.sub ?_ ?_
      · exact (hgcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable.sub aestronglyMeasurable_const
      · exact (hgcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable.sub aestronglyMeasurable_const
    · filter_upwards with x using hPt x
  have hIntN : IntegrableOn (fun x => Φ x * Ψ x) N volume :=
    hIntB.mono_set (by
      rw [hB, hN]; intro x hx
      simp only [Work.CR.Flat.Cauchy.mem_eucBall] at hx ⊢
      exact lt_of_lt_of_le hx (min_le_right _ _))
  have hIntS : IntegrableOn (fun x => Φ x * Ψ x) S volume :=
    hIntB.mono_set (by
      rw [hB, hS]; intro x hx
      simp only [Work.CR.Flat.Cauchy.mem_eucBall, Work.CR.Flat.Cauchy.mem_eucShell] at hx ⊢
      exact hx.2)
  -- near bound
  have hNear : ‖∫ x in N, Φ x * Ψ x‖ ≤ NearC * K * ρ^α := by
    have hIntN2 : IntegrableOn (fun x => 2*A*K * Work.CR.Flat.Cauchy.eucNorm x ^ (α - 2*(n:ℝ))) N volume :=
      MeasureTheory.Integrable.const_mul (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_ball hn (by linarith) (min (2*ρ) (4*R))) _
    have hIntNn : IntegrableOn (fun x => ‖Φ x * Ψ x‖) N volume :=
      MeasureTheory.Integrable.norm hIntN
    calc ‖∫ x in N, Φ x * Ψ x‖ ≤ ∫ x in N, ‖Φ x * Ψ x‖ := norm_setIntegral_le_integral_norm N _
      _ ≤ ∫ x in N, 2*A*K * Work.CR.Flat.Cauchy.eucNorm x ^ (α - 2*(n:ℝ)) :=
          MeasureTheory.setIntegral_mono_on hIntNn hIntN2 (Work.CR.Flat.Cauchy.measurableSet_eucBall _)
            (fun x _ => hPt x)
      _ = 2*A*K * ∫ x in N, Work.CR.Flat.Cauchy.eucNorm x ^ (α - 2*(n:ℝ)) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ 2*A*K * ∫ x in Work.CR.Flat.Cauchy.eucBall (n:=n) (2*ρ),
            Work.CR.Flat.Cauchy.eucNorm x ^ (α - 2*(n:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine MeasureTheory.setIntegral_mono_set
            (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_ball hn (by linarith) (2*ρ))
            (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (Work.CR.Flat.Cauchy.eucNorm_nonneg x) _))
            (Filter.Eventually.of_forall (fun x hx => ?_))
          rw [hN] at hx
          simp only [Work.CR.Flat.Cauchy.mem_eucBall] at hx
          exact lt_of_lt_of_le hx (min_le_left _ _)
      _ ≤ 2*A*K * (Crad * (2*ρ)^α) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := hCrad (2*ρ) (by positivity)
          rwa [show α - 2*(n:ℝ) + 2*(n:ℝ) = α from by ring] at this
      _ = NearC * K * ρ^α := by
          rw [hNearC, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hρpos.le]; ring
  have hFar : ‖∫ x in S, Φ x * Ψ x‖ ≤ FarC * K * ρ^α := by
    rcases le_or_gt (2*ρ) (4*R) with hcase | hcase
    · have h2ρpos : 0 < 2*ρ := by linarith
      have hSmeas : MeasurableSet S := by
        rw [hS]; exact Work.CR.Flat.Cauchy.measurableSet_eucShell _ _
      have hSfin : volume S < ∞ := by
        rw [hS]
        exact Work.CR.Flat.Cauchy.volume_lt_top_of_subset_eucNorm (M := 4*R)
          (fun x hx => le_of_lt hx.2)
      set c0 : ℂ := g z' - g z with hc0
      set Se : Set (Fin n → ℂ) := (fun x => x + e) '' S with hSe
      have hSe_pre : (fun x : Fin n → ℂ => x + e) '' S = (fun u : Fin n → ℂ => u - e) ⁻¹' S := by
        ext u; simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩; simpa using hx
        · intro hu; exact ⟨u - e, hu, by abel⟩
      have hSe_meas : MeasurableSet Se := by
        rw [hSe, hSe_pre]
        exact hSmeas.preimage (continuous_id.sub continuous_const).measurable
      have hSe_mem : ∀ u : Fin n → ℂ, u ∈ Se ↔ u - e ∈ S := by
        intro u; rw [hSe, hSe_pre]; exact Iff.rfl
      have hSe_lt : ∀ u ∈ Se, Work.CR.Flat.Cauchy.eucNorm (u - e) < 4*R := by
        intro u hu; exact (Work.CR.Flat.Cauchy.mem_eucShell.mp ((hSe_mem u).mp hu)).2
      have hSe_ge : ∀ u ∈ Se, 2*ρ ≤ Work.CR.Flat.Cauchy.eucNorm (u - e) := by
        intro u hu; exact (Work.CR.Flat.Cauchy.mem_eucShell.mp ((hSe_mem u).mp hu)).1
      have hS_ge : ∀ x ∈ S, 2*ρ ≤ Work.CR.Flat.Cauchy.eucNorm x := by
        intro x hx; exact (Work.CR.Flat.Cauchy.mem_eucShell.mp (by rwa [hS] at hx)).1
      have hS_lt : ∀ x ∈ S, Work.CR.Flat.Cauchy.eucNorm x < 4*R := by
        intro x hx; exact (Work.CR.Flat.Cauchy.mem_eucShell.mp (by rwa [hS] at hx)).2
      have hSefin : volume Se < ∞ := by
        refine lt_of_le_of_lt (MeasureTheory.measure_mono ?_)
          (Work.CR.Flat.Cauchy.volume_lt_top_of_subset_eucNorm
            (s := Work.CR.Flat.Cauchy.eucBall (n:=n) (4*R+ρ)) (M := 4*R+ρ)
            (fun y hy => le_of_lt hy))
        intro u hu
        rw [Work.CR.Flat.Cauchy.mem_eucBall]
        calc Work.CR.Flat.Cauchy.eucNorm u = Work.CR.Flat.Cauchy.eucNorm ((u-e)+e) := by rw [sub_add_cancel]
          _ ≤ Work.CR.Flat.Cauchy.eucNorm (u-e) + Work.CR.Flat.Cauchy.eucNorm e := eucNorm_add_le _ _
          _ < 4*R + ρ := by rw [hρ]; linarith [hSe_lt u hu]
      have hSdom : ∀ s : ℝ, IntegrableOn (fun x => Work.CR.Flat.Cauchy.eucNorm x ^ s) S volume := by
        intro s; rw [hS]
        exact Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_shell (n:=n) (s:=s) h2ρpos hcase
      have hIntS_of : ∀ (F : (Fin n → ℂ)→ℂ) (s C : ℝ), AEStronglyMeasurable F (volume.restrict S) →
          (∀ x ∈ S, ‖F x‖ ≤ C * Work.CR.Flat.Cauchy.eucNorm x ^ s) → IntegrableOn F S volume := by
        intro F s C hm hb
        refine MeasureTheory.Integrable.mono' ((hSdom s).const_mul C) hm ?_
        exact (MeasureTheory.ae_restrict_iff' hSmeas).mpr (Filter.Eventually.of_forall (fun x hx => hb x hx))
      have hIntSe_of : ∀ (F : (Fin n → ℂ)→ℂ) (M : ℝ), AEStronglyMeasurable F (volume.restrict Se) →
          (∀ x ∈ Se, ‖F x‖ ≤ M) → IntegrableOn F Se volume :=
        fun F M hm hb => Work.CR.Flat.Cauchy.integrableOn_of_norm_le_const_aux hSe_meas hSefin hm hb
      have hGc : Continuous G := by rw [hG]; exact (hgcont.comp (continuous_const.add continuous_id)).sub continuous_const
      have hΦe : AEStronglyMeasurable (fun x : Fin n → ℂ => Φ (x-e)) volume :=
        hΦm.comp_quasiMeasurePreserving
          (MeasureTheory.measurePreserving_add_right volume (-e)).quasiMeasurePreserving
      have hρ_le_bet : ρ ≤ Bet * ρ^α := by
        have h1a : 0 < 1-α := by linarith
        calc ρ = ρ^(1-α) * ρ^α := by
              rw [← Real.rpow_add hρpos (1-α) α, show (1-α)+α = 1 from by ring, Real.rpow_one]
          _ ≤ (2*R)^(1-α) * ρ^α := mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow hρpos.le (by linarith [hn1]) h1a.le) (Real.rpow_nonneg hρpos.le _)
          _ ≤ Bet * ρ^α := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hρpos.le _)
      have hGxall : ∀ x, ‖G x‖ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := by
        intro x; rw [hG]
        have h4 : ‖x‖^α ≤ Work.CR.Flat.Cauchy.eucNorm x^α :=
          Real.rpow_le_rpow (norm_nonneg x) (Work.CR.Flat.Cauchy.pi_norm_le_eucNorm x) hα.le
        calc ‖g (z+x)-g z‖ ≤ K*‖x‖^α := by simpa using hg (z+x) z
          _ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := mul_le_mul_of_nonneg_left h4 hK
      have hΦebd : ∀ x ∈ Se, ‖Φ (x-e)‖ ≤ A/(2*ρ)^(2*n) := by
        intro x hx
        have hge : 2*ρ ≤ Work.CR.Flat.Cauchy.eucNorm (x-e) := hSe_ge x hx
        have hne : x - e ≠ 0 := fun h => absurd hge (by rw [h, Work.CR.Flat.Cauchy.eucNorm_zero]; linarith [hρpos])
        calc ‖Φ (x-e)‖ ≤ A / Work.CR.Flat.Cauchy.eucNorm (x-e)^(2*n) := hP1 (x-e) hne
          _ ≤ A/(2*ρ)^(2*n) := by
              apply div_le_div_of_nonneg_left hA.le (by positivity)
              exact pow_le_pow_left₀ (by positivity) hge (2*n)
      have hGxS : ∀ x ∈ S, ‖G x‖ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := by
        intro x hx
        rw [hG]
        have h4 : ‖x‖^α ≤ Work.CR.Flat.Cauchy.eucNorm x^α :=
          Real.rpow_le_rpow (norm_nonneg x) (Work.CR.Flat.Cauchy.pi_norm_le_eucNorm x) hα.le
        calc ‖g (z+x)-g z‖ ≤ K*‖x‖^α := by simpa using hg (z+x) z
          _ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := mul_le_mul_of_nonneg_left h4 hK
      have hΦxS : ∀ x ∈ S, ‖Φ x‖ ≤ A * Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) := by
        intro x hx
        have hxpos : 0 < Work.CR.Flat.Cauchy.eucNorm x := lt_of_lt_of_le h2ρpos (hS_ge x hx)
        have hxne : x ≠ 0 := fun h => by rw [h] at hxpos; simp [Work.CR.Flat.Cauchy.eucNorm_zero] at hxpos
        calc ‖Φ x‖ ≤ A / Work.CR.Flat.Cauchy.eucNorm x^(2*n) := hP1 x hxne
          _ = A * Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) := by
              rw [div_eq_mul_inv, rpow_inv_natpow hxpos (2*n),
                show ((2*n:ℕ):ℝ) = 2*(n:ℝ) from by push_cast; ring]
      have hDifS : ∀ x ∈ S, ‖Φ x - Φ (x-e)‖ ≤ A*ρ * Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))-1) := by
        intro x hx
        have hxpos : 0 < Work.CR.Flat.Cauchy.eucNorm x := lt_of_lt_of_le h2ρpos (hS_ge x hx)
        have hxe : 2*Work.CR.Flat.Cauchy.eucNorm e ≤ Work.CR.Flat.Cauchy.eucNorm x := by
          rw [← hρ]; exact hS_ge x hx
        rw [norm_sub_rev]
        calc ‖Φ (x-e) - Φ x‖ ≤ A*Work.CR.Flat.Cauchy.eucNorm e / Work.CR.Flat.Cauchy.eucNorm x^(2*n+1) := hP2 x e hxe
          _ = A*ρ / Work.CR.Flat.Cauchy.eucNorm x^(2*n+1) := by rw [hρ]
          _ = A*ρ * Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ)+1)) := by
              rw [div_eq_mul_inv, rpow_inv_natpow hxpos (2*n+1),
                show ((2*n+1:ℕ):ℝ) = 2*(n:ℝ)+1 from by push_cast; ring]
          _ = A*ρ * Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))-1) := by ring_nf
      have hΦeS : ∀ x ∈ S, ‖Φ (x-e)‖ ≤ (3/2)*A * Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) := by
        intro x hx
        have hxpos : 0 < Work.CR.Flat.Cauchy.eucNorm x := lt_of_lt_of_le h2ρpos (hS_ge x hx)
        have h1 : ‖Φ (x-e) - Φ x‖ ≤ A*ρ * Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))-1) := by
          have := hDifS x hx; rwa [norm_sub_rev] at this
        have h2 := hΦxS x hx
        have hsplit : A*ρ*Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))-1)
            = A*Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) * (ρ * Work.CR.Flat.Cauchy.eucNorm x ^ (-1 : ℝ)) := by
          rw [rpow_add_one_neg hxpos (-(2*(n:ℝ)))]; ring
        have hrle : ρ * Work.CR.Flat.Cauchy.eucNorm x ^ (-1 : ℝ) ≤ 1/2 := by
          rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hxpos]; nlinarith [hS_ge x hx]
        have hAe : 0 ≤ A*Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) := by positivity
        calc ‖Φ (x-e)‖ = ‖(Φ (x-e) - Φ x) + Φ x‖ := by ring_nf
          _ ≤ ‖Φ (x-e) - Φ x‖ + ‖Φ x‖ := norm_add_le _ _
          _ ≤ A*ρ*Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))-1)
              + A*Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) := add_le_add h1 h2
          _ = A*Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) * (ρ*Work.CR.Flat.Cauchy.eucNorm x^(-1 : ℝ))
              + A*Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) := by rw [hsplit]
          _ = A*Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) * (ρ*Work.CR.Flat.Cauchy.eucNorm x^(-1 : ℝ)+1) := by ring
          _ ≤ A*Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) * (1/2+1) :=
              mul_le_mul_of_nonneg_left (by linarith [hrle]) hAe
          _ = (3/2)*A * Work.CR.Flat.Cauchy.eucNorm x ^ (-(2*(n:ℝ))) := by ring
      have hΦeout : ∀ u, 4*R ≤ Work.CR.Flat.Cauchy.eucNorm u →
          ‖Φ (u-e)‖ ≤ (3/2)*A * Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))) := by
        intro u hu
        have hu2 : 2*ρ ≤ Work.CR.Flat.Cauchy.eucNorm u := by linarith
        have hupos : 0 < Work.CR.Flat.Cauchy.eucNorm u := by linarith [h2ρpos, hcase]
        have h2 : ‖Φ u‖ ≤ A * Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))) := by
          have hune : u ≠ 0 := fun h => by rw [h] at hupos; simp [Work.CR.Flat.Cauchy.eucNorm_zero] at hupos
          calc ‖Φ u‖ ≤ A / Work.CR.Flat.Cauchy.eucNorm u^(2*n) := hP1 u hune
            _ = A * Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))) := by
                rw [div_eq_mul_inv, rpow_inv_natpow hupos (2*n),
                  show ((2*n:ℕ):ℝ) = 2*(n:ℝ) from by push_cast; ring]
        have h1 : ‖Φ (u-e) - Φ u‖ ≤ A*ρ * Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))-1) := by
          have hpm := hP2 u e hu2
          calc ‖Φ (u-e) - Φ u‖ ≤ A*Work.CR.Flat.Cauchy.eucNorm e / Work.CR.Flat.Cauchy.eucNorm u^(2*n+1) := hpm
            _ = A*ρ / Work.CR.Flat.Cauchy.eucNorm u^(2*n+1) := by rw [hρ]
            _ = A*ρ * Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ)+1)) := by
                rw [div_eq_mul_inv, rpow_inv_natpow hupos (2*n+1),
                  show ((2*n+1:ℕ):ℝ) = 2*(n:ℝ)+1 from by push_cast; ring]
            _ = A*ρ * Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))-1) := by ring_nf
        have hsplit : A*ρ*Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))-1)
            = A*Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))) * (ρ * Work.CR.Flat.Cauchy.eucNorm u ^ (-1 : ℝ)) := by
          rw [rpow_add_one_neg hupos (-(2*(n:ℝ)))]; ring
        have hrle : ρ * Work.CR.Flat.Cauchy.eucNorm u ^ (-1 : ℝ) ≤ 1/2 := by
          rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hupos]; nlinarith [hu2]
        have hAe : 0 ≤ A*Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))) := by positivity
        calc ‖Φ (u-e)‖ = ‖(Φ (u-e) - Φ u) + Φ u‖ := by ring_nf
          _ ≤ ‖Φ (u-e) - Φ u‖ + ‖Φ u‖ := norm_add_le _ _
          _ ≤ A*ρ*Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))-1)
              + A*Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))) := add_le_add h1 h2
          _ = A*Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))) * (ρ*Work.CR.Flat.Cauchy.eucNorm u^(-1 : ℝ))
              + A*Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))) := by rw [hsplit]
          _ = A*Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ)))*(ρ*Work.CR.Flat.Cauchy.eucNorm u^(-1 : ℝ)+1) := by ring
          _ ≤ A*Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ)))*(1/2+1) :=
              mul_le_mul_of_nonneg_left (by linarith [hrle]) hAe
          _ = (3/2)*A * Work.CR.Flat.Cauchy.eucNorm u ^ (-(2*(n:ℝ))) := by ring
      -- integrability (constant bounds)
      have hP1bd : ∀ x ∈ S, ‖Φ x‖ ≤ A/(2*ρ)^(2*n) := by
        intro x hx
        have hxpos : 0 < Work.CR.Flat.Cauchy.eucNorm x := lt_of_lt_of_le h2ρpos (hS_ge x hx)
        have hxne : x ≠ 0 := fun h => by rw [h] at hxpos; simp [Work.CR.Flat.Cauchy.eucNorm_zero] at hxpos
        calc ‖Φ x‖ ≤ A / Work.CR.Flat.Cauchy.eucNorm x^(2*n) := hP1 x hxne
          _ ≤ A/(2*ρ)^(2*n) := by
              apply div_le_div_of_nonneg_left hA.le (by positivity)
              exact pow_le_pow_left₀ (by positivity) (hS_ge x hx) (2*n)
      have hP2bd : ∀ x ∈ S, ‖Φ (x-e)‖ ≤ A/ρ^(2*n) := by
        intro x hx
        have hge : ρ ≤ Work.CR.Flat.Cauchy.eucNorm (x-e) := by
          have h := Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le x (x-e)
          rw [sub_sub_cancel, ← hρ] at h
          have := (abs_le.mp h).2
          linarith [hS_ge x hx]
        have hne : x - e ≠ 0 := fun h => absurd hge (by rw [h, Work.CR.Flat.Cauchy.eucNorm_zero]; linarith [hρpos])
        calc ‖Φ (x-e)‖ ≤ A / Work.CR.Flat.Cauchy.eucNorm (x-e)^(2*n) := hP1 (x-e) hne
          _ ≤ A/ρ^(2*n) := by
              apply div_le_div_of_nonneg_left hA.le (by positivity)
              exact pow_le_pow_left₀ (le_of_lt hρpos) hge (2*n)
      have hGbd : ∀ x ∈ S, ‖G x‖ ≤ K*(4*R)^α := by
        intro x hx
        calc ‖G x‖ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := hGxS x hx
          _ ≤ K*(4*R)^α := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Work.CR.Flat.Cauchy.eucNorm_nonneg x) (le_of_lt (hS_lt x hx)) hα.le) hK
      have hGebd : ∀ x ∈ S, ‖G (x+e)‖ ≤ 2*K*(4*R)^α := by
        intro x hx
        have h1 : ‖g (z'+x) - g z'‖ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := by
          have h4 : ‖x‖^α ≤ Work.CR.Flat.Cauchy.eucNorm x^α :=
            Real.rpow_le_rpow (norm_nonneg x) (Work.CR.Flat.Cauchy.pi_norm_le_eucNorm x) hα.le
          calc ‖g (z'+x)-g z'‖ ≤ K*‖x‖^α := by simpa using hg (z'+x) z'
            _ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := mul_le_mul_of_nonneg_left h4 hK
        have h2 : ‖g z' - g z‖ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := by
          have h5 : ‖z'-z‖ ≤ Work.CR.Flat.Cauchy.eucNorm x := by
            rw [← he]
            calc ‖e‖ ≤ Work.CR.Flat.Cauchy.eucNorm e := Work.CR.Flat.Cauchy.pi_norm_le_eucNorm e
              _ = ρ := hρ.symm
              _ ≤ Work.CR.Flat.Cauchy.eucNorm x := by linarith [hS_ge x hx]
          calc ‖g z'-g z‖ ≤ K*‖z'-z‖^α := by simpa using hg z' z
            _ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) h5 hα.le) hK
        calc ‖G (x+e)‖ = ‖g (z+x+e) - g z‖ := by rw [hG]; simp only [add_assoc]
          _ = ‖(g (z'+x) - g z') + (g z' - g z)‖ := by
              rw [show z+x+e = z'+x from by rw [← hz'e]; abel]; congr 1; ring
          _ ≤ ‖g (z'+x)-g z'‖ + ‖g z'-g z‖ := norm_add_le _ _
          _ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α + K*Work.CR.Flat.Cauchy.eucNorm x^α := add_le_add h1 h2
          _ = 2*K*Work.CR.Flat.Cauchy.eucNorm x^α := by ring
          _ ≤ 2*K*(4*R)^α := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Work.CR.Flat.Cauchy.eucNorm_nonneg x) (le_of_lt (hS_lt x hx)) hα.le)
              (by positivity)
      have i_GS : IntegrableOn (fun x => Φ x * G x) S volume :=
        hIntS_of _ 0 ((A/(2*ρ)^(2*n))*(K*(4*R)^α))
          ((hΦm.mono_measure Measure.restrict_le_self).mul hGc.measurable.aestronglyMeasurable)
          (fun x hx => by
            rw [norm_mul, Real.rpow_zero, mul_one]
            exact mul_le_mul (hP1bd x hx) (hGbd x hx) (norm_nonneg _) (by positivity))
      have i_GeS : IntegrableOn (fun x => Φ x * G (x+e)) S volume :=
        hIntS_of _ 0 ((A/(2*ρ)^(2*n))*(2*K*(4*R)^α))
          ((hΦm.mono_measure Measure.restrict_le_self).mul
            ((hGc.comp (continuous_id.add continuous_const)).measurable.aestronglyMeasurable))
          (fun x hx => by
            rw [norm_mul, Real.rpow_zero, mul_one]
            exact mul_le_mul (hP1bd x hx) (hGebd x hx) (norm_nonneg _) (by positivity))
      have i_c0S : IntegrableOn (fun x => Φ x * c0) S volume :=
        hIntS_of _ 0 ((A/(2*ρ)^(2*n))*‖c0‖)
          ((hΦm.mono_measure Measure.restrict_le_self).mul aestronglyMeasurable_const)
          (fun x hx => by
            rw [norm_mul, Real.rpow_zero, mul_one]
            exact mul_le_mul_of_nonneg_right (hP1bd x hx) (norm_nonneg _))
      have i_B1S : IntegrableOn (fun x => Φ (x-e) * G x) S volume :=
        hIntS_of _ 0 ((A/ρ^(2*n))*(K*(4*R)^α))
          ((hΦe.mono_measure Measure.restrict_le_self).mul hGc.measurable.aestronglyMeasurable)
          (fun x hx => by
            rw [norm_mul, Real.rpow_zero, mul_one]
            exact mul_le_mul (hP2bd x hx) (hGbd x hx) (norm_nonneg _) (by positivity))
      have i_DifS : IntegrableOn (fun x => (Φ x - Φ (x-e)) * G x) S volume :=
        hIntS_of _ 0 (((A/(2*ρ)^(2*n)) + (A/ρ^(2*n)))*(K*(4*R)^α))
          (((hΦm.mono_measure Measure.restrict_le_self).sub (hΦe.mono_measure Measure.restrict_le_self)).mul
            hGc.measurable.aestronglyMeasurable)
          (fun x hx => by
            rw [norm_mul, Real.rpow_zero, mul_one]
            have hd : ‖Φ x - Φ (x-e)‖ ≤ (A/(2*ρ)^(2*n)) + (A/ρ^(2*n)) :=
              le_trans (norm_sub_le _ _) (add_le_add (hP1bd x hx) (hP2bd x hx))
            exact mul_le_mul hd (hGbd x hx) (norm_nonneg _) (by positivity))
      have i_B1Se : IntegrableOn (fun x => Φ (x-e) * G x) Se volume :=
        hIntSe_of _ ((A/(2*ρ)^(2*n))*(K*(4*R+ρ)^α))
          ((hΦe.mono_measure Measure.restrict_le_self).mul hGc.measurable.aestronglyMeasurable)
          (fun x hx => by
            rw [norm_mul]
            have hx4 : Work.CR.Flat.Cauchy.eucNorm x ≤ 4*R+ρ := by
              calc Work.CR.Flat.Cauchy.eucNorm x = Work.CR.Flat.Cauchy.eucNorm ((x-e)+e) := by rw [sub_add_cancel]
                _ ≤ Work.CR.Flat.Cauchy.eucNorm (x-e) + Work.CR.Flat.Cauchy.eucNorm e := eucNorm_add_le _ _
                _ ≤ 4*R + ρ := by rw [hρ]; linarith [hSe_lt x hx]
            have hGx : ‖G x‖ ≤ K*(4*R+ρ)^α :=
              calc ‖G x‖ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := hGxall x
                _ ≤ K*(4*R+ρ)^α := mul_le_mul_of_nonneg_left
                    (Real.rpow_le_rpow (Work.CR.Flat.Cauchy.eucNorm_nonneg x) hx4 hα.le) hK
            exact mul_le_mul (hΦebd x hx) hGx (norm_nonneg _) (by positivity))
      have hfarA : ∫ x in S, Φ x * Ψ x = ∫ x in S, Φ x * (G x - G (x+e)) := by
        have hpt : ∀ x, Φ x*Ψ x = Φ x*(G x - G (x+e)) + Φ x*c0 := by
          intro x
          have hΨx : Ψ x = (g (z+x) - g z) - (g (z'+x) - g z') := by simp only [hΨ]
          have hGx : G x = g (z+x) - g z := by simp only [hG]
          have hGe : G (x+e) = g (z'+x) - g z := by
            simp only [hG]; rw [show z + (x+e) = z'+x from by rw [← hz'e]; abel]
          rw [hΨx, hGx, hGe, hc0]; ring
        have hI1 : IntegrableOn (fun x => Φ x*(G x - G (x+e))) S volume :=
          (i_GS.sub i_GeS).congr (Filter.Eventually.of_forall (fun x => (mul_sub _ _ _).symm))
        calc ∫ x in S, Φ x*Ψ x
            = ∫ x in S, (Φ x*(G x-G (x+e)) + Φ x*c0) := by
                apply MeasureTheory.setIntegral_congr_fun hSmeas; intro x hx; exact hpt x
          _ = (∫ x in S, Φ x*(G x-G (x+e))) + ∫ x in S, Φ x*c0 := MeasureTheory.integral_add hI1 i_c0S
          _ = (∫ x in S, Φ x*(G x-G (x+e))) + 0 := by
              rw [show (∫ x in S, Φ x*c0) = 0 from by
                rw [MeasureTheory.integral_mul_const, hH2' (2*ρ) (4*R) h2ρpos hcase, zero_mul]]
          _ = ∫ x in S, Φ x*(G x-G (x+e)) := by rw [add_zero]
      have hfarB : ∫ x in S, Φ x * (G x - G (x+e)) = (∫ x in S, Φ x*G x) - (∫ x in S, Φ x*G (x+e)) := by
        rw [← MeasureTheory.integral_sub i_GS i_GeS]
        apply MeasureTheory.setIntegral_congr_fun hSmeas
        intro x hx; ring
      have hfarC2 : ∫ x in S, Φ x*G (x+e) = ∫ u in Se, Φ (u-e)*G u := by
        have := Work.CR.Flat.Cauchy.setIntegral_translate_euc e (fun u => Φ (u-e)*G u) S
        rw [hSe]; simpa using this
      have hfarD : ∫ x in S, Φ x*G x = (∫ x in S, (Φ x - Φ (x-e))*G x) + ∫ x in S, Φ (x-e)*G x := by
        rw [← MeasureTheory.integral_add i_DifS i_B1S]
        apply MeasureTheory.setIntegral_congr_fun hSmeas
        intro x hx; ring
      have hSdec : ∫ x in S, Φ (x-e)*G x = (∫ x in S\Se, Φ (x-e)*G x) + ∫ x in S∩Se, Φ (x-e)*G x := by
        have h1 := MeasureTheory.setIntegral_union
          (by rw [Set.disjoint_left]; intro x hx hy; exact hx.2 hy.2)
          (hSmeas.inter hSe_meas)
          (i_B1S.mono_set Set.sdiff_subset) (i_B1S.mono_set Set.inter_subset_left)
        rw [Set.sdiff_union_inter S Se] at h1
        exact h1
      have hSedec : ∫ x in Se, Φ (x-e)*G x = (∫ x in Se\S, Φ (x-e)*G x) + ∫ x in Se∩S, Φ (x-e)*G x := by
        have h1 := MeasureTheory.setIntegral_union
          (by rw [Set.disjoint_left]; intro x hx hy; exact hx.2 hy.2)
          (hSe_meas.inter hSmeas)
          (i_B1Se.mono_set Set.sdiff_subset) (i_B1Se.mono_set Set.inter_subset_left)
        rw [Set.sdiff_union_inter Se S] at h1
        exact h1
      have hint_eq : ∫ x in S∩Se, Φ (x-e)*G x = ∫ x in Se∩S, Φ (x-e)*G x := by rw [Set.inter_comm]
      have hsplitSe : (∫ x in S, Φ (x-e)*G x) - (∫ x in Se, Φ (x-e)*G x)
          = (∫ x in S\Se, Φ (x-e)*G x) - (∫ x in Se\S, Φ (x-e)*G x) := by
        rw [hSdec, hSedec, hint_eq]; ring
      -- ==== bounds ====
      have hShellbd : ∀ {a b : ℝ}, 0 < a → a ≤ b → b ≤ 6*R →
          ∫ x in Work.CR.Flat.Cauchy.eucShell (n:=n) a b, Work.CR.Flat.Cauchy.eucNorm x ^ (α-2*(n:ℝ))
            ≤ a^(α-2*(n:ℝ)) * ((2*(n:ℝ))*b^(2*n-1)*(b-a)*V) := by
        intro a b ha hab hb6
        have hfin : volume (Work.CR.Flat.Cauchy.eucShell (n:=n) a b) < ∞ :=
          Work.CR.Flat.Cauchy.volume_lt_top_of_subset_eucNorm (M := b)
            (fun x hx => le_of_lt (Work.CR.Flat.Cauchy.mem_eucShell.mp hx).2)
        have hbd : ∀ᵐ x ∂volume, x ∈ Work.CR.Flat.Cauchy.eucShell (n:=n) a b → ‖Work.CR.Flat.Cauchy.eucNorm x ^ (α-2*(n:ℝ))‖ ≤ a^(α-2*(n:ℝ)) := by
          filter_upwards with x hx
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (Work.CR.Flat.Cauchy.eucNorm_nonneg x) _)]
          exact Real.rpow_le_rpow_of_nonpos ha
            (Work.CR.Flat.Cauchy.mem_eucShell.mp hx).1 (by linarith [hn1])
        have h1 : ‖∫ x in Work.CR.Flat.Cauchy.eucShell (n:=n) a b, Work.CR.Flat.Cauchy.eucNorm x ^ (α-2*(n:ℝ))‖
            ≤ a^(α-2*(n:ℝ)) * (volume : Measure (Fin n → ℂ)).real (Work.CR.Flat.Cauchy.eucShell (n:=n) a b) :=
          MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae' hfin hbd
        have h2 : (0:ℝ) ≤ ∫ x in Work.CR.Flat.Cauchy.eucShell (n:=n) a b, Work.CR.Flat.Cauchy.eucNorm x ^ (α-2*(n:ℝ)) :=
          MeasureTheory.setIntegral_nonneg (Work.CR.Flat.Cauchy.measurableSet_eucShell a b)
            (fun x _ => Real.rpow_nonneg (Work.CR.Flat.Cauchy.eucNorm_nonneg x) _)
        calc ∫ x in Work.CR.Flat.Cauchy.eucShell (n:=n) a b, Work.CR.Flat.Cauchy.eucNorm x ^ (α-2*(n:ℝ))
            = ‖∫ x in Work.CR.Flat.Cauchy.eucShell (n:=n) a b, Work.CR.Flat.Cauchy.eucNorm x ^ (α-2*(n:ℝ))‖ :=
              (Real.norm_of_nonneg h2).symm
          _ ≤ a^(α-2*(n:ℝ)) * (volume : Measure (Fin n → ℂ)).real (Work.CR.Flat.Cauchy.eucShell (n:=n) a b) := h1
          _ ≤ a^(α-2*(n:ℝ)) * ((2*(n:ℝ))*b^(2*n-1)*(b-a)*V) :=
              mul_le_mul_of_nonneg_left (by simpa [hV] using volume_real_eucShell_le ha hab)
                (Real.rpow_nonneg ha.le _)
      have b1 : ‖∫ x in S, (Φ x - Φ (x-e))*G x‖ ≤ T1*K*ρ^α := by
        have hpt : ∀ x ∈ S, ‖(Φ x - Φ (x-e))*G x‖ ≤ A*ρ*K * eucNorm x ^ (α-2*(n:ℝ)-1) := by
          intro x hx
          have hxpos : 0 < eucNorm x := lt_of_lt_of_le h2ρpos (hS_ge x hx)
          calc ‖(Φ x - Φ (x-e))*G x‖ = ‖Φ x - Φ (x-e)‖*‖G x‖ := norm_mul _ _
            _ ≤ (A*ρ*eucNorm x ^ (-(2*(n:ℝ))-1))*(K*eucNorm x^α) :=
                mul_le_mul (hDifS x hx) (hGxS x hx) (norm_nonneg _)
                  (mul_nonneg (mul_nonneg hA.le hρpos.le) (Real.rpow_nonneg hxpos.le _))
            _ = A*ρ*K * (eucNorm x ^ (-(2*(n:ℝ))-1) * eucNorm x^α) := by ring
            _ = A*ρ*K * eucNorm x ^ (α-2*(n:ℝ)-1) := by
                rw [rpow_mul_rpow hxpos (-(2*(n:ℝ))-1) α]
                congr 2; ring
        calc ‖∫ x in S, (Φ x - Φ (x-e))*G x‖ ≤ ∫ x in S, ‖(Φ x - Φ (x-e))*G x‖ :=
              norm_setIntegral_le_integral_norm S _
          _ ≤ ∫ x in S, A*ρ*K * eucNorm x ^ (α-2*(n:ℝ)-1) :=
              MeasureTheory.setIntegral_mono_on (MeasureTheory.Integrable.norm i_DifS)
                ((hSdom (α-2*(n:ℝ)-1)).const_mul _) hSmeas (fun x hx => hpt x hx)
          _ = A*ρ*K * ∫ x in S, eucNorm x ^ (α-2*(n:ℝ)-1) := by rw [MeasureTheory.integral_const_mul]
          _ ≤ A*ρ*K * (Csh * (2*ρ) ^ (α-1)) :=
              mul_le_mul_of_nonneg_left (by
                have hc := hCsh h2ρpos hcase
                rw [← hS] at hc
                rwa [show α-2*(n:ℝ)-1 + 2*(n:ℝ) = α-1 from by ring] at hc) (by positivity)
          _ = T1*K*ρ^α := by
              rw [hT1, show (2*ρ) ^ (α-1) = (2:ℝ)^(α-1) * ρ^(α-1) from Real.mul_rpow (by norm_num) hρpos.le]
              rw [show ρ^α = ρ * ρ^(α-1) from by
                conv_lhs => rw [show α = 1+(α-1) from by ring]
                rw [Real.rpow_add hρpos, Real.rpow_one]]
              ring
      have b2 : ‖∫ x in S\Se, Φ (x-e)*G x‖ ≤ (T2+T3)*K*ρ^α := by
        have hpt : ∀ x ∈ S\Se, ‖Φ (x-e)*G x‖ ≤ (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) := by
          intro x hx
          have hxS : x ∈ S := hx.1
          have hxpos : 0 < eucNorm x := lt_of_lt_of_le h2ρpos (hS_ge x hxS)
          rw [norm_mul]
          calc ‖Φ (x-e)‖*‖G x‖ ≤ ((3/2)*A*eucNorm x ^ (-(2*(n:ℝ))))*(K*eucNorm x^α) :=
                mul_le_mul (hΦeS x hxS) (hGxS x hxS) (norm_nonneg _)
                  (mul_nonneg (by positivity) (Real.rpow_nonneg hxpos.le _))
            _ = (3/2)*A*K * (eucNorm x ^ (-(2*(n:ℝ))) * eucNorm x^α) := by ring
            _ = (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) := by
                rw [rpow_mul_rpow hxpos (-(2*(n:ℝ))) α]; congr 2; ring
        have hsubc : S\Se ⊆ eucBall (3*ρ) ∪ (eucShell (n:=n) (4*R-ρ) (4*R) \ eucBall (3*ρ)) := by
          intro x hx
          have hxS : x ∈ S := hx.1
          by_cases hc : eucNorm x < 3*ρ
          · left; rw [Work.CR.Flat.Cauchy.mem_eucBall]; exact hc
          · push_neg at hc
            right
            rw [Set.mem_diff, Work.CR.Flat.Cauchy.mem_eucShell, Work.CR.Flat.Cauchy.mem_eucBall]
            refine ⟨⟨?_, hS_lt x hxS⟩, not_lt.mpr hc⟩
            by_contra hcon
            push_neg at hcon
            apply hx.2
            rw [hSe_mem x, hS, Work.CR.Flat.Cauchy.mem_eucShell]
            refine ⟨?_, ?_⟩
            · by_contra h2; push_neg at h2
              have h3 := eucNorm_add_le (x-e) e
              rw [sub_add_cancel, ← hρ] at h3
              linarith [h3, h2, hc]
            · have h4 := (abs_le.mp (Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le x (x-e))).1
              rw [show x - (x-e) = e from by abel, ← hρ] at h4
              linarith [h4, hcon]
        set A_in := (S\Se) ∩ eucBall (3*ρ) with hAin
        set A_out := (S\Se) ∩ (eucShell (n:=n) (4*R-ρ) (4*R) \ eucBall (3*ρ)) with hAout
        have hAmeas : MeasurableSet A_in :=
          (hSmeas.diff hSe_meas).inter (Work.CR.Flat.Cauchy.measurableSet_eucBall _)
        have hAoutmeas : MeasurableSet A_out :=
          (hSmeas.diff hSe_meas).inter ((Work.CR.Flat.Cauchy.measurableSet_eucShell _ _).diff (Work.CR.Flat.Cauchy.measurableSet_eucBall _))
        have hunion : S\Se = A_in ∪ A_out := by
          rw [hAin, hAout]; ext x; constructor
          · intro hx; rcases hsubc hx with h|h; exacts [Or.inl ⟨hx,h⟩, Or.inr ⟨hx,h⟩]
          · rintro (⟨hx,_⟩|⟨hx,_⟩) <;> exact hx
        have hIntAin : IntegrableOn (fun x => Φ (x-e)*G x) A_in volume :=
          (i_B1S.mono_set Set.sdiff_subset).mono_set Set.inter_subset_left
        have hIntAout : IntegrableOn (fun x => Φ (x-e)*G x) A_out volume :=
          (i_B1S.mono_set Set.sdiff_subset).mono_set Set.inter_subset_left
        have hdisjAA : Disjoint A_in A_out := by
          rw [Set.disjoint_left]; intro x hx hy
          rw [hAin] at hx; rw [hAout] at hy
          simp only [Set.mem_inter_iff, Set.mem_diff, Work.CR.Flat.Cauchy.mem_eucBall] at hx hy
          exact hy.2.2 hx.2
        have hbInner : ‖∫ x in A_in, Φ (x-e)*G x‖ ≤ T2*K*ρ^α := by
          have hii2 : IntegrableOn (fun x => (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ))) A_in volume :=
            ((hSdom (α-2*(n:ℝ))).mono_set (Set.Subset.trans Set.inter_subset_left Set.sdiff_subset)).const_mul _
          calc ‖∫ x in A_in, Φ (x-e)*G x‖ ≤ ∫ x in A_in, ‖Φ (x-e)*G x‖ := norm_setIntegral_le_integral_norm _ _
            _ ≤ ∫ x in A_in, (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) :=
                MeasureTheory.setIntegral_mono_on (MeasureTheory.Integrable.norm hIntAin) hii2 hAmeas
                  (fun x hx => hpt x hx.1)
            _ ≤ ∫ x in eucBall (3*ρ), (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) := by
                refine MeasureTheory.setIntegral_mono_set
                  ((Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_ball hn (by linarith [hn1]) (3*ρ)).const_mul _) ?_ ?_
                · exact Filter.Eventually.of_forall (fun x => mul_nonneg (by positivity) (Real.rpow_nonneg (eucNorm_nonneg x) _))
                · exact Filter.Eventually.of_forall (fun x hx => hx.2)
            _ = (3/2)*A*K * ∫ x in eucBall (3*ρ), eucNorm x ^ (α-2*(n:ℝ)) := by rw [MeasureTheory.integral_const_mul]
            _ ≤ (3/2)*A*K * (Crad * (3*ρ)^α) :=
                mul_le_mul_of_nonneg_left (by
                  have hcr := hCrad (3*ρ) (by positivity)
                  rwa [show α-2*(n:ℝ) + 2*(n:ℝ) = α from by ring] at hcr) (by positivity)
            _ = T2*K*ρ^α := by
                rw [hT2, show (3*ρ)^α = (3:ℝ)^α * ρ^α from Real.mul_rpow (by norm_num) hρpos.le]; ring
        have hbOuter : ‖∫ x in A_out, Φ (x-e)*G x‖ ≤ T3*K*ρ^α := by
          have hii2sh : IntegrableOn (fun x => (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)))
              (eucShell (n:=n) (4*R-ρ) (4*R)) volume :=
            (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_shell (n:=n) (s:=α-2*(n:ℝ))
              (by linarith [hρpos]) (by linarith [hρpos])).const_mul _
          have hsh : ∫ x in eucShell (n:=n) (4*R-ρ) (4*R), eucNorm x ^ (α-2*(n:ℝ))
              ≤ (2*R)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(4*R)^(2*n-1)*ρ*V) := by
            calc ∫ x in eucShell (n:=n) (4*R-ρ) (4*R), eucNorm x ^ (α-2*(n:ℝ))
                ≤ (4*R-ρ)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(4*R)^(2*n-1)*(4*R-(4*R-ρ))*V) :=
                  hShellbd (a := 4*R-ρ) (b := 4*R) (by linarith [hρpos]) (by linarith [hρpos]) (by linarith)
              _ = (4*R-ρ)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(4*R)^(2*n-1)*ρ*V) := by ring_nf
              _ ≤ (2*R)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(4*R)^(2*n-1)*ρ*V) :=
                  mul_le_mul_of_nonneg_right
                    (Real.rpow_le_rpow_of_nonpos (by linarith [hR]) (by linarith [hcase]) (by linarith [hn1]))
                    (by positivity)
          calc ‖∫ x in A_out, Φ (x-e)*G x‖ ≤ ∫ x in A_out, ‖Φ (x-e)*G x‖ := norm_setIntegral_le_integral_norm _ _
            _ ≤ ∫ x in A_out, (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) :=
                MeasureTheory.setIntegral_mono_on (MeasureTheory.Integrable.norm hIntAout)
                  (hii2sh.mono_set (by intro x hx; exact hx.2.1)) hAoutmeas (fun x hx => hpt x hx.1)
            _ ≤ ∫ x in eucShell (n:=n) (4*R-ρ) (4*R), (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) := by
                refine MeasureTheory.setIntegral_mono_set hii2sh ?_ ?_
                · exact Filter.Eventually.of_forall (fun x => mul_nonneg (by positivity) (Real.rpow_nonneg (eucNorm_nonneg x) _))
                · exact Filter.Eventually.of_forall (fun x hx => hx.2.1)
            _ = (3/2)*A*K * ∫ x in eucShell (n:=n) (4*R-ρ) (4*R), eucNorm x ^ (α-2*(n:ℝ)) := by rw [MeasureTheory.integral_const_mul]
            _ ≤ (3/2)*A*K * ((2*R)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(4*R)^(2*n-1)*ρ*V)) :=
                mul_le_mul_of_nonneg_left hsh (by positivity)
            _ ≤ T3*K*ρ^α := by
                rw [hT3]
                rw [show (3/2)*A*K * ((2*R)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(4*R)^(2*n-1)*ρ*V))
                    = ((3/2)*A*(2*R)^(α-2*(n:ℝ))*(2*(n:ℝ))*(4*R)^(2*n-1)*V*K)*ρ from by ring]
                rw [show (3/2)*A*(2*R)^(α-2*(n:ℝ))*(2*(n:ℝ))*(4*R)^(2*n-1)*V*Bet*K*ρ^α
                    = ((3/2)*A*(2*R)^(α-2*(n:ℝ))*(2*(n:ℝ))*(4*R)^(2*n-1)*V*K)*(Bet*ρ^α) from by ring]
                exact mul_le_mul_of_nonneg_left hρ_le_bet (by positivity)
        calc ‖∫ x in S\Se, Φ (x-e)*G x‖ = ‖∫ x in A_in ∪ A_out, Φ (x-e)*G x‖ := by rw [← hunion]
          _ = ‖(∫ x in A_in, Φ (x-e)*G x) + ∫ x in A_out, Φ (x-e)*G x‖ := by
              rw [MeasureTheory.setIntegral_union hdisjAA hAoutmeas hIntAin hIntAout]
          _ ≤ ‖∫ x in A_in, Φ (x-e)*G x‖ + ‖∫ x in A_out, Φ (x-e)*G x‖ := norm_add_le _ _
          _ ≤ T2*K*ρ^α + T3*K*ρ^α := add_le_add hbInner hbOuter
          _ = (T2+T3)*K*ρ^α := by ring
      have b3 : ‖∫ x in Se\S, Φ (x-e)*G x‖ ≤ (T4+T5)*K*ρ^α := by
        have hsub3 : Se\S ⊆ eucBall (2*ρ) ∪ eucShell (n:=n) (4*R) (4*R+ρ) := by
          intro x hx
          have hxSe : x ∈ Se := hx.1
          have hx4 : eucNorm x < 4*R+ρ := by
            calc eucNorm x = eucNorm ((x-e)+e) := by rw [sub_add_cancel]
              _ ≤ eucNorm (x-e) + eucNorm e := eucNorm_add_le _ _
              _ < 4*R + ρ := by rw [hρ]; linarith [hSe_lt x hxSe]
          by_cases hc : eucNorm x < 2*ρ
          · left; rw [Work.CR.Flat.Cauchy.mem_eucBall]; exact hc
          · push_neg at hc
            right; rw [Work.CR.Flat.Cauchy.mem_eucShell]; refine ⟨?_, hx4⟩
            by_contra hcon; push_neg at hcon
            exact hx.2 (by rw [hS, Work.CR.Flat.Cauchy.mem_eucShell]; exact ⟨hc, hcon⟩)
        set B_in := (Se\S) ∩ eucBall (2*ρ) with hBin
        set B_out := (Se\S) ∩ eucShell (n:=n) (4*R) (4*R+ρ) with hBout
        have hBmeas : MeasurableSet B_in := (hSe_meas.diff hSmeas).inter (Work.CR.Flat.Cauchy.measurableSet_eucBall _)
        have hBoutmeas : MeasurableSet B_out := (hSe_meas.diff hSmeas).inter (Work.CR.Flat.Cauchy.measurableSet_eucShell _ _)
        have hunion3 : Se\S = B_in ∪ B_out := by
          rw [hBin, hBout]; ext x; constructor
          · intro hx; rcases hsub3 hx with h|h; exacts [Or.inl ⟨hx,h⟩, Or.inr ⟨hx,h⟩]
          · rintro (⟨hx,_⟩|⟨hx,_⟩) <;> exact hx
        have hIntBin : IntegrableOn (fun x => Φ (x-e)*G x) B_in volume :=
          (i_B1Se.mono_set Set.sdiff_subset).mono_set Set.inter_subset_left
        have hIntBout : IntegrableOn (fun x => Φ (x-e)*G x) B_out volume :=
          (i_B1Se.mono_set Set.sdiff_subset).mono_set Set.inter_subset_left
        have hdisjBB : Disjoint B_in B_out := by
          rw [Set.disjoint_left]; intro x hx hy
          rw [hBin] at hx; rw [hBout] at hy
          simp only [Set.mem_inter_iff, Work.CR.Flat.Cauchy.mem_eucBall, Work.CR.Flat.Cauchy.mem_eucShell] at hx hy
          linarith [hx.2, hy.2.1]
        have hbInner3 : ‖∫ x in B_in, Φ (x-e)*G x‖ ≤ T4*K*ρ^α := by
          have hCnn : (0:ℝ) ≤ (A/(2*ρ)^(2*n))*(K*(2*ρ)^α) :=
            mul_nonneg (div_nonneg hA.le (pow_nonneg (by linarith [hρpos]) _))
              (mul_nonneg hK (Real.rpow_nonneg (by linarith [hρpos]) _))
          have hfinB : volume B_in < ∞ := lt_of_le_of_lt
            (MeasureTheory.measure_mono (Set.Subset.trans Set.inter_subset_left Set.sdiff_subset)) hSefin
          have hptB : ∀ x ∈ B_in, ‖Φ (x-e)*G x‖ ≤ (A/(2*ρ)^(2*n))*(K*(2*ρ)^α) := by
            intro x hx
            rw [norm_mul]
            have hG : ‖G x‖ ≤ K*(2*ρ)^α :=
              calc ‖G x‖ ≤ K*eucNorm x^α := hGxall x
                _ ≤ K*(2*ρ)^α := mul_le_mul_of_nonneg_left
                    (Real.rpow_le_rpow (eucNorm_nonneg x) (le_of_lt hx.2) hα.le) hK
            exact mul_le_mul (hΦebd x hx.1.1) hG (norm_nonneg _) (le_of_lt (div_pos hA (pow_pos (by linarith [hρpos]) _)))
          have hii2bin : IntegrableOn (fun _ : Fin n → ℂ => (A/(2*ρ)^(2*n))*(K*(2*ρ)^α)) B_in volume :=
            Work.CR.Flat.Cauchy.integrableOn_of_norm_le_const_aux hBmeas hfinB aestronglyMeasurable_const
              (fun x hx => by rw [Real.norm_of_nonneg hCnn])
          have hfinB2 : volume (eucBall (2*ρ)) < ∞ := lt_of_le_of_lt
            (MeasureTheory.measure_mono (Work.CR.Flat.Cauchy.eucBall_subset_ball (R := 2*ρ)))
            (MeasureTheory.measure_ball_lt_top (μ := (volume : Measure (Fin n → ℂ))))
          have hii2ball : IntegrableOn (fun _ : Fin n → ℂ => (A/(2*ρ)^(2*n))*(K*(2*ρ)^α)) (eucBall (2*ρ)) volume :=
            Work.CR.Flat.Cauchy.integrableOn_of_norm_le_const_aux (Work.CR.Flat.Cauchy.measurableSet_eucBall _) hfinB2
              aestronglyMeasurable_const (fun x hx => by rw [Real.norm_of_nonneg hCnn])
          calc ‖∫ x in B_in, Φ (x-e)*G x‖ ≤ ∫ x in B_in, ‖Φ (x-e)*G x‖ := norm_setIntegral_le_integral_norm _ _
            _ ≤ ∫ x in B_in, (A/(2*ρ)^(2*n))*(K*(2*ρ)^α) :=
                MeasureTheory.setIntegral_mono_on (MeasureTheory.Integrable.norm hIntBin) hii2bin hBmeas hptB
            _ ≤ ∫ x in eucBall (2*ρ), (A/(2*ρ)^(2*n))*(K*(2*ρ)^α) := by
                refine MeasureTheory.setIntegral_mono_set hii2ball ?_ ?_
                · exact Filter.Eventually.of_forall (fun x => hCnn)
                · exact Filter.Eventually.of_forall (fun x hx => hx.2)
            _ = (A/(2*ρ)^(2*n))*(K*(2*ρ)^α) * (volume : Measure (Fin n → ℂ)).real (eucBall (2*ρ)) := by
                rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
            _ = T4*K*ρ^α := by
                rw [hT4, volume_real_eucBall_eq (n:=n) (by linarith [hρpos]),
                  show (2*ρ)^α = (2:ℝ)^α * ρ^α from Real.mul_rpow (by norm_num) hρpos.le]
                field_simp
                ring
        have hbOuter3 : ‖∫ x in B_out, Φ (x-e)*G x‖ ≤ T5*K*ρ^α := by
          have hii2sh : IntegrableOn (fun x => (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)))
              (eucShell (n:=n) (4*R) (4*R+ρ)) volume :=
            (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_shell (n:=n) (s:=α-2*(n:ℝ))
              (by linarith [hR]) (by linarith [hρpos])).const_mul _
          have hptB : ∀ x ∈ B_out, ‖Φ (x-e)*G x‖ ≤ (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) := by
            intro x hx
            have hxpos : 0 < eucNorm x := by linarith [hx.2.1]
            rw [norm_mul]
            calc ‖Φ (x-e)‖*‖G x‖ ≤ ((3/2)*A*eucNorm x ^ (-(2*(n:ℝ))))*(K*eucNorm x^α) :=
                  mul_le_mul (hΦeout x hx.2.1) (hGxall x) (norm_nonneg _)
                    (mul_nonneg (by positivity) (Real.rpow_nonneg hxpos.le _))
              _ = (3/2)*A*K * (eucNorm x ^ (-(2*(n:ℝ))) * eucNorm x^α) := by ring
              _ = (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) := by
                  rw [rpow_mul_rpow hxpos (-(2*(n:ℝ))) α]; congr 2; ring
          have hsh : ∫ x in eucShell (n:=n) (4*R) (4*R+ρ), eucNorm x ^ (α-2*(n:ℝ))
              ≤ (4*R)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(6*R)^(2*n-1)*ρ*V) := by
            calc ∫ x in eucShell (n:=n) (4*R) (4*R+ρ), eucNorm x ^ (α-2*(n:ℝ))
                ≤ (4*R)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(4*R+ρ)^(2*n-1)*(4*R+ρ-(4*R))*V) :=
                  hShellbd (a := 4*R) (b := 4*R+ρ) (by linarith [hR]) (by linarith [hρpos]) (by linarith [hcase])
              _ ≤ (4*R)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(6*R)^(2*n-1)*ρ*V) :=
                  mul_le_mul_of_nonneg_left
                    (by
                      rw [show 4*R+ρ-(4*R) = ρ from by ring]
                      exact mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left
                            (pow_le_pow_left₀ (by positivity) (by linarith [hcase]) _) (by positivity))
                          (le_of_lt hρpos))
                        (by positivity))
                    (Real.rpow_nonneg (by linarith [hR]) _)
          calc ‖∫ x in B_out, Φ (x-e)*G x‖ ≤ ∫ x in B_out, ‖Φ (x-e)*G x‖ := norm_setIntegral_le_integral_norm _ _
            _ ≤ ∫ x in B_out, (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) :=
                MeasureTheory.setIntegral_mono_on (MeasureTheory.Integrable.norm hIntBout)
                  (hii2sh.mono_set Set.inter_subset_right) hBoutmeas (fun x hx => hptB x hx)
            _ ≤ ∫ x in eucShell (n:=n) (4*R) (4*R+ρ), (3/2)*A*K * eucNorm x ^ (α-2*(n:ℝ)) := by
                refine MeasureTheory.setIntegral_mono_set hii2sh ?_ ?_
                · exact Filter.Eventually.of_forall (fun x => mul_nonneg (by positivity) (Real.rpow_nonneg (eucNorm_nonneg x) _))
                · exact Filter.Eventually.of_forall (fun x hx => hx.2)
            _ = (3/2)*A*K * ∫ x in eucShell (n:=n) (4*R) (4*R+ρ), eucNorm x ^ (α-2*(n:ℝ)) := by rw [MeasureTheory.integral_const_mul]
            _ ≤ (3/2)*A*K * ((4*R)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(6*R)^(2*n-1)*ρ*V)) :=
                mul_le_mul_of_nonneg_left hsh (by positivity)
            _ ≤ T5*K*ρ^α := by
                rw [hT5]
                rw [show (3/2)*A*K * ((4*R)^(α-2*(n:ℝ)) * ((2*(n:ℝ))*(6*R)^(2*n-1)*ρ*V))
                    = ((3/2)*A*(4*R)^(α-2*(n:ℝ))*(2*(n:ℝ))*(6*R)^(2*n-1)*V*K)*ρ from by ring]
                rw [show (3/2)*A*(4*R)^(α-2*(n:ℝ))*(2*(n:ℝ))*(6*R)^(2*n-1)*V*Bet*K*ρ^α
                    = ((3/2)*A*(4*R)^(α-2*(n:ℝ))*(2*(n:ℝ))*(6*R)^(2*n-1)*V*K)*(Bet*ρ^α) from by ring]
                exact mul_le_mul_of_nonneg_left hρ_le_bet (by positivity)
        calc ‖∫ x in Se\S, Φ (x-e)*G x‖ = ‖∫ x in B_in ∪ B_out, Φ (x-e)*G x‖ := by rw [← hunion3]
          _ = ‖(∫ x in B_in, Φ (x-e)*G x) + ∫ x in B_out, Φ (x-e)*G x‖ := by
              rw [MeasureTheory.setIntegral_union hdisjBB hBoutmeas hIntBin hIntBout]
          _ ≤ ‖∫ x in B_in, Φ (x-e)*G x‖ + ‖∫ x in B_out, Φ (x-e)*G x‖ := norm_add_le _ _
          _ ≤ T4*K*ρ^α + T5*K*ρ^α := add_le_add hbInner3 hbOuter3
          _ = (T4+T5)*K*ρ^α := by ring
      have hfar_eq : ∫ x in S, Φ x * Ψ x
          = (∫ x in S, (Φ x - Φ (x-e))*G x) + (∫ x in S\Se, Φ (x-e)*G x)
            - (∫ x in Se\S, Φ (x-e)*G x) := by
        have h1 : ∫ x in S, Φ x * Ψ x = (∫ x in S, Φ x*G x) - (∫ x in S, Φ x*G (x+e)) := by rw [hfarA, hfarB]
        have hBC : (∫ x in S, Φ (x-e)*G x) - (∫ x in Se, Φ (x-e)*G x)
            = (∫ x in S\Se, Φ (x-e)*G x) - (∫ x in Se\S, Φ (x-e)*G x) := hsplitSe
        rw [h1, hfarD, hfarC2]
        linear_combination hBC
      calc ‖∫ x in S, Φ x * Ψ x‖
          = ‖(∫ x in S, (Φ x - Φ (x-e))*G x) + (∫ x in S\Se, Φ (x-e)*G x) - (∫ x in Se\S, Φ (x-e)*G x)‖ := by
              rw [hfar_eq]
        _ = ‖(∫ x in S, (Φ x - Φ (x-e))*G x) + ((∫ x in S\Se, Φ (x-e)*G x) - (∫ x in Se\S, Φ (x-e)*G x))‖ := by
              congr 1; ring
        _ ≤ ‖∫ x in S, (Φ x - Φ (x-e))*G x‖ + ‖(∫ x in S\Se, Φ (x-e)*G x) - (∫ x in Se\S, Φ (x-e)*G x)‖ :=
              norm_add_le _ _
        _ ≤ ‖∫ x in S, (Φ x - Φ (x-e))*G x‖ + (‖∫ x in S\Se, Φ (x-e)*G x‖ + ‖∫ x in Se\S, Φ (x-e)*G x‖) :=
              add_le_add (le_refl _) (norm_sub_le _ _)
        _ ≤ T1*K*ρ^α + ((T2+T3)*K*ρ^α + (T4+T5)*K*ρ^α) := add_le_add b1 (add_le_add b2 b3)
        _ = FarC*K*ρ^α := by rw [hFarC]; ring

    · have hempty : S = ∅ := by
        rw [hS]; ext x
        simp only [Work.CR.Flat.Cauchy.mem_eucShell, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2; linarith
      rw [hempty]; simp only [MeasureTheory.setIntegral_empty, norm_zero]
      exact mul_nonneg (mul_nonneg hFarCpos.le hK) (Real.rpow_nonneg hρpos.le _)

  -- ============ integrability of the original integrands ============
  have hInt_w : ∀ w : Fin n → ℂ, IntegrableOn (fun x => Φ x * (g (w+x) - g w)) B volume := by
    intro w
    have hmaj : IntegrableOn (fun x => A*K * Work.CR.Flat.Cauchy.eucNorm x ^ (α - 2*(n:ℝ))) B volume :=
      MeasureTheory.Integrable.const_mul (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_ball hn (by linarith) (4*R)) (A*K)
    refine hmaj.mono' ?_ ?_
    · exact (hΦm.mono_measure Measure.restrict_le_self).mul
        (((hgcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable.sub aestronglyMeasurable_const))
    · filter_upwards with x
      by_cases hx : x = 0
      · subst hx
        simp [Work.CR.Flat.Cauchy.eucNorm_zero, Real.zero_rpow hzpow]
      · have hxpos : 0 < Work.CR.Flat.Cauchy.eucNorm x := Work.CR.Flat.Cauchy.eucNorm_pos hx
        have hw : ‖g (w+x) - g w‖ ≤ K * Work.CR.Flat.Cauchy.eucNorm x ^ α := by
          have h4 : ‖x‖ ^ α ≤ Work.CR.Flat.Cauchy.eucNorm x ^ α :=
            Real.rpow_le_rpow (norm_nonneg x) (Work.CR.Flat.Cauchy.pi_norm_le_eucNorm x) hα.le
          calc ‖g (w+x)-g w‖ ≤ K*‖x‖^α := by simpa using hg (w+x) w
            _ ≤ K*Work.CR.Flat.Cauchy.eucNorm x^α := mul_le_mul_of_nonneg_left h4 hK
        calc ‖Φ x * (g (w+x)-g w)‖ = ‖Φ x‖*‖g (w+x)-g w‖ := norm_mul _ _
          _ ≤ (A/(Work.CR.Flat.Cauchy.eucNorm x)^(2*n))*(K*Work.CR.Flat.Cauchy.eucNorm x^α) :=
              mul_le_mul (hP1 x hx) hw (norm_nonneg _) (div_nonneg hA.le (by positivity))
          _ = A*K*(Work.CR.Flat.Cauchy.eucNorm x^α/(Work.CR.Flat.Cauchy.eucNorm x)^(2*n)) := by ring
          _ = A*K*Work.CR.Flat.Cauchy.eucNorm x^(α-2*(n:ℝ)) := by
              rw [rpow_div_natpow hxpos α (2*n),
                show ((2*n:ℕ):ℝ)=2*(n:ℝ) from by push_cast; ring]
  have hIntz := hInt_w z
  have hIntz' := hInt_w z'
  rw [← MeasureTheory.integral_sub hIntz hIntz']
  have hcong1 : ∫ x in B, (Φ x * (g (z+x) - g z) - Φ x * (g (z'+x) - g z'))
      = ∫ x in B, Φ x * Ψ x := by
    apply MeasureTheory.setIntegral_congr_fun (Work.CR.Flat.Cauchy.measurableSet_eucBall (n:=n) (4*R))
    intro x hx
    rw [hΨ]; ring
  rw [hcong1]
  -- split B
  have hsplit : B = N ∪ S := by
    rw [hB, hN, hS]; ext x
    simp only [Work.CR.Flat.Cauchy.mem_eucBall, Work.CR.Flat.Cauchy.mem_eucShell, Set.mem_union]
    constructor
    · intro hx
      rcases le_or_gt (2*ρ) (4*R) with h | h
      · rw [min_eq_left h]
        by_cases h2 : Work.CR.Flat.Cauchy.eucNorm x < 2*ρ
        · exact Or.inl h2
        · exact Or.inr ⟨le_of_not_gt h2, hx⟩
      · rw [min_eq_right h.le]; exact Or.inl hx
    · rintro (h | ⟨h1, h2⟩)
      · exact lt_of_lt_of_le h (min_le_right _ _)
      · exact h2
  have hdisj : Disjoint N S := by
    rw [Set.disjoint_left]; intro x hx1 hx2
    rw [hN] at hx1; rw [hS] at hx2
    simp only [Work.CR.Flat.Cauchy.mem_eucBall, Work.CR.Flat.Cauchy.mem_eucShell] at hx1 hx2
    exact absurd (lt_of_lt_of_le hx1 (min_le_left _ _)) (not_lt.mpr hx2.1)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj (Work.CR.Flat.Cauchy.measurableSet_eucShell _ _) hIntN hIntS]
  -- final
  have hρbound : ρ ^ α ≤ (Real.sqrt (n:ℝ)) ^ α * ‖z - z'‖ ^ α := by
    have hle : ρ ≤ Real.sqrt (n:ℝ) * ‖z - z'‖ := by
      rw [hρ]
      calc Work.CR.Flat.Cauchy.eucNorm e ≤ Real.sqrt (n:ℝ) * ‖e‖ :=
            Work.CR.Flat.Cauchy.bmCz.eucNorm_le_sqrt_mul_norm e
        _ = Real.sqrt (n:ℝ) * ‖z - z'‖ := by rw [he, norm_sub_rev]
    calc ρ^α ≤ (Real.sqrt (n:ℝ) * ‖z-z'‖)^α := Real.rpow_le_rpow hρpos.le hle hα.le
      _ = (Real.sqrt (n:ℝ))^α * ‖z-z'‖^α :=
          Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)
  calc ‖(∫ x in N, Φ x * Ψ x) + ∫ x in S, Φ x * Ψ x‖
      ≤ ‖∫ x in N, Φ x * Ψ x‖ + ‖∫ x in S, Φ x * Ψ x‖ := norm_add_le _ _
    _ ≤ NearC * K * ρ^α + FarC * K * ρ^α := add_le_add hNear hFar
    _ = BigC * K * ρ^α := by rw [hBigC]; ring
    _ ≤ (Real.sqrt (n:ℝ))^α * BigC * K * ‖z - z'‖^α := by
        have h1 : BigC*K*ρ^α ≤ BigC*K*((Real.sqrt (n:ℝ))^α * ‖z-z'‖^α) :=
          mul_le_mul_of_nonneg_left hρbound (mul_nonneg hBigCpos.le hK)
        calc BigC*K*ρ^α ≤ BigC*K*((Real.sqrt (n:ℝ))^α * ‖z-z'‖^α) := h1
          _ = (Real.sqrt (n:ℝ))^α * BigC * K * ‖z-z'‖^α := by ring


end Work.CR.Flat.Cauchy.bmCz
