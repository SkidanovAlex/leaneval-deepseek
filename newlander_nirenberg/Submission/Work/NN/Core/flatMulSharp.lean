import Mathlib
import Submission.Work.NN.Core.contDiff_flatMul

/-!
# Flat functions times `C^k` functions: the sharp form

`Work.NN.Core.flatMulSharp` is the sharp form of `Work.NN.Core.contDiff_flatMul`: the
regularity hypothesis on `u` is exactly the level of the conclusion (only `C^m`, not `C^{m+1}`),
with the `C^{m,α}` Hölder norm finite there.  The same proof as in
`Submission.Work.NN.Core.contDiff_flatMul` works verbatim: the master Leibniz estimate needs the
orders of `u` and of its Hölder norm to be *equal* (both `m`), not the extra order that
`contDiff_flatMul` asks for, so we re-run the argument with that bookkeeping corrected.
-/

noncomputable section

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff Classical
open Set

/-! ## The master estimate (sharp form) -/

theorem flatMul_iteratedFDerivWithin_bound_sharp {n : ℕ} {k : ℕ} {α : ℝ} {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j)
    {v : (Fin n → ℂ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → v z = 0)
    {u : (Fin n → ℂ) → ℂ}
    (hu : ContDiffOn ℝ (((k : ℕ)) : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ))
    (huf : Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤)
    {m : ℕ} (hm : m ≤ k) {x₀ : Fin n → ℂ} (hx₀ : x₀ ∉ Work.CR.Flat.polydisc 0 ρ) (N : ℕ) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ y : Fin n → ℂ, ‖y - x₀‖ < δ →
      ‖(if y ∈ Work.CR.Flat.polydisc 0 ρ then
          iteratedFDerivWithin ℝ m (fun z => v z * u z) (Work.CR.Flat.polydisc 0 ρ) y
        else 0)‖ ≤ C * ‖y - x₀‖ ^ N := by
  classical
  set Ω : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ with hΩ
  have hΩopen : IsOpen Ω := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hΩuniq : UniqueDiffOn ℝ Ω := hΩopen.uniqueDiffOn
  obtain ⟨Cu, hCunn, huC⟩ := exists_iteratedFDerivWithin_bound_of_holderNorm_ne_top huf
  have hvflat : ∀ i : ℕ, iteratedFDeriv ℝ i v x₀ = 0 :=
    fun i => iteratedFDeriv_eq_zero_of_notMem_polydisc hρ hv hv0 hx₀ i
  choose Cv δv hCv hδv hbnd using fun i : ℕ => flat_iteratedFDeriv_bound hv x₀ hvflat i N
  set δ : ℝ := (Finset.range (m + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩ δv with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact (Finset.lt_inf'_iff _).mpr fun i _ => hδv i
  have hδle : ∀ i ∈ Finset.range (m + 1), δ ≤ δv i := fun i hi => by
    rw [hδdef]
    exact Finset.inf'_le δv hi
  set C : ℝ := (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Cv i) * Cu with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCv i)) hCunn
  have hvΩ : ContDiffOn ℝ (((k : ℕ)) : ℕ∞) v Ω :=
    (hv.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have huΩ : ContDiffOn ℝ (((k : ℕ)) : ℕ∞) u Ω := hu
  refine ⟨C, δ, hCnn, hδpos, fun y hy => ?_⟩
  by_cases hyΩ : y ∈ Ω
  · rw [ite_eq_left hyΩ]
    refine le_trans (norm_iteratedFDerivWithin_mul_le (s := Ω) (A := ℂ) (f := v) (g := u)
      (N := (((k : ℕ)) : ℕ∞)) hvΩ huΩ hΩuniq hyΩ
      (show (((m : ℕ)) : ℕ∞ω) ≤ (((k : ℕ)) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hm))) ?_
    calc (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i v Ω y‖ * ‖iteratedFDerivWithin ℝ (m - i) u Ω y‖)
        ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Cv i * Cu * ‖y - x₀‖ ^ N :=
          Finset.sum_le_sum fun i hi => ?_
      _ = C * ‖y - x₀‖ ^ N := by
          rw [hCdef, ← Finset.sum_mul, ← Finset.sum_mul]
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hik : i ≤ k := le_trans him hm
    have hmi : m - i ≤ k := le_trans (Nat.sub_le m i) hm
    have hvbound : ‖iteratedFDerivWithin ℝ i v Ω y‖ ≤ Cv i * ‖y - x₀‖ ^ N := by
      rw [(iteratedFDerivWithin_of_isOpen (s := Ω) i hΩopen) hyΩ]
      exact hbnd i y (lt_of_lt_of_le hy (hδle i hi))
    have hubound : ‖iteratedFDerivWithin ℝ (m - i) u Ω y‖ ≤ Cu := huC (m - i) hmi y hyΩ
    calc (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i v Ω y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) u Ω y‖
        ≤ (m.choose i : ℝ) * (Cv i * ‖y - x₀‖ ^ N) * Cu :=
          mul_le_mul (mul_le_mul_of_nonneg_left hvbound (Nat.cast_nonneg _)) hubound
            (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hCv i) (pow_nonneg (norm_nonneg _) N)))
      _ = (m.choose i : ℝ) * Cv i * Cu * ‖y - x₀‖ ^ N := by ring
  · rw [ite_eq_right hyΩ]
    simp only [norm_zero]
    exact mul_nonneg hCnn (pow_nonneg (norm_nonneg _) N)

/-! ## The main theorem (sharp form) -/

theorem contDiff_flatMul_of_smooth_sharp {n : ℕ} {k : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {v : Work.NN.Core.Cn n → ℂ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → v z = 0)
    {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ (((k : ℕ)) : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ))
    (huf : Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤) :
    ContDiff ℝ k (fun z => v z * u z) := by
  classical
  set Ω : Set (Work.NN.Core.Cn n) := Work.CR.Flat.polydisc 0 ρ with hΩ
  have hΩopen : IsOpen Ω := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hΩuniq : UniqueDiffOn ℝ Ω := hΩopen.uniqueDiffOn
  have hv0' : ∀ z ∉ Ω, v z = 0 := fun z hz =>
    hv0 z (by
      by_contra h
      push Not at h
      exact hz (by rw [Work.CR.Flat.mem_polydisc]; exact fun i => by simpa using h i))
  -- smoothness of the pieces on the polydisc
  have hk : (((k : ℕ)) : ℕ∞) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
  have hvΩ : ContDiffOn ℝ (((k : ℕ)) : ℕ∞) v Ω := (hv.of_le hk).contDiffOn
  have hwΩ : ContDiffOn ℝ (((k : ℕ)) : ℕ∞) (fun z => v z * u z) Ω := hvΩ.mul hu
  -- the candidate Taylor family: the within-derivatives on the polydisc, extended by `0`
  set p : Work.NN.Core.Cn n → FormalMultilinearSeries ℝ (Work.NN.Core.Cn n) ℂ :=
    fun x m => if x ∈ Ω then iteratedFDerivWithin ℝ m (fun z => v z * u z) Ω x else 0 with hp
  have hp_pos : ∀ x ∈ Ω, ∀ m, p x m = iteratedFDerivWithin ℝ m (fun z => v z * u z) Ω x :=
    fun x hx m => by simp only [hp]; exact ite_eq_left hx
  have hp_neg : ∀ x ∉ Ω, ∀ m, p x m = 0 := fun x hx m => by simp only [hp]; exact ite_eq_right hx
  have hzero : ∀ x, (p x 0).curry0 = (fun z => v z * u z) x := by
    intro x
    by_cases hx : x ∈ Ω
    · rw [hp_pos x hx 0]
      simp [ContinuousMultilinearMap.curry0_apply, iteratedFDerivWithin_zero_apply]
    · rw [hp_neg x hx 0]
      simp only [ContinuousMultilinearMap.curry0_apply, zero_apply]
      rw [show v x = 0 from hv0' x hx, zero_mul]
  have hfderiv : ∀ m : ℕ, m < (((k : ℕ)) : ℕ∞ω) → ∀ x,
      HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x := by
    intro m hm x
    have hmk : m < k := by exact_mod_cast hm
    by_cases hx : x ∈ Ω
    · have hFTS := hwΩ.ftaylorSeriesWithin hΩuniq
      have hfd := hFTS.fderivWithin m (by exact_mod_cast hmk) x hx
      have h2 : HasFDerivAt (fun y => iteratedFDerivWithin ℝ m (fun z => v z * u z) Ω y)
          ((p x m.succ).curryLeft) x := by
        have h3 : (iteratedFDerivWithin ℝ (m + 1) (fun z => v z * u z) Ω x).curryLeft
            = (p x m.succ).curryLeft := by
          rw [hp_pos x hx m.succ]
        rw [← h3]
        exact hfd.hasFDerivAt (hΩopen.mem_nhds hx)
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [hΩopen.mem_nhds hx] with y hy
      exact hp_pos y hy m
    · rw [hp_neg x hx m.succ]
      have hzero' : (0 : ContinuousMultilinearMap ℝ
          (fun _ : Fin (m + 1) => Work.NN.Core.Cn n) ℂ).curryLeft = 0 := by
        ext v w
        simp [ContinuousMultilinearMap.curryLeft_apply]
      rw [hzero', hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
      intro c hc
      obtain ⟨C, δ, hCnn, hδ, hbound⟩ :=
        flatMul_iteratedFDerivWithin_bound_sharp hρ hv hv0 hu huf (le_of_lt hmk) hx 2
      have hA : 0 < min δ (c / (C + 1)) := lt_min hδ (div_pos hc (by linarith))
      filter_upwards [Metric.ball_mem_nhds x hA] with y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have hyδ : ‖y - x‖ < δ := lt_of_lt_of_le hy (min_le_left _ _)
      have hyc : ‖y - x‖ < c / (C + 1) := lt_of_lt_of_le hy (min_le_right _ _)
      have hbd : ‖p y m‖ ≤ C * ‖y - x‖ ^ 2 := by
        rw [hp]
        exact hbound y hyδ
      have hx0 : p x m = 0 := hp_neg x hx m
      rw [hx0]
      simp only [zero_apply, sub_zero]
      calc ‖p y m‖ ≤ C * ‖y - x‖ ^ 2 := hbd
        _ = C * ‖y - x‖ * ‖y - x‖ := by rw [pow_two]; ring
        _ ≤ c * ‖y - x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            have hpos : 0 ≤ c / (C + 1) := div_nonneg hc.le (by linarith)
            calc C * ‖y - x‖ ≤ C * (c / (C + 1)) := mul_le_mul_of_nonneg_left hyc.le hCnn
              _ ≤ (C + 1) * (c / (C + 1)) := mul_le_mul_of_nonneg_right (by linarith) hpos
              _ = c := by
                  rw [show (C + 1) * (c / (C + 1)) = c * (C + 1) / (C + 1) by ring,
                    mul_div_cancel_right₀ c (by linarith : (C + 1) ≠ 0)]
  have hcont : ∀ m : ℕ, m ≤ (((k : ℕ)) : ℕ∞ω) → Continuous fun x => p x m := by
    intro m hm
    have hmk : m ≤ k := by exact_mod_cast hm
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ Ω
    · have hcontΩ : ContinuousOn
          (fun y => iteratedFDerivWithin ℝ m (fun z => v z * u z) Ω y) Ω :=
        hwΩ.continuousOn_iteratedFDerivWithin hm hΩuniq
      refine (hcontΩ.continuousAt (hΩopen.mem_nhds hx)).congr ?_
      filter_upwards [hΩopen.mem_nhds hx] with y hy
      exact (hp_pos y hy m).symm
    · have hx0 : p x m = 0 := hp_neg x hx m
      rw [ContinuousAt, hx0]
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨C, δ, hCnn, hδ, hbound⟩ :=
        flatMul_iteratedFDerivWithin_bound_sharp hρ hv hv0 hu huf hmk hx 1
      have hA : 0 < min δ (ε / (2 * (C + 1))) :=
        lt_min hδ (div_pos (by linarith) (by linarith))
      filter_upwards [Metric.ball_mem_nhds x hA] with y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have hyδ : ‖y - x‖ < δ := lt_of_lt_of_le hy (min_le_left _ _)
      have hyε : ‖y - x‖ < ε / (2 * (C + 1)) := lt_of_lt_of_le hy (min_le_right _ _)
      have hbd : ‖p y m‖ ≤ C * ‖y - x‖ := by
        have h := hbound y hyδ
        rw [pow_one] at h
        exact h
      rw [dist_eq_norm, sub_zero]
      have h3 : C * ‖y - x‖ ≤ ε / 2 := by
        have hpos : 0 ≤ ε / (2 * (C + 1)) := div_nonneg hε.le (by linarith)
        calc C * ‖y - x‖ ≤ C * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hyε.le hCnn
          _ ≤ (C + 1) * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_right (by linarith) hpos
          _ = ε / 2 := by
              rw [show (C + 1) * (ε / (2 * (C + 1))) = ε * (C + 1) / (2 * (C + 1)) by ring,
                mul_div_mul_right ε 2 (by linarith : (C + 1) ≠ 0)]
      linarith
  exact HasFTaylorSeriesUpTo.contDiff ⟨hzero, hfderiv, hcont⟩


/-- **The requested statement.**  Same as `contDiff_flatMul` but with the regularity hypothesis
`ContDiffOn ℝ m u` at exactly the level `m` of the conclusion; the extra `+1` in
`contDiff_flatMul` is not needed. -/
theorem flatMulSharp {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {v : (Fin n → ℂ) → ℂ} (hv : ContDiff ℝ ⊤ v)
    (hv0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → v z = 0)
    {u : (Fin n → ℂ) → ℂ} {m : ℕ} {α : ℝ}
    (hu : ContDiffOn ℝ (m : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ))
    (huf : Work.CR.Flat.holderNorm m α u (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤) :
    ContDiff ℝ m (fun z => v z * u z) :=
  contDiff_flatMul_of_smooth_sharp hρ (hv.of_le le_top) hv0 hu huf

end Work.NN.Core
