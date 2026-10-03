import Mathlib
import Submission.Work.L62.l62c_end
import Submission.Work.L62.tail_of_branch
import Submission.Work.L62.tail_of_branch_lower
import Submission.Work.L62.perturbed_branch
import Submission.Work.L62.perturbed_branch_lower
import Submission.Work.L62.lift_fatou
import Submission.Work.L62.periodic_decay_up
import Submission.Work.L62.periodic_decay_low
import Submission.Work.L62.branch_at_depth_up
import Submission.Work.L62.branch_at_depth_low
import Submission.Work.L62.fatou_coord_fix
import Submission.Work.L62.fatou_of_decay_low
import Submission.Work.L62.tail_lin_up
import Submission.Work.L62.tail_lin_low
import Submission.Work.L62.num_shift

namespace Work.L62

open MandelDim

/-- The upper-end filter is nontrivial. -/
private lemma neBot_upperEnd : (Filter.comap Complex.im Filter.atTop).NeBot :=
  Filter.comap_neBot fun t ht => by
    obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.mp ht
    exact ⟨(a : ℂ) * Complex.I, ha _ (by simp [Complex.mul_im])⟩

/-- The lower-end filter is nontrivial. -/
private lemma neBot_lowerEnd : (Filter.comap Complex.im Filter.atBot).NeBot :=
  Filter.comap_neBot fun t ht => by
    obtain ⟨a, ha⟩ := Filter.mem_atBot_sets.mp ht
    exact ⟨(a : ℂ) * Complex.I, ha _ (by simp [Complex.mul_im])⟩

/-- A point of the box `{0 ≤ re ≤ 1, |im| ≤ b}` has norm at most `1 + b`. -/
private lemma norm_le_one_add_of_box {β : ℂ} {b : ℝ} (h1 : 0 ≤ β.re) (h2 : β.re ≤ 1)
    (h3 : |β.im| ≤ b) : ‖β‖ ≤ 1 + b := by
  have h := norm_add_le (β.re : ℂ) ((β.im : ℂ) * Complex.I)
  have heq : (β.re : ℂ) + (β.im : ℂ) * Complex.I = β := Complex.re_add_im β
  rw [heq] at h
  have h5 : ‖β‖ ≤ |β.re| + |β.im| := by simpa using h
  have h4 : |β.re| ≤ 1 := by rw [abs_of_nonneg h1]; exact h2
  linarith

theorem tail_uniform3 {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b κ : ℝ} (hb : 0 < b) (hκ : 0 < κ) {cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl)) :
    ∃ (Y δt C₀ C₂ C₂' : ℝ), d.η₀ + 2 < Y ∧ 0 < δt ∧ 0 < C₀ ∧ 0 < C₂ ∧ 0 < C₂' ∧
      ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b → ∀ s : ℝ,
        ((s = 1 ∧ Work.L62.AvailableUp d hd β ∧ κ ≤ β.im) ∨
          (s = -1 ∧ Work.L62.AvailableDown d hd β ∧ κ ≤ cl.im - β.im)) →
        ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR → MandelDim.IsTEquivariantOn R DR →
          DifferentiableOn ℂ R DR → {w : ℂ | Y - 1 ≤ |w.im|} ⊆ DR →
          (∀ w : ℂ, Y - 1 ≤ |w.im| → ‖R w - d.E w‖ < δt) →
          ∀ W₀ : Set ℂ, IsOpen W₀ → IsConnected W₀ → Bornology.IsBounded W₀ →
            Metric.diam W₀ ≤ 1 / 24 → 3 * Metric.diam W₀ < κ / 4 →
            (∀ u ∈ W₀, Y < s * u.im) →
            ∃ V : ℕ → Set ℂ, V 0 = W₀ ∧ ∀ j : ℕ,
              IsOpen (V j) ∧ IsConnected (V j) ∧ V (j + 1) ⊆ DR ∧
              Set.InjOn (fun u => R u - β) (V (j + 1)) ∧
              (fun u => R u - β) '' V (j + 1) = V j ∧
              (∀ u ∈ V j, Y + (j : ℝ) * κ / 8 < s * u.im) ∧
              Bornology.IsBounded (V j) ∧ Metric.diam (V j) < 1 / 2 ∧
              (∃ u ∈ V j, ∃ u' ∈ V (j + 1), ‖u - u'‖ < C₀) ∧
              (∀ i j : ℕ, i ≠ j → Disjoint (MandelDim.piExp '' V i) (MandelDim.piExp '' V j)) ∧
              (∀ u ∈ V j, C₂ < ‖deriv ((fun u => R u - β)^[j]) u‖ ∧
                ‖deriv ((fun u => R u - β)^[j]) u‖ < C₂') := by
  classical
  -- ## the smallness parameter `δt`
  set δt : ℝ := min (κ / 1000) (1 / 1000) with hδtdef
  have hδtpos : 0 < δt := by
    rw [hδtdef]; exact lt_min (by linarith) (by norm_num)
  have hδt0 : 0 ≤ δt := hδtpos.le
  have hδt1000 : δt ≤ κ / 1000 := by rw [hδtdef]; exact min_le_left _ _
  have hδt1 : δt ≤ 1 / 1000 := by rw [hδtdef]; exact min_le_right _ _
  have hδtκ16 : δt ≤ κ / 16 := by
    have h : κ / 1000 ≤ κ / 16 := by linarith
    exact le_trans hδt1000 h
  have hδt8 : δt ≤ 1 / 8 := by linarith
  have hδtmin : δt ≤ min (κ / 16) (1 / 8) := le_min hδtκ16 hδt8
  -- ## the depth thresholds
  obtain ⟨y₀u, hbu⟩ := branch_at_depth_up d hd hκ hδtpos hδtmin
  obtain ⟨y₀l, hbl⟩ := branch_at_depth_low d hd hcl hκ hδtpos hδtmin
  set Y : ℝ := max (d.η₀ + 3) (max (y₀u + 1) (y₀l + 1)) with hYdef
  have hYη : d.η₀ + 2 < Y := by
    have h := le_max_left (d.η₀ + 3) (max (y₀u + 1) (y₀l + 1))
    rw [hYdef]; linarith
  have hYu : y₀u + 1 ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hYl : y₀l + 1 ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Y, δt, 1 + b + ‖cl‖ + κ / 4 + 2, 1 / 3, 3, hYη, hδtpos, ?_, by norm_num, by norm_num, ?_⟩
  · have h := norm_nonneg cl; linarith
  -- ## the main statement
  intro β hβre0 hβre1 hβim s hs R DR hDRo hTeq hRd hDRsub hclose W₀ hW₀o hW₀c hW₀b hW₀diam hκdiam hW₀im
  have hβnorm : ‖β‖ ≤ 1 + b := norm_le_one_add_of_box hβre0 hβre1 hβim
  haveI : (Filter.comap Complex.im Filter.atTop).NeBot := neBot_upperEnd
  haveI : (Filter.comap Complex.im Filter.atBot).NeBot := neBot_lowerEnd
  rcases hs with ⟨rfl, _, hβκ⟩ | ⟨rfl, _, hκcl⟩
  · -- ================= s = 1 : the upper end =================
    have hyu : y₀u ≤ Y - 1 / 2 := by linarith
    -- the branch at depth `Y - 1/2`
    have hDRsub1 : {w : ℂ | (Y - 1 / 2) - 1 / 2 < w.im} ⊆ DR := by
      intro w hw
      rw [Set.mem_ofPred_eq] at hw
      apply hDRsub
      have h1 : Y - 1 < w.im := by linarith
      exact le_trans (le_of_lt h1) (le_abs_self w.im)
    have hclose1 : ∀ w : ℂ, (Y - 1 / 2) - 1 / 2 < w.im → ‖R w - d.E w‖ ≤ δt := by
      intro w hw
      refine le_of_lt (hclose w ?_)
      have h1 : Y - 1 < w.im := by linarith
      exact le_trans (le_of_lt h1) (le_abs_self w.im)
    obtain ⟨H, ρ, c, hHd, hHmem, hρd, hρper, hρbd, hdrift, hInj, hρlim⟩ :=
      hbu (Y - 1 / 2) hyu β hβκ R DR hDRo hTeq hRd hDRsub1 hclose1
    -- restrict to the half-plane `{Y < Im}`
    have hyY : Y - 1 / 2 < Y := by linarith
    have hh : ∀ w : ℂ, Y < w.im → Y - 1 / 2 < w.im := fun w hw => lt_trans hyY hw
    have hHd' : DifferentiableOn ℂ H {w : ℂ | Y < w.im} := hHd.mono fun w hw => hh w hw
    have hρd' : DifferentiableOn ℂ ρ {w : ℂ | Y < w.im} := hρd.mono fun w hw => hh w hw
    have hHmap : ∀ w : ℂ, Y - 1 / 2 < w.im → Y - 1 / 2 < (H w).im :=
      fun w hw => (hHmem w hw).1
    have hinc'' : ∀ w : ℂ, Y - 1 / 2 < w.im → H w = w + β + ρ w :=
      fun w hw => (hHmem w hw).2.2.2
    have hHmem' : ∀ w : ℂ, Y < w.im → Y < (H w).im ∧ H w ∈ DR ∧ R (H w) - β = w := by
      intro w hw
      obtain ⟨h1, h2, h3, -⟩ := hHmem w (hh w hw)
      refine ⟨?_, h2, h3⟩
      have h4 := hdrift w (hh w hw)
      have h5 : (H w - w).im = (H w).im - w.im := Complex.sub_im _ _
      linarith
    have hinc' : ∀ w : ℂ, Y < w.im → H w = w + β + ρ w := fun w hw => hinc'' w (hh w hw)
    have hdrift' : ∀ w : ℂ, Y < w.im → κ / 4 ≤ (H w - w).im := fun w hw => hdrift w (hh w hw)
    have hρbd' : ∀ w : ℂ, Y < w.im → ‖ρ w‖ ≤ (κ / 4) / 4 := by
      intro w hw
      have h1 := hρbd w (hh w hw)
      have h2 : 2 * δt ≤ κ / 16 := by linarith
      have h3 : (κ / 4) / 4 = κ / 16 := by ring
      linarith
    -- the amplitude of `ρ - c` and the Fatou coordinate
    have hcbd : ‖c‖ ≤ 2 * δt := by
      have h1 : Filter.Tendsto (fun w : ℂ => ‖ρ w‖) (Filter.comap Complex.im Filter.atTop)
          (nhds ‖c‖) := hρlim.norm
      refine le_of_tendsto h1 ?_
      rw [Filter.eventually_iff, Filter.mem_comap]
      exact ⟨Set.Ioi (Y - 1 / 2), Filter.Ioi_mem_atTop _, fun w hw => hρbd w hw⟩
    have hψbd : ∀ w : ℂ, Y - 1 / 2 < w.im → ‖ρ w - c‖ ≤ 4 * δt := by
      intro w hw
      have h1 := hρbd w hw
      calc ‖ρ w - c‖ ≤ ‖ρ w‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ 2 * δt + 2 * δt := by linarith
        _ = 4 * δt := by ring
    have hdec : ∀ w : ℂ, Y - 1 / 2 < w.im →
        ‖ρ w - c‖ ≤ (4 * δt) * Real.exp (-2 * Real.pi * (w.im - (Y - 1 / 2))) := by
      refine periodic_decay_up (ψ := fun w => ρ w - c) (y := Y - 1 / 2) (M := 4 * δt)
        (by linarith) (hρd.sub_const c) ?_ hψbd ?_
      · intro w hw
        show ρ (w + 1) - c = ρ w - c
        rw [hρper w hw]
      · simpa using hρlim.sub_const c
    have hnum : 2 * (4 * δt) * Real.exp (-2 * Real.pi * (Y - (Y - 1 / 2) - 1 / 2)) /
        (1 - Real.exp (-2 * Real.pi * (κ / 4))) ≤ 1 / 2 := by
      have h0 : Y - (Y - 1 / 2) - 1 / 2 = 0 := by ring
      have h8 : 2 * (4 * δt) = 8 * δt := by ring
      have hexp : Real.exp (-2 * Real.pi * (Y - (Y - 1 / 2) - 1 / 2)) = 1 := by
        rw [h0, mul_zero, Real.exp_zero]
      rw [hexp, mul_one, h8]
      exact num_shift hκ hδt0 hδt1000 hδt1
    obtain ⟨L, hL⟩ := fatou_of_decay_up (y := Y - 1 / 2) (Y := Y) (κ := κ / 4) (M := 4 * δt)
      (by linarith) (by linarith) (by linarith) hHd hHmap hinc'' hρd hdec hdrift hnum
    have hL' : ∀ w : ℂ, Y < w.im → DifferentiableAt ℂ L w ∧ L (H w) = L w + (β + c) ∧
        ‖deriv L w - 1‖ ≤ 1 / 2 := by
      intro w hw
      obtain ⟨h1, h2, -, h4⟩ := hL w hw
      exact ⟨h1, h2, h4⟩
    have hW₀sub' : W₀ ⊆ {w : ℂ | Y < w.im} := by
      intro u hu
      have h := hW₀im u hu
      simpa using h
    -- the tail
    obtain ⟨V, hV0, hopen, hchain, hdisj, hbdd, hcloseC, hlin, hderiv⟩ :=
      tail_lin_up (R := R) (β := β) (DR := DR) (κ := κ / 4) (by linarith) (y' := Y) (a := β + c)
        hHd' hinc' hρd' hρbd' hHmem' hdrift' hL' hW₀o hW₀c hW₀sub' hW₀b hW₀diam hκdiam
    refine ⟨V, hV0, fun j => ?_⟩
    obtain ⟨h1, h2⟩ := hopen j
    obtain ⟨h3, h4, h5⟩ := hchain j
    obtain ⟨h6, h7⟩ := hbdd j
    obtain ⟨u, hu, u', hu', hlt⟩ := hcloseC j
    refine ⟨h1, h2, h3, h4, h5, ?_, h6, h7, ⟨u, hu, u', hu', ?_⟩, hdisj, ?_⟩
    · intro v hv
      show Y + (j : ℝ) * κ / 8 < 1 * v.im
      rw [one_mul]
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        rw [hV0] at hv
        simpa using hW₀im v hv
      · have h1 := hlin j v hv
        have hj : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
        nlinarith [h1, hκ, hj]
    · have h1 : (κ / 4) / 4 = κ / 16 := by ring
      have h2 : ‖β‖ + κ / 16 + 1 < 1 + b + ‖cl‖ + κ / 4 + 2 := by
        have h3 := norm_nonneg cl
        linarith
      linarith
    · intro v hv
      exact hderiv j v hv
  · -- ================= s = -1 : the lower end =================
    have hyl : y₀l ≤ Y - 1 / 2 := by linarith
    have hDRsub1 : {w : ℂ | w.im < -((Y - 1 / 2) - 1 / 2)} ⊆ DR := by
      intro w hw
      rw [Set.mem_ofPred_eq] at hw
      apply hDRsub
      have h1 : w.im < -(Y - 1) := by linarith
      have h2 : Y - 1 < -w.im := by linarith
      exact le_trans (le_of_lt h2) (neg_le_abs w.im)
    have hclose1 : ∀ w : ℂ, w.im < -((Y - 1 / 2) - 1 / 2) → ‖R w - d.E w‖ ≤ δt := by
      intro w hw
      refine le_of_lt (hclose w ?_)
      have h1 : w.im < -(Y - 1) := by linarith
      have h2 : Y - 1 < -w.im := by linarith
      exact le_trans (le_of_lt h2) (neg_le_abs w.im)
    obtain ⟨H, ρ, c, hHd, hHmem, hρd, hρper, hρbd, hdrift, hInj, hρlim⟩ :=
      hbl (Y - 1 / 2) hyl β hκcl R DR hDRo hTeq hRd hDRsub1 hclose1
    -- restrict to the half-plane `{Im < -Y}`
    have hh : ∀ w : ℂ, w.im < -Y → w.im < -(Y - 1 / 2) := by intro w hw; linarith
    have hHd' : DifferentiableOn ℂ H {w : ℂ | w.im < -Y} := hHd.mono fun w hw => hh w hw
    have hρd' : DifferentiableOn ℂ ρ {w : ℂ | w.im < -Y} := hρd.mono fun w hw => hh w hw
    have hHmap : ∀ w : ℂ, w.im < -(Y - 1 / 2) → (H w).im < -(Y - 1 / 2) :=
      fun w hw => (hHmem w hw).1
    have hinc'' : ∀ w : ℂ, w.im < -(Y - 1 / 2) → H w = w + (β - cl) + ρ w :=
      fun w hw => (hHmem w hw).2.2.2
    have hHmem' : ∀ w : ℂ, w.im < -Y → (H w).im < -Y ∧ H w ∈ DR ∧ R (H w) - β = w := by
      intro w hw
      obtain ⟨h1, h2, h3, -⟩ := hHmem w (hh w hw)
      refine ⟨?_, h2, h3⟩
      have h4 := hdrift w (hh w hw)
      have h5 : (H w - w).im = (H w).im - w.im := Complex.sub_im _ _
      linarith
    have hinc' : ∀ w : ℂ, w.im < -Y → H w = w + (β - cl) + ρ w := fun w hw => hinc'' w (hh w hw)
    have hdrift' : ∀ w : ℂ, w.im < -Y → (H w - w).im ≤ -(κ / 4) := fun w hw => hdrift w (hh w hw)
    have hρbd' : ∀ w : ℂ, w.im < -Y → ‖ρ w‖ ≤ (κ / 4) / 4 := by
      intro w hw
      have h1 := hρbd w (hh w hw)
      have h2 : 2 * δt ≤ κ / 16 := by linarith
      have h3 : (κ / 4) / 4 = κ / 16 := by ring
      linarith
    have hcbd : ‖c‖ ≤ 2 * δt := by
      have h1 : Filter.Tendsto (fun w : ℂ => ‖ρ w‖) (Filter.comap Complex.im Filter.atBot)
          (nhds ‖c‖) := hρlim.norm
      refine le_of_tendsto h1 ?_
      rw [Filter.eventually_iff, Filter.mem_comap]
      exact ⟨Set.Iio (-(Y - 1 / 2)), Filter.Iio_mem_atBot _, fun w hw => hρbd w hw⟩
    have hψbd : ∀ w : ℂ, w.im < -(Y - 1 / 2) → ‖ρ w - c‖ ≤ 4 * δt := by
      intro w hw
      have h1 := hρbd w hw
      calc ‖ρ w - c‖ ≤ ‖ρ w‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ 2 * δt + 2 * δt := by linarith
        _ = 4 * δt := by ring
    have hdec : ∀ w : ℂ, w.im < -(Y - 1 / 2) →
        ‖ρ w - c‖ ≤ (4 * δt) * Real.exp (-2 * Real.pi * (-(Y - 1 / 2) - w.im)) := by
      refine periodic_decay_low (ψ := fun w => ρ w - c) (y := Y - 1 / 2) (M := 4 * δt)
        (by linarith) (hρd.sub_const c) ?_ hψbd ?_
      · intro w hw
        show ρ (w + 1) - c = ρ w - c
        rw [hρper w hw]
      · simpa using hρlim.sub_const c
    have hnum : 2 * (4 * δt) * Real.exp (-2 * Real.pi * (Y - (Y - 1 / 2) - 1 / 2)) /
        (1 - Real.exp (-2 * Real.pi * (κ / 4))) ≤ 1 / 2 := by
      have h0 : Y - (Y - 1 / 2) - 1 / 2 = 0 := by ring
      have h8 : 2 * (4 * δt) = 8 * δt := by ring
      have hexp : Real.exp (-2 * Real.pi * (Y - (Y - 1 / 2) - 1 / 2)) = 1 := by
        rw [h0, mul_zero, Real.exp_zero]
      rw [hexp, mul_one, h8]
      exact num_shift hκ hδt0 hδt1000 hδt1
    obtain ⟨L, hL⟩ := fatou_of_decay_low (y := Y - 1 / 2) (Y := Y) (κ := κ / 4) (M := 4 * δt)
      (by linarith) (by linarith) (by linarith) hHd hHmap hinc'' hρd hdec hdrift hnum
    have hL' : ∀ w : ℂ, w.im < -Y → DifferentiableAt ℂ L w ∧ L (H w) = L w + ((β - cl) + c) ∧
        ‖deriv L w - 1‖ ≤ 1 / 2 := by
      intro w hw
      obtain ⟨h1, h2, -, h4⟩ := hL w hw
      exact ⟨h1, h2, h4⟩
    have hW₀sub' : W₀ ⊆ {w : ℂ | w.im < -Y} := by
      intro u hu
      have h := hW₀im u hu
      have h2 : (-1 : ℝ) * u.im = -u.im := by ring
      rw [h2] at h
      show u.im < -Y
      linarith
    obtain ⟨V, hV0, hopen, hchain, hdisj, hbdd, hcloseC, hlin, hderiv⟩ :=
      tail_lin_low (R := R) (β := β) (γ := β - cl) (DR := DR) (κ := κ / 4) (by linarith)
        (y' := Y) (a := (β - cl) + c)
        hHd' hinc' hρd' hρbd' hHmem' hdrift' hL' hW₀o hW₀c hW₀sub' hW₀b hW₀diam hκdiam
    refine ⟨V, hV0, fun j => ?_⟩
    obtain ⟨h1, h2⟩ := hopen j
    obtain ⟨h3, h4, h5⟩ := hchain j
    obtain ⟨h6, h7⟩ := hbdd j
    obtain ⟨u, hu, u', hu', hlt⟩ := hcloseC j
    refine ⟨h1, h2, h3, h4, h5, ?_, h6, h7, ⟨u, hu, u', hu', ?_⟩, hdisj, ?_⟩
    · intro v hv
      show Y + (j : ℝ) * κ / 8 < -1 * v.im
      have h2 : (-1 : ℝ) * v.im = -v.im := by ring
      rw [h2]
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        rw [hV0] at hv
        have h3 := hW₀im v hv
        have h4 : (-1 : ℝ) * v.im = -v.im := by ring
        rw [h4] at h3
        simpa using h3
      · have h1 := hlin j v hv
        have hj : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
        nlinarith [h1, hκ, hj]
    · have h1 : (κ / 4) / 4 = κ / 16 := by ring
      have h2 : ‖β - cl‖ ≤ ‖β‖ + ‖cl‖ := norm_sub_le _ _
      have h3 : ‖β‖ + ‖cl‖ + κ / 16 + 1 < 1 + b + ‖cl‖ + κ / 4 + 2 := by linarith
      linarith
    · intro v hv
      exact hderiv j v hv

end Work.L62
