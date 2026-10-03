import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.exists_model_data_full
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic
-- the `PinLogDev` toolkit (`deltaF`, `modelA`, `modelDelta`, the gate geometry, the pieces)
import Submission.Work.Pert.PinLogDev.Setup
import Submission.Work.Pert.PinLogDev.u_close_hF
import Submission.Work.Pert.PinLogDev.delta_model_taylor
import Submission.Work.Pert.PinLogDev.tauC_primitive
import Submission.Work.Pert.PinAux.tauC_norm_mul_exp_le
import Submission.Work.Pert.Pin3.pin_data
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.Pin3.dev_vert_log
import Submission.Work.Pert.Pin3.dev_vert_log_neg
import Submission.Work.Pert.Pin3.dev_horiz_log
import Submission.Work.Pert.PinLogDev.AnchorWalk
import Submission.Work.Pert.PinLogDev.anchor_walk
import Submission.Work.Pert.PinLogDev.tauC_sub_tau0_alpha
import Submission.Work.Pert.PinLogDev.liftF_sub_model_le_pointwise_wide
import Submission.Work.Pert.PinLogDev.u_sub_hF_le_rho
import Submission.Work.Pert.PinLogDev.anchor_transport
import Submission.Work.Pert.PinLogDev.axis_decay_budget
import Submission.Work.Pert.PinLogDev.anchor_to_all_t_const
import Submission.Work.Pert.PinLogDev.anchor_point_bound2
import Submission.Work.Pert.PinLogDev.axis_decay_budget2
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.PinLogDev.anchor_to_all_t
import Submission.Work.Pert.PinLogDev.deltaF_axis_le
import Submission.Work.Pert.PinAux.dev_axis_transport
import Submission.Work.Pert.count_gate_walk_close

/-!
See `Submission/Work/Pert/PinLogDev/NOTES.md` for the route of the proof (the exact primitive of
`tauC` cancels the logarithmic divergences of the pin and of the path integral; the `t/64` slack
absorbs the deep-end drift) and for the list of corrected statements.
-/

namespace Work.Pert.PinLogDev

set_option maxHeartbeats 4000000

open Complex Metric Filter

/-! ## Auxiliary lemmas for the (new) route to `anchor_dev_le`

See `NOTES_new_route.md`: the pin is at `z_pin = Xc d (−M)`, the telescoping runs along the
`F0f`-walk `X j = Xc d (−M + j)` (`Xc d (u+1) = F0f (Xc d u)`), and the deviation at the anchor
`± i Y₀` is reached through the comparison of `F` with the limit model `F0f f₀`. -/

/-- **Telescoping of the deviation along a `G`-walk.**  If `Φ` is a Fatou coordinate for `F` on
`Q` (i.e. `Φ (F z) = Φ z + 1` for `z, F z ∈ Q`) and `X (j+1) = G (X j)` with `X j, F (X j) ∈ Q`
for `j < n`, then

  `Φ (X n) = Φ (X 0) + n + ∑_{j<n} (Φ (G (X j)) - Φ (F (X j)))`.

This is the exact identity used by the walk: the summand is the *model comparison error* of the
`j`-th step, so the deviation of the pinned coordinate at `X n` is `Φ (X 0) + n - X n` plus the
accumulated comparison errors. -/
theorem anchor_walk_telescope {F G Φ : ℂ → ℂ} {Q : Set ℂ} {X : ℕ → ℂ} {n : ℕ}
    (hab : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hXQ : ∀ j, j ≤ n → X j ∈ Q)
    (hXFQ : ∀ j, j < n → F (X j) ∈ Q)
    (hstep : ∀ j, j < n → X (j + 1) = G (X j)) :
    Φ (X n) = Φ (X 0) + (n : ℂ) +
      ∑ j ∈ Finset.range n, (Φ (G (X j)) - Φ (F (X j))) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hXQ' : ∀ j, j ≤ k → X j ∈ Q := fun j hj => hXQ j (by omega)
    have hXFQ' : ∀ j, j < k → F (X j) ∈ Q := fun j hj => hXFQ j (by omega)
    have hstep' : ∀ j, j < k → X (j + 1) = G (X j) := fun j hj => hstep j (by omega)
    have hik := ih hXQ' hXFQ' hstep'
    have hFQ : F (X k) ∈ Q := hXFQ k (by omega)
    have hXQk : X k ∈ Q := hXQ k (by omega)
    have hXk1 : X (k + 1) = G (X k) := hstep k (by omega)
    have habel : Φ (F (X k)) = Φ (X k) + 1 := hab (X k) hXQk hFQ
    have hstepk : Φ (X (k + 1)) = Φ (X k) + 1 + (Φ (G (X k)) - Φ (F (X k))) := by
      rw [hXk1, habel]; ring
    rw [hstepk, hik, Finset.sum_range_succ]
    push_cast
    ring

/-- **Lipschitz bound for a Fatou coordinate on a convex domain.**  If `Q` is convex, `Φ` is
holomorphic on `Q` with `‖Φ'‖ ≤ Λ` there, then `‖Φ a - Φ b‖ ≤ Λ ‖a - b‖` for all `a, b ∈ Q`.
This is the mean value inequality used to convert the pointwise comparison of the lifts into the
per-step error of `anchor_walk_telescope`. -/
theorem anchor_Phi_lipschitz {Φ : ℂ → ℂ} {Q : Set ℂ} {Λ : ℝ}
    (hconv : Convex ℝ Q) (hdiff : ∀ z ∈ Q, DifferentiableAt ℂ Φ z)
    (hder : ∀ z ∈ Q, ‖deriv Φ z‖ ≤ Λ) {a b : ℂ} (ha : a ∈ Q) (hb : b ∈ Q) :
    ‖Φ a - Φ b‖ ≤ Λ * ‖a - b‖ :=
  Convex.norm_image_sub_le_of_norm_deriv_le hdiff hder hconv hb ha

theorem anchor_dev_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀) :
    ∃ A C Y₀ : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ 0 < Y₀ ∧
    ∃ Ms : ℝ, 0 < Ms ∧ ∀ M : ℝ, Ms ≤ M →
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ Metric.closedBall (0 : ℂ) rr ⊆ L ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
        ∀ Φ : ℂ → ℂ, MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α) →
          Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α →
          Φ (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) →
          ∀ t : ℝ, Y₀ ≤ t →
            ‖Φ (((t : ℝ) : ℂ) * Complex.I) - ((t : ℝ) : ℂ) * Complex.I‖ ≤
              A * Real.log (t + 2) + C + t / 64 ∧
            ‖Φ (-(((t : ℝ) : ℂ) * Complex.I)) + ((t : ℝ) : ℂ) * Complex.I‖ ≤
              A * Real.log (t + 2) + C + t / 64 := by
  classical
  obtain ⟨hEx, hOrb, hUniq, hCont, hDE, hEnds⟩ := hF
  obtain ⟨Rde, C1', C2, hRde, hC1', hC2, hderiv⟩ := hDE
  obtain ⟨hFm, ρm, D, hρm, hρm8, hD, hFm0, hclρm, hf0eqm, hFmd, hFml, hFmb⟩ :=
    Work.Pert.Ksub2.exists_model_data_full hd
  obtain ⟨a, b, Rax, hRax, hξRax, hexpRax, hasym⟩ := exists_Xc_axis_asym d
  obtain ⟨Rw, Kw, K1w, hRw, hKw0, hKw1, hwalk⟩ := anchor_walk d Ξ hΞ
  obtain ⟨r0s, hr0s, hclr0s, Csn, hCsn0, hsn⟩ := small_of_nearOn hd
  obtain ⟨Kd, hKd0, haxis⟩ := deltaF_axis_le rr hrr (a - 1)
  -- the model function on the whole disc
  set hF2 : ℂ → ℂ := fun z => if z = 0 then 1 else (f₀ z - z) / z ^ 2 with hF2def
  set ρ : ℝ := min ρm rr with hρdef
  have hρpos : 0 < ρ := lt_min hρm hrr
  have hρrr : ρ ≤ rr := min_le_right _ _
  have hρρm : ρ ≤ ρm := min_le_left _ _
  have hf00 : f₀ 0 = 0 := hd.2.2.2.1
  have hF2eq : ∀ z : ℂ, f₀ z = z + z ^ 2 * hF2 z := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp [hF2def, hf00]
    · have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
      have hmul : z ^ 2 * ((f₀ z - z) / z ^ 2) = f₀ z - z := by field_simp
      simp only [hF2def, hz, if_false]
      rw [hmul]; ring
  have hF2eqm : ∀ z ∈ Metric.ball (0 : ℂ) ρ, f₀ z = z + z ^ 2 * hF2 z :=
    fun z _ => hF2eq z
  have hF2_0 : hF2 0 = 1 := by simp [hF2def]
  have hF2_eq_hFm : ∀ z ∈ Metric.ball (0 : ℂ) ρ, hF2 z = hFm z := by
    intro z hz
    have hzm : z ∈ Metric.ball (0 : ℂ) ρm := Metric.ball_subset_ball hρρm hz
    by_cases hz0 : z = 0
    · subst hz0; rw [hF2_0, hFm0]
    · have h1 : f₀ z = z + z ^ 2 * hFm z := hf0eqm z hzm
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
      have hmul : z ^ 2 * hFm z / z ^ 2 = hFm z := by field_simp
      simp only [hF2def, hz0, if_false]
      rw [h1, add_sub_cancel_left, hmul]
  have hF2d : DifferentiableOn ℂ hF2 (Metric.ball (0 : ℂ) ρ) := by
    refine DifferentiableOn.congr (hFmd.mono (Metric.ball_subset_ball hρρm)) ?_
    intro z hz
    exact hF2_eq_hFm z hz
  have hF2b : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖hF2 z‖ ≤ 3 / 2 := by
    intro z hz; rw [hF2_eq_hFm z hz]; exact hFmb z (Metric.ball_subset_ball hρρm hz)
  have hF2l : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖deriv hF2 z‖ ≤ D := by
    intro z hz
    have hzm : z ∈ Metric.ball (0 : ℂ) ρm := Metric.ball_subset_ball hρρm hz
    have hcongr : hF2 =ᶠ[nhds z] hFm := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact hF2_eq_hFm y hy
    rw [hcongr.deriv_eq]
    exact hFml z hzm
  -- ## datum-level constants
  have hY0p0 : 0 < Ξ + 4 * (Rde + C2 + 2) + 10 := by
    have h1 : (0 : ℝ) < Ξ := by linarith [Real.pi_pos, hΞ]
    linarith
  obtain ⟨Ct, hCt0, htrans⟩ := anchor_transport Ξ Rde C2 hΞ hRde hC2.le
    (fun Φ' v z' R hR' hd' hi hv hcl hrel => (hderiv Φ' v z' R hR' hd' hi hv hcl hrel).2)
  have hBw0 : 0 < max (Rw + Kw * Real.log Rw + K1w + 2) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKan1 : 1 ≤ (max (Rw + Kw * Real.log Rw + K1w + 2) 1 + 2)
      + Ct * (2 * (max (Rw + Kw * Real.log Rw + K1w + 2) 1) + (Ξ + 4 * (Rde + C2 + 2) + 10) + 3) := by
    have h1 : 0 ≤ 2 * max (Rw + Kw * Real.log Rw + K1w + 2) 1 + (Ξ + 4 * (Rde + C2 + 2) + 10) + 3 := by
      linarith [hBw0, hY0p0]
    have h2 : 0 ≤ Ct * (2 * max (Rw + Kw * Real.log Rw + K1w + 2) 1 + (Ξ + 4 * (Rde + C2 + 2) + 10) + 3) :=
      mul_nonneg hCt0 h1
    have h3 : 0 < max (Rw + Kw * Real.log Rw + K1w + 2) 1 := hBw0
    linarith
  have hYtgt : Ξ + 4 * (Rde + C2 + 2) + 10 ≤ Ξ + 4 * (Rde + C2 + 2) + 11 := by linarith
  have hDEparam : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C2 / R :=
    fun Φ' v z' R hR hd' hi hv hcl hrel => (hderiv Φ' v z' R hR hd' hi hv hcl hrel).2
  have hFs : MandelDim.FatouStatement :=
    ⟨hEx, hOrb, hUniq, hCont, ⟨Rde, C1', C2, hRde, hC1', hC2, hderiv⟩, hEnds⟩
  obtain ⟨K1ab, Msab, hK1ab0, hMsab0, hanch⟩ :=
    anchor_point_bound2 d hFs hd Ξ Rde C2 (Ξ + 4 * (Rde + C2 + 2) + 11) hΞ hRde hC2.le hYtgt
      hDEparam hrr hrrD
  have hYtgt' : Ξ < Ξ + 4 * (Rde + C2 + 2) + 11 := by
    have h1 : (0 : ℝ) < Ξ := by linarith [Real.pi_pos, hΞ]
    linarith
  obtain ⟨Kdax, Msax, hKdax0, hMsax0, hax⟩ :=
    axis_decay_budget2 d hd Ξ (Ξ + 4 * (Rde + C2 + 2) + 11) hΞ hYtgt' hrr hrrD
  obtain ⟨Aat, Cat, hAat, hCat, hmain⟩ :=
    anchor_to_all_t_const Ξ Rde C2 K1ab Kdax (1 / 128) hΞ hRde hC2.le hK1ab0 hKdax0
      (by norm_num) (by norm_num) hDEparam
  refine ⟨Aat, Cat, Ξ + 4 * (Rde + C2 + 2) + 11, hAat, hCat, ?_, ?_⟩
  · have h1 : (0 : ℝ) < Ξ := by linarith [Real.pi_pos, hΞ]
    linarith
  refine ⟨max (max (Rw + 1) (16 * Rde + 100)) (max (max Msab (Msax + 1)) 1000) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ max (max (Rw + 1) (16 * Rde + 100)) (max (max Msab (Msax + 1)) 1000) := by
      have h2 := le_max_left (Rw + 1) (16 * Rde + 100)
      have h3 := le_max_left (max (Rw + 1) (16 * Rde + 100)) (max (max Msab (Msax + 1)) 1000)
      linarith [hRw]
    linarith
  intro M hM
  refine ⟨Metric.closedBall (0 : ℂ) rr, isCompact_closedBall 0 rr, hrrD, fun z hz => hz, ?_⟩
  let δ0 : ℝ := min (1 / (1000 * (M + 1))) (min rr r0s / ((40 * (Csn + 1)) * (M + 1)))
  have hMbig : max (max (Rw + 1) (16 * Rde + 100)) (max (max Msab (Msax + 1)) 1000) + 1 ≤ M := hM
  have hM0 : (0 : ℝ) < M := by
    have h1 : (0 : ℝ) < max (max (Rw + 1) (16 * Rde + 100))
        (max (max Msab (Msax + 1)) 1000) + 1 := by
      have h2 : (0 : ℝ) ≤ max (max Msab (Msax + 1)) 1000 :=
        le_trans (by norm_num : (0 : ℝ) ≤ 1000) (le_max_right _ _)
      have h3 : (0 : ℝ) ≤ max (Rw + 1) (16 * Rde + 100) := by
        have := le_max_left (Rw + 1) (16 * Rde + 100)
        linarith [hRw]
      have h4 : (0 : ℝ) ≤ max (max (Rw + 1) (16 * Rde + 100)) (max (max Msab (Msax + 1)) 1000) :=
        le_trans h3 (le_max_left _ _)
      linarith
    linarith
  have hM1 : (1 : ℝ) ≤ M + 1 := by linarith
  have hρ2pos : 0 < min rr r0s := lt_min hrr hr0s
  have hδ0pos : 0 < δ0 :=
    lt_min (by positivity) (div_pos hρ2pos (by positivity))
  have hδ0le1 : δ0 ≤ 1 / (1000 * (M + 1)) := min_le_left _ _
  have hδ0le2 : δ0 ≤ min rr r0s / ((40 * (Csn + 1)) * (M + 1)) := min_le_right _ _
  have hMab : Msab ≤ M := by
    have h4 : Msab ≤ max Msab (Msax + 1) := le_max_left _ _
    have h5 : max Msab (Msax + 1) ≤ max (max Msab (Msax + 1)) 1000 := le_max_left _ _
    have h6 : max (max Msab (Msax + 1)) 1000
        ≤ max (max (Rw + 1) (16 * Rde + 100)) (max (max Msab (Msax + 1)) 1000) := le_max_right _ _
    linarith
  have hMbd : Msax ≤ M := by
    have h4 : Msax ≤ Msax + 1 := by linarith
    have h5 : Msax + 1 ≤ max Msab (Msax + 1) := le_max_right _ _
    have h6 : max Msab (Msax + 1) ≤ max (max Msab (Msax + 1)) 1000 := le_max_left _ _
    have h7 : max (max Msab (Msax + 1)) 1000
        ≤ max (max (Rw + 1) (16 * Rde + 100)) (max (max Msab (Msax + 1)) 1000) := le_max_right _ _
    linarith
  refine ⟨δ0, hδ0pos, ?_⟩
  intro f Df u σ α hNear hf0 hInF1 hα hdu huB hfF hnorm htauQ hQAdm hNT
  intro Φ hΦ hW0 hpin t ht
  -- ## `‖α‖ * M ≤ 1/2`
  have hαM : ‖α‖ * M ≤ 1 / 2 := by
    have hρ2rr : min rr r0s ≤ rr := min_le_left _ _
    have hnear2 : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) (min rr r0s)) δ0 :=
      ⟨hNear.1, fun z hz => hNear.2.1 (Metric.closedBall_subset_closedBall hρ2rr hz),
        hNear.2.2.1, fun z hz => hNear.2.2.2 z (Metric.closedBall_subset_closedBall hρ2rr hz)⟩
    have h2δ : 2 * δ0 ≤ min rr r0s := by
      have h1 : (2 : ℝ) / ((40 * (Csn + 1)) * (M + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [hM1, hCsn0]
      calc 2 * δ0 ≤ 2 * (min rr r0s / ((40 * (Csn + 1)) * (M + 1))) := by linarith [hδ0le2]
        _ = min rr r0s * ((2 : ℝ) / ((40 * (Csn + 1)) * (M + 1))) := by ring
        _ ≤ min rr r0s * 1 := mul_le_mul_of_nonneg_left h1 hρ2pos.le
        _ = min rr r0s := by ring
    have hsm := hsn hρ2pos (min_le_right _ _) hδ0pos h2δ hrr hnear2 hf0 hdu huB hfF
    have h3 : ‖α‖ ≤ Csn * δ0 / min rr r0s := by
      have h3' := hsm.2.2
      rwa [← hα] at h3'
    have hne : min rr r0s ≠ 0 := ne_of_gt hρ2pos
    have h5 : ‖α‖ ≤ 1 / (40 * (M + 1)) := by
      have h7 : Csn * δ0 / min rr r0s
          ≤ Csn * (min rr r0s / ((40 * (Csn + 1)) * (M + 1))) / min rr r0s :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hδ0le2 hCsn0.le) hρ2pos.le
      have h8 : Csn * (min rr r0s / ((40 * (Csn + 1)) * (M + 1))) / min rr r0s
          = Csn / ((40 * (Csn + 1)) * (M + 1)) := by
        have hne : min rr r0s ≠ 0 := ne_of_gt hρ2pos
        field_simp
      have h9 : Csn / ((40 * (Csn + 1)) * (M + 1)) ≤ 1 / (40 * (M + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hCsn0, hM1]
      linarith [h3, h7, h8, h9]
    have h11 : (1 : ℝ) / (40 * (M + 1)) * M ≤ 1 / 2 := by
      have hden : (0 : ℝ) < 40 * (M + 1) := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [hM1]
    calc ‖α‖ * M ≤ (1 / (40 * (M + 1))) * M := by nlinarith [norm_nonneg α]
      _ ≤ 1 / 2 := h11
  obtain ⟨εM, hεM0, hεM1, haxM⟩ := hax M hMbd
  have hanchor := hanch M hMab δ0 hδ0pos hδ0le1
    f Df u σ α Φ hNear hf0 hInF1 hα hdu huB hfF hnorm htauQ hQAdm hαM hNT hΦ hW0 hpin
  have haxisdecay := haxM δ0 hδ0pos hδ0le1
    f Df u σ α hNear hf0 hInF1 hα hdu huB hfF hnorm htauQ
  have hbig : Ξ + 4 * (Rde + C2 + 2) + 10 ≤ Ξ + 4 * (Rde + C2 + 2) + 11 := by linarith
  have hres := hmain (α := α) (Y₀ := Ξ + 4 * (Rde + C2 + 2) + 11) hbig hQAdm hNT hΦ
    haxisdecay.1 (fun s hs => le_trans (haxisdecay.2 s hs) (by linarith [hεM1]))
    hanchor.1 hanchor.2 t ht
  exact hres

end Work.Pert.PinLogDev
