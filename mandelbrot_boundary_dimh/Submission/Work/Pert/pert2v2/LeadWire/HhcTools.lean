import Mathlib
import Submission.Work.Pert.tauC_add_inv_le
import Submission.Work.Pert.sigma_alpha_close
import Submission.Work.Pert.pert2v2.HresFixed
import Submission.Work.Pert.pert2v2.LeadWire.SegSetup

/-!
# `Work.Pert.pert2v2.LeadWire.HhcTools` — the pieces of the single-height (A.4.4) residual

* `tau_close_of_small` — `‖tauC σ α w + 1/w‖ ≤ κ` on `1 ≤ ‖w‖ ≤ 2 y₀`, from the normal-form
  smallness `‖α‖ ≤ Csm δ0/ρ`, `‖u 0 - 1‖ ≤ Csm (δ0/ρ² + δ0/(ρρ))` and one `δ0`-condition;
* `hres_core` — the residual `‖Φp ς - d.E W‖ < δ'` from the closeness of `τ ς` to `d.φ W`
  (the pinned `coordP` closeness), the pin of `Φp` at the curve point `Xc d W`, and the gate
  Lipschitz bound on the waist tube;
* `disc_step_waist` — a point of the disc `closedBall (t i) (t/8)` and its forward step stay in
  the waist.
-/

namespace Work.Pert.pert2v2.LeadWire

open _root_.MandelDim Complex Set Metric

/-- **`tauC ≈ τ₀` at bounded height, as a `δ0`-condition.** -/
theorem tau_close_of_small {σ α : ℂ} {u : ℂ → ℂ} {w : ℂ} {Csm ρ δ0 κ y₀ : ℝ}
    (hα : α ≠ 0) (hCsm : 0 < Csm) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ0 : 0 ≤ δ0)
    (hy₀ : 1 ≤ y₀) (hκ : 0 < κ) (hκy : κ ≤ 1 / (64 * Real.pi * (y₀ + 1)))
    (hδκ : δ0 ≤ ρ ^ 2 * κ / (60 * Csm))
    (hαs : ‖α‖ ≤ Csm * δ0 / ρ)
    (hu0 : ‖u 0 - 1‖ ≤ Csm * (δ0 / ρ ^ 2 + δ0 / (ρ * ρ)))
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hw1 : 1 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 2 * y₀) :
    ‖Work.Pert.tauC σ α w + 1 / w‖ ≤ κ := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  -- `a := Csm δ0/ρ ≤ Csm δ0/ρ² ≤ κ/50`
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hkey : Csm * δ0 / ρ ^ 2 ≤ κ / 60 := by
    rw [div_le_iff₀ hρ2]
    have h := mul_le_mul_of_nonneg_left hδκ hCsm.le
    have h2 : Csm * (ρ ^ 2 * κ / (60 * Csm)) = κ / 60 * ρ ^ 2 := by field_simp
    linarith
  have ha1 : Csm * δ0 / ρ ≤ Csm * δ0 / ρ ^ 2 := by
    have hnum : 0 ≤ Csm * δ0 := mul_nonneg hCsm.le hδ0
    apply div_le_div_of_nonneg_left hnum hρ2
    nlinarith
  have ha : ‖α‖ ≤ κ / 60 := le_trans hαs (le_trans ha1 hkey)
  have hb' : Csm * (δ0 / ρ ^ 2 + δ0 / (ρ * ρ)) = 2 * (Csm * δ0 / ρ ^ 2) := by
    rw [show ρ * ρ = ρ ^ 2 by ring]; ring
  have hb : ‖u 0 - 1‖ ≤ 2 * (κ / 60) := by
    rw [hb'] at hu0; linarith
  have hκsmall : κ ≤ 1 / (64 * Real.pi * 2) := by
    refine le_trans hκy ?_
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Real.pi_pos]
  have hκ1 : κ ≤ 1 / 384 := by
    refine le_trans hκsmall ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hα2π : ‖α‖ ≤ 1 / (2 * Real.pi) := by
    refine le_trans ha ?_
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hu12 : ‖u 0 - 1‖ ≤ 1 / 2 := by linarith
  obtain ⟨hsa, -⟩ := Work.Pert.sigma_alpha_close hα hα2π hu12 hnorm
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw1; linarith
  have hsmall : 2 * Real.pi * ‖α‖ * ‖w‖ ≤ 1 / 2 := by
    have h1 : 2 * Real.pi * ‖α‖ * ‖w‖ ≤ 2 * Real.pi * (κ / 60) * (2 * y₀) := by
      have := mul_le_mul ha hw2 (norm_nonneg w) (by positivity)
      nlinarith [Real.pi_pos]
    have h2 : κ * (y₀ + 1) ≤ 1 / (64 * Real.pi) := by
      have hy : 0 < y₀ + 1 := by linarith
      have := mul_le_mul_of_nonneg_right hκy hy.le
      rw [show 1 / (64 * Real.pi * (y₀ + 1)) * (y₀ + 1) = 1 / (64 * Real.pi) by
        field_simp] at this
      exact this
    have h3 : 2 * Real.pi * (κ / 60) * (2 * y₀) ≤ 1 / 2 := by
      have h4 : Real.pi * (κ * (y₀ + 1)) ≤ 1 / 64 := by
        have := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
        rw [show Real.pi * (1 / (64 * Real.pi)) = 1 / 64 by field_simp] at this
        exact this
      nlinarith [Real.pi_pos, hκ.le]
    linarith
  have hmain := Work.Pert.tauC_add_inv_le σ α w hα hw0 (m := 1) one_pos hw1 hsmall
  have hX : ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * 1)
      ≤ 8 * Real.pi * ‖α‖ + 4 * ‖u 0 - 1‖ := by
    rw [mul_one, div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_pos, norm_nonneg α, norm_nonneg (u 0 - 1)]
  have hY : (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi = 4 * Real.pi * ‖α‖ := by
    field_simp; ring
  rw [hY] at hmain
  have : 12 * Real.pi * ‖α‖ + 4 * ‖u 0 - 1‖ ≤ κ := by
    have h1 : 12 * Real.pi * ‖α‖ ≤ 48 * (κ / 60) := by nlinarith [norm_nonneg α]
    linarith
  linarith

/-- **The residual at a fixed height from the `τ`-closeness.** -/
theorem hres_core {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ' y₀ Cgl Rgl εp ηs ε1 κ δ' : ℝ} {α : ℂ} {Φp τ : ℂ → ℂ} {W ς : ℂ}
    (hInF1 : MandelDim.InF1 α) (hy₀ : 16 ≤ y₀) (hΞ'y : Ξ' + y₀ / 2 < y₀)
    (hRgl0 : 0 ≤ Rgl) (hRgl : Rgl ≤ y₀ / 8)
    (hς : ‖ς - (y₀ : ℂ) * Complex.I‖ ≤ y₀ / 8)
    (hZ : ‖Work.Pert.Xc d W - (y₀ : ℂ) * Complex.I‖ ≤ y₀ / 8)
    (hφW : d.φ W ∈ MandelDim.ParabolicBasin f₀ D₀)
    (hτφ : ‖τ ς - d.φ W‖ ≤ ε1)
    (hτinv : ‖τ ς + 1 / ς‖ ≤ κ)
    (hsmall : 4 * y₀ ^ 2 * (ε1 + κ) ≤ ηs)
    (hLip : ∀ x y : ℂ, (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Metric.closedBall ((1 - t) * x + t * y) Rgl ⊆ Work.Pert.Qp Ξ' α) →
      ‖Φp x - Φp y‖ ≤ Cgl * ‖x - y‖)
    (hpin : ‖Φp (Work.Pert.Xc d W) - d.Φ (MandelDim.tau0 (Work.Pert.Xc d W))‖ < εp)
    (hCgl : 0 ≤ Cgl) (harith : Cgl * ηs + εp ≤ δ') :
    ‖Φp ς - d.E W‖ < δ' := by
  have hy₀pos : 0 < y₀ := by linarith
  set p : ℂ := d.φ W with hp
  have hp0 : p ≠ 0 := by
    have := d.orbit_avoid p hφW 0
    simpa using this
  set Z : ℂ := Work.Pert.Xc d W with hZdef
  have hZp : Z = -1 / p := by rw [hZdef, hp]; rfl
  have htZ : MandelDim.tau0 Z = p := by
    rw [hZp]; simp only [MandelDim.tau0]; field_simp
  -- norms
  have hnorm_le : ∀ z : ℂ, ‖z - (y₀ : ℂ) * Complex.I‖ ≤ y₀ / 8 → ‖z‖ ≤ 2 * y₀ := by
    intro z hz
    have h1 : ‖(y₀ : ℂ) * Complex.I‖ = y₀ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy₀pos]
    have h2 := norm_le_norm_add_norm_sub' z ((y₀ : ℂ) * Complex.I)
    have h3 : ‖z‖ ≤ ‖(y₀ : ℂ) * Complex.I‖ + ‖z - (y₀ : ℂ) * Complex.I‖ := by
      have := norm_sub_norm_le z ((y₀ : ℂ) * Complex.I)
      linarith
    linarith
  have hnorm_ge : ∀ z : ℂ, ‖z - (y₀ : ℂ) * Complex.I‖ ≤ y₀ / 8 → y₀ / 2 ≤ ‖z‖ := by
    intro z hz
    have h1 : ‖(y₀ : ℂ) * Complex.I‖ = y₀ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy₀pos]
    have h3 := norm_sub_norm_le ((y₀ : ℂ) * Complex.I) z
    rw [norm_sub_rev] at h3
    linarith
  have hςn := hnorm_le ς hς
  have hZn := hnorm_le Z hZ
  have hς0 : ς ≠ 0 := by
    intro h; have := hnorm_ge ς hς; rw [h, norm_zero] at this; linarith
  have hZ0 : Z ≠ 0 := by
    intro h; have := hnorm_ge Z hZ; rw [h, norm_zero] at this; linarith
  -- the inverse closeness
  have hinv : ‖1 / ς - 1 / Z‖ ≤ ε1 + κ := by
    have hpZ : p = -(1 / Z) := by
      rw [hZp]; field_simp
    have heq : 1 / ς - 1 / Z = (τ ς + 1 / ς) - (τ ς - p) := by rw [hpZ]; ring
    rw [heq]
    calc ‖(τ ς + 1 / ς) - (τ ς - p)‖ ≤ ‖τ ς + 1 / ς‖ + ‖τ ς - p‖ := norm_sub_le _ _
      _ ≤ κ + ε1 := add_le_add hτinv hτφ
      _ = ε1 + κ := by ring
  have hsz : ς - Z = -(ς * Z * (1 / ς - 1 / Z)) := by field_simp; ring
  have hdist : ‖ς - Z‖ ≤ ηs := by
    rw [hsz, norm_neg, norm_mul, norm_mul]
    have h1 : ‖ς‖ * ‖Z‖ ≤ 4 * y₀ ^ 2 := by
      have := mul_le_mul hςn hZn (norm_nonneg Z) (by positivity)
      nlinarith
    have h2 : ‖ς‖ * ‖Z‖ * ‖1 / ς - 1 / Z‖ ≤ 4 * y₀ ^ 2 * (ε1 + κ) :=
      mul_le_mul h1 hinv (norm_nonneg _) (by positivity)
    linarith
  -- the tube
  have htube := (Work.Pert.pert2v2.waist_tube_gates (Ξ := Ξ') (T := y₀) (ρ := y₀ / 4)
    (R₂ := Rgl) (α := α) (x := ς) (y := Z) hInF1 hy₀pos (by positivity) hRgl0
    (by linarith) (by linarith) (by linarith)).1
  have hLipςZ : ‖Φp ς - Φp Z‖ ≤ Cgl * ‖ς - Z‖ :=
    hLip ς Z (fun t ht => fun z hz => (htube t ht hz).2)
  have hEW : d.E W = d.Φ (MandelDim.tau0 Z) := by
    rw [htZ, hp]; rfl
  rw [hEW]
  calc ‖Φp ς - d.Φ (MandelDim.tau0 Z)‖
      ≤ ‖Φp ς - Φp Z‖ + ‖Φp Z - d.Φ (MandelDim.tau0 Z)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < Cgl * ηs + εp := by
        have := mul_le_mul_of_nonneg_left hdist hCgl
        linarith
    _ ≤ δ' := harith

/-- **A point of the axis disc and its forward step stay in the waist.** -/
theorem disc_step_waist {Ξ t : ℝ} {α : ℂ} {F : ℂ → ℂ} {ς : ℂ} (hInF1 : MandelDim.InF1 α)
    (ht : 32 ≤ t) (hΞt : Ξ + t / 2 < t)
    (hς : ‖ς - (t : ℂ) * Complex.I‖ ≤ t / 8) (hF : ‖F ς - (ς + 1)‖ ≤ 1 / 32) :
    ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α ∧ F ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := by
  have htpos : 0 < t := by linarith
  have hdisc : Metric.closedBall ((t : ℂ) * Complex.I) (t / 4) ⊆
      Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α :=
    Work.Pert.WaistPinned.waist_disc_window (ξ := Ξ) (T := t) (ρ := t / 4) (α := α)
      (z₀ := (t : ℂ) * Complex.I) hInF1 (by positivity) (by linarith) (by simp)
      (by simp [abs_of_pos htpos])
  refine ⟨hdisc ?_, hdisc ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  · rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : F ς - (t : ℂ) * Complex.I
        = (F ς - (ς + 1)) + (ς - (t : ℂ) * Complex.I) + 1 := by ring
    rw [heq]
    calc ‖(F ς - (ς + 1)) + (ς - (t : ℂ) * Complex.I) + 1‖
        ≤ ‖(F ς - (ς + 1)) + (ς - (t : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖F ς - (ς + 1)‖ + ‖ς - (t : ℂ) * Complex.I‖ + ‖(1 : ℂ)‖ := by
          have := norm_add_le (F ς - (ς + 1)) (ς - (t : ℂ) * Complex.I)
          linarith
      _ ≤ 1 / 32 + t / 8 + 1 := by rw [norm_one]; linarith
      _ ≤ t / 4 := by linarith

/-- Norm bounds for a point of the axis disc `closedBall (y₀ i) (y₀/8)`. -/
theorem norm_bounds_near_axis {z : ℂ} {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hz : ‖z - (y₀ : ℂ) * Complex.I‖ ≤ y₀ / 8) : 7 * y₀ / 8 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * y₀ := by
  have h1 : ‖(y₀ : ℂ) * Complex.I‖ = y₀ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy₀]
  have h2 := norm_sub_norm_le z ((y₀ : ℂ) * Complex.I)
  have h3 := norm_sub_norm_le ((y₀ : ℂ) * Complex.I) z
  rw [norm_sub_rev] at h3
  constructor <;> linarith

end Work.Pert.pert2v2.LeadWire
