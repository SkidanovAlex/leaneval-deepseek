import Mathlib
import Submission.Work.Pert.tauC_add_inv_le
import Submission.Work.Pert.sigma_alpha_close
import Submission.Work.PertCrux.liftF_sub_model_le_var
import Submission.Work.Pert.Ksub2.F0f_eq_model
import Submission.Work.Pert.Ksub2.exists_model_data_full
import Submission.Work.Pert.pert2v2.LeadWire.HhcTools

/-!
# `Work.Pert.pert2v2.LeadWire.ShadowTools` — the datum-level pieces of the `(SHADOW)` row (S12)

* `liftF_F0f_close_datum` — `‖liftF u σ α w - F0f f₀ w‖ ≤ Cm η` far out (`‖w‖ ≥ Rm`), from the
  `η`-smallness of the normal-form data (`u ≈ (f₀ - id)/z²`, `u 0 ≈ 1`, `α ≈ 0`, `τ ≈ τ₀` at `w`);
  the radius `Rm` and the constant `Cm` depend only on the germ and the normal-form radius `ρ`.
* `dist_le_of_tau_close` — the inverse-`τ` localisation: `‖ς - Z‖ ≤ R² (ε₁ + κ)` from
  `‖τ ς - p‖ ≤ ε₁`, `‖τ ς + 1/ς‖ ≤ κ`, `Z = -1/p`.
* `walk_disp` — a walk with near-translation steps moves by at most `2` per step.
-/

namespace Work.Pert.pert2v2.LeadWire

open _root_.MandelDim Complex Set Metric

/-- **The perturbed lift is close to the model lift far out, as a datum-level statement.** -/
theorem liftF_F0f_close_datum {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Rm : ℝ, 128 ≤ Rm ∧ ∃ Cm : ℝ, 0 < Cm ∧ ∀ {u : ℂ → ℂ} {σ α w : ℂ} {η : ℝ},
      0 < η → η ≤ 1 / 1000 → η ≤ 1 / (2 * Real.pi) → η ≤ 1 / Rm →
      DifferentiableOn ℂ u (Metric.ball 0 ρ) →
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, z ≠ 0 → ‖u z - (f₀ z - z) / z ^ 2‖ < η) →
      ‖u 0 - 1‖ ≤ η → α ≠ 0 → ‖α‖ ≤ η →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      Rm ≤ ‖w‖ → ‖Work.Pert.tauC σ α w + 1 / w‖ ≤ η → ‖α‖ * ‖w‖ ≤ 1 / 2 →
      ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖ ≤ Cm * η := by
  obtain ⟨hF, ρg, D, hρg, hρg8, hD, hF0, -, hFeq, hFd, hFl, hFb⟩ :=
    Work.Pert.Ksub2.exists_model_data_full hd
  set ρu : ℝ := min ρ ρg with hρudef
  have hρu : 0 < ρu := lt_min hρ hρg
  have hρuρ : ρu ≤ ρ := min_le_left _ _
  have hρuρg : ρu ≤ ρg := min_le_right _ _
  set Rm : ℝ := max 128 (16 / ρu) with hRmdef
  have hRm128 : 128 ≤ Rm := le_max_left _ _
  have hRmρ : 16 / ρu ≤ Rm := le_max_right _ _
  have hRmpos : 0 < Rm := by linarith
  have hinvRm : 1 / Rm ≤ ρu / 16 := by
    rw [div_le_iff₀ hRmpos]
    have h1 : 16 / ρu * (ρu / 16) = 1 := by field_simp
    have h2 : 16 / ρu * (ρu / 16) ≤ Rm * (ρu / 16) :=
      mul_le_mul_of_nonneg_right hRmρ (by positivity)
    linarith
  have hinvRm' : 1 / Rm ≤ 1 / 128 := one_div_le_one_div_of_le (by norm_num) hRm128
  refine ⟨Rm, hRm128, 2000 * (D + 1), by positivity, ?_⟩
  intro u σ α w η hη hη1 hη2π hηR hu hud hu0 hα hαη hnorm hwR htau hαw
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hRmpos hwR
  have hw : w ≠ 0 := norm_pos_iff.mp hwpos
  -- `τ₀ w` and `τ w` are small
  have ht0n : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by simp [MandelDim.tau0]
  have ht0 : ‖MandelDim.tau0 w‖ ≤ 1 / Rm := by
    rw [ht0n]; exact one_div_le_one_div_of_le hRmpos hwR
  have htt : Work.Pert.tauC σ α w - MandelDim.tau0 w = Work.Pert.tauC σ α w + 1 / w := by
    rw [MandelDim.tau0]; ring
  have htdiff : ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ η := by rw [htt]; exact htau
  have htn : ‖Work.Pert.tauC σ α w‖ ≤ 2 / Rm := by
    have h := norm_le_norm_add_norm_sub' (Work.Pert.tauC σ α w) (MandelDim.tau0 w)
    have h2 : ‖Work.Pert.tauC σ α w‖ ≤ ‖MandelDim.tau0 w‖
        + ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ := by
      have := norm_sub_norm_le (Work.Pert.tauC σ α w) (MandelDim.tau0 w)
      linarith
    have h3 : 2 / Rm = 1 / Rm + 1 / Rm := by ring
    linarith
  have htu : Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) ρu := by
    rw [Metric.mem_ball, dist_zero_right]
    have h3 : 2 / Rm = 1 / Rm + 1 / Rm := by ring
    linarith
  have ht0b : MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) ρg := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have ht16 : ‖Work.Pert.tauC σ α w‖ ≤ 1 / 16 := by
    have h3 : 2 / Rm = 1 / Rm + 1 / Rm := by ring
    linarith
  have ht64 : ‖MandelDim.tau0 w‖ ≤ 1 / 64 := by linarith
  -- `u` close to `hF` on the punctured ball of radius `ρu`
  have huc : ∀ z ∈ Metric.ball (0 : ℂ) ρu, z ≠ 0 → ‖u z - hF z‖ ≤ η := by
    intro z hz hz0
    have hzρ : z ∈ Metric.ball (0 : ℂ) ρ := Metric.ball_subset_ball hρuρ hz
    have h1 := hud z hzρ hz0
    have hfe := hFeq z (Metric.ball_subset_ball hρuρg hz)
    have heq : (f₀ z - z) / z ^ 2 = hF z := by rw [hfe]; field_simp; ring
    rw [heq] at h1
    exact h1.le
  have hαπ : ‖α‖ ≤ 1 / (2 * Real.pi) := le_trans hαη hη2π
  have hmain := Work.PertCrux.liftF_sub_model_le_var (u := u) (hF := hF) (σ := σ) (α := α) (w := w)
    (ρu := ρu) (ρh := ρg) (D := D) (η := η) (δ₂ := η) hρu hρg hρuρg (by linarith) hD hη hη1
    htu ht0b ht16 ht64 htdiff hη.le (hFd) (hFl) (hFb) (hu.mono (Metric.ball_subset_ball hρuρ))
    huc hu0 hα hαη hαπ hnorm hw hαw
  -- the model lift is `F0f`
  have ht0g : MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) ρg := ht0b
  have hfe : f₀ (MandelDim.tau0 w)
      = MandelDim.tau0 w + MandelDim.tau0 w ^ 2 * hF (MandelDim.tau0 w) := hFeq _ ht0g
  have hden : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0 := by
    intro h
    have htG : MandelDim.tau0 w * hF (MandelDim.tau0 w) = -1 := by linear_combination h
    have h1 : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ < 1 := by
      rw [norm_mul]
      calc ‖MandelDim.tau0 w‖ * ‖hF (MandelDim.tau0 w)‖ ≤ (1 / 64) * (3 / 2) :=
            mul_le_mul ht64 (hFb _ ht0g) (norm_nonneg _) (by norm_num)
        _ < 1 := by norm_num
    rw [htG, norm_neg, norm_one] at h1
    exact absurd h1 (by norm_num)
  have hmodel := Work.Pert.Ksub2.F0f_eq_model (f₀ := f₀) (hF := hF) hw hfe hden
  rw [hmodel]
  calc _ ≤ 1000 * (D + 1) * (η + η) := hmain
    _ = 2000 * (D + 1) * η := by ring

/-- **Inverse-`τ` localisation.** -/
theorem dist_le_of_tau_close {τ : ℂ → ℂ} {ς Z p : ℂ} {R ε₁ κ : ℝ}
    (hς0 : ς ≠ 0) (hZ0 : Z ≠ 0) (hςR : ‖ς‖ ≤ R) (hZR : ‖Z‖ ≤ R) (hZp : Z = -1 / p)
    (hp : p ≠ 0) (hτφ : ‖τ ς - p‖ ≤ ε₁) (hτinv : ‖τ ς + 1 / ς‖ ≤ κ) :
    ‖ς - Z‖ ≤ R ^ 2 * (ε₁ + κ) := by
  have hpZ : p = -(1 / Z) := by rw [hZp]; field_simp
  have hinv : ‖1 / ς - 1 / Z‖ ≤ ε₁ + κ := by
    have heq : 1 / ς - 1 / Z = (τ ς + 1 / ς) - (τ ς - p) := by rw [hpZ]; ring
    rw [heq]
    calc ‖(τ ς + 1 / ς) - (τ ς - p)‖ ≤ ‖τ ς + 1 / ς‖ + ‖τ ς - p‖ := norm_sub_le _ _
      _ ≤ κ + ε₁ := add_le_add hτinv hτφ
      _ = ε₁ + κ := by ring
  have hsz : ς - Z = -(ς * Z * (1 / ς - 1 / Z)) := by field_simp; ring
  rw [hsz, norm_neg, norm_mul, norm_mul]
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hςR
  have h1 : ‖ς‖ * ‖Z‖ ≤ R ^ 2 := by
    have := mul_le_mul hςR hZR (norm_nonneg Z) hR0
    nlinarith
  exact mul_le_mul h1 hinv (norm_nonneg _) (by positivity)

/-- **A near-translation walk moves by at most `2` per step.** -/
theorem walk_disp {G : ℂ → ℂ} {z : ℂ} {m : ℕ} {c : ℝ} (hc : c ≤ 1)
    (hstep : ∀ j : ℕ, j < m → ‖G (G^[j] z) - (G^[j] z + 1)‖ ≤ c) :
    ∀ j : ℕ, j ≤ m → ‖G^[j] z - z‖ ≤ 2 * j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ m := Nat.le_of_succ_le hk
    have h1 := ih hk'
    have h2 := hstep k (Nat.lt_of_succ_le hk)
    rw [Function.iterate_succ_apply']
    have heq : G (G^[k] z) - z = (G (G^[k] z) - (G^[k] z + 1)) + (G^[k] z - z) + 1 := by ring
    rw [heq]
    calc ‖(G (G^[k] z) - (G^[k] z + 1)) + (G^[k] z - z) + 1‖
        ≤ ‖(G (G^[k] z) - (G^[k] z + 1)) + (G^[k] z - z)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖G (G^[k] z) - (G^[k] z + 1)‖ + ‖G^[k] z - z‖ + ‖(1 : ℂ)‖ := by
          have := norm_add_le (G (G^[k] z) - (G^[k] z + 1)) (G^[k] z - z)
          linarith
      _ ≤ c + 2 * k + 1 := by rw [norm_one]; linarith
      _ ≤ 2 * ((k + 1 : ℕ) : ℝ) := by push_cast; linarith

/-- `Qp` is antitone in the gate parameter. -/
theorem Qp_anti {Ξ₁ Ξ₂ : ℝ} {α : ℂ} (h : Ξ₁ ≤ Ξ₂) : Work.Pert.Qp Ξ₂ α ⊆ Work.Pert.Qp Ξ₁ α := by
  intro z hz
  rw [Work.Pert.Qp_mem_iff] at hz ⊢
  exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- **A point near the axis point `s i` is in the gate `Qp Ξ α`, with walk room `N`.** -/
theorem qp_room_near_axis {Ξ s N : ℝ} {α z : ℂ} (hs : 32 ≤ |s|) (hΞs : Ξ ≤ |s| / 2) (hN : 0 ≤ N)
    (hz : ‖z - (s : ℂ) * Complex.I‖ ≤ |s| / 8 + 1) (hA : Ξ + |s| + N + 4 ≤ (1 / α).re) :
    z ∈ Work.Pert.Qp Ξ α ∧
      N ≤ |(z - (-(Ξ : ℂ) + 1 / α)).im| - (z - (-(Ξ : ℂ) + 1 / α)).re := by
  obtain ⟨hre, him⟩ := re_im_of_near_axis hz
  have hre' := abs_le.mp hre
  have hIm : 7 * |s| / 8 - 1 ≤ |z.im| := by
    have h1 : |s| ≤ |z.im| + |z.im - s| := by
      have := abs_sub_abs_le_abs_sub s z.im
      rw [abs_sub_comm] at this
      linarith
    linarith
  refine ⟨?_, ?_⟩
  · rw [Work.Pert.Qp_mem_iff]
    refine ⟨by linarith, ?_⟩
    have := abs_nonneg (z.im - (1 / α).im)
    linarith [hre'.2]
  · have hre2 : (z - (-(Ξ : ℂ) + 1 / α)).re = z.re + Ξ - (1 / α).re := by simp; ring
    rw [hre2]
    have := abs_nonneg (z - (-(Ξ : ℂ) + 1 / α)).im
    linarith

/-- **The arithmetic of the shadowing horizon.** -/
theorem shadow_arith {K η δ Bm : ℝ} {m Mn : ℕ} (hK : 1 ≤ K) (hBm : 0 < Bm) (hm : m ≤ Mn)
    (hη : η = Bm / (4 * K ^ Mn)) (hδ : δ = Bm / (4 * K ^ Mn * ((Mn : ℝ) + 1))) :
    K ^ m * (η + (m : ℝ) * δ) ≤ Bm / 2 := by
  have hKpos : 0 < K := by linarith
  have hKm : K ^ m ≤ K ^ Mn := pow_le_pow_right₀ hK hm
  have hKMpos : 0 < K ^ Mn := pow_pos hKpos _
  have hMpos : (0 : ℝ) < (Mn : ℝ) + 1 := by positivity
  have hmM : (m : ℝ) ≤ Mn := by exact_mod_cast hm
  have hηnn : 0 ≤ η := by rw [hη]; positivity
  have hδnn : 0 ≤ δ := by rw [hδ]; positivity
  have h1 : (m : ℝ) * δ ≤ (Mn : ℝ) * δ := mul_le_mul_of_nonneg_right hmM hδnn
  have h2 : (Mn : ℝ) * δ ≤ Bm / (4 * K ^ Mn) := by
    rw [hδ]
    rw [show (Mn : ℝ) * (Bm / (4 * K ^ Mn * ((Mn : ℝ) + 1)))
        = Bm / (4 * K ^ Mn) * ((Mn : ℝ) / ((Mn : ℝ) + 1)) by field_simp]
    have h3 : (Mn : ℝ) / ((Mn : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hMpos]; linarith
    have h4 : 0 ≤ Bm / (4 * K ^ Mn) := by positivity
    nlinarith
  have hsum : η + (m : ℝ) * δ ≤ 2 * (Bm / (4 * K ^ Mn)) := by rw [hη] at *; linarith
  have hnn : 0 ≤ η + (m : ℝ) * δ := by positivity
  calc K ^ m * (η + (m : ℝ) * δ) ≤ K ^ Mn * (η + (m : ℝ) * δ) :=
        mul_le_mul_of_nonneg_right hKm hnn
    _ ≤ K ^ Mn * (2 * (Bm / (4 * K ^ Mn))) := mul_le_mul_of_nonneg_left hsum hKMpos.le
    _ = Bm / 2 := by field_simp; ring

/-- Norm bounds for a point of the axis disc `closedBall (s i) (|s|/8)` (either sign of `s`). -/
theorem norm_bounds_near_axis_abs {z : ℂ} {s : ℝ}
    (hz : ‖z - (s : ℂ) * Complex.I‖ ≤ |s| / 8) : 7 * |s| / 8 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * |s| := by
  have h1 : ‖(s : ℂ) * Complex.I‖ = |s| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 := norm_sub_norm_le z ((s : ℂ) * Complex.I)
  have h3 := norm_sub_norm_le ((s : ℂ) * Complex.I) z
  rw [norm_sub_rev] at h3
  have h4 := abs_nonneg s
  constructor <;> linarith

/-- The closed band `{|Re| ≤ 1, a ≤ |Im| ≤ b}` is compact. -/
theorem isCompact_band (a b : ℝ) :
    IsCompact {w : ℂ | |w.re| ≤ 1 ∧ a ≤ |w.im| ∧ |w.im| ≤ b} := by
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · refine (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im)).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |b|)).subset ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := Complex.norm_le_abs_re_add_abs_im w
    have h2 : |w.im| ≤ |b| := le_trans hw.2.2 (le_abs_self b)
    linarith [hw.1]

/-- The curve `Xc d` is bounded on every compact subset of `d.DE`. -/
theorem Xc_bounded_on_compact {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE) :
    ∃ R : ℝ, ∀ w ∈ K, ‖Work.Pert.Xc d w‖ ≤ R := by
  have hcont : ContinuousOn (Work.Pert.Xc d) K := by
    intro w hw
    have hwD := hK hw
    have hφc : ContinuousAt d.φ w :=
      (d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hwD.1)).continuousAt
    have hne : d.φ w ≠ 0 := by
      have := d.orbit_avoid _ hwD.2 0
      simpa using this
    have h : ContinuousAt (fun u => -1 / d.φ u) w :=
      continuousAt_const.div hφc hne
    exact h.continuousWithinAt
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn hcont
  exact ⟨R, hR⟩

/-- The normal-form smallness as a single `δ0`-condition. -/
theorem small_of_delta {a b Csm ρ δ0 θ : ℝ} (hCsm : 0 < Csm) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ0 : 0 ≤ δ0) (hθ : δ0 ≤ ρ ^ 2 * θ / (2 * Csm))
    (ha : a ≤ Csm * δ0 / ρ) (hb : b ≤ Csm * (δ0 / ρ ^ 2 + δ0 / (ρ * ρ))) :
    a ≤ θ / 2 ∧ b ≤ θ := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hkey : Csm * δ0 / ρ ^ 2 ≤ θ / 2 := by
    rw [div_le_iff₀ hρ2]
    have h := mul_le_mul_of_nonneg_left hθ hCsm.le
    have h2 : Csm * (ρ ^ 2 * θ / (2 * Csm)) = θ / 2 * ρ ^ 2 := by field_simp
    linarith
  have ha1 : Csm * δ0 / ρ ≤ Csm * δ0 / ρ ^ 2 := by
    apply div_le_div_of_nonneg_left (mul_nonneg hCsm.le hδ0) hρ2
    nlinarith
  have hb' : Csm * (δ0 / ρ ^ 2 + δ0 / (ρ * ρ)) = 2 * (Csm * δ0 / ρ ^ 2) := by
    rw [show ρ * ρ = ρ ^ 2 by ring]; ring
  constructor
  · linarith
  · rw [hb'] at hb; linarith

end Work.Pert.pert2v2.LeadWire
