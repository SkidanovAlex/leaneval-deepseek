import Mathlib
import Submission.Work.OddVolterra.RowIdentity.contDiffAt_WW
import Submission.Work.OddVolterra.RowIdentity.Qy_Qx_rect_pos

/-!
# Full smoothness (`C^∞`) of the swept part `WW`

`WW n h x y u = ∫_σ in u..1, (σ-u)^{n+1/2} · B(u,σ) dσ`.  The proof of
`Work.OddVolterra.RowIdentity.contDiffAt_WW` already produces, on a neighbourhood of every
`s ∈ [a,c]`, the substitution

`WW n h x y u = (1-u)^{n+3/2} ∫_θ in 0..1, F(u,θ) dθ`

with `F` *jointly* `C^∞` on all of `ℝ²`.  Since `1 - s > 0`, the product is `C^∞` at `s`, and
the arguments used there (`rpow` with a positive base, parametric interval integrals of smooth
functions) are available at order `⊤`; only the descent to the finite order `n+1` is dropped
here.  Consequently `WW` is smooth at `s`, not merely `C^{n+1}`.
-/

namespace Work.OddVolterra.Smooth

open MeasureTheory Set Filter
open Work.OddVolterra.RowIdentity
open scoped Topology ContDiff Interval

noncomputable section

theorem contDiffAt_WW_top (H : Work.OddVolterra.RowIdentity.Setup) {s δ : ℝ}
    (hs : s ∈ Set.Icc H.a H.c) (hδ : 0 < δ)
    (hQy : ∀ q : ℝ × ℝ, q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) →
      0 < Work.OddVolterra.RowIdentity.Qy H.h H.y q.1 q.2)
    (hQx : ∀ q : ℝ × ℝ, q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) →
      0 < Work.OddVolterra.RowIdentity.Qx H.h H.x q.1 q.2) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.OddVolterra.RowIdentity.WW H.n H.h H.x H.y) s := by
  have hs_pos : 0 < s := lt_of_lt_of_le H.ha hs.1
  have hs_lt_one : s < 1 := lt_of_le_of_lt hs.2 H.hc1
  have h1s : 0 < 1 - s := by linarith
  -- a small radius, small enough for all the local statements below
  set ε : ℝ := min (min δ s) (1 - s) / 16 with hεdef
  have hε_pos : 0 < ε := by rw [hεdef]; positivity
  have hε8 : 8 * ε < min (min δ s) (1 - s) := by
    rw [hεdef]
    have h : 8 * (min (min δ s) (1 - s) / 16) = min (min δ s) (1 - s) / 2 := by ring
    rw [h]
    linarith [lt_min (lt_min hδ hs_pos) h1s]
  have hεδ : 8 * ε < δ :=
    lt_of_lt_of_le hε8 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεs : 8 * ε < s :=
    lt_of_lt_of_le hε8 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε1s : 8 * ε < 1 - s := lt_of_lt_of_le hε8 (min_le_right _ _)
  have hεδ' : ε < δ := by linarith
  have hεs' : ε < s := by linarith
  have hε1s' : ε < 1 - s := by linarith
  -- global smooth extensions of `y` and `x`
  obtain ⟨ν, hν_sm, hν_eq⟩ := exists_contDiff_eqOn_of_contDiffOn_Ioi
    (c := s - ε) (d := 1 + ε) (by linarith) (by linarith) H.hy
  obtain ⟨μ, hμ_sm, hμ_eq⟩ := exists_contDiff_eqOn_of_contDiffOn_Ioi
    (c := s - ε) (d := 1 + ε) (by linarith) (by linarith) H.hx
  -- the agreement region of the extension lemmas contains `[s-ε, 1+ε]`
  have hcenter : ∀ t : ℝ, t ∈ Set.Icc (s - ε) (1 + ε) →
      |t - ((s - ε) + (1 + ε)) / 2| < ((1 + ε) - (s - ε)) / 2 + (s - ε) / 4 := by
    intro t ht
    have h1 : |t - ((s - ε) + (1 + ε)) / 2| ≤ (1 - s) / 2 + ε := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have h2 : (1 - s) / 2 + ε < ((1 + ε) - (s - ε)) / 2 + (s - ε) / 4 := by linarith
    linarith
  have hν_eq_Icc : ∀ t ∈ Set.Icc (s - ε) (1 + ε), ν t = H.y t :=
    fun t ht => hν_eq t (hcenter t ht)
  have hμ_eq_Icc : ∀ t ∈ Set.Icc (s - ε) (1 + ε), μ t = H.x t :=
    fun t ht => hμ_eq t (hcenter t ht)
  have hν_deriv : ∀ t ∈ Set.Icc (s - ε) (1 + ε), deriv ν t = deriv H.y t := by
    intro t ht
    have hball : t ∈ Metric.ball ((s - ε + (1 + ε)) / 2)
        (((1 + ε) - (s - ε)) / 2 + (s - ε) / 4) := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact hcenter t ht
    have hev : ν =ᶠ[𝓝 t] H.y := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hball] with z hz
      exact hν_eq z (by rwa [Metric.mem_ball, Real.dist_eq] at hz)
    exact hev.deriv_eq
  have hμ_deriv : ∀ t ∈ Set.Icc (s - ε) (1 + ε), deriv μ t = deriv H.x t := by
    intro t ht
    have hball : t ∈ Metric.ball ((s - ε + (1 + ε)) / 2)
        (((1 + ε) - (s - ε)) / 2 + (s - ε) / 4) := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact hcenter t ht
    have hev : μ =ᶠ[𝓝 t] H.x := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hball] with z hz
      exact hμ_eq z (by rwa [Metric.mem_ball, Real.dist_eq] at hz)
    exact hev.deriv_eq
  -- positivity of the frozen factors on the window used by the extension theorem
  have hQy_win : ∀ u : ℝ, |u - s| < 8 * ε → ∀ t ∈ Set.Icc (s - ε) (1 + ε),
      0 < Qy H.h ν u t := by
    intro u hu t ht
    unfold Qy line
    rw [hν_eq_Icc t ht]
    exact hQy (u, t) ⟨by rw [abs_lt] at hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩,
      ⟨by linarith [ht.1], by linarith [ht.2, hεδ]⟩⟩
  have hQx_win : ∀ u : ℝ, |u - s| < 8 * ε → ∀ t ∈ Set.Icc (s - ε) (1 + ε),
      0 < Qx H.h μ u t := by
    intro u hu t ht
    unfold Qx line
    rw [hμ_eq_Icc t ht]
    exact hQx (u, t) ⟨by rw [abs_lt] at hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩,
      ⟨by linarith [ht.1], by linarith [ht.2, hεδ]⟩⟩
  -- globally smooth, globally positive continuations of the two frozen factors
  obtain ⟨Φy, hΦy_sm, hΦy_pos, hΦy_eq⟩ :=
    Work.OddVolterra.Window.exists_pos_smooth_extension
      (Φ := fun q : ℝ × ℝ => Qy H.h ν q.1 q.2) (contDiff_family_Qy H.hh hν_sm)
      (c := s - ε) (d := 1 + ε) (by linarith) (ε := 8 * ε) (by linarith) hQy_win
  obtain ⟨Φx, hΦx_sm, hΦx_pos, hΦx_eq⟩ :=
    Work.OddVolterra.Window.exists_pos_smooth_extension
      (Φ := fun q : ℝ × ℝ => Qx H.h μ q.1 q.2) (contDiff_family_Qx H.hh hμ_sm)
      (c := s - ε) (d := 1 + ε) (by linarith) (ε := 8 * ε) (by linarith) hQx_win
  have hΦy_eq' : ∀ u : ℝ, |u - s| ≤ ε → ∀ t ∈ Set.Icc (s - ε) (1 + ε),
      Φy (u, t) = Qy H.h H.y u t := by
    intro u hu t ht
    have hu' : |u - s| ≤ 8 * ε / 8 := by linarith
    rw [hΦy_eq u hu' t ht]
    unfold Qy line
    rw [hν_eq_Icc t ht]
  have hΦx_eq' : ∀ u : ℝ, |u - s| ≤ ε → ∀ t ∈ Set.Icc (s - ε) (1 + ε),
      Φx (u, t) = Qx H.h H.x u t := by
    intro u hu t ht
    have hu' : |u - s| ≤ 8 * ε / 8 := by linarith
    rw [hΦx_eq u hu' t ht]
    unfold Qx line
    rw [hμ_eq_Icc t ht]
  -- the globally smooth extension of the integrand factor `B`
  let Bext : ℝ × ℝ → ℝ := fun q =>
    (Φy q) ^ ((H.n : ℝ) + 1 / 2) * (-(deriv ν q.2))
      + (Φx q) ^ ((H.n : ℝ) + 1 / 2) * (-(deriv μ q.2))
  have hBext_sm : ContDiff ℝ (⊤ : ℕ∞) Bext := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (Φy q) ^ ((H.n : ℝ) + 1 / 2)) :=
      ContDiff.rpow hΦy_sm contDiff_const (fun q => (hΦy_pos q).ne')
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (Φx q) ^ ((H.n : ℝ) + 1 / 2)) :=
      ContDiff.rpow hΦx_sm contDiff_const (fun q => (hΦx_pos q).ne')
    have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => deriv ν q.2) := by
      have h : ContDiff ℝ (⊤ : ℕ∞) (deriv ν) := by
        simpa [Function.iterate_one] using hν_sm.iterate_deriv 1
      exact h.comp contDiff_snd
    have h4 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => deriv μ q.2) := by
      have h : ContDiff ℝ (⊤ : ℕ∞) (deriv μ) := by
        simpa [Function.iterate_one] using hμ_sm.iterate_deriv 1
      exact h.comp contDiff_snd
    exact (h1.mul h3.neg).add (h2.mul h4.neg)
  have hBext_eq : ∀ u ∈ Set.Icc (s - ε) (s + ε), ∀ σ ∈ Set.Icc (s - ε) (1 + ε),
      Bext (u, σ) = Bfun H.n H.h H.x H.y u σ := by
    intro u hu σ hσ
    have huabs : |u - s| ≤ ε := by
      rw [abs_le]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hΦy_val : Φy (u, σ) = Qy H.h H.y u σ := hΦy_eq' u huabs σ hσ
    have hΦx_val : Φx (u, σ) = Qx H.h H.x u σ := hΦx_eq' u huabs σ hσ
    have hdν : deriv ν σ = deriv H.y σ := hν_deriv σ hσ
    have hdμ : deriv μ σ = deriv H.x σ := hμ_deriv σ hσ
    show (Φy (u, σ)) ^ ((H.n : ℝ) + 1 / 2) * (-(deriv ν σ))
        + (Φx (u, σ)) ^ ((H.n : ℝ) + 1 / 2) * (-(deriv μ σ)) = _
    rw [hΦy_val, hΦx_val, hdν, hdμ]
    rfl
  -- the substituted integral is smooth
  let F : ℝ × ℝ → ℝ := fun q =>
    2 * q.2 ^ (2 * H.n + 2) * Bext (q.1, q.1 + q.2 ^ 2 * (1 - q.1))
  have hF_sm : ContDiff ℝ (⊤ : ℕ∞) F := by
    have hinner : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ => (q.1, q.1 + q.2 ^ 2 * (1 - q.1))) := by fun_prop
    have hθ : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.2 ^ (2 * H.n + 2)) := by fun_prop
    exact (contDiff_const.mul hθ).mul (hBext_sm.comp hinner)
  have hG_sm : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ∫ θ in (0 : ℝ)..1, F (u, θ)) :=
    Work.OddVolterra.Window.contDiff_intervalIntegral_const_bounds hF_sm
  -- assemble
  have hpow : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (1 - u) ^ ((H.n : ℝ) + 3 / 2)) s := by
    have hbase : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => 1 - u) s := by fun_prop
    have hexp : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : ℝ => ((H.n : ℝ) + 3 / 2)) s :=
      contDiffAt_const
    have hne : (1 - s) ≠ 0 := by linarith
    exact hbase.rpow hexp hne
  have hG_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => ∫ θ in (0 : ℝ)..1, F (u, θ)) s :=
    hG_sm.contDiffAt
  refine (hpow.mul hG_at).congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds s hε_pos] with u hu
  rw [Metric.mem_ball, Real.dist_eq] at hu
  have hu_lt1 : u < 1 := by linarith [(abs_lt.mp hu).2, hε1s]
  have hu_pos : 0 < u := by linarith [(abs_lt.mp hu).1, hεs]
  have huI : u ∈ Set.Icc (s - ε) (s + ε) :=
    ⟨by linarith [(abs_lt.mp hu).1], by linarith [(abs_lt.mp hu).2]⟩
  rw [WW_eq_subst H hu_pos hu_lt1]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
  have hσ : u + θ ^ 2 * (1 - u) ∈ Set.Icc (s - ε) (1 + ε) := by
    have hlow : (0 : ℝ) ≤ θ ^ 2 * (1 - u) :=
      mul_nonneg (sq_nonneg θ) (by linarith)
    have hθsq : θ ^ 2 ≤ 1 := by nlinarith [hθ.1, hθ.2]
    have hhigh : θ ^ 2 * (1 - u) ≤ 1 * (1 - u) :=
      mul_le_mul_of_nonneg_right hθsq (by linarith)
    constructor
    · nlinarith [hlow, huI.1]
    · nlinarith [hhigh, hu_lt1]
  show 2 * θ ^ (2 * H.n + 2) * Bfun H.n H.h H.x H.y u (u + θ ^ 2 * (1 - u))
      = 2 * θ ^ (2 * H.n + 2) * Bext (u, u + θ ^ 2 * (1 - u))
  rw [hBext_eq u huI (u + θ ^ 2 * (1 - u)) hσ]

end

end Work.OddVolterra.Smooth
