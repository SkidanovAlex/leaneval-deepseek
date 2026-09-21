import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.window_iteratedDeriv_of_eventually_pos
import Submission.Work.Analysis.Abel.integral_moving_split_local
import Submission.Work.OddVolterra.RowIdentity.odd_rowH_aux
import Submission.Work.OddVolterra.RowIdentity.Basic
import Submission.Work.OddVolterra.RowIdentity.section_box
import Submission.Work.OddVolterra.RowIdentity.Qy_Qx_rect_pos
import Submission.Work.OddVolterra.RowIdentity.contDiffOn_AH
import Submission.Work.OddVolterra.Swept.swept_iteratedDeriv_rpow_add
import Submission.Work.OddVolterra.Window.window_iteratedDeriv_momentH
import Submission.Work.OddVolterra.Window.contDiffOn_fixed_window
import Submission.Work.OddVolterra.Positivity.base_window_pos
import Submission.Work.OddVolterra.Swept.swept_iteratedDeriv_rpow_add

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle)

noncomputable section

/-!
# The odd centroid-moment row identity

The proof of `Work.OddVolterra.RowIdentity.odd_rowH` follows the same route as the sibling
first row `odd_rowF`:

* split the section integral `momentH` at the base interval `(-X₁, X₁)` (the local Leibniz
  rule `Work.Analysis.Abel.integral_moving_split_local`,
  `Work.OddVolterra.RowIdentity.section_box` for the box containing the sections);
* write the resulting swept integral as `∫_u^1 (σ-u)^{n-1/2} A(u,σ) dσ` (`swept_pointwise`)
  and differentiate it under the integral sign with `swept_iteratedDeriv_rpow_add`;
* identify the resulting integrand with the Abel kernel `Kvec … 1 / √(σ-s)` using
  `kvec_one_div_sqrt_eq`;
* identify the fixed-window part with `E2` using `window_iteratedDeriv_momentH`.
-/

/-- The centroid integrand is `C^n` in the slope variable wherever the radicand is positive. -/
theorem contDiffAt_centroidIntegrand {n : ℕ} (hn : 1 ≤ n) {h f : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s t : ℝ} (hψ : 0 < psi h f s t) :
    ContDiffAt ℝ (n : ℕ∞ω) (fun u : ℝ => centroidIntegrand n h f u t) s := by
  have hh' : ContDiff ℝ (n : ℕ∞ω) h :=
    hh.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hfun : (fun u : ℝ => centroidIntegrand n h f u t)
      = fun u : ℝ => (psi h f u t) ^ ((n : ℝ) - 1 / 2) * lineSlope h u t := by
    funext u
    rw [centroidIntegrand, pow_mul_sqrt_eq_rpow (n - 1) (psi h f u t), cast_sub_half hn]
  rw [hfun]
  have hpsi_fun : (fun u : ℝ => psi h f u t) = fun u => f t ^ 2 - (u * t + h u) ^ 2 := by
    funext u; simp only [psi, line]
  have hpsi : ContDiffAt ℝ (n : ℕ∞ω) (fun u : ℝ => psi h f u t) s := by
    rw [hpsi_fun]; fun_prop
  have hrpow : ContDiffAt ℝ (n : ℕ∞ω)
      (fun z : ℝ => z ^ ((n : ℝ) - 1 / 2)) (psi h f s t) :=
    Real.contDiffAt_rpow_const (Or.inl (ne_of_gt hψ))
  have hdinf : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := hh.deriv'
  have hd : ContDiffAt ℝ (n : ℕ∞ω) (deriv h) s :=
    (hdinf.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞)))).contDiffAt
  have hls : ContDiffAt ℝ (n : ℕ∞ω) (fun u : ℝ => lineSlope h u t) s := by
    have : (fun u : ℝ => lineSlope h u t) = fun u => t + deriv h u := by
      funext u; rw [lineSlope]
    rw [this]
    exact contDiffAt_const.add hd
  exact (hrpow.comp s hpsi).mul hls

/-- On the base window `(-X₁, X₁)` the true profile is the semicircle, so `AAfH` is the
polynomial window integral. -/
theorem AAfH_eq_window (H : Setup) :
    AAfH H.n H.h H.f = fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
      (1 - t ^ 2 - line H.h u t ^ 2) ^ (H.n - 1) *
        Real.sqrt (1 - t ^ 2 - line H.h u t ^ 2) * lineSlope H.h u t := by
  have hle : -(profileX 1) ≤ profileX 1 := by linarith [profileX_one_pos]
  funext u
  rw [AAfH]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hle] at ht
  have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [ht.1, profileX_one_le_one], by linarith [ht.2, profileX_one_le_one]⟩
  have hft : H.f t = semicircle t := H.hfb t ⟨ht.1, ht.2⟩
  have hsq : semicircle t ^ 2 = 1 - t ^ 2 :=
    Commons.Geometry.Ulam.semicircle_sq_of_mem_Icc htIcc
  simp only [centroidIntegrand, psi, line]
  rw [hft, hsq]

/-- The fixed-window part of the centroid moment has `n`-th derivative `E2`. -/
theorem AAfH_iteratedDeriv (H : Setup) {s : ℝ} (hs : s ∈ Set.Icc H.a H.c) :
    iteratedDeriv H.n (AAfH H.n H.h H.f) s = E2 H.n H.h s := by
  have hle : -(profileX 1) ≤ profileX 1 := by linarith [profileX_one_pos]
  obtain ⟨ε, hε, hε'⟩ := Setup.Psi_window_pos H hs
  have hpos : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      0 < 1 - t ^ 2 - line H.h u t ^ 2 :=
    ⟨ε, hε, fun u hu t ht => by simpa [Psi, line] using hε' u hu t ht⟩
  have hwin := Work.OddVolterra.Window.window_iteratedDeriv_momentH (n := H.n) H.hn
    (c := -(profileX 1)) (d := profileX 1) hle H.hh hpos
  rw [AAfH_eq_window H, hwin, E2]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hle] at ht
  have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [ht.1, profileX_one_le_one], by linarith [ht.2, profileX_one_le_one]⟩
  have hsq : semicircle t ^ 2 = 1 - t ^ 2 :=
    Commons.Geometry.Ulam.semicircle_sq_of_mem_Icc htIcc
  simp only [psi, line]
  rw [hsq]

/-- **The kernel identification for the centroid row.**  For `σ > s`, the `n`-th derivative of
the swept integrand `u ↦ WintH n h x y u σ` at `u = s` is the second Abel kernel divided by
`√(σ-s)`. -/
theorem swept_deriv_eq_kernel {n : ℕ} (hn : 1 ≤ n) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hxy : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      f (y u) = u * y u + h u ∧ f (-(x u)) = -(u * (-(x u)) + h u))
    {s σ δ : ℝ} (hsσ : s < σ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hδ : 0 < δ)
    (hQy : ∀ u : ℝ, u ∈ Set.Ioo (s - δ) (s + δ) → 0 < QyH h y u σ)
    (hQx : ∀ u : ℝ, u ∈ Set.Ioo (s - δ) (s + δ) → 0 < QxH h x u σ) :
    iteratedDeriv n (fun u : ℝ => WintH n h x y u σ) s =
      (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 / Real.sqrt (σ - s) := by
  have hs_mem : s ∈ Set.Ioo (s - δ) (s + δ) := ⟨by linarith, by linarith⟩
  have hψy : 0 < psi h f s (y σ) :=
    psi_y_pos_pt (hh.of_le (by norm_cast)) (hxy σ ⟨hσ0, hσ1⟩).1 hsσ (hQy s hs_mem)
  have hψx : 0 < psi h f s (-(x σ)) :=
    psi_negx_pos_pt (hh.of_le (by norm_cast)) (hxy σ ⟨hσ0, hσ1⟩).2 hsσ (hQx s hs_mem)
  have hnear : (fun u : ℝ => WintH n h x y u σ) =ᶠ[𝓝 s]
      (fun u => centroidIntegrand n h f u (y σ) * (-(deriv y σ))
        + centroidIntegrand n h f u (-(x σ)) * (-(deriv x σ))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs_mem, isOpen_Iio.mem_nhds hsσ] with u hu_rect hu_lt
    have huσ : u ≤ σ := le_of_lt hu_lt
    have hy_eq : centroidIntegrand n h f u (y σ)
        = (σ - u) ^ ((n : ℝ) - 1 / 2) * (QyH h y u σ) ^ ((n : ℝ) - 1 / 2) *
          lineSlope h u (y σ) :=
      centroidIntegrand_y_eq_rpow (n := n) hn (hh.of_le (by norm_cast)) huσ
        (le_of_lt (hQy u hu_rect)) (hxy σ ⟨hσ0, hσ1⟩).1
    have hx_eq : centroidIntegrand n h f u (-(x σ))
        = (σ - u) ^ ((n : ℝ) - 1 / 2) * (QxH h x u σ) ^ ((n : ℝ) - 1 / 2) *
          lineSlope h u (-(x σ)) :=
      centroidIntegrand_negx_eq_rpow (n := n) hn (hh.of_le (by norm_cast)) huσ
        (le_of_lt (hQx u hu_rect)) (hxy σ ⟨hσ0, hσ1⟩).2
    rw [hy_eq, hx_eq, WintH, AH]
    ring
  rw [hnear.iteratedDeriv_eq n]
  have h1 : ContDiffAt ℝ (n : ℕ∞ω) (fun u : ℝ => centroidIntegrand n h f u (y σ)) s :=
    contDiffAt_centroidIntegrand hn hh hψy
  have h2 : ContDiffAt ℝ (n : ℕ∞ω) (fun u : ℝ => centroidIntegrand n h f u (-(x σ))) s :=
    contDiffAt_centroidIntegrand hn hh hψx
  have hF1 : ContDiffAt ℝ (n : ℕ∞ω)
      (fun u : ℝ => (-(deriv y σ)) * centroidIntegrand n h f u (y σ)) s :=
    contDiffAt_const.mul h1
  have hF2 : ContDiffAt ℝ (n : ℕ∞ω)
      (fun u : ℝ => (-(deriv x σ)) * centroidIntegrand n h f u (-(x σ))) s :=
    contDiffAt_const.mul h2
  have heq : (fun u : ℝ => centroidIntegrand n h f u (y σ) * (-(deriv y σ))
        + centroidIntegrand n h f u (-(x σ)) * (-(deriv x σ)))
      = fun u : ℝ => (-(deriv y σ)) * centroidIntegrand n h f u (y σ)
        + (-(deriv x σ)) * centroidIntegrand n h f u (-(x σ)) := by
    funext u; ring
  have hsum : iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (y σ) * (-(deriv y σ))
        + centroidIntegrand n h f u (-(x σ)) * (-(deriv x σ))) s
      = (iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (y σ)) s) * (-(deriv y σ))
        + (iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (-(x σ))) s) * (-(deriv x σ)) := by
    have heq2 : (fun u : ℝ => (-(deriv y σ)) * centroidIntegrand n h f u (y σ)
          + (-(deriv x σ)) * centroidIntegrand n h f u (-(x σ)))
        = (fun u : ℝ => (-(deriv y σ)) * centroidIntegrand n h f u (y σ))
          + (fun u : ℝ => (-(deriv x σ)) * centroidIntegrand n h f u (-(x σ))) := rfl
    rw [heq, heq2, iteratedDeriv_add hF1 hF2, iteratedDeriv_const_mul _ h1,
      iteratedDeriv_const_mul _ h2]
    ring
  rw [hsum]
  have hk := kvec_one_div_sqrt_eq (n := n) hn (hh.of_le (by norm_cast)) hsσ
    (hxy σ ⟨hσ0, hσ1⟩).1 (hxy σ ⟨hσ0, hσ1⟩).2 (hQy s hs_mem) (hQx s hs_mem)
  rw [show (iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (y σ)) s) * (-(deriv y σ))
      + (iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (-(x σ))) s) * (-(deriv x σ))
      = -((iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (y σ)) s) * deriv y σ
        + (iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (-(x σ))) s) * deriv x σ) by ring]
  rw [← hk]

/-- **The split of the centroid section integral**: `momentH = AAfH + WWH` for `u ∈ (0,1]`,
provided the sections stay in a fixed interval `[c,d]` and the frozen endpoint factors are
positive. -/
theorem momentH_eq_AAH_add_WWH (H : Setup) {u c d : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hc : ContinuousOn (centroidIntegrand H.n H.h H.f u) (Set.Icc c d))
    (hbox : ∀ σ ∈ Set.Icc u 1, c < -(H.x σ) ∧ -(H.x σ) ≤ d ∧ c ≤ H.y σ ∧ H.y σ < d)
    (henv : ∀ σ ∈ Set.Ioc u 1,
      H.f (H.y σ) = σ * H.y σ + H.h σ ∧ H.f (-(H.x σ)) = -(σ * (-(H.x σ)) + H.h σ))
    (hQy : ∀ σ ∈ Set.Icc u 1, 0 < Qy H.h H.y u σ)
    (hQx : ∀ σ ∈ Set.Icc u 1, 0 < Qx H.h H.x u σ) :
    momentH H.n H.h H.x H.y H.f u = AAfH H.n H.h H.f u + WWH H.n H.h H.x H.y u := by
  have hsplit := Work.Analysis.Abel.integral_moving_split_local
    (x := H.x) (y := H.y) (P := centroidIntegrand H.n H.h H.f u) H.hx H.hy hu hu1 hc hbox
  rw [momentH]
  -- the fixed window
  have hfix : (∫ t in (-(H.x 1))..(H.y 1), centroidIntegrand H.n H.h H.f u t) = AAfH H.n H.h H.f u := by
    rw [H.hxb, H.hyb, AAfH]
  -- the swept part
  have hswept : (∫ σ in u..1, (centroidIntegrand H.n H.h H.f u (H.y σ) * (-(deriv H.y σ))
      + centroidIntegrand H.n H.h H.f u (-(H.x σ)) * (-(deriv H.x σ))))
      = WWH H.n H.h H.x H.y u := by
    rw [WWH]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro σ hσ
    rw [Set.uIoc_of_le hu1] at hσ
    have huσ : u ≤ σ := le_of_lt hσ.1
    have hσ1 : σ ≤ 1 := hσ.2
    have hσ0 : 0 < σ := lt_of_lt_of_le hu hσ.1.le
    have hqy : 0 < QyH H.h H.y u σ := hQy σ ⟨huσ, hσ1⟩
    have hqx : 0 < QxH H.h H.x u σ := hQx σ ⟨huσ, hσ1⟩
    have hmain := swept_pointwise (n := H.n) H.hn (H.hh.of_le (by norm_cast)) huσ
      hqy.le hqx.le (henv σ ⟨hσ.1, hσ1⟩).1 (henv σ ⟨hσ.1, hσ1⟩).2
    rw [hmain, WintH]
  rw [hsplit, hfix, hswept]

theorem odd_rowH (n : ℕ) (hn : 1 ≤ n) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (hc1 : c < 1)
    {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0))
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-1 : ℝ) 1))
    (hxy : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      f (y u) = u * y u + h u ∧ f (-(x u)) = -(u * (-(x u)) + h u))
    (hxdec : ∀ σ ∈ Set.Ioo a 1, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a 1, deriv y σ ≤ 0)
    (hxb : x 1 = Commons.Geometry.Ulam.profileX 1)
    (hyb : y 1 = Commons.Geometry.Ulam.profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      f t = Commons.Geometry.Ulam.semicircle t)
    (hxle : ∀ s ∈ Set.Icc a 1, x 1 ≤ x s) (hyle : ∀ s ∈ Set.Icc a 1, y 1 ≤ y s)
    (hord : -x 1 ≤ y 1)
    (hint : ∀ s ∈ Set.Icc a 1, -(x s) ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1)
    (hKden : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      0 < (y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ)) ∧
      0 < (-(x σ) + hquot h s σ) * (line h σ (-(x σ)) + line h s (-(x σ))))
    (hmid : ∀ s ∈ Set.Icc a 1, ∀ t ∈ Set.Ioo (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < psi h Commons.Geometry.Ulam.semicircle s t)
    {s : ℝ} (hs : s ∈ Set.Icc a c) :
    iteratedDeriv n (fun u : ℝ => momentH n h x y f u) s =
      E2 n h s + ∫ σ in s..1,
        (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 / Real.sqrt (σ - s) := by
  set H : Setup :=
    { n := n, hn := hn, a := a, c := c, ha := ha, hac := hac, hc1 := hc1, h := h, x := x, y := y,
      f := f, hh := hh, hx := hx, hy := hy, hf := hf, hxy := hxy, hxdec := hxdec,
      hydec := hydec, hxb := hxb, hyb := hyb, hfb := hfb, hxle := hxle, hyle := hyle,
      hord := hord, hint := hint,
      hKden := fun s σ hs' hsσ hσ1 => hKden s σ hs' hsσ hσ1, hmid := hmid } with hHdef
  have hHa : H.a = a := by rw [hHdef]
  have hHc : H.c = c := by rw [hHdef]
  have hs' : s ∈ Set.Icc H.a H.c := by rw [hHa, hHc]; exact hs
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 hc1
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  obtain ⟨δQ, hδQpos, hQrect⟩ := Qy_Qx_rect_pos H hs'
  obtain ⟨δB, hδBpos, c₀, d₀, hc₀, hc₀d₀, hd₀, hboxB⟩ := section_box H hs'
  obtain ⟨δS, hδSpos, hδSC⟩ := Work.OddVolterra.Window.contDiffOn_fixed_window H.n H.hn H.hh (by
    obtain ⟨ε, hε, hε'⟩ := Setup.Psi_window_pos H hs'
    exact ⟨ε, hε, fun u hu t ht => by simpa [Psi, line] using hε' u hu t ht⟩)
  set δ : ℝ := min (min δQ δB) (min δS (min (s / 2) ((1 - s) / 2))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδQpos hδBpos) (lt_min hδSpos (lt_min (by linarith) (by linarith)))
  have hδQ : δ ≤ δQ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδB : δ ≤ δB := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδS : δ ≤ δS := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδs : δ ≤ s / 2 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ1s : δ ≤ (1 - s) / 2 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδs' : δ < s := by linarith
  have hδ1s' : δ < 1 - s := by linarith
  -- positivity of the frozen endpoint factors on the box
  have hQbox : ∀ u σ : ℝ, u ∈ Set.Ioo (s - δ) (s + δ) → σ ∈ Set.Ioo (s - δ) (1 + δ) →
      0 < QyH H.h H.y u σ ∧ 0 < QxH H.h H.x u σ := by
    intro u σ hu hσ
    exact hQrect (u, σ)
      ⟨⟨by linarith [hu.1, hδQ], by linarith [hu.2, hδQ]⟩,
       ⟨by linarith [hσ.1, hδQ], by linarith [hσ.2, hδQ]⟩⟩
  -- smoothness of the swept coefficient
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => AH H.n H.h H.x H.y p.1 p.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ)) :=
    contDiffOn_AH (by linarith : 0 < s - δ) H.hh H.hx H.hy hQbox
  -- smoothness of the fixed part
  have hC : ContDiffOn ℝ (⊤ : ℕ∞) (AAfH H.n H.h H.f) (Set.Ioo (s - δ) (s + δ)) := by
    rw [AAfH_eq_window H]
    exact hδSC.mono (Set.Ioo_subset_Ioo (by linarith [hδS]) (by linarith [hδS]))
  -- the eventual split
  have hev : (fun u : ℝ => momentH H.n H.h H.x H.y H.f u) =ᶠ[𝓝 s]
      (fun u => AAfH H.n H.h H.f u + WWH H.n H.h H.x H.y u) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds s hδpos) (fun u hu => ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
    have hu_pos : 0 < u := by linarith [hu.1, hδs, hs0]
    have hu1 : u ≤ 1 := by linarith [hu.2, hδ1s, hs1]
    refine momentH_eq_AAH_add_WWH (c := c₀) (d := d₀) H hu_pos hu1 ?_ ?_ ?_ ?_ ?_
    · have hfcont : ContinuousOn H.f (Set.Icc c₀ d₀) :=
        (H.hf.continuousOn).mono (fun t ht => ⟨by linarith [ht.1, hc₀], by linarith [ht.2, hd₀]⟩)
      have hpsi : ContinuousOn (fun t : ℝ => psi H.h H.f u t) (Set.Icc c₀ d₀) := by
        unfold psi line
        exact (hfcont.pow 2).sub
          (((continuousOn_const.mul continuousOn_id).add continuousOn_const).pow 2)
      have hls : ContinuousOn (fun t : ℝ => lineSlope H.h u t) (Set.Icc c₀ d₀) := by
        unfold lineSlope; fun_prop
      exact ((hpsi.pow (H.n - 1)).mul hpsi.sqrt).mul hls
    · intro σ hσ
      exact hboxB σ ⟨by linarith [hσ.1, hu.1, hδB], hσ.2⟩
    · intro σ hσ
      exact H.hxy σ ⟨lt_of_lt_of_le hu_pos hσ.1.le, hσ.2⟩
    · intro σ hσ
      exact (hQbox u σ ⟨by linarith [hu.1], by linarith [hu.2]⟩
        ⟨by linarith [hσ.1, hu.1, hδdef], by linarith [hσ.2]⟩).1
    · intro σ hσ
      exact (hQbox u σ ⟨by linarith [hu.1], by linarith [hu.2]⟩
        ⟨by linarith [hσ.1, hu.1, hδdef], by linarith [hσ.2]⟩).2
  -- the swept lemma with the additive smooth term
  have hcomb := Work.OddVolterra.Swept.swept_iteratedDeriv_rpow_add (n := H.n - 1) (b := 1) (s := s) (δ := δ)
    hs1 hδpos hA hC
  have hcomb' := hcomb
  rw [Nat.sub_add_cancel H.hn] at hcomb'
  have e1 : (fun u : ℝ => AAfH H.n H.h H.f u +
        ∫ σ in u..1, (σ - u) ^ (((H.n - 1 : ℕ) : ℝ) + 1 / 2) * AH H.n H.h H.x H.y u σ)
      = (fun u : ℝ => AAfH H.n H.h H.f u + WWH H.n H.h H.x H.y u) := by
    funext u
    simp only [WWH, WintH, cast_sub_half H.hn]
  have e2 : ∀ σ : ℝ, iteratedDeriv H.n
        (fun u : ℝ => (σ - u) ^ (((H.n - 1 : ℕ) : ℝ) + 1 / 2) * AH H.n H.h H.x H.y u σ) s
      = iteratedDeriv H.n (fun u : ℝ => WintH H.n H.h H.x H.y u σ) s := by
    intro σ
    congr 1
    funext u
    rw [cast_sub_half H.hn, WintH]
  have hswap : iteratedDeriv H.n (fun u : ℝ => AAfH H.n H.h H.f u + WWH H.n H.h H.x H.y u) s
      = iteratedDeriv H.n (AAfH H.n H.h H.f) s
        + ∫ σ in s..1, iteratedDeriv H.n (fun u : ℝ => WintH H.n H.h H.x H.y u σ) s := by
    rw [← e1, hcomb']
    congr 1
    apply intervalIntegral.integral_congr
    intro σ _
    exact e2 σ
  -- identify the swept derivative with the kernel
  have hkernel : (∫ σ in s..1, iteratedDeriv H.n (fun u : ℝ => WintH H.n H.h H.x H.y u σ) s)
      = ∫ σ in s..1,
          (Kvec H.n H.h s σ (H.x σ) (H.y σ) (deriv H.x σ) (deriv H.y σ)) 1 /
            Real.sqrt (σ - s) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro σ hσ
    rw [Set.uIoc_of_le hs1.le] at hσ
    exact swept_deriv_eq_kernel (n := H.n) H.hn H.hh H.hxy hσ.1 (by linarith [hs0, hσ.1])
      hσ.2 hδpos (fun u hu => (hQbox u σ hu
        ⟨by linarith [hσ.1, hδpos], by linarith [hσ.2, hδpos]⟩).1)
      (fun u hu => (hQbox u σ hu ⟨by linarith [hσ.1, hδpos], by linarith [hσ.2, hδpos]⟩).2)
  rw [hev.iteratedDeriv_eq H.n, hswap, AAfH_iteratedDeriv H hs', hkernel]

end

end Work.OddVolterra.RowIdentity
