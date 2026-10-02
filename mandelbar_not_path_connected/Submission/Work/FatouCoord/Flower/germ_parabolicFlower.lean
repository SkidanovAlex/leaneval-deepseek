import Mathlib
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Flower.PsiData
import Submission.Work.FatouCoord.Flower.ConjRefined
import Submission.Work.FatouCoord.Flower.Psi_cover
import Submission.Work.FatouCoord.Flower.Pa_basic
import Submission.Work.FatouCoord.Flower.exists_anti_shift
import Submission.Work.FatouCoord.Flower.exists_phia_pushforward
import Submission.Work.FatouCoord.Flower.rV_window
import Submission.Work.FatouCoord.Flower.rV_tendsto_atTop
import Submission.Work.FatouCoord.Flower.V_preimage
import Submission.Work.FatouCoord.Flower.antiholomorphic_fatou_real
import Submission.Work.FatouCoord.Flower.entire_repelling
import Submission.Work.FatouCoord.Flower.WidePetalPropsAux
import Submission.Work.FatouCoord.Flower.exists_iterate_mem_Petal
import Submission.Work.FatouCoord.Flower.widePetal_growth
import Submission.Work.FatouCoord.Petal.repelling_coord
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.FatouCoord.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Flower

open Work.FatouCoord Set Filter Metric Function
open scoped Topology

noncomputable section

/-! ## Auxiliary lemmas for `germ_parabolicFlower` -/

/-- `ParabolicBounds` is insensitive to shrinking the radius. -/
theorem gpf_bounds_mono {f h : ℂ → ℂ} {a : ℂ} {r r' A A' : ℝ} (hb : ParabolicBounds f h a r A A')
    (hr' : 0 < r') (hle : r' ≤ r) : ParabolicBounds f h a r' A A' := by
  refine ⟨hr', hb.hA, hb.hA', ?_, hb.h_diff.mono (Metric.ball_subset_ball hle), ?_, ?_, ?_⟩
  · intro z hz; exact hb.f_eq z (Metric.ball_subset_ball hle hz)
  · intro z hz; exact hb.h_close z (Metric.ball_subset_ball hle hz)
  · intro z hz; exact hb.h_bound z (Metric.ball_subset_ball hle hz)
  · intro z hz; exact hb.h_deriv_bound z (Metric.ball_subset_ball hle hz)

/-- A holomorphic germ with `f 0 = 0`, `f' 0 = 1` is locally injective at `0`. -/
theorem gpf_localInjOn {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    ∃ ε : ℝ, 0 < ε ∧ Set.InjOn f (Metric.ball 0 ε) := by
  have han : AnalyticAt ℂ f 0 := Petal.parabolic_analyticAt_f hb
  have hstrict : HasStrictDerivAt f (deriv f 0) 0 := han.hasStrictDerivAt
  have hne : deriv f 0 ≠ 0 := by rw [Petal.parabolic_deriv_f_zero hb]; norm_num
  have hev : ∀ᶠ x in 𝓝 (0 : ℂ),
      HasStrictDerivAt.localInverse f (deriv f 0) 0 hstrict hne (f x) = x :=
    hstrict.eventually_left_inverse hne
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε, hε, fun x hx y hy hxy => ?_⟩
  have hx' : HasStrictDerivAt.localInverse f (deriv f 0) 0 hstrict hne (f x) = x := hsub hx
  have hy' : HasStrictDerivAt.localInverse f (deriv f 0) 0 hstrict hne (f y) = y := hsub hy
  rw [hxy] at hx'
  exact hx'.symm.trans hy'

/-- The repelling coordinate `Ψ = -1/V` built from a chart conjugacy `V`. -/
theorem gpf_isRepellingCoord_repPsi {f V : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hVdiff : DifferentiableOn ℂ V {w : ℂ | w.re < -R})
    (hVshift : ∀ w : ℂ, w.re < -R → V (w + 1) = wMap f (V w))
    (hVbd : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ (1 / 2) * ‖w‖)
    (hVne : ∀ w : ℂ, w.re < -R → V w ≠ 0)
    (hVinj : Set.InjOn V {w : ℂ | w.re < -R}) :
    IsRepellingCoord f 0 R (Petal.repPsi f V R) := by
  refine ⟨hR, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : DifferentiableOn ℂ (fun w : ℂ => -1 / V w) {w : ℂ | w.re < -R} :=
      (differentiableOn_const (c := (-1 : ℂ))).div hVdiff fun w hw => hVne w hw
    exact h1.congr (fun w hw => Petal.repPsi_of_mem hw)
  · intro w hw
    by_cases h2 : (w + 1).re < -R
    · rw [Petal.repPsi_of_mem h2, Petal.repPsi_of_mem hw]
      have h := hVshift w hw
      simp only [wMap, chart] at h
      rw [h]
      field_simp
    · have h3 : (w + 1).re < -R + 1 := by
        have : (w + 1).re = w.re + 1 := by simp
        linarith
      rw [Petal.repPsi_of_not_mem h2 h3, Petal.repPsi_of_mem hw]
      congr 1
      ring_nf
  · intro x hx y hy hxy
    rw [Petal.repPsi_of_mem hx, Petal.repPsi_of_mem hy] at hxy
    have h1 : V x = V y := by
      have h2 := congrArg (fun z : ℂ => -1 / z) hxy
      simpa using h2
    exact hVinj hx hy h1
  · intro w hw
    rw [Petal.repPsi_of_mem hw]
    exact div_ne_zero (by norm_num) (hVne w hw)
  · intro ε hε
    refine ⟨max R (2 / ε + 1), fun w hw => ?_⟩
    have hwR : w.re < -R := lt_of_lt_of_le hw (neg_le_neg (le_max_left _ _))
    rw [Petal.repPsi_of_mem hwR, sub_zero]
    have hmax : (2 / ε + 1 : ℝ) ≤ max R (2 / ε + 1) := le_max_right _ _
    have h1 : (2 / ε + 1 : ℝ) ≤ ‖w‖ := by
      calc (2 / ε + 1 : ℝ) ≤ max R (2 / ε + 1) := hmax
        _ ≤ -w.re := by linarith
        _ ≤ ‖w‖ := le_trans (neg_le_abs w.re) (Complex.abs_re_le_norm w)
    have hnorm : 2 / ε < ‖w‖ := by linarith
    have hVw := hVbd w hwR
    have h2 : ‖w‖ / 2 ≤ ‖V w‖ := by
      have h3 : |‖V w‖ - ‖w‖| ≤ ‖V w - w‖ := abs_norm_sub_norm_le (V w) w
      have h3' : ‖w‖ - ‖V w - w‖ ≤ ‖V w‖ := by
        have h := (abs_le.mp h3).1
        linarith
      linarith
    have hwpos : (0 : ℝ) < ‖w‖ := by
      have : (0 : ℝ) < 2 / ε := by positivity
      linarith
    have hVpos : 0 < ‖V w‖ := by linarith
    rw [norm_div, norm_neg, norm_one, div_lt_iff₀ hVpos]
    have h4 : 1 < ε * (‖w‖ / 2) := by
      have h5 : ε * (2 / ε) = 2 := by field_simp
      nlinarith [hε, hnorm]
    have h5 : ε * (‖w‖ / 2) ≤ ε * ‖V w‖ := mul_le_mul_of_nonneg_left h2 hε.le
    linarith

/-- The quantitative step behind `widePetal_growth`, at the explicit threshold: once the
sector value exceeds the threshold the chart dynamics increases `sgauge` by `1/4` and the
real part by `1/2`. -/
theorem gpf_widePetal_growth_step {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') {W : ℂ}
    (hW : 2 * max 1 (max (1 / r) (max 4 (4 * Estimate.Ksub A a))) + 1 < sgauge W) :
    sgauge W + 1 / 4 ≤ sgauge (wMap f W) ∧ (wMap f W).re ≥ W.re + 1 / 2 := by
  have hKnn : 0 ≤ Estimate.Ksub A a := Estimate.Ksub_nonneg hb.hA a
  set K := Estimate.Ksub A a with hKdef
  set L : ℝ := max (1 / r) (max 4 (4 * K)) with hLdef
  have hL4 : (4 : ℝ) ≤ L := le_trans (le_max_left (4 : ℝ) (4 * K)) (le_max_right _ _)
  have hL4K : 4 * K ≤ L := le_trans (le_max_right (4 : ℝ) (4 * K)) (le_max_right _ _)
  have hrle : 1 / r ≤ L := le_max_left _ _
  have hbig : L < ‖W‖ := by
    have h1 : sgauge W / 2 ≤ ‖W‖ := by linarith [sgauge_le_two_norm W]
    have h2 : max 1 L + 1 / 2 < sgauge W / 2 := by linarith
    have hmax1 : (1 : ℝ) ≤ max 1 L := le_max_left _ _
    have hLmax : L ≤ max 1 L := le_max_right _ _
    linarith
  have hx : 1 / r < ‖W‖ := lt_of_le_of_lt hrle hbig
  have hx4 : 4 ≤ ‖W‖ := le_of_lt (lt_of_le_of_lt hL4 hbig)
  have hΔ := Repelling.near_translation_mod hb hx hx4
  have hWpos : (0 : ℝ) < ‖W‖ := by linarith
  have hKle : K / ‖W‖ < 1 / 4 := by
    rw [div_lt_iff₀ hWpos]
    linarith
  have hre : (wMap f W).re ≥ W.re + 1 / 2 := by
    have h1 : |(wMap f W - W - 1).re| ≤ ‖wMap f W - W - 1‖ := Complex.abs_re_le_norm _
    have h2 : |(wMap f W - W - 1).re| ≤ 1 / 4 := le_trans h1 (le_trans hΔ hKle.le)
    have h3 : -(1 / 4) ≤ (wMap f W - W - 1).re := (abs_le.mp h2).1
    simp only [Complex.sub_re, Complex.one_re] at h3
    linarith
  refine ⟨?_, hre⟩
  have him : |(wMap f W).im - W.im| ≤ 1 / 4 := by
    have h1 : |(wMap f W - W - 1).im| ≤ ‖wMap f W - W - 1‖ := Complex.abs_im_le_norm _
    have h2 : |(wMap f W - W - 1).im| ≤ 1 / 4 := le_trans h1 (le_trans hΔ hKle.le)
    simpa using h2
  have h5 : |W.im| - 1 / 4 ≤ |(wMap f W).im| := by
    have h6 : |W.im| - |(wMap f W).im| ≤ |W.im - (wMap f W).im| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_sub_comm] at h6
    linarith
  have h7 : sgauge W + 1 / 4 ≤ sgauge (wMap f W) := by
    rw [sgauge, sgauge]
    linarith
  exact h7

/-- The growth property of the wide petal holds for *every* level above the threshold. -/
theorem gpf_widePetal_growth_mono {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → ∀ W : ℂ, M < sgauge W →
      M < sgauge (wMap f W) ∧ (wMap f W).re ≥ W.re + 1 / 2 := by
  refine ⟨2 * max 1 (max (1 / r) (max 4 (4 * Estimate.Ksub A a))) + 1, fun M hM W hW => ?_⟩
  obtain ⟨h1, h2⟩ := gpf_widePetal_growth_step hb (lt_of_le_of_lt hM hW)
  exact ⟨by linarith, h2⟩

/-- **The Leau–Fatou flower germ.**  A simple parabolic germ `f z = z + z ^ 2 h z` together
with an antiholomorphic square root `gU` (`gU ∘ gU = f`, `gU 0 = 0`, `gU z = star z + O(z ^ 2)`)
has a Leau–Fatou flower at `0`. -/
theorem germ_parabolicFlower {f gU h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {G₀ ρ : ℝ}
    (hf : Differentiable ℂ f) (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hgl : ∀ z : ℂ, ‖z‖ < ρ → ‖gU z - star z‖ ≤ G₀ * ‖z‖ ^ 2)
    (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z)
    (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0) (ha : star a = a) :
    Nonempty (Work.FatouCoord.ParabolicFlower f gU 0) := by
  -- the bounds at the smaller radius
  have hbρ : ParabolicBounds f h a ρ A A' := gpf_bounds_mono hb hρ hρr
  -- local injectivity of `f` at `0`
  obtain ⟨ε, hε, hεinj⟩ := gpf_localInjOn hb
  -- the chart conjugacy `V`
  obtain ⟨R, hRpos, hRr, Z, V, hZdiff, hZbd, hVZ, hVdiff, hVshift, hVbd, hVne, hVinj, hVref⟩ :=
    Rep.exists_conjugacy hb
  have hZfun : ∀ w : ℂ, w.re < -R → V w - w - (1 - a) * Petal.Lambda w = Z w := by
    intro w hw
    have h1 := hVZ w hw
    rw [h1]; ring
  have hZdiff' : DifferentiableOn ℂ (fun w : ℂ => V w - w - (1 - a) * Petal.Lambda w)
      {w : ℂ | w.re < -R} := hZdiff.congr hZfun
  have hZbd' : ∀ w : ℂ, w.re < -R → ‖V w - w - (1 - a) * Petal.Lambda w‖ ≤ 1 / 2 :=
    fun w hw => by rw [hZfun w hw]; exact hZbd w hw
  have hVinv : ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ Y : ℂ, R₁ ≤ ‖Y‖ →
      (Y - (1 - a) * Petal.Lambda Y).re < -R₁ →
      ∃ x : ℂ, x.re < -R ∧ V x = Y ∧ ‖x - (Y - (1 - a) * Petal.Lambda Y)‖ ≤ 4 :=
    V_preimage hb V hVdiff hZdiff' hZbd' hVinj
  -- the local repelling coordinate and its entire extension
  have hΨ₀coord : IsRepellingCoord f 0 R (Petal.repPsi f V R) :=
    gpf_isRepellingCoord_repPsi hRpos hVdiff hVshift hVbd hVne hVinj
  set Ψ₀ : ℂ → ℂ := Petal.repPsi f V R with hΨ₀def
  have hΨ₀mem : ∀ u : ℂ, u.re < -R → Ψ₀ u = -1 / V u :=
    fun u hu => Petal.repPsi_of_mem hu
  set Ψb : ℂ → ℂ := EntireRepelling.rΨ f Ψ₀ R with hΨbdef
  have hΨbshift : ∀ w : ℂ, Ψb (w + 1) = f (Ψb w) :=
    fun w => EntireRepelling.rΨ_shift hΨ₀coord.shift
  have hΨbdiff : Differentiable ℂ Ψb :=
    EntireRepelling.rΨ_differentiable hf hΨ₀coord.shift hΨ₀coord.diff
  have hΨbrV : ∀ w : ℂ, Ψb w = -1 / rV f V R w := rΨ_eq_neg_inv_rV hVshift hΨ₀mem
  have hΨb_eq : ∀ w : ℂ, w.re < -R → Ψb w = -1 / V w := by
    intro w hw
    rw [hΨbrV w, rV_eq_of_re_lt hVshift hw]
  have hΨb_ne : ∀ w : ℂ, w.re < -R → Ψb w ≠ 0 := by
    intro w hw
    rw [hΨb_eq w hw]
    exact div_ne_zero (by norm_num) (hVne w hw)
  have hΨbsmall : ∀ ε' : ℝ, 0 < ε' → ∃ R' : ℝ, ∀ w : ℂ, w.re < -R' → ‖Ψb w‖ < ε' := by
    intro ε' hε'
    obtain ⟨R', hR'⟩ := hΨ₀coord.small ε' hε'
    refine ⟨max R' R, fun w hw => ?_⟩
    have hwR : w.re < -R := lt_of_lt_of_le hw (neg_le_neg (le_max_right R' R))
    have hwR' : w.re < -R' := lt_of_lt_of_le hw (neg_le_neg (le_max_left R' R))
    have h3 : Ψb w = Ψ₀ w := (hΨb_eq w hwR).trans (hΨ₀mem w hwR).symm
    rw [h3]
    simpa using hR' w hwR'
  have hΨbinj : ∃ R₀' : ℝ, Set.InjOn Ψb {w : ℂ | w.re < -R₀'} := by
    refine ⟨R, fun a ha b hb' hab => ?_⟩
    exact hΨ₀coord.inj ha hb' (by
      rw [← EntireRepelling.rΨ_eq_Ψ₀ hΨ₀coord.shift ha,
        ← EntireRepelling.rΨ_eq_Ψ₀ hΨ₀coord.shift hb']
      exact hab)
  -- the antiholomorphic shift constant
  obtain ⟨c, hc_real, hc_anti⟩ :=
    exists_anti_shift (f := f) (gU := gU) (h := h) (a := a) (r := r) hb hgU_anti hgg hgU0 ha
      (R := R) (V := V) hRr hVdiff hVshift hVbd hVref hVinj hVinv
      (Ψ := Ψb) hΨbdiff hΨbshift hΨb_eq
  have hcre : c.re = 0 := by
    have h := congrArg Complex.re hc_real
    simp at h
    linarith
  have hc_re : ∀ w : ℂ, (w + c).re = w.re := by
    intro w
    simp [Complex.add_re, hcre]
  -- the shifted repelling coordinate
  set Ψ : ℂ → ℂ := fun w => Ψb (w + c) with hΨdef
  have hΨ_shift : ∀ w : ℂ, Ψ (w + 1) = f (Ψ w) := by
    intro w
    have h1 : (w + 1) + c = (w + c) + 1 := by ring
    show Ψb ((w + 1) + c) = f (Ψb (w + c))
    rw [h1, hΨbshift]
  have hΨ_anti : ∀ w : ℂ, Ψ (star w + 1 / 2) = gU (Ψ w) := by
    intro w
    exact hc_anti w
  have hΨ_diff : Differentiable ℂ Ψ := hΨbdiff.comp (differentiable_id.add_const c)
  have hΨ_rV : ∀ w : ℂ, Ψ w = -1 / rV f V R (w + c) := fun w => hΨbrV (w + c)
  have hΨ_small : ∀ ε' : ℝ, 0 < ε' → ∃ R' : ℝ, ∀ w : ℂ,
      w.re < -R' → Ψ w ≠ 0 ∧ ‖Ψ w - 0‖ < ε' := by
    intro ε' hε'
    obtain ⟨R', hR'⟩ := hΨbsmall ε' hε'
    refine ⟨max R' R, fun w hw => ?_⟩
    have hwR : w.re < -R := lt_of_lt_of_le hw (neg_le_neg (le_max_right R' R))
    have hwR' : w.re < -R' := lt_of_lt_of_le hw (neg_le_neg (le_max_left R' R))
    have h1 : ‖Ψb (w + c)‖ < ε' := by
      refine hR' (w + c) ?_
      rw [hc_re]; exact hwR'
    have h2 : Ψb (w + c) ≠ 0 := hΨb_ne (w + c) (by rw [hc_re]; exact hwR)
    have h1' : ‖Ψ w - 0‖ < ε' := by
      show ‖Ψb (w + c) - 0‖ < ε'
      rwa [sub_zero]
    exact ⟨h2, h1'⟩
  have hΨ_inj : ∃ R₀' : ℝ, Set.InjOn Ψ {w : ℂ | w.re < -R₀'} := by
    obtain ⟨R₀', hR₀'⟩ := hΨbinj
    refine ⟨R₀', fun a ha b hb' hab => ?_⟩
    have ha' : (a + c).re < -R₀' := by rw [hc_re]; exact ha
    have hb'' : (b + c).re < -R₀' := by rw [hc_re]; exact hb'
    exact add_right_cancel (hR₀' ha' hb'' hab)
  -- ### thresholds
  obtain ⟨M₀w, hgr⟩ := gpf_widePetal_growth_mono hb
  obtain ⟨Mpet, _hMpetpos, hMpet_maps, hMpet_lim, hMpet_fatou, hMpet_inj, _hMpet_img⟩ :=
    exists_petal_fatouCoord hbρ
  obtain ⟨M₀p, hM₀p⟩ := Petal.petal_mapsTo_tendsto_of_le hbρ
  obtain ⟨Manti, s, _hMantipos, hAntiF, hAntiInj⟩ :=
    Anti.antiholomorphic_fatou_real (g := gU) hbρ ha (fun z _ => hgU_anti z)
      (fun z _ => congrFun hgg z) hgU0 (fun z hz => hgl z (mem_ball_zero_iff.mp hz))
  have hAntiF' : IsAntiholomorphicFatouOn gU (fun z => fatouCoord f (1 - a) z + s)
      (Petal ρ Manti) := hAntiF
  have hAntiInj' : Set.InjOn (fun z => fatouCoord f (1 - a) z + s) (Petal ρ Manti) := hAntiInj
  set δinv : ℝ := 1 / ε with hδinvdef
  have hδinv_pos : 0 < δinv := by rw [hδinvdef]; exact one_div_pos.mpr hε
  have hδ : ε * δinv = 1 := by rw [hδinvdef]; field_simp
  set Ms : ℝ := max (max (max M₀w (1 / ρ + 1)) (Real.sqrt 2 * δinv + 1)) 1 with hMsdef
  have hMs_1 : 1 ≤ Ms := le_max_right _ _
  have hMs_pos : 0 < Ms := lt_of_lt_of_le one_pos hMs_1
  have hMs_ge_M₀w : M₀w ≤ Ms :=
    (le_max_left M₀w (1 / ρ + 1)).trans
      ((le_max_left (max M₀w (1 / ρ + 1)) (Real.sqrt 2 * δinv + 1)).trans (le_max_left _ _))
  have hMs_ρ' : 1 / ρ + 1 ≤ Ms :=
    (le_max_right M₀w (1 / ρ + 1)).trans
      ((le_max_left (max M₀w (1 / ρ + 1)) (Real.sqrt 2 * δinv + 1)).trans (le_max_left _ _))
  have hMs_sqrt : Real.sqrt 2 * δinv + 1 ≤ Ms :=
    (le_max_right (max M₀w (1 / ρ + 1)) (Real.sqrt 2 * δinv + 1)).trans (le_max_left _ _)
  have hMs_ρ : 1 / ρ < Ms := lt_of_lt_of_le (by linarith) hMs_ρ'
  have hMs_sqrt' : Real.sqrt 2 * δinv ≤ Ms :=
    le_trans (le_add_of_nonneg_right zero_le_one) hMs_sqrt
  set M : ℝ := max (max (max Ms Mpet) (max M₀p Manti)) 1 with hMdef
  have hM_1 : 1 ≤ M := le_max_right _ _
  have hM_Ms : Ms ≤ M :=
    (le_max_left Ms Mpet).trans
      ((le_max_left (max Ms Mpet) (max M₀p Manti)).trans (le_max_left _ _))
  have hM_Mpet : Mpet ≤ M :=
    (le_max_right Ms Mpet).trans
      ((le_max_left (max Ms Mpet) (max M₀p Manti)).trans (le_max_left _ _))
  have hM_M₀p : M₀p ≤ M :=
    (le_max_left M₀p Manti).trans
      ((le_max_right (max Ms Mpet) (max M₀p Manti)).trans (le_max_left _ _))
  have hM_Manti : Manti ≤ M :=
    (le_max_right M₀p Manti).trans
      ((le_max_right (max Ms Mpet) (max M₀p Manti)).trans (le_max_left _ _))
  have hM_ρ : 1 / ρ < M := lt_of_lt_of_le hMs_ρ hM_Ms
  have hgrMs : ∀ W : ℂ, Ms < sgauge W →
      Ms < sgauge (wMap f W) ∧ (wMap f W).re ≥ W.re + 1 / 2 := hgr Ms hMs_ge_M₀w
  -- ### the Fatou coordinate on the petal
  have hW6 := WPA.widePetal_props hbρ hMs_1 hMs_ρ hgrMs
  have hWide : IsOpen (WidePetal Ms) ∧ IsPreconnected (WidePetal Ms) ∧ (0 : ℂ) ∉ WidePetal Ms ∧
      MapsTo f (WidePetal Ms) (WidePetal Ms) ∧
      (∀ u ∈ WidePetal Ms, Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0)) :=
    ⟨hW6.1, hW6.2.1, hW6.2.2.1, hW6.2.2.2.1, hW6.2.2.2.2.1⟩
  have hWide_ball : WidePetal Ms ⊆ ball 0 ε :=
    le_trans hW6.2.2.2.2.2 (ball_subset_ball (by
      rw [div_le_iff₀ hMs_pos]
      have h2 : ε * (Real.sqrt 2 * δinv) ≤ ε * Ms := mul_le_mul_of_nonneg_left hMs_sqrt' hε.le
      have h3 : ε * (Real.sqrt 2 * δinv) = Real.sqrt 2 := by
        rw [← mul_assoc, mul_comm ε (Real.sqrt 2), mul_assoc, hδ, mul_one]
      linarith))
  -- the petal sits inside the wide petal
  have hsub_petal : Petal ρ M ⊆ WidePetal Ms := by
    intro z hz
    have hz0 : z ≠ 0 := ne_zero_of_mem_Petal hz
    have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    rw [mem_WidePetal]
    refine ⟨hz0, ?_⟩
    have h1 : Ms < ((-1 : ℂ) / z).re := by
      show Ms < (chart z).re
      rw [re_chart hz0, lt_div_iff₀ hns]
      have h2 := hz.2
      have h3 : Ms ≤ M := hM_Ms
      nlinarith [h2, hns, h3]
    have h2 : ((-1 : ℂ) / z).re ≤ sgauge ((-1 : ℂ) / z) := by
      rw [sgauge]
      have := abs_nonneg (((-1 : ℂ) / z).im)
      linarith
    linarith
  -- the Fatou coordinate pushed forward from a half-plane petal
  have hsub_M : Petal ρ M ⊆ Petal ρ Mpet := Petal_mono le_rfl hM_Mpet
  have hsub_Ma : Petal ρ M ⊆ Petal ρ Manti := Petal_mono le_rfl hM_Manti
  have hφ : IsFatouCoordinateOn f (fun z => fatouCoord f (1 - a) z + s) (Petal ρ M) := by
    refine ⟨(hMpet_fatou.1.mono hsub_M).add_const s, fun z hz => ?_⟩
    have h1 := hMpet_fatou.2 z (hsub_M hz)
    show fatouCoord f (1 - a) (f z) + s = (fatouCoord f (1 - a) z + s) + 1
    rw [h1]; ring
  have hφinj : Set.InjOn (fun z => fatouCoord f (1 - a) z + s) (Petal ρ M) := by
    intro x hx y hy hxy
    exact hMpet_inj (hsub_M hx) (hsub_M hy) (add_right_cancel hxy)
  have hanti : IsAntiholomorphicFatouOn gU (fun z => fatouCoord f (1 - a) z + s) (Petal ρ M) :=
    ⟨hAntiF'.1.mono hsub_Ma, hAntiF'.2.1.mono hsub_Ma,
      fun z hz => hAntiF'.2.2 z (hsub_Ma hz)⟩
  have hPmaps : MapsTo f (Petal ρ M) (Petal ρ M) := (hM₀p M hM_M₀p).1
  have hPentry : ∀ x : ℂ, Tendsto (fun n : ℕ => f^[n] x) atTop (nhds 0) →
      (∀ n : ℕ, f^[n] x ≠ 0) → ∃ n : ℕ, f^[n] x ∈ Petal ρ M :=
    exists_iterate_mem_Petal hbρ hMs_1 hMs_ρ hgrMs hM_1 hM_ρ
  -- ### the window thresholds
  have hR₀_ge : R + 1 ≤ R + 1 := le_refl _
  obtain ⟨T₁, hT₁pos, hT₁⟩ :=
    rV_window hb V hVdiff hVshift hVbd hVref (M := Ms) (R₀ := R + 1) (le_of_lt hMs_pos) hR₀_ge
  obtain ⟨T₂, hT₂pos, hT₂⟩ := rV_tendsto_atTop hb hRpos hRr V hVshift hVbd
  set T : ℝ := max (max (T₁ + |c.im| + 1) (T₂ + |c.im| + 1))
      (max (|c.im| + 2 * δinv + 1) 1) with hTdef
  have hT_pos : 0 < T :=
    lt_of_lt_of_le one_pos
      ((le_max_right (|c.im| + 2 * δinv + 1) 1).trans (le_max_right _ _))
  have hT₁_le : T₁ + |c.im| ≤ T := by
    have h : T₁ + |c.im| + 1 ≤ T :=
      (le_max_left (T₁ + |c.im| + 1) (T₂ + |c.im| + 1)).trans (le_max_left _ _)
    linarith
  have hT₂_le : T₂ + |c.im| ≤ T := by
    have h : T₂ + |c.im| + 1 ≤ T :=
      (le_max_right (T₁ + |c.im| + 1) (T₂ + |c.im| + 1)).trans (le_max_left _ _)
    linarith
  have hTδ_le : |c.im| + 2 * δinv ≤ T := by
    have h : |c.im| + 2 * δinv + 1 ≤ T :=
      (le_max_left (|c.im| + 2 * δinv + 1) 1).trans (le_max_right _ _)
    linarith
  -- the "large imaginary part" bounds
  have him_ge : ∀ w : ℂ, |w.im| - |c.im| ≤ |(w + c).im| := by
    intro w
    have h1 : (w + c).im = w.im + c.im := by simp
    rw [h1]
    have h3 : |(w.im + c.im) - c.im| ≤ |w.im + c.im| + |c.im| := abs_sub _ _
    have h4 : (w.im + c.im) - c.im = w.im := by ring
    rw [h4] at h3
    linarith
  -- ### `Pa`
  set Pa : Set ℂ := WidePetal Ms ∪ Ψ '' {w : ℂ | w.re < -(R + 1) ∧ T < |w.im|} with hPadef
  have hne : ∀ w : ℂ, w.re < -(R + 1) → T < |w.im| → Ψ w ≠ 0 := by
    intro w hw1 _hw2 h0
    have hwre : (w + c).re < -R := by
      have := hc_re w
      rw [this] at *
      linarith
    have hwave : Ψ w = -1 / V (w + c) := by rw [hΨ_rV w, rV_eq_of_re_lt hVshift hwre]
    rw [hwave] at h0
    rcases div_eq_zero_iff.mp h0 with h | h
    · norm_num at h
    · exact hVne (w + c) hwre h
  have hwin : ∀ w : ℂ, -(R + 1) - 1 ≤ w.re → w.re < -(R + 1) + 1 → T < |w.im| →
      Ψ w ∈ WidePetal Ms := by
    intro w h1 h2 h3
    have h1' : -(R + 1) - 1 ≤ (w + c).re := by rw [hc_re]; exact h1
    have h2' : (w + c).re < -(R + 1) + 1 := by rw [hc_re]; exact h2
    have h3' : T₁ < |(w + c).im| := by
      have := him_ge w
      linarith
    obtain ⟨hne', hsg⟩ := hT₁ (w + c) h1' h2' h3'
    rw [hΨ_rV w, mem_WidePetal]
    refine ⟨?_, ?_⟩
    · intro h0
      rcases div_eq_zero_iff.mp h0 with h | h
      · norm_num at h
      · exact hne' h
    · rw [neg_one_div_neg_one_div]
      exact hsg
  have hlim : ∀ w : ℂ, w.re < -(R + 1) → T < |w.im| →
      Tendsto (fun n : ℕ => f^[n] (Ψ w)) atTop (nhds 0) := by
    intro w _hw1 hw2
    have him : T₂ < |(w + c).im| := by
      have := him_ge w
      linarith
    have hten := hT₂ (w + c) him
    have h1 : Tendsto (fun n : ℕ => ((‖rV f V R ((w + c) + (n : ℂ))‖ : ℝ))⁻¹) atTop (nhds 0) :=
      hten.inv_tendsto_atTop
    have h2 : Tendsto (fun n : ℕ => Ψb (w + c + (n : ℂ))) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have heq : (fun n : ℕ => ‖Ψb (w + c + (n : ℂ))‖)
          = fun n : ℕ => (‖rV f V R (w + c + (n : ℂ))‖)⁻¹ := by
        funext n
        have hA : Ψb (w + c + (n : ℂ)) = (-1 : ℂ) / rV f V R (w + c + (n : ℂ)) := hΨbrV _
        rw [hA, norm_div, norm_neg, norm_one, one_div]
      rw [heq]
      exact h1
    have h3 : (fun n : ℕ => f^[n] (Ψ w)) = fun n : ℕ => Ψb (w + c + (n : ℂ)) := by
      funext n
      show f^[n] (Ψb (w + c)) = Ψb (w + c + (n : ℂ))
      exact (Psi_add_nat hΨbshift n (w + c)).symm
    rw [h3]
    exact h2
  obtain ⟨hPa_open, hPa_pre, hPa_zero, hPa_maps, hPa_tend⟩ :=
    Pa_basic hΨ_diff (by
      have han : AnalyticOnNhd ℂ Ψ Set.univ := hΨ_diff.differentiableOn.analyticOnNhd isOpen_univ
      rcases han.is_constant_or_isOpenMap with hcst | hop
      · exfalso
        obtain ⟨k, hk⟩ := hcst
        obtain ⟨R₀', hR₀'⟩ := hΨ_inj
        have h1 : Ψ (((-R₀' - 1 : ℝ)) : ℂ) = Ψ (((-R₀' - 2 : ℝ)) : ℂ) := by rw [hk, hk]
        have h2 : (((-R₀' - 1 : ℝ)) : ℂ) = (((-R₀' - 2 : ℝ)) : ℂ) :=
          hR₀' (by simp [Complex.ofReal_re]) (by simp [Complex.ofReal_re]) h1
        have h3 : (-R₀' - 1 : ℝ) = (-R₀' - 2 : ℝ) := Complex.ofReal_injective h2
        linarith
      · exact hop)
      hPadef hne hWide hwin hΨ_shift hlim
  -- `Pa` is small, so `f` is injective on it
  have hPa_ball : Pa ⊆ ball 0 ε := by
    intro z hz
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact hWide_ball hz
    · rw [mem_ball_zero_iff]
      have hwre : (w + c).re < -R := by
        have := hc_re w
        rw [this] at *
        linarith [hw.1]
      have hwave : Ψ w = -1 / V (w + c) := by rw [hΨ_rV w, rV_eq_of_re_lt hVshift hwre]
      rw [hwave]
      have hV2 : ‖w + c‖ / 2 ≤ ‖V (w + c)‖ := by
        have h3 := hVbd (w + c) hwre
        have h4 : ‖w + c‖ ≤ ‖V (w + c)‖ + ‖V (w + c) - (w + c)‖ := by
          calc ‖w + c‖ = ‖V (w + c) - (V (w + c) - (w + c))‖ := by ring_nf
            _ ≤ ‖V (w + c)‖ + ‖V (w + c) - (w + c)‖ := norm_sub_le _ _
        linarith
      have hbig : 2 * δinv < ‖w + c‖ := by
        have h5 : |c.im| + 2 * δinv < |w.im| := by linarith [hTδ_le, hw.2]
        have h6 : |w.im| - |c.im| ≤ |(w + c).im| := him_ge w
        have h7 : |(w + c).im| ≤ ‖w + c‖ := Complex.abs_im_le_norm _
        linarith
      have hVpos : 0 < ‖V (w + c)‖ := by linarith
      have h3 : δinv < ‖V (w + c)‖ := by linarith
      have h4 : ε * δinv < ε * ‖V (w + c)‖ := mul_lt_mul_of_pos_left h3 hε
      rw [norm_div, norm_neg, norm_one, div_lt_iff₀ hVpos]
      linarith
  have hfinj : Set.InjOn f Pa := fun x hx y hy hxy => hεinj (hPa_ball hx) (hPa_ball hy) hxy
  have hPa_ne : ∀ z ∈ Pa, ∀ n : ℕ, f^[n] z ≠ 0 := by
    intro z hz n hn
    have hmem : (0 : ℂ) ∈ Pa := by
      rw [← hn]
      exact mapsTo_iterate_of_mapsTo hPa_maps n hz
    exact hPa_zero hmem
  -- ### the antiholomorphic Fatou coordinate on `Pa`
  obtain ⟨φa, hφa_anti, hφa_inj⟩ :=
    exists_phia_pushforward (f := f) (gU := gU) (φ₀ := fun z => fatouCoord f (1 - a) z + s)
      (P := Petal ρ M) (Pa := Pa) hf hgU_anti isOpen_Petal hPmaps hφ hφinj hanti hgg hgU0
      hPa_maps hPa_zero hPa_tend hPa_ne hfinj hPentry
  -- ### the remaining fields
  have hΨ_ends : ∃ R₀' : ℝ, ∀ w : ℂ, w.re < -R₀' → R₀' < |w.im| → Ψ w ∈ Pa := by
    refine ⟨max (R + 1) T, fun w hw1 hw2 => ?_⟩
    have h1 : w.re < -(R + 1) := by
      have : (R + 1) ≤ max (R + 1) T := le_max_left _ _
      linarith
    have h2 : T < |w.im| := lt_of_le_of_lt (le_max_right (R + 1) T) hw2
    exact Or.inr ⟨w, ⟨h1, h2⟩, rfl⟩
  have hcover : ∀ Rpar : ℝ, ∃ rr : ℝ, 0 < rr ∧ ∀ z : ℂ, 0 < ‖z - 0‖ → ‖z - 0‖ < rr →
      z ∈ Pa ∨ ∃ w : ℂ, w.re < -Rpar ∧ Ψ w = z := by
    intro Rpar
    obtain ⟨rr, hrr, hspec⟩ :=
      Psi_cover hbρ V hVshift hVinv hMs_1 hMs_ρ hc_real hΨ_rV Rpar
    refine ⟨rr, hrr, fun z hz0 hzlt => ?_⟩
    rcases hspec z (by simpa using hz0) (by simpa using hzlt) with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  have hEnter : ∀ z : ℂ, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds 0) →
      (∀ n : ℕ, f^[n] z ≠ 0) → ∃ n : ℕ, f^[n] z ∈ Pa := by
    intro z ht hnz
    obtain ⟨n, hn⟩ := hPentry z ht hnz
    exact ⟨n, Or.inl (hsub_petal hn)⟩
  exact ⟨⟨Pa, φa, Ψ, hPa_open, hPa_pre, hPa_zero, hPa_maps,
    hPa_tend, hEnter, ⟨hφa_anti, hφa_inj⟩, hΨ_diff, hΨ_shift, hΨ_anti, hΨ_small, hΨ_inj,
    hΨ_ends, hcover⟩⟩


end

end Work.FatouCoord.Flower
