import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ODE

open Set Filter
open scoped Topology

/-- **Maximum principle, right side.**  Let `a > 0`, `c < d` with `a * (d - c) < π`.
Let `w` be continuous on `[c,d]`, differentiable on `(c,d)` with derivative `w'`, and let `w'` be
differentiable with derivative `F` on `(c,d)`.  If `w c = 0`, `w` has derivative `0` at `c`, and
`F t + a^2 * w t ≥ 0` on `(c,d)`, then `w ≥ 0` on `[c,d]`. -/
lemma sturm_max_principle_right {a c d : ℝ} (ha : 0 < a) (hcd : c < d) (hdπ : a * (d - c) < Real.pi)
    {w w' F : ℝ → ℝ}
    (hwcont : ContinuousOn w (Set.Icc c d))
    (hwderiv : ∀ t ∈ Set.Ioo c d, HasDerivAt w (w' t) t)
    (hw'deriv : ∀ t ∈ Set.Ioo c d, HasDerivAt w' (F t) t)
    (hc0 : HasDerivAt w 0 c) (hwc : w c = 0)
    (hF : ∀ t ∈ Set.Ioo c d, 0 ≤ F t + a ^ 2 * w t) :
    ∀ t ∈ Set.Icc c d, 0 ≤ w t := by
  have hsin_pos : ∀ t ∈ Set.Ioo c d, 0 < Real.sin (a * (t - c)) := by
    intro t ht
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos ha (by linarith [ht.1])
    · calc a * (t - c) < a * (d - c) := mul_lt_mul_of_pos_left (by linarith [ht.2]) ha
        _ < Real.pi := hdπ
  have hsin_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.sin (a * (s - c)))
      (a * Real.cos (a * (t - c))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a t := by
      have := (hasDerivAt_id t).sub_const c
      simpa using this.const_mul a
    have := h1.sin
    simpa [Real.cos_zero, mul_comm, sub_self, mul_zero] using this
  have hcos_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.cos (a * (s - c)))
      (-(a * Real.sin (a * (t - c)))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a t := by
      have := (hasDerivAt_id t).sub_const c
      simpa using this.const_mul a
    have := h1.cos
    simpa [Real.sin_zero, mul_comm, sub_self, mul_zero] using this
  set Ψ : ℝ → ℝ := fun t => w' t * Real.sin (a * (t - c)) - a * w t * Real.cos (a * (t - c)) with hΨdef
  have hΨ_deriv : ∀ t ∈ Set.Ioo c d,
      HasDerivAt Ψ ((F t + a ^ 2 * w t) * Real.sin (a * (t - c))) t := by
    intro t ht
    have hA : HasDerivAt (fun s : ℝ => w' s * Real.sin (a * (s - c)))
        (F t * Real.sin (a * (t - c)) + w' t * (a * Real.cos (a * (t - c)))) t :=
      (hw'deriv t ht).mul (hsin_deriv t)
    have hB : HasDerivAt (fun s : ℝ => a * w s * Real.cos (a * (s - c)))
        (a * (w' t * Real.cos (a * (t - c)) + w t * (-(a * Real.sin (a * (t - c)))))) t := by
      have h2 : HasDerivAt (fun s : ℝ => w s * Real.cos (a * (s - c)))
          (w' t * Real.cos (a * (t - c)) + w t * (-(a * Real.sin (a * (t - c))))) t :=
        (hwderiv t ht).mul (hcos_deriv t)
      simpa [mul_assoc] using h2.const_mul a
    have hAB := hA.sub hB
    have heq : ((F t * Real.sin (a * (t - c)) + w' t * (a * Real.cos (a * (t - c))))
          - a * (w' t * Real.cos (a * (t - c)) + w t * (-(a * Real.sin (a * (t - c))))))
        = (F t + a ^ 2 * w t) * Real.sin (a * (t - c)) := by ring
    rw [heq] at hAB
    rw [hΨdef]
    exact hAB
  have hdiffOd : DifferentiableOn ℝ Ψ (Set.Ioo c d) :=
    fun x hx => (hΨ_deriv x hx).differentiableAt.differentiableWithinAt
  have hcontOd : ContinuousOn Ψ (Set.Ioo c d) := hdiffOd.continuousOn
  have hPsi_mono : ∀ p ∈ Set.Ioo c d, ∀ q ∈ Set.Ioo c d, p ≤ q → Ψ p ≤ Ψ q := by
    intro p hp q hq hpq
    have hsub : Set.Icc p q ⊆ Set.Ioo c d := fun x hx =>
      ⟨lt_of_lt_of_le hp.1 hx.1, lt_of_le_of_lt hx.2 hq.2⟩
    refine (monotoneOn_of_deriv_nonneg (convex_Icc p q) (hcontOd.mono hsub) ?_ ?_)
      ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
    · rw [interior_Icc]
      exact hdiffOd.mono (fun x hx => ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩)
    · intro x hx
      rw [interior_Icc] at hx
      have hxcd : x ∈ Set.Ioo c d := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
      rw [(hΨ_deriv x hxcd).deriv]
      exact mul_nonneg (hF x hxcd) (hsin_pos x hxcd).le
  set R : ℝ → ℝ := fun t => w t / Real.sin (a * (t - c)) with hRdef
  have hR_deriv : ∀ t ∈ Set.Ioo c d, HasDerivAt R (Ψ t / (Real.sin (a * (t - c))) ^ 2) t := by
    intro t ht
    have hs := hsin_pos t ht
    have h := (hwderiv t ht).div (hsin_deriv t) hs.ne'
    have heqval : (w' t * Real.sin (a * (t - c)) - w t * (a * Real.cos (a * (t - c)))) / Real.sin (a * (t - c)) ^ 2
        = Ψ t / Real.sin (a * (t - c)) ^ 2 := by
      rw [hΨdef]; ring
    rw [hRdef, ← heqval]
    exact h
  have hRdiffOd : DifferentiableOn ℝ R (Set.Ioo c d) :=
    fun x hx => (hR_deriv x hx).differentiableAt.differentiableWithinAt
  have hRcontOd : ContinuousOn R (Set.Ioo c d) := hRdiffOd.continuousOn
  have hw_slope : Tendsto (fun s : ℝ => w s / (s - c)) (𝓝[>] c) (𝓝 0) := by
    have h := (hasDerivAt_iff_tendsto_slope_left_right.mp hc0).2
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field, hwc, sub_zero]
  have hsin_slope : Tendsto (fun s : ℝ => Real.sin (a * (s - c)) / (s - c)) (𝓝[>] c) (𝓝 a) := by
    have hg : HasDerivAt (fun s : ℝ => Real.sin (a * (s - c))) a c := by
      have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a c := by
        have := (hasDerivAt_id c).sub_const c
        simpa using this.const_mul a
      have := h1.sin
      simpa [Real.cos_zero, mul_comm, sub_self, mul_zero] using this
    have h := hg.tendsto_slope
    have h2 := h.mono_left (nhdsGT_le_nhdsNE c)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field]
    simp only [sub_self, mul_zero, Real.sin_zero, sub_zero]
  have hR_tendsto : Tendsto R (𝓝[>] c) (𝓝 0) := by
    have hdiv := hw_slope.div hsin_slope ha.ne'
    simp only [zero_div] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hcd] with s hs
    rw [hRdef]
    have hsne : s - c ≠ 0 := by linarith [hs.1]
    have hsinne : Real.sin (a * (s - c)) ≠ 0 := (hsin_pos s hs).ne'
    simp only [Pi.div_apply]
    field_simp
  have hPsi_nonneg : ∀ t ∈ Set.Ioo c d, 0 ≤ Ψ t := by
    intro u hu
    by_contra hneg
    rw [not_le] at hneg
    have hPsin_neg : ∀ v ∈ Set.Ioo c u, Ψ v < 0 := by
      intro v hv
      have hvcd : v ∈ Set.Ioo c d := ⟨hv.1, lt_trans hv.2 hu.2⟩
      exact lt_of_le_of_lt (hPsi_mono v hvcd u hu hv.2.le) hneg
    have hR_anti : ∀ p ∈ Set.Ioo c u, ∀ q ∈ Set.Ioo c u, p ≤ q → R q ≤ R p := by
      intro p hp q hq hpq
      have hsub : Set.Icc p q ⊆ Set.Ioo c d := fun x hx =>
        ⟨lt_of_lt_of_le hp.1 hx.1, lt_of_le_of_lt hx.2 (lt_trans hq.2 hu.2)⟩
      refine (antitoneOn_of_deriv_nonpos (convex_Icc p q) (hRcontOd.mono hsub) ?_ ?_)
        ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
      · rw [interior_Icc]
        exact hRdiffOd.mono (fun x hx => ⟨lt_trans hp.1 hx.1, lt_trans hx.2 (lt_trans hq.2 hu.2)⟩)
      · intro x hx
        rw [interior_Icc] at hx
        have hxcd : x ∈ Set.Ioo c d := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 (lt_trans hq.2 hu.2)⟩
        have hxcu : x ∈ Set.Ioo c u := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
        rw [(hR_deriv x hxcd).deriv]
        exact div_nonpos_of_nonpos_of_nonneg (hPsin_neg x hxcu).le (sq_nonneg _)
    have hR_le : ∀ v ∈ Set.Ioo c u, R v ≤ 0 := by
      intro v hv
      have hev : ∀ᶠ x in 𝓝[>] c, R v ≤ R x := by
        filter_upwards [Ioo_mem_nhdsGT hv.1] with x hx
        exact hR_anti x ⟨hx.1, lt_trans hx.2 hv.2⟩ v hv hx.2.le
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hR_tendsto hev
    have hw_le : ∀ v ∈ Set.Ioo c u, w v ≤ 0 := by
      intro v hv
      have hvcd : v ∈ Set.Ioo c d := ⟨hv.1, lt_trans hv.2 hu.2⟩
      have hs := hsin_pos v hvcd
      have h := hR_le v hv
      rw [hRdef] at h
      have hv2 : w v = (w v / Real.sin (a * (v - c))) * Real.sin (a * (v - c)) :=
        (div_mul_cancel₀ _ hs.ne').symm
      rw [hv2]
      exact mul_nonpos_of_nonpos_of_nonneg h hs.le
    have hF_nonneg : ∀ v ∈ Set.Ioo c u, 0 ≤ F v := by
      intro v hv
      have hvcd : v ∈ Set.Ioo c d := ⟨hv.1, lt_trans hv.2 hu.2⟩
      have h1 := hF v hvcd
      have h2 := hw_le v hv
      have h3 : a ^ 2 * w v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) h2
      linarith
    have hw'_mono : ∀ p ∈ Set.Ioo c u, ∀ q ∈ Set.Ioo c u, p ≤ q → w' p ≤ w' q := by
      intro p hp q hq hpq
      have hsub : Set.Icc p q ⊆ Set.Ioo c d := fun x hx =>
        ⟨lt_of_lt_of_le hp.1 hx.1, lt_of_le_of_lt hx.2 (lt_trans hq.2 hu.2)⟩
      have hdiff' : DifferentiableOn ℝ w' (Set.Ioo c d) :=
        fun x hx => (hw'deriv x hx).differentiableAt.differentiableWithinAt
      have hcont' : ContinuousOn w' (Set.Icc p q) := hdiff'.continuousOn.mono hsub
      refine (monotoneOn_of_deriv_nonneg (convex_Icc p q) hcont' ?_ ?_)
        ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
      · rw [interior_Icc]
        exact hdiff'.mono (fun x hx => ⟨lt_trans hp.1 hx.1, lt_trans hx.2 (lt_trans hq.2 hu.2)⟩)
      · intro x hx
        rw [interior_Icc] at hx
        have hxcd : x ∈ Set.Ioo c d := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 (lt_trans hq.2 hu.2)⟩
        have hxcu : x ∈ Set.Ioo c u := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
        rw [(hw'deriv x hxcd).deriv]
        exact hF_nonneg x hxcu
    have hw'_nonneg : ∀ v ∈ Set.Ioo c u, 0 ≤ w' v := by
      intro v hv
      have hev : ∀ᶠ s in 𝓝[>] c, w s / (s - c) ≤ w' v := by
        filter_upwards [Ioo_mem_nhdsGT hv.1] with s hs
        have hcs : c < s := hs.1
        have hsd : s < d := lt_trans hs.2 (lt_trans hv.2 hu.2)
        have hcont_s : ContinuousOn w (Set.Icc c s) :=
          hwcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hsd.le⟩)
        have hdiff_s : DifferentiableOn ℝ w (Set.Ioo c s) := fun x hx =>
          (hwderiv x ⟨hx.1, lt_trans hx.2 hsd⟩).differentiableAt.differentiableWithinAt
        obtain ⟨ξ, hξ1, hξ2⟩ := exists_deriv_eq_slope w hcs hcont_s hdiff_s
        have hξcd : ξ ∈ Set.Ioo c d := ⟨hξ1.1, lt_trans hξ1.2 hsd⟩
        have hξcu : ξ ∈ Set.Ioo c u := ⟨hξ1.1, lt_trans hξ1.2 (lt_trans hs.2 hv.2)⟩
        have hderiv : w' ξ = w s / (s - c) := by
          rw [← (hwderiv ξ hξcd).deriv, hξ2, hwc, sub_zero]
        rw [← hderiv]
        exact hw'_mono ξ hξcu v hv (le_of_lt (lt_trans hξ1.2 hs.2))
      exact le_of_tendsto_of_tendsto hw_slope tendsto_const_nhds hev
    have hw_nonneg : ∀ v ∈ Set.Ioo c u, 0 ≤ w v := by
      intro v hv
      have hw_mono : ∀ p ∈ Set.Ioo c u, ∀ q ∈ Set.Ioo c u, p ≤ q → w p ≤ w q := by
        intro p hp q hq hpq
        have hsub : Set.Icc p q ⊆ Set.Icc c d := fun x hx =>
          ⟨le_trans (le_of_lt hp.1) hx.1, le_trans hx.2 (le_of_lt (lt_trans hq.2 hu.2))⟩
        refine (monotoneOn_of_deriv_nonneg (convex_Icc p q) (hwcont.mono hsub) ?_ ?_)
          ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
        · rw [interior_Icc]
          intro x hx
          exact (hwderiv x ⟨lt_trans hp.1 hx.1, lt_trans hx.2 (lt_trans hq.2 hu.2)⟩).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have hxcd : x ∈ Set.Ioo c d := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 (lt_trans hq.2 hu.2)⟩
          rw [(hwderiv x hxcd).deriv]
          exact hw'_nonneg x ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
      have hw_tendsto : Tendsto w (𝓝[>] c) (𝓝 0) := by
        have h := hc0.continuousAt.tendsto
        rw [hwc] at h
        exact h.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ s in 𝓝[>] c, w s ≤ w v := by
        filter_upwards [Ioo_mem_nhdsGT hv.1] with s hs
        exact hw_mono s ⟨hs.1, lt_trans hs.2 hv.2⟩ v hv hs.2.le
      exact le_of_tendsto_of_tendsto hw_tendsto tendsto_const_nhds hev
    obtain ⟨v, hvc, hvu⟩ := exists_between hu.1
    have hvcu : v ∈ Set.Ioo c u := ⟨hvc, hvu⟩
    have hw_le_v := hw_le v hvcu
    have hw_ge_v := hw_nonneg v hvcu
    have hwv : w v = 0 := le_antisymm hw_le_v hw_ge_v
    have hw0 : ∀ s ∈ Set.Ioo c u, w s = 0 := fun s hs =>
      le_antisymm (hw_le s hs) (hw_nonneg s hs)
    have hzero : HasDerivAt w 0 v := by
      have heq : w =ᶠ[𝓝 v] (fun _ : ℝ => (0:ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hvcu] with s hs
        exact hw0 s hs
      exact (hasDerivAt_const v (0:ℝ)).congr_of_eventuallyEq heq
    have hvcd : v ∈ Set.Ioo c d := ⟨hvc, lt_trans hvu hu.2⟩
    have hw'v : w' v = 0 := (hwderiv v hvcd).unique hzero
    have hPsiv : Ψ v = 0 := by
      simp only [hΨdef]
      rw [hw'v, hwv]
      ring
    have hPv := hPsin_neg v hvcu
    rw [hPsiv] at hPv
    exact lt_irrefl 0 hPv
  intro t ht
  have hw_open : ∀ s ∈ Set.Ioo c d, 0 ≤ w s := by
    intro s hs
    have hR_mono : ∀ p ∈ Set.Ioo c d, ∀ q ∈ Set.Ioo c d, p ≤ q → R p ≤ R q := by
      intro p hp q hq hpq
      have hsub : Set.Icc p q ⊆ Set.Ioo c d := fun x hx =>
        ⟨lt_of_lt_of_le hp.1 hx.1, lt_of_le_of_lt hx.2 hq.2⟩
      refine (monotoneOn_of_deriv_nonneg (convex_Icc p q) (hRcontOd.mono hsub) ?_ ?_)
        ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
      · rw [interior_Icc]
        exact hRdiffOd.mono (fun x hx => ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩)
      · intro x hx
        rw [interior_Icc] at hx
        have hxcd : x ∈ Set.Ioo c d := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
        rw [(hR_deriv x hxcd).deriv]
        exact div_nonneg (hPsi_nonneg x hxcd) (sq_nonneg _)
    have hev : ∀ᶠ x in 𝓝[>] c, R s ≥ R x := by
      filter_upwards [Ioo_mem_nhdsGT hs.1] with x hx
      exact hR_mono x ⟨hx.1, lt_trans hx.2 hs.2⟩ s hs hx.2.le
    have hRs : 0 ≤ R s := le_of_tendsto_of_tendsto hR_tendsto tendsto_const_nhds hev
    have hsin := hsin_pos s hs
    have hs2 : w s = R s * Real.sin (a * (s - c)) := by
      rw [hRdef]; exact (div_mul_cancel₀ _ hsin.ne').symm
    rw [hs2]
    exact mul_nonneg hRs hsin.le
  rcases eq_or_lt_of_le ht.1 with hc | hc
  · rw [← hc, hwc]
  · rcases eq_or_lt_of_le ht.2 with hd | hd
    · rw [hd]
      have hle : 𝓝[<] d ≤ 𝓝[Set.Icc c d] d := by
        rw [nhdsWithin_le_iff]
        exact mem_nhdsLT_iff_exists_Ioo_subset.mpr
          ⟨c, hcd, fun x hx => ⟨hx.1.le, hx.2.le⟩⟩
      have htend : Tendsto w (𝓝[<] d) (𝓝 (w d)) :=
        (hwcont.continuousWithinAt (right_mem_Icc.mpr hcd.le)).tendsto.mono_left hle
      have hev : ∀ᶠ x in 𝓝[<] d, 0 ≤ w x := by
        filter_upwards [Ioo_mem_nhdsLT hcd] with x hx
        exact hw_open x hx
      exact le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
    · exact hw_open t ⟨hc, hd⟩

/-- **Maximum principle, left side.**  Let `a > 0`, `d < c` with `a * (c - d) < π`.
Let `w` be continuous on `[d,c]`, differentiable on `(d,c)` with derivative `w'`, and let `w'` be
differentiable with derivative `F` on `(d,c)`.  If `w c = 0`, `w` has derivative `0` at `c`, and
`F t + a^2 * w t ≥ 0` on `(d,c)`, then `w ≥ 0` on `[d,c]`. -/
lemma sturm_max_principle_left {a c d : ℝ} (ha : 0 < a) (hdc : d < c) (hdπ : a * (c - d) < Real.pi)
    {w w' F : ℝ → ℝ}
    (hwcont : ContinuousOn w (Set.Icc d c))
    (hwderiv : ∀ t ∈ Set.Ioo d c, HasDerivAt w (w' t) t)
    (hw'deriv : ∀ t ∈ Set.Ioo d c, HasDerivAt w' (F t) t)
    (hc0 : HasDerivAt w 0 c) (hwc : w c = 0)
    (hF : ∀ t ∈ Set.Ioo d c, 0 ≤ F t + a ^ 2 * w t) :
    ∀ t ∈ Set.Icc d c, 0 ≤ w t := by
  have hsin_neg : ∀ t ∈ Set.Ioo d c, Real.sin (a * (t - c)) < 0 := by
    intro t ht
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · exact mul_neg_of_pos_of_neg ha (by linarith [ht.2])
    · calc -Real.pi < -(a * (c - d)) := by linarith [hdπ]
        _ = a * (d - c) := by ring
        _ < a * (t - c) := mul_lt_mul_of_pos_left (by linarith [ht.1]) ha
  have hsin_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.sin (a * (s - c)))
      (a * Real.cos (a * (t - c))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a t := by
      have := (hasDerivAt_id t).sub_const c
      simpa using this.const_mul a
    have := h1.sin
    simpa [Real.cos_zero, mul_comm, sub_self, mul_zero] using this
  have hcos_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.cos (a * (s - c)))
      (-(a * Real.sin (a * (t - c)))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a t := by
      have := (hasDerivAt_id t).sub_const c
      simpa using this.const_mul a
    have := h1.cos
    simpa [Real.sin_zero, mul_comm, sub_self, mul_zero] using this
  set Ψ : ℝ → ℝ := fun t => w' t * Real.sin (a * (t - c)) - a * w t * Real.cos (a * (t - c)) with hΨdef
  have hΨ_deriv : ∀ t ∈ Set.Ioo d c,
      HasDerivAt Ψ ((F t + a ^ 2 * w t) * Real.sin (a * (t - c))) t := by
    intro t ht
    have hA : HasDerivAt (fun s : ℝ => w' s * Real.sin (a * (s - c)))
        (F t * Real.sin (a * (t - c)) + w' t * (a * Real.cos (a * (t - c)))) t :=
      (hw'deriv t ht).mul (hsin_deriv t)
    have hB : HasDerivAt (fun s : ℝ => a * w s * Real.cos (a * (s - c)))
        (a * (w' t * Real.cos (a * (t - c)) + w t * (-(a * Real.sin (a * (t - c)))))) t := by
      have h2 : HasDerivAt (fun s : ℝ => w s * Real.cos (a * (s - c)))
          (w' t * Real.cos (a * (t - c)) + w t * (-(a * Real.sin (a * (t - c))))) t :=
        (hwderiv t ht).mul (hcos_deriv t)
      simpa [mul_assoc] using h2.const_mul a
    have hAB := hA.sub hB
    have heq : ((F t * Real.sin (a * (t - c)) + w' t * (a * Real.cos (a * (t - c))))
          - a * (w' t * Real.cos (a * (t - c)) + w t * (-(a * Real.sin (a * (t - c))))))
        = (F t + a ^ 2 * w t) * Real.sin (a * (t - c)) := by ring
    rw [heq] at hAB
    rw [hΨdef]
    exact hAB
  have hdiffOd : DifferentiableOn ℝ Ψ (Set.Ioo d c) :=
    fun x hx => (hΨ_deriv x hx).differentiableAt.differentiableWithinAt
  have hcontOd : ContinuousOn Ψ (Set.Ioo d c) := hdiffOd.continuousOn
  have hPsi_anti : ∀ p ∈ Set.Ioo d c, ∀ q ∈ Set.Ioo d c, p ≤ q → Ψ q ≤ Ψ p := by
    intro p hp q hq hpq
    have hsub : Set.Icc p q ⊆ Set.Ioo d c := fun x hx =>
      ⟨lt_of_lt_of_le hp.1 hx.1, lt_of_le_of_lt hx.2 hq.2⟩
    refine (antitoneOn_of_deriv_nonpos (convex_Icc p q) (hcontOd.mono hsub) ?_ ?_)
      ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
    · rw [interior_Icc]
      exact hdiffOd.mono (fun x hx => ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩)
    · intro x hx
      rw [interior_Icc] at hx
      have hxcd : x ∈ Set.Ioo d c := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
      rw [(hΨ_deriv x hxcd).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (hF x hxcd) (hsin_neg x hxcd).le
  set R : ℝ → ℝ := fun t => w t / Real.sin (a * (t - c)) with hRdef
  have hR_deriv : ∀ t ∈ Set.Ioo d c, HasDerivAt R (Ψ t / (Real.sin (a * (t - c))) ^ 2) t := by
    intro t ht
    have hs := hsin_neg t ht
    have h := (hwderiv t ht).div (hsin_deriv t) hs.ne
    have heqval : (w' t * Real.sin (a * (t - c)) - w t * (a * Real.cos (a * (t - c)))) / Real.sin (a * (t - c)) ^ 2
        = Ψ t / Real.sin (a * (t - c)) ^ 2 := by
      rw [hΨdef]; ring
    rw [hRdef, ← heqval]
    exact h
  have hRdiffOd : DifferentiableOn ℝ R (Set.Ioo d c) :=
    fun x hx => (hR_deriv x hx).differentiableAt.differentiableWithinAt
  have hRcontOd : ContinuousOn R (Set.Ioo d c) := hRdiffOd.continuousOn
  have hw_slope : Tendsto (fun s : ℝ => w s / (s - c)) (𝓝[<] c) (𝓝 0) := by
    have h := (hasDerivAt_iff_tendsto_slope_left_right.mp hc0).1
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field, hwc, sub_zero]
  have hsin_slope : Tendsto (fun s : ℝ => Real.sin (a * (s - c)) / (s - c)) (𝓝[<] c) (𝓝 a) := by
    have hg : HasDerivAt (fun s : ℝ => Real.sin (a * (s - c))) a c := by
      have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a c := by
        have := (hasDerivAt_id c).sub_const c
        simpa using this.const_mul a
      have := h1.sin
      simpa [Real.cos_zero, mul_comm, sub_self, mul_zero] using this
    have h := hg.tendsto_slope
    have h2 := h.mono_left (nhdsLT_le_nhdsNE c)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field]
    simp only [sub_self, mul_zero, Real.sin_zero, sub_zero]
  have hR_tendsto : Tendsto R (𝓝[<] c) (𝓝 0) := by
    have hdiv := hw_slope.div hsin_slope ha.ne'
    simp only [zero_div] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hdc] with s hs
    rw [hRdef]
    have hsne : s - c ≠ 0 := by linarith [hs.2]
    have hsinne : Real.sin (a * (s - c)) ≠ 0 := (hsin_neg s hs).ne
    simp only [Pi.div_apply]
    field_simp
  have hPsi_nonneg : ∀ t ∈ Set.Ioo d c, 0 ≤ Ψ t := by
    intro u hu
    by_contra hneg
    rw [not_le] at hneg
    have hPsin_neg : ∀ v ∈ Set.Ioo u c, Ψ v < 0 := by
      intro v hv
      have hvdc : v ∈ Set.Ioo d c := ⟨lt_trans hu.1 hv.1, hv.2⟩
      exact lt_of_le_of_lt (hPsi_anti u hu v hvdc hv.1.le) hneg
    have hR_anti : ∀ p ∈ Set.Ioo u c, ∀ q ∈ Set.Ioo u c, p ≤ q → R q ≤ R p := by
      intro p hp q hq hpq
      have hsub : Set.Icc p q ⊆ Set.Ioo d c := fun x hx =>
        ⟨lt_of_lt_of_le (lt_trans hu.1 hp.1) hx.1, lt_of_le_of_lt hx.2 hq.2⟩
      refine (antitoneOn_of_deriv_nonpos (convex_Icc p q) (hRcontOd.mono hsub) ?_ ?_)
        ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
      · rw [interior_Icc]
        exact hRdiffOd.mono (fun x hx => ⟨lt_trans (lt_trans hu.1 hp.1) hx.1, lt_trans hx.2 hq.2⟩)
      · intro x hx
        rw [interior_Icc] at hx
        have hxdc : x ∈ Set.Ioo d c := ⟨lt_trans (lt_trans hu.1 hp.1) hx.1, lt_trans hx.2 hq.2⟩
        have hxuc : x ∈ Set.Ioo u c := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
        rw [(hR_deriv x hxdc).deriv]
        exact div_nonpos_of_nonpos_of_nonneg (hPsin_neg x hxuc).le (sq_nonneg _)
    have hR_ge : ∀ v ∈ Set.Ioo u c, 0 ≤ R v := by
      intro v hv
      have hev : ∀ᶠ x in 𝓝[<] c, R x ≤ R v := by
        filter_upwards [Ioo_mem_nhdsLT hv.2] with x hx
        exact hR_anti v hv x ⟨lt_trans hv.1 hx.1, hx.2⟩ hx.1.le
      exact le_of_tendsto_of_tendsto hR_tendsto tendsto_const_nhds hev
    have hw_le : ∀ v ∈ Set.Ioo u c, w v ≤ 0 := by
      intro v hv
      have hvdc : v ∈ Set.Ioo d c := ⟨lt_trans hu.1 hv.1, hv.2⟩
      have hs := hsin_neg v hvdc
      have h := hR_ge v hv
      rw [hRdef] at h
      have hv2 : w v = (w v / Real.sin (a * (v - c))) * Real.sin (a * (v - c)) :=
        (div_mul_cancel₀ _ hs.ne).symm
      rw [hv2]
      exact mul_nonpos_of_nonneg_of_nonpos h hs.le
    have hF_nonneg : ∀ v ∈ Set.Ioo u c, 0 ≤ F v := by
      intro v hv
      have hvdc : v ∈ Set.Ioo d c := ⟨lt_trans hu.1 hv.1, hv.2⟩
      have h1 := hF v hvdc
      have h2 := hw_le v hv
      have h3 : a ^ 2 * w v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) h2
      linarith
    have hw'_mono : ∀ p ∈ Set.Ioo u c, ∀ q ∈ Set.Ioo u c, p ≤ q → w' p ≤ w' q := by
      intro p hp q hq hpq
      have hsub : Set.Icc p q ⊆ Set.Ioo d c := fun x hx =>
        ⟨lt_of_lt_of_le (lt_trans hu.1 hp.1) hx.1, lt_of_le_of_lt hx.2 hq.2⟩
      have hdiff' : DifferentiableOn ℝ w' (Set.Ioo d c) :=
        fun x hx => (hw'deriv x hx).differentiableAt.differentiableWithinAt
      have hcont' : ContinuousOn w' (Set.Icc p q) := hdiff'.continuousOn.mono hsub
      refine (monotoneOn_of_deriv_nonneg (convex_Icc p q) hcont' ?_ ?_)
        ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
      · rw [interior_Icc]
        exact hdiff'.mono (fun x hx => ⟨lt_trans (lt_trans hu.1 hp.1) hx.1, lt_trans hx.2 hq.2⟩)
      · intro x hx
        rw [interior_Icc] at hx
        have hxdc : x ∈ Set.Ioo d c := ⟨lt_trans (lt_trans hu.1 hp.1) hx.1, lt_trans hx.2 hq.2⟩
        have hxuc : x ∈ Set.Ioo u c := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
        rw [(hw'deriv x hxdc).deriv]
        exact hF_nonneg x hxuc
    have hw'_nonpos : ∀ v ∈ Set.Ioo u c, w' v ≤ 0 := by
      intro v hv
      have hev : ∀ᶠ s in 𝓝[<] c, w' v ≤ w s / (s - c) := by
        filter_upwards [Ioo_mem_nhdsLT hv.2] with s hs
        have hcs : s < c := hs.2
        have hsd : d < s := lt_trans (lt_trans hu.1 hv.1) hs.1
        have hcont_s : ContinuousOn w (Set.Icc s c) :=
          hwcont.mono (fun x hx => ⟨le_trans hsd.le hx.1, hx.2⟩)
        have hdiff_s : DifferentiableOn ℝ w (Set.Ioo s c) := fun x hx =>
          (hwderiv x ⟨lt_trans hsd hx.1, hx.2⟩).differentiableAt.differentiableWithinAt
        obtain ⟨ξ, hξ1, hξ2⟩ := exists_deriv_eq_slope w hcs hcont_s hdiff_s
        have hξdc : ξ ∈ Set.Ioo d c := ⟨lt_trans hsd hξ1.1, hξ1.2⟩
        have hξuc : ξ ∈ Set.Ioo u c := ⟨lt_trans hv.1 (lt_trans hs.1 hξ1.1), hξ1.2⟩
        have hderiv : w' ξ = w s / (s - c) := by
          rw [← (hwderiv ξ hξdc).deriv, hξ2, hwc, zero_sub, neg_div]
          rw [show s - c = -(c - s) from by ring, div_neg]
        rw [← hderiv]
        exact hw'_mono v hv ξ hξuc (le_of_lt (lt_trans hs.1 hξ1.1))
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hw_slope hev
    have hw_nonneg : ∀ v ∈ Set.Ioo u c, 0 ≤ w v := by
      intro v hv
      have hw_mono : ∀ p ∈ Set.Ioo u c, ∀ q ∈ Set.Ioo u c, p ≤ q → w q ≤ w p := by
        intro p hp q hq hpq
        have hsub : Set.Icc p q ⊆ Set.Icc d c := fun x hx =>
          ⟨le_trans (le_of_lt (lt_trans hu.1 hp.1)) hx.1, le_trans hx.2 hq.2.le⟩
        refine (antitoneOn_of_deriv_nonpos (convex_Icc p q) (hwcont.mono hsub) ?_ ?_)
          ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
        · rw [interior_Icc]
          intro x hx
          exact (hwderiv x ⟨lt_trans (lt_trans hu.1 hp.1) hx.1, lt_trans hx.2 hq.2⟩).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have hxdc : x ∈ Set.Ioo d c := ⟨lt_trans (lt_trans hu.1 hp.1) hx.1, lt_trans hx.2 hq.2⟩
          rw [(hwderiv x hxdc).deriv]
          exact hw'_nonpos x ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
      have hw_tendsto : Tendsto w (𝓝[<] c) (𝓝 0) := by
        have h := hc0.continuousAt.tendsto
        rw [hwc] at h
        exact h.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ s in 𝓝[<] c, w s ≤ w v := by
        filter_upwards [Ioo_mem_nhdsLT hv.2] with s hs
        exact hw_mono v hv s ⟨lt_trans hv.1 hs.1, hs.2⟩ hs.1.le
      exact le_of_tendsto_of_tendsto hw_tendsto tendsto_const_nhds hev
    obtain ⟨v, huv, hvc⟩ := exists_between hu.2
    have hvuc : v ∈ Set.Ioo u c := ⟨huv, hvc⟩
    have hwv : w v = 0 := le_antisymm (hw_le v hvuc) (hw_nonneg v hvuc)
    have hw0 : ∀ s ∈ Set.Ioo u c, w s = 0 := fun s hs =>
      le_antisymm (hw_le s hs) (hw_nonneg s hs)
    have hzero : HasDerivAt w 0 v := by
      have heq : w =ᶠ[𝓝 v] (fun _ : ℝ => (0:ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hvuc] with s hs
        exact hw0 s hs
      exact (hasDerivAt_const v (0:ℝ)).congr_of_eventuallyEq heq
    have hvdc : v ∈ Set.Ioo d c := ⟨lt_trans hu.1 huv, hvc⟩
    have hw'v : w' v = 0 := (hwderiv v hvdc).unique hzero
    have hPsiv : Ψ v = 0 := by
      simp only [hΨdef]
      rw [hw'v, hwv]
      ring
    have hPv := hPsin_neg v hvuc
    rw [hPsiv] at hPv
    exact lt_irrefl 0 hPv
  intro t ht
  have hw_open : ∀ s ∈ Set.Ioo d c, 0 ≤ w s := by
    intro s hs
    have hR_mono : ∀ p ∈ Set.Ioo d c, ∀ q ∈ Set.Ioo d c, p ≤ q → R p ≤ R q := by
      intro p hp q hq hpq
      have hsub : Set.Icc p q ⊆ Set.Ioo d c := fun x hx =>
        ⟨lt_of_lt_of_le hp.1 hx.1, lt_of_le_of_lt hx.2 hq.2⟩
      refine (monotoneOn_of_deriv_nonneg (convex_Icc p q) (hRcontOd.mono hsub) ?_ ?_)
        ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
      · rw [interior_Icc]
        exact hRdiffOd.mono (fun x hx => ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩)
      · intro x hx
        rw [interior_Icc] at hx
        have hxdc : x ∈ Set.Ioo d c := ⟨lt_trans hp.1 hx.1, lt_trans hx.2 hq.2⟩
        rw [(hR_deriv x hxdc).deriv]
        exact div_nonneg (hPsi_nonneg x hxdc) (sq_nonneg _)
    have hev : ∀ᶠ x in 𝓝[<] c, R x ≥ R s := by
      filter_upwards [Ioo_mem_nhdsLT hs.2] with x hx
      exact hR_mono s hs x ⟨lt_trans hs.1 hx.1, hx.2⟩ hx.1.le
    have hRs : R s ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hR_tendsto hev
    have hsin := hsin_neg s hs
    have hs2 : w s = R s * Real.sin (a * (s - c)) := by
      rw [hRdef]; exact (div_mul_cancel₀ _ hsin.ne).symm
    rw [hs2]
    exact mul_nonneg_of_nonpos_of_nonpos hRs hsin.le
  rcases eq_or_lt_of_le ht.2 with hc | hc
  · rw [hc, hwc]
  · rcases eq_or_lt_of_le ht.1 with hd | hd
    · rw [← hd]
      have hle : 𝓝[>] d ≤ 𝓝[Set.Icc d c] d := by
        rw [nhdsWithin_le_iff]
        exact mem_nhdsGT_iff_exists_Ioo_subset.mpr
          ⟨c, hdc, fun x hx => ⟨hx.1.le, hx.2.le⟩⟩
      have htend : Tendsto w (𝓝[>] d) (𝓝 (w d)) :=
        (hwcont.continuousWithinAt (left_mem_Icc.mpr hdc.le)).tendsto.mono_left hle
      have hev : ∀ᶠ x in 𝓝[>] d, 0 ≤ w x := by
        filter_upwards [Ioo_mem_nhdsGT hdc] with x hx
        exact hw_open x hx
      exact le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
    · exact hw_open t ⟨hd, hc⟩

/-- **Sturm / maximum-principle comparison lemma.**  Let `h ≥ 0` be continuous on `[0,T]` with
`h 0 = 0`, differentiable with derivative `g` on `(0,T)`, with `g` differentiable with derivative
`G` on `(0,T)`.  If `G + lam * h ≥ 0` on `(0,T)` and `h` vanishes at some `t₁ ∈ (0,T)` with
`t₁ < π/√lam`, then `h ≡ 0` on `[0,t₁]`. -/
theorem sturm_eqOn_zero_of_second_deriv_add_nonneg {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    (hT' : T < Real.pi / Real.sqrt lam) {h g G : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Icc 0 T)) (h0 : h 0 = 0)
    (hnn : ∀ t ∈ Set.Icc 0 T, 0 ≤ h t)
    (hd1 : ∀ t ∈ Set.Ioo 0 T, HasDerivAt h (g t) t)
    (hd2 : ∀ t ∈ Set.Ioo 0 T, HasDerivAt g (G t) t)
    (hineq : ∀ t ∈ Set.Ioo 0 T, 0 ≤ G t + lam * h t)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Set.Ioo 0 T) (ht₁0 : h t₁ = 0) :
    Set.EqOn h (fun _ => 0) (Set.Icc 0 t₁) := by
  set a : ℝ := Real.sqrt lam with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; exact Real.sqrt_pos_of_pos hlam
  have ha_sq : a ^ 2 = lam := by rw [ha_def]; exact Real.sq_sqrt hlam.le
  have ht₁_lt_a : t₁ < Real.pi / a := by rw [ha_def]; exact lt_trans ht₁.2 hT'
  have ht₁π : a * t₁ < Real.pi := by
    have h1 : a * t₁ < a * (Real.pi / a) := mul_lt_mul_of_pos_left ht₁_lt_a ha_pos
    have h2 : a * (Real.pi / a) = Real.pi := by field_simp
    linarith
  have hg_t₁ : g t₁ = 0 := by
    have hloc : IsLocalMin h t₁ := by
      filter_upwards [Icc_mem_nhds ht₁.1 ht₁.2] with t ht
      rw [ht₁0]
      exact hnn t ht
    exact hloc.hasDerivAt_eq_zero (hd1 t₁ ht₁)
  obtain ⟨c, hc_mem, hc_max⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc ⟨0, left_mem_Icc.mpr ht₁.1.le⟩
      (hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 ht₁.2.le⟩))
  rcases eq_or_ne (h c) 0 with hM | hM
  · intro t ht
    have h1 : h t ≤ 0 := by rw [← hM]; exact hc_max ht
    have h2 : 0 ≤ h t := hnn t ⟨ht.1, le_trans ht.2 ht₁.2.le⟩
    linarith
  · have hc_pos : 0 < h c := lt_of_le_of_ne' (hnn c ⟨hc_mem.1, le_trans hc_mem.2 ht₁.2.le⟩) hM
    have hc0 : 0 < c := by
      rcases eq_or_lt_of_le hc_mem.1 with h | h
      · rw [← h, h0] at hc_pos; exact absurd hc_pos (lt_irrefl 0)
      · exact h
    have hct₁ : c < t₁ := by
      rcases eq_or_lt_of_le hc_mem.2 with h | h
      · rw [h, ht₁0] at hc_pos; exact absurd hc_pos (lt_irrefl 0)
      · exact h
    have hc_Ioo : c ∈ Set.Ioo 0 T := ⟨hc0, lt_trans hct₁ ht₁.2⟩
    have hgc : g c = 0 := by
      have hloc : IsLocalMax h c := by
        filter_upwards [Icc_mem_nhds hc0 hct₁] with t ht
        exact hc_max ht
      exact hloc.hasDerivAt_eq_zero (hd1 c hc_Ioo)
    have hsin_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.sin (a * (s - c)))
        (a * Real.cos (a * (t - c))) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a t := by
        have := (hasDerivAt_id t).sub_const c
        simpa using this.const_mul a
      have := h1.sin
      simpa [Real.cos_zero, mul_comm, sub_self, mul_zero] using this
    have hcos_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.cos (a * (s - c)))
        (-(a * Real.sin (a * (t - c)))) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a t := by
        have := (hasDerivAt_id t).sub_const c
        simpa using this.const_mul a
      have := h1.cos
      simpa [Real.sin_zero, mul_comm, sub_self, mul_zero] using this
    set w : ℝ → ℝ := fun t => h t - h c * Real.cos (a * (t - c)) with hw_def
    set w' : ℝ → ℝ := fun t => g t + h c * a * Real.sin (a * (t - c)) with hw'_def
    set F : ℝ → ℝ := fun t => G t + h c * a ^ 2 * Real.cos (a * (t - c)) with hF_def
    have hw_deriv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt w (w' t) t := by
      intro t ht
      have h2 : HasDerivAt (fun s : ℝ => h c * Real.cos (a * (s - c)))
          (h c * (-(a * Real.sin (a * (t - c))))) t := (hcos_deriv t).const_mul (h c)
      have hd := (hd1 t ht).sub h2
      have heqval : g t - h c * (-(a * Real.sin (a * (t - c)))) = w' t := by
        rw [hw'_def]; ring
      rw [hw_def, ← heqval]
      exact hd
    have hw'_deriv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt w' (F t) t := by
      intro t ht
      have h2 : HasDerivAt (fun s : ℝ => h c * a * Real.sin (a * (s - c)))
          ((h c * a) * (a * Real.cos (a * (t - c)))) t := (hsin_deriv t).const_mul (h c * a)
      have hd := (hd2 t ht).add h2
      have heqval : G t + (h c * a) * (a * Real.cos (a * (t - c))) = F t := by
        rw [hF_def]; ring
      rw [hw'_def, ← heqval]
      exact hd
    have hF_nn : ∀ t ∈ Set.Ioo 0 T, 0 ≤ F t + a ^ 2 * w t := by
      intro t ht
      have hineq_t := hineq t ht
      have key : F t + a ^ 2 * w t = G t + lam * h t := by rw [hF_def, hw_def, ha_sq]; ring
      rw [key]; exact hineq_t
    have hwc : w c = 0 := by simp [hw_def]
    have hw'c : w' c = 0 := by simp [hw'_def, hgc]
    have hw_at_c : HasDerivAt w 0 c := by
      have h := hw_deriv c hc_Ioo
      rwa [hw'c] at h
    have hwcont_R : ContinuousOn w (Set.Icc c t₁) := by
      have h1 : ContinuousOn h (Set.Icc c t₁) :=
        hcont.mono (fun x hx => ⟨le_trans (le_of_lt hc0) hx.1, le_trans hx.2 ht₁.2.le⟩)
      have h2 : ContinuousOn (fun s : ℝ => h c * Real.cos (a * (s - c))) (Set.Icc c t₁) :=
        (by continuity : Continuous (fun s : ℝ => h c * Real.cos (a * (s - c)))).continuousOn
      rw [hw_def]
      exact h1.sub h2
    have hR : ∀ t ∈ Set.Icc c t₁, 0 ≤ w t := by
      refine sturm_max_principle_right (w := w) (w' := w') (F := F) ha_pos hct₁ ?_ hwcont_R ?_ ?_ hw_at_c hwc ?_
      · have h1 : a * (t₁ - c) < a * t₁ := mul_lt_mul_of_pos_left (by linarith [hc0]) ha_pos
        linarith
      · intro t ht
        exact hw_deriv t ⟨lt_trans hc0 ht.1, lt_trans ht.2 ht₁.2⟩
      · intro t ht
        exact hw'_deriv t ⟨lt_trans hc0 ht.1, lt_trans ht.2 ht₁.2⟩
      · intro t ht
        exact hF_nn t ⟨lt_trans hc0 ht.1, lt_trans ht.2 ht₁.2⟩
    have hcos₁ : Real.cos (a * (t₁ - c)) ≤ 0 := by
      have hR1 := hR t₁ ⟨hct₁.le, le_refl t₁⟩
      have hw_eq : w t₁ = -h c * Real.cos (a * (t₁ - c)) := by
        simp only [hw_def, ht₁0]; ring
      rw [hw_eq] at hR1
      have h' : h c * Real.cos (a * (t₁ - c)) ≤ 0 := by linarith
      have h'0 : h c * Real.cos (a * (t₁ - c)) ≤ h c * 0 := by rw [mul_zero]; exact h'
      exact le_of_mul_le_mul_left h'0 hc_pos
    have hwcont_L : ContinuousOn w (Set.Icc 0 c) := by
      have h1 : ContinuousOn h (Set.Icc 0 c) :=
        hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hc_Ioo.2.le⟩)
      have h2 : ContinuousOn (fun s : ℝ => h c * Real.cos (a * (s - c))) (Set.Icc 0 c) :=
        (by continuity : Continuous (fun s : ℝ => h c * Real.cos (a * (s - c)))).continuousOn
      rw [hw_def]
      exact h1.sub h2
    have hL : ∀ t ∈ Set.Icc 0 c, 0 ≤ w t := by
      refine sturm_max_principle_left (w := w) (w' := w') (F := F) ha_pos hc0 ?_ hwcont_L ?_ ?_ hw_at_c hwc ?_
      · have h1 : a * c < a * t₁ := mul_lt_mul_of_pos_left hct₁ ha_pos
        linarith
      · intro t ht
        exact hw_deriv t ⟨ht.1, lt_trans ht.2 hc_Ioo.2⟩
      · intro t ht
        exact hw'_deriv t ⟨ht.1, lt_trans ht.2 hc_Ioo.2⟩
      · intro t ht
        exact hF_nn t ⟨ht.1, lt_trans ht.2 hc_Ioo.2⟩
    have hcos0 : Real.cos (a * c) ≤ 0 := by
      have hL1 := hL 0 ⟨le_refl 0, hc0.le⟩
      have hw_eq : w 0 = -h c * Real.cos (a * c) := by
        have harg : a * (0 - c) = -(a * c) := by ring
        simp only [hw_def, h0, harg, Real.cos_neg]
        ring
      rw [hw_eq] at hL1
      have h' : h c * Real.cos (a * c) ≤ 0 := by linarith
      have h'0 : h c * Real.cos (a * c) ≤ h c * 0 := by rw [mul_zero]; exact h'
      exact le_of_mul_le_mul_left h'0 hc_pos
    have hge1 : Real.pi / 2 ≤ a * (t₁ - c) := by
      have hpos : 0 < a * (t₁ - c) := mul_pos ha_pos (by linarith)
      by_contra hcon
      push Not at hcon
      have : 0 < Real.cos (a * (t₁ - c)) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos, Real.pi_pos], hcon⟩
      linarith
    have hge0 : Real.pi / 2 ≤ a * c := by
      have hpos : 0 < a * c := mul_pos ha_pos hc0
      by_contra hcon
      push Not at hcon
      have : 0 < Real.cos (a * c) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos, Real.pi_pos], hcon⟩
      linarith
    have : Real.pi ≤ a * t₁ := by
      have : a * t₁ = a * c + a * (t₁ - c) := by ring
      linarith
    linarith

end Commons.Analysis.ODE