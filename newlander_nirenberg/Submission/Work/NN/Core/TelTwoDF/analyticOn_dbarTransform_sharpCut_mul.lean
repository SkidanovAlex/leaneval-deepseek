import Mathlib
import Submission.Work.NN.Core.TelTwoDF.analyticOn_cauchyTransform_disc
import Submission.Work.NN.Core.TelTwoDF.analyticOn_integral_of_bounded_support
import Submission.Work.NN.Core.TelTwoDF.dbarTransform_eq_ball
import Submission.Work.NN.Core.sharpCut
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.openSolDefs

/-!
# Real analyticity of the `∂̄`-transform of `sharpCut a b (· s) * D`

Let `D` be real analytic on the polydisc `polydisc 0 Q` and `0 < a < b`, `b ≤ r/2`.
If `ρ' s < a` and `ρ' k < Q k` for `k ≠ s`, then

`z ↦ dbarTransform r s (fun y => sharpCut a b (y s) * D y) z`

is real analytic on `polydisc 0 ρ'`.

The proof rewrites `dbarTransform` in pole form (`dbarTransform_eq_ball`), shrinks the disc of
integration to a disc of radius `b'` with `b < b' < min (Q s) (r - a)` (legitimate because
`sharpCut a b` vanishes off the disc of radius `b`), and splits

`sharpCut a b ζ = 1 + (sharpCut a b ζ - 1)`.

The first summand is the truncated Cauchy transform of `D`, analytic by
`analyticOn_cauchyTransform_disc`; the second has a weight `sharpCut a b - 1` supported in the
annulus `a ≤ ‖ζ‖ ≤ b'`, away from the pole `ζ = z s` (`‖z s‖ < a`), and is handled by
`analyticOn_integral_of_bounded_support`.
-/

namespace Work.NN.Core.TelTwoDF

open MeasureTheory Metric Set
open scoped Topology

/-- If `f` vanishes off `t` and `t ⊆ s`, then the set integrals of `f` over `s` and over `t`
agree. -/
private lemma setIntegral_eq_setIntegral_of_subset {f : ℂ → ℂ} {s t : Set ℂ} (hst : t ⊆ s)
    (h0 : ∀ x ∉ t, f x = 0) : ∫ x in s, f x = ∫ x in t, f x := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => h0 x (fun hxt => hx (hst hxt))),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h0]

/-- Joint real analyticity of `p ↦ D (Function.update p.1 s p.2)` on a product `Ω ×ˢ U`,
provided the update map sends `Ω × U` into the polydisc of analyticity of `D`. -/
private lemma analyticOn_comp_update {n : ℕ} (s : Fin n) {Q : Fin n → ℝ}
    {D : (Fin n → ℂ) → ℂ} (hD : AnalyticOn ℝ D (Work.CR.Flat.polydisc 0 Q))
    {Ω : Set (Fin n → ℂ)} {U : Set ℂ}
    (hmap : ∀ z ∈ Ω, ∀ ζ ∈ U, Function.update z s ζ ∈ Work.CR.Flat.polydisc 0 Q) :
    AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => D (Function.update p.1 s p.2)) (Ω ×ˢ U) := by
  refine hD.comp ?_ ?_
  · refine AnalyticOn.pi (fun k => ?_)
    by_cases hk : k = s
    · have he : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 s p.2 k) = (fun p => p.2) := by
        funext p
        rw [hk]
        exact Function.update_self s p.2 p.1
      rw [he]
      exact ContinuousLinearMap.analyticOn (ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ) _
    · have he : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 s p.2 k) = (fun p => p.1 k) := by
        funext p; exact Function.update_of_ne hk p.2 p.1
      rw [he]
      exact ContinuousLinearMap.analyticOn
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℂ)) _
  · rintro ⟨z, ζ⟩ ⟨hz, hζ⟩
    exact hmap z hz ζ hζ

theorem analyticOn_dbarTransform_sharpCut_mul {n : ℕ} (s : Fin n) {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hbr : b ≤ r / 2)
    {Q ρ' : Fin n → ℝ} (hQ : ∀ k, 0 < Q k) (hbQ : b < Q s) (hρ'a : ρ' s < a)
    (hρ'Q : ∀ k, k ≠ s → ρ' k < Q k)
    {D : (Fin n → ℂ) → ℂ} (hD : AnalyticOn ℝ D (Work.CR.Flat.polydisc 0 Q)) (hDc : Continuous D) :
    AnalyticOn ℝ (fun z : Fin n → ℂ => Work.CR.Flat.Cauchy.dbarTransform r s
        (fun y => Work.NN.Core.sharpCut a b (y s) * D y) z)
      (Work.CR.Flat.polydisc 0 ρ') := by
  classical
  have hbpos : 0 < b := lt_trans ha hab
  have hrpos : 0 < r := by linarith
  have hra : b < r - a := by linarith
  -- ## The shrunk disc radius `b'`
  have hb_bm : b < min (Q s) (r - a) := lt_min hbQ hra
  set b' : ℝ := (b + min (Q s) (r - a)) / 2 with hb'def
  have hbb' : b < b' := by rw [hb'def]; linarith
  have hb'Q : b' < Q s := by
    have h := min_le_left (Q s) (r - a); rw [hb'def]; linarith
  have hb'ra : b' < r - a := by
    have h := min_le_right (Q s) (r - a); rw [hb'def]; linarith
  have hb'pos : 0 < b' := lt_trans hbpos hbb'
  -- ## The annulus radii `c0`, `c1`
  have hmaxa : max (ρ' s) 0 < a := max_lt hρ'a ha
  set c0 : ℝ := (max (ρ' s) 0 + a) / 2 with hc0def
  set c1 : ℝ := (b' + Q s) / 2 with hc1def
  have hc0_lt_a : c0 < a := by rw [hc0def]; linarith
  have hmax_lt_c0 : max (ρ' s) 0 < c0 := by rw [hc0def]; linarith
  have hc1_gt : b' < c1 := by rw [hc1def]; linarith
  have hc1_lt : c1 < Q s := by rw [hc1def]; linarith
  -- ## Real analyticity of the truncated Cauchy transform of `D`
  have hPana : AnalyticOn ℝ (fun z : Fin n → ℂ =>
      ∫ w in Metric.ball (0 : ℂ) b', D (Function.update z s w) / (w - z s))
      (Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ') := by
    have h := analyticOn_cauchyTransform_disc (n := n) s hb'pos hQ hb'Q (g := D) hD
    refine h.mono ?_
    intro z hz
    have hzs : ‖z s‖ < ρ' s := by have := hz s; simpa using this
    refine ⟨?_, fun k hk => ?_⟩
    · exact lt_trans hzs (lt_trans hρ'a (lt_trans hab hbb'))
    · have hzk : ‖z k‖ < ρ' k := by have := hz k; simpa using this
      exact lt_trans hzk (hρ'Q k hk)
  -- ## Real analyticity of the annulus part
  have hQana : AnalyticOn ℝ (fun z : Fin n → ℂ =>
      ∫ ζ in Metric.ball (0 : ℂ) b',
        (Work.NN.Core.sharpCut a b ζ - 1) * D (Function.update z s ζ) / (ζ - z s))
      (Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ') := by
    let Ω : Set (Fin n → ℂ) := Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ'
    let U : Set ℂ := {ζ : ℂ | c0 < ‖ζ‖ ∧ ‖ζ‖ < c1}
    let S : ℂ → ℂ := fun ζ => Work.NN.Core.sharpCut a b ζ - 1
    let K : ℂ → ℂ := (Metric.ball (0 : ℂ) b').indicator S
    let Ffun : (Fin n → ℂ) × ℂ → ℂ :=
      fun p => D (Function.update p.1 s p.2) / (p.2 - p.1 s)
    have hΩopen : IsOpen Ω := Work.CR.Flat.isOpen_polydisc _ _
    have hUopen : IsOpen U := by
      have hUeq : U = {ζ : ℂ | c0 < ‖ζ‖} ∩ {ζ : ℂ | ‖ζ‖ < c1} := by
        ext ζ; simp [U]
      rw [hUeq]
      exact (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    -- the update map is analytic on `Ω × U` and lands in the polydisc of `D`
    have hUpdmap : ∀ z ∈ Ω, ∀ ζ ∈ U, Function.update z s ζ ∈ Work.CR.Flat.polydisc 0 Q := by
      intro z hz ζ hζ
      rw [Work.CR.Flat.mem_polydisc]
      intro k
      simp only [Pi.zero_apply]
      have hz' : ‖z k‖ < ρ' k := by have := hz k; simpa using this
      by_cases hk : k = s
      · rw [hk, Function.update_self]
        simp only [sub_zero]
        linarith [hζ.2, hc1_lt]
      · rw [Function.update_of_ne hk]
        simp only [sub_zero]
        linarith [hz', hρ'Q k hk]
    have hDcomp : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => D (Function.update p.1 s p.2))
        (Ω ×ˢ U) := analyticOn_comp_update s hD hUpdmap
    have hlin : AnalyticOn ℝ (fun p : (Fin n → ℂ) × ℂ => p.2 - p.1 s) (Ω ×ˢ U) := by
      exact ContinuousLinearMap.analyticOn
        (ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ
         - (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) s).comp
             (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℂ)) (Ω ×ˢ U)
    have hne : ∀ p ∈ Ω ×ˢ U, p.2 - p.1 s ≠ 0 := by
      rintro ⟨z, ζ⟩ ⟨hz, hζ⟩ hzero
      have hz' : ‖z s‖ < ρ' s := by have := hz s; simpa using this
      have hlt : ‖z s‖ < c0 :=
        lt_of_lt_of_le hz' (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hmax_lt_c0))
      rw [sub_eq_zero] at hzero
      rw [hzero] at hζ
      exact absurd hlt (not_lt.mpr hζ.1.le)
    have hFfun : AnalyticOn ℝ Ffun (Ω ×ˢ U) := hDcomp.div hlin hne
    -- the weight `K`
    have hSm : Measurable S :=
      ((Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).continuous.sub
        continuous_const).measurable
    have hKm : MeasureTheory.AEStronglyMeasurable K volume :=
      (hSm.indicator measurableSet_ball).aestronglyMeasurable
    have hsuppK : Function.support K ⊆ Metric.closedBall (0 : ℂ) b' := by
      intro ζ hζ
      rw [Function.mem_support] at hζ
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h
      have hb : b' < ‖ζ‖ := not_le.mp h
      have hnot : ζ ∉ Metric.ball (0 : ℂ) b' := by
        intro hmem
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hmem
        linarith [hmem, hb]
      exact hζ (by simp only [K, Set.indicator_of_notMem hnot])
    have hKs : HasCompactSupport K :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) b') hsuppK
    have hKb : ∃ C, ∀ v : ℂ, ‖K v‖ ≤ C := by
      refine ⟨2, fun v => ?_⟩
      by_cases hv : v ∈ Metric.ball (0 : ℂ) b'
      · have hv' : K v = S v := by simp only [K, Set.indicator_of_mem hv]
        rw [hv']
        have h1 := Work.NN.Core.norm_sharpCut_le_one a b v
        calc ‖S v‖ = ‖Work.NN.Core.sharpCut a b v - 1‖ := rfl
          _ ≤ ‖Work.NN.Core.sharpCut a b v‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by rw [norm_one]; linarith
          _ = 2 := by norm_num
      · have hv' : K v = 0 := by simp only [K, Set.indicator_of_notMem hv]
        rw [hv', norm_zero]; norm_num
    have hKU : tsupport K ⊆ U := by
      have hS0 : ∀ x : ℂ, ‖x‖ < a → S x = 0 := by
        intro x hx
        simp only [S, Work.NN.Core.sharpCut_eq_one ha.le hab hx.le, sub_self]
      have hc : tsupport S ⊆ {x : ℂ | a ≤ ‖x‖} :=
        closure_minimal (fun x hx => by
          rw [Function.mem_support] at hx
          by_contra h
          exact hx (hS0 x (not_le.mp h)))
          (isClosed_le continuous_const continuous_norm)
      intro ζ hζ
      have hcl : ζ ∈ Metric.closedBall (0 : ℂ) b' :=
        closure_minimal hsuppK (isCompact_closedBall (0 : ℂ) b').isClosed hζ
      have hSζ : ζ ∈ tsupport S := by
        apply closure_mono (fun x hx => ?_) hζ
        rw [Function.mem_support] at hx ⊢
        intro hS
        exact hx (by
          by_cases hmem : x ∈ Metric.ball (0 : ℂ) b'
          · simp only [K, Set.indicator_of_mem hmem, hS]
          · simp only [K, Set.indicator_of_notMem hmem])
      have ha' : a ≤ ‖ζ‖ := hc hSζ
      rw [Metric.mem_closedBall, dist_zero_right] at hcl
      exact ⟨lt_of_lt_of_le hc0_lt_a ha', lt_of_le_of_lt hcl hc1_gt⟩
    have haux : AnalyticOn ℝ (fun z : Fin n → ℂ => ∫ v : ℂ, K v * Ffun (z, v)) Ω :=
      analyticOn_integral_of_bounded_support hΩopen hUopen hKm hKs hKb hKU hFfun
    refine haux.congr ?_
    intro z hz
    show (∫ ζ in Metric.ball (0 : ℂ) b',
        (Work.NN.Core.sharpCut a b ζ - 1) * D (Function.update z s ζ) / (ζ - z s))
      = ∫ v : ℂ, K v * Ffun (z, v)
    rw [show (fun v : ℂ => K v * Ffun (z, v))
        = (Metric.ball (0 : ℂ) b').indicator (fun v => S v * Ffun (z, v)) from by
      funext v
      simp only [K, Set.indicator_apply]
      split_ifs with hv <;> ring]
    rw [MeasureTheory.integral_indicator measurableSet_ball]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_ball (fun ζ _ => ?_)
    simp only [Ffun, S]
    ring
  -- ## The pointwise identity
  have hkey : ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ',
      Work.CR.Flat.Cauchy.dbarTransform r s
          (fun y => Work.NN.Core.sharpCut a b (y s) * D y) z
        = -((Real.pi : ℂ))⁻¹ *
          ((∫ w in Metric.ball (0 : ℂ) b', D (Function.update z s w) / (w - z s))
           + (∫ ζ in Metric.ball (0 : ℂ) b',
                (Work.NN.Core.sharpCut a b ζ - 1) * D (Function.update z s ζ) / (ζ - z s))) := by
    intro z hz
    have hzs : ‖z s‖ < ρ' s := by have := hz s; simpa using this
    have hzsa : ‖z s‖ < a := lt_trans hzs hρ'a
    set h1 : ℂ → ℂ :=
      fun ζ => (Work.NN.Core.sharpCut a b ζ * D (Function.update z s ζ)) / (ζ - z s) with h1def
    have h1e : ∀ ζ : ℂ, h1 ζ
        = (Work.NN.Core.sharpCut a b ζ * D (Function.update z s ζ)) / (ζ - z s) :=
      fun ζ => by simp only [h1def]
    have hcontupd : Continuous (fun ζ : ℂ => Function.update z s ζ) := by
      refine continuous_pi (fun k => ?_)
      by_cases hk : k = s
      · have he : (fun ζ : ℂ => Function.update z s ζ k) = (fun ζ : ℂ => ζ) := by
          funext ζ; rw [hk]; exact Function.update_self s ζ z
        rw [he]
        exact continuous_id
      · have he : (fun ζ : ℂ => Function.update z s ζ k) = (fun _ : ℂ => z k) := by
          funext ζ; exact Function.update_of_ne hk ζ z
        rw [he]
        exact continuous_const
    have hcontDupd : Continuous (fun ζ : ℂ => D (Function.update z s ζ)) := hDc.comp hcontupd
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
      (isCompact_closedBall (0 : ℂ) b') hcontDupd.continuousOn
    have hMnn : 0 ≤ M :=
      le_trans (norm_nonneg _) (hM 0 (Metric.mem_closedBall_self hb'pos.le))
    have hInt2 : MeasureTheory.IntegrableOn
        (fun ζ : ℂ => D (Function.update z s ζ) * (ζ - z s)⁻¹) (Metric.ball (0 : ℂ) b') := by
      refine (Work.NN.Core.integrableOn_sub_inv_ball b' (z s)).bdd_mul (c := M) ?_ ?_
      · exact hcontDupd.continuousOn.aestronglyMeasurable measurableSet_ball
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with ζ hζ
        exact hM ζ (Metric.ball_subset_closedBall hζ)
    have hInt3 : MeasureTheory.IntegrableOn
        (fun ζ : ℂ => ((Work.NN.Core.sharpCut a b ζ - 1) * D (Function.update z s ζ))
          * (ζ - z s)⁻¹) (Metric.ball (0 : ℂ) b') := by
      refine (Work.NN.Core.integrableOn_sub_inv_ball b' (z s)).bdd_mul (c := 2 * M) ?_ ?_
      · have hc : Continuous (fun ζ : ℂ =>
            (Work.NN.Core.sharpCut a b ζ - 1) * D (Function.update z s ζ)) :=
          ((Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).continuous.sub
            continuous_const).mul hcontDupd
        exact hc.continuousOn.aestronglyMeasurable measurableSet_ball
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with ζ hζ
        have hb1 : ‖Work.NN.Core.sharpCut a b ζ - 1‖ ≤ 2 := by
          have h1' := Work.NN.Core.norm_sharpCut_le_one a b ζ
          calc ‖Work.NN.Core.sharpCut a b ζ - 1‖
              ≤ ‖Work.NN.Core.sharpCut a b ζ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := by rw [norm_one]; linarith
            _ = 2 := by norm_num
        calc ‖(Work.NN.Core.sharpCut a b ζ - 1) * D (Function.update z s ζ)‖
            = ‖Work.NN.Core.sharpCut a b ζ - 1‖ * ‖D (Function.update z s ζ)‖ :=
              norm_mul _ _
          _ ≤ 2 * M :=
              mul_le_mul hb1 (hM ζ (Metric.ball_subset_closedBall hζ)) (norm_nonneg _)
                (by norm_num)
    have hballsub : Metric.ball (0 : ℂ) b' ⊆ Metric.ball (z s) r := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hζ
      rw [Metric.mem_ball, dist_eq_norm]
      have h3 : ‖ζ - z s‖ ≤ ‖ζ‖ + ‖z s‖ := norm_sub_le _ _
      linarith [hζ, hzsa, h3, hb'ra]
    have hzero1 : ∀ ζ ∉ Metric.ball (z s) r, h1 ζ = 0 := by
      intro ζ hζ
      have hb_le : b ≤ ‖ζ‖ := by
        by_contra h
        push_neg at h
        have hmem : ζ ∈ Metric.ball (z s) r := by
          rw [Metric.mem_ball, dist_eq_norm]
          have h3 : ‖ζ - z s‖ ≤ ‖ζ‖ + ‖z s‖ := norm_sub_le _ _
          linarith [h, hzsa, h3]
        exact hζ hmem
      rw [h1e ζ, Work.NN.Core.sharpCut_eq_zero ha.le hab hb_le]
      ring
    have hzero2 : ∀ ζ ∉ Metric.ball (0 : ℂ) b', h1 ζ = 0 := by
      intro ζ hζ
      have hζ' : b' ≤ ‖ζ‖ := by
        have h : ¬ (‖ζ‖ < b') := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
        exact le_of_not_gt h
      have hb_le : b ≤ ‖ζ‖ := le_trans hbb'.le hζ'
      rw [h1e ζ, Work.NN.Core.sharpCut_eq_zero ha.le hab hb_le]
      ring
    have hset : ∫ ζ in Metric.ball (z s) r, h1 ζ = ∫ ζ in Metric.ball (0 : ℂ) b', h1 ζ :=
      setIntegral_eq_setIntegral_of_subset (f := h1) hballsub hzero2
    have hsplit : ∫ ζ in Metric.ball (0 : ℂ) b', h1 ζ
        = (∫ w in Metric.ball (0 : ℂ) b', D (Function.update z s w) / (w - z s))
          + (∫ ζ in Metric.ball (0 : ℂ) b',
              (Work.NN.Core.sharpCut a b ζ - 1) * D (Function.update z s ζ) / (ζ - z s)) := by
      have hcongr : ∫ ζ in Metric.ball (0 : ℂ) b', h1 ζ
          = ∫ ζ in Metric.ball (0 : ℂ) b',
              (D (Function.update z s ζ) * (ζ - z s)⁻¹
               + ((Work.NN.Core.sharpCut a b ζ - 1) * D (Function.update z s ζ))
                 * (ζ - z s)⁻¹) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_ball (fun ζ _ => ?_)
        rw [h1e ζ]
        ring
      rw [hcongr, MeasureTheory.integral_add hInt2 hInt3]
      congr 1
    have hdb : Work.CR.Flat.Cauchy.dbarTransform r s
          (fun y => Work.NN.Core.sharpCut a b (y s) * D y) z
        = -((Real.pi : ℂ))⁻¹ * ∫ ζ in Metric.ball (z s) r, h1 ζ := by
      have hg_cont : Continuous (fun y : Fin n → ℂ => Work.NN.Core.sharpCut a b (y s) * D y) :=
        ((Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).continuous.comp
          (continuous_apply s)).mul hDc
      rw [dbarTransform_eq_ball (ρ := r) s hg_cont z]
      congr 1
      refine MeasureTheory.setIntegral_congr_fun measurableSet_ball (fun ζ _ => ?_)
      rw [h1e ζ]
      simp only [Function.update_self]
    rw [hdb, hset, hsplit]
  -- ## Assembly
  refine ((analyticOn_const (v := -((Real.pi : ℂ))⁻¹)).mul (hPana.add hQana)).congr ?_
  exact hkey

end Work.NN.Core.TelTwoDF
