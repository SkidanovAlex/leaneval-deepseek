import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Arc.branch_count
import Submission.Work.WilE3.Taylor.Arc.eaEvalC_arc_order
import Submission.Work.WilE3.Taylor.Arc.complexify_order
import Submission.Work.WilE3.Taylor.Arc.order_restrict
import Submission.Work.WilE3.Taylor.Arc.fibre_card_le
import Submission.Work.WilE3.Taylor.Arc.ofReal_order
import Submission.Work.WilE3.Taylor.Arc.card_le_mul_card_image
import Submission.Work.WilE3.Frame.exists_card_solutions_simple_tendsto
import Submission.Work.WilE3.Frame.eaEvalC_toC
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

open Filter
open scoped Topology

namespace Work.WilE3.Taylor.Grad

/-- A punctured-neighbourhood `∀ᶠ` statement is an explicit `ε`-`δ` statement:  if
eventually in `𝓝[≠] 0` the predicate `P` holds, then for all small nonzero `ε` the predicate
holds.  (The converse is not needed.) -/
private lemma punctured_eventually_iff {P : ℂ → Prop}
    (h : ∀ᶠ ε in nhdsWithin (0 : ℂ) {0}ᶜ, P ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → P ε := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hδp⟩ := h
  exact ⟨δ, hδ, fun ε h0 hlt => hδp (by simpa [dist_eq_norm] using hlt) (by simpa using h0)⟩

/-- **The complexification of a ramified real analytic arc.**

Let `γ` be a real analytic arc at `0` with `γ 0 = y` and `ord_0 (γ - y) = a ≥ 1`.  Then `γ - y`
factors as `t ^ a • u t` near `0` with `u` real analytic at `0` and `u 0 ≠ 0` (the finite order
factorisation `AnalyticAt.analyticOrderNatAt_eq_iff`).  Complexifying the coordinates of `u`
(`Arc.complexify_order`) and setting `σ s := toC y + s ^ a • v s` gives a complex analytic arc `σ`
through the complex point `toC y` which ramifies of order exactly `a` at `0`
(`σ s - σ 0 = s ^ a • v s`, `v 0 ≠ 0`) and agrees with `toC ∘ γ` near `0` on the real axis. -/
private lemma ramifiedComplexification {k : ℕ} {γ : ℝ → Fin k → ℝ} {y : Fin k → ℝ} {a : ℕ}
    (hγ : AnalyticAt ℝ γ 0) (ha : 0 < a)
    (hram : analyticOrderAt (fun t : ℝ => γ t - y) 0 = a) :
    ∃ (σ : ℂ → Fin k → ℂ) (v : ℂ → Fin k → ℂ),
      AnalyticAt ℂ σ 0 ∧ (∀ i, AnalyticAt ℂ (fun s : ℂ => v s i) 0) ∧
      v 0 ≠ 0 ∧ (∀ s : ℂ, σ s - σ 0 = s ^ a • v s) ∧
      σ 0 = Work.WilE3.Frame.toC y ∧
      Filter.Eventually (fun t : ℝ => σ (t : ℂ) = Work.WilE3.Frame.toC (γ t)) (nhds (0 : ℝ)) := by
  have hf : AnalyticAt ℝ (fun t : ℝ => γ t - y) 0 := hγ.sub analyticAt_const
  have hne_top : analyticOrderAt (fun t : ℝ => γ t - y) 0 ≠ ⊤ := by
    rw [hram]; exact ENat.natCast_ne_top a
  have hnat : analyticOrderNatAt (fun t : ℝ => γ t - y) 0 = a := by
    have h := Nat.cast_analyticOrderNatAt (f := fun t : ℝ => γ t - y) (z₀ := (0 : ℝ)) hne_top
    rw [hram] at h
    exact Nat.cast_injective h
  obtain ⟨u, huan, hu0, hufact⟩ := (hf.analyticOrderNatAt_eq_iff hne_top).mp hnat
  -- Complexify the coordinates of `u`.
  have hu_coord : ∀ i : Fin k, AnalyticAt ℝ (fun t : ℝ => u t i) 0 := fun i =>
    ((ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).analyticAt (u 0)).comp huan
  choose F ρ hρpos hFan hFeq _hFord using
    fun i => Work.WilE3.Taylor.Arc.complexify_order (fun t : ℝ => u t i) (hu_coord i)
  obtain ⟨ρ₀, hρ₀pos, hρ₀le⟩ := Work.WilE3.Taylor.Arc.exists_pos_le_all hρpos
  refine ⟨fun s i => (y i : ℂ) + s ^ a * F i s, fun s i => F i s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- analyticity of `σ`
    refine AnalyticAt.pi (f := fun (i : Fin k) (s : ℂ) => (y i : ℂ) + s ^ a * F i s) fun i => ?_
    have hFi : AnalyticAt ℂ (fun s : ℂ => F i s) 0 :=
      hFan i 0 (by rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hρpos i)
    exact analyticAt_const.add ((analyticAt_id.pow a).mul hFi)
  · -- analyticity of `v`
    intro i
    exact hFan i 0 (by rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hρpos i)
  · -- `v 0 ≠ 0`
    intro hcontra
    obtain ⟨i, hi⟩ : ∃ i : Fin k, u 0 i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hu0 (funext h)
    have hFi0 : F i 0 = ((u 0 i : ℝ) : ℂ) := hFeq i 0 (by rw [abs_zero]; exact hρpos i)
    have hz : F i 0 = 0 := congr_fun hcontra i
    rw [hFi0] at hz
    exact hi (Complex.ofReal_eq_zero.mp hz)
  · -- the ramification identity, valid for every `s`
    intro s
    funext i
    show ((y i : ℂ) + s ^ a * F i s) - ((y i : ℂ) + (0 : ℂ) ^ a * F i 0) = s ^ a * F i s
    rw [zero_pow ha.ne', zero_mul, add_zero]
    ring
  · -- `σ 0 = toC y`
    funext i
    show (y i : ℂ) + (0 : ℂ) ^ a * F i 0 = (y i : ℂ)
    rw [zero_pow ha.ne', zero_mul, add_zero]
  · -- agreement with the complexification of `γ` near `0`
    filter_upwards [hufact, Metric.ball_mem_nhds (0 : ℝ) hρ₀pos] with t hfact ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    funext i
    show (y i : ℂ) + (t : ℂ) ^ a * F i (t : ℂ) = ((γ t) i : ℂ)
    have hFi : F i (t : ℂ) = ((u t i : ℝ) : ℂ) := hFeq i t (lt_of_lt_of_le ht (hρ₀le i))
    have hfacti : γ t i - y i = t ^ a * u t i := by
      have h := congr_fun hfact i
      simpa [Pi.smul_apply, smul_eq_mul, sub_zero] using h
    rw [hFi]
    have hcast : (y i : ℂ) + (t : ℂ) ^ a * ((u t i : ℝ) : ℂ)
        = (((y i) + t ^ a * u t i : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    congr 1
    linarith

/-- **Branches of a level set of a complexified EA polynomial.**

Let `γ` be a real analytic arc with `γ 0 = y`, let `m = ord_0 (eaEval c Φ ∘ γ)` and
`a = ord_0 (γ - y)`.  Then for every `η > 0` and every sufficiently small positive real `ε` the
level set `{z : eaEvalC c Φ z = ε}` has at least `m / a` points within distance `η` of `y`
(viewed as a complex point).

The argument complexifies the arc: `ramifiedComplexification` produces a
holomorphic arc `σ` through `toC y` with `σ s - σ 0 = s ^ a • v s`, `v 0 ≠ 0`, agreeing with `toC ∘ γ`
on the real axis.  The composite `G = eaEvalC c Φ ∘ σ` is holomorphic at `0` with `G 0 = 0` and
`ord_0 G = m` (orders are preserved by complexification, `Arc.ofReal_order` and
`Arc.order_restrict`), so for small `ε ≠ 0` the equation `G = ε` has exactly `m` solutions `s`
in a small disc, all of them tending to `0` as `ε → 0`
(`Frame.exists_card_solutions_simple_tendsto`).  Their images `σ s` are points of the level set
`{eaEvalC c Φ = ε}`, they are `η`-close to `y` for small `ε`, and since `σ` is at most `a`-to-one
near `0` (`Arc.card_le_mul_card_image`, from the fibre bound `Arc.fibre_card_le`) those images are
at least `m / a` in number. -/
theorem branchPointsAtLevel {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ)
    {γ : ℝ → Fin k → ℝ} {m a : ℕ}
    (hγ : AnalyticAt ℝ γ 0) (hγ0 : γ 0 = y) (ha : 0 < a)
    (hne : ¬ (γ =ᶠ[nhds (0 : ℝ)] fun _ => y))
    (hord : analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = m)
    (hram : analyticOrderAt (fun t : ℝ => γ t - y) 0 = a) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ S : Finset (Fin k → ℂ),
        (∀ z ∈ S, Work.WilE3.eaEvalC c Φ z = (ε : ℂ)) ∧
        (∀ z ∈ S, ‖z - (fun i => (y i : ℂ))‖ < η) ∧
        m ≤ a * S.card := by
  intro η hη
  -- If `m = 0` the cardinality bound is vacuous and the empty set works.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exact ⟨1, one_pos, fun ε hε0 hε1 => ⟨∅, by simp, by simp, by simp [hm0]⟩⟩
  -- The complexified ramified arc through `y`.
  obtain ⟨σ, v, hσan, hvan, hv0, hram', hσ0, hagree⟩ :=
    ramifiedComplexification hγ ha hram
  set G : ℂ → ℂ := fun s => Work.WilE3.eaEvalC c Φ (σ s) with hGdef
  have hGan : AnalyticAt ℂ G 0 :=
    (Work.WilE3.API.eaEvalC_fderiv_analytic c Φ (σ 0)).1.comp hσan
  -- `G` is the complexification of `t ↦ eaEval c Φ (γ t)`, hence has order `m` at `0`.
  have hgReal : AnalyticAt ℝ (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 :=
    (Work.WilE3.eaEval_analytic c Φ (γ 0)).comp hγ
  have hGord : analyticOrderAt G 0 = m := by
    rw [← Work.WilE3.Taylor.Arc.order_restrict G hGan]
    rw [analyticOrderAt_congr (f := fun t : ℝ => G (t : ℂ))
      (g := fun t : ℝ => ((WilkiesDesign.E.eaEval c Φ (γ t) : ℝ) : ℂ)) ?_]
    · rw [Work.WilE3.Taylor.Arc.ofReal_order hgReal, hord]
    · filter_upwards [hagree] with t ht
      simp only [hGdef]
      rw [ht, Work.WilE3.Frame.eaEvalC_toC]
  have hG0 : G 0 = 0 := by
    refine apply_eq_zero_of_analyticOrderAt_ne_zero (f := G) (z₀ := (0 : ℂ)) ?_
    rw [hGord]
    exact_mod_cast hmpos.ne'
  -- The one-variable count: `m` simple solutions of `G = ε` near `0`, converging to `0`.
  obtain ⟨r, δ, hr, hδ, hcount, hconv⟩ :=
    Work.WilE3.Frame.exists_card_solutions_simple_tendsto hGan hG0 m hGord
  -- `σ` is at most `a`-to-one near `0`.
  have hvPi : AnalyticAt ℂ v 0 := AnalyticAt.pi hvan
  obtain ⟨δc, hδc, hδcprop⟩ :=
    Work.WilE3.Taylor.Arc.card_le_mul_card_image (k := k) (v := v) ha hvPi hv0 hram'
  -- A radius around `0` on which `σ` stays within `η` of `σ 0 = toC y`.
  have hball_mem : σ ⁻¹' Metric.ball (σ 0) η ∈ 𝓝 (0 : ℂ) :=
    hσan.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (σ 0) hη)
  obtain ⟨η₁, hη₁, hη₁sub⟩ := Metric.mem_nhds_iff.mp hball_mem
  -- The clustering radius is the smaller of the continuity radius and the fibre bound radius.
  set η' : ℝ := min η₁ δc with hη'def
  have hη'pos : 0 < η' := lt_min hη₁ hδc
  have hη'le₁ : η' ≤ η₁ := min_le_left _ _
  have hη'lec : η' ≤ δc := min_le_right _ _
  have hη'ball : ∀ s : ℂ, ‖s‖ < η' → ‖σ s - σ 0‖ < η := by
    intro s hs
    have hs₁ : s ∈ Metric.ball (0 : ℂ) η₁ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le hs hη'le₁
    have h2 : σ s ∈ Metric.ball (σ 0) η := hη₁sub hs₁
    rwa [Metric.mem_ball, dist_eq_norm] at h2
  -- For `ε` small enough every solution of `G = ε` in the disc of radius `r` is `η'`-close to `0`.
  obtain ⟨δ', hδ'pos, hδ'prop⟩ := punctured_eventually_iff (hconv η' hη'pos)
  refine ⟨min δ δ', lt_min hδ hδ'pos, ?_⟩
  intro ε hε0 hεmin
  have hnormε : ‖((ε : ℝ) : ℂ)‖ = ε := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
  have hεc0 : 0 < ‖((ε : ℝ) : ℂ)‖ := by rw [hnormε]; exact hε0
  have hεcδ : ‖((ε : ℝ) : ℂ)‖ < δ := by
    rw [hnormε]; exact lt_of_lt_of_le hεmin (min_le_left _ _)
  have hεcδ' : ‖((ε : ℝ) : ℂ)‖ < δ' := by
    rw [hnormε]; exact lt_of_lt_of_le hεmin (min_le_right _ _)
  obtain ⟨S₀, hS₀card, hS₀prop, hS₀all⟩ := hcount (ε : ℂ) hεc0 hεcδ
  have hS₀r : ∀ s ∈ S₀, ‖s - (0 : ℂ)‖ < r := fun s hs => (hS₀prop s hs).2.1
  have hcluster : ∀ s ∈ S₀, ‖s‖ < η' := fun s hs =>
    by simpa using hδ'prop (ε : ℂ) hεc0 hεcδ' s (hS₀prop s hs).1 (hS₀r s hs)
  have hclusterc : ∀ s ∈ S₀, ‖s‖ < δc := fun s hs =>
    lt_of_lt_of_le (hcluster s hs) hη'lec
  -- The image of the `m` solutions under `σ`.
  refine ⟨S₀.image σ, ?_, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    simpa [hGdef] using (hS₀prop s hs).1
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    have h1 : ‖σ s - σ 0‖ < η := hη'ball s (hcluster s hs)
    rw [hσ0] at h1
    exact h1
  · have hcard : S₀.card ≤ a * (S₀.image σ).card := hδcprop S₀ hclusterc
    rw [← hS₀card]
    exact hcard

end Work.WilE3.Taylor.Grad
