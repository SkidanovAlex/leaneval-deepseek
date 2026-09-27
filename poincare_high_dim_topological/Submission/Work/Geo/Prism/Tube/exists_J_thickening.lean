import Mathlib
import Submission.Work.Geo.Prism.Defs
import Submission.Work.PL.Defs

open Set Metric Filter
open scoped Topology

namespace Work.Geo.Prism.Tube

/-- The prism over a nonempty closed `J ⊆ F` lies in the open set `U`; then the prism over a whole neighbourhood of `J` (thickened in the `z` direction and in the `t` direction, uniformly in `z`) is still in `U`.  This is the quantitative input to the `ψ` construction of `prism_push_rel`.  Proof by contradiction along sequences: if no `ρ` works, there are `zₙ → z*` with `infDist zₙ J < 1/n` (so `z* ∈ J`, using `F` compact and `J` closed) and `tₙ ∈ Icc (γ₀ zₙ - 1/n) (γ₁ zₙ + 1/n)` with `(0,zₙ,tₙ) ∉ U`; the `tₙ` are bounded (continuity of `γ₀, γ₁` on the bounded `cthickening 1 J`), so a subsequence converges to `t* ∈ Icc (γ₀ z*) (γ₁ z*)`, giving `(0,z*,t*) ∈ U` by `hJU`, contradicting the openness of `U`.  Do not use a naive "clamp `t` into `[γ₀ z', γ₁ z']` for a nearest `z'`" argument: that interval can be inverted/empty. -/
theorem exists_J_thickening {a b : ℕ} {F J : Set (PL.E b)} (hF : IsCompact F) (hJ : IsClosed J)
    (hJF : J ⊆ F) (hJne : J.Nonempty) {γ₀ γ₁ : PL.E b → ℝ} (h₀ : Continuous γ₀)
    (h₁ : Continuous γ₁) {U : Set (Work.Geo.Prism.Pr a b)} (hU : IsOpen U)
    (hJU : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      ((0 : PL.E a), z, t) ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : PL.E b, Metric.infDist z J < ρ →
      ∀ t ∈ Set.Icc (γ₀ z - ρ) (γ₁ z + ρ), ((0 : PL.E a), z, t) ∈ U := by
  -- The closed thickening of `J` is compact, so `γ₀` and `γ₁` are bounded on it.
  have hScpx : IsCompact (Metric.cthickening (1:ℝ) J) :=
    IsCompact.of_isClosed_subset (hF.cthickening (r := 1)) Metric.isClosed_cthickening
      (Metric.cthickening_subset_of_subset 1 hJF)
  obtain ⟨C₀, hC₀⟩ := hScpx.exists_bound_of_continuousOn h₀.continuousOn
  obtain ⟨C₁, hC₁⟩ := hScpx.exists_bound_of_continuousOn h₁.continuousOn
  set M : ℝ := max C₀ C₁ + 1 with hM
  by_contra hcon
  push Not at hcon
  choose z hz t ht hnotU using fun n : ℕ => hcon (1/((n:ℝ)+1)) (by positivity)
  have hρle1 : ∀ n : ℕ, (1:ℝ)/((n:ℝ)+1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hzS : ∀ n, z n ∈ Metric.cthickening (1:ℝ) J := by
    intro n
    exact Metric.thickening_subset_cthickening 1 J
      ((Metric.mem_thickening_iff_infDist_lt hJne).2 (lt_of_lt_of_le (hz n) (hρle1 n)))
  have htIcc : ∀ n, t n ∈ Set.Icc (-M) M := by
    intro n
    have hb₀ : |γ₀ (z n)| ≤ C₀ := by simpa [Real.norm_eq_abs] using hC₀ (z n) (hzS n)
    have hb₁ : |γ₁ (z n)| ≤ C₁ := by simpa [Real.norm_eq_abs] using hC₁ (z n) (hzS n)
    have hgl : -C₀ ≤ γ₀ (z n) := (abs_le.mp hb₀).1
    have hgu : γ₁ (z n) ≤ C₁ := (abs_le.mp hb₁).2
    have ht' := ht n
    rw [Set.mem_Icc] at ht' ⊢
    refine ⟨?_, ?_⟩
    · have hm : C₀ ≤ max C₀ C₁ := le_max_left _ _
      linarith [ht'.1, hgl, hρle1 n, hm, hM]
    · have hm : C₁ ≤ max C₀ C₁ := le_max_right _ _
      linarith [ht'.2, hgu, hρle1 n, hm, hM]
  have hKcpt : IsCompact (Metric.cthickening (1:ℝ) J ×ˢ Set.Icc (-M) M) :=
    hScpx.prod isCompact_Icc
  obtain ⟨pt, hpt, φ, hφmono, hconv⟩ :=
    hKcpt.tendsto_subseq (fun n => (show (z n, t n) ∈
      Metric.cthickening (1:ℝ) J ×ˢ Set.Icc (-M) M from ⟨hzS n, htIcc n⟩))
  have hzf : Tendsto (fun k => z (φ k)) atTop (𝓝 pt.1) := by
    have h := (continuous_fst.tendsto pt).comp hconv
    simpa [Function.comp_def] using h
  have htf : Tendsto (fun k => t (φ k)) atTop (𝓝 pt.2) := by
    have h := (continuous_snd.tendsto pt).comp hconv
    simpa [Function.comp_def] using h
  have hρk : Tendsto (fun k => (1:ℝ)/((φ k : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono.tendsto_atTop
  have hinf : Metric.infDist pt.1 J = 0 := by
    apply le_antisymm _ Metric.infDist_nonneg
    apply le_of_forall_pos_le_add
    intro ε hε
    have hε2 : 0 < ε/2 := by linarith
    have h1 : ∀ᶠ k in atTop, (1:ℝ)/((φ k : ℝ)+1) < ε/2 :=
      hρk.eventually_lt tendsto_const_nhds hε2
    have h2 : ∀ᶠ k in atTop, dist (z (φ k)) pt.1 < ε/2 := by
      simpa [Metric.mem_ball] using hzf.eventually (Metric.ball_mem_nhds pt.1 hε2)
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    have hle := Metric.infDist_le_infDist_add_dist (s := J) (x := pt.1) (y := z (φ k))
    have hk2' : dist pt.1 (z (φ k)) < ε/2 := by rw [dist_comm]; exact hk2
    have hlt : Metric.infDist (z (φ k)) J < ε/2 := lt_trans (hz (φ k)) hk1
    linarith
  have hzJ : pt.1 ∈ J := by
    have h1 : pt.1 ∈ closure J := (Metric.mem_closure_iff_infDist_zero hJne).2 hinf
    rwa [hJ.closure_eq] at h1
  have htstar : pt.2 ∈ Set.Icc (γ₀ pt.1) (γ₁ pt.1) := by
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · have hγ : Tendsto (fun k => γ₀ (z (φ k))) atTop (𝓝 (γ₀ pt.1)) := by
        have h := (h₀.tendsto pt.1).comp hzf
        simpa [Function.comp_def] using h
      have hf : Tendsto (fun k => γ₀ (z (φ k)) - (1:ℝ)/((φ k : ℝ)+1)) atTop (𝓝 (γ₀ pt.1)) := by
        have h := hγ.sub hρk
        simpa using h
      refine le_of_tendsto_of_tendsto hf htf (Eventually.of_forall fun k => ?_)
      exact (Set.mem_Icc.mp (ht (φ k))).1
    · have hγ : Tendsto (fun k => γ₁ (z (φ k))) atTop (𝓝 (γ₁ pt.1)) := by
        have h := (h₁.tendsto pt.1).comp hzf
        simpa [Function.comp_def] using h
      have hf : Tendsto (fun k => γ₁ (z (φ k)) + (1:ℝ)/((φ k : ℝ)+1)) atTop (𝓝 (γ₁ pt.1)) := by
        have h := hγ.add hρk
        simpa using h
      refine le_of_tendsto_of_tendsto htf hf (Eventually.of_forall fun k => ?_)
      exact (Set.mem_Icc.mp (ht (φ k))).2
  have hmemU : ((0:PL.E a), pt.1, pt.2) ∈ U := hJU pt.1 hzJ pt.2 htstar
  have hcont3 : Tendsto (fun k => ((0:PL.E a), z (φ k), t (φ k))) atTop
      (𝓝 ((0:PL.E a), pt.1, pt.2)) :=
    tendsto_const_nhds.prodMk_nhds hconv
  have hev : ∀ᶠ k in atTop, ((0:PL.E a), z (φ k), t (φ k)) ∈ U :=
    hcont3.eventually (hU.mem_nhds hmemU)
  obtain ⟨k, hk⟩ := hev.exists
  exact (hnotU (φ k)) hk

end Work.Geo.Prism.Tube
