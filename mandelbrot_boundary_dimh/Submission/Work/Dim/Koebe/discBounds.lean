import Mathlib
import Submission.Unif.UnivalentCompactness
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

open Set Metric Filter
open scoped Topology

namespace Work.Dim.Koebe

/-- Extraction step common to the upper and the lower bound: from a sequence of normalised
univalent functions and points in the closed disc of radius `1/2`, extract a strictly monotone
subsequence along which the points converge and the functions converge locally uniformly to a
normalised univalent limit. -/
private lemma extract {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ (F n) z) ∧
      Set.InjOn (F n) (Metric.ball (0 : ℂ) 1) ∧ F n 0 = 0 ∧ deriv (F n) 0 = 1)
    (x : ℕ → ℂ) (hx : ∀ n, ‖x n‖ ≤ 1 / 2) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ) (x₀ : ℂ), StrictMono φ ∧ ‖x₀‖ ≤ 1 / 2 ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g Filter.atTop (Metric.ball (0 : ℂ) 1) ∧
      AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) 1) ∧ Set.InjOn g (Metric.ball (0 : ℂ) 1) ∧
      g 0 = 0 ∧ deriv g 0 = 1 ∧
      Filter.Tendsto (fun n => x (φ n)) Filter.atTop (nhds x₀) := by
  obtain ⟨x₀, hx₀mem, ψ, hψ, hxt⟩ := IsCompact.tendsto_subseq
      (isCompact_closedBall (0 : ℂ) (1 / 2))
      (fun n => by rw [mem_closedBall_zero_iff]; exact hx n)
  obtain ⟨θ, g, hθ, hconv, hgana, hginj, hg0, hg1⟩ :=
      Submission.exists_subseq_tendstoLocallyUniformlyOn_of_injOn_deriv_one
        (f := fun n => F (ψ n))
        (fun n => (hF (ψ n)).1) (fun n => (hF (ψ n)).2.1)
        (fun n => (hF (ψ n)).2.2.1) (fun n => (hF (ψ n)).2.2.2)
  refine ⟨fun n => ψ (θ n), g, x₀, ?_, ?_, ?_, hgana, hginj, hg0, hg1, ?_⟩
  · simpa [Function.comp_def] using hψ.comp hθ
  · rw [mem_closedBall_zero_iff] at hx₀mem; exact hx₀mem
  · simpa using hconv
  · simpa [Function.comp_def] using hxt.comp (StrictMono.tendsto_atTop hθ)

private theorem derivLimit' {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {x : ℕ → ℂ} {x₀ : ℂ}
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F g Filter.atTop U)
    (hx : ∀ n, x n ∈ K) (hxt : Filter.Tendsto x Filter.atTop (nhds x₀)) :
    Filter.Tendsto (fun n => deriv (F n) (x n)) Filter.atTop (nhds (deriv g x₀)) := by
  have hF' : ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ (F n) U := Filter.Eventually.of_forall hF
  have hd : TendstoLocallyUniformlyOn (deriv ∘ F) (deriv g) Filter.atTop U := hconv.deriv hF' hU
  have hUnif : TendstoUniformlyOn (deriv ∘ F) (deriv g) Filter.atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hd K hKU hK
  have hgd : DifferentiableOn ℂ g U := hconv.differentiableOn hF' hU
  have hdgd : DifferentiableOn ℂ (deriv g) U := hgd.deriv hU
  have hx₀K : x₀ ∈ K := hK.isClosed.mem_of_tendsto hxt (Filter.Eventually.of_forall hx)
  have hcontK : ContinuousWithinAt (deriv g) K x₀ :=
    ((hdgd.mono hKU).continuousOn).continuousWithinAt hx₀K
  have hxtK : Filter.Tendsto x Filter.atTop (nhdsWithin x₀ K) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxt, Filter.Eventually.of_forall hx⟩
  exact hUnif.tendsto_comp hcontK hxtK

theorem discBounds :
    ∃ Cup Clow : ℝ, 0 < Cup ∧ 0 < Clow ∧
      ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
        Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
        ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → Clow ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ Cup := by
  classical
  have hUpper : ∃ Cup : ℝ, 0 < Cup ∧ ∀ f : ℂ → ℂ,
      (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖deriv f z‖ ≤ Cup := by
    by_contra hcon
    push_neg at hcon
    choose F hFnu using fun n : ℕ => hcon ((n : ℝ) + 1) (by positivity)
    choose x hx using fun n : ℕ => (hFnu n).2.2.2.2
    obtain ⟨φ, g, x₀, hφ, hx₀, hconv, hgana, hginj, hg0, hg1, hxt⟩ :=
      extract (F := F)
        (fun n => ⟨(hFnu n).1, (hFnu n).2.1, (hFnu n).2.2.1, (hFnu n).2.2.2.1⟩)
        x (fun n => (hx n).1)
    have hFd : ∀ n, DifferentiableOn ℂ (F (φ n)) (Metric.ball (0 : ℂ) 1) :=
      fun n z hz => ((hFnu (φ n)).1 z hz).differentiableWithinAt
    have hxK : ∀ n, x (φ n) ∈ Metric.closedBall (0 : ℂ) (1 / 2) :=
      fun n => by rw [mem_closedBall_zero_iff]; exact (hx (φ n)).1
    have hKU : Metric.closedBall (0 : ℂ) (1 / 2) ⊆ Metric.ball (0 : ℂ) 1 :=
      Metric.closedBall_subset_ball (by norm_num)
    have hlim := derivLimit' (F := fun n => F (φ n)) (x := fun n => x (φ n)) (x₀ := x₀)
      (U := Metric.ball (0 : ℂ) 1) (K := Metric.closedBall (0 : ℂ) (1 / 2))
      Metric.isOpen_ball (isCompact_closedBall 0 (1 / 2)) hKU hFd hconv hxK hxt
    have hnormlim : Filter.Tendsto (fun n => ‖deriv (F (φ n)) (x (φ n))‖) Filter.atTop
        (nhds ‖deriv g x₀‖) := hlim.norm
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hφcast : Filter.Tendsto (fun n : ℕ => ((φ n : ℕ) : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => by
        have : (n : ℝ) ≤ ((φ n : ℕ) : ℝ) := by exact_mod_cast hφ.id_le n
        linarith) hcast
    have hbd : Filter.Tendsto (fun n => ‖deriv (F (φ n)) (x (φ n))‖) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => le_of_lt (hx (φ n)).2) hφcast
    exact not_tendsto_atTop_of_tendsto_nhds hnormlim hbd
  have hLower : ∃ Clow : ℝ, 0 < Clow ∧ ∀ f : ℂ → ℂ,
      (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → Clow ≤ ‖deriv f z‖ := by
    by_contra hcon
    push_neg at hcon
    choose F hFnu using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
    choose x hx using fun n : ℕ => (hFnu n).2.2.2.2
    obtain ⟨φ, g, x₀, hφ, hx₀, hconv, hgana, hginj, hg0, hg1, hxt⟩ :=
      extract (F := F)
        (fun n => ⟨(hFnu n).1, (hFnu n).2.1, (hFnu n).2.2.1, (hFnu n).2.2.2.1⟩)
        x (fun n => (hx n).1)
    have hFd : ∀ n, DifferentiableOn ℂ (F (φ n)) (Metric.ball (0 : ℂ) 1) :=
      fun n z hz => ((hFnu (φ n)).1 z hz).differentiableWithinAt
    have hxK : ∀ n, x (φ n) ∈ Metric.closedBall (0 : ℂ) (1 / 2) :=
      fun n => by rw [mem_closedBall_zero_iff]; exact (hx (φ n)).1
    have hKU : Metric.closedBall (0 : ℂ) (1 / 2) ⊆ Metric.ball (0 : ℂ) 1 :=
      Metric.closedBall_subset_ball (by norm_num)
    have hlim := derivLimit' (F := fun n => F (φ n)) (x := fun n => x (φ n)) (x₀ := x₀)
      (U := Metric.ball (0 : ℂ) 1) (K := Metric.closedBall (0 : ℂ) (1 / 2))
      Metric.isOpen_ball (isCompact_closedBall 0 (1 / 2)) hKU hFd hconv hxK hxt
    have hnormlim : Filter.Tendsto (fun n => ‖deriv (F (φ n)) (x (φ n))‖) Filter.atTop
        (nhds ‖deriv g x₀‖) := hlim.norm
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hdiv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hcast
    have h2 : ∀ n, ‖deriv (F (φ n)) (x (φ n))‖ < 1 / ((n : ℝ) + 1) := by
      intro n
      refine lt_of_lt_of_le (hx (φ n)).2 ?_
      apply one_div_le_one_div_of_le
      · positivity
      · have : (n : ℝ) ≤ ((φ n : ℕ) : ℝ) := by exact_mod_cast hφ.id_le n
        linarith
    have hlim0 : Filter.Tendsto (fun n => ‖deriv (F (φ n)) (x (φ n))‖) Filter.atTop
        (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
        (fun n => norm_nonneg _) (fun n => le_of_lt (h2 n))
    have hzero : ‖deriv g x₀‖ = 0 := tendsto_nhds_unique hnormlim hlim0
    have hzg : deriv g x₀ = 0 := norm_eq_zero.mp hzero
    have hx₀ball : x₀ ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hsub : Metric.ball x₀ (1 - ‖x₀‖) ⊆ Metric.ball (0 : ℂ) 1 := by
      intro w hw
      rw [Metric.mem_ball] at hw ⊢
      have hw' : ‖w - x₀‖ < 1 - ‖x₀‖ := by simpa [dist_eq_norm] using hw
      have h1 : ‖w‖ < 1 := by
        calc ‖w‖ = ‖(w - x₀) + x₀‖ := by ring_nf
          _ ≤ ‖w - x₀‖ + ‖x₀‖ := norm_add_le _ _
          _ < (1 - ‖x₀‖) + ‖x₀‖ := by linarith
          _ = 1 := by ring
      simpa [dist_eq_norm] using h1
    have hne : deriv g x₀ ≠ 0 := by
      refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
        (c := x₀) (r := 1 - ‖x₀‖) (by linarith) (hgana x₀ hx₀ball) ?_
      exact fun a ha b hb hab => hginj (hsub ha) (hsub hb) hab
    exact hne hzg
  obtain ⟨Cup, hCuppos, hCup⟩ := hUpper
  obtain ⟨Clow, hClowpos, hClow⟩ := hLower
  exact ⟨Cup, Clow, hCuppos, hClowpos,
    fun f hf hinj h0 h1 z hz => ⟨hClow f hf hinj h0 h1 z hz, hCup f hf hinj h0 h1 z hz⟩⟩

end Work.Dim.Koebe
