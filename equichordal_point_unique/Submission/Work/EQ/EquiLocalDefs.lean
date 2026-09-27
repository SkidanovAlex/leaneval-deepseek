import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_structure

/-! # Support definitions for the local normal form of `ψ₁`

This file collects the vocabulary used by `Work.EQ.cycle_local_normal_form` and by the lemmas
that are delegated for it:

* `LocalInj` — clause 1 of `H0_structure`: `ψ₁` is locally injective on `H0`;
* `IsSection` — clause 2 of `H0_structure`: an analytic local section of `ψ₁` through a point;
* `IsChartData` — the geometric content of `IsPuncturedChart` (a punctured disc parametrising an
  unramified/unbranched leg of the spread, without the meromorphy clauses);
* `legFibre` — the set of points of a leg over the value `u`.

The basic consequences (`LocalInj` and `HasSection` from `H0_structure`, continuity of a section
into `ChainData`, sections stay in the component) are proved here. -/

namespace Work.EQ

open Filter _root_.Topology

/-! ## Local injectivity of `ψ₁` -/

/-- **Local injectivity of `ψ₁` on `H0`**: through every point of `H0`, `ψ₁` is injective on a
neighbourhood intersected with `H0`.  This is clause 1 of `H0_structure`. -/
def LocalInj (a : ℝ) (h : ℂ → ℂ) : Prop :=
  ∀ q ∈ H0 a h, ∃ U : Set ChainData, IsOpen U ∧ q ∈ U ∧
    ∀ q₁ ∈ U, q₁ ∈ H0 a h → ∀ q₂ ∈ U, q₂ ∈ H0 a h → q₁.2.1 = q₂.2.1 → q₁ = q₂

lemma localInj_of_localHomeomorph {a : ℝ} {h : ℂ → ℂ}
    (hφ : IsLocalHomeomorph (fun q : H0 a h => (q : ChainData).2.1)) : LocalInj a h := by
  intro q hq
  obtain ⟨e, hmem, heq⟩ := hφ ⟨q, hq⟩
  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.mp e.open_source
  refine ⟨U, hUo, ?_, ?_⟩
  · have : (⟨q, hq⟩ : H0 a h) ∈ Subtype.val ⁻¹' U := by rw [hU]; exact hmem
    exact this
  · intro q₁ h₁U h₁H q₂ h₂U h₂H hψ
    have hm₁ : (⟨q₁, h₁H⟩ : H0 a h) ∈ e.source := by rw [← hU]; exact h₁U
    have hm₂ : (⟨q₂, h₂H⟩ : H0 a h) ∈ e.source := by rw [← hU]; exact h₂U
    have h1 : e ⟨q₁, h₁H⟩ = q₁.2.1 := (congrFun heq ⟨q₁, h₁H⟩).symm
    have h2 : e ⟨q₂, h₂H⟩ = q₂.2.1 := (congrFun heq ⟨q₂, h₂H⟩).symm
    have : (⟨q₁, h₁H⟩ : H0 a h) = ⟨q₂, h₂H⟩ := e.injOn hm₁ hm₂ (by rw [h1, h2]; exact hψ)
    exact Subtype.ext_iff.mp this

/-! ## Local analytic sections -/

/-- **A local analytic section of `ψ₁` through `q` of radius `ρ`.** -/
def IsSection (a : ℝ) (h : ℂ → ℂ) (f : ℂ → ChainData) (q : ChainData) (ρ : ℝ) : Prop :=
  0 < ρ ∧ f q.2.1 = q ∧ (∀ u ∈ Metric.ball q.2.1 ρ, f u ∈ H0 a h ∧ (f u).2.1 = u) ∧
  (∀ n : ℤ, AnalyticOnNhd ℂ (fun u => (f u).1 n) (Metric.ball q.2.1 ρ)) ∧
  AnalyticOnNhd ℂ (fun u => (f u).2.2) (Metric.ball q.2.1 ρ)

/-- **Local sections exist** (clause 2 of `H0_structure`). -/
theorem hasSection_of_structure {a : ℝ} {h : ℂ → ℂ}
    (hsect : ∀ p ∈ H0 a h, ∃ ρ : ℝ, 0 < ρ ∧ ∃ f : ℂ → ChainData, f p.2.1 = p ∧
      (∀ u ∈ Metric.ball p.2.1 ρ, f u ∈ H0 a h ∧ (f u).2.1 = u) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (fun u => (f u).1 n) (Metric.ball p.2.1 ρ)) ∧
      AnalyticOnNhd ℂ (fun u => (f u).2.2) (Metric.ball p.2.1 ρ) ∧
      f '' Metric.ball p.2.1 ρ ∈ 𝓝[H0 a h] p)
    (q : ChainData) (hq : q ∈ H0 a h) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ f : ℂ → ChainData, IsSection a h f q ρ := by
  obtain ⟨ρ, hρ, f, hf0, hfmem, hfan, hfan2, -⟩ := hsect q hq
  exact ⟨ρ, hρ, f, hρ, hf0, hfmem, hfan, hfan2⟩

/-- A section is continuous as a map into `ChainData`. -/
lemma IsSection.continuousOn {a : ℝ} {h : ℂ → ℂ} {f : ℂ → ChainData} {q : ChainData} {ρ : ℝ}
    (hf : IsSection a h f q ρ) : ContinuousOn f (Metric.ball q.2.1 ρ) := by
  obtain ⟨hρ, hf0, hfmem, hfan, hfan2⟩ := hf
  have h1 : ContinuousOn (fun u => (f u).1) (Metric.ball q.2.1 ρ) :=
    continuousOn_pi.mpr (fun n => (hfan n).continuousOn)
  have h2 : ContinuousOn (fun u => (f u).2.1) (Metric.ball q.2.1 ρ) :=
    continuousOn_id.congr (fun u hu => (hfmem u hu).2)
  exact h1.prodMk (h2.prodMk hfan2.continuousOn)

/-- A section through a point of `H0` is continuous at its centre. -/
lemma IsSection.continuousAt {a : ℝ} {h : ℂ → ℂ} {f : ℂ → ChainData} {q : ChainData} {ρ : ℝ}
    (hf : IsSection a h f q ρ) : ContinuousAt f q.2.1 :=
  hf.continuousOn.continuousAt (Metric.ball_mem_nhds _ hf.1)

/-- The image of a section over a ball lies in the connected component of `q` in `H0`. -/
lemma IsSection.image_subset_connectedComponentIn {a : ℝ} {h : ℂ → ℂ} {f : ℂ → ChainData}
    {q : ChainData} {ρ : ℝ} (hf : IsSection a h f q ρ) (hq : q ∈ H0 a h) :
    f '' Metric.ball q.2.1 ρ ⊆ connectedComponentIn (H0 a h) q := by
  have hpre : IsPreconnected (f '' Metric.ball q.2.1 ρ) :=
    Metric.isPreconnected_ball.image f (hf.continuousOn.mono (fun x hx => hx))
  obtain ⟨hρ, hf0, hfmem, hfan, hfan2⟩ := hf
  have hqmem : q ∈ f '' Metric.ball q.2.1 ρ :=
    ⟨q.2.1, by rw [Metric.mem_ball, dist_self]; exact hρ, hf0⟩
  refine hpre.subset_connectedComponentIn hqmem ?_
  rintro y ⟨u, hu, rfl⟩
  exact (hfmem u hu).1

/-! ## Legs of the spread: chart data and their fibres -/

/-- **Chart data**: `E` parametrises a punctured disc of `H0` over the `ψ₁`-values
`w + κ ζ^k`, injectively and continuously.  This is the geometric part of `IsPuncturedChart`. -/
def IsChartData (a : ℝ) (h : ℂ → ℂ) (E : ℂ → ChainData) (w κ : ℂ) (k : ℕ) : Prop :=
  0 < k ∧ κ ≠ 0 ∧
  (∀ ζ ∈ Metric.ball (0 : ℂ) 1 \ {0}, E ζ ∈ H0 a h ∧ (E ζ).2.1 = w + κ * ζ ^ k) ∧
  Set.InjOn E (Metric.ball (0 : ℂ) 1 \ {0}) ∧ ContinuousOn E (Metric.ball (0 : ℂ) 1 \ {0})

/-- The points of a leg `E` (with `ψ₁ ∘ E = u₁ + κ ζ^k`) over the value `u`. -/
def legFibre (E : ℂ → ChainData) (u₁ u κ : ℂ) (k : ℕ) : Set ChainData :=
  E '' {ζ : ℂ | ζ ≠ 0 ∧ u₁ + κ * ζ ^ k = u}

lemma legFibre_subset_range (E : ℂ → ChainData) (u₁ u κ : ℂ) (k : ℕ) :
    legFibre E u₁ u κ k ⊆ Set.range E := Set.image_subset_range _ _

end Work.EQ
