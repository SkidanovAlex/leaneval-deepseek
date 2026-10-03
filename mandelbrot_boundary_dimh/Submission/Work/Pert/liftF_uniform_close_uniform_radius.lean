import Mathlib
import Submission.Work.Pert.tendsto_uniformly_liftF_F0_uniform_r
import Submission.Work.Pert.tendsto_uniformly_liftF_F0
import Submission.Work.Pert.u_close_of_nearOn
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.SmallOfNearOnConst
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# `Work.Pert.liftF_uniform_close_uniform_radius`

The **uniform-radius** form of `Work.Pert.liftF_uniform_close`: the perturbed lift
`F_f = liftF u σ α` of a perturbation `f z = z + z (z - σ) u z` of the parabolic germ `f₀` is
uniformly close to `τ₀ ∘ f₀ ∘ τ₀` on every compact set of `Qreg (some Ξ') none`, and the *only*
requirement on the working radius `ρ` is `ρ ≥ ρ₀`, where `ρ₀` is a constant depending on `f₀`
alone -- uniformly in the compact set `K` and in the tolerance `ε` (which are quantified
*after* `ρ` in the statement of `Work.Pert.PertStatement`'s gate estimates).

The point of the reordering is that the analytic input
`Work.Pert.tendsto_uniformly_liftF_F0_uniform_r` (the `α → 0` limit with the radius hoisted out of
the `∀ K ∀ ε` quantifiers) supplies a radius `r` for which the hypotheses on `u` are needed only on
`ball 0 r`; taking `ρ₀ := r` one may then restrict `ball 0 ρ` to `ball 0 r` whenever `ρ ≥ ρ₀`.

The rest of the argument is region-independent bookkeeping, identical to the proof of
`Work.Pert.liftF_uniform_close`: `Work.Pert.u_close_of_nearOn` converts the `C⁰`-closeness of `f`
to `f₀` into the closeness of `u` to `(f₀ - id)/z²`, and `Work.Pert.SmallOfNearOnConst` bounds
`rotOf f` by a multiple of the `NearOn` tolerance.

Quantifier bookkeeping: `ρ' := min ρ r₀` (with `r₀` the smallness radius of
`SmallOfNearOnConst`) is the working radius on which the `NearOn`-hypothesis is restricted to a
closed ball; the tolerance `δ₀` is `min δ₁ (min (ρ'/4) (ρ' η/20))`, so that both the smallness
estimate `‖rotOf f‖ ≤ 10 δ₀/ρ'` and the two regime estimates of `SmallOfNearOnConst` hold.
-/

namespace Work.Pert

open Complex Metric Filter Set

open scoped Topology

noncomputable section

/-- On `Qreg (some ξ) none` the condition is `-|Im z| < Re z - ξ`. -/
private lemma Qreg_some_none_eq' (ξ : ℝ) :
    MandelDim.Qreg (some (ξ : ℂ)) none = {z : ℂ | -|z.im| < z.re - ξ} := by
  ext z
  simp only [MandelDim.Qreg, Set.mem_ofPred_eq, Option.mem_some_iff, Option.not_mem_none,
    forall_eq']
  constructor
  · intro h; simpa using h.1
  · intro h; exact ⟨by simpa using h, fun b hb => hb.elim⟩

/-- `Qreg (some ·) none` is antitone in the constant. -/
private lemma Qreg_some_none_mono' {a b : ℝ} (h : b ≤ a) :
    MandelDim.Qreg (some (a : ℂ)) none ⊆ MandelDim.Qreg (some (b : ℂ)) none := by
  rw [Qreg_some_none_eq' a, Qreg_some_none_eq' b]
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  linarith

/-- `NearOn` is monotone in the compact set (`L' ⊆ L`) and in the tolerance (`δ ≤ δ'`). -/
private lemma NearOn_mono' {f₀ f : ℂ → ℂ} {Df L L' : Set ℂ} {δ δ' : ℝ} (hL : L' ⊆ L)
    (hδ : δ ≤ δ') (hN : MandelDim.NearOn f₀ f Df L δ) : MandelDim.NearOn f₀ f Df L' δ' := by
  obtain ⟨h1, h2, h3, h4⟩ := hN
  exact ⟨h1, fun z hz => h2 (hL hz), h3, fun z hz => lt_of_lt_of_le (h4 z (hL hz)) hδ⟩

theorem liftF_uniform_close_uniform_radius {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (h₀ : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ Ξ' : ℝ, ξ ≤ Ξ' →
      ∀ K : Set ℂ, IsCompact K → K ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none →
      ∀ ε : ℝ, 0 < ε → ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∀ L : Set ℂ, IsCompact L → L ⊆ D₀ → Metric.closedBall (0 : ℂ) ρ ⊆ L →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 →
        MandelDim.InF1 (MandelDim.rotOf f) → α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ) →
        (∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) ρ, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        ∀ w ∈ K, ‖Work.Pert.liftF u σ α w - MandelDim.tau0 (f₀ (MandelDim.tau0 w))‖ < ε := by
  obtain ⟨ξ, hξpos, ρ₀, hρ₀pos, hlim⟩ := tendsto_uniformly_liftF_F0_uniform_r h₀
  refine ⟨ξ, hξpos, ρ₀, hρ₀pos, ?_⟩
  intro Ξ' hΞ' K hKc hKQ ε hε ρ hρL L hLc hLD0 hballL
  -- the limit theorem, on the smaller region `Qreg (some ξ) none ⊆ Qreg (some Ξ') none`
  obtain ⟨η, hηpos, hkey⟩ :=
    hlim K hKc (fun z hz => Qreg_some_none_mono' hΞ' (hKQ hz)) ε hε
  -- the `C⁰`-closeness of `u` to `(f₀ - id)/z²`, with tolerance `η`
  have hρpos : 0 < ρ := lt_of_lt_of_le hρ₀pos hρL
  obtain ⟨δ₁, hδ₁pos, huc⟩ := u_close_of_nearOn (ρ := ρ) h₀ hρpos hηpos
  -- the smallness data, used at the radius `min ρ r₀`
  obtain ⟨r₀, hr₀pos, _hr₀sub, hsm⟩ := SmallOfNearOnConst h₀
  set ρ' : ℝ := min ρ r₀ with hρ'def
  have hρ'pos : 0 < ρ' := by rw [hρ'def]; exact lt_min hρpos hr₀pos
  have hρ'leρ : ρ' ≤ ρ := by rw [hρ'def]; exact min_le_left _ _
  have hρ'ler₀ : ρ' ≤ r₀ := by rw [hρ'def]; exact min_le_right _ _
  set δ₀ : ℝ := min δ₁ (min (ρ' / 4) (ρ' * η / 20)) with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact lt_min hδ₁pos (lt_min (by positivity) (by positivity))
  have hδ₀le₁ : δ₀ ≤ δ₁ := by rw [hδ₀def]; exact min_le_left _ _
  have hδ₀leρ : δ₀ ≤ ρ' / 4 := by
    rw [hδ₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₀leη : δ₀ ≤ ρ' * η / 20 := by
    rw [hδ₀def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro f Df u σ α hnear hf0 hInF1 hαeq hudiff hubnd hform hnorm w hwK
  -- ## `α ≠ 0`, from `InF1 α`
  have hαne : α ≠ 0 := by
    have h1 : MandelDim.InF1 α := by rw [hαeq]; exact hInF1
    simp only [MandelDim.InF1] at h1
    intro h0
    rw [h0] at h1
    simp at h1
  -- ## the smallness of `rotOf f`, and hence `‖α‖ ≤ η`
  have hnear' : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ') δ₀ :=
    NearOn_mono' (fun z hz => hballL (Metric.closedBall_subset_closedBall hρ'leρ hz)) le_rfl hnear
  have hsm' := hsm (f := f) (Df := Df) (ρ := ρ') (δ₀ := δ₀) (rr := ρ') (u := u) (σ := σ)
    hρ'pos hρ'ler₀ hδ₀pos (by linarith) hρ'pos hnear' hf0
    (hudiff.mono (Metric.ball_subset_ball hρ'leρ))
    (fun z hz => hubnd z (Metric.ball_subset_ball hρ'leρ hz))
    (fun z hz => hform z (Metric.ball_subset_ball hρ'leρ hz))
  have hαη : ‖α‖ ≤ η := by
    rw [hαeq]
    have h1 : 10 * δ₀ / ρ' ≤ η / 2 := by
      rw [div_le_iff₀ hρ'pos]
      nlinarith [hδ₀leη, hηpos, hρ'pos]
    have h2 : ‖MandelDim.rotOf f‖ ≤ 10 * δ₀ / ρ' := hsm'.2.2
    linarith
  -- ## the `C⁰`-closeness of `u`, with the tolerance `η` of the limit theorem
  have hue : ∀ z ∈ Metric.ball (0 : ℂ) ρ, z ≠ 0 →
      ‖u z - (f₀ z - z) / z ^ 2‖ < η :=
    huc f Df L u σ hLc hballL hLD0
      (NearOn_mono' (fun z hz => hz) hδ₀le₁ hnear) hf0 hudiff hubnd hform
  exact hkey hαne hαη hnorm (hudiff.mono (Metric.ball_subset_ball hρL))
    (fun z hz hz0 => hue z (Metric.ball_subset_ball hρL hz) hz0) w hwK

end

end Work.Pert
