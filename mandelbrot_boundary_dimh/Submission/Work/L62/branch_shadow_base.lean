import Mathlib
import Submission.Work.L62.local_branch_disc
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn
import Submission.Work.L62.exists_unique_eq_of_lipschitz_close
import Submission.Work.L62.lipschitz_and_injOn_of_deriv_close

/-!
# `branch_shadow_base`: shadowing of an inverse branch over an arbitrary base

This is `Submission.Work.L62.branch_shadow` with `ball c r` replaced by a general open set `Ω` and
the disc `ball c ρ` by a general base `B`: the contraction argument is applied on the convex discs
`Metric.closedBall z R₀`, `z ∈ B`, rather than globally on a ball.

Two auxiliary facts are proved first:

* `differentiableAt_and_deriv_of_comp_eq_id`: if `F ∘ ψ = id` near `w` and `deriv ψ w ≠ 0`, then
  `F` is differentiable at `ψ w` and `deriv F (ψ w) * deriv ψ w = 1`.  This is what makes
  `w ↦ F' (ψ w)` differentiable at every point of the collars even though `F'` is only assumed
  holomorphic on `Ω`: the hypothesis `hcloseD`, combined with `deriv F (ψ w) = (deriv ψ w)⁻¹`
  (which holds because a holomorphic injective map has nowhere vanishing derivative,
  `Work.Parab.inversion.deriv_ne_zero_of_injOn`), forces `deriv F' (ψ w) ≠ 0`;
* `exists_branch_abstract`: the purely metric part — a map `S` which is `δ`-close to the identity
  and has `‖deriv S w - 1‖ ≤ k < 1` on each disc `closedBall z R₀` (`z ∈ B`) attains each value
  `z ∈ B` at a unique point of that disc, and the resulting map can be glued over `B` into a
  function which is differentiable at every point of `B` (the local inverse function theorem
  provides the germs; they are compatible because `S` is injective on each disc).
-/

namespace Work.L62

open Set Metric Filter
open scoped Topology

noncomputable section

set_option linter.unusedVariables false

/-- **`F` is differentiable at `ψ w` and the chain rule holds whenever `F ∘ ψ = id` near `w`.**
If `ψ` is holomorphic on the open set `Ω`, `F (ψ z) = z` for `z ∈ Ω`, `w ∈ Ω` and `deriv ψ w ≠ 0`,
then `F` is differentiable at `ψ w` (with `deriv F (ψ w)` the reciprocal of `deriv ψ w`). -/
theorem differentiableAt_and_deriv_of_comp_eq_id {F ψ : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hψd : DifferentiableOn ℂ ψ Ω) (hψinv : ∀ z ∈ Ω, F (ψ z) = z)
    {w : ℂ} (hw : w ∈ Ω) (hderiv : deriv ψ w ≠ 0) :
    DifferentiableAt ℂ F (ψ w) ∧ deriv F (ψ w) * deriv ψ w = 1 := by
  have hψa : AnalyticAt ℂ ψ w := hψd.analyticAt (hΩ.mem_nhds hw)
  obtain ⟨r, hr, ψ', hψ'd, hψ'w, hψ'sec, hψ'mem, _⟩ :=
    local_branch_disc hψa hderiv hΩ hw
  have hev : F =ᶠ[𝓝 (ψ w)] ψ' := by
    filter_upwards [Metric.ball_mem_nhds (ψ w) hr] with z hz
    calc F z = F (ψ (ψ' z)) := by rw [hψ'sec z hz]
      _ = ψ' z := hψinv (ψ' z) (hψ'mem hz)
  have hFd : DifferentiableAt ℂ F (ψ w) :=
    (hψ'd.differentiableAt (Metric.ball_mem_nhds (ψ w) hr)).congr_of_eventuallyEq hev
  refine ⟨hFd, ?_⟩
  have hψat : DifferentiableAt ℂ ψ w := hψd.differentiableAt (hΩ.mem_nhds hw)
  have hcomp : deriv (F ∘ ψ) w = deriv F (ψ w) * deriv ψ w := deriv_comp w hFd hψat
  have hone : deriv (F ∘ ψ) w = 1 := by
    have h1 : HasDerivAt (F ∘ ψ) 1 w :=
      (hasDerivAt_id w).congr_of_eventuallyEq (by
        filter_upwards [hΩ.mem_nhds hw] with z hz
        exact hψinv z hz)
    exact h1.deriv
  rw [← hcomp, hone]

/-- **Abstract shadowing.**  If `S : ℂ → ℂ` is differentiable on each closed disc `closedBall z R₀`
(`z ∈ B`), is `δ`-close to the identity there (`‖S w - w‖ ≤ δ`) and has `‖deriv S w - 1‖ ≤ k` with
`k < 1`, and `δ ≤ (1 - k) R₀` with `δ < R₀`, then there is a function `W : ℂ → ℂ` which, in each
disc `closedBall z R₀` (`z ∈ B`), takes the unique value at which `S` equals `z`, is `δ`-close to
`z`, and which is (complex) differentiable at every point of `B`. -/
theorem exists_branch_abstract {S : ℂ → ℂ} {B : Set ℂ} {R₀ k δ : ℝ}
    (hR₀ : 0 < R₀) (hk0 : 0 ≤ k) (hk1 : k < 1) (hδ : 0 ≤ δ) (hδR₀ : δ ≤ (1 - k) * R₀)
    (hδlt : δ < R₀)
    (hSdiff : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, DifferentiableAt ℂ S w)
    (hSval : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, ‖S w - w‖ ≤ δ)
    (hSderiv : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, ‖deriv S w - 1‖ ≤ k) :
    ∃ W : ℂ → ℂ, (∀ z ∈ B, W z ∈ Metric.closedBall z R₀ ∧ S (W z) = z ∧ ‖W z - z‖ ≤ δ) ∧
      (∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, S w = z → w = W z) ∧
      (∀ z ∈ B, DifferentiableAt ℂ W z) := by
  classical
  -- ### 1. Lipschitz and injectivity of `S` on every disc
  have hP3 : ∀ z ∈ B, (∀ a ∈ Metric.closedBall z R₀, ∀ b ∈ Metric.closedBall z R₀,
        ‖(S a - a) - (S b - b)‖ ≤ k * ‖a - b‖) ∧ Set.InjOn S (Metric.closedBall z R₀) :=
    fun z hz => lipschitz_and_injOn_of_deriv_close hk0 hk1 (hSdiff z hz) (hSderiv z hz)
  -- ### 2. the value `z` is attained in each disc, uniquely
  have hex : ∀ z ∈ B, ∃ w ∈ Metric.closedBall z R₀, S w = z ∧ ‖w - z‖ ≤ δ ∧
      ∀ w' ∈ Metric.closedBall z R₀, S w' = z → w' = w :=
    fun z hz => exists_unique_eq_of_lipschitz_close hR₀ hk0 hk1 hδ hδR₀ (hSval z hz) (hP3 z hz).1
  -- ### 3. that value as a function
  let p : ℂ → ℂ := fun z => if h : z ∈ B then (hex z h).choose else 0
  have hp_spec : ∀ z (hz : z ∈ B), p z ∈ Metric.closedBall z R₀ ∧ S (p z) = z ∧ ‖p z - z‖ ≤ δ ∧
      ∀ w' ∈ Metric.closedBall z R₀, S w' = z → w' = p z := by
    intro z hz
    have hred : p z = (hex z hz).choose := by simp only [p]; exact dite_eq_left hz
    rw [hred]
    exact (hex z hz).choose_spec
  have hp_mem : ∀ z ∈ B, p z ∈ Metric.closedBall z R₀ := fun z hz => (hp_spec z hz).1
  have hp_eq : ∀ z ∈ B, S (p z) = z := fun z hz => (hp_spec z hz).2.1
  have hp_close : ∀ z ∈ B, ‖p z - z‖ ≤ δ := fun z hz => (hp_spec z hz).2.2.1
  have hp_uniq : ∀ z ∈ B, ∀ w' ∈ Metric.closedBall z R₀, S w' = z → w' = p z :=
    fun z hz => (hp_spec z hz).2.2.2
  -- ### 4. local models: near every `b ∈ B`, `p` is a holomorphic local inverse of `S`
  have hmodel : ∀ b : ℂ, ∃ (r : ℝ) (G : ℂ → ℂ), b ∈ B →
      (0 < r ∧ r ≤ (R₀ - δ) / 8 ∧
        DifferentiableOn ℂ G (Metric.ball b r) ∧ G b = p b ∧
        (∀ z ∈ Metric.ball b r, S (G z) = z) ∧
        (∀ z ∈ Metric.ball b r, ‖G z - p b‖ ≤ (R₀ - δ) / 4) ∧
        (∀ z ∈ B ∩ Metric.ball b r, G z = p z)) := by
    intro b
    by_cases hb : b ∈ B
    · have hpb_lt : ‖p b - b‖ < R₀ := lt_of_le_of_lt (hp_close b hb) hδlt
      have hε : 0 < R₀ - ‖p b - b‖ := sub_pos.mpr hpb_lt
      have hSb_ana : AnalyticAt ℂ S (p b) := by
        refine DifferentiableOn.analyticAt (s := Metric.ball (p b) (R₀ - ‖p b - b‖)) ?_
          (Metric.ball_mem_nhds _ hε)
        intro w hw
        have hwb : ‖w - b‖ < R₀ := by
          rw [Metric.mem_ball, dist_eq_norm] at hw
          calc ‖w - b‖ = ‖(w - p b) + (p b - b)‖ := by ring_nf
            _ ≤ ‖w - p b‖ + ‖p b - b‖ := norm_add_le _ _
            _ < R₀ := by linarith
        exact (hSdiff b hb w
          (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hwb.le))).differentiableWithinAt
      have hSderiv_ne : deriv S (p b) ≠ 0 := by
        intro h0
        have h1 := hSderiv b hb (p b) (hp_mem b hb)
        rw [h0, zero_sub, norm_neg, norm_one] at h1
        linarith
      obtain ⟨r, hr, G, hGd, hGb, hGsec, _hGmem, _hGinj⟩ :=
        local_branch_disc hSb_ana hSderiv_ne (Metric.isOpen_ball) (Metric.mem_ball_self hε)
      rw [hp_eq b hb] at hGd hGb hGsec
      have hη : 0 < (R₀ - δ) / 4 := by linarith
      have hGc : ContinuousAt G b := (hGd.differentiableAt (Metric.ball_mem_nhds b hr)).continuousAt
      have hball : Metric.ball (p b) ((R₀ - δ) / 4) ∈ 𝓝 (G b) := by
        rw [hGb]; exact Metric.ball_mem_nhds (p b) hη
      have hpre : G ⁻¹' Metric.ball (p b) ((R₀ - δ) / 4) ∈ 𝓝 b := hGc.preimage_mem_nhds hball
      obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhds_iff.mp hpre
      have hbound : ∀ z ∈ Metric.ball b r₁, ‖G z - p b‖ < (R₀ - δ) / 4 := by
        intro z hz
        have h1 : G z ∈ Metric.ball (p b) ((R₀ - δ) / 4) := hr₁sub hz
        rwa [Metric.mem_ball, dist_eq_norm] at h1
      have hsub₁ : Metric.ball b (min r (min r₁ ((R₀ - δ) / 8))) ⊆ Metric.ball b r :=
        Metric.ball_subset_ball (min_le_left _ _)
      have hsub₁' : Metric.ball b (min r (min r₁ ((R₀ - δ) / 8))) ⊆ Metric.ball b r₁ :=
        Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _))
      refine ⟨min r (min r₁ ((R₀ - δ) / 8)), G, fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · exact lt_min hr (lt_min hr₁ (by linarith))
      · exact le_trans (min_le_right _ _) (min_le_right _ _)
      · exact hGd.mono hsub₁
      · exact hGb
      · intro z hz
        exact hGsec z (hsub₁ hz)
      · intro z hz
        exact (hbound z (hsub₁' hz)).le
      · intro z hz
        obtain ⟨hzb, hzball⟩ := hz
        have hzr : z ∈ Metric.ball b r := hsub₁ hzball
        have h1 : ‖G z - p b‖ ≤ (R₀ - δ) / 4 := (hbound z (hsub₁' hzball)).le
        have h2 : ‖z - b‖ < (R₀ - δ) / 8 := by
          have h3 : dist z b < min r (min r₁ ((R₀ - δ) / 8)) := hzball
          rw [dist_eq_norm] at h3
          exact lt_of_lt_of_le h3 (le_trans (min_le_right _ _) (min_le_right _ _))
        have hmem : G z ∈ Metric.closedBall z R₀ := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have h4 : ‖G z - z‖ ≤ ‖G z - p b‖ + ‖p b - b‖ + ‖b - z‖ := by
            have h9 : G z - z = (G z - p b) + (p b - b) + (b - z) := by ring
            rw [h9]
            exact norm_add_le_of_le (norm_add_le _ _) le_rfl
          have h6 : ‖p b - b‖ ≤ δ := hp_close b hb
          have h7 : ‖b - z‖ = ‖z - b‖ := norm_sub_rev _ _
          linarith
        exact hp_uniq z hzb (G z) hmem (hGsec z hzr)
    · exact ⟨0, 0, fun hb' => absurd hb' hb⟩
  -- ### 5. choose the local models globally
  choose r G hspec using hmodel
  have hrpos : ∀ b ∈ B, 0 < r b := fun b hb => (hspec b hb).1
  have hrle : ∀ b ∈ B, r b ≤ (R₀ - δ) / 8 := fun b hb => (hspec b hb).2.1
  have hGdiff : ∀ b ∈ B, DifferentiableOn ℂ (G b) (Metric.ball b (r b)) :=
    fun b hb => (hspec b hb).2.2.1
  have hGb' : ∀ b ∈ B, G b b = p b := fun b hb => (hspec b hb).2.2.2.1
  have hGsec' : ∀ b ∈ B, ∀ z ∈ Metric.ball b (r b), S (G b z) = z :=
    fun b hb => (hspec b hb).2.2.2.2.1
  have hGbound' : ∀ b ∈ B, ∀ z ∈ Metric.ball b (r b), ‖G b z - p b‖ ≤ (R₀ - δ) / 4 :=
    fun b hb => (hspec b hb).2.2.2.2.2.1
  have hGagree' : ∀ b ∈ B, ∀ z ∈ B ∩ Metric.ball b (r b), G b z = p z :=
    fun b hb => (hspec b hb).2.2.2.2.2.2
  -- ### 6. glue them into a global function
  let W : ℂ → ℂ := fun z =>
    if h : ∃ b, b ∈ B ∧ z ∈ Metric.ball b (r b) then G (Classical.choose h) z else 0
  have hW_apply : ∀ z (h : ∃ b, b ∈ B ∧ z ∈ Metric.ball b (r b)),
      W z = G (Classical.choose h) z := by
    intro z h
    simp only [W]
    exact dite_eq_left h
  -- `W` agrees with `p` on `B`
  have hWval : ∀ z ∈ B, W z = p z := by
    intro z hz
    have hzmem : z ∈ Metric.ball z (r z) := Metric.mem_ball_self (hrpos z hz)
    have hexists : ∃ b, b ∈ B ∧ z ∈ Metric.ball b (r b) := ⟨z, hz, hzmem⟩
    rw [hW_apply z hexists]
    exact hGagree' (Classical.choose hexists) (Classical.choose_spec hexists).1 z
      ⟨hz, (Classical.choose_spec hexists).2⟩
  -- `W` agrees with the local model `G z₀` near each `z₀ ∈ B`
  have hev : ∀ z₀ ∈ B, W =ᶠ[𝓝 z₀] (G z₀) := by
    intro z₀ hz₀
    refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds z₀ (hrpos z₀ hz₀)) ?_
    intro z hz
    have hexists : ∃ b, b ∈ B ∧ z ∈ Metric.ball b (r b) := ⟨z₀, hz₀, hz⟩
    obtain ⟨hb', hz'⟩ := Classical.choose_spec hexists
    rw [hW_apply z hexists]
    have hmem₁ : G (Classical.choose hexists) z ∈ Metric.closedBall z₀ R₀ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h5 : ‖G (Classical.choose hexists) z - p (Classical.choose hexists)‖ ≤ (R₀ - δ) / 4 :=
        hGbound' (Classical.choose hexists) hb' z hz'
      have h6 : ‖p (Classical.choose hexists) - Classical.choose hexists‖ ≤ δ :=
        hp_close (Classical.choose hexists) hb'
      have h7 : ‖z - Classical.choose hexists‖ < (R₀ - δ) / 8 := by
        have h3 : dist z (Classical.choose hexists) < r (Classical.choose hexists) := hz'
        rw [dist_eq_norm] at h3
        exact lt_of_lt_of_le h3 (hrle (Classical.choose hexists) hb')
      have h8 : ‖z - z₀‖ < (R₀ - δ) / 8 := by
        have h3 : dist z z₀ < r z₀ := hz
        rw [dist_eq_norm] at h3
        exact lt_of_lt_of_le h3 (hrle z₀ hz₀)
      have h4 : ‖G (Classical.choose hexists) z - z₀‖
          ≤ ‖G (Classical.choose hexists) z - p (Classical.choose hexists)‖
            + ‖p (Classical.choose hexists) - Classical.choose hexists‖
            + ‖Classical.choose hexists - z‖ + ‖z - z₀‖ := by
        have h9 : G (Classical.choose hexists) z - z₀
            = (G (Classical.choose hexists) z - p (Classical.choose hexists))
              + (p (Classical.choose hexists) - Classical.choose hexists)
              + (Classical.choose hexists - z) + (z - z₀) := by ring
        rw [h9]
        exact norm_add_le_of_le (norm_add_le_of_le (norm_add_le _ _) le_rfl) le_rfl
      have h7' : ‖Classical.choose hexists - z‖ = ‖z - Classical.choose hexists‖ :=
        norm_sub_rev _ _
      linarith
    have hmem₂ : G z₀ z ∈ Metric.closedBall z₀ R₀ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h5 : ‖G z₀ z - p z₀‖ ≤ (R₀ - δ) / 4 := hGbound' z₀ hz₀ z hz
      have h6 : ‖p z₀ - z₀‖ ≤ δ := hp_close z₀ hz₀
      have h4 : ‖G z₀ z - z₀‖ ≤ ‖G z₀ z - p z₀‖ + ‖p z₀ - z₀‖ := by
        have h9 : G z₀ z - z₀ = (G z₀ z - p z₀) + (p z₀ - z₀) := by ring
        rw [h9]
        exact norm_add_le _ _
      linarith
    exact (hP3 z₀ hz₀).2 hmem₁ hmem₂ (by
      rw [hGsec' (Classical.choose hexists) hb' z hz', hGsec' z₀ hz₀ z hz])
  refine ⟨W, ?_, ?_, ?_⟩
  · intro z hz
    rw [hWval z hz]
    exact ⟨hp_mem z hz, hp_eq z hz, hp_close z hz⟩
  · intro z hz w' hw' heq
    rw [hWval z hz]
    exact hp_uniq z hz w' hw' heq
  · intro z₀ hz₀
    exact ((hGdiff z₀ hz₀).differentiableAt
      (Metric.ball_mem_nhds z₀ (hrpos z₀ hz₀))).congr_of_eventuallyEq (hev z₀ hz₀)

/-- **Shadowing of an inverse branch over an arbitrary base (base-general `branch_shadow`).**  Let `Ω` be open, `F, F', ψ` holomorphic on `Ω` with `F (ψ z) = z` on `Ω`, and let `B ⊆ ℂ` be a base whose `R₀`-neighbourhood lies in `Ω`.  If on the `R₀`-neighbourhood of `B` we have `‖deriv ψ‖ ≤ L`, `‖F' - F‖ ≤ δ` and `‖deriv F' - deriv F‖ ≤ δ'` (all evaluated at `ψ`-images), with `δ' * L < 1` and `δ ≤ (1 - δ' * L) * R₀`, then over `B` there is an inverse branch `χ` of `F'`, holomorphic, taking its values in the `ψ`-image of the `R₀`-neighbourhood of `B`, with the *strong* fixed-point form `χ z = ψ w` where `w` is within `δ` of `z`, and with the uniqueness property that any `ψ w` with `F' (ψ w) = z` and `w` in the `R₀`-ball of `z` equals `χ z`.  This is `Submission.Work.L62.branch_shadow` with `ball c r` replaced by a general open `Ω` and `ball c ρ` by a general base `B` (the contraction argument is applied on the convex balls `closedBall z R₀`, `z ∈ B`, rather than globally on the ball). -/
theorem branch_shadow_base {F F' ψ : ℂ → ℂ} {Ω B : Set ℂ} {R₀ L δ δ' : ℝ}
    (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω) (hF' : DifferentiableOn ℂ F' Ω)
    (hψd : DifferentiableOn ℂ ψ Ω) (hψinv : ∀ z ∈ Ω, F (ψ z) = z)
    (hR₀ : 0 < R₀) (hδ : 0 < δ) (hδ' : 0 < δ') (hL : 0 ≤ L) (hδL : δ' * L < 1)
    (hcollar : ∀ z ∈ B, Metric.closedBall z R₀ ⊆ Ω)
    (hLb : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, ‖deriv ψ w‖ ≤ L)
    (hclose : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, ‖F' (ψ w) - F (ψ w)‖ ≤ δ)
    (hcloseD : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, ‖deriv F' (ψ w) - deriv F (ψ w)‖ ≤ δ')
    (hδR₀ : δ ≤ (1 - δ' * L) * R₀) :
    ∃ χ : ℂ → ℂ, (∀ z ∈ B, F' (χ z) = z) ∧ (∀ z ∈ B, DifferentiableAt ℂ χ z) ∧
      Set.InjOn χ B ∧
      (∀ z ∈ B, χ z ∈ ψ '' Metric.closedBall z R₀) ∧
      (∀ z ∈ B, ∃ w ∈ Metric.closedBall z R₀, χ z = ψ w ∧ F' (ψ w) = z ∧ ‖w - z‖ ≤ δ) ∧
      (∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, F' (ψ w) = z → ψ w = χ z) := by
  by_cases hB : B = ∅
  · refine ⟨fun z => z, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (intro z hz; exact absurd hz (by simp [hB]))
  · have hinj : Set.InjOn ψ Ω := by
      intro x hx y hy hxy
      calc x = F (ψ x) := (hψinv x hx).symm
        _ = F (ψ y) := by rw [hxy]
        _ = y := hψinv y hy
    have hderiv_ne : ∀ w ∈ Ω, deriv ψ w ≠ 0 :=
      Work.Parab.inversion.deriv_ne_zero_of_injOn hΩ hψd hinj
    obtain ⟨z₀, hz₀⟩ := Set.nonempty_iff_ne_empty.mpr hB
    have hz₀Ω : z₀ ∈ Ω := hcollar z₀ hz₀ (Metric.mem_closedBall_self hR₀.le)
    have hLpos : 0 < L := by
      have h1 : deriv ψ z₀ ≠ 0 := hderiv_ne z₀ hz₀Ω
      have h2 : 0 < ‖deriv ψ z₀‖ := norm_pos_iff.mpr h1
      have h3 : ‖deriv ψ z₀‖ ≤ L := hLb z₀ hz₀ z₀ (Metric.mem_closedBall_self hR₀.le)
      linarith
    have hδlt : δ < R₀ := by
      have h1 : 0 < δ' * L := mul_pos hδ' hLpos
      nlinarith [hδR₀, hR₀]
    set k : ℝ := δ' * L with hkdef
    have hk0 : 0 ≤ k := by rw [hkdef]; exact mul_nonneg hδ'.le hL
    have hk1 : k < 1 := by rw [hkdef]; exact hδL
    have hδR₀' : δ ≤ (1 - k) * R₀ := by rw [hkdef]; exact hδR₀
    -- ### chain rule for `F` at every `ψ w`, `w` in a collar
    have hFchain : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀,
        DifferentiableAt ℂ F (ψ w) ∧ deriv F (ψ w) * deriv ψ w = 1 :=
      fun z hz w hw => differentiableAt_and_deriv_of_comp_eq_id hΩ hψd hψinv
        (hcollar z hz hw) (hderiv_ne w (hcollar z hz hw))
    -- ### `F'` is differentiable at every `ψ w`, `w` in a collar
    have hF'diff : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, DifferentiableAt ℂ F' (ψ w) := by
      intro z hz w hw
      by_contra hnot
      have h0 : deriv F' (ψ w) = 0 := deriv_zero_of_not_differentiableAt hnot
      have h1 : ‖deriv F (ψ w)‖ ≤ δ' := by
        have h := hcloseD z hz w hw
        rwa [h0, zero_sub, norm_neg] at h
      have hmul : ‖deriv F (ψ w)‖ * ‖deriv ψ w‖ = 1 := by
        have h := congrArg norm (hFchain z hz w hw).2
        rwa [norm_mul, norm_one] at h
      have hne : deriv ψ w ≠ 0 := hderiv_ne w (hcollar z hz hw)
      have h3 : ‖deriv F (ψ w)‖ = 1 / ‖deriv ψ w‖ := by
        rw [eq_div_iff (norm_ne_zero_iff.mpr hne)]
        exact hmul
      have h4 : 1 / L ≤ 1 / ‖deriv ψ w‖ :=
        one_div_le_one_div_of_le (norm_pos_iff.mpr hne) (hLb z hz w hw)
      have h5 : δ' < 1 / L := by
        rw [lt_div_iff₀ hLpos]
        linarith [hδL]
      linarith
    -- ### the shadowing map `w ↦ F' (ψ w)` satisfies the abstract hypotheses
    have hSdiff : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀,
        DifferentiableAt ℂ (fun w => F' (ψ w)) w :=
      fun z hz w hw => (hF'diff z hz w hw).comp w
        (hψd.differentiableAt (hΩ.mem_nhds (hcollar z hz hw)))
    have hSval : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀, ‖F' (ψ w) - w‖ ≤ δ := by
      intro z hz w hw
      have h := hclose z hz w hw
      rwa [hψinv w (hcollar z hz hw)] at h
    have hSderiv : ∀ z ∈ B, ∀ w ∈ Metric.closedBall z R₀,
        ‖deriv (fun w => F' (ψ w)) w - 1‖ ≤ k := by
      intro z hz w hw
      have hder : deriv (fun w => F' (ψ w)) w = deriv F' (ψ w) * deriv ψ w :=
        deriv_comp w (hF'diff z hz w hw) (hψd.differentiableAt (hΩ.mem_nhds (hcollar z hz hw)))
      rw [hder]
      have hchain := (hFchain z hz w hw).2
      have h3 : deriv F' (ψ w) * deriv ψ w - 1
          = (deriv F' (ψ w) - deriv F (ψ w)) * deriv ψ w := by
        rw [← hchain]; ring
      rw [h3, hkdef, norm_mul]
      exact mul_le_mul (hcloseD z hz w hw) (hLb z hz w hw) (norm_nonneg _) hδ'.le
    obtain ⟨W, hW1, hW2, hW3⟩ := exists_branch_abstract (S := fun w => F' (ψ w))
      hR₀ hk0 hk1 hδ.le hδR₀' hδlt hSdiff hSval hSderiv
    refine ⟨fun z => ψ (W z), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact (hW1 z hz).2.1
    · intro z hz
      exact (hψd.differentiableAt (hΩ.mem_nhds (hcollar z hz (hW1 z hz).1))).comp z (hW3 z hz)
    · intro z₁ hz₁ z₂ hz₂ heq
      have heq' : ψ (W z₁) = ψ (W z₂) := heq
      have h₁ : F' (ψ (W z₁)) = z₁ := (hW1 z₁ hz₁).2.1
      have h₂ : F' (ψ (W z₂)) = z₂ := (hW1 z₂ hz₂).2.1
      rw [heq'] at h₁
      exact h₁.symm.trans h₂
    · intro z hz
      exact ⟨W z, (hW1 z hz).1, rfl⟩
    · intro z hz
      exact ⟨W z, (hW1 z hz).1, rfl, (hW1 z hz).2.1, (hW1 z hz).2.2⟩
    · intro z hz w hw hwz
      rw [hW2 z hz w hw hwz]

end

end Work.L62
