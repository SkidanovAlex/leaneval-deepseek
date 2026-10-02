import Mathlib
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Repelling.near_translation_mod
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.SatFree.gU_sgauge_loss

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Backward orbits inside the wide chart sector

This file proves `Work.SatFree.backward_orbit`: for a parabolic germ `f z = z + z ^ 2 * h z` with
the quantitative bounds `ParabolicBounds`, every `W` deep inside the wide sector of opening
`3π/2` (i.e. with `sgauge W = W.re + |W.im|` large) admits, for each `m`, an `m`-fold backward
iterate `W'` with `f^[m] (-1/W') = -1/W`, whose gauge has dropped by at most `m * C`:

  `M + m * C ≤ sgauge W  →  ∃ W', M ≤ sgauge W' ∧ (f^[m]) (-1/W') = -1/W`.

The proof has two ingredients.  The *one-step* lemma `backward_step_core` inverts the chart
dynamics: the local inverse `G` of `f` at `0` (from
`Work.FatouCoord.Petal.exists_local_inverse_of_parabolicBounds`) maps a small disc into itself, and
for `u = -1/W`, `v = Gu`, the point `W' = -1/v` satisfies `f (-1/W') = f v = u = -1/W`; the
algebraic identity `W' - (W - 1) = (u - v * h v)/u`, valid because `f v = v + v^2 h v`, shows
`‖W' - (W - 1)‖ ≤ (A + 4‖a‖ + 8) * ‖u‖`, and `sgauge` is `2`-Lipschitz with
`sgauge (W - 1) = sgauge W - 1`.  Iterating this step (induction on the number of steps) gives the
statement.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.SatFree

open Work.FatouCoord.Flower

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

private lemma sgauge_sub_one (W : ℂ) : sgauge (W - 1) = sgauge W - 1 := by
  simp only [sgauge, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring_nf

private theorem backward_step_core (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ M₀ C₀ : ℝ, 0 < M₀ ∧ 0 ≤ C₀ ∧ ∀ W : ℂ, M₀ ≤ sgauge W →
      ∃ W' : ℂ, f (-1 / W') = -1 / W ∧ sgauge W' ≥ sgauge W - C₀ := by
  obtain ⟨G, hGan, hG0, _h1, _h2, _h3, _h4, hGr⟩ :=
    Work.FatouCoord.Petal.exists_local_inverse_of_parabolicBounds hb
  -- disc on which `f ∘ G = id`
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp hGr
  have hδ₁' : ∀ w : ℂ, ‖w‖ < δ₁ → f (G w) = w :=
    fun w hw => hδ₁ (by simpa [dist_eq_norm] using hw)
  -- disc on which `G` is small
  have hcont : Tendsto G (𝓝 (0 : ℂ)) (𝓝 0) := by
    have h : Tendsto G (𝓝 (0 : ℂ)) (𝓝 (G 0)) := hGan.continuousAt
    rw [hG0] at h
    exact h
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ), ‖G w‖ < min r (1 / 4) := by
    have hmem : Metric.ball (0 : ℂ) (min r (1 / 4)) ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds 0 (lt_min hb.hr (by norm_num))
    have := hcont.eventually (show ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ Metric.ball (0 : ℂ) (min r (1 / 4))
      from hmem)
    simpa [Metric.mem_ball, dist_eq_norm] using this
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp hev
  have hδ₂' : ∀ w : ℂ, ‖w‖ < δ₂ → ‖G w‖ < min r (1 / 4) :=
    fun w hw => hδ₂ (by simpa [dist_eq_norm] using hw)
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hδ₁pos hδ₂pos
  have hδ₁ge : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hδ₂ge : δ ≤ δ₂ := by rw [hδdef]; exact min_le_right _ _
  set M₀ : ℝ := max 8 (4 / δ) with hM₀def
  have hM₀pos : 0 < M₀ := by
    rw [hM₀def]
    exact lt_of_lt_of_le (by norm_num) (le_max_left (8 : ℝ) (4 / δ))
  have hM₀δ : 4 / δ ≤ M₀ := by rw [hM₀def]; exact le_max_right _ _
  have hM₀8 : (8 : ℝ) ≤ M₀ := by rw [hM₀def]; exact le_max_left _ _
  refine ⟨M₀, 2 * A + 8 * ‖a‖ + 17, hM₀pos, ?_, ?_⟩
  · have hA0 : 0 ≤ A := hb.hA
    positivity
  · intro W hW
    have hWsg : (0 : ℝ) < sgauge W := lt_of_lt_of_le hM₀pos hW
    have hW0 : W ≠ 0 := by
      intro h0
      rw [h0] at hWsg
      simp [sgauge] at hWsg
    have hWnorm : M₀ / 2 ≤ ‖W‖ := by
      have h1 : sgauge W ≤ 2 * ‖W‖ := sgauge_le_two_mul_norm W
      linarith
    set u : ℂ := -1 / W with hudef
    have hu0 : u ≠ 0 := by rw [hudef]; exact div_ne_zero (by norm_num) hW0
    have hunorm : ‖u‖ = 1 / ‖W‖ := by simp [hudef]
    have hu_le : ‖u‖ ≤ 2 / M₀ := by
      rw [hunorm]
      have h2M : (2 : ℝ) / M₀ = 1 / (M₀ / 2) := by ring
      rw [h2M]
      exact one_div_le_one_div_of_le (by linarith : (0 : ℝ) < M₀ / 2) hWnorm
    have hstep : 2 / M₀ ≤ δ / 2 := by
      have h4 : 4 ≤ δ * M₀ := by
        have hh := mul_le_mul_of_nonneg_left hM₀δ hδpos.le
        rwa [mul_div_cancel₀ _ (ne_of_gt hδpos)] at hh
      rw [div_le_iff₀ hM₀pos]
      have htmp : δ / 2 * M₀ = δ * M₀ / 2 := by ring
      rw [htmp, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hu_lt_δ : ‖u‖ < δ := by linarith [hδpos]
    have hu_lt_δ₁ : ‖u‖ < δ₁ := lt_of_lt_of_le hu_lt_δ hδ₁ge
    have hu_lt_δ₂ : ‖u‖ < δ₂ := lt_of_lt_of_le hu_lt_δ hδ₂ge
    set v : ℂ := G u with hvdef
    have hfv : f v = u := by rw [hvdef]; exact hδ₁' u hu_lt_δ₁
    have hv_small : ‖v‖ < min r (1 / 4) := by rw [hvdef]; exact hδ₂' u hu_lt_δ₂
    have hvm : v ∈ ball 0 r := by
      rw [mem_ball_zero_iff]
      exact lt_of_lt_of_le hv_small (min_le_left _ _)
    have hv_le4 : ‖v‖ < 1 / 4 := lt_of_lt_of_le hv_small (min_le_right _ _)
    have hv0 : v ≠ 0 := by
      intro h0
      have hzero : u = 0 := by
        rw [← hfv, h0, hb.f_eq 0 (by simpa using hb.hr)]
        ring
      exact hu0 hzero
    -- the algebra
    have huv : u = v + v ^ 2 * h v := by
      rw [← hfv]
      exact hb.f_eq v hvm
    have hWu : W = -1 / u := by rw [hudef]; field_simp
    have hmul : u * ((-1 / v) - (W - 1)) = u - v * h v := by
      have hWu' : W - 1 = -1 / u - 1 := by rw [hWu]
      rw [hWu']
      have hexp : u * ((-1 / v) - (-1 / u - 1)) = -(u / v) + 1 + u := by
        field_simp
        ring
      rw [hexp]
      have hdiv : u / v = 1 + v * h v := by
        rw [huv]
        field_simp
      rw [hdiv, huv]
      ring
    have hid : (-1 / v) - (W - 1) = (u - v * h v) / u := by
      rw [← hmul]
      exact (mul_div_cancel_left₀ _ hu0).symm
    -- norm estimates
    have hv_le_2u : ‖v‖ ≤ 2 * ‖u‖ := by
      have hdiff : v - u = -(v ^ 2 * h v) := by rw [huv]; ring
      have h1 : ‖v - u‖ ≤ 2 * ‖v‖ ^ 2 := by
        rw [hdiff, norm_neg, norm_mul, norm_pow]
        have h := mul_le_mul_of_nonneg_left (hb.h_bound v hvm) (sq_nonneg ‖v‖)
        linarith
      have h2 : ‖v‖ ≤ ‖u‖ + ‖v - u‖ := by
        calc ‖v‖ = ‖u + (v - u)‖ := by ring_nf
          _ ≤ ‖u‖ + ‖v - u‖ := norm_add_le _ _
      have h3 : 2 * ‖v‖ ^ 2 ≤ ‖v‖ / 2 := by nlinarith [hv_le4, norm_nonneg v]
      linarith
    have hv_le_u : ‖v‖ ≤ 2 * ‖u‖ := hv_le_2u
    have h1hv : ‖1 - h v‖ ≤ (A * ‖v‖ + ‖a‖) * ‖v‖ := by
      have hc := hb.h_close v hvm
      have hsplit : (1 : ℂ) - h v = -(h v - 1 - a * v) - a * v := by ring
      rw [hsplit]
      calc ‖-(h v - 1 - a * v) - a * v‖
          ≤ ‖-(h v - 1 - a * v)‖ + ‖a * v‖ := norm_sub_le _ _
        _ = ‖h v - 1 - a * v‖ + ‖a‖ * ‖v‖ := by rw [norm_neg, norm_mul]
        _ ≤ A * ‖v‖ ^ 2 + ‖a‖ * ‖v‖ := by linarith
        _ = (A * ‖v‖ + ‖a‖) * ‖v‖ := by ring
    have hnum : ‖u - v * h v‖ ≤ (A + 4 * ‖a‖ + 8) * ‖u‖ ^ 2 := by
      have hkey : u - v * h v = v * (1 - h v) + v ^ 2 * h v := by rw [huv]; ring
      rw [hkey]
      calc ‖v * (1 - h v) + v ^ 2 * h v‖
          ≤ ‖v * (1 - h v)‖ + ‖v ^ 2 * h v‖ := norm_add_le _ _
        _ = ‖v‖ * ‖1 - h v‖ + ‖v‖ ^ 2 * ‖h v‖ := by rw [norm_mul, norm_mul, norm_pow]
        _ ≤ ‖v‖ * ((A * ‖v‖ + ‖a‖) * ‖v‖) + ‖v‖ ^ 2 * 2 := by
            have hb1 : ‖v‖ * ‖1 - h v‖ ≤ ‖v‖ * ((A * ‖v‖ + ‖a‖) * ‖v‖) :=
              mul_le_mul_of_nonneg_left h1hv (norm_nonneg v)
            have hb2 : ‖v‖ ^ 2 * ‖h v‖ ≤ ‖v‖ ^ 2 * 2 :=
              mul_le_mul_of_nonneg_left (hb.h_bound v hvm) (sq_nonneg ‖v‖)
            linarith
        _ ≤ (A + 4 * ‖a‖ + 8) * ‖u‖ ^ 2 := by
            have hA0 : 0 ≤ A := hb.hA
            have hv2 : ‖v‖ ^ 2 ≤ 4 * ‖u‖ ^ 2 := by
              nlinarith [hv_le_u, norm_nonneg v, norm_nonneg u]
            have hv3a : ‖v‖ ^ 3 ≤ ‖v‖ ^ 2 / 4 := by
              have h := mul_le_mul_of_nonneg_left hv_le4.le (sq_nonneg ‖v‖)
              nlinarith [h]
            have hv3b : ‖v‖ ^ 2 / 4 ≤ ‖u‖ ^ 2 := by linarith
            have hv3 : A * ‖v‖ ^ 3 ≤ A * ‖u‖ ^ 2 := by
              have h1 : A * ‖v‖ ^ 3 ≤ A * (‖v‖ ^ 2 / 4) :=
                mul_le_mul_of_nonneg_left hv3a hA0
              have h2 : A * (‖v‖ ^ 2 / 4) ≤ A * ‖u‖ ^ 2 :=
                mul_le_mul_of_nonneg_left hv3b hA0
              linarith
            have h5 : ‖a‖ * ‖v‖ ^ 2 ≤ ‖a‖ * (4 * ‖u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hv2 (norm_nonneg a)
            have h6 : 2 * ‖v‖ ^ 2 ≤ 2 * (4 * ‖u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hv2 (by norm_num)
            linarith [hv3, h5, h6]
    have hη : ‖(-1 / v) - (W - 1)‖ ≤ (A + 4 * ‖a‖ + 8) * ‖u‖ := by
      rw [hid, norm_div, div_le_iff₀ (norm_pos_iff.mpr hu0)]
      nlinarith [hnum]
    have h2M₀ : 2 / M₀ ≤ 1 / 4 := by
      rw [div_le_iff₀ hM₀pos]
      linarith
    have hu_le4 : ‖u‖ ≤ 1 / 4 := by linarith [hu_le, h2M₀]
    refine ⟨-1 / v, ?_, ?_⟩
    · have hv' : -1 / (-1 / v) = v := by field_simp
      rw [hv', hfv, hudef]
    · have hsub := sgauge_sub_le (W - 1) ((-1 / v) - (W - 1))
      have hsum : (W - 1) + ((-1 / v) - (W - 1)) = -1 / v := by ring
      rw [hsum] at hsub
      have hsub1 : sgauge (W - 1) = sgauge W - 1 := sgauge_sub_one W
      rw [hsub1] at hsub
      have hC1 : 0 ≤ A + 4 * ‖a‖ + 8 := by
        have hA0 : 0 ≤ A := hb.hA
        positivity
      nlinarith [hsub, hη, hu_le4, hC1]
/-- **Backward orbits exist in the wide chart sector and lose only `O(1)` of `sgauge` per step.**

Setting: `f z = z + z² h z` on `ball 0 r` with `h 0 = 1` (`ParabolicBounds`), and
`wMap f W = -1 / f (-1 / W)` (`Work.FatouCoord.wMap`); for `‖W‖` large,
`‖wMap f W - (W + 1)‖ ≤ K / ‖W‖` (`Work.FatouCoord.Repelling.near_translation_mod`), because
`wMap f W - W = h (-1/W) / (1 + (-1/W) * h (-1/W))` (`Work.FatouCoord.wMap_eq`).

This is the "pull back `m` steps inside the wide petal" input of `SatFree.germ_flowerFix_wideSat`.
It is the iterated form of the one-step statement

  `∃ M C ≥ 0, ∀ W, M < sgauge W → ∃ W', wMap f W' = W ∧ W'.re ≥ W.re - 1 - C/‖W‖
     ∧ |W'.im - W.im| ≤ C/‖W‖`

(prove that as a private lemma: put `W' = W - 1 + δ` and solve the fixed point
`δ = -g (W-1+δ)`, `g z = wMap f z - z - 1`, in the disc `‖δ‖ ≤ 2K/‖W‖`; `g` maps that disc into
itself and is `1/2`-Lipschitz there, since `g z = h(-1/z)/(1 + (-1/z)h(-1/z))` with `h`
differentiable at `0`, or equivalently `‖deriv (wMap f) z - 1‖ ≤ C'/‖z‖`).  Each step loses
`1 + C/‖W‖ ≤ 1 + C'` of `sgauge` as long as `sgauge > 1`, so iterating `m` times and translating
back through the chart `W ↦ -1/W` (the `f`-orbit relation is `wMap f W' = W ↔ f (-1/W') = -1/W`)
gives the statement: start from `sgauge W ≥ M + m*C` and land on `sgauge W' ≥ M`. -/
theorem backward_orbit {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ M C : ℝ, 1 ≤ C ∧ ∀ W : ℂ, ∀ m : ℕ,
      M + (m : ℝ) * C ≤ Work.FatouCoord.Flower.sgauge W →
      ∃ W' : ℂ, M ≤ Work.FatouCoord.Flower.sgauge W' ∧ (f^[m]) (-1 / W') = -1 / W := by
  obtain ⟨M₀, C₀, _hM₀pos, hC₀nn, hst⟩ := backward_step_core hb
  have hCnn : 0 ≤ max C₀ 1 := le_trans hC₀nn (le_max_left _ _)
  refine ⟨M₀, max C₀ 1, le_max_right _ _, ?_⟩
  have key : ∀ j : ℕ, ∀ V : ℂ, M₀ + (j : ℝ) * max C₀ 1 ≤ sgauge V →
      ∃ V' : ℂ, M₀ ≤ sgauge V' ∧ (f^[j]) (-1 / V') = -1 / V := by
    intro j
    induction j with
    | zero =>
      intro V hV
      exact ⟨V, by simpa using hV, by simp⟩
    | succ j ih =>
      intro V hV
      have hcast : M₀ + ((j : ℝ) + 1) * max C₀ 1 ≤ sgauge V := by
        simpa [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hV
      have hM₀le : M₀ ≤ sgauge V := by
        have h2 : M₀ ≤ M₀ + ((j : ℝ) + 1) * max C₀ 1 := by
          have : 0 ≤ ((j : ℝ) + 1) * max C₀ 1 := mul_nonneg (by positivity) hCnn
          linarith
        linarith
      obtain ⟨V₁, hV₁f, hV₁g⟩ := hst V hM₀le
      have hstep : M₀ + (j : ℝ) * max C₀ 1 ≤ sgauge V₁ := by
        have hle : C₀ ≤ max C₀ 1 := le_max_left _ _
        linarith
      obtain ⟨V', hV'g, hV'f⟩ := ih V₁ hstep
      exact ⟨V', hV'g, by rw [Function.iterate_succ_apply', hV'f, hV₁f]⟩
  exact fun W m hW => key m W hW

end

end Work.SatFree
