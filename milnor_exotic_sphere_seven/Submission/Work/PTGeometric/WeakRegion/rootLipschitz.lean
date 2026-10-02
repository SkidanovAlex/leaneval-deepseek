import Mathlib
import Submission.Work.PTGeometric.WeakRegion.HalfSpaceGraphData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric.WeakRegion

noncomputable section

variable {n : ℕ} [NeZero n]

/-- **The tangential mean-value bound.**  For `s ∈ [0,δ]` and `a`, `b` in the box ball, the
difference `F (a,s) - F (b,s)` is bounded by `M ‖a - b‖`: the tangential derivatives `Du` are
bounded by `M` and the ball is convex. -/
theorem abs_F_sub_F_le {S : HalfSpaceGraphSetup n} {ρ δ M : ℝ} (B : S.Box ρ δ M)
    {s : ℝ} (hs : s ∈ Set.Icc 0 δ) {a b : hsTang n}
    (ha : a ∈ Metric.ball (hsMk S.p) ρ) (hb : b ∈ Metric.ball (hsMk S.p) ρ) :
    |S.F (a, s) - S.F (b, s)| ≤ M * ‖a - b‖ := by
  have hbnd : ∀ v ∈ Metric.ball (hsMk S.p) ρ, ‖S.Du (v, s)‖ ≤ M := by
    intro v hv
    refine ContinuousLinearMap.opNorm_le_bound _ (le_of_lt B.hM) fun w => ?_
    rw [S.Du_apply]
    calc ‖S.L (v, s) ((w : hsTang n) : EuclideanSpace ℝ (Fin n))‖
        ≤ ‖S.L (v, s)‖ * ‖((w : hsTang n) : EuclideanSpace ℝ (Fin n))‖ :=
          (S.L (v, s)).le_opNorm _
      _ = ‖S.L (v, s)‖ * ‖w‖ := rfl
      _ ≤ M * ‖w‖ :=
          mul_le_mul_of_nonneg_right (B.hL v hv s hs).1 (norm_nonneg w)
  have h := (convex_ball (hsMk S.p) ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun v : hsTang n => S.F (v, s)) (f' := fun v : hsTang n => S.Du (v, s))
    (fun v hv => S.hasFDerivWithinAt_F_slice B s hs v hv) hbnd hb ha
  rwa [Real.norm_eq_abs] at h

/-- **The root function is Lipschitz.** If `h` is the root function of `F` on a box `B` (`Root B h`),
then on `ball (hsMk S.p) ρ` one has `|h u' - h u| ≤ (2 M / |c|) ‖u' - u‖`, the constant coming from
the uniform lower bound `|∂_s F| ≥ |c|/2` on the box and the bound `‖∂_u F‖ ≤ M`. -/
theorem rootLipschitz {n : ℕ} [NeZero n] (S : Work.PTGeometric.WeakRegion.HalfSpaceGraphSetup n)
    {ρ δ M : ℝ} {B : S.Box ρ δ M} {h : Work.PTGeometric.WeakRegion.hsTang n → ℝ}
    (H : S.Root B h) :
    ∀ u ∈ Metric.ball (Work.PTGeometric.WeakRegion.hsMk S.p) ρ,
      ∀ u' ∈ Metric.ball (Work.PTGeometric.WeakRegion.hsMk S.p) ρ,
      |h u' - h u| ≤ 2 * M / |S.c| * ‖u' - u‖ := by
  have hcneg : S.c < 0 := S.hc
  have habs : (0 : ℝ) < |S.c| := abs_pos.mpr (ne_of_lt hcneg)
  have hKnn : 0 ≤ 2 * M / |S.c| := by
    have h1 : (0 : ℝ) < 2 * M := by linarith [B.hM]
    exact le_of_lt (div_pos h1 habs)
  -- the one-sided estimate `h b - h a ≤ K ‖b - a‖`, from the slice monotonicity and the mean value
  -- bound for the tangential variable
  have key : ∀ a ∈ Metric.ball (hsMk S.p) ρ, ∀ b ∈ Metric.ball (hsMk S.p) ρ,
      h b - h a ≤ 2 * M / |S.c| * ‖b - a‖ := by
    intro a ha b hb
    obtain ⟨haI, hFa⟩ := H.hmem a ha
    obtain ⟨hbI, hFb⟩ := H.hmem b hb
    rcases lt_or_ge (h a) (h b) with hlt | hle
    · -- `h a < h b`: compare the two zeros through the slice at `b`
      have hslice : S.F (b, h b) - S.F (b, h a) ≤ S.c / 2 * (h b - h a) :=
        (S.slice_mem_Icc B hb haI hbI hlt.le).2
      have htan : |S.F (a, h a) - S.F (b, h a)| ≤ M * ‖a - b‖ :=
        abs_F_sub_F_le (S := S) B haI ha hb
      have hge : -(M * ‖a - b‖) ≤ S.F (a, h a) - S.F (b, h a) := neg_le_of_abs_le htan
      have hmain : -(M * ‖a - b‖) ≤ S.c / 2 * (h b - h a) := by
        rw [hFa] at hge
        rw [hFb] at hslice
        linarith
      -- divide by the negative scalar `c/2`
      have hpos : (0 : ℝ) < -(S.c / 2) := by linarith
      have hcomm : S.c / 2 * (h b - h a) = (h b - h a) * (S.c / 2) := by ring
      rw [hcomm, norm_sub_rev a b] at hmain
      have h1 : -((h b - h a) * (S.c / 2)) ≤ M * ‖b - a‖ := by linarith
      have h2 : (h b - h a) * (-(S.c / 2)) = -((h b - h a) * (S.c / 2)) := by ring
      have h3 : (h b - h a) * (-(S.c / 2)) ≤ M * ‖b - a‖ := by rw [h2]; exact h1
      have h4 : h b - h a ≤ M * ‖b - a‖ / (-(S.c / 2)) := (le_div_iff₀ hpos).mpr h3
      have h5 : M * ‖b - a‖ / (-(S.c / 2)) = 2 * M / |S.c| * ‖b - a‖ := by
        rw [abs_of_neg hcneg]
        field_simp
      rw [h5] at h4
      exact h4
    · -- `h b ≤ h a`: the bound is trivial
      have hmul := mul_nonneg hKnn (norm_nonneg (b - a))
      linarith
  intro u hu u' hu'
  have h1 := key u hu u' hu'
  have h2 := key u' hu' u hu
  rw [norm_sub_rev u u'] at h2
  rw [abs_le]
  exact ⟨by linarith, h1⟩

end

end Work.PTGeometric.WeakRegion
