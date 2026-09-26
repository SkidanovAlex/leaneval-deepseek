import Mathlib
import Submission.Work.Drive.CleanDiscsDefs

/-!
# The pushed null-homotopy with a prescribed level profile

`Work.Drive.pushedNullHomotopy_level` gives, for an inessential closed curve `γ` of the torus and a
constant `ε` with `|ε| ≤ 1/4`, a disc map `H` with boundary `γ` and level
`levP (H z) = 1 + ε (1 - ‖z‖)` on the open disc.  Here we show that the level profile can be
*prescribed*: for every continuous `ε : 𝔻 → ℝ` with `ε = 0` on the boundary circle and
`|ε| ≤ 1/8`, there is a disc map with boundary `γ` and level exactly `1 + ε z` everywhere.

This is what the δ-based cut-and-paste needs for its cap replacement: the cap's level profile
`S.ε` of `Work.Drive.InnermostPushData` has to be realised by an actual disc map.

Route: take the constant-profile null-homotopy with `ε₀ = 1/16` (level `1 + (1-‖z‖)/16`, which
lies in the collar `[1/2, 5/4]`), and push it by the continuous amount
`ε z - (1 - ‖z‖)/16`, of modulus at most `1/8 + 1/16 = 3/16 ≤ 1/4`; `PD.hshift` then gives the
level `1 + ε z`, and the push vanishes on the boundary circle since both terms do.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive

open Work.CoreTopology

noncomputable section

/-- **The pushed null-homotopy with a prescribed level profile.** -/
theorem pushedNullHomotopy_profile {ψ : R3 ≃ₜ R3} (PD : PushData ψ)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) (hγ : ¬ IsEssential _ γ)
    (ε : C(Work.InnermostDisk.Disc, ℝ))
    (hεbdy : ∀ θ : ℝ, ε (circlePoint θ) = 0)
    (hε : ∀ w : Work.InnermostDisk.Disc, |ε w| ≤ 1/8) :
    ∃ H : C(Work.InnermostDisk.Disc, R3),
      (∀ θ : ℝ, H (circlePoint θ) = γ.γ θ) ∧
      ∀ w : Work.InnermostDisk.Disc, PD.levP (H w) = 1 + ε w := by
  obtain ⟨H₀, hH₀bdy, hH₀lev⟩ :=
    pushedNullHomotopy_level PD γ hγ (1/16) (by norm_num)
  have hnorm : Continuous fun w : Work.InnermostDisk.Disc => ‖(w : ℂ)‖ :=
    continuous_norm.comp continuous_subtype_val
  have hnorm_le : ∀ w : Work.InnermostDisk.Disc, ‖(w : ℂ)‖ ≤ 1 := fun w => by
    have h := w.2; rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hlev : ∀ w : Work.InnermostDisk.Disc,
      PD.levP (H₀ w) = 1 + (1/16) * (1 - ‖(w : ℂ)‖) := by
    intro w
    rcases lt_or_eq_of_le (hnorm_le w) with hlt | heq
    · exact hH₀lev w hlt
    · obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq w heq
      have h1 : H₀ w = γ.γ θ := by
        rw [← hθ]
        exact (congrArg H₀ (Subtype.ext rfl)).trans (hH₀bdy θ)
      have h2 : PD.levP (γ.γ θ) = 1 := (PD.hlev _).mpr (γ.mem θ)
      rw [h1, h2, heq]; ring
  refine ⟨⟨fun w => PD.pushP (H₀ w) (ε w - (1/16) * (1 - ‖(w : ℂ)‖)), ?_⟩, ?_, ?_⟩
  · refine PD.hcont.comp (H₀.continuous.prodMk ?_)
    exact ε.continuous.sub (continuous_const.mul (continuous_const.sub hnorm))
  · intro θ
    have h1 : ‖((circlePoint θ : Work.InnermostDisk.Disc) : ℂ)‖ = 1 := by
      rw [circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    show PD.pushP (H₀ (circlePoint θ)) (ε (circlePoint θ) - (1/16) * (1 - ‖_‖)) = γ.γ θ
    rw [hεbdy θ, h1, sub_self, mul_zero, sub_zero, PD.hzero]
    exact hH₀bdy θ
  · intro w
    have hle : ‖(w : ℂ)‖ ≤ 1 := hnorm_le w
    have hnn : 0 ≤ 1 - ‖(w : ℂ)‖ := by linarith
    have hpre : PD.levP (H₀ w) ∈ Set.Icc (1/2 : ℝ) (5/4) := by
      rw [hlev w]
      have h1 : 0 ≤ (1/16) * (1 - ‖(w : ℂ)‖) := by
        have := hnn; nlinarith
      have h2 : (1/16) * (1 - ‖(w : ℂ)‖) ≤ 1/4 := by
        have hle1 : 1 - ‖(w : ℂ)‖ ≤ 1 := by
          linarith [norm_nonneg (w : ℂ), hle]
        calc (1/16) * (1 - ‖(w : ℂ)‖) ≤ (1/16) * 1 :=
              mul_le_mul_of_nonneg_left hle1 (by norm_num)
          _ = 1/16 := by norm_num
          _ ≤ 1/4 := by norm_num
      constructor <;> linarith
    have hd : |ε w - (1/16) * (1 - ‖(w : ℂ)‖)| ≤ 1/4 := by
      have h1 : |(1/16 : ℝ) * (1 - ‖(w : ℂ)‖)| ≤ 1/16 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/16), abs_of_nonneg hnn]
        have hle1 : 1 - ‖(w : ℂ)‖ ≤ 1 := by
          linarith [norm_nonneg (w : ℂ), hle]
        calc (1/16) * (1 - ‖(w : ℂ)‖) ≤ (1/16) * 1 :=
              mul_le_mul_of_nonneg_left hle1 (by norm_num)
          _ = 1/16 := by norm_num
      calc |ε w - (1/16) * (1 - ‖(w : ℂ)‖)|
          ≤ |ε w| + |(1/16) * (1 - ‖(w : ℂ)‖)| := abs_sub _ _
        _ ≤ 1/8 + 1/16 := add_le_add (hε w) h1
        _ ≤ 1/4 := by norm_num
    show PD.levP (PD.pushP (H₀ w) (ε w - (1/16) * (1 - ‖(w : ℂ)‖))) = 1 + ε w
    rw [PD.hshift _ _ hpre hd, hlev w]
    ring

end

end Work.Drive
