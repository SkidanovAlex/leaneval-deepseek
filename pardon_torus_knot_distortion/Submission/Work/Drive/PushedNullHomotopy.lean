import Mathlib
import Submission.Work.Drive.WPushDefs
import Submission.Work.InnermostDisk.boundsDiscInSurface_of_not_isEssential

namespace Work.Drive

open LeanEval.KnotTheory.PardonDistortion
open Work.CoreTopology

noncomputable section

/-- The boundary of the disc has norm one. -/
private lemma norm_circlePoint (θ : ℝ) :
    ‖((Work.CoreTopology.circlePoint θ : Work.InnermostDisk.Disc) : ℂ)‖ = 1 := by
  rw [Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- A point of the closed unit disc has norm at most one. -/
private lemma norm_le_one_of_disc (z : Work.InnermostDisk.Disc) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := Metric.mem_closedBall.mp z.2
  rwa [dist_zero_right] at h

/-- **The pushed null-homotopy of an inessential curve.**  Given a continuous collar push
`(pushP, levP)` for the torus `F = ψ(F_std)`, whose level set `{1}` is `F` and which changes the
level by the prescribed amount on the collar, every closed curve `γ` of `F` that is
*inessential* (winding vector zero) bounds a disc map whose open interior lies entirely in
**either** of the two sides of `F`: this is a null-homotopy of `γ` inside `F`
(`Work.InnermostDisk.boundsDiscInSurface_of_not_isEssential`, which gives a disc in the surface)
pushed off `F` by the collar push.  The two sides are `{1 < levP}` and `{levP < 1}`. -/
theorem PushedNullHomotopy (ψ : R3 ≃ₜ R3) (pushP : R3 → ℝ → R3) (levP : R3 → ℝ)
    (hlev : ∀ x : R3, levP x = 1 ↔ x ∈ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier)
    (hcont : Continuous (Function.uncurry pushP))
    (hzero : ∀ x : R3, pushP x 0 = x)
    (hshift : ∀ x : R3, ∀ δ : ℝ, levP x ∈ Set.Icc (1/2) (5/4) → |δ| ≤ 1/4 →
      levP (pushP x δ) = levP x + δ) :
    (∀ γ : Work.CoreTopology.ClosedCurve (Work.CoreTopology.ParamTorus.mapHomeomorph ψ),
      ¬ Work.CoreTopology.IsEssential _ γ →
      (∃ H : C(Work.InnermostDisk.Disc, R3),
        (∀ θ : ℝ, H (Work.CoreTopology.circlePoint θ) = γ.γ θ) ∧
        ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 → 1 < levP (H z)) ∧
      (∃ H : C(Work.InnermostDisk.Disc, R3),
        (∀ θ : ℝ, H (Work.CoreTopology.circlePoint θ) = γ.γ θ) ∧
        ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 → levP (H z) < 1)) := by
  intro γ hγ
  -- A disc in the surface bounded by `γ`.
  obtain ⟨e, he⟩ := Work.InnermostDisk.boundsDiscInSurface_of_not_isEssential
    (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) hγ
  have hecont : Continuous fun z : Work.InnermostDisk.Disc =>
      ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3) :=
    continuous_subtype_val.comp e.continuous
  have hnorm : Continuous fun z : Work.InnermostDisk.Disc => ‖(z : ℂ)‖ :=
    continuous_norm.comp continuous_subtype_val
  -- The level of a point of the disc in the surface is `1`.
  have hlevel : ∀ z : Work.InnermostDisk.Disc,
      levP ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3) = 1 :=
    fun z => (hlev _).mpr (e z).2
  -- The push of that disc by a fixed amount `ε` along the collar.
  -- Its boundary is `γ` (the push amount vanishes there) and its level is `1 + ε` on the
  -- open disc (up to the non-negative factor `1 - ‖z‖`).
  have hkey : ∀ ε : ℝ, |ε| ≤ 1/4 →
      ∃ H : C(Work.InnermostDisk.Disc, R3),
        (∀ θ : ℝ, H (Work.CoreTopology.circlePoint θ) = γ.γ θ) ∧
        (∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 →
          levP (H z) = 1 + ε * (1 - ‖(z : ℂ)‖)) := by
    intro ε hε
    let F : Work.InnermostDisk.Disc → R3 := fun z =>
      pushP ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3)
        (ε * (1 - ‖(z : ℂ)‖))
    have hcontF : Continuous F :=
      hcont.comp (hecont.prodMk (continuous_const.mul (continuous_const.sub hnorm)))
    refine ⟨⟨F, hcontF⟩, ?_, ?_⟩
    · intro θ
      have h1 : ‖((Work.CoreTopology.circlePoint θ : Work.InnermostDisk.Disc) : ℂ)‖ = 1 :=
        norm_circlePoint θ
      show F (Work.CoreTopology.circlePoint θ) = γ.γ θ
      simp only [F, h1, sub_self, mul_zero, hzero]
      exact he θ
    · intro z hz
      have hze : levP ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3)
          = 1 := hlevel z
      have hIcc : levP ((e z : (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier) : R3)
          ∈ Set.Icc (1/2 : ℝ) (5/4) := by
        rw [hze]; norm_num
      have hdle1 : ‖(z : ℂ)‖ ≤ 1 := norm_le_one_of_disc z
      have hnn : 0 ≤ 1 - ‖(z : ℂ)‖ := by linarith
      have hdle : |ε * (1 - ‖(z : ℂ)‖)| ≤ 1/4 := by
        rw [abs_mul]
        have h2 : |1 - ‖(z : ℂ)‖| ≤ 1 := by rw [abs_of_nonneg hnn]; simp
        calc |ε| * |1 - ‖(z : ℂ)‖| ≤ (1/4) * 1 :=
              mul_le_mul hε h2 (abs_nonneg _) (by norm_num)
          _ ≤ 1 / 4 := by norm_num
      show levP (F z) = 1 + ε * (1 - ‖(z : ℂ)‖)
      simp only [F]
      rw [hshift _ _ hIcc hdle, hze]
  constructor
  · -- the side `{1 < levP}`: push by `+ 1/4`.
    obtain ⟨H, hb, hlev'⟩ := hkey (1/4) (by norm_num)
    refine ⟨H, hb, fun z hz => ?_⟩
    rw [hlev' z hz]
    have hpos : 0 < 1 - ‖(z : ℂ)‖ := by have := norm_le_one_of_disc z; linarith
    linarith
  · -- the side `{levP < 1}`: push by `- 1/4`.
    obtain ⟨H, hb, hlev'⟩ := hkey (-1/4) (by norm_num)
    refine ⟨H, hb, fun z hz => ?_⟩
    rw [hlev' z hz]
    have hpos : 0 < 1 - ‖(z : ℂ)‖ := by have := norm_le_one_of_disc z; linarith
    linarith

end

end Work.Drive
