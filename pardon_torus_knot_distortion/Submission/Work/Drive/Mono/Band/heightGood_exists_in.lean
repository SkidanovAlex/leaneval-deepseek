import Mathlib
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.Generic.ae_height_morse
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized

namespace Work.Drive.Mono.Band

/-- **Every non-empty open set of directions contains a good direction.**

`Work.Drive.Generic.ae_height_morse` says that for almost every `n : R3` the height
`heightIn ψ n = fun q => ⟪n, par ψ q⟫` has injective Hessian at every critical point (in the form
`∀ p, dF p = 0 → ∀ w, (∀ w', Hess p w w' = 0) → w = 0`, converted to
`Function.Injective (fderiv ℝ (fderiv ℝ (heightIn ψ n)) p)` by
`Work.Drive.EpsForm.injective_fderiv_fderiv_of_forall` in `tiltedSweepGenericity_holds_sized.lean`).
A set whose complement is null has empty interior (`IsOpen.measure_pos`), hence is dense, so the
given non-empty open `U` contains a direction `n₁` with the Morse property.  Then
`Work.Drive.EpsForm.goodHeight_exists ψ n₁ ρ hρ (Morse at n₁)` produces `n₂ ∈ Metric.ball n₁ ρ`
whose height is Morse *and* has injectively valued critical points, i.e. `HeightGood ψ n₂`; take
`ρ` small enough that `Metric.ball n₁ ρ ⊆ U`. -/
theorem heightGood_exists_in (ψ : Submission.Diffeo)
    {U : Set LeanEval.KnotTheory.PardonDistortion.R3} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ n ∈ U, Work.Drive.Mono.Band.HeightGood ψ n := by
  classical
  -- ## 1. a ball around a point of `U`, contained in `U`
  obtain ⟨x, hxU⟩ := hne
  obtain ⟨ρ₀, hρ₀, hρ₀U⟩ := Metric.isOpen_iff.mp hU x hxU
  -- ## 2. almost every direction is Morse (Gauss map + Sard)
  have hΦ3 : ContDiff ℝ 3 (Work.BoxShrink.Pinch.par ψ) :=
    (Work.Smooth.Morse.param_contDiff ψ).of_le (WithTop.coe_le_coe.mpr le_top)
  have himm : ∀ p : ℝ × ℝ, Function.Injective (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p) :=
    Work.Smooth.Morse.Immersion.isImmersion ψ
  have hae := Work.Drive.Generic.ae_height_morse hΦ3 himm
  -- ## 3. a Morse direction inside that ball
  obtain ⟨n₁, hn₁ball, hn₁w⟩ := Work.Drive.EpsForm.exists_mem_ball_of_ae
    (fun n : LeanEval.KnotTheory.PardonDistortion.R3 => ∀ p : ℝ × ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
      ∀ w : ℝ × ℝ, (∀ w' : ℝ × ℝ,
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q))) p)
          w w' = 0) → w = 0)
    hae x hρ₀
  have hn₁ball' : dist n₁ x < ρ₀ := Metric.mem_ball.mp hn₁ball
  have hn₁Morse : ∀ p : ℝ × ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₁ (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
      Function.Injective
        (fderiv ℝ (fderiv ℝ
          (fun q : ℝ × ℝ => inner ℝ n₁ (Work.BoxShrink.Pinch.par ψ q))) p) :=
    Work.Drive.EpsForm.injective_fderiv_fderiv_of_forall hn₁w
  -- ## 4. a direction near `n₁`, still inside the ball, that is Morse *and* injectively valued
  obtain ⟨n₂, hn₂ball, hn₂Morse, hn₂dist⟩ :=
    Work.Drive.EpsForm.goodHeight_exists ψ n₁ (ρ₀ - dist n₁ x)
      (sub_pos.mpr hn₁ball') hn₁Morse
  have hn₂ball' : dist n₂ n₁ < ρ₀ - dist n₁ x := Metric.mem_ball.mp hn₂ball
  -- ## 5. it lies in `U`
  refine ⟨n₂, hρ₀U ?_, hn₂Morse, hn₂dist⟩
  rw [Metric.mem_ball]
  calc dist n₂ x ≤ dist n₂ n₁ + dist n₁ x := dist_triangle _ _ _
    _ < (ρ₀ - dist n₁ x) + dist n₁ x := by linarith
    _ = ρ₀ := by ring

end Work.Drive.Mono.Band
