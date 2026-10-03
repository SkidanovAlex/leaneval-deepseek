import Mathlib
import Submission.Lib.Unif2.Work.Mori.Defs
import Submission.Lib.Unif2.HolomorphicLog

namespace Work.Mori

/-- **The monodromy of the argument of a nowhere-zero holomorphic function is trivial under the
challenge hypothesis.**  Let `X` be a connected complex one-manifold whose fundamental group has no
non-trivial homomorphism to `ℝ`, let `G : X → ℂ` be holomorphic on `X` and nowhere zero, and let
`f : ℝ → X` be a continuous `1`-periodic curve.  Then the closed curve `t ↦ G (f t)` admits a
continuous `1`-periodic argument function:
`Commons.Topology.Winding.HasArg (fun t => G (f t)) 0`.

Route: `u := fun y => Real.log ‖G y‖` is harmonic (`Submission.harmonicOnX_log_norm`,
`Submission/HolomorphicLog.lean`, or `Submission.harmonicOnXAt_log_norm` pointwise), so the challenge
hypothesis produces a global holomorphic conjugate `F` with `(F y).re = u y`
(`Submission.exists_holomorphicOnX_re_of_harmonic`); the function
`W := fun y => G y * Complex.exp (-(F y))` is holomorphic (`Submission.HolomorphicOnX.cexp`,
`HolomorphicOnX.mul`) with `‖W y‖ = 1` for all `y` (since `‖G y‖ > 0` and
`Real.exp (-log ‖G y‖) = 1 / ‖G y‖`), hence constant by
`Work.Mori.eq_const_of_holomorphicOnX_norm_eq`; writing that constant as `Complex.exp (i c)`, the
function `θ t = c + (F (f t)).im` is a continuous `1`-periodic argument for `t ↦ G (f t)`
(`F` is single-valued — this is where the hypothesis is used — and continuous). -/
theorem hasArg_comp_of_holomorphic_of_subsingleton
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x : X}
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    {G : X → ℂ} (hG : Submission.HolomorphicOnX G Set.univ) (hGne : ∀ y : X, G y ≠ 0)
    {f : ℝ → X} (hf : Continuous f) (hfper : ∀ t : ℝ, f (t + 1) = f t) :
    Commons.Topology.Winding.HasArg (fun t : ℝ => G (f t)) 0 := by
  -- A global holomorphic logarithm of `G` exists because `Hom(π₁(X), ℝ) = 0`.
  obtain ⟨H, hHhol, hHexp⟩ := Submission.HolomorphicOnX.exists_log_of_ne_zero x hG hGne
  have hHcont : Continuous H := hHhol.continuous
  refine ⟨fun t : ℝ => (H (f t)).im,
    Complex.continuous_im.comp (hHcont.comp hf), ?_, ?_⟩
  · intro t
    simp only [hfper t]
  · intro t
    rw [sub_zero]
    -- `G (f t) = exp (H (f t))`, and `exp z = ‖exp z‖ * exp (i · Im z)`.
    have hsplit : Complex.exp (H (f t))
        = ((Real.exp (H (f t)).re : ℝ) : ℂ)
          * Complex.exp (((H (f t)).im : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.re_add_im (H (f t))]
      rw [Complex.exp_add, ← Complex.ofReal_exp]
    show G (f t) = (‖G (f t)‖ : ℂ) * Complex.exp ((H (f t)).im * Complex.I)
    rw [hHexp (f t), Complex.norm_exp, hsplit]

end Work.Mori
