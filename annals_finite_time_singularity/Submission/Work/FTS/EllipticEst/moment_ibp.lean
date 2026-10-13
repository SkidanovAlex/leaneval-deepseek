import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- **The two integrations by parts on `(0,∞)` behind the radial energy identity.**  `∫F·H'' = ∫F''·H` and `∫G·H' = -∫G'·H`, with the boundary terms `F·H'`, `F'·H` and `G·H` vanishing at `0⁺` and at `+∞`, integrability of the six products, and differentiability of `F, F', G, H, H'` on `(0,∞)`.  Proof: `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` twice (with `(u,v) = (F,H')` and `(u,v) = (F',H)`) for the first identity, once (with `(u,v) = (G,H)`) for the second. -/
theorem moment_ibp (F F' F'' G G' H H' H'' : ℝ → ℝ)
    (hF : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' z) z)
    (hF' : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt F' (F'' z) z)
    (hG : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt G (G' z) z)
    (hH : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt H (H' z) z)
    (hH' : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt H' (H'' z) z)
    (h1 : MeasureTheory.IntegrableOn (fun z => F z * H'' z) (Set.Ioi (0 : ℝ)))
    (h2 : MeasureTheory.IntegrableOn (fun z => F' z * H' z) (Set.Ioi (0 : ℝ)))
    (h3 : MeasureTheory.IntegrableOn (fun z => F'' z * H z) (Set.Ioi (0 : ℝ)))
    (h4 : MeasureTheory.IntegrableOn (fun z => G z * H' z) (Set.Ioi (0 : ℝ)))
    (h5 : MeasureTheory.IntegrableOn (fun z => G' z * H z) (Set.Ioi (0 : ℝ)))
    (hb1 : Filter.Tendsto (fun z => F z * H' z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb2 : Filter.Tendsto (fun z => F z * H' z) Filter.atTop (nhds 0))
    (hb3 : Filter.Tendsto (fun z => F' z * H z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb4 : Filter.Tendsto (fun z => F' z * H z) Filter.atTop (nhds 0))
    (hb5 : Filter.Tendsto (fun z => G z * H z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb6 : Filter.Tendsto (fun z => G z * H z) Filter.atTop (nhds 0)) :
    (∫ z in Set.Ioi (0 : ℝ), F z * H'' z = ∫ z in Set.Ioi (0 : ℝ), F'' z * H z) ∧
      (∫ z in Set.Ioi (0 : ℝ), G z * H' z = - ∫ z in Set.Ioi (0 : ℝ), G' z * H z) := by
  -- First integration by parts: `(u, v) = (F, H')`, so that `u·v' = F·H''` and `u'·v = F'·H'`.
  have e1 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := F) (u' := F') (v := H') (v' := H'') hF hH' h1 h2 hb1 hb2
  -- Second integration by parts: `(u, v) = (F', H)`, so that `u·v' = F'·H'` and `u'·v = F''·H`.
  have e2 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := F') (u' := F'') (v := H) (v' := H') hF' hH h2 h3 hb3 hb4
  -- Third integration by parts: `(u, v) = (G, H)`, so that `u·v' = G·H'` and `u'·v = G'·H`.
  have e3 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := G) (u' := G') (v := H) (v' := H') hG hH h4 h5 hb5 hb6
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

end Work.FTS.EllipticEst
