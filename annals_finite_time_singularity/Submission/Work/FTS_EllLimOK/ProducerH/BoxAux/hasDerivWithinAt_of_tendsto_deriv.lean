import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

theorem hasDerivWithinAt_of_tendsto_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hL : ∃ L : ℝ, Filter.Tendsto f' (nhdsWithin a (Set.Ioi a)) (nhds L))
    (hR : ∃ R : ℝ, Filter.Tendsto f' (nhdsWithin b (Set.Iio b)) (nhds R)) :
    HasDerivWithinAt f (derivWithin f (Set.Icc a b) a) (Set.Icc a b) a ∧
      HasDerivWithinAt f (derivWithin f (Set.Icc a b) b) (Set.Icc a b) b := by
  obtain ⟨L, hL⟩ := hL
  obtain ⟨R, hR⟩ := hR
  have hab' : a ≤ b := hab.le
  -- `(a, b)` is a right-neighbourhood of `a` and a left-neighbourhood of `b`
  have hmemA : Set.Ioo a b ∈ nhdsWithin a (Set.Ioi a) := Ioo_mem_nhdsGT hab
  have hmemB : Set.Ioo a b ∈ nhdsWithin b (Set.Iio b) := Ioo_mem_nhdsLT hab
  -- `f` is differentiable on `(a, b)` and continuous at both endpoints within `(a, b)`
  have hdiff : DifferentiableOn ℝ f (Set.Ioo a b) := fun x hx =>
    (hd x hx).differentiableAt.differentiableWithinAt
  have hcontA : ContinuousWithinAt f (Set.Ioo a b) a :=
    (hcont.continuousWithinAt (Set.left_mem_Icc.mpr hab')).mono Set.Ioo_subset_Icc_self
  have hcontB : ContinuousWithinAt f (Set.Ioo a b) b :=
    (hcont.continuousWithinAt (Set.right_mem_Icc.mpr hab')).mono Set.Ioo_subset_Icc_self
  -- the derivative function agrees with `f'` near the endpoints, so it has the same limits
  have hderivA : Filter.Tendsto (fun x => deriv f x) (nhdsWithin a (Set.Ioi a)) (nhds L) :=
    hL.congr' (Filter.eventually_of_mem hmemA fun x hx => (hd x hx).deriv.symm)
  have hderivB : Filter.Tendsto (fun x => deriv f x) (nhdsWithin b (Set.Iio b)) (nhds R) :=
    hR.congr' (Filter.eventually_of_mem hmemB fun x hx => (hd x hx).deriv.symm)
  -- extension of differentiability to the endpoints
  have hA : HasDerivWithinAt f L (Set.Icc a b) a :=
    (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcontA hmemA hderivA).mono
      (fun x hx => hx.1)
  have hB : HasDerivWithinAt f R (Set.Icc a b) b :=
    (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcontB hmemB hderivB).mono
      (fun x hx => hx.2)
  exact ⟨hA.differentiableWithinAt.hasDerivWithinAt,
    hB.differentiableWithinAt.hasDerivWithinAt⟩

end Work.FTS_EllLimOK.ProducerH.BoxAux
