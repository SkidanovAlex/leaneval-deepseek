import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The right half `(π/4, π/2]` -/

/-- **The weighted Hardy inequality on the right half.**  Obtained from
`hardy_half_left_open` by the mirror `u ↦ f(π/2 - u)`. -/
theorem hardy_half_right_open {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
      (Set.Ioc (Real.pi / 4) (Real.pi / 2))) :
    IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        (Set.Ioc (Real.pi / 4) (Real.pi / 2)) ∧
      (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hqpos : (0 : ℝ) < Real.pi / 4 := by linarith
  have hqlt : Real.pi / 4 < Real.pi / 2 := by linarith
  have hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (deriv f θ) θ :=
    fun θ hθ => hasDerivAt_of_contDiffOn_one hsm hθ
  -- the mirror
  have hg_sm : ContDiffOn ℝ 1 (fun u : ℝ => f (Real.pi / 2 - u)) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_mirror_open hsm
  have hmir : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun u : ℝ => f (Real.pi / 2 - u)) u = -deriv f (Real.pi / 2 - u) :=
    Work.FTS.H2.Transport3Aux.deriv_mirror_weak hder
  -- integrability of the mirrored derivative integrand
  have hint_g : IntegrableOn
      (fun u : ℝ => (deriv (fun u : ℝ => f (Real.pi / 2 - u)) u) ^ 2
        * (Real.sin (2 * u)) ^ (1 - β)) (Set.Ioc (0 : ℝ) (Real.pi / 4)) := by
    have hIoo : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).mp hint
    have href := (Work.FTS.EllSol.VthAux.traceAux.reflectIntegrableOn_iff
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) hqpos)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring] at href
    have h1 : IntegrableOn
        (fun u : ℝ => (deriv f (Real.pi / 2 - u)) ^ 2
          * (Real.sin (2 * (Real.pi / 2 - u))) ^ (1 - β)) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      href.mp hIoo
    have h2 : IntegrableOn
        (fun u : ℝ => (deriv f (Real.pi / 2 - u)) ^ 2
          * (Real.sin (2 * u)) ^ (1 - β)) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      h1.congr_fun (fun u _ => by
        show deriv f (Real.pi / 2 - u) ^ 2 * Real.sin (2 * (Real.pi / 2 - u)) ^ (1 - β)
          = deriv f (Real.pi / 2 - u) ^ 2 * Real.sin (2 * u) ^ (1 - β)
        rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u from by ring, Real.sin_pi_sub])
        measurableSet_Ioo
    have h3 : IntegrableOn
        (fun u : ℝ => (deriv (fun u : ℝ => f (Real.pi / 2 - u)) u) ^ 2
          * (Real.sin (2 * u)) ^ (1 - β)) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      h2.congr_fun (fun u hu => by
        have hu' : u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hu.1, lt_trans hu.2 hqlt⟩
        have hd : deriv (fun u : ℝ => f (Real.pi / 2 - u)) u = -deriv f (Real.pi / 2 - u) :=
          hmir u hu'
        rw [hd]; ring) measurableSet_Ioo
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr h3
  -- apply the left half to the mirror
  have hL := hardy_half_left_open (β := β) hβ hβ1 hg_sm hint_g
  -- the mirror identities
  have e1 : (∫ u in Set.Ioc (0 : ℝ) (Real.pi / 4),
        (f (Real.pi / 2 - u)) ^ 2 * (Real.sin (2 * u)) ^ (β - 1))
      = ∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
          (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1) := by
    rw [← intervalIntegral.integral_of_le hqpos.le, ← intervalIntegral.integral_of_le hqlt.le]
    exact Work.FTS.H2.Transport3Aux.mirror_sq_sin_rpow (β - 1) f
  have e2 : (∫ u in Set.Ioc (0 : ℝ) (Real.pi / 4),
        (deriv (fun u : ℝ => f (Real.pi / 2 - u)) u) ^ 2 * (Real.sin (2 * u)) ^ (1 - β))
      = ∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) := by
    rw [← intervalIntegral.integral_of_le hqpos.le, ← intervalIntegral.integral_of_le hqlt.le]
    exact Work.FTS.H2.Transport3Aux.mirror_deriv_sq_integral_weak (β := β) hder
  have e3 : (f (Real.pi / 2 - Real.pi / 4)) ^ 2 = (f (Real.pi / 4)) ^ 2 := by
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring]
  constructor
  · -- integrability of the right-hand integrand
    have hIoo : IntegrableOn
        (fun u : ℝ => (f (Real.pi / 2 - u)) ^ 2 * (Real.sin (2 * u)) ^ (β - 1))
        (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).mp hL.1
    have href := (Work.FTS.EllSol.VthAux.traceAux.reflectIntegrableOn_iff
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1)) hqpos)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring] at href
    have h2 : IntegrableOn
        (fun u : ℝ => (f (Real.pi / 2 - u)) ^ 2 * (Real.sin (2 * (Real.pi / 2 - u))) ^ (β - 1))
        (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      hIoo.congr_fun (fun u _ => by
        show (f (Real.pi / 2 - u)) ^ 2 * Real.sin (2 * u) ^ (β - 1)
          = (f (Real.pi / 2 - u)) ^ 2 * Real.sin (2 * (Real.pi / 2 - u)) ^ (β - 1)
        rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u from by ring, Real.sin_pi_sub])
        measurableSet_Ioo
    have h3 : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := href.mpr h2
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr h3
  · have hmain := hL.2
    rw [e1, e2, e3] at hmain
    exact hmain

end

end Work.FTS.StrongPersist.N6Trans.SixRoute
