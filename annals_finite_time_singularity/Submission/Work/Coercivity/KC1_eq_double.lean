import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.C0Defs
import Submission.Work.Coercivity.C0thetaIBP
import Submission.Work.Coercivity.SmoothNbhd_pth_slice
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem KC1_eq_double (f : ℝ → ℝ → ℝ) (hs : Work.Spaces.SmoothNbhd f) :
    Work.Coercivity.CT.KC1 f = -∫ s in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Coercivity.C0g θ * Work.Spaces.Dth f s θ / (s * (1 + s)) := by
  have hD : Spaces.SmoothNbhd (Spaces.Dth f) := Spaces.SmoothNbhd.Dth hs
  have step1 : CT.KC1 f
      = ∫ s in Set.Ioi (0 : ℝ), FM.L12dens Spaces.K (Transport (Spaces.Dth f)) s := by
    rw [CT.KC1, L12f, FM.L12]
  have step2 : (∫ s in Set.Ioi (0 : ℝ), FM.L12dens Spaces.K (Transport (Spaces.Dth f)) s)
      = ∫ s in Set.Ioi (0 : ℝ),
          (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ,
            C0h θ * Spaces.pth (Spaces.Dth f) s θ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
    have hs0' : (0 : ℝ) < s := hs'
    have hs0 : s ≠ 0 := ne_of_gt hs0'
    have hs1 : (1 : ℝ) + s ≠ 0 := by
      have : (0 : ℝ) < 1 + s := by linarith
      exact ne_of_gt this
    rw [FM.L12dens]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall (fun θ => ?_))
    simp only [Transport, Spaces.Dth, C0h, Spaces.K]
    field_simp
  have step3 : (∫ s in Set.Ioi (0 : ℝ),
        (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ,
          C0h θ * Spaces.pth (Spaces.Dth f) s θ)
      = -∫ s in Set.Ioi (0 : ℝ),
          (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0g θ * Spaces.Dth f s θ := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
    obtain ⟨hgd, hgi⟩ :=
      SmoothNbhd_pth_slice (Spaces.Dth f) hD s (le_of_lt hs')
    rw [C0thetaIBP (Spaces.Dth f s) (Spaces.pth (Spaces.Dth f) s) hgd hgi]
    ring
  calc CT.KC1 f
      = ∫ s in Set.Ioi (0 : ℝ), FM.L12dens Spaces.K (Transport (Spaces.Dth f)) s := step1
    _ = ∫ s in Set.Ioi (0 : ℝ),
          (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ,
            C0h θ * Spaces.pth (Spaces.Dth f) s θ := step2
    _ = -∫ s in Set.Ioi (0 : ℝ),
          (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0g θ * Spaces.Dth f s θ := step3
    _ = -∫ s in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          C0g θ * Spaces.Dth f s θ / (s * (1 + s)) := by
        have hsw : (∫ s in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              C0g θ * Spaces.Dth f s θ / (s * (1 + s)))
            = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
                C0g θ * Spaces.Dth f s θ / (s * (1 + s)) :=
          (setIntegral_congr_set (μ := volume)
            (f := fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
              C0g θ * Spaces.Dth f s θ / (s * (1 + s)))
            (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
        rw [hsw]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
        rw [integral_div]
        ring

end Work.Coercivity
