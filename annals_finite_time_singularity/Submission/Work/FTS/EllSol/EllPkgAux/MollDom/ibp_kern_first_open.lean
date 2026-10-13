import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollAux0
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.ibp_kern_first

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- The "open" (trace-class) version of `ibp_kern_first`: the derivative `H` of the slice `G`
is only assumed *interval integrable* (`H` need not be continuous, and no a.e. identification
with `deriv G` is used).  The integration by parts is carried out directly on `0..π/2` with the
given `H`, exactly as in `ibp_first_pi`. -/
theorem ibp_kern_first_open {ρ ρ' G H : ℝ → ℝ} {θ : ℝ}
    (hρ : ∀ t : ℝ, HasDerivAt ρ (ρ' t) t) (hρ'c : Continuous ρ')
    (hGc : ContinuousOn G Work.Spaces.Iθ)
    (hHG : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt G (H x) x)
    (hG0 : G 0 = 0) (hGp : G (Real.pi / 2) = 0)
    (hHint : IntervalIntegrable H MeasureTheory.volume 0 (Real.pi / 2)) :
    (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern ρ' θ s * G s)
      = ∫ s in Work.Spaces.Iθ,
          (ρ (θ - s) + ρ (θ + s) + ρ (θ + s - Real.pi)) * H s := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- `ρ` is continuous, being differentiable everywhere
  have hρc : Continuous ρ := continuous_iff_continuousAt.mpr fun t => (hρ t).continuousAt
  -- the primitive of `Kern ρ' θ` in the `s` variable
  set ψ : ℝ → ℝ := fun s => -(ρ (θ - s) + ρ (θ + s) + ρ (θ + s - Real.pi)) with hψ
  have hψc : Continuous ψ := by
    rw [hψ]
    exact (((hρc.comp (continuous_const.sub continuous_id)).add
      (hρc.comp (continuous_const.add continuous_id))).add
      (hρc.comp ((continuous_const.add continuous_id).sub continuous_const))).neg
  have hKc : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern ρ' θ s) := by
    have h1 : Continuous (fun s : ℝ => ρ' (θ - s)) :=
      hρ'c.comp (continuous_const.sub continuous_id)
    have h2 : Continuous (fun s : ℝ => ρ' (θ + s)) :=
      hρ'c.comp (continuous_const.add continuous_id)
    have h3 : Continuous (fun s : ℝ => ρ' (θ + s - Real.pi)) :=
      hρ'c.comp ((continuous_const.add continuous_id).sub continuous_const)
    exact (h1.sub h2).sub h3
  -- `∂_s ψ = Kern ρ' θ` on the open interval
  have hψ_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt ψ (Work.FTS.EllSol.EllPkgAux.Kern ρ' θ x) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => ρ (θ - s)) (-(ρ' (θ - x))) x :=
      HasDerivAt.comp_const_sub θ x (hρ (θ - x))
    have h2 : HasDerivAt (fun s : ℝ => ρ (θ + s)) (ρ' (θ + x)) x :=
      HasDerivAt.comp_const_add θ x (hρ (θ + x))
    have h3 : HasDerivAt (fun s : ℝ => ρ (θ + s - Real.pi)) (ρ' (θ + x - Real.pi)) x := by
      have h := HasDerivAt.comp_const_add (θ - Real.pi) x (hρ ((θ - Real.pi) + x))
      have hfun : (fun s : ℝ => ρ ((θ - Real.pi) + s))
          = fun s : ℝ => ρ (θ + s - Real.pi) := by
        funext s; rw [show (θ - Real.pi) + s = θ + s - Real.pi by ring]
      have hval : ρ' ((θ - Real.pi) + x) = ρ' (θ + x - Real.pi) := by
        rw [show (θ - Real.pi) + x = θ + x - Real.pi by ring]
      rw [hfun, hval] at h
      exact h
    have hd := ((h1.add h2).add h3).neg
    rw [hψ]
    convert hd using 1
    rw [Work.FTS.EllSol.EllPkgAux.Kern]
    ring
  have hIb := Work.FTS.EllSol.EllPkgAux.ibp_first_pi
    (u := ψ) (u' := fun s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern ρ' θ s) (g := G) (h := H)
    hψc.continuousOn hGc hψ_deriv hHG (hKc.intervalIntegrable 0 (Real.pi / 2)) hHint
  -- both sides as interval integrals over `0..π/2`
  rw [Work.FTS.EllSol.EllPkgAux.setIntegral_Iθ_eq_interval,
    Work.FTS.EllSol.EllPkgAux.setIntegral_Iθ_eq_interval]
  -- the boundary terms vanish by `G 0 = G (π/2) = 0`
  have hkey : (∫ x in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllSol.EllPkgAux.Kern ρ' θ x * G x)
      = -∫ x in (0 : ℝ)..(Real.pi / 2), ψ x * H x := by
    have h := hIb
    rw [hGp, hG0] at h
    have h' : (∫ x in (0 : ℝ)..(Real.pi / 2), ψ x * H x)
        = -∫ x in (0 : ℝ)..(Real.pi / 2),
            Work.FTS.EllSol.EllPkgAux.Kern ρ' θ x * G x := by
      simpa using h
    linarith
  rw [hkey, ← intervalIntegral.integral_neg]
  have hpt : ∀ x : ℝ, -(ψ x * H x)
      = (ρ (θ - x) + ρ (θ + x) + ρ (θ + x - Real.pi)) * H x := by
    intro x
    simp only [hψ]
    ring
  exact intervalIntegral.integral_congr (fun x _ => hpt x)

end Work.FTS.EllSol.EllPkgAux.MollDom
