import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

theorem energy_barrier {e e' : ℝ → ℝ} {Λ T : ℝ} (hT : 0 ≤ T) (hΛ : 0 ≤ Λ)
    (hcont : ContinuousOn e (Set.Icc 0 T))
    (hd : ∀ τ ∈ Set.Ioo 0 T, HasDerivAt e (e' τ) τ)
    (hle : ∀ τ ∈ Set.Ioo 0 T, e' τ ≤ Λ * (1 + e τ)) :
    ∀ τ ∈ Set.Icc 0 T, e τ ≤ (e 0 + 1) * Real.exp (Λ * τ) - 1 := by
  -- Grönwall: the comparison function `g x = (e x + 1) * exp (-Λ x)` is antitone on `[0,T]`.
  intro τ hτ
  let g : ℝ → ℝ := fun x => (e x + 1) * Real.exp ((-Λ) * x)
  let g' : ℝ → ℝ :=
    fun x => e' x * Real.exp ((-Λ) * x) + (e x + 1) * (Real.exp ((-Λ) * x) * (-Λ))
  have hcont_g : ContinuousOn g (Set.Icc 0 T) := by
    have h1 : ContinuousOn (fun x : ℝ => e x + 1) (Set.Icc 0 T) := hcont.add continuousOn_const
    have h2 : ContinuousOn (fun x : ℝ => Real.exp ((-Λ) * x)) (Set.Icc 0 T) :=
      Real.continuous_exp.comp_continuousOn (continuousOn_const.mul continuousOn_id)
    exact h1.mul h2
  have hg' : ∀ x ∈ interior (Set.Icc 0 T), HasDerivWithinAt g (g' x) (interior (Set.Icc 0 T)) x := by
    intro x hx
    rw [interior_Icc] at hx
    have he : HasDerivAt e (e' x) x := hd x hx
    have hexp : HasDerivAt (fun y : ℝ => Real.exp ((-Λ) * y)) (Real.exp ((-Λ) * x) * (-Λ)) x := by
      have h2 : HasDerivAt (fun y : ℝ => (-Λ) * y) (-Λ) x := by
        simpa using ((hasDerivAt_id x).const_mul (-Λ))
      simpa using h2.exp
    exact ((he.add_const 1).mul hexp).hasDerivWithinAt
  have hg'0 : ∀ x ∈ interior (Set.Icc 0 T), g' x ≤ 0 := by
    intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Set.Ioo 0 T := hx
    have hb : e' x - Λ * (e x + 1) ≤ 0 := by
      have h := hle x hx'
      nlinarith
    have hval : g' x = Real.exp ((-Λ) * x) * (e' x - Λ * (e x + 1)) := by
      simp only [g']
      ring
    rw [hval]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hb
  have hanti : AntitoneOn g (Set.Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hcont_g hg' hg'0
  have h := hanti (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_refl 0, hT⟩) hτ hτ.1
  have hg0 : g 0 = e 0 + 1 := by simp [g]
  have key : (e τ + 1) * Real.exp ((-Λ) * τ) ≤ e 0 + 1 := by rwa [hg0] at h
  have key2 : e τ + 1 ≤ (e 0 + 1) * Real.exp (Λ * τ) := by
    calc e τ + 1 = (e τ + 1) * Real.exp ((-Λ) * τ) * Real.exp (Λ * τ) := by
          rw [mul_assoc, ← Real.exp_add]
          norm_num
      _ ≤ (e 0 + 1) * Real.exp (Λ * τ) :=
          mul_le_mul_of_nonneg_right key (le_of_lt (Real.exp_pos _))
  linarith

end Work.FTS.StrongEps.EpsE4Thr
