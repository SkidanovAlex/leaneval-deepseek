import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6.sliceAng_le6
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.SlotJets

/-- **Weighted angular `L²` bound for the `∂_θ` of a mixed slot, uniformly in `z`.**

For `0 < α ≤ 1`, `f` of class `SmoothOpen` (i.e. `C^∞` on the open quadrant
`(0,∞) × (0,π/2)`) with `HkMem α 6 f`, and `a + b ≤ 4`, the angular slice of
`∂_θ (D_z^b D_θ^a f)` at a radius `z > 0`, weighted by `sin(2θ)^{2-γ}` (`γ = gam α`),
has an integral bounded by a universal multiple of `HkSq α 6 f` — with a constant
independent of `z`.

Route: on `(0, π/2)` the identity `sin(2θ)·∂_θ(mixed b a f) = mixed b (a+1) f` holds
(from `Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open` for `D_θ` and
`D_z^b`), so the integrand equals `(mixed b (a+1) f)²·sin(2θ)^{-γ}`; the bound is then
`Work.FTS.StrongPersist.N6.sliceAng_le6` applied to the slot `(b, a+1)` (which satisfies
`1 ≤ a+1` and `a+1+b ≤ 5`), together with the a.e. agreement of `Set.Ioo 0 (π/2)` and
`Work.Spaces.Iθ` (`Ioo_ae_eq_Icc`). -/
theorem slotPthSliceLe : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    a + b ≤ 4 → ∀ z : ℝ, 0 < z →
      ∫ θ in Set.Ioo (0:ℝ) (π/2),
          (Work.Spaces.pth (Work.Spaces.mixed b a f) z θ)^2
            * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
        ≤ C * Work.Spaces.HkSq α 6 f := by
  -- the constant of the order-6 angular slot bound
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.StrongPersist.N6.sliceAng_le6
  refine ⟨C₀, hC₀pos, ?_⟩
  intro α f b a hα hα1 hF hmem hab z hz
  -- on `(0,π/2)`, `sin(2θ)·∂_θ(mixed b a f) = mixed b (a+1) f`, so the `sin(2θ)²` hidden in the
  -- weight `sin(2θ)^{2-γ}` exactly cancels the one produced by `∂_θ = sin(2θ)^{-1}·D_θ`
  have hkey : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
      (Work.Spaces.pth (Work.Spaces.mixed b a f) z θ)^2
          * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
        = (Work.Spaces.mixed b (a+1) f z θ)^2
          * (Real.sin (2*θ))^(-(Work.Spaces.gam α)) := by
    intro θ hθ
    have hsinpos : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hid : Real.sin (2*θ) * Work.Spaces.pth (Work.Spaces.mixed b a f) z θ
        = Work.Spaces.mixed b (a+1) f z θ :=
      Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open
        (f := Work.Spaces.DthIter a f) (fun n => (hF.DthIter a).forall n) b 1 hz hθ
    have hpow : (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
        = (Real.sin (2*θ))^(2:ℝ) * (Real.sin (2*θ))^(-(Work.Spaces.gam α)) := by
      rw [show (2:ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring]
      exact Real.rpow_add hsinpos 2 (-(Work.Spaces.gam α))
    have hs2 : (Real.sin (2*θ))^(2:ℝ) = (Real.sin (2*θ))^2 := by
      simpa using Real.rpow_natCast (Real.sin (2*θ)) 2
    rw [hpow, hs2, ← hid]
    ring
  calc ∫ θ in Set.Ioo (0:ℝ) (π/2),
        (Work.Spaces.pth (Work.Spaces.mixed b a f) z θ)^2
          * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
      = ∫ θ in Set.Ioo (0:ℝ) (π/2),
        (Work.Spaces.mixed b (a+1) f z θ)^2
          * (Real.sin (2*θ))^(-(Work.Spaces.gam α)) :=
        setIntegral_congr_fun measurableSet_Ioo hkey
    _ = ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b (a+1) f z θ)^2
          * (Real.sin (2*θ))^(-(Work.Spaces.gam α)) := by
        rw [Work.Spaces.Iθ]
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ))
            (b := Real.pi / 2))
    _ ≤ C₀ * Work.Spaces.HkSq α 6 f :=
        hC₀ α f b (a+1) hα hα1 hF hmem (by omega) (by omega) z hz

end Work.FTS_EllLimOK.SlotJets
