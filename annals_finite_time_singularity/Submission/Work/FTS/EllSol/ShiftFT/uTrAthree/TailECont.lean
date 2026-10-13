/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# Continuity of the tail integral `tailE`

The consumer (`Work.FTS.EllSol.ShiftFT.uTr_niceFlat`, and the `Gc`/`uTr` calculus) needs the
*mere* continuity (not the `C²` regularity) of the parametric interval integral

`(t, θ) ↦ ∫ s in t..c, g s θ`

for an integrand `g` known to be continuous only on `Set.univ ×ˢ V` — the weaker hypothesis
that appears when the datum is only known to be continuous up to the boundary in `t`.

The general statement is proved for an arbitrary `V : Set ℝ` and arbitrary upper endpoint `c`
(`continuousOn_intervalIntegral_param`); the requested lemma `TailECont` is the instance

`g s θ = exp (-(b*s)) * deriv (chi N) s * f s θ`,  `c = 2*N`,

with the elementary prefactor `exp (b*t)`.

The proof is a reduction to Mathlib's parametric primitive
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`: pull the interval
`∫ s in t..c` back to an integral with the *varying upper* endpoint via
`intervalIntegral.integral_symm`, restrict the parameter space to the subtype
`↥(Set.univ ×ˢ V)` (on which the integrand is genuinely continuous, by
`ContinuousOn.comp_continuous`), and finally compose with `exp (b * ·)`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.ShiftFT.uTrAthree.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAthree

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-- **Parametric continuity of an interval integral with a variable lower endpoint**, for an
integrand which is only known to be continuous on `Set.univ ×ˢ V`. -/
theorem continuousOn_intervalIntegral_param {g : ℝ → ℝ → ℝ} (V : Set ℝ) (C : ℝ)
    (hg : ContinuousOn (Function.uncurry g) (Set.univ ×ˢ V)) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ s in p.1..C, g s p.2) (Set.univ ×ˢ V) := by
  let S : Set (ℝ × ℝ) := Set.univ ×ˢ V
  have hint : Continuous (Function.uncurry (fun (x : ↥S) (s : ℝ) => g s x.1.2)) := by
    have hphi : Continuous (fun p : ↥S × ℝ => (p.2, p.1.1.2)) := by fun_prop
    exact hg.comp_continuous hphi (fun p => ⟨trivial, p.1.2.2⟩)
  have hbase : Continuous (fun x : ↥S => ∫ s in C..x.1.1, g s x.1.2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hint (by fun_prop)
  have hmain : Continuous (fun x : ↥S => ∫ s in x.1.1..C, g s x.1.2) := by
    refine hbase.neg.congr (fun x => ?_)
    simp only [Pi.neg_apply]
    rw [intervalIntegral.integral_symm x.1.1 C, neg_neg]
  rw [continuousOn_iff_continuous_domRestrict]
  exact hmain

/-- **Continuity of the tail integral `tailE`.**  `tailE N b f t θ` is the product of the
elementary prefactor `exp (b*t)` with a parametric interval integral; both factors are
continuous on `Set.univ ×ˢ Set.Ioo 0 (π/2)` as soon as the `θ`-dependent integrand is. -/
theorem TailECont (f : ℝ → ℝ → ℝ) (N b : ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.ShiftFT.uTrAthree.tailE N b f p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hchi : Continuous (deriv (Work.FTS.EllSol.Trunc.chi N)) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous_deriv (by norm_num)
  have hlin : Continuous (fun q : ℝ × ℝ => -(b * q.1)) := by fun_prop
  have hA : ContinuousOn (fun q : ℝ × ℝ =>
      Real.exp (-(b * q.1)) * deriv (Work.FTS.EllSol.Trunc.chi N) q.1)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_exp.comp hlin).mul (hchi.comp continuous_fst)).continuousOn
  have hg := hA.mul hf
  have hmain : ContinuousOn (fun p : ℝ × ℝ => ∫ s in p.1..(2 * N),
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * f s p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_intervalIntegral_param (Set.Ioo 0 (Real.pi / 2)) (2 * N)
      (g := fun s θ => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * f s θ) hg
  have hexp : ContinuousOn (fun p : ℝ × ℝ => Real.exp (b * p.1))
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_exp.comp (by fun_prop)).continuousOn
  exact hexp.mul hmain

end

end Work.FTS.EllSol.ShiftFT.uTrAthree
