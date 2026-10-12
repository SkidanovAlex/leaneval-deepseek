import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity in `p` of the `i`-th raw slot mode form

`rawSlotAmp s p Ψ i x = ∫_z χ(z)e^{−i⟪p,z⟫}Ψ(x_{i←z})dz` is the windowed `p`-mode of the
`i`-th fibre of `Ψ`.  We prove the joint continuity of `(p,x) ↦ rawSlotAmp s p Ψ i x`
(the integrand over the compact `acube s` depends continuously on the parameters) and
deduce that `p ↦ ∫_{abox N s} ‖rawSlotAmp s p Ψ i x‖²` is continuous, by a second
parametric integral over the compact box `abox N s`.
-/

namespace Work.SmallBoxBridge.Fourier

open MeasureTheory Metric
open scoped Topology Real BigOperators
open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Joint continuity of the raw slot amplitude** `(p,x) ↦ rawSlotAmp s p Ψ i x`
(for continuous `Ψ`). -/
theorem continuous_rawSlotAmp_pair {N : ℕ} {s : ℝ} (hs : 0 < s) {Ψ : X N → ℝ}
    (hΨ : Continuous Ψ) (i : Fin N) :
    Continuous (fun q : ℝ³ × X N => rawSlotAmp s q.1 Ψ i q.2) := by
  rw [show (fun q : ℝ³ × X N => rawSlotAmp s q.1 Ψ i q.2)
      = fun q => ∫ z in acube s, (chiScale s z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
          (Ψ (Function.update q.2 i z) : ℂ) from by
    funext q; simp only [rawSlotAmp]]
  refine continuous_parametric_integral_of_continuous
    (f := fun (q : ℝ³ × X N) (z : ℝ³) => (chiScale s z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
          (Ψ (Function.update q.2 i z) : ℂ)) ?_ (acube_compact hs)
  rw [show Function.uncurry (fun (q : ℝ³ × X N) (z : ℝ³) => (chiScale s z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
          (Ψ (Function.update q.2 i z) : ℂ))
      = fun r : (ℝ³ × X N) × ℝ³ => (chiScale s r.2 : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ r.1.1 r.2 : ℂ))) *
          (Ψ (Function.update r.1.2 i r.2) : ℂ) from rfl]
  have hχ : Continuous (fun r : (ℝ³ × X N) × ℝ³ => (chiScale s r.2 : ℂ)) :=
    Complex.continuous_ofReal.comp ((chiScale_continuous s).comp continuous_snd)
  have hexp : Continuous (fun r : (ℝ³ × X N) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ r.1.1 r.2 : ℂ)))) :=
    Complex.continuous_exp.comp (Continuous.neg (Continuous.mul continuous_const
      (Complex.continuous_ofReal.comp (continuous_inner.comp
        (continuous_fst.fst.prodMk continuous_snd)))))
  have hΨ' : Continuous (fun r : (ℝ³ × X N) × ℝ³ =>
      (Ψ (Function.update r.1.2 i r.2) : ℂ)) :=
    Complex.continuous_ofReal.comp (hΨ.comp ((continuous_fst.snd).update i continuous_snd))
  exact (hχ.mul hexp).mul hΨ'

/-- **Continuity in `p` of the `i`-th raw slot mode form** `p ↦ ∫_x ‖rawSlotAmp s p Ψ i x‖²`. -/
theorem continuous_integral_rawSlotAmp_sq {N : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΨ : Continuous Ψ) (i : Fin N) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      ∫ x in Submission.BoseGases.abox N s,
        ‖Submission.BoseGases.rawSlotAmp s p Ψ i x‖ ^ 2) := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (p : ℝ³) (x : X N) => ‖rawSlotAmp s p Ψ i x‖ ^ 2) ?_ (abox_compact N hs)
  rw [show Function.uncurry (fun (p : ℝ³) (x : X N) => ‖rawSlotAmp s p Ψ i x‖ ^ 2)
      = fun r : ℝ³ × X N => ‖rawSlotAmp s r.1 Ψ i r.2‖ ^ 2 from rfl]
  exact (continuous_norm.comp (continuous_rawSlotAmp_pair hs hΨ i)).pow 2

end Work.SmallBoxBridge.Fourier
