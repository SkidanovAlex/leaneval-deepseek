import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.pdAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Adjointness of `g ↦ m · ∂_a g` for the real `L²` pairing on the torus

For a `1`-periodic smooth *real* coefficient `m` and `1`-periodic smooth complex functions
`f, g` on the flat torus `(ι → ℝ)`, the first-order operator `f ↦ m · ∂_a f` is skew-adjoint for
the real `L²` pairing `L2re`:

`L2re (m · ∂_a f) g = - L2re f (∂_a (m · g))`.

The proof is the periodic integration by parts on the cube.  With `M := ↑m`,
`A := fun y => M y * f y * star (g y)`, the Leibniz rule plus `pd a (star ∘ g) = star ∘ pd a g`
give the pointwise identity

`(M x * ∂_a f x) * star (g x) + f x * star (∂_a (M · g) x) = ∂_a A x`,

and `∫_{cube} ∂_a A = 0` because `A` is `C¹` and periodic in the coordinate `a`
(`Work.Diff.STE.integral_pd_unitCube_zero`).  Taking real parts gives the claim.

The statement is proved in the general form `L2re_pd_adjoint_of_real`, which only asks the
coefficient `M` to be `C¹`, periodic, and *real* (`star (M x) = M x`), with a real partial
derivative (`star (∂_a M x) = ∂_a M x`); the target theorem is the specialisation
`M = ↑m`.
-/

noncomputable section

namespace Work.Diff.STE.B3.VarCoef

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complexification of a smooth real function has a *real* partial derivative. -/
lemma star_pd_ofReal (m : (ι → ℝ) → ℝ) (a : ι) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (x : ι → ℝ) :
    star (Work.Diff.STE.pd a (fun y => ((m y : ℝ) : ℂ)) x)
      = Work.Diff.STE.pd a (fun y => ((m y : ℝ) : ℂ)) x := by
  have hm1 : ContDiff ℝ 1 m := hm.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [Work.Diff.STE.ga_pd_ofReal a m x (hm1.differentiable (by norm_num) x)]
  exact Complex.conj_ofReal _

/-- **Adjointness of the first-order operator `f ↦ M · ∂_a f`** for a `C¹` periodic coefficient
`M` whose values *and* whose partial derivative are real. -/
lemma L2re_pd_adjoint_of_real (M : (ι → ℝ) → ℂ) (a : ι) (f g : (ι → ℝ) → ℂ)
    (hMsm : ContDiff ℝ 1 M) (hMp : Work.Diff.STE.PeriodicIn a M)
    (hMreal : ∀ x, star (M x) = M x)
    (hMpdreal : ∀ x, star (Work.Diff.STE.pd a M x) = Work.Diff.STE.pd a M x)
    (hf : ContDiff ℝ 1 f) (hfp : Work.Diff.STE.PeriodicIn a f)
    (hg : ContDiff ℝ 1 g) (hgp : Work.Diff.STE.PeriodicIn a g) :
    Work.Diff.STE.L2re (fun x => M x * Work.Diff.STE.pd a f x) g
      = - Work.Diff.STE.L2re f (fun x => Work.Diff.STE.pd a (fun y => M y * g y) x) := by
  have hMg_sm : ContDiff ℝ 1 (fun y => M y * g y) := hMsm.mul hg
  have hstarg_sm : ContDiff ℝ 1 (fun y => star (g y)) := Work.Diff.STE.ga_contDiff_star hg
  have hH_sm : ContDiff ℝ 1 (fun y => M y * f y * star (g y)) := (hMsm.mul hf).mul hstarg_sm
  have hstarg_per : Work.Diff.STE.PeriodicIn a (fun y => star (g y)) := by
    intro x
    show star (g (x + Pi.single a 1)) = star (g x)
    rw [hgp x]
  have hH_per : Work.Diff.STE.PeriodicIn a (fun y => M y * f y * star (g y)) :=
    Work.Diff.STE.ga_periodicIn_mul a (Work.Diff.STE.ga_periodicIn_mul a hMp hfp) hstarg_per
  -- The pointwise identity: `∂_a (M · f · star g) = (M · ∂_a f) · star g + f · star (∂_a (M · g))`.
  have hpt : ∀ x : ι → ℝ,
      (M x * Work.Diff.STE.pd a f x) * star (g x)
        + f x * star (Work.Diff.STE.pd a (fun y => M y * g y) x)
        = Work.Diff.STE.pd a (fun y => M y * f y * star (g y)) x := by
    intro x
    have h1 := Work.Diff.STE.pd_mul a (hMsm.differentiable (by norm_num) x)
      (hg.differentiable (by norm_num) x)
    have h2 := Work.Diff.STE.pd_mul a (hMsm.differentiable (by norm_num) x)
      (hf.differentiable (by norm_num) x)
    have h3 : Work.Diff.STE.pd a (fun y => M y * f y * star (g y)) x
        = Work.Diff.STE.pd a (fun y => M y * f y) x * star (g x)
          + (M x * f x) * Work.Diff.STE.pd a (fun y => star (g y)) x :=
      Work.Diff.STE.pd_mul a (x := x)
        ((hMsm.differentiable (by norm_num)).mul (hf.differentiable (by norm_num)) x)
        ((Work.Diff.STE.ga_contDiff_star hg).differentiable (by norm_num) x)
    rw [h3, h2, (star_pd a g x).symm, h1]
    simp only [star_add, star_mul, hMreal x, hMpdreal x]
    ring
  -- Integrability of the two integrands on the cube.
  have hA_int : Integrable (fun x => (M x * Work.Diff.STE.pd a f x) * star (g x))
      (volume.restrict Work.Diff.STE.unitCube) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous
      ((hMsm.continuous.mul (Work.Diff.STE.continuous_pd hf a)).mul
        (continuous_star.comp hg.continuous))
  have hB_int : Integrable (fun x => f x * star (Work.Diff.STE.pd a (fun y => M y * g y) x))
      (volume.restrict Work.Diff.STE.unitCube) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous
      (hf.continuous.mul (continuous_star.comp (Work.Diff.STE.continuous_pd hMg_sm a)))
  -- The sum of the two integrals vanishes, being the integral of a periodic partial derivative.
  have hsum : (∫ x in Work.Diff.STE.unitCube, (M x * Work.Diff.STE.pd a f x) * star (g x))
      + ∫ x in Work.Diff.STE.unitCube, f x * star (Work.Diff.STE.pd a (fun y => M y * g y) x)
      = 0 := by
    rw [← integral_add hA_int hB_int]
    rw [show (fun x => (M x * Work.Diff.STE.pd a f x) * star (g x)
          + f x * star (Work.Diff.STE.pd a (fun y => M y * g y) x))
        = fun x => Work.Diff.STE.pd a (fun y => M y * f y * star (g y)) x from funext hpt]
    exact Work.Diff.STE.integral_pd_unitCube_zero a hH_sm hH_per
  have hre : (∫ x in Work.Diff.STE.unitCube, (M x * Work.Diff.STE.pd a f x) * star (g x)).re
      = - (∫ x in Work.Diff.STE.unitCube,
          f x * star (Work.Diff.STE.pd a (fun y => M y * g y) x)).re := by
    have h := congrArg Complex.re hsum
    simp only [Complex.add_re, Complex.zero_re] at h
    linarith
  rw [Work.Diff.STE.L2re, Work.Diff.STE.L2re]
  exact hre

/-- **Skew-adjointness of `f ↦ m · ∂_a f` on the torus** for a smooth `1`-periodic real
coefficient `m`. -/
theorem cm_pd_L2re_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : (ι → ℝ) → ℝ) (a : ι) (f g : (ι → ℝ) → ℂ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hmp : Work.Diff.STE.Periodic1 m)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : Work.Diff.STE.Periodic1 f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgp : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.L2re (fun x => ((m x : ℝ) : ℂ) * Work.Diff.STE.pd a f x) g
      = - Work.Diff.STE.L2re f
          (fun x => Work.Diff.STE.pd a (fun y => ((m y : ℝ) : ℂ) * g y) x) := by
  have hMsm : ContDiff ℝ 1 (fun y => ((m y : ℝ) : ℂ)) :=
    (Work.Diff.STE.ga_contDiff_ofReal hm).of_le (WithTop.coe_le_coe.mpr le_top)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  exact L2re_pd_adjoint_of_real (fun y => ((m y : ℝ) : ℂ)) a f g hMsm
    (Work.Diff.STE.ga_periodicIn_ofReal a hmp) (fun x => star_cm m x)
    (star_pd_ofReal m a hm) hf1 (hfp a) hg1 (hgp a)

end Work.Diff.STE.B3.VarCoef
