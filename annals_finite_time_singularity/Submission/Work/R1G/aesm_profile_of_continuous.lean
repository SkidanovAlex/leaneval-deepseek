import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

open MeasureTheory

/-- **Measurability of the real power function in its base, for a fixed real exponent.**

Mathlib has `Real.continuousAt_rpow_const` (hence measurability of `x ↦ x ^ q`) only under the
side condition `0 ≤ q`, which our exponent `p / 3` does not satisfy for a general real `p`.  Here
we prove measurability for *every* real `q` by splitting at `x = 0`: on `x ≥ 0` the definition of
`Real.rpow` is `if x = 0 then (if q = 0 then 1 else 0) else exp (log x * q)`
(`Real.rpow_def_of_nonneg`), on `x < 0` it is `exp (log x * q) * cos (q * π)`
(`Real.rpow_def_of_neg`); both branches are measurable in `x`. -/
lemma measurable_real_rpow_const (q : ℝ) : Measurable (fun x : ℝ => x ^ q) := by
  have hexp : Measurable (fun x : ℝ => Real.exp (Real.log x * q)) :=
    Real.continuous_exp.measurable.comp (Real.measurable_log.mul measurable_const)
  have hmeas : Measurable (fun x : ℝ =>
      if 0 ≤ x then (if x = 0 then (if q = 0 then 1 else 0) else Real.exp (Real.log x * q))
      else Real.exp (Real.log x * q) * Real.cos (q * Real.pi)) := by
    refine Measurable.ite (measurableSet_le measurable_const measurable_id)
      (Measurable.ite (measurableSet_singleton 0) measurable_const hexp) ?_
    exact hexp.mul (Real.measurable_cos.comp (measurable_const.mul measurable_const))
  convert hmeas using 1
  funext x
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, Real.rpow_def_of_nonneg hx]
  · rw [ite_eq_right hx, Real.rpow_def_of_neg (not_le.mp hx)]

/-- **The scalar profile `x ↦ F(ρ(x)^p, θ(x))` is a.e. strongly measurable for continuous `g`.**

`profile p g z θ = if 0 ≤ θ then F_*(z,θ) + g z θ else -(F_*(z,-θ) + g z (-θ))`, an odd extension
in `θ`; all the pieces are measurable in `x`: `ρ(x)^p` through `measurable_real_rpow_const`,
`θ(x) = arctan(x₃/r)` from the measurable coordinate functions, `Γ(θ) = (sinθ cos²θ)^{p/3}` and
`F_*(z) = 2z/(1+z)²` by composition with continuous functions, and `g(ρ^p, θ)` because
`(z,θ) ↦ g z θ` is continuous (hence measurable) and `x ↦ (ρ(x)^p, θ(x))` is measurable.  No
continuity of the composite is needed, which matters because `profile` is *not* continuous across
the plane `θ = 0` when `g(z,0) ≠ 0`. -/
theorem aesm_profile_of_continuous {p : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Continuous (Function.uncurry g)) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : Work.ConstructionInstance.R3 =>
        Work.ConstructionInstance.profile p g (Work.Cyl.Rc p x) (Work.Cyl.theta x))
      MeasureTheory.volume := by
  have hgmeas : Measurable (Function.uncurry g) := hg.measurable
  have hGam : Measurable (fun θ : ℝ => Work.Spaces.Gam p θ) :=
    (measurable_real_rpow_const (p / 3)).comp
      (by show Measurable fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2; fun_prop)
  have hFstarm : Measurable (fun z : ℝ => Work.FM.Fstar z) := by
    show Measurable fun z : ℝ => 2 * z / (1 + z) ^ 2
    fun_prop
  have hrho : Measurable (fun x : Work.ConstructionInstance.R3 => Work.Cyl.rho x) := by
    show Measurable fun x : Work.ConstructionInstance.R3 =>
      Real.sqrt (Work.Cyl.radSq x + Work.Cyl.axial x ^ 2)
    refine Continuous.measurable ?_
    have h1 : Continuous fun x : Work.ConstructionInstance.R3 => Work.Cyl.radSq x := by
      show Continuous fun x : Work.ConstructionInstance.R3 => x 0 ^ 2 + x 1 ^ 2
      fun_prop
    have h2 : Continuous fun x : Work.ConstructionInstance.R3 => Work.Cyl.axial x ^ 2 := by
      show Continuous fun x : Work.ConstructionInstance.R3 => x 2 ^ 2
      fun_prop
    exact (h1.add h2).sqrt
  have hRc : Measurable (fun x : Work.ConstructionInstance.R3 => Work.Cyl.Rc p x) :=
    (measurable_real_rpow_const p).comp hrho
  have htheta : Measurable (fun x : Work.ConstructionInstance.R3 => Work.Cyl.theta x) := by
    show Measurable fun x : Work.ConstructionInstance.R3 =>
      Real.arctan (Work.Cyl.axial x / Work.Cyl.radial x)
    have hax : Measurable fun x : Work.ConstructionInstance.R3 => Work.Cyl.axial x := by
      show Measurable fun x : Work.ConstructionInstance.R3 => x 2
      fun_prop
    have hr : Measurable fun x : Work.ConstructionInstance.R3 => Work.Cyl.radial x := by
      show Measurable fun x : Work.ConstructionInstance.R3 => Real.sqrt (Work.Cyl.radSq x)
      have : Continuous fun x : Work.ConstructionInstance.R3 => Work.Cyl.radSq x := by
        show Continuous fun x : Work.ConstructionInstance.R3 => x 0 ^ 2 + x 1 ^ 2
        fun_prop
      exact this.measurable.sqrt
    exact Real.continuous_arctan.measurable.comp (hax.div hr)
  have hgcomp : Measurable (fun x : Work.ConstructionInstance.R3 =>
      g (Work.Cyl.Rc p x) (Work.Cyl.theta x)) := by
    have h := hgmeas.comp (hRc.prodMk htheta)
    convert h using 1
    funext x
    exact Function.uncurry_apply_pair g (Work.Cyl.Rc p x) (Work.Cyl.theta x)
  have hgnegcomp : Measurable (fun x : Work.ConstructionInstance.R3 =>
      g (Work.Cyl.Rc p x) (-(Work.Cyl.theta x))) := by
    have h := hgmeas.comp (hRc.prodMk htheta.neg)
    convert h using 1
    funext x
    exact Function.uncurry_apply_pair g (Work.Cyl.Rc p x) (-(Work.Cyl.theta x))
  have hFstar : Measurable (fun x : Work.ConstructionInstance.R3 =>
      Work.Construction.Fstar p (Work.Cyl.Rc p x) (Work.Cyl.theta x)) := by
    show Measurable fun x : Work.ConstructionInstance.R3 =>
      p * (Work.Spaces.Gam p (Work.Cyl.theta x) / Work.Spaces.c p)
        * Work.FM.Fstar (Work.Cyl.Rc p x)
    have h1 : Measurable (fun x : Work.ConstructionInstance.R3 =>
        Work.Spaces.Gam p (Work.Cyl.theta x)) :=
      hGam.comp htheta
    have h2 : Measurable (fun x : Work.ConstructionInstance.R3 =>
        Work.FM.Fstar (Work.Cyl.Rc p x)) :=
      hFstarm.comp hRc
    fun_prop
  have hFstar_neg : Measurable (fun x : Work.ConstructionInstance.R3 =>
      Work.Construction.Fstar p (Work.Cyl.Rc p x) (-(Work.Cyl.theta x))) := by
    show Measurable fun x : Work.ConstructionInstance.R3 =>
      p * (Work.Spaces.Gam p (-(Work.Cyl.theta x)) / Work.Spaces.c p)
        * Work.FM.Fstar (Work.Cyl.Rc p x)
    have h1 : Measurable (fun x : Work.ConstructionInstance.R3 =>
        Work.Spaces.Gam p (-(Work.Cyl.theta x))) :=
      hGam.comp htheta.neg
    have h2 : Measurable (fun x : Work.ConstructionInstance.R3 =>
        Work.FM.Fstar (Work.Cyl.Rc p x)) :=
      hFstarm.comp hRc
    fun_prop
  have hite : Measurable (fun x : Work.ConstructionInstance.R3 =>
      if 0 ≤ Work.Cyl.theta x then
        Work.Construction.Fstar p (Work.Cyl.Rc p x) (Work.Cyl.theta x)
          + g (Work.Cyl.Rc p x) (Work.Cyl.theta x)
      else
        -(Work.Construction.Fstar p (Work.Cyl.Rc p x) (-(Work.Cyl.theta x))
          + g (Work.Cyl.Rc p x) (-(Work.Cyl.theta x)))) :=
    Measurable.ite (measurableSet_le measurable_const htheta) (hFstar.add hgcomp)
      (hFstar_neg.add hgnegcomp).neg
  have hEq : (fun x : Work.ConstructionInstance.R3 =>
        Work.ConstructionInstance.profile p g (Work.Cyl.Rc p x) (Work.Cyl.theta x))
      = (fun x : Work.ConstructionInstance.R3 =>
      if 0 ≤ Work.Cyl.theta x then
        Work.Construction.Fstar p (Work.Cyl.Rc p x) (Work.Cyl.theta x)
          + g (Work.Cyl.Rc p x) (Work.Cyl.theta x)
      else
        -(Work.Construction.Fstar p (Work.Cyl.Rc p x) (-(Work.Cyl.theta x))
          + g (Work.Cyl.Rc p x) (-(Work.Cyl.theta x)))) := by
    funext x
    rcases le_or_gt 0 (Work.Cyl.theta x) with h | h
    · rw [Work.ConstructionInstance.profile_of_nonneg h, ite_eq_left h]
    · rw [Work.ConstructionInstance.profile_of_neg (not_le.mpr h), ite_eq_right (not_le.mpr h)]
  rw [hEq]
  exact hite.aestronglyMeasurable

end Work.R1G
