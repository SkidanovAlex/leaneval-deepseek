import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.EllipticEst.Prop.MixedSlotAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The fundamental-theorem-of-calculus identity along the mollifier path

`Work.FTS.StrongEps.DiffAux.shiftPath_sub`: for a profile `g` of class `C^∞` on the open quadrant,

`g (zShift z p₁) (thShift θ p₂) - g z θ
   = ∫₀¹ -(p₁ · D_z g (zShift z (t p₁)) (thShift θ (t p₂))
           + (p₂/2) · D_θ g (zShift z (t p₁)) (thShift θ (t p₂))) dt`.

This is the chain rule along the one-parameter curve

`t ↦ (z e^{-t p₁}, arctan (tan θ · e^{-t p₂}))`

(in log coordinates `(s,ζ) ↦ (s - t p₁, ζ - t p₂)`, i.e. the mollifier displacement), together with
the fundamental theorem of calculus.  The two ingredients of the integrand are exactly the
derivatives of the two components of the curve:

* `d/dt (zShift z (t p₁)) = -p₁ · zShift z (t p₁)`, so the `z`-term is `-p₁ D_z g`;
* `d/dt (thShift θ (t p₂)) = -(p₂/2) sin (2 · thShift θ (t p₂))`, and `D_θ = sin(2θ) ∂_θ`,
  so the `θ`-term is `-(p₂/2) D_θ g`.

The chain rule for the two-variable profile is taken in the Fréchet form
(`HasFDerivAt.comp_hasDerivAt`), with the value of `fderiv ℝ (uncurry g)` on the tangent vector
computed from `Work.FTS.EllipticEst.Prop.pz_eq_fderiv` / `pth_eq_fderiv` (linearity + the two
coordinate directions `(1,0)`, `(0,1)`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

open Work.FTS.StrongEps

set_option autoImplicit false

/-- The `z`-component of the mollifier path: `t ↦ z e^{-t p} = zShift z (t p)` has derivative
`-p · zShift z (t p)`, which is `-p` times the `D_z`-weight `z` of the point. -/
private lemma hasDerivAt_zShift_param (z p t : ℝ) :
    HasDerivAt (fun s : ℝ => zShift z (s * p)) (-p * zShift z (t * p)) t := by
  have hd : HasDerivAt (fun s : ℝ => s * p) p t := by
    simpa using (hasDerivAt_id t).mul_const p
  have hdn : HasDerivAt (fun s : ℝ => -(s * p)) (-p) t := hd.neg
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(s * p)))
      (Real.exp (-(t * p)) * (-p)) t := by
    exact (Real.hasDerivAt_exp (-(t * p))).comp t hdn
  have h2 : HasDerivAt (fun s : ℝ => z * Real.exp (-(s * p)))
      (z * (Real.exp (-(t * p)) * (-p))) t := hexp.const_mul z
  have hder : z * (Real.exp (-(t * p)) * (-p)) = -p * (z * Real.exp (-(t * p))) := by ring
  rw [hder] at h2
  simpa only [zShift] using h2

/-- The `θ`-component of the mollifier path: `t ↦ arctan (tan θ · e^{-t p}) = thShift θ (t p)` has
derivative `-(p/2) sin (2 · thShift θ (t p))`, which is `-(p/2)` times `sin(2θ)` at the shifted
point, i.e. `-(p/2)` times the `D_θ`-weight. -/
private lemma hasDerivAt_thShift_param (θ p t : ℝ) :
    HasDerivAt (fun s : ℝ => thShift θ (s * p))
      (-(p / 2) * Real.sin (2 * thShift θ (t * p))) t := by
  have hd : HasDerivAt (fun s : ℝ => s * p) p t := by
    simpa using (hasDerivAt_id t).mul_const p
  have hdn : HasDerivAt (fun s : ℝ => -(s * p)) (-p) t := hd.neg
  have hexp : HasDerivAt (fun s : ℝ => Real.tan θ * Real.exp (-(s * p)))
      (Real.tan θ * (Real.exp (-(t * p)) * (-p))) t := by
    exact ((Real.hasDerivAt_exp (-(t * p))).comp t hdn).const_mul (Real.tan θ)
  have harct : HasDerivAt (fun s : ℝ => Real.arctan (Real.tan θ * Real.exp (-(s * p))))
      ((1 / (1 + (Real.tan θ * Real.exp (-(t * p))) ^ 2))
        * (Real.tan θ * (Real.exp (-(t * p)) * (-p)))) t := by
    exact (Real.hasDerivAt_arctan (Real.tan θ * Real.exp (-(t * p)))).comp t hexp
  have hval : (1 / (1 + (Real.tan θ * Real.exp (-(t * p))) ^ 2))
        * (Real.tan θ * (Real.exp (-(t * p)) * (-p)))
      = -(p / 2) * Real.sin (2 * Real.arctan (Real.tan θ * Real.exp (-(t * p)))) := by
    have hsin : Real.sin (2 * Real.arctan (Real.tan θ * Real.exp (-(t * p))))
        = 2 * (Real.tan θ * Real.exp (-(t * p)))
          / (1 + (Real.tan θ * Real.exp (-(t * p))) ^ 2) := by
      rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
      field_simp
      rw [show Real.sqrt (1 + Real.tan θ ^ 2 * Real.exp (-(t * p)) ^ 2) ^ 2
          = 1 + Real.tan θ ^ 2 * Real.exp (-(t * p)) ^ 2 from Real.sq_sqrt (by positivity)]
    rw [hsin]
    rw [show Real.tan θ * (Real.exp (-(t * p)) * (-p))
        = (Real.tan θ * Real.exp (-(t * p))) * (-p) by ring]
    field_simp
  rw [hval] at harct
  simpa only [thShift] using harct

/-- **The chain rule along the mollifier path.**  For `g` of class `C^∞` on the quadrant and
`(z,θ) ∈ Quad`, the function `t ↦ g (zShift z (t p₁)) (thShift θ (t p₂))` has derivative
`-(p₁ · D_z g + (p₂/2) · D_θ g)` at the shifted point. -/
private lemma hasDerivAt_shiftPath {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g (zShift z (s * p.1)) (thShift θ (s * p.2)))
      (-(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
        + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)))) t := by
  have hperm : (zShift z (t * p.1), thShift θ (t * p.2)) ∈ Quad :=
    ⟨zShift_pos hz, thShift_mem hθ⟩
  have hdiff : DifferentiableAt ℝ (Function.uncurry g) (zShift z (t * p.1), thShift θ (t * p.2)) :=
    ((hg 1).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hperm)
  have hG : HasFDerivAt (Function.uncurry g)
      (fderiv ℝ (Function.uncurry g) (zShift z (t * p.1), thShift θ (t * p.2)))
      (zShift z (t * p.1), thShift θ (t * p.2)) := hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => (zShift z (s * p.1), thShift θ (s * p.2)))
      ((-p.1 * zShift z (t * p.1)), (-(p.2 / 2) * Real.sin (2 * thShift θ (t * p.2)))) t :=
    (hasDerivAt_zShift_param z p.1 t).prodMk (hasDerivAt_thShift_param θ p.2 t)
  have hcomp := hG.comp_hasDerivAt t hcurve
  have hkey : (fderiv ℝ (Function.uncurry g) (zShift z (t * p.1), thShift θ (t * p.2)))
        ((-p.1 * zShift z (t * p.1)), (-(p.2 / 2) * Real.sin (2 * thShift θ (t * p.2))))
      = -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
        + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))) := by
    rw [show ((-p.1 * zShift z (t * p.1)), (-(p.2 / 2) * Real.sin (2 * thShift θ (t * p.2))))
        = (-p.1 * zShift z (t * p.1)) • ((1 : ℝ), (0 : ℝ))
          + (-(p.2 / 2) * Real.sin (2 * thShift θ (t * p.2))) • ((0 : ℝ), (1 : ℝ)) by
      ext <;> simp [Prod.smul_mk]]
    rw [map_add, map_smul, map_smul,
      ← Work.FTS.EllipticEst.Prop.pz_eq_fderiv hdiff,
      ← Work.FTS.EllipticEst.Prop.pth_eq_fderiv hdiff]
    simp only [Work.Spaces.Dz, Work.Spaces.Dth]
    ring
  rw [hkey] at hcomp
  simpa only [Function.comp_def, Function.uncurry] using hcomp

theorem shiftPath_sub {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ) :
    g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - g z θ
      = ∫ t in (0 : ℝ)..1, (-(p.1 * Work.Spaces.Dz g (Work.FTS.StrongEps.zShift z (t * p.1))
            (Work.FTS.StrongEps.thShift θ (t * p.2))
          + (p.2 / 2) * Work.Spaces.Dth g (Work.FTS.StrongEps.zShift z (t * p.1))
            (Work.FTS.StrongEps.thShift θ (t * p.2)))) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => g (zShift z (s * p.1)) (thShift θ (s * p.2)))
      (-(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
        + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)))) t :=
    fun t => hasDerivAt_shiftPath hg hz hθ p t
  have hcont : Continuous fun t : ℝ => -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1))
          (thShift θ (t * p.2))
        + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))) := by
    have hP : Continuous fun t : ℝ => zShift z (t * p.1) := by
      have h : Continuous fun t : ℝ => z * Real.exp (-(t * p.1)) := by fun_prop
      simpa only [zShift] using h
    have hT : Continuous fun t : ℝ => thShift θ (t * p.2) := by
      have h : Continuous fun t : ℝ => Real.arctan (Real.tan θ * Real.exp (-(t * p.2))) := by
        fun_prop
      simpa only [thShift] using h
    have hpzc : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pz g q.1 q.2) Quad :=
      (Work.FTS.EllipticEst.Prop.contDiffOn_uncurry_pz_succ (G := g) (V := Quad) (n := 0)
        (isOpen_Ioi.prod isOpen_Ioo) (by simpa using hg 1)).continuousOn
    have hpthc : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pth g q.1 q.2) Quad :=
      (Work.FTS.EllipticEst.Prop.contDiffOn_uncurry_pth_succ (G := g) (V := Quad) (n := 0)
        (isOpen_Ioi.prod isOpen_Ioo) (by simpa using hg 1)).continuousOn
    have hquad : ∀ t : ℝ, (zShift z (t * p.1), thShift θ (t * p.2)) ∈ Quad :=
      fun t => ⟨zShift_pos hz, thShift_mem hθ⟩
    have hpz : Continuous fun t : ℝ =>
        Work.Spaces.pz g (zShift z (t * p.1)) (thShift θ (t * p.2)) := by
      have := hpzc.comp_continuous (hP.prodMk hT) hquad
      simpa only [Function.comp_def] using this
    have hpth : Continuous fun t : ℝ =>
        Work.Spaces.pth g (zShift z (t * p.1)) (thShift θ (t * p.2)) := by
      have := hpthc.comp_continuous (hP.prodMk hT) hquad
      simpa only [Function.comp_def] using this
    have h1 : Continuous fun t : ℝ =>
        Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
      hP.mul hpz
    have hsin : Continuous fun t : ℝ => Real.sin (2 * thShift θ (t * p.2)) :=
      Real.continuous_sin.comp (continuous_const.mul hT)
    have h2 : Continuous fun t : ℝ =>
        Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
      hsin.mul hpth
    have hsum : Continuous fun t : ℝ =>
        p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
          + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
      (h1.const_mul p.1).add (h2.const_mul (p.2 / 2))
    exact hsum.neg
  have hint : IntervalIntegrable (fun t : ℝ => -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1))
        (thShift θ (t * p.2))
      + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))))
      volume (0 : ℝ) 1 :=
    hcont.intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ => g (zShift z (s * p.1)) (thShift θ (s * p.2)))
    (f' := fun t : ℝ => -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
      + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))))
    (fun x _ => hderiv x) hint
  have hF1 : g (zShift z (1 * p.1)) (thShift θ (1 * p.2))
      = g (zShift z p.1) (thShift θ p.2) := by simp
  have hF0 : g (zShift z (0 * p.1)) (thShift θ (0 * p.2)) = g z θ := by
    have key : Real.arctan (Real.tan θ) = θ :=
      Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2
    simp only [zero_mul, zShift, thShift, neg_zero, Real.exp_zero, mul_one, key]
  rw [hF1, hF0] at hftc
  rw [← hftc]

end Work.FTS.StrongEps.DiffAux
