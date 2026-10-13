import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.CoreResiduals.pdR_ssVort_lam
import Submission.Work.CoreResiduals.pdZ_ssVort_lam
import Submission.Work.CoreResiduals.pdR_ssPsi_lam
import Submission.Work.CoreResiduals.pdZ_ssPsi_lam
import Submission.Work.CoreResiduals.timeDeriv_ssVort_lam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `meridianEq_of_dynEqConst` — the chain-rule reduction of the meridian equation

Given profiles `F, Φ` satisfying the constant-rate profile equation `DynEqConst p (2κ) 1 F Φ`
on the open quadrant, and a modulation `λ` with `λ(t) > 0` and `λ'(t) = -κ` (`κ = -λ'`),
the self-similar pair

  `W(r,z,t) = λ(t)⁻¹ F(ρ^p/λ(t), θ)`,  `ψ(r,z,t) = ρ² λ(t)⁻¹ Φ(ρ^p/λ(t), θ)`

solves the meridian scalar equation off the axis.

The engine is the exact pointwise identity (proved below by the chain rule and algebra)

  `meridianResid W ψ r z t = (2 λ(t)²)⁻¹ · ( 2κ·(F + D_z F) + UVR p F Φ )`

evaluated at `(Z, Θ) = (ρ^p/λ(t), arctan(z/r))`; the bracket vanishes by `DynEqConst`.
-/

noncomputable section
open scoped Topology

namespace Work.CoreResiduals

/-- `tan θ(r,z) = z/r` for the polar angle. -/
lemma tan_thetaP_eq (r z : ℝ) (hr : 0 < r) :
    Real.tan (Work.Cyl.thetaP r z) = z / r := by
  rw [Work.Cyl.thetaP, Real.tan_arctan]

/-- **The expansion of `UVR` in polar coordinates.**  Substituting `sin Θ = z/ρ`, `cos Θ = r/ρ`
and `tan Θ = z/r` turns the operator `UVR p F Φ` at `(Z,Θ)` into the purely rational expression
appearing on the right-hand side (this is the form the meridian-residual algebra produces). -/
lemma UVR_polar_expand (p r z ρ : ℝ) (F Φ : ℝ → ℝ → ℝ) (Z Θ : ℝ)
    (hr : r ≠ 0) (hρ : ρ ≠ 0) (hsin : Real.sin Θ = z / ρ) (hcos : Real.cos Θ = r / ρ)
    (htan : Real.tan Θ = z / r) :
    Work.Construction.UVR p F Φ Z Θ =
      2 * (-3 * Φ Z Θ - p * Z * Work.Cyl.pdR Φ Z Θ) * Work.Cyl.pdZ F Z Θ
      + 2 * p * (Work.Cyl.pdZ Φ Z Θ - (z / r) * Φ Z Θ) * (Z * Work.Cyl.pdR F Z Θ)
      - 2 * ((2 * z * Φ Z Θ + p * z * Z * Work.Cyl.pdR Φ Z Θ + r * Work.Cyl.pdZ Φ Z Θ) / r)
          * F Z Θ := by
  rw [Work.Construction.UVR, Work.Construction.Uop, Work.Construction.Vop, Work.Construction.Rop]
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pth, Work.Cyl.pdR, Work.Cyl.pdZ,
    hsin, hcos, htan]
  field_simp

/-- **The algebraic core of the reduction.**  With `ρsq` playing the role of `ρ²` (hypothesis
`hρ : ρsq = r² + z²`), the meridian residual of the self-similar pair — written out with the
five chain-rule identities substituted — equals `(2λ²)⁻¹` times
`2κ(f + Z f₁) + UVR`, in the expanded form of `UVR_polar_expand`. -/
lemma meridianResid_algebra {p κ r z ρsq Z f f1 f2 g g1 g2 lam : ℝ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hrz : r ^ 2 + z ^ 2 ≠ 0) (hρ : ρsq = r ^ 2 + z ^ 2) :
    κ * (lam ^ 2)⁻¹ * (f + Z * f1)
      + (lam⁻¹ * (2 * z * g + ρsq * (g1 * (p * Z * (z / ρsq)) + g2 * (r / ρsq))))
        * (lam⁻¹ * (f1 * (p * Z * (r / ρsq)) - f2 * (z / ρsq)))
      + (-(ρsq * (lam⁻¹ * g) / r)
            - lam⁻¹ * (2 * r * g + ρsq * (g1 * (p * Z * (r / ρsq)) - g2 * (z / ρsq))))
        * (lam⁻¹ * (f1 * (p * Z * (z / ρsq)) + f2 * (r / ρsq)))
      - (lam⁻¹ * (2 * z * g + ρsq * (g1 * (p * Z * (z / ρsq)) + g2 * (r / ρsq))) / r)
        * (lam⁻¹ * f)
      = (2 * lam ^ 2)⁻¹ * (2 * κ * (f + Z * f1)
          + (2 * (-3 * g - p * Z * g1) * f2 + 2 * p * (g2 - (z / r) * g) * (Z * f1)
             - 2 * ((2 * z * g + p * z * Z * g1 + r * g2) / r) * f)) := by
  rw [hρ]
  field_simp
  ring

theorem meridianEq_of_dynEqConst {p κ : ℝ} (hp : 0 < p) {lam : ℝ → ℝ}
    {F Φ : ℝ → ℝ → ℝ}
    (hlam : ∀ t : ℝ, 0 < t → 0 < lam t) (hderiv : ∀ t : ℝ, 0 < t → HasDerivAt lam (-κ) t)
    (hF : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => F q.1 q.2) (z, θ))
    (hΦ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2) (z, θ))
    (h : DynEqConst p (2 * κ) 1 F Φ) :
    ∀ r z t : ℝ, 0 < r → 0 < z → 0 < t →
      meridianResid (ssVort p lam F) (ssPsi p lam Φ) r z t = 0 := by
  intro r z t hr hz ht
  have hlam_pos : 0 < lam t := hlam t ht
  have hlam_ne : lam t ≠ 0 := ne_of_gt hlam_pos
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hρne : Work.Cyl.rhoP r z ≠ 0 := ne_of_gt hρpos
  have hρsq : Work.Cyl.rhoP r z ^ 2 = r ^ 2 + z ^ 2 := Work.Cyl.rhoP_sq r z
  have hΘpos : 0 < Work.Cyl.thetaP r z := by
    rw [Work.Cyl.thetaP]; exact Real.arctan_pos.mpr (div_pos hz hr)
  have hΘlt : Work.Cyl.thetaP r z < Real.pi / 2 := by
    rw [Work.Cyl.thetaP]; exact Real.arctan_lt_pi_div_two _
  have hZpos : 0 < Work.Cyl.rhoP r z ^ p / lam t :=
    div_pos (Real.rpow_pos_of_pos hρpos p) hlam_pos
  have hFd : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z) :=
    (hF _ _ hZpos hΘpos hΘlt).differentiableAt (by norm_num)
  have hΦd : Work.Cyl.DiffAt2 Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z) :=
    (hΦ _ _ hZpos hΘpos hΘlt).differentiableAt (by norm_num)
  have hmem : (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z) ∈ Work.Construction.Qd := by
    simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨hZpos, hΘpos, hΘlt⟩
  have hdyn := h _ _ hmem
  have htan : Real.tan (Work.Cyl.thetaP r z) = z / r := tan_thetaP_eq r z hr
  have hUVR := UVR_polar_expand p r z (Work.Cyl.rhoP r z) F Φ
      (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
      (ne_of_gt hr) hρne (Work.Cyl.sin_thetaP hr z) (Work.Cyl.cos_thetaP hr z) htan
  have halg := meridianResid_algebra (p := p) (κ := κ) (r := r) (z := z)
      (ρsq := Work.Cyl.rhoP r z ^ 2) (Z := Work.Cyl.rhoP r z ^ p / lam t)
      (f := F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (f1 := Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (f2 := Work.Cyl.pdZ F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (g := Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (g1 := Work.Cyl.pdR Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (g2 := Work.Cyl.pdZ Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (lam := lam t) (ne_of_gt hr) hlam_ne (by positivity) hρsq
  unfold meridianResid
  rw [timeDeriv_ssVort_lam hlam_ne (hderiv t ht) hFd,
      pdZ_ssPsi_lam hr hlam_ne hΦd, pdR_ssVort_lam hr hlam_ne hFd,
      pdR_ssPsi_lam hr hlam_ne hΦd, pdZ_ssVort_lam hr hlam_ne hFd]
  simp only [ssVort, ssPsi]
  rw [halg]
  have hb : 2 * κ * (F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
        + (Work.Cyl.rhoP r z ^ p / lam t)
            * Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      + (2 * (-3 * Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
              - p * (Work.Cyl.rhoP r z ^ p / lam t)
                  * Work.Cyl.pdR Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
            * Work.Cyl.pdZ F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
         + 2 * p * (Work.Cyl.pdZ Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
              - (z / r) * Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
            * ((Work.Cyl.rhoP r z ^ p / lam t)
                * Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
         - 2 * ((2 * z * Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
                + p * z * (Work.Cyl.rhoP r z ^ p / lam t)
                    * Work.Cyl.pdR Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
                + r * Work.Cyl.pdZ Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) / r)
            * F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) = 0 := by
    rw [← hUVR]
    simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Cyl.pdR, one_mul] at hdyn ⊢
    exact hdyn
  rw [hb, mul_zero]

end Work.CoreResiduals
