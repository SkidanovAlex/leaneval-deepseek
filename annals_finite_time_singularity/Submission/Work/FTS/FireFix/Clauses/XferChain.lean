/-
# The `(ρ, θ)`-transfer, `lintegral` form

`lintegral_transfer` is the `ℝ≥0∞`-valued change of variables underlying
`Work.FTS.FireFix.Clauses.transfer_rho_theta`: for a measurable `g : ℝ → ℝ → ℝ≥0∞`,

`∫⁻ x : ℝ³, g (ρ x ^ (3α) / B) (θ x)
   = ofReal (2π B^{1/α} / (3α)) * ∫⁻ q in (0,∞) × (-π/2,π/2), ofReal (q.1^{1/α-1} cos q.2) * g q.1 q.2`.

The proof decomposes `ℝ³ = ℝ × ℝ²` (axis coordinate first), applies the two-dimensional polar
change of variables in the plane, then the polar change of variables in the half plane `r > 0`, and
finally the one-dimensional substitution `ρ = (B s)^{1/(3α)}`.
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.FireFix.Clauses.XferDefs
import Submission.Work.FTS.FireFix.Clauses.xfer_plane_radial
import Submission.Work.FTS.FireFix.Clauses.xfer_halfline_polar
import Submission.Work.FTS.FireFix.Clauses.xfer_scaling_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Work.FTS.FireFix.Clauses

/-- The angular interval `(-π/2, π/2)`. -/
abbrev ThetaI : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

/-- The domain `(0,∞) × (-π/2, π/2)` of the transferred profile. -/
abbrev Adom : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ ThetaI

/-- The profile pulled back to a point `(r,z)` of the half plane:
`(r,z) ↦ g (√(r²+z²)^{3α}/B) (arctan (z/r))`. -/
def prof (α B : ℝ) (g : ℝ → ℝ → ENNReal) (r z : ℝ) : ENNReal :=
  g (Real.sqrt (r ^ 2 + z ^ 2) ^ (3 * α) / B) (Real.arctan (z / r))

@[simp] lemma rho_pt3 (a b t : ℝ) :
    Work.Cyl.rho (pt3 a b t) = Real.sqrt (a ^ 2 + b ^ 2 + t ^ 2) := by
  simp only [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, pt3_zero, pt3_one, pt3_two]

@[simp] lemma theta_pt3 (a b t : ℝ) :
    Work.Cyl.theta (pt3 a b t) = Real.arctan (t / Real.sqrt (a ^ 2 + b ^ 2)) := by
  simp only [Work.Cyl.theta, Work.Cyl.axial, Work.Cyl.radial, Work.Cyl.radSq,
    pt3_zero, pt3_one, pt3_two]

lemma prof_measurable {α B : ℝ} (hα : 0 ≤ α) {g : ℝ → ℝ → ENNReal}
    (hg : Measurable (fun q : ℝ × ℝ => g q.1 q.2)) :
    Measurable (fun p : ℝ × ℝ => prof α B g p.1 p.2) := by
  refine hg.comp (Measurable.prodMk ?_ ?_)
  · have hsq : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
    have hpow : Measurable (fun p : ℝ × ℝ => Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ (3 * α)) :=
      ((Real.continuous_sqrt.comp hsq).rpow_const
        (fun p => Or.inr (by linarith))).measurable
    exact hpow.div measurable_const
  · exact Real.continuous_arctan.measurable.comp (measurable_snd.div measurable_fst)

/-- The angular profile is radial in the plane: `prof α B g (√(a²+b²)) t` is the profile of the
point `pt3 a b t`. -/
lemma prof_sqrt (α B : ℝ) (g : ℝ → ℝ → ENNReal) (a b t : ℝ) :
    prof α B g (Real.sqrt (a ^ 2 + b ^ 2)) t
      = g (Real.sqrt (a ^ 2 + b ^ 2 + t ^ 2) ^ (3 * α) / B)
          (Real.arctan (t / Real.sqrt (a ^ 2 + b ^ 2))) := by
  simp only [prof, Real.sq_sqrt (by positivity : (0:ℝ) ≤ a ^ 2 + b ^ 2)]

/-- On the half plane `r > 0` the polar coordinates `z ↦ (r cos z, r sin z)` give back the
profile `g (r^{3α}/B) z`. -/
lemma prof_polar (α B : ℝ) (g : ℝ → ℝ → ENNReal) {r z : ℝ} (hr : 0 < r) (hz : z ∈ ThetaI) :
    prof α B g (r * Real.cos z) (r * Real.sin z) = g (r ^ (3 * α) / B) z := by
  have hsq : (r * Real.cos z) ^ 2 + (r * Real.sin z) ^ 2 = r ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [prof, hsq, Real.sqrt_sq hr.le]
  congr 1
  rw [mul_div_mul_left _ _ (ne_of_gt hr), ← Real.tan_eq_sin_div_cos]
  exact Real.arctan_tan hz.1 hz.2

/-- Measurability of the integrand after the Fubini decomposition of `ℝ³`. -/
lemma ghat_measurable {α B : ℝ} (hα : 0 ≤ α) {g : ℝ → ℝ → ENNReal}
    (hg : Measurable (fun q : ℝ × ℝ => g q.1 q.2)) :
    Measurable (fun p : ℝ × (ℝ × ℝ) =>
      g (Real.sqrt (p.2.1 ^ 2 + p.2.2 ^ 2 + p.1 ^ 2) ^ (3 * α) / B)
        (Real.arctan (p.1 / Real.sqrt (p.2.1 ^ 2 + p.2.2 ^ 2)))) := by
  refine hg.comp (Measurable.prodMk ?_ ?_)
  · have hsq : Continuous fun p : ℝ × (ℝ × ℝ) =>
        Real.sqrt (p.2.1 ^ 2 + p.2.2 ^ 2 + p.1 ^ 2) := by fun_prop
    exact ((hsq.rpow_const (fun p => Or.inr (by linarith))).measurable).div measurable_const
  · exact Real.continuous_arctan.measurable.comp
      (measurable_fst.div (by fun_prop : Measurable fun p : ℝ × (ℝ × ℝ) =>
        Real.sqrt (p.2.1 ^ 2 + p.2.2 ^ 2)))

/-- The coordinate map `x ↦ (ρ x ^ (3α)/B, θ x)` is measurable. -/
lemma measurable_rhoTheta {α B : ℝ} (hα : 0 ≤ α) :
    Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (Work.Cyl.rho x ^ (3 * α) / B, Work.Cyl.theta x)) := by
  refine Measurable.prodMk ?_ ?_
  · have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 3) => Work.Cyl.rho x := by
      simp only [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial]
      fun_prop
    exact ((hcont.rpow_const (fun x => Or.inr (by linarith))).measurable).div_const B
  · show Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
        Real.arctan (x 2 / Real.sqrt (x 0 ^ 2 + x 1 ^ 2)))
    exact Real.continuous_arctan.measurable.comp
      ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin 3) => x 2).div
        (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin 3) =>
          Real.sqrt (x 0 ^ 2 + x 1 ^ 2)))

/-- **The half plane step**: the polar change of variables on `r > 0`, with the constant `2π` of
the plane already present. -/
lemma halfline_step {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {g : ℝ → ℝ → ENNReal}
    (hg : Measurable (fun q : ℝ × ℝ => g q.1 q.2)) :
    (∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
        ENNReal.ofReal p.1 * (ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2))
      = ∫⁻ q in Adom,
          ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) * (ENNReal.ofReal (2 * Real.pi) *
            g (q.1 ^ (3 * α) / B) q.2) := by
  have hK : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2) MeasureTheory.volume :=
    (measurable_const.mul (prof_measurable hα.le hg)).aemeasurable
  have h := xfer_halfline_polar (K := fun r z => ENNReal.ofReal (2 * Real.pi) * prof α B g r z) hK
  rw [h]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, z⟩ hq
  obtain ⟨hr, hz⟩ := hq
  show ENNReal.ofReal (r ^ 2 * Real.cos z) *
      (ENNReal.ofReal (2 * Real.pi) * prof α B g (r * Real.cos z) (r * Real.sin z))
    = ENNReal.ofReal (r ^ 2 * Real.cos z) *
        (ENNReal.ofReal (2 * Real.pi) * g (r ^ (3 * α) / B) z)
  rw [prof_polar α B g hr hz]

/-- **The scaling step**: the substitution `ρ = (B s)^{1/(3α)}` in the radial variable. -/
lemma scaling_step {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {g : ℝ → ℝ → ENNReal}
    (hg : Measurable (fun q : ℝ × ℝ => g q.1 q.2)) :
    (∫⁻ q in Adom, ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) * g (q.1 ^ (3 * α) / B) q.2)
      = ENNReal.ofReal (B ^ (1 / α) / (3 * α)) *
        ∫⁻ q in Adom, ENNReal.ofReal (q.1 ^ (1 / α - 1) * Real.cos q.2) * g q.1 q.2 := by
  have h3α : (0 : ℝ) < 3 * α := by positivity
  have hmul : (1 : ℝ) / (3 * α) * (3 * α) = 1 := by field_simp
  -- measurability of the two integrands
  have hmeas1 : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 ^ 2 * Real.cos p.2) * g (p.1 ^ (3 * α) / B) p.2)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Adom) :=
    Measurable.aemeasurable (Measurable.mul
      (ENNReal.measurable_ofReal.comp
        ((measurable_fst.pow_const 2).mul (Real.continuous_cos.measurable.comp measurable_snd)))
      (hg.comp (Measurable.prodMk
        ((measurable_fst.pow_const _).div measurable_const) measurable_snd)))
  have hmeas2 : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 ^ (1 / α - 1) * Real.cos p.2) * g p.1 p.2)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Adom) :=
    Measurable.aemeasurable (Measurable.mul
      (ENNReal.measurable_ofReal.comp
        ((measurable_fst.pow_const _).mul (Real.continuous_cos.measurable.comp measurable_snd)))
      hg)
  -- pass to the iterated integral, angular variable outermost
  have hunwrap : (∫⁻ q in Adom,
        ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) * g (q.1 ^ (3 * α) / B) q.2)
      = ∫⁻ z in ThetaI, ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r ^ 2 * Real.cos z) * g (r ^ (3 * α) / B) z := by
    rw [show Adom = Set.Ioi (0 : ℝ) ×ˢ ThetaI from rfl]
    exact setLIntegral_prod_symm _ hmeas1
  rw [hunwrap]
  have hstep : ∀ z ∈ ThetaI, (∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (r ^ 2 * Real.cos z) * g (r ^ (3 * α) / B) z)
      = ENNReal.ofReal (Real.cos z) *
        (ENNReal.ofReal (B ^ (1 / α) / (3 * α)) *
          ∫⁻ s in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (s ^ (1 / α - 1)) * g s z) := by
    intro z hz
    have hcos : 0 ≤ Real.cos z := (Real.cos_pos_of_mem_Ioo hz).le
    have hG : AEMeasurable (fun r : ℝ => g (r ^ (3 * α) / B) z) MeasureTheory.volume :=
      (hg.comp (Measurable.prodMk ((measurable_id.pow_const _).div measurable_const)
        measurable_const)).aemeasurable
    have hcongr : (∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r ^ 2 * Real.cos z) * g (r ^ (3 * α) / B) z)
        = ∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (Real.cos z) * (ENNReal.ofReal (r ^ 2) * g (r ^ (3 * α) / B) z) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      rw [mul_comm (r ^ 2) (Real.cos z), ENNReal.ofReal_mul hcos, mul_assoc]
    rw [hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [xfer_scaling_rpow (α := α) (B := B) hα hB (G := fun r => g (r ^ (3 * α) / B) z) hG]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs
    have hBs : (0:ℝ) < B * s := mul_pos hB hs0
    have harg : ((B * s) ^ (1 / (3 * α))) ^ (3 * α) / B = s := by
      rw [← Real.rpow_mul hBs.le, hmul, Real.rpow_one, mul_div_cancel_left₀ s (ne_of_gt hB)]
    rw [harg]
  rw [setLIntegral_congr_fun measurableSet_Ioo (fun z hz => hstep z hz)]
  -- reassociate so that the constant `B^{1/α}/(3α)` is the outermost factor
  rw [show (∫⁻ z in ThetaI, ENNReal.ofReal (Real.cos z) *
        (ENNReal.ofReal (B ^ (1 / α) / (3 * α)) *
          ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ (1 / α - 1)) * g s z))
      = ∫⁻ z in ThetaI, ENNReal.ofReal (B ^ (1 / α) / (3 * α)) *
        (ENNReal.ofReal (Real.cos z) *
          ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ (1 / α - 1)) * g s z) from
    setLIntegral_congr_fun measurableSet_Ioo (fun z _ => by
      rw [← mul_assoc,
        mul_comm (ENNReal.ofReal (Real.cos z)) (ENNReal.ofReal (B ^ (1 / α) / (3 * α))),
        mul_assoc])]
  -- pull the constant out of the angular integral
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  -- move `ofReal (cos z)` inside the radial integral
  have hinner : (∫⁻ z in ThetaI, ENNReal.ofReal (Real.cos z) *
        ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ (1 / α - 1)) * g s z)
      = ∫⁻ z in ThetaI, ∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.cos z) * (ENNReal.ofReal (s ^ (1 / α - 1)) * g s z) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun z _ => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hinner]
  -- back to the product domain, and identify the two weights
  have hmeas3 : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.cos p.2) * (ENNReal.ofReal (p.1 ^ (1 / α - 1)) * g p.1 p.2))
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Adom) :=
    Measurable.aemeasurable (Measurable.mul
      (ENNReal.measurable_ofReal.comp (Real.continuous_cos.measurable.comp measurable_snd))
      (Measurable.mul (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)) hg))
  have hrewrap : (∫⁻ z in ThetaI, ∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.cos z) * (ENNReal.ofReal (r ^ (1 / α - 1)) * g r z))
      = ∫⁻ q in Adom,
          ENNReal.ofReal (Real.cos q.2) *
            (ENNReal.ofReal (q.1 ^ (1 / α - 1)) * g q.1 q.2) := by
    rw [show Adom = Set.Ioi (0 : ℝ) ×ˢ ThetaI from rfl]
    exact (setLIntegral_prod_symm _ hmeas3).symm
  rw [hrewrap]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := hp
  have hcos : 0 ≤ Real.cos p.2 := (Real.cos_pos_of_mem_Ioo hp2).le
  show ENNReal.ofReal (Real.cos p.2) * (ENNReal.ofReal (p.1 ^ (1 / α - 1)) * g p.1 p.2)
    = ENNReal.ofReal (p.1 ^ (1 / α - 1) * Real.cos p.2) * g p.1 p.2
  rw [mul_comm (p.1 ^ (1 / α - 1)) (Real.cos p.2), ENNReal.ofReal_mul hcos, mul_assoc]

/-- **The `(ρ, θ)`-transfer** (the `ℝ≥0∞`-valued change of variables): the pushforward of the
Lebesgue measure on `ℝ³` under `x ↦ (ρ x ^ (3α)/B, θ x)` has density
`ofReal (2π B^{1/α} / (3α)) * ofReal (q.1^{1/α-1} cos q.2)` on `(0,∞) × (-π/2, π/2)`. -/
theorem lintegral_transfer {α B : ℝ} (hα : 0 < α) (hB : 0 < B)
    {g : ℝ → ℝ → ENNReal} (hg : Measurable (fun q : ℝ × ℝ => g q.1 q.2)) :
    ∫⁻ x : EuclideanSpace ℝ (Fin 3), g (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)
      = ENNReal.ofReal (2 * Real.pi * B ^ (1 / α) / (3 * α)) *
        ∫⁻ q in Adom, ENNReal.ofReal (q.1 ^ (1 / α - 1) * Real.cos q.2) * g q.1 q.2 := by
  have h3α : (0 : ℝ) < 3 * α := by positivity
  -- measurability of the coordinate map and of the integrand
  have hT : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (Work.Cyl.rho x ^ (3 * α) / B, Work.Cyl.theta x)) := measurable_rhoTheta hα.le
  have hGb : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      g (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)) := hg.comp hT
  -- transport to the iterated integral over the axis coordinate and the plane coordinates
  rw [lintegral_eucl3_eq_prod hGb]
  -- rewrite `ρ` and `θ` on the coordinate points
  rw [show (∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, g (Work.Cyl.rho (pt3 v.1 v.2 t) ^ (3 * α) / B)
        (Work.Cyl.theta (pt3 v.1 v.2 t)))
      = ∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ,
          g (Real.sqrt (v.1 ^ 2 + v.2 ^ 2 + t ^ 2) ^ (3 * α) / B)
            (Real.arctan (t / Real.sqrt (v.1 ^ 2 + v.2 ^ 2))) from
    lintegral_congr fun t => lintegral_congr fun v => by rw [rho_pt3, theta_pt3]]
  -- identify the integrand as the profile, radial in the plane
  rw [show (∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ,
          g (Real.sqrt (v.1 ^ 2 + v.2 ^ 2 + t ^ 2) ^ (3 * α) / B)
            (Real.arctan (t / Real.sqrt (v.1 ^ 2 + v.2 ^ 2))))
      = ∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, prof α B g (Real.sqrt (v.1 ^ 2 + v.2 ^ 2)) t from
    lintegral_congr fun t => lintegral_congr fun v => (prof_sqrt α B g v.1 v.2 t).symm]
  -- the two-dimensional polar change of variables in the plane, slice by slice
  rw [show (∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, prof α B g (Real.sqrt (v.1 ^ 2 + v.2 ^ 2)) t)
      = ∫⁻ t : ℝ, ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * prof α B g r t from
    lintegral_congr fun t =>
      xfer_plane_radial ((prof_measurable hα.le hg).comp
        (by fun_prop : Measurable fun r : ℝ => (r, t))).aemeasurable]
  -- move the constant `2π` inside the radial integral
  rw [show (∫⁻ t : ℝ, ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * prof α B g r t)
      = ∫⁻ t : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal r * (ENNReal.ofReal (2 * Real.pi) * prof α B g r t) from
    lintegral_congr fun t => by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_congr_fun measurableSet_Ioi fun r _ => by
        rw [← mul_assoc,
          mul_comm (ENNReal.ofReal (2 * Real.pi)) (ENNReal.ofReal r), mul_assoc]]
  -- Fubini: the iterated integral over `(0,∞) × ℝ` is the integral over the half plane
  have hmeasH : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * (ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2))
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
    (Measurable.aemeasurable (Measurable.mul (ENNReal.measurable_ofReal.comp measurable_fst)
      (Measurable.mul measurable_const (prof_measurable hα.le hg)))).mono_measure
        Measure.restrict_le_self
  rw [show (∫⁻ t : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal r * (ENNReal.ofReal (2 * Real.pi) * prof α B g r t))
      = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
          ENNReal.ofReal p.1 * (ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2) from by
    have h := (setLIntegral_prod_symm (f := fun p : ℝ × ℝ =>
        ENNReal.ofReal p.1 * (ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2)) hmeasH).symm
    simpa only [MeasureTheory.Measure.restrict_univ,
      show (MeasureTheory.volume : Measure (ℝ × ℝ))
        = (MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ) from rfl]
      using h]
  -- the polar change of variables in the half plane `r > 0`
  rw [halfline_step hα hB hg]
  -- reassociate and pull the constant `2π` out of the integral over the domain
  rw [show (∫⁻ q in Adom, ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) *
        (ENNReal.ofReal (2 * Real.pi) * g (q.1 ^ (3 * α) / B) q.2))
      = ∫⁻ q in Adom, ENNReal.ofReal (2 * Real.pi) *
          (ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) * g (q.1 ^ (3 * α) / B) q.2) from
    setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun q _ => by
      rw [← mul_assoc, mul_comm (ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2))
        (ENNReal.ofReal (2 * Real.pi)), mul_assoc])]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the radial substitution `ρ = (B s)^{1/(3α)}`
  rw [scaling_step hα hB hg]
  -- combine the two constants
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  congr 1
  ring_nf

end Work.FTS.FireFix.Clauses
