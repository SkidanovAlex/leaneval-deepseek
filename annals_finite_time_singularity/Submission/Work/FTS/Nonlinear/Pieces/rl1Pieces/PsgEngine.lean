/-
# `PsgEngine` — the `rl¹` engine for the `sg`-rows of `N`

This module collects the reusable measure-theoretic machinery needed for the five
`sg`-rows `N₁^{sg}, …, N₅^{sg}` (the pieces in which the `Φ̃_*`-coefficients multiply a
factor of the perturbation `g`):

* `radial_of_sqrt` — **the radial Hölder engine**.  If `A r ≤ ofReal (c·(r/(1+r)²)·√(J r))`
  for a.e. `r > 0` with `J` integrable and nonnegative, then
  `∫⁻_r A r ≤ ofReal (c·√(∫_r J r))`: the weight `r/(1+r)² = 1/(r·w r)` is the `L²`-function
  of the radial Cauchy–Schwarz step (`∫ (r/(1+r)²)² ≤ 1`).
* `ang_le_of_slot` — the angular Cauchy–Schwarz step for a function `k` whose weighted square
  is dominated by the `ℋ⁴`-integrand of `g`:
  `∫⁻_θ ofReal |k r θ| ≤ ofReal (2·√(∫_θ HkIntegrand α 4 g r θ)/w r)`.
* `angPth` — the same for `∂_θ g`, with the extra factor `√(∫ sin(2θ)^{γ-2}) ≤ 10√(10/α)`.
* `envG`, `envDz`, `envPth` — the three *basis bounds*: the full `rl¹`-norm of `g`, `D_z g`
  and `∂_θ g` against the radial weight `r⁻¹`, all in terms of `|g|_{ℋ⁴}`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gSlots
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.LintEngine
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary facts -/

/-- The `ℋ^k`-integrand is nonnegative. -/
lemma HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  exact add_nonneg (Work.Spaces.hkZSum_nonneg α k f z θ)
    (Work.Spaces.hkMixedSum_nonneg α k f z θ)

/-- The `θ`-slice of a `SmoothQuad` function is a.e.-measurable on `Iθ`. -/
lemma slice_aem_of_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f)
    {z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun θ : ℝ => f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => f z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ h (show (-1 : ℝ) < z by linarith)
  have h1 : AEMeasurable (fun θ : ℝ => f z θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcd.continuousOn.aemeasurable measurableSet_Ioo
  rwa [← restrict_Iθ_eq_Ioo] at h1

/-- `√x ≤ 2` for `x ≤ 4`. -/
lemma sqrt_le_two {x : ℝ} (hx : x ≤ 4) : Real.sqrt x ≤ 2 := by
  have h := Real.sqrt_le_sqrt hx
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h4] at h

/-- `√(π/2) ≤ 2`. -/
lemma sqrt_pi_div_two_le_two : Real.sqrt (Real.pi / 2) ≤ 2 :=
  sqrt_le_two (by linarith [Real.pi_le_four])

/-- The angular volume in `ENNReal`: `∫⁻_θ 1 = ofReal (π/2)`. -/
lemma lintegral_one_Iθ : (∫⁻ _θ in Work.Spaces.Iθ, (1 : ENNReal)) = ENNReal.ofReal (Real.pi / 2) := by
  rw [MeasureTheory.setLIntegral_const, one_mul]
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  norm_num

/-! ## The radial Hölder engine -/

/-- **The radial Hölder engine.**  If `A r ≤ ofReal (c·(r/(1+r)²)·√(J r))` a.e. on `r > 0`,
with `J` integrable and nonnegative, then

  `∫⁻_{r>0} A r ≤ ofReal (c · √(∫_{r>0} J r))`.

The proof is Cauchy–Schwarz for the two `L²`-functions `r ↦ c·r/(1+r)²` and `r ↦ √(J r)`,
using `∫_{r>0} (r/(1+r)²)² ≤ 1`. -/
theorem radial_of_sqrt {J : ℝ → ℝ} {A : ℝ → ENNReal} {c : ℝ}
    (hc : 0 ≤ c) (hJint : IntegrableOn J (Set.Ioi (0 : ℝ)))
    (hJnn : ∀ r, 0 ≤ J r)
    (hA : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      A r ≤ ENNReal.ofReal (c * (r / (1 + r) ^ 2) * Real.sqrt (J r))) :
    (∫⁻ r in Set.Ioi (0 : ℝ), A r)
      ≤ ENNReal.ofReal (c * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), J r)) := by
  have hcont : ContinuousOn (fun r : ℝ => c * (r / (1 + r) ^ 2)) (Set.Ioi (0 : ℝ)) := by
    refine continuousOn_const.mul (continuousOn_id.div ?_ ?_)
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro r hr
      have hr0 : 0 < r := hr
      exact (pow_pos (by linarith : (0 : ℝ) < 1 + r) 2).ne'
  have hLae : AEMeasurable (fun r : ℝ => ENNReal.ofReal (c * (r / (1 + r) ^ 2)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hcont.aemeasurable measurableSet_Ioi).ennreal_ofReal
  have hJae : AEMeasurable J (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hJint.aestronglyMeasurable.aemeasurable
  have hMae : AEMeasurable (fun r : ℝ => ENNReal.ofReal (Real.sqrt (J r)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := (hJae.sqrt).ennreal_ofReal
  have h22 : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (p := 2) (q := 2) h22 hLae hMae
  -- ### the monotonicity step, with the pointwise bound rewritten as a product
  have hmono : (∫⁻ r in Set.Ioi (0 : ℝ), A r)
      ≤ ∫⁻ r, ENNReal.ofReal (c * (r / (1 + r) ^ 2)) * ENNReal.ofReal (Real.sqrt (J r))
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine le_trans (lintegral_mono_ae hA) ?_
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    exact le_of_eq (ENNReal.ofReal_mul
      (mul_nonneg hc (div_nonneg hr0.le (by positivity))))
  -- ### the `L`-factor `r ↦ ofReal (c·r/(1+r)²)`
  have hc2int : Integrable (fun r : ℝ => (c * (r / (1 + r) ^ 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : Integrable (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.integrableOn_G_sq
    refine (h1.const_mul (c ^ 2)).congr ?_
    filter_upwards with r
    ring
  have hInt0 : 0 ≤ ∫ r in Set.Ioi (0 : ℝ), (c * (r / (1 + r) ^ 2)) ^ 2 :=
    integral_nonneg fun r => sq_nonneg _
  have hLpt : (fun r : ℝ => (fun r : ℝ => ENNReal.ofReal (c * (r / (1 + r) ^ 2))) r ^ (2 : ℝ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      fun r : ℝ => ENNReal.ofReal ((c * (r / (1 + r) ^ 2)) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    rw [ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg hc (div_nonneg hr0.le (by positivity))) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_two]
  have hLeq : (∫⁻ r, (fun r : ℝ => ENNReal.ofReal (c * (r / (1 + r) ^ 2))) r ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
      = ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), (c * (r / (1 + r) ^ 2)) ^ 2) := by
    rw [lintegral_congr_ae hLpt]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hc2int
      (Eventually.of_forall fun r => sq_nonneg _)).symm
  have hAle : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (c * (r / (1 + r) ^ 2)) ^ 2) ≤ c := by
    have hval : (∫ r in Set.Ioi (0 : ℝ), (c * (r / (1 + r) ^ 2)) ^ 2)
        = c ^ 2 * ∫ r in Set.Ioi (0 : ℝ), (r / (1 + r) ^ 2) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun r => by ring)
    rw [hval, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
    exact le_trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_one.mpr Work.FTS.Nonlinear.Pieces.rl1Tools.integral_G_sq_le_one) hc)
      (le_of_eq (mul_one c))
  have hLbound : (∫⁻ r, (fun r : ℝ => ENNReal.ofReal (c * (r / (1 + r) ^ 2))) r ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c := by
    rw [hLeq, ENNReal.ofReal_rpow_of_nonneg hInt0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact ENNReal.ofReal_le_ofReal (by rwa [← Real.sqrt_eq_rpow])
  -- ### the `M`-factor `r ↦ ofReal (√(J r))`
  have hJint0 : 0 ≤ ∫ r in Set.Ioi (0 : ℝ), J r := integral_nonneg hJnn
  have hMpt : (fun r : ℝ => (fun r : ℝ => ENNReal.ofReal (Real.sqrt (J r))) r ^ (2 : ℝ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      fun r : ℝ => ENNReal.ofReal (J r) := by
    filter_upwards with r
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_two, Real.sq_sqrt (hJnn r)]
  have hMeq : (∫⁻ r, (fun r : ℝ => ENNReal.ofReal (Real.sqrt (J r))) r ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
      = ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), J r) := by
    rw [lintegral_congr_ae hMpt]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hJint
      (Eventually.of_forall hJnn)).symm
  have hMbound : (∫⁻ r, (fun r : ℝ => ENNReal.ofReal (Real.sqrt (J r))) r ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt (∫ r in Set.Ioi (0 : ℝ), J r)) := by
    rw [hMeq, ENNReal.ofReal_rpow_of_nonneg hJint0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      Real.sqrt_eq_rpow]
  refine le_trans (le_trans hmono hhold) ?_
  refine le_trans (mul_le_mul' hLbound hMbound) ?_
  exact le_of_eq (ENNReal.ofReal_mul hc).symm

/-! ## The slice of the `ℋ⁴`-integrand as a function of `r` -/

/-- `Jfun α g r` is the `θ`-slice of the `ℋ⁴`-integrand of `g`: the `r`-integrand of `HkSq`. -/
def Jfun (α : ℝ) (g : ℝ → ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ

/-- `HkSq α 4 g` is the integral of `Jfun α g` over `(0,∞)`. -/
lemma HkSq_eq_Ioi (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 4 g = ∫ r in Set.Ioi (0 : ℝ), Jfun α g r := by
  rw [Work.Spaces.HkSq, Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
  rfl

lemma Jfun_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (r : ℝ) : 0 ≤ Jfun α g r :=
  integral_nonneg fun θ => HkIntegrand_nonneg α 4 g r θ

lemma Jfun_integrableOn {α : ℝ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 g) :
    IntegrableOn (Jfun α g) (Set.Ioi (0 : ℝ)) := by
  have h : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 g z θ) (Set.Ici (0 : ℝ)) := hmem.2
  exact (h.mono_set (fun x hx => show (0 : ℝ) ≤ x from le_of_lt hx))

/-! ## The angular Cauchy–Schwarz step -/

/-- **The angular step.**  If the weighted square of `k` is dominated by the `ℋ⁴`-integrand of
`g` (`w(z)²·k(z,θ)² ≤ HkIntegrand α 4 g z θ` a.e.), then the angular lintegral of `|k|` is
bounded by `ofReal (2·√(Jfun α g r)/w r)`:
Cauchy–Schwarz in `θ` against `1`, using `∫_θ 1 = π/2 ≤ 4`. -/
lemma ang_le_of_slot {α : ℝ} {g k : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (hkaem : ∀ r : ℝ, 0 < r → AEMeasurable (fun θ : ℝ => k r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hslot : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w r) ^ 2 * (k r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)
      ≤ ENNReal.ofReal (2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r) := by
  have hw : 0 < Work.Spaces.w r := w_pos_of_pos hr
  have h22 : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)
      ≤ (∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal |k r θ|) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∫⁻ θ in Work.Spaces.Iθ, (1 : ENNReal) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (p := 2) (q := 2) h22 (f := fun θ : ℝ => ENNReal.ofReal |k r θ|)
      (g := fun _ : ℝ => (1 : ENNReal)) (hkaem r hr).abs.ennreal_ofReal aemeasurable_const
    simpa using h
  have hk2int : IntegrableOn (fun θ : ℝ => (k r θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' (g := fun θ : ℝ =>
      Work.Spaces.HkIntegrand α 4 g r θ / (Work.Spaces.w r) ^ 2) ?_ ?_ ?_
    · exact (hmem.1 r hr.le).div_const ((Work.Spaces.w r) ^ 2)
    · exact ((hkaem r hr).pow_const 2).aestronglyMeasurable
    · filter_upwards [hslot r hr] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hw2 : 0 < (Work.Spaces.w r) ^ 2 := pow_pos hw 2
      rw [le_div_iff₀ hw2]
      exact le_of_eq_of_le (by ring :
        (k r θ) ^ 2 * (Work.Spaces.w r) ^ 2 = (Work.Spaces.w r) ^ 2 * (k r θ) ^ 2) hθ
  have hUpt : (fun θ : ℝ => (ENNReal.ofReal |k r θ|) ^ (2 : ℝ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ : ℝ => ENNReal.ofReal ((k r θ) ^ 2) := by
    filter_upwards with θ
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_two, sq_abs]
  have hU : (∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal |k r θ|) ^ (2 : ℝ))
      = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2) := by
    rw [lintegral_congr_ae hUpt]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hk2int
      (Eventually.of_forall fun θ => sq_nonneg _)).symm
  have hV : (∫⁻ θ in Work.Spaces.Iθ, (1 : ENNReal) ^ (2 : ℝ)) = ENNReal.ofReal (Real.pi / 2) := by
    rw [show (fun θ : ℝ => (1 : ENNReal) ^ (2 : ℝ)) = fun _ : ℝ => (1 : ENNReal) from by
      funext θ; simp]
    exact lintegral_one_Iθ
  have hE0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
  have hU2 : (∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal |k r θ|) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2)) := by
    rw [hU, ENNReal.ofReal_rpow_of_nonneg hE0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      Real.sqrt_eq_rpow]
  have hV2 : (∫⁻ θ in Work.Spaces.Iθ, (1 : ENNReal) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal 2 := by
    rw [hV, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.sqrt_eq_rpow]
    exact sqrt_pi_div_two_le_two
  have hEbound : Real.sqrt (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2)
      ≤ Real.sqrt (Jfun α g r) / Work.Spaces.w r := by
    have h2 : (Work.Spaces.w r) ^ 2 * (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2) ≤ Jfun α g r := by
      rw [Jfun, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hmem.1 r hr.le) ?_
      exact hslot r hr
    have h3 : Real.sqrt (Work.Spaces.w r ^ 2 * ∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2)
        ≤ Real.sqrt (Jfun α g r) := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hw.le] at h3
    rw [le_div_iff₀ hw, mul_comm]
    exact h3
  refine le_trans h1 ?_
  have hstep : ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2))
        * ENNReal.ofReal 2
      ≤ ENNReal.ofReal (2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r) := by
    rw [mul_comm, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h3 : 2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2)
        ≤ 2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r := by
      have h4 := mul_le_mul_of_nonneg_left hEbound (by norm_num : (0 : ℝ) ≤ 2)
      rwa [show (2 : ℝ) * (Real.sqrt (Jfun α g r) / Work.Spaces.w r)
          = 2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r from by ring] at h4
    exact h3
  exact le_trans (mul_le_mul' (le_of_eq hU2) hV2) hstep

/-- `w(z)²·(D_z g)² ≤ HkIntegrand α 4 g`: the `D_z¹`-slot of the `ℋ⁴`-integrand. -/
lemma w2_Dz_sq_le_HkIntegrand (α : ℝ) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.Dz g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 (by norm_num [Work.Spaces.eta])
  have hw : 0 ≤ Work.Spaces.w z := w_nonneg z
  have h1 : Work.Spaces.w z ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspos]
    nlinarith [hsle, hw]
  have hstep : (Work.Spaces.w z * |Work.Spaces.Dz g z θ|) ^ 2
      ≤ (Work.Spaces.Dz g z θ * (Work.Spaces.w z
          / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have hle := mul_le_mul_of_nonneg_right h1 (abs_nonneg (Work.Spaces.Dz g z θ))
    rw [mul_comm (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
      |Work.Spaces.Dz g z θ|] at hle
    have h5 : (|Work.Spaces.Dz g z θ| * (Work.Spaces.w z
        / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.Dz g z θ * (Work.Spaces.w z
          / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
    rw [← h5]
    exact pow_le_pow_left₀ (mul_nonneg hw (abs_nonneg _)) hle 2
  have hdep : (Work.Spaces.w z) ^ 2 * (Work.Spaces.Dz g z θ) ^ 2
      = (Work.Spaces.w z * |Work.Spaces.Dz g z θ|) ^ 2 := by rw [mul_pow, sq_abs]
  rw [hdep]
  refine le_trans hstep ?_
  have hslot := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 1 (by norm_num)
  simpa [Work.Spaces.Dz, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hslot

/-! ## The three basis bounds -/

/-- **The `rl¹`-norm of `g` itself.** -/
theorem envG {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|))
      ≤ ENNReal.ofReal (2 * Work.Spaces.HkNorm α 4 g) := by
  have hslot : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w r) ^ 2 * (g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ := by
    intro r hr
    rw [restrict_Iθ_eq_Ioo]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => w2_sq_le_HkIntegrand α hr hθ)
  have hA : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|)
        ≤ ENNReal.ofReal (2 * (r / (1 + r) ^ 2) * Real.sqrt (Jfun α g r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    refine le_trans (mul_le_mul' le_rfl (ang_le_of_slot hα hsm hmem
      (fun r hr => slice_aem_of_smoothQuad hsm hr) hslot hr0)) ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : r⁻¹ * (2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r)
        = 2 * (r / (1 + r) ^ 2) * Real.sqrt (Jfun α g r) := by
      rw [Work.Spaces.w]
      field_simp
    rw [heq]
  have hmain := radial_of_sqrt (J := Jfun α g) (A := fun r : ℝ => ENNReal.ofReal r⁻¹ *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|)) (c := 2)
    (by norm_num) (Jfun_integrableOn hmem) (Jfun_nonneg α g) hA
  rw [← HkSq_eq_Ioi α g] at hmain
  simpa [Work.Spaces.HkNorm] using hmain

/-- **The `rl¹`-norm of `D_z g`.** -/
theorem envDz {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.Dz g r θ|))
      ≤ ENNReal.ofReal (2 * Work.Spaces.HkNorm α 4 g) := by
  have hsm2 : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) :=
    Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hsm
  have hslot : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w r) ^ 2 * (Work.Spaces.Dz g r θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g r θ := by
    intro r hr
    rw [restrict_Iθ_eq_Ioo]
    exact ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => w2_Dz_sq_le_HkIntegrand α hr hθ)
  have hA : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.Dz g r θ|)
        ≤ ENNReal.ofReal (2 * (r / (1 + r) ^ 2) * Real.sqrt (Jfun α g r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    refine le_trans (mul_le_mul' le_rfl (ang_le_of_slot hα hsm hmem
      (fun r hr => slice_aem_of_smoothQuad hsm2 hr) hslot hr0)) ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : r⁻¹ * (2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r)
        = 2 * (r / (1 + r) ^ 2) * Real.sqrt (Jfun α g r) := by
      rw [Work.Spaces.w]
      field_simp
    rw [heq]
  have hmain := radial_of_sqrt (J := Jfun α g) (A := fun r : ℝ => ENNReal.ofReal r⁻¹ *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.Dz g r θ|)) (c := 2)
    (by norm_num) (Jfun_integrableOn hmem) (Jfun_nonneg α g) hA
  rw [← HkSq_eq_Ioi α g] at hmain
  simpa [Work.Spaces.HkNorm] using hmain


end Work.FTS.Nonlinear.Pieces.rl1Tools
