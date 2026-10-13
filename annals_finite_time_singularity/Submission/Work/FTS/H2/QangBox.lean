/-
Copyright: work module for the Elgindi finite-time singularity project.

# Joint integrability of the `z`-differentiated angular moment (interior class)

This module proves the Fubini input of the identity

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`

of `Work.FTS.H2.QangDiff`, in the interior class `SmoothQuad g + HkMem α 4 g` (no analyticity
hypothesis):

* `HkIntegrand_joint_integrable`: the `ℋ⁴`-integrand of `g` is jointly integrable on
  `Iz × Iθ` for the product of the restrictions of Lebesgue measure (`Tonelli`, from the two
  halves of `HkMem α 4 g` and the continuity of the integrand on the open quadrant);
* `DzIter_sq_joint_integrable`: the square of `D_zⁱ g` is jointly integrable for `i ≤ 4`
  (domination by `HkIntegrand α 4 g`, since `w ≥ 1`);
* `QangBoxIntegrable`: on a box `uIoc a b ×ˢ uIoc 0 (π/2)` with `0 < a ≤ b` (and `j ≤ 3`), the
  joint integrand `(x,θ) ↦ Kθ(θ)·D_z^{j+1} g x θ / x` is integrable (domination by
  `(3/a)·((D_z^{j+1} g)² + 1)`, using `|Kθ| ≤ 3`, `1/x ≤ 1/a`), and so is its `θ`-integral,
  namely `x ↦ Qang g (j+1) x / x` (Fubini–Tonelli).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.QangAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The radial weight and the derivatives -/

/-- The radial weight is at least `1` (it is `(1 + 1/z)²`). -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-! ## Almost-everywhere statements on the quadrant and on a box -/

/-- A property which holds on the *open* quadrant holds almost everywhere on `Iz × Iθ` (the
complement is contained in the coordinate hyperplanes and the two angular endpoints). -/
theorem ae_prod_quad {p : ℝ × ℝ → Prop}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → p (z, θ)) :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p q := by
  have h1 : (MeasureTheory.volume.restrict Work.Spaces.Iz : Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici).symm
  have h2 : (MeasureTheory.volume.restrict Work.Spaces.Iθ : Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  rw [h1, h2, MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.ae_restrict_of_forall_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet ?_
  rintro ⟨z, θ⟩ hq
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq
  exact h z θ hq.1 hq.2.1 hq.2.2

/-- The same for the box `uIoc a b ×ˢ uIoc 0 (π/2)`, `a ≤ b`. -/
theorem ae_prod_box {a b : ℝ} (hab : a ≤ b) {p : ℝ × ℝ → Prop}
    (h : ∀ z θ : ℝ, z ∈ Set.uIoc a b → 0 < θ → θ < π / 2 → p (z, θ)) :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
      (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))), p q := by
  have h2 : (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc).symm
  rw [h2, MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.ae_restrict_of_forall_mem
    ((measurableSet_uIoc).prod isOpen_Ioo.measurableSet) ?_
  rintro ⟨z, θ⟩ hq
  simp only [Set.mem_prod, Set.mem_Ioo] at hq
  exact h z θ hq.1 hq.2.1 hq.2.2

/-! ## Joint integrability of the `ℋ⁴`-integrand -/

/-- The uncurried `ℋ⁴`-integrand of a `SmoothQuad` function is a.e. strongly measurable for the
product of the restrictions of Lebesgue measure. -/
theorem aesm_joint_HkIntegrand {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 g hsm)

/-- **`HkIntegrand α 4 g` is jointly integrable on the quadrant** for
`SmoothQuad g + HkMem α 4 g`, by Tonelli: both iterated integrals are the two halves of
`HkMem α 4 g`. -/
theorem HkIntegrand_joint_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have haesm := aesm_joint_HkIntegrand (α := α) hsm
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact hmem.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α 4 g z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  exact (Work.Spaces.integrable_prod_of_iterated hnn haesm hslice houter).1

/-! ## Joint integrability of the square of a `D_z`-iterate -/

/-- **`(D_zⁱ g)²` is jointly integrable on the quadrant** for `i ≤ 4`: it is dominated by
`HkIntegrand α 4 g` because `w ≥ 1` on `z > 0`. -/
theorem DzIter_sq_joint_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 4) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (HkIntegrand_joint_integrable hsm hmem) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((SmoothQuad.toSmoothOpen hsm).DzIter i).continuousOn.pow 2
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  · refine ae_prod_quad (fun z θ hz hθ1 hθ2 => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := sq_DzIter_le_HkIntegrand_div_w_sq α 4 g i hi hz ⟨hθ1, hθ2⟩
    have h2 : Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
      rw [div_le_iff₀ (pow_pos (w_pos hz) 2)]
      have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (one_le_w hz) 2
        simpa using h
      nlinarith [Work.Spaces.HkIntegrand_nonneg α 4 g z θ, hw2]
    linarith

/-! ## The joint integrand of the angular moment on a box -/

/-- The joint integrand `(x,θ) ↦ Kθ(θ)·D_z^{j+1} g x θ / x` is continuous on the open
quadrant. -/
theorem continuousOn_Ktheta_DzIter_div {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
      * Work.Spaces.DzIter j g p.1 p.2 / p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (continuousOn_Ktheta_DzIter hsm j).div continuousOn_fst (fun p hp => ne_of_gt hp.1)

/-- **Joint integrability on a box, and of its `θ`-integral.**  For `0 < a ≤ b` and `j ≤ 3`,

* the joint integrand `(x,θ) ↦ Kθ(θ)·D_z^{j+1} g x θ / x` is integrable on the box
  `uIoc a b ×ˢ uIoc 0 (π/2)` (this is the Fubini hypothesis);
* its `θ`-integral `x ↦ Qang g (j+1) x / x` is integrable on `uIoc a b`. -/
theorem QangBoxIntegrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 3) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2)) ∧
      MeasureTheory.IntegrableOn (fun x : ℝ => Work.Elliptic.Qang g (j + 1) x / x)
        (Set.uIoc a b) := by
  have hsub1 : Set.uIoc a b ⊆ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.uIoc_of_le hab]
    exact fun x hx => le_of_lt (lt_trans ha hx.1)
  have hsub2 : Set.uIoc 0 (π / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    exact fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hle : (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono (Set.prod_mono hsub1 hsub2) le_rfl
  have hD2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter (j + 1) g p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    (DzIter_sq_joint_integrable hsm hmem (by omega)).mono_measure hle
  have hconst : MeasureTheory.Integrable (fun _ : ℝ × ℝ => (1 : ℝ))
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) := by
    have hne : ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) Set.univ ≠ ⊤ := by
      rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod,
        MeasureTheory.Measure.restrict_apply_univ, MeasureTheory.Measure.restrict_apply_univ,
        Set.uIoc_of_le hab, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2),
        Real.volume_Ioc, Real.volume_Ioc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    simpa only [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_univ] using
      (MeasureTheory.integrableOn_const (μ := (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) (s := Set.univ) (C := (1 : ℝ)) hne)
  -- the a.e. domination of the joint integrand
  have haesmF : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_Ktheta_DzIter_div hsm (j + 1))).mono_measure hle
  have hdom : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
      (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))),
      ‖Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1‖
        ≤ (3 / a) * ((Work.Spaces.DzIter (j + 1) g p.1 p.2) ^ 2 + 1) := by
    refine ae_prod_box hab (fun z θ hz hθ1 hθ2 => ?_)
    have hzpos : 0 < z := by
      rw [Set.uIoc_of_le hab] at hz
      exact lt_trans ha hz.1
    have haz : a ≤ z := by
      rw [Set.uIoc_of_le hab] at hz
      exact hz.1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hzpos, abs_mul]
    have hD1 : |Work.Spaces.DzIter (j + 1) g z θ|
        ≤ (Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|Work.Spaces.DzIter (j + 1) g z θ| - 1),
        sq_abs (Work.Spaces.DzIter (j + 1) g z θ),
        abs_nonneg (Work.Spaces.DzIter (j + 1) g z θ)]
    have hDnn : 0 ≤ |Work.Spaces.DzIter (j + 1) g z θ| := abs_nonneg _
    have h1 : |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter (j + 1) g z θ| / z
        ≤ 3 * |Work.Spaces.DzIter (j + 1) g z θ| / z :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (abs_Ktheta_le_three θ) hDnn) hzpos.le
    have h2 : 3 * |Work.Spaces.DzIter (j + 1) g z θ| / z
        ≤ 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / z :=
      div_le_div_of_nonneg_right (by linarith) hzpos.le
    have h3 : 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / z
        ≤ 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / a :=
      div_le_div_of_nonneg_left (by positivity) ha haz
    have h4 : 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / a
        = (3 / a) * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) := by ring
    linarith [h1, h2, h3, h4.le, h4.ge]
  have hFbox : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    MeasureTheory.Integrable.mono' ((hD2.add hconst).const_mul (3 / a)) haesmF hdom
  refine ⟨?_, ?_⟩
  · have hvol : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2))
        = (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
          (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2))) := by
      rw [MeasureTheory.Measure.prod_restrict]
      rfl
    show MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2)))
    rw [hvol]
    exact hFbox
  · have h1 : MeasureTheory.Integrable
        (fun x : ℝ => ∫ θ, (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
            * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1) (x, θ)
          ∂(MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2))))
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
      MeasureTheory.Integrable.integral_prod_left hFbox
    have hset : Set.uIoc 0 (π / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ := by
      rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2), Work.Spaces.Iθ]
      exact MeasureTheory.Ioc_ae_eq_Icc
    refine h1.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun x hx => ?_)
    have hxpos : 0 < x := by
      rw [Set.uIoc_of_le hab] at hx
      exact lt_trans ha hx.1
    change (∫ θ in Set.uIoc 0 (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ / x)
      = Work.Elliptic.Qang g (j + 1) x / x
    rw [MeasureTheory.setIntegral_congr_set hset, MeasureTheory.integral_div]
    rfl

end Work.FTS.H2
