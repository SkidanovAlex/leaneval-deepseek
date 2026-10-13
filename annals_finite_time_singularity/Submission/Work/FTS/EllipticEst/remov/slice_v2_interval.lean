/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `(v'')²σ` coercivity bound on a bounded interval

`Work.FTS.EllipticEst.remov.slice_v2_interval`: with `v = u/cos θ`, `σ = sin(2θ)^{2-γ}`,
`1 ≤ γ ≤ 3/2`, `g = Lzero1 u` on `(0, π/2)`, `u 0 = u (π/2) = 0` and the four integrability
hypotheses of the statement,

`∫_{π/4}^{b} (v'')²σ ≤ C (∫(g')²σ + ∫(u'')²sEta + ∫(u')² + ∫u²)` for every `b ∈ (π/4, π/2)`.

The proof applies the weighted integration-by-parts identity `slice_ibp_w` on `[π/4, b]` and
bounds the four resulting terms by Cauchy–Schwarz, using the pointwise boundary bound
`slice_bd_ptwise` for the two boundary terms.
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.remov.slice_ibp_w
import Submission.Work.FTS.EllipticEst.remov.slice_Y2_le
import Submission.Work.FTS.EllipticEst.remov.slice_G2_le
import Submission.Work.FTS.EllipticEst.remov.slice_u_div_cos_sq_le
import Submission.Work.FTS.EllipticEst.remov.slice_bd_ptwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology Interval
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 8000000

/-! ## The two slope estimates for `σ` on `[π/4, π/2)` (from `slice_V2_le`) -/

/-- On `(0, π/2)`, `deriv (cos · σ) = σ · ((2-γ) cos 2θ / sin θ - sin θ)`. -/
private lemma deriv_cos_sgm (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ
      = Real.rpow (Real.sin (2 * θ)) (2 - γ)
          * ((2 - γ) * Real.cos (2 * θ) / Real.sin θ - Real.sin θ) := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have h1 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    rwa [show Real.cos (2 * θ) * (2 * 1) = 2 * Real.cos (2 * θ) from by ring] at h
  have h2 : HasDerivAt (fun t : ℝ => Real.rpow (Real.sin (2 * t)) (2 - γ))
      ((2 * Real.cos (2 * θ)) * (2 - γ) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1)) θ :=
    h1.rpow_const (Or.inl hsin2.ne')
  have h3 : HasDerivAt (fun t : ℝ => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ))
      ((-Real.sin θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + Real.cos θ * ((2 * Real.cos (2 * θ)) * (2 - γ)
            * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1))) θ :=
    (Real.hasDerivAt_cos θ).mul h2
  rw [h3.deriv]
  have hsplit : Real.rpow (Real.sin (2 * θ)) (2 - γ - 1) * Real.sin (2 * θ)
      = Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
    have h := Real.rpow_add hsin2 (2 - γ - 1) 1
    rw [Real.rpow_one (Real.sin (2 * θ))] at h
    rw [show (2 - γ - 1) + 1 = 2 - γ from by ring] at h
    exact h.symm
  have hkey : (2 * Real.cos θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1)
      = Real.rpow (Real.sin (2 * θ)) (2 - γ) / Real.sin θ := by
    have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    rw [eq_div_iff hsinθ.ne']
    rw [show (2 * Real.cos θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1) * Real.sin θ
        = (Real.sin (2 * θ)) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1) from by
          rw [Real.sin_two_mul]; ring,
      mul_comm (Real.sin (2 * θ)) (Real.rpow _ _), hsplit]
  rw [show (-Real.sin θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      + Real.cos θ * ((2 * Real.cos (2 * θ)) * (2 - γ)
          * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1))
      = Real.rpow (Real.sin (2 * θ)) (2 - γ)
          * ((2 - γ) * Real.cos (2 * θ) / Real.sin θ - Real.sin θ) from by
    rw [show Real.cos θ * ((2 * Real.cos (2 * θ)) * (2 - γ)
          * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1))
        = ((2 - γ) * Real.cos (2 * θ))
            * ((2 * Real.cos θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1)) from by ring,
      hkey]
    ring]

/-- The two slope estimates for `σ` on `[π/4, π/2)`: the coercivity coefficient
`4 sin θ σ + ½ (cos · σ)'` dominates `(3/2)σ`, and `|(cos · σ)'| ≤ 4σ`. -/
private lemma weight_facts (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    (3 / 2) * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ 4 * Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ
      ∧ |deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ|
          ≤ 4 * Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ'.1, by linarith [hθ'.2, Real.pi_pos]⟩
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hσpos : 0 < Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_pos_of_pos hsin2 _
  have hc2 : Real.cos (2 * θ) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos])
  have hc2le : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hg2γ : (2 - γ) ≤ 1 := by linarith
  have hg2γ0 : (0 : ℝ) < 2 - γ := by linarith
  have hsinθge : Real.sqrt 2 / 2 ≤ Real.sin θ := by
    have h1 : Real.sin (Real.pi / 4) ≤ Real.sin θ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [hθ.2]) hθ.1
    rwa [Real.sin_pi_div_four] at h1
  have hq : |(2 - γ) * Real.cos (2 * θ) / Real.sin θ| ≤ Real.sqrt 2 := by
    simp only [abs_div, abs_mul, abs_of_pos hg2γ0, abs_of_pos hsinθ]
    have h4 : (2 - γ) * |Real.cos (2 * θ)| ≤ 1 := by nlinarith [hc2le, hg2γ]
    have h5 : 1 / (Real.sqrt 2 / 2) = Real.sqrt 2 := by
      rw [div_div_eq_mul_div, one_mul, div_eq_iff (by positivity : Real.sqrt 2 ≠ 0)]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    calc (2 - γ) * |Real.cos (2 * θ)| / Real.sin θ
        ≤ 1 / Real.sin θ := div_le_div_of_nonneg_right h4 hsinθ.le
      _ ≤ 1 / (Real.sqrt 2 / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsinθge
      _ = Real.sqrt 2 := h5
  have hder := deriv_cos_sgm γ hθ'
  have hA : 4 * Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ
      = Real.rpow (Real.sin (2 * θ)) (2 - γ)
          * ((7 / 2) * Real.sin θ + ((2 - γ) * Real.cos (2 * θ) / Real.sin θ) / 2) := by
    rw [hder]; ring
  constructor
  · rw [hA]
    have hlow : (3 : ℝ) / 2 ≤ (7 / 2) * Real.sin θ
        + ((2 - γ) * Real.cos (2 * θ) / Real.sin θ) / 2 := by
      have h1 : (2 - γ) * Real.cos (2 * θ) / Real.sin θ ≥ -Real.sqrt 2 := by
        have := abs_le.mp hq; linarith [this.1]
      have h2 : (7 / 2) * Real.sin θ ≥ 7 / 2 * (Real.sqrt 2 / 2) :=
        mul_le_mul_of_nonneg_left hsinθge (by norm_num)
      have hs2 : (6 : ℝ) / 5 ≤ Real.sqrt 2 :=
        (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      have h3 : (7 : ℝ) / 2 * (Real.sqrt 2 / 2) = 7 * Real.sqrt 2 / 4 := by ring
      nlinarith [h1, h2, h3, hs2]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hlow hσpos.le
  · rw [hder, abs_mul, abs_of_pos hσpos]
    have hb : |(2 - γ) * Real.cos (2 * θ) / Real.sin θ - Real.sin θ| ≤ 4 := by
      have h1 := abs_le.mp hq
      have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
      have h2 : |(2 - γ) * Real.cos (2 * θ) / Real.sin θ - Real.sin θ|
          ≤ |(2 - γ) * Real.cos (2 * θ) / Real.sin θ| + |Real.sin θ| := abs_sub _ _
      rw [abs_of_pos hsinθ] at h2
      linarith [h1.1, h1.2, h2]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hb hσpos.le

/-! ## The assembly step, given the pointwise boundary bound -/

/-- On `Iθ`, `sin(2θ)^{-η} ≥ 0`. -/
private lemma sEta_nonneg' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

/-- Almost-everywhere nonnegativity on `Iθ` from pointwise nonnegativity. -/
private lemma ae_nonneg_forall_Iθ {f : ℝ → ℝ} (h : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ f x) :
    0 ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] f := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall h)

/-- `∫_{(π/4,b]} f ≤ ∫_{Iθ} f` for nonnegative `f`. -/
private lemma setIntegral_Ioc_le_Iθ {f : ℝ → ℝ} {b : ℝ} (hb2 : b ≤ Real.pi / 2)
    (hint : IntegrableOn f Work.Spaces.Iθ) (hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ f x) :
    (∫ x in Set.Ioc (Real.pi / 4) b, f x) ≤ ∫ x in Work.Spaces.Iθ, f x :=
  MeasureTheory.setIntegral_mono_set hint (ae_nonneg_forall_Iθ hnn)
    (Filter.Eventually.of_forall fun x hx =>
      ⟨le_trans (by linarith [Real.pi_pos]) hx.1.le, le_trans hx.2 hb2⟩)

/-- **Assembly step.**  Given the pointwise boundary bound `hbd` (the conclusion of
`slice_bd_ptwise`), deduce the `(v'')²σ` coercivity estimate on `(π/4, b)`. -/
private lemma slice_v2_interval_of_bd (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {Cbd : ℝ}
    (hCbd0 : 0 < Cbd)
    (hbd : ∀ (u g : ℝ → ℝ),
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Icc (Real.pi / 4) (Real.pi / 2),
        Real.rpow (Real.sin (2 * θ)) (2 - γ) * Real.cos θ *
          ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
            + (deriv (fun t => u t / Real.cos t) θ) ^ 2)
        ≤ Cbd * ((∫ x in Work.Spaces.Iθ, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
            + (∫ x in Work.Spaces.Iθ, (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x)
            + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2)
            + (∫ x in Work.Spaces.Iθ, (u x) ^ 2)
            + (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u g : ℝ → ℝ),
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      ∀ b ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (∫ θ in (Real.pi / 4)..b,
            (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨CG, hCG0, hG2lem⟩ := slice_G2_le γ hγ1 hγ2
  obtain ⟨CY, hCY0, hY2lem⟩ := slice_Y2_le γ hγ1 hγ2
  obtain ⟨CH, hCH0, hHVlem⟩ := slice_u_div_cos_sq_le γ hγ1 hγ2
  refine ⟨1 + (64 / 81) * (16 / 3 + (64 / 3) * CH + 2 * CY * (1 + CG) + Cbd * (1 + CG)),
    by positivity, ?_⟩
  intro u g hu hcont hu0 hupi hode hB hC1 hC0 hD b hb
  have hb1 : Real.pi / 4 < b := hb.1
  have hb2 : b < Real.pi / 2 := hb.2
  have ha1 : Real.pi / 4 ≤ b := hb.1.le
  have hbpi : b ≤ Real.pi / 2 := hb.2.le
  obtain ⟨hG2int, hG2bd⟩ := hG2lem u g hu hcont hu0 hupi hode hB hC1 hC0 hD
  obtain ⟨hY2int, hY2bd⟩ := hY2lem u g hu hcont hu0 hupi hode hG2int hB hC1 hC0
  obtain ⟨hVint, hVbd⟩ := hHVlem u hu hcont hu0 hupi hC1 hC0
  have hbd_b := hbd u g hu hcont hu0 hupi hode hB hC1 hC0 hD hG2int b ⟨ha1, hbpi⟩
  have hbd_a := hbd u g hu hcont hu0 hupi hode hB hC1 hC0 hD hG2int (Real.pi / 4)
    ⟨le_rfl, by linarith [hb1]⟩
  set J : Set ℝ := Set.Ioc (Real.pi / 4) b with hJ
  -- nonnegativity of the resources
  have hSgnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ Real.rpow (Real.sin (2 * x)) (2 - γ) := fun x hx =>
    Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩) _
  have hDnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x hx => mul_nonneg (sq_nonneg _) (hSgnn x hx)
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x hx =>
      mul_nonneg (sq_nonneg _) (sEta_nonneg' hx)
  have hC1nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x _ => sq_nonneg _
  have hC0nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x _ => sq_nonneg _
  have hG2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x hx => mul_nonneg (sq_nonneg _) (hSgnn x hx)
  -- the identity and its four pieces
  have hid := slice_ibp_w γ (Real.pi / 4) b hb1 (by linarith [Real.pi_pos]) hb2 hu hode
  simp only [intervalIntegral.integral_of_le ha1] at hid
  rw [← hJ] at hid
  have hJsub : J ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_trans (by linarith [Real.pi_pos]) hx.1.le, le_trans hx.2 hbpi⟩
  have hσJ : ∀ x ∈ J, 0 ≤ Real.rpow (Real.sin (2 * x)) (2 - γ) := fun x hx =>
    Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [(hJsub hx).1], by linarith [(hJsub hx).2, Real.pi_pos]⟩) _
  -- sizes
  set Q : ℝ := ∫ θ in J, (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ) with hQ
  set DJ : ℝ := ∫ θ in J, Real.rpow (Real.sin (2 * θ)) (2 - γ) * (deriv g θ) ^ 2 with hDJ
  set YJ : ℝ := ∫ θ in J, Real.rpow (Real.sin (2 * θ)) (2 - γ)
      * (deriv (fun t => u t / Real.cos t) θ) ^ 2 with hYJ
  set VJ : ℝ := ∫ θ in J, Real.rpow (Real.sin (2 * θ)) (2 - γ) * (u θ / Real.cos θ) ^ 2 with hVJ
  -- integrability facts on `J`
  have hσcont : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
    (Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ 2 - γ)).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hvC3 : ContDiffOn ℝ 3 (fun s => u s / Real.cos s) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn fun t ht => ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  have hvpp_cont : ContinuousOn
      (fun θ => deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) (Set.Icc (Real.pi / 4) b) := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hx.1, Real.pi_pos], lt_of_le_of_lt hx.2 hb2⟩
    have h3 : ContDiffAt ℝ 3 (fun s => u s / Real.cos s) x := hvC3.contDiffAt (isOpen_Ioo.mem_nhds hx')
    have h2 : ContDiffAt ℝ 2 (deriv (fun s => u s / Real.cos s)) x :=
      contDiffAt_deriv_of_le_w (m := 2) h3 (by norm_num)
    have h1 : ContDiffAt ℝ 0 (fun θ => deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) x :=
      contDiffAt_deriv_of_le_w (m := 0) h2 (by norm_num)
    exact (h1.continuousWithinAt).mono (Set.subset_univ _)
  have hvp_cont : ContinuousOn (fun θ => deriv (fun t => u t / Real.cos t) θ)
      (Set.Icc (Real.pi / 4) b) := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hx.1, Real.pi_pos], lt_of_le_of_lt hx.2 hb2⟩
    have h3 : ContDiffAt ℝ 3 (fun s => u s / Real.cos s) x := hvC3.contDiffAt (isOpen_Ioo.mem_nhds hx')
    have h1 : ContDiffAt ℝ 1 (deriv (fun s => u s / Real.cos s)) x :=
      contDiffAt_deriv_of_le_w (m := 1) h3 (by norm_num)
    exact (h1.continuousAt.continuousWithinAt).mono (Set.subset_univ _)
  have hu_cont : ContinuousOn u (Set.Icc (Real.pi / 4) b) :=
    hcont.mono fun x hx => ⟨le_trans (by linarith [Real.pi_pos]) hx.1, le_trans hx.2 hbpi⟩
  have hcos_cont : ContinuousOn (fun θ => u θ / Real.cos θ) (Set.Icc (Real.pi / 4) b) :=
    hu_cont.div Real.continuous_cos.continuousOn fun x hx => ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1, Real.pi_pos], lt_of_le_of_lt hx.2 hb2⟩)
  have hΦcont : ContinuousOn
      (fun θ => deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ)
      (Set.Icc (Real.pi / 4) b) := by
    have hder : ∀ x ∈ Set.Icc (Real.pi / 4) b,
        deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
          = Real.rpow (Real.sin (2 * x)) (2 - γ)
            * ((2 - γ) * Real.cos (2 * x) / Real.sin x - Real.sin x) := fun x hx =>
      deriv_cos_sgm γ ⟨by linarith [hx.1, Real.pi_pos], lt_of_le_of_lt hx.2 hb2⟩
    refine ContinuousOn.congr ?_ fun x hx => (hder x hx)
    have hratio : ContinuousOn (fun x : ℝ => (2 - γ) * Real.cos (2 * x) / Real.sin x)
        (Set.Icc (Real.pi / 4) b) :=
      ContinuousOn.div
        ((continuous_const.mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))).continuousOn)
        Real.continuous_sin.continuousOn
        (fun x hx => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, Real.pi_pos])
          (by linarith [hx.2, Real.pi_pos])))
    exact (hσcont.continuousOn).mul (hratio.sub Real.continuous_sin.continuousOn)
  have hInt_σvpp : IntegrableOn (fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ)
      * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2) J :=
    (ContinuousOn.integrableOn_Icc (hσcont.continuousOn.mul (hvpp_cont.pow 2))).mono_set
      (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hInt_σvp : IntegrableOn (fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ)
      * (deriv (fun t => u t / Real.cos t) θ) ^ 2) J :=
    (ContinuousOn.integrableOn_Icc (hσcont.continuousOn.mul (hvp_cont.pow 2))).mono_set
      (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hInt_σv : IntegrableOn (fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ)
      * (u θ / Real.cos θ) ^ 2) J :=
    (ContinuousOn.integrableOn_Icc (hσcont.continuousOn.mul (hcos_cont.pow 2))).mono_set
      (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hInt_Φ : IntegrableOn (fun θ =>
      deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ
      * (deriv (fun t => u t / Real.cos t) θ) ^ 2) J :=
    (ContinuousOn.integrableOn_Icc (hΦcont.mul (hvp_cont.pow 2))).mono_set
      (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hInt_Aσvpp : IntegrableOn (fun θ => (4 * Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ)
      * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2) J := by
    have hcont : ContinuousOn (fun θ => (4 * Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ)
        * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2)
        (Set.Icc (Real.pi / 4) b) :=
      (((continuous_const.mul Real.continuous_sin).mul hσcont).continuousOn.add
        (hΦcont.const_mul (1 / 2))).mul (hvpp_cont.pow 2)
    exact (ContinuousOn.integrableOn_Icc hcont).mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hInt_σg : IntegrableOn (fun θ => (deriv g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ)) J := hD.mono_set hJsub
  have hInt_σg' : IntegrableOn (fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ)
      * (deriv g θ) ^ 2) J := by
    refine hInt_σg.congr ?_
    filter_upwards with x
    ring
  -- pointwise Cauchy–Schwarz bounds (with the σ-weight)
  have hσnonneg : ∀ᵐ x ∂(volume : Measure ℝ).restrict J,
      0 ≤ Real.rpow (Real.sin (2 * x)) (2 - γ) := by
    rw [show J = Set.Ioc (Real.pi / 4) b from rfl,
      MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx => hσJ x hx
  -- `Q` versus `P`
  have hPQ : (3 / 2) * Q
      ≤ ∫ θ in J, (4 * Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ)
        * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 := by
    rw [hQ, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ hInt_Aσvpp ?_
    · rw [show J = Set.Ioc (Real.pi / 4) b from rfl]
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (hσJ x hx))
    · rw [show J = Set.Ioc (Real.pi / 4) b from rfl]
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hw := (weight_facts γ hγ1 hγ2 ⟨le_of_lt hx.1, lt_of_le_of_lt hx.2 hb2⟩).1
      have h2 : (0 : ℝ) ≤ (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2 :=
        sq_nonneg _
      nlinarith [hw, h2]
  -- the term bounds
  have hSbd : |∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
      * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
      ≤ (3 / 64) * (∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ)
          * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2) + (16 / 3) * DJ := by
    have h1 : |∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
        * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
        ≤ ∫ x in J, |Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
        * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x| := by
      rw [← Real.norm_eq_abs]
      exact MeasureTheory.norm_integral_le_integral_norm _
    have h2 : (∫ x in J, |Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
        * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|)
        ≤ ∫ x in J, ((3 / 64) * (Real.rpow (Real.sin (2 * x)) (2 - γ)
            * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2)
          + (16 / 3) * (Real.rpow (Real.sin (2 * x)) (2 - γ) * (deriv g x) ^ 2)) := by
      refine MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _)
        ((hInt_σvpp.const_mul _).add (hInt_σg'.const_mul _)) ?_
      rw [show J = Set.Ioc (Real.pi / 4) b from rfl]
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hσθ : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 - γ) := hσJ x hx
      have h3 : |Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
          * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
          = Real.rpow (Real.sin (2 * x)) (2 - γ) * |deriv g x|
            * |deriv (fun t => deriv (fun s => u s / Real.cos s) t) x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hσθ]
      rw [h3]
      have hkey : |deriv g x| * |deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
          ≤ (3 / 64) * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2
            + (16 / 3) * (deriv g x) ^ 2 := by
        nlinarith [sq_nonneg (3 * |deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
            - 32 * |deriv g x|), sq_abs (deriv g x),
          sq_abs (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x),
          abs_nonneg (deriv g x),
          abs_nonneg (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x)]
      have hmul := mul_le_mul_of_nonneg_left hkey hσθ
      nlinarith [hmul]
    have h3 : (∫ x in J, ((3 / 64) * (Real.rpow (Real.sin (2 * x)) (2 - γ)
            * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2)
          + (16 / 3) * (Real.rpow (Real.sin (2 * x)) (2 - γ) * (deriv g x) ^ 2)))
        = (3 / 64) * (∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ)
            * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2) + (16 / 3) * DJ := by
      rw [MeasureTheory.integral_add (hInt_σvpp.const_mul _) (hInt_σg'.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hDJ]
    linarith [h1, h2, h3.le, h3.ge]
  have hRbd : |∫ x in J, Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ)
      * (u x / Real.cos x) * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
      ≤ (3 / 64) * (∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ)
          * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2) + (16 / 3) * VJ := by
    have h1 : |∫ x in J, Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ)
        * (u x / Real.cos x) * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
        ≤ ∫ x in J, |Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ)
        * (u x / Real.cos x) * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x| := by
      rw [← Real.norm_eq_abs]
      exact MeasureTheory.norm_integral_le_integral_norm _
    have h2 : (∫ x in J, |Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ)
        * (u x / Real.cos x) * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|)
        ≤ ∫ x in J, ((3 / 64) * (Real.rpow (Real.sin (2 * x)) (2 - γ)
            * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2)
          + (16 / 3) * (Real.rpow (Real.sin (2 * x)) (2 - γ) * (u x / Real.cos x) ^ 2)) := by
      refine MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _)
        ((hInt_σvpp.const_mul _).add (hInt_σv.const_mul _)) ?_
      rw [show J = Set.Ioc (Real.pi / 4) b from rfl]
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hσθ : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 - γ) := hσJ x hx
      have hsθ : |Real.sin x| ≤ 1 := by
        rw [abs_of_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨(hJsub hx).1, by linarith [(hJsub hx).2, Real.pi_pos]⟩)]
        exact Real.sin_le_one x
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hσθ]
      have hkey : |Real.sin x| * |u x / Real.cos x|
            * |deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
          ≤ (3 / 64) * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2
            + (16 / 3) * (u x / Real.cos x) ^ 2 := by
        have h1 : |Real.sin x| * |u x / Real.cos x|
              * |deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
            ≤ |u x / Real.cos x|
              * |deriv (fun t => deriv (fun s => u s / Real.cos s) t) x| := by
          have h2 : |Real.sin x| * |u x / Real.cos x| ≤ 1 * |u x / Real.cos x| :=
            mul_le_mul_of_nonneg_right hsθ (abs_nonneg _)
          have h3 := mul_le_mul_of_nonneg_right h2
            (abs_nonneg (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x))
          simpa only [one_mul] using h3
        have h2 : |u x / Real.cos x| * |deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
            ≤ (3 / 64) * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2
              + (16 / 3) * (u x / Real.cos x) ^ 2 := by
          nlinarith [sq_nonneg (3 * |deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
              - 32 * |u x / Real.cos x|), sq_abs (u x / Real.cos x),
            sq_abs (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x),
            abs_nonneg (u x / Real.cos x),
            abs_nonneg (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x)]
        linarith
      have hmul := mul_le_mul_of_nonneg_left hkey hσθ
      nlinarith [hmul]
    have h3 : (∫ x in J, ((3 / 64) * (Real.rpow (Real.sin (2 * x)) (2 - γ)
            * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2)
          + (16 / 3) * (Real.rpow (Real.sin (2 * x)) (2 - γ) * (u x / Real.cos x) ^ 2)))
        = (3 / 64) * (∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ)
            * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2) + (16 / 3) * VJ := by
      rw [MeasureTheory.integral_add (hInt_σvpp.const_mul _) (hInt_σv.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hVJ]
    linarith [h1, h2, h3.le, h3.ge]
  have hTbd : |∫ x in J, deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
      * (deriv (fun t => u t / Real.cos t) x) ^ 2| ≤ 4 * YJ := by
    have h1 : |∫ x in J, deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
        * (deriv (fun t => u t / Real.cos t) x) ^ 2|
        ≤ ∫ x in J, |deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
        * (deriv (fun t => u t / Real.cos t) x) ^ 2| := by
      rw [← Real.norm_eq_abs]
      exact MeasureTheory.norm_integral_le_integral_norm _
    have h2 : (∫ x in J, |deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
        * (deriv (fun t => u t / Real.cos t) x) ^ 2|)
        ≤ ∫ x in J, 4 * (Real.rpow (Real.sin (2 * x)) (2 - γ)
          * (deriv (fun t => u t / Real.cos t) x) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _)
        (hInt_σvp.const_mul 4) ?_
      rw [show J = Set.Ioc (Real.pi / 4) b from rfl]
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hw := (weight_facts γ hγ1 hγ2 ⟨le_of_lt hx.1, lt_of_le_of_lt hx.2 hb2⟩).2
      have h3 : |deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
          * (deriv (fun t => u t / Real.cos t) x) ^ 2|
          = |deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x|
            * (deriv (fun t => u t / Real.cos t) x) ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv (fun t => u t / Real.cos t) x))]
      rw [h3]
      nlinarith [hw, sq_nonneg (deriv (fun t => u t / Real.cos t) x)]
    have h3 : (∫ x in J, 4 * (Real.rpow (Real.sin (2 * x)) (2 - γ)
          * (deriv (fun t => u t / Real.cos t) x) ^ 2)) = 4 * YJ := by
      rw [MeasureTheory.integral_const_mul, hYJ]
    linarith [h1, h2, h3.le, h3.ge]
  -- the boundary terms
  have hKb_le : Real.cos b * Real.rpow (Real.sin (2 * b)) (2 - γ)
      * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) b) ^ 2
        + (deriv (fun t => u t / Real.cos t) b) ^ 2)
      ≤ Cbd * ((∫ x in Work.Spaces.Iθ, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
        + (∫ x in Work.Spaces.Iθ, (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x)
        + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2)
        + (∫ x in Work.Spaces.Iθ, (u x) ^ 2)
        + (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))) := by
    refine le_trans (le_of_eq ?_) hbd_b
    ring
  have hKa_le : Real.cos (Real.pi / 4) * Real.rpow (Real.sin (2 * (Real.pi / 4))) (2 - γ)
      * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) (Real.pi / 4)) ^ 2
        + (deriv (fun t => u t / Real.cos t) (Real.pi / 4)) ^ 2)
      ≤ Cbd * ((∫ x in Work.Spaces.Iθ, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
        + (∫ x in Work.Spaces.Iθ, (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x)
        + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2)
        + (∫ x in Work.Spaces.Iθ, (u x) ^ 2)
        + (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))) := by
    refine le_trans (le_of_eq ?_) hbd_a
    ring
  -- `P ≤ ...` from the identity
  have hPle : (∫ x in J, (4 * Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ)
        + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x)
      * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2)
      ≤ |∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
            * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
        + 4 * |∫ x in J, Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ)
            * (u x / Real.cos x) * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x|
        + (1 / 2) * |∫ x in J, deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
            * (deriv (fun t => u t / Real.cos t) x) ^ 2|
        + (1 / 2) * |Real.cos b * Real.rpow (Real.sin (2 * b)) (2 - γ)
            * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) b) ^ 2
              + (deriv (fun t => u t / Real.cos t) b) ^ 2)|
        + (1 / 2) * |Real.cos (Real.pi / 4) * Real.rpow (Real.sin (2 * (Real.pi / 4))) (2 - γ)
            * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) (Real.pi / 4)) ^ 2
              + (deriv (fun t => u t / Real.cos t) (Real.pi / 4)) ^ 2)| := by
    have h1 : (∫ x in J, (4 * Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ)
        + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x)
      * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2)
        + (1 / 2) * (∫ x in J,
            deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
          * (deriv (fun t => u t / Real.cos t) x) ^ 2)
        + 4 * (∫ x in J, Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ) * (u x / Real.cos x)
          * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x)
        = (∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
            * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x)
          + (1 / 2) * (Real.cos b * Real.rpow (Real.sin (2 * b)) (2 - γ)
            * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) b) ^ 2
              + (deriv (fun t => u t / Real.cos t) b) ^ 2)
            - Real.cos (Real.pi / 4) * Real.rpow (Real.sin (2 * (Real.pi / 4))) (2 - γ)
            * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) (Real.pi / 4)) ^ 2
              + (deriv (fun t => u t / Real.cos t) (Real.pi / 4)) ^ 2)) := hid
    have h2 : (∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
        * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x)
        ≤ |∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
            * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x| := le_abs_self _
    have h3 : (∫ x in J,
          deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
        * (deriv (fun t => u t / Real.cos t) x) ^ 2)
        ≤ |∫ x in J, deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
            * (deriv (fun t => u t / Real.cos t) x) ^ 2| := le_abs_self _
    have h4 : (∫ x in J, Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ) * (u x / Real.cos x)
        * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x)
        ≤ |∫ x in J, Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ) * (u x / Real.cos x)
            * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x| := le_abs_self _
    set S : ℝ := ∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ) * deriv g x
      * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x with hSdef
    set T : ℝ := ∫ x in J, deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x
      * (deriv (fun t => u t / Real.cos t) x) ^ 2 with hTdef
    set R : ℝ := ∫ x in J, Real.sin x * Real.rpow (Real.sin (2 * x)) (2 - γ) * (u x / Real.cos x)
      * deriv (fun t => deriv (fun s => u s / Real.cos s) t) x with hRdef
    set Ab : ℝ := Real.cos b * Real.rpow (Real.sin (2 * b)) (2 - γ)
      * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) b) ^ 2
        + (deriv (fun t => u t / Real.cos t) b) ^ 2) with hAbdef
    set Aa : ℝ := Real.cos (Real.pi / 4) * Real.rpow (Real.sin (2 * (Real.pi / 4))) (2 - γ)
      * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) (Real.pi / 4)) ^ 2
        + (deriv (fun t => u t / Real.cos t) (Real.pi / 4)) ^ 2) with hAadef
    have hS' := le_abs_self S
    have hAb' := le_abs_self Ab
    have hAa' := neg_le_abs Aa
    have hT' := neg_le_abs T
    have hR' := neg_le_abs R
    linarith [h1, hS', hAb', hAa', hT', hR']
  -- the boundary terms in absolute value
  have hKabs : |Real.cos b * Real.rpow (Real.sin (2 * b)) (2 - γ)
      * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) b) ^ 2
        + (deriv (fun t => u t / Real.cos t) b) ^ 2)| ≤ Cbd
      * ((∫ x in Work.Spaces.Iθ, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
        + (∫ x in Work.Spaces.Iθ, (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x)
        + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2)
        + (∫ x in Work.Spaces.Iθ, (u x) ^ 2)
        + (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))) := by
    have hKnn : 0 ≤ Real.cos b * Real.rpow (Real.sin (2 * b)) (2 - γ)
        * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) b) ^ 2
          + (deriv (fun t => u t / Real.cos t) b) ^ 2) := by
      refine mul_nonneg (mul_nonneg (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hb1, Real.pi_pos], by linarith [hb2, Real.pi_pos]⟩).le
        (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hb1, Real.pi_pos], by linarith [hb2, Real.pi_pos]⟩) _))
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [abs_of_nonneg hKnn]
    exact hKb_le
  have hKaabs : |Real.cos (Real.pi / 4) * Real.rpow (Real.sin (2 * (Real.pi / 4))) (2 - γ)
      * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) (Real.pi / 4)) ^ 2
        + (deriv (fun t => u t / Real.cos t) (Real.pi / 4)) ^ 2)| ≤ Cbd
      * ((∫ x in Work.Spaces.Iθ, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
        + (∫ x in Work.Spaces.Iθ, (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x)
        + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2)
        + (∫ x in Work.Spaces.Iθ, (u x) ^ 2)
        + (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))) := by
    have hKann : 0 ≤ Real.cos (Real.pi / 4) * Real.rpow (Real.sin (2 * (Real.pi / 4))) (2 - γ)
        * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) (Real.pi / 4)) ^ 2
          + (deriv (fun t => u t / Real.cos t) (Real.pi / 4)) ^ 2) := by
      refine mul_nonneg (mul_nonneg (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).le
        (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) _))
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [abs_of_nonneg hKann]
    exact hKa_le
  -- the resources in terms of the four integrals
  have hDJle : DJ ≤ ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
    rw [hDJ]
    refine le_trans (setIntegral_Ioc_le_Iθ
      (f := fun x => Real.rpow (Real.sin (2 * x)) (2 - γ) * (deriv g x) ^ 2)
      hbpi (hD.congr (by filter_upwards with x; ring))
      (fun x hx => mul_nonneg (hSgnn x hx) (sq_nonneg _))) ?_
    exact le_of_eq (MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => by ring))
  have hYJle : YJ ≤ CY * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
    rw [hYJ]
    have hcmp : (∫ x in Set.Ioc (Real.pi / 4) b, Real.rpow (Real.sin (2 * x)) (2 - γ)
        * (deriv (fun t => u t / Real.cos t) x) ^ 2)
        ≤ ∫ x in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 - γ) := by
      refine le_trans (setIntegral_Ioc_le_Iθ
        (f := fun x => Real.rpow (Real.sin (2 * x)) (2 - γ)
          * (deriv (fun t => u t / Real.cos t) x) ^ 2)
        hbpi (hY2int.congr (by filter_upwards with x; ring))
        (fun x hx => mul_nonneg (hSgnn x hx) (sq_nonneg _))) ?_
      exact le_of_eq (MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => by ring))
    exact le_trans hcmp hY2bd
  have hVJle : VJ ≤ CH * ((∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
    rw [hVJ]
    have hcmp : (∫ x in Set.Ioc (Real.pi / 4) b, Real.rpow (Real.sin (2 * x)) (2 - γ)
        * (u x / Real.cos x) ^ 2)
        ≤ ∫ x in Work.Spaces.Iθ, (u x / Real.cos x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 - γ) := by
      refine le_trans (setIntegral_Ioc_le_Iθ
        (f := fun x => Real.rpow (Real.sin (2 * x)) (2 - γ) * (u x / Real.cos x) ^ 2)
        hbpi (hVint.congr (by filter_upwards with x; ring))
        (fun x hx => mul_nonneg (hSgnn x hx) (sq_nonneg _))) ?_
      exact le_of_eq (MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => by ring))
    exact le_trans hcmp hVbd
  -- the main inequality
  have hmain : (3 / 2) * Q ≤ (3 / 64) * Q + (16 / 3) * DJ
      + 4 * ((3 / 64) * Q + (16 / 3) * VJ) + (1 / 2) * (4 * YJ)
      + (1 / 2) * (Cbd * ((∫ x in Work.Spaces.Iθ, (deriv g x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 - γ))
          + (∫ x in Work.Spaces.Iθ, (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x)
          + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2)
          + (∫ x in Work.Spaces.Iθ, (u x) ^ 2)
          + (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))
        + Cbd * ((∫ x in Work.Spaces.Iθ, (deriv g x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 - γ))
          + (∫ x in Work.Spaces.Iθ, (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x)
          + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2)
          + (∫ x in Work.Spaces.Iθ, (u x) ^ 2)
          + (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))) := by
    refine le_trans hPQ ?_
    refine le_trans hPle ?_
    have hQe : (∫ x in J, Real.rpow (Real.sin (2 * x)) (2 - γ)
        * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2) = Q := by
      rw [hQ]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      ring
    have h1 := hSbd
    have h2 := hRbd
    have h3 := hTbd
    rw [hQe] at h1 h2
    linarith [h1, h2, h3, hKabs, hKaabs]
  -- final arithmetic
  have hG2le : (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
      ≤ CG * ((∫ x in Work.Spaces.Iθ, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
        + (∫ x in Work.Spaces.Iθ, (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x)
        + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2)
        + (∫ x in Work.Spaces.Iθ, (u x) ^ 2)) := hG2bd
  set RG : ℝ := (∫ x in Work.Spaces.Iθ, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
      + (∫ x in Work.Spaces.Iθ, (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x)
      + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2)
      + (∫ x in Work.Spaces.Iθ, (u x) ^ 2) with hRG
  have hRGnn : 0 ≤ RG := by
    rw [hRG]; linarith [hDnn, hBnn, hC1nn, hC0nn]
  have hRle : RG + (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
      ≤ (1 + CG) * RG := by
    have h := hG2le
    rw [hRG] at h ⊢
    linarith [h, hDnn, hBnn, hC1nn, hC0nn]
  have hQfin : Q ≤ (64 / 81) * (16 / 3 + (64 / 3) * CH + 2 * CY * (1 + CG)
      + Cbd * (1 + CG)) * RG := by
    have hTB : 4 * YJ ≤ 4 * (CY * (1 + CG) * RG) := by
      have h1 : YJ ≤ CY * (1 + CG) * RG := by
        refine le_trans hYJle ?_
        rw [hRG]
        have h0 : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))
            ≤ (1 + CG) * ((∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 - γ))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
          nlinarith [hG2bd, hDnn, hBnn, hC1nn, hC0nn]
        nlinarith [h0, hCY0, hCG0]
      nlinarith [h1, hCY0, hCG0, hRGnn]
    have hVB : VJ ≤ CH * RG := by
      refine le_trans hVJle ?_
      rw [hRG]
      nlinarith [hCH0, hC1nn, hC0nn, hDnn, hBnn]
    have hKB : Cbd * (RG + (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))
        ≤ Cbd * (1 + CG) * RG := by
      nlinarith [hRle, hCbd0, hRGnn]
    have hDJle' : DJ ≤ RG := by
      rw [hRG]
      linarith [hDJle, hBnn, hC1nn, hC0nn]
    have hTB' : 2 * YJ ≤ 2 * (CY * (1 + CG) * RG) := by linarith [hTB]
    have e5 : (81 / 64) * Q ≤ (16 / 3) * DJ + (64 / 3) * VJ + 2 * YJ
        + Cbd * (RG + (∫ x in Work.Spaces.Iθ,
            (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))) := by
      rw [hRG] at hmain ⊢
      linarith [hmain]
    have e1 : (16 / 3) * DJ ≤ (16 / 3) * RG := mul_le_mul_of_nonneg_left hDJle' (by norm_num)
    have e2 : (64 / 3) * VJ ≤ (64 / 3) * (CH * RG) :=
      mul_le_mul_of_nonneg_left hVB (by norm_num)
    have e4 : Cbd * (RG + (∫ x in Work.Spaces.Iθ,
          (g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))
        ≤ Cbd * (1 + CG) * RG := hKB
    have e6 := add_le_add (add_le_add (add_le_add e1 e2) hTB') e4
    have e7 : (16 / 3) * RG + (64 / 3) * (CH * RG)
        + 2 * (CY * (1 + CG) * RG) + Cbd * (1 + CG) * RG
        = (16 / 3 + (64 / 3) * CH + 2 * CY * (1 + CG) + Cbd * (1 + CG)) * RG := by ring
    rw [e7] at e6
    have hsum : (81 / 64) * Q
        ≤ (16 / 3 + (64 / 3) * CH + 2 * CY * (1 + CG) + Cbd * (1 + CG)) * RG :=
      le_trans e5 e6
    calc Q = (64 / 81) * ((81 / 64) * Q) := by ring
      _ ≤ (64 / 81) * ((16 / 3 + (64 / 3) * CH + 2 * CY * (1 + CG) + Cbd * (1 + CG)) * RG) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (64 / 81) * (16 / 3 + (64 / 3) * CH + 2 * CY * (1 + CG) + Cbd * (1 + CG)) * RG := by
          ring
  -- transfer to the interval integral of the statement
  have hQint : (∫ θ in (Real.pi / 4)..b,
      (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - γ)) = Q := by
    rw [hQ, intervalIntegral.integral_of_le ha1]
  rw [hQint]
  have hCpos : (0:ℝ) < 1 + (64 / 81) * (16 / 3 + (64 / 3) * CH + 2 * CY * (1 + CG) + Cbd * (1 + CG)) :=
    by positivity
  have hfin : (64 / 81) * (16 / 3 + (64 / 3) * CH + 2 * CY * (1 + CG) + Cbd * (1 + CG))
      ≤ 1 + (64 / 81) * (16 / 3 + (64 / 3) * CH + 2 * CY * (1 + CG) + Cbd * (1 + CG)) :=
    le_add_of_nonneg_left zero_le_one
  exact le_trans hQfin (mul_le_mul_of_nonneg_right hfin hRGnn)

theorem slice_v2_interval (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u g : ℝ → ℝ),
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      ∀ b ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (∫ θ in (Real.pi / 4)..b,
            (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨CY, hCY0, hY2lem⟩ := slice_Y2_le γ hγ1 hγ2
  obtain ⟨Cbd, hCbd0, hbd5⟩ := slice_bd_ptwise γ hγ1 hγ2
  obtain ⟨C, hC, hmain⟩ := slice_v2_interval_of_bd γ hγ1 hγ2 hCbd0
    (fun u g hu hcont hu0 hupi hode hB hC1 hC0 hD hG2 θ hθ => by
      obtain ⟨hY2int, -⟩ := hY2lem u g hu hcont hu0 hupi hode hG2 hB hC1 hC0
      exact hbd5 u g hu hcont hu0 hupi hode hB hC1 hC0 hD hG2 hY2int θ hθ)
  exact ⟨C, hC, hmain⟩

end

end Work.FTS.EllipticEst.remov
