import Submission.EquilibriumMeasure
import Submission.Serre
import Submission.SerreExample
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# 1/2-Hölder bound for the interval equilibrium measure

First analytic property of the potential machinery (weighted norms / Theorem
squarefree's Hölder hypothesis).  For the arcsine law on `[a,b]`,

    equilibrium a b (Set.Icc x y) ≤ C · √(y − x)      for a ≤ x ≤ y ≤ b

with an explicit constant `C` (any will do; e.g. `C = 4 / √(b − a)`).
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.EquilibriumHolder

open Submission.Equilibrium
open Submission.Serre
open Submission.SerreExample

/-! ## 1/2-Hölder estimates for `arcsin` -/

/-- For `0 ≤ φ ≤ θ ≤ π/2`, `sin θ − sin φ ≥ 2·((θ−φ)/π)²`. -/
lemma sin_sub_sin_ge_sq {θ φ : ℝ} (hφ0 : 0 ≤ φ) (hφθ : φ ≤ θ) (hθπ : θ ≤ Real.pi / 2) :
    2 * (((θ - φ) / Real.pi) ^ 2) ≤ Real.sin θ - Real.sin φ := by
  have hx0 : 0 ≤ (θ - φ) / 2 := by
    have : 0 ≤ θ - φ := sub_nonneg.mpr hφθ
    linarith
  have hxπ : (θ - φ) / 2 ≤ Real.pi / 2 := by
    have hδπ : θ - φ ≤ Real.pi / 2 := by linarith
    linarith
  have hsinx0 : 0 ≤ Real.sin ((θ - φ) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
  -- Jordan: sin((θ−φ)/2) ≥ (θ−φ)/π
  have hsinlow : (θ - φ) / Real.pi ≤ Real.sin ((θ - φ) / 2) := by
    have hj := Real.mul_le_sin hx0 hxπ
    have hnorm : (2 / Real.pi) * ((θ - φ) / 2) = (θ - φ) / Real.pi := by ring
    rwa [hnorm] at hj
  -- cos((θ+φ)/2) ≥ sin((θ−φ)/2)
  have hcosge : Real.sin ((θ - φ) / 2) ≤ Real.cos ((θ + φ) / 2) := by
    have hθ0 : 0 ≤ θ := le_trans hφ0 hφθ
    have hwle : (θ - φ) / 2 ≤ Real.pi / 2 - (θ + φ) / 2 := by
      linarith
    have hA : -(Real.pi / 2) ≤ (θ - φ) / 2 := by linarith
    have hB : Real.pi / 2 - (θ + φ) / 2 ≤ Real.pi / 2 := by
      have : 0 ≤ (θ + φ) / 2 := by linarith
      linarith
    have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two (x := (θ - φ) / 2)
      (y := Real.pi / 2 - (θ + φ) / 2) hA hB hwle
    simpa [Real.sin_pi_div_two_sub] using hmono
  calc
    2 * (((θ - φ) / Real.pi) ^ 2)
        ≤ 2 * (Real.sin ((θ - φ) / 2)) ^ 2 := by
          have hsq : ((θ - φ) / Real.pi) ^ 2 ≤ (Real.sin ((θ - φ) / 2)) ^ 2 := by
            have hnn1 : 0 ≤ (θ - φ) / Real.pi := by
              have : 0 ≤ θ - φ := sub_nonneg.mpr hφθ
              positivity
            have hsq' : |(θ - φ) / Real.pi| ≤ |Real.sin ((θ - φ) / 2)| := by
              rw [abs_of_nonneg hnn1, abs_of_nonneg hsinx0]
              exact hsinlow
            exact sq_le_sq.2 hsq'
          nlinarith
    _ ≤ 2 * (Real.sin ((θ - φ) / 2) * Real.cos ((θ + φ) / 2)) := by
          have hmul : Real.sin ((θ - φ) / 2) * Real.sin ((θ - φ) / 2) ≤
              Real.sin ((θ - φ) / 2) * Real.cos ((θ + φ) / 2) := by
            exact mul_le_mul_of_nonneg_left hcosge hsinx0
          nlinarith
    _ = Real.sin θ - Real.sin φ := by
          rw [Real.sin_sub_sin θ φ]
          ring

/-- 1/2-Hölder of `arcsin` on `[0,1]` (one-sided, constant `π`). -/
lemma arcsin_holder_nonneg {u v : ℝ} (hv0 : 0 ≤ v) (hvu : v ≤ u) (hu1 : u ≤ 1) :
    Real.arcsin u - Real.arcsin v ≤ Real.pi * Real.sqrt (u - v) := by
  have hu0 : 0 ≤ u := le_trans hv0 hvu
  have hum1 : -1 ≤ u := by linarith
  have hvm1 : -1 ≤ v := by linarith
  have hv1 : v ≤ 1 := le_trans hvu hu1
  have harc : Real.arcsin v ≤ Real.arcsin u := Real.arcsin_le_arcsin hvu
  have hθπ : Real.arcsin u ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two u
  have hφ0 : 0 ≤ Real.arcsin v := (Real.arcsin_nonneg).2 hv0
  set d : ℝ := Real.arcsin u - Real.arcsin v with hd
  have hsq_ge : 2 * ((d / Real.pi) ^ 2) ≤ Real.sin (Real.arcsin u) - Real.sin (Real.arcsin v) := by
    simpa [hd] using (sin_sub_sin_ge_sq hφ0 harc hθπ)
  have hsinu : Real.sin (Real.arcsin u) = u := Real.sin_arcsin hum1 hu1
  have hsinv : Real.sin (Real.arcsin v) = v := Real.sin_arcsin hvm1 hv1
  have hmain : 2 * ((d / Real.pi) ^ 2) ≤ u - v := by
    calc
      2 * ((d / Real.pi) ^ 2) ≤ Real.sin (Real.arcsin u) - Real.sin (Real.arcsin v) := hsq_ge
      _ = u - v := by rw [hsinu, hsinv]
  have hd0 : 0 ≤ d := by
    rw [hd]
    exact sub_nonneg.mpr harc
  have hnonneg_rhs : 0 ≤ u - v := sub_nonneg.mpr hvu
  have hsq_div : (d / Real.pi) ^ 2 * Real.pi ^ 2 = d ^ 2 := by
    field_simp [Real.pi_ne_zero]
  have hmul := mul_le_mul_of_nonneg_right hmain (sq_nonneg Real.pi)
  have hmain2 : 2 * d ^ 2 ≤ Real.pi ^ 2 * (u - v) := by
    have hnorm : 2 * ((d / Real.pi) ^ 2) * Real.pi ^ 2 = 2 * d ^ 2 := by
      calc
        2 * ((d / Real.pi) ^ 2) * Real.pi ^ 2 = 2 * (((d / Real.pi) ^ 2) * Real.pi ^ 2) := by ring
        _ = 2 * d ^ 2 := by rw [hsq_div]
    simpa [hnorm, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hsq_le : d ^ 2 ≤ Real.pi ^ 2 * (u - v) := by
    have hsq_nonneg : 0 ≤ d ^ 2 := sq_nonneg d
    nlinarith
  calc
    d ≤ Real.sqrt (Real.pi ^ 2 * (u - v)) := by
      exact (Real.le_sqrt hd0 (mul_nonneg (sq_nonneg Real.pi) hnonneg_rhs)).2 hsq_le
    _ = Real.pi * Real.sqrt (u - v) := by
      rw [Real.sqrt_mul (sq_nonneg Real.pi)]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt Real.pi_pos)]

/-- 1/2-Hölder of `arcsin` on `[-1,0]` (one-sided, constant `π`). -/
lemma arcsin_holder_nonpos {u v : ℝ} (hu0 : u ≤ 0) (hvu : v ≤ u) (hvm1 : -1 ≤ v) :
    Real.arcsin u - Real.arcsin v ≤ Real.pi * Real.sqrt (u - v) := by
  have hvu' : -u ≤ -v := by linarith
  have h0 : 0 ≤ -u := by linarith
  have h1 : -v ≤ 1 := by linarith
  have hmain := arcsin_holder_nonneg (u := -v) (v := -u) h0 hvu' h1
  have hneg1 : Real.arcsin (-v) = -Real.arcsin v := Real.arcsin_neg v
  have hneg2 : Real.arcsin (-u) = -Real.arcsin u := Real.arcsin_neg u
  have hmain2 : Real.arcsin u - Real.arcsin v ≤ Real.pi * Real.sqrt (u - v) := by
    have hL : Real.arcsin u - Real.arcsin v = -Real.arcsin v + Real.arcsin u := by ring
    have hclean2 : Real.arcsin u - Real.arcsin v ≤ Real.pi * Real.sqrt ((-v) - (-u)) := by
      simpa [hL, hneg1, hneg2] using hmain
    have harg : (-v) - (-u) = u - v := by ring
    rwa [harg] at hclean2
  exact hmain2

/-- 1/2-Hölder of `arcsin` for mixed signs `-1 ≤ v ≤ 0 ≤ u ≤ 1` (constant `2·π`). -/
lemma arcsin_holder_mixed {u v : ℝ} (hvm1 : -1 ≤ v) (hv0 : v ≤ 0) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.arcsin u - Real.arcsin v ≤ (2 * Real.pi) * Real.sqrt (u - v) := by
  have h1 : Real.arcsin u ≤ Real.pi * Real.sqrt u := by
    have h := arcsin_holder_nonneg (u := u) (v := 0) (by norm_num) hu0 hu1
    simpa [Real.arcsin_zero] using h
  have h2 : Real.arcsin (-v) ≤ Real.pi * Real.sqrt (-v) := by
    have h := arcsin_holder_nonneg (u := -v) (v := 0) (by norm_num) (by linarith) (by linarith)
    simpa [Real.arcsin_zero] using h
  have hsqrt_u : Real.sqrt u ≤ Real.sqrt (u - v) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrt_v : Real.sqrt (-v) ≤ Real.sqrt (u - v) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hu_le : Real.arcsin u ≤ Real.pi * Real.sqrt (u - v) := by
    calc
      Real.arcsin u ≤ Real.pi * Real.sqrt u := h1
      _ ≤ Real.pi * Real.sqrt (u - v) := by
        exact mul_le_mul_of_nonneg_left hsqrt_u (le_of_lt Real.pi_pos)
  have hv_le : Real.arcsin (-v) ≤ Real.pi * Real.sqrt (u - v) := by
    calc
      Real.arcsin (-v) ≤ Real.pi * Real.sqrt (-v) := h2
      _ ≤ Real.pi * Real.sqrt (u - v) := by
        exact mul_le_mul_of_nonneg_left hsqrt_v (le_of_lt Real.pi_pos)
  have hneg : Real.arcsin (-v) = -Real.arcsin v := Real.arcsin_neg v
  calc
    Real.arcsin u - Real.arcsin v = Real.arcsin u + Real.arcsin (-v) := by
      rw [hneg]
      ring
    _ ≤ Real.pi * Real.sqrt (u - v) + Real.pi * Real.sqrt (u - v) := add_le_add hu_le hv_le
    _ = (2 * Real.pi) * Real.sqrt (u - v) := by ring

/-- One-sided 1/2-Hölder of `arcsin` on `[-1,1]` (constant `2·π`). -/
lemma arcsin_holder_one {u v : ℝ} (hum1 : -1 ≤ u) (hu1 : u ≤ 1) (hvm1 : -1 ≤ v)
    (hv1 : v ≤ 1) (hvu : v ≤ u) :
    Real.arcsin u - Real.arcsin v ≤ (2 * Real.pi) * Real.sqrt (u - v) := by
  have hnonneg : 0 ≤ Real.sqrt (u - v) := Real.sqrt_nonneg (u - v)
  have hpi_le : Real.pi * Real.sqrt (u - v) ≤ (2 * Real.pi) * Real.sqrt (u - v) := by
    have : Real.pi ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
    exact mul_le_mul_of_nonneg_right this hnonneg
  by_cases hv0 : 0 ≤ v
  · have h := arcsin_holder_nonneg hv0 hvu hu1
    exact le_trans h hpi_le
  · have hvneg : v ≤ 0 := le_of_not_ge hv0
    by_cases hu0 : u ≤ 0
    · have h := arcsin_holder_nonpos hu0 hvu hvm1
      exact le_trans h hpi_le
    · have hu_nonneg : 0 ≤ u := le_of_not_ge hu0
      exact arcsin_holder_mixed hvm1 hvneg hu_nonneg hu1

/-- The 1/2-Hölder estimate of `arcsin` on `[-1,1]` (constant `2·π`). -/
lemma arcsin_sub_le {u v : ℝ} (hu : -1 ≤ u) (hu1 : u ≤ 1) (hv : -1 ≤ v) (hv1 : v ≤ 1) :
    |Real.arcsin u - Real.arcsin v| ≤ (2 * Real.pi) * Real.sqrt |u - v| := by
  by_cases hvu : v ≤ u
  · have h := arcsin_holder_one hu hu1 hv hv1 hvu
    have hnn : 0 ≤ Real.arcsin u - Real.arcsin v := sub_nonneg.mpr (Real.arcsin_le_arcsin hvu)
    have hnn2 : 0 ≤ u - v := sub_nonneg.mpr hvu
    rw [abs_of_nonneg hnn, abs_of_nonneg hnn2]
    exact h
  · have hltuv : u < v := lt_of_not_ge hvu
    have harc_lt : Real.arcsin u < Real.arcsin v := Real.arcsin_lt_arcsin hu hltuv hv1
    have h := arcsin_holder_one hv hv1 hu hu1 (le_of_not_ge hvu)
    calc
      |Real.arcsin u - Real.arcsin v| = -(Real.arcsin u - Real.arcsin v) := by
        rw [abs_of_neg]
        linarith
      _ = Real.arcsin v - Real.arcsin u := by ring
      _ ≤ (2 * Real.pi) * Real.sqrt (v - u) := h
      _ = (2 * Real.pi) * Real.sqrt |u - v| := by
        congr 1
        rw [abs_of_neg (by linarith : u - v < 0)]
        rw [neg_sub]

/-! ## The measure of a subinterval in chart parameters -/

/-- The normalized parameter `(t − (a+b)/2)/((b−a)/2)` of `t ∈ [a,b]` lies in `[−1,1]`. -/
def ucoord (a b : ℝ) (t : ℝ) : ℝ := (t - (a + b) / 2) / ((b - a) / 2)

/-- `ucoord a b t ∈ [−1,1]` when `t ∈ [a,b]`. -/
lemma ucoord_mem {a b t : ℝ} (hab : a < b) (hat : a ≤ t) (htb : t ≤ b) :
    ucoord a b t ∈ Set.Icc (-1) 1 := by
  unfold ucoord
  have hd : 0 < (b - a) / 2 := by linarith
  constructor
  · -- −1 ≤ (t − m)/d
    apply (le_div_iff₀ hd).2
    have h1 : -((b - a) / 2) ≤ t - (a + b) / 2 := by
      calc
        -((b - a) / 2) = a - (a + b) / 2 := by ring
        _ ≤ t - (a + b) / 2 := by linarith
    simpa using h1
  · -- (t − m)/d ≤ 1
    apply (div_le_iff₀ hd).2
    have h1 : t - (a + b) / 2 ≤ (b - a) / 2 := by
      calc
        t - (a + b) / 2 ≤ b - (a + b) / 2 := by linarith
        _ = (b - a) / 2 := by ring
    simpa using h1

/-- `ucoord` is monotone. -/
lemma ucoord_le {a b x y : ℝ} (hab : a < b) (hxy : x ≤ y) : ucoord a b x ≤ ucoord a b y := by
  unfold ucoord
  have hd : 0 < (b - a) / 2 := by linarith
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hd)

/-- For `w ∈ [0,π]`, `cos w ≤ c` implies `arccos c ≤ w` (cos decreases on `[0,π]`). -/
lemma arccos_le_of_cos_le {w c : ℝ} (hw0 : 0 ≤ w) (hwp : w ≤ Real.pi)
    (hcm : -1 ≤ c) (hc1 : c ≤ 1) (h : Real.cos w ≤ c) : Real.arccos c ≤ w := by
  by_contra hnot
  have hwlt : w < Real.arccos c := lt_of_not_ge hnot
  have hcc : Real.cos (Real.arccos c) = c := Real.cos_arccos hcm hc1
  have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi hw0 (Real.arccos_le_pi c) hwlt
  have : c < Real.cos w := by
    simpa [hcc] using hcoslt
  linarith

/-- For `w ∈ [0,π]`, `c ≤ cos w` implies `w ≤ arccos c` (cos decreases on `[0,π]`). -/
lemma arccos_ge_of_cos_ge {w c : ℝ} (hw0 : 0 ≤ w) (hwp : w ≤ Real.pi)
    (hcm : -1 ≤ c) (hc1 : c ≤ 1) (h : c ≤ Real.cos w) : w ≤ Real.arccos c := by
  by_contra hnot
  have hlt : Real.arccos c < w := lt_of_not_ge hnot
  have hcc : Real.cos (Real.arccos c) = c := Real.cos_arccos hcm hc1
  have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg c) hwp hlt
  have : Real.cos w < c := by
    simpa [hcc] using hcoslt
  linarith

/-- If `chart a b u ∈ [x,y]` with `u ∈ (0,1]` then `cos(πu) ∈ [ucoord x, ucoord y]`. -/
lemma chart_mem_cos {a b x y u : ℝ} (hab : a < b) (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b)
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) (hmem : chart a b u ∈ Set.Icc x y) :
    ucoord a b x ≤ Real.cos (Real.pi * u) ∧ Real.cos (Real.pi * u) ≤ ucoord a b y := by
  have hd : 0 < (b - a) / 2 := by linarith
  have hchart : chart a b u = (a + b) / 2 + ((b - a) / 2) * Real.cos (Real.pi * u) := by
    rfl
  constructor
  · have hxle : x ≤ (a + b) / 2 + ((b - a) / 2) * Real.cos (Real.pi * u) := by
      simpa [hchart] using hmem.1
    have hsub : x - (a + b) / 2 ≤ ((b - a) / 2) * Real.cos (Real.pi * u) := by linarith
    unfold ucoord
    rw [div_le_iff₀ hd]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsub
  · have hyge : (a + b) / 2 + ((b - a) / 2) * Real.cos (Real.pi * u) ≤ y := by
      simpa [hchart] using hmem.2
    have hsub : ((b - a) / 2) * Real.cos (Real.pi * u) ≤ y - (a + b) / 2 := by linarith
    unfold ucoord
    rw [le_div_iff₀ hd]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsub

/-- The preimage of `[x,y]` under the chart (restricted to `(0,1]`) sits inside the
interval `[arccos(ucoord y)/π, arccos(ucoord x)/π]`. -/
lemma chart_preimage_subset {a b x y : ℝ} (hab : a < b) (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    ((chart a b) ⁻¹' (Set.Icc x y)) ∩ Set.Ioc (0 : ℝ) 1 ⊆
      Set.Icc (Real.arccos (ucoord a b y) / Real.pi) (Real.arccos (ucoord a b x) / Real.pi) := by
  intro u hu
  have huS : chart a b u ∈ Set.Icc x y := hu.1
  have hu0 : 0 < u := hu.2.1
  have hu1 : u ≤ 1 := hu.2.2
  have hmem := chart_mem_cos hab hx hxy hy hu.2 huS
  have hux : ucoord a b x ≤ Real.cos (Real.pi * u) := hmem.1
  have huy : Real.cos (Real.pi * u) ≤ ucoord a b y := hmem.2
  have huxm : ucoord a b x ∈ Set.Icc (-1) 1 := ucoord_mem hab hx (le_trans hxy hy)
  have huym : ucoord a b y ∈ Set.Icc (-1) 1 := ucoord_mem hab (le_trans hx hxy) hy
  have hw0 : 0 ≤ Real.pi * u := mul_nonneg (le_of_lt Real.pi_pos) (le_of_lt hu0)
  have hwπ : Real.pi * u ≤ Real.pi := by
    calc
      Real.pi * u ≤ Real.pi * 1 := mul_le_mul_of_nonneg_left hu1 (le_of_lt Real.pi_pos)
      _ = Real.pi := by ring
  have hlo : Real.arccos (ucoord a b y) / Real.pi ≤ u := by
    have h1 : Real.arccos (ucoord a b y) ≤ Real.pi * u :=
      arccos_le_of_cos_le hw0 hwπ huym.1 huym.2 huy
    rw [div_le_iff₀ Real.pi_pos]
    simpa [mul_comm] using h1
  have hup : u ≤ Real.arccos (ucoord a b x) / Real.pi := by
    have h2 : Real.pi * u ≤ Real.arccos (ucoord a b x) :=
      arccos_ge_of_cos_ge hw0 hwπ huxm.1 huxm.2 hux
    rw [le_div_iff₀ Real.pi_pos]
    simpa [mul_comm] using h2
  exact ⟨hlo, hup⟩

/-- Mass of `[x,y]` under the equilibrium measure is at most
`(arccos(ucoord x) − arccos(ucoord y))/π`. -/
lemma equilibrium_le_arccos {a b x y : ℝ} (hab : a < b) (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    equilibrium a b (Set.Icc x y) ≤
      ENNReal.ofReal ((Real.arccos (ucoord a b x) - Real.arccos (ucoord a b y)) / Real.pi) := by
  unfold equilibrium
  have hmap : (Measure.map (chart a b) uniform01) (Set.Icc x y) =
      uniform01 ((chart a b) ⁻¹' (Set.Icc x y)) := by
    exact Measure.map_apply (chart_measurable a b) isClosed_Icc.measurableSet
  have hres : uniform01 ((chart a b) ⁻¹' (Set.Icc x y)) =
      volume (((chart a b) ⁻¹' (Set.Icc x y)) ∩ Set.Ioc (0 : ℝ) 1) := by
    unfold uniform01
    exact Measure.restrict_apply ((chart_measurable a b) (isClosed_Icc.measurableSet))
  have hmono : volume (((chart a b) ⁻¹' (Set.Icc x y)) ∩ Set.Ioc (0 : ℝ) 1) ≤
      volume (Set.Icc (Real.arccos (ucoord a b y) / Real.pi)
        (Real.arccos (ucoord a b x) / Real.pi)) := by
    exact MeasureTheory.measure_mono (μ := volume) (chart_preimage_subset hab hx hxy hy)
  have hvol : volume
      (Set.Icc (Real.arccos (ucoord a b y) / Real.pi) (Real.arccos (ucoord a b x) / Real.pi)) =
      ENNReal.ofReal ((Real.arccos (ucoord a b x) - Real.arccos (ucoord a b y)) / Real.pi) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  rw [hmap, hres]
  exact hmono.trans (le_of_eq hvol)

/-- The equilibrium measure of `[a,b]` gives mass `≤ C·√(y−x)` to any
subinterval `[x,y] ⊆ [a,b]` (with `0 < C` depending only on the interval). -/
theorem equilibrium_holder {a b x y : ℝ} (hab : a < b) (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    equilibrium a b (Set.Icc x y) ≤
      ENNReal.ofReal ((4 / Real.sqrt (b - a)) * Real.sqrt (y - x)) := by
  have hmeas := equilibrium_le_arccos hab hx hxy hy
  let ux : ℝ := ucoord a b x
  let uy : ℝ := ucoord a b y
  have hux_mem : ux ∈ Set.Icc (-1) 1 := by
    simpa [ux] using (ucoord_mem hab hx (le_trans hxy hy))
  have huy_mem : uy ∈ Set.Icc (-1) 1 := by
    simpa [uy] using (ucoord_mem hab (le_trans hx hxy) hy)
  have huxy : ux ≤ uy := by
    simpa [ux, uy] using ucoord_le hab hxy
  have hhold := arcsin_holder_one huy_mem.1 huy_mem.2 hux_mem.1 hux_mem.2 huxy
  have hA : (Real.arccos ux - Real.arccos uy) = Real.arcsin uy - Real.arcsin ux := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin ux, Real.arccos_eq_pi_div_two_sub_arcsin uy]
    ring
  have hB : (Real.arcsin uy - Real.arcsin ux) / Real.pi ≤ 2 * Real.sqrt (uy - ux) := by
    calc
      (Real.arcsin uy - Real.arcsin ux) / Real.pi
          ≤ ((2 * Real.pi) * Real.sqrt (uy - ux)) / Real.pi := by
            exact div_le_div_of_nonneg_right hhold (le_of_lt Real.pi_pos)
      _ = 2 * Real.sqrt (uy - ux) := by
            field_simp [Real.pi_ne_zero]
  have hC : 2 * Real.sqrt (uy - ux) ≤ (4 / Real.sqrt (b - a)) * Real.sqrt (y - x) := by
    have hBpos : 0 < b - a := sub_pos.mpr hab
    have hsqrtB : 0 < Real.sqrt (b - a) := Real.sqrt_pos.mpr hBpos
    have hd : 0 ≤ uy - ux := sub_nonneg.mpr huxy
    have hd' : 0 ≤ y - x := sub_nonneg.mpr hxy
    have hΔ : uy - ux = 2 * (y - x) / (b - a) := by
      simp only [ux, uy, ucoord]
      have hm : (y - (a + b) / 2) / ((b - a) / 2) - (x - (a + b) / 2) / ((b - a) / 2) =
          (y - x) / ((b - a) / 2) := by
        field_simp
        ring
      rw [hm]
      field_simp [(sub_ne_zero.mpr hab.ne)]
    have hsqL : (2 * Real.sqrt (uy - ux)) ^ 2 = (8 * (y - x)) / (b - a) := by
      calc
        (2 * Real.sqrt (uy - ux)) ^ 2 = 4 * (uy - ux) := by
          rw [mul_pow, Real.sq_sqrt hd]
          norm_num
        _ = (8 * (y - x)) / (b - a) := by
          rw [hΔ]
          field_simp [(sub_ne_zero.mpr hab.ne)]
          ring
    have hsqR : ((4 / Real.sqrt (b - a)) * Real.sqrt (y - x)) ^ 2 = (16 * (y - x)) / (b - a) := by
      calc
        ((4 / Real.sqrt (b - a)) * Real.sqrt (y - x)) ^ 2
            = (4 / Real.sqrt (b - a)) ^ 2 * (Real.sqrt (y - x)) ^ 2 := by
              rw [mul_pow]
        _ = (16 / (b - a)) * (y - x) := by
              congr 1
              · rw [div_pow, Real.sq_sqrt (le_of_lt hBpos)]
                norm_num
              · rw [Real.sq_sqrt hd']
        _ = (16 * (y - x)) / (b - a) := by ring
    have hsq : (2 * Real.sqrt (uy - ux)) ^ 2 ≤ ((4 / Real.sqrt (b - a)) * Real.sqrt (y - x)) ^ 2 := by
      rw [hsqL, hsqR]
      have hnn : 0 ≤ (y - x) / (b - a) := div_nonneg hd' (le_of_lt hBpos)
      calc
        (8 * (y - x)) / (b - a) = 8 * ((y - x) / (b - a)) := by ring
        _ ≤ 16 * ((y - x) / (b - a)) := mul_le_mul_of_nonneg_right (by norm_num) hnn
        _ = (16 * (y - x)) / (b - a) := by ring
    have hnnL : 0 ≤ 2 * Real.sqrt (uy - ux) := by positivity
    have hnnR : 0 ≤ (4 / Real.sqrt (b - a)) * Real.sqrt (y - x) :=
      mul_nonneg (div_nonneg (by norm_num) (le_of_lt hsqrtB)) (Real.sqrt_nonneg (y - x))
    have habs := (sq_le_sq).1 hsq
    have hLabs : |2 * Real.sqrt (uy - ux)| = 2 * Real.sqrt (uy - ux) := abs_of_nonneg hnnL
    have hRabs : |(4 / Real.sqrt (b - a)) * Real.sqrt (y - x)| =
        (4 / Real.sqrt (b - a)) * Real.sqrt (y - x) := abs_of_nonneg hnnR
    rwa [hLabs, hRabs] at habs
  have hreal : (Real.arccos ux - Real.arccos uy) / Real.pi ≤
      (4 / Real.sqrt (b - a)) * Real.sqrt (y - x) := by
    rw [hA]
    exact le_trans hB hC
  have hmeas' : equilibrium a b (Set.Icc x y) ≤
      ENNReal.ofReal ((Real.arccos ux - Real.arccos uy) / Real.pi) := by
    simpa [ux, uy] using hmeas
  exact hmeas'.trans (ENNReal.ofReal_le_ofReal hreal)


end Submission.EquilibriumHolder
