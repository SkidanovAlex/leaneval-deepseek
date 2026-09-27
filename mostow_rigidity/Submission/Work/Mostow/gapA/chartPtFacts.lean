import Mathlib
import Submission.Work.Mostow.gapA.slabDefs

/-!
# The Fermi chart `chartPt a b B v w`: lift, axis coordinate and distance to the axis

Let `a b ∈ Sph 3`, `a ≠ b`, and let `B : AxisBasis a b` be a positive definite orthonormal
basis of the normal plane `NormSub a b` of the geodesic `geodSet a b`.  For `v : E 1`,
`w : E 2` the point of `ℍ³` with Fermi coordinates `(v, w)` around that geodesic is

  `axisPt_slabDefs a b B v w = cosh ‖w‖ • gcAxis a b (arsinh (v 0)) + sinhc ‖w‖ • (w 0 • B.E1 + w 1 • B.E2)`

as a vector on the hyperboloid, and `chartPt a b B v w` is its chart representation.  This file
collects the three structural facts about it:

* `chartPt_hlift` — `hlift (chartPt a b B v w) = axisPt_slabDefs a b B v w`, i.e. `axisPt_slabDefs` really is the
  hyperboloid lift of the chart point (the Minkowski self-pairing is `-1` and the time
  coordinate is positive, so `eq_hlift_of_upper` applies);
* `chartPt_sig` — the Busemann coordinate `sig a b u = (β_b u - β_a u)/2` along the axis is
  `arsinh (v 0)` (both horosphere levels pick up the same factor `cosh ‖w‖ · 2 κ L`, so the
  `v`-coordinate is read off directly);
* `chartPt_distGeod` — the distance to the geodesic is `‖w‖`.

The proofs are the Minkowski bilinear computations together with the standard parametrisation
`gcAxis` of the geodesic and its `lev` values (`mink_nvec_a_gcAxis`, `mink_nvec_b_gcAxis`).
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {a b : E 3}

/-! ## Elementary facts about `sinhc` -/

lemma chartPt_sinhc_mul_self (s : ℝ) : Submission.Mostow.sinhc s * s = Real.sinh s := by
  rw [Submission.Mostow.sinhc]
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ↓reduceIte]; field_simp

lemma chartPt_sinhc_sq_mul_sq (s : ℝ) :
    Submission.Mostow.sinhc s ^ 2 * s ^ 2 = Real.sinh s ^ 2 := by
  rw [← mul_pow, chartPt_sinhc_mul_self]

/-! ## The Minkowski pairings of the normal vector `w 0 • E1 + w 1 • E2` -/

lemma chartPt_mink_E1E2_self (B : AxisBasis a b) (w : E 2) :
    mink (w 0 • B.E1 + w 1 • B.E2) (w 0 • B.E1 + w 1 • B.E2) = ‖w‖ ^ 2 := by
  rw [mink_expand2, B.n11, B.n22, B.n12, mink_E2_E1]
  have hw : ‖w‖ ^ 2 = w 0 * w 0 + w 1 * w 1 := by
    rw [Hyper.norm_sq_eq_sum]; simp [Fin.sum_univ_two]
  rw [hw]; ring

lemma chartPt_mink_nvec_a_E1E2 (B : AxisBasis a b) (w : E 2) :
    mink (nvec a) (w 0 • B.E1 + w 1 • B.E2) = 0 := by
  rw [minkSeg_add_right, mink_smul_right'', mink_smul_right'', mink_a_E1, mink_a_E2]; ring

lemma chartPt_mink_nvec_b_E1E2 (B : AxisBasis a b) (w : E 2) :
    mink (nvec b) (w 0 • B.E1 + w 1 • B.E2) = 0 := by
  rw [minkSeg_add_right, mink_smul_right'', mink_smul_right'', mink_b_E1, mink_b_E2]; ring

/-- The normal vector is Minkowski orthogonal to the axis. -/
lemma chartPt_mink_gcAxis_E1E2 (B : AxisBasis a b) (s : ℝ) (w : E 2) :
    mink (gcAxis a b s) (w 0 • B.E1 + w 1 • B.E2) = 0 := by
  have hxa := chartPt_mink_nvec_a_E1E2 (a := a) (b := b) B w
  have hxb := chartPt_mink_nvec_b_E1E2 (a := a) (b := b) B w
  rw [gcAxis, mink_smul_left'', minkSeg_add_left, mink_smul_left'', mink_smul_left'', hxa, hxb]
  ring

/-! ## `axisPt_slabDefs` is a point of the upper sheet of the hyperboloid -/

/-- The Minkowski self-pairing of `axisPt_slabDefs` is `-1`. -/
lemma chartPt_mink_axisPt_self (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (v : E 1) (w : E 2) :
    mink (axisPt_slabDefs a b B v w) (axisPt_slabDefs a b B v w) = -1 := by
  have hN := chartPt_mink_E1E2_self (a := a) (b := b) B w
  have hAN := chartPt_mink_gcAxis_E1E2 (a := a) (b := b) B (Real.arsinh (v 0)) w
  have hNA : mink (w 0 • B.E1 + w 1 • B.E2) (gcAxis a b (Real.arsinh (v 0))) = 0 := by
    rw [minkSeg_comm]; exact hAN
  have hAx : mink (gcAxis a b (Real.arsinh (v 0))) (gcAxis a b (Real.arsinh (v 0))) = -1 := by
    rw [mink_gcAxis a b ha hb hab, sub_self, Real.cosh_zero]
  rw [axisPt_slabDefs, mink_expand2, hAx, hAN, hNA, hN]
  have hsq := chartPt_sinhc_sq_mul_sq ‖w‖
  have hc := Real.cosh_sq_sub_sinh_sq ‖w‖
  nlinarith [hsq, hc]

/-- The time coordinate of `axisPt_slabDefs` is positive. -/
lemma chartPt_axisPt_time_pos (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (v : E 1) (w : E 2) : 0 < axisPt_slabDefs a b B v w (Sum.inr 0) := by
  have hAx : mink (gcAxis a b (Real.arsinh (v 0))) (gcAxis a b (Real.arsinh (v 0))) = -1 := by
    rw [mink_gcAxis a b ha hb hab, sub_self, Real.cosh_zero]
  have hAN := chartPt_mink_gcAxis_E1E2 (a := a) (b := b) B (Real.arsinh (v 0)) w
  have hself := chartPt_mink_axisPt_self (a := a) (b := b) B ha hb hab v w
  have hneg : mink (hlift (gcAxisPt a b (Real.arsinh (v 0)))) (axisPt_slabDefs a b B v w) < 0 := by
    rw [hlift_gcAxisPt a b ha hb hab, axisPt_slabDefs, minkSeg_add_right, mink_smul_right'',
      mink_smul_right'', hAx, hAN]
    have := Real.cosh_pos ‖w‖
    linarith
  exact upper_of_mink_neg (gcAxisPt a b (Real.arsinh (v 0))) (axisPt_slabDefs a b B v w) hself hneg

/-- `axisPt_slabDefs` is the hyperboloid lift of its chart representation `chartPt`. -/
lemma chartPt_hlift (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (v : E 1) (w : E 2) :
    hlift (chartPt a b B v w) = axisPt_slabDefs a b B v w := by
  have h1 : mform (axisPt_slabDefs a b B v w) (axisPt_slabDefs a b B v w) = -1 := by
    rw [← mink_eq_mform]; exact chartPt_mink_axisPt_self B ha hb hab v w
  have h2 := chartPt_axisPt_time_pos B ha hb hab v w
  exact (eq_hlift_of_upper (axisPt_slabDefs a b B v w) h1 h2).symm

/-! ## Horosphere levels and the coordinates of `chartPt` -/

/-- The two horosphere levels `lev a`, `lev b` of `chartPt a b B v w`: the normal part drops out
(`mink (nvec a) (w 0 • E1 + w 1 • E2) = 0`) and only the axis `v`-coordinate survives. -/
lemma chartPt_lev (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (v : E 1) (w : E 2) :
    lev a (chartPt a b B v w)
        = Real.cosh ‖w‖ * (2 * gcK a b * gcL a b) * Real.exp (-(Real.arsinh (v 0))) ∧
    lev b (chartPt a b B v w)
        = Real.cosh ‖w‖ * (2 * gcK a b * gcL a b) * Real.exp (Real.arsinh (v 0)) := by
  have hU := chartPt_hlift B ha hb hab v w
  have hxa := chartPt_mink_nvec_a_E1E2 (a := a) (b := b) B w
  have hxb := chartPt_mink_nvec_b_E1E2 (a := a) (b := b) B w
  constructor
  · rw [lev_eq_neg_mink, hU, axisPt_slabDefs, minkSeg_add_right, mink_smul_right'', mink_smul_right'',
      mink_nvec_a_gcAxis a b ha hb hab, hxa]
    ring
  · rw [lev_eq_neg_mink, hU, axisPt_slabDefs, minkSeg_add_right, mink_smul_right'', mink_smul_right'',
      mink_nvec_b_gcAxis a b ha hb hab, hxb]
    ring

/-- The Busemann coordinate `sig` of `chartPt a b B v w` is `arsinh (v 0)`. -/
lemma chartPt_sig (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (v : E 1) (w : E 2) :
    sig a b (chartPt a b B v w) = Real.arsinh (v 0) := by
  obtain ⟨hla, hlb⟩ := chartPt_lev B ha hb hab v w
  set c := Real.cosh ‖w‖ * (2 * gcK a b * gcL a b) with hc
  have hcpos : 0 < c := by
    rw [hc]
    have h1 := Real.cosh_pos ‖w‖
    have h2 := gcK_pos a b ha hb hab
    have h3 := gcL_pos a b ha hb hab
    positivity
  have hloga : busemann a (chartPt a b B v w) = Real.log c - Real.arsinh (v 0) := by
    have h1 : Real.exp (busemann a (chartPt a b B v w))
        = c * Real.exp (-(Real.arsinh (v 0))) := by
      rw [← lev_eq_exp ha (chartPt a b B v w), hla]
    have h2 := congrArg Real.log h1
    rw [Real.log_exp, Real.log_mul hcpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
    linarith
  have hlogb : busemann b (chartPt a b B v w) = Real.log c + Real.arsinh (v 0) := by
    have h1 : Real.exp (busemann b (chartPt a b B v w)) = c * Real.exp (Real.arsinh (v 0)) := by
      rw [← lev_eq_exp hb (chartPt a b B v w), hlb]
    have h2 := congrArg Real.log h1
    rw [Real.log_exp, Real.log_mul hcpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
    linarith
  rw [sig, hloga, hlogb]; ring

/-- The distance to the geodesic `geodSet a b` of `chartPt a b B v w` is `‖w‖`. -/
lemma chartPt_distGeod (B : AxisBasis a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) (v : E 1) (w : E 2) :
    distGeod a b (chartPt a b B v w) = ‖w‖ := by
  obtain ⟨hla, hlb⟩ := chartPt_lev B ha hb hab v w
  have hL : gcL a b ≠ 0 := (gcL_pos a b ha hb hab).ne'
  have hk := gcK_sq_four a b ha hb hab
  have hexp : Real.exp (-(Real.arsinh (v 0))) * Real.exp (Real.arsinh (v 0)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hmain : lev a (chartPt a b B v w) * lev b (chartPt a b B v w) / gcL a b
      = Real.cosh ‖w‖ ^ 2 := by
    rw [hla, hlb, div_eq_iff hL]
    linear_combination
      (Real.cosh ‖w‖ ^ 2 * gcL a b * Real.exp (-(Real.arsinh (v 0)))
        * Real.exp (Real.arsinh (v 0))) * hk
      + (Real.cosh ‖w‖ ^ 2 * gcL a b) * hexp
  rw [distGeod_eq a b ha hb, hmain, Real.sqrt_sq (le_of_lt (Real.cosh_pos ‖w‖)),
    Real.arcosh_cosh (norm_nonneg w)]

/-! ## The statement -/

theorem chartPtFacts (a b : Submission.Mostow.E 3) (B : Work.Mostow.gapA.AxisBasis a b)
    (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (v : Submission.Mostow.E 1) (w : Submission.Mostow.E 2) :
    Submission.Mostow.hlift (Work.Mostow.gapA.chartPt a b B v w)
        = Work.Mostow.gapA.axisPt_slabDefs a b B v w ∧
    Work.Mostow.gapA.sig a b (Work.Mostow.gapA.chartPt a b B v w) = Real.arsinh (v 0) ∧
    Work.Mostow.distGeod a b (Work.Mostow.gapA.chartPt a b B v w) = ‖w‖ :=
  ⟨chartPt_hlift B ha hb hab v w, chartPt_sig B ha hb hab v w,
    chartPt_distGeod B ha hb hab v w⟩

end

end Work.Mostow.gapA
