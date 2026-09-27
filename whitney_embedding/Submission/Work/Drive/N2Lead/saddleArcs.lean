import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.windowBallTarget
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2Lead.saddlePinDefs

/-!
# The two model arcs of a level of the saddle window, as points of `M`

`NOTES_LEAD_saddlePacket.md` §1.2/§1.3.  At the level `f = f p - lam0² * η` (with `lam0 = ρ j / 8`)
the two arcs of the anchor hyperbola are, in the *scaled* chart coordinate `Z` (where the complex
chart coordinate of the datum satisfies `Zs = lam0 * Z`), the solutions of

  `Z ^ 2 = -η + I * w`,   `|w| ≤ m`,

i.e. `Z = ± arcZ η w` with `arcZ η w = I * sqrt (η - I * w)`.  This file provides

* `cE2` / `cplxE2` — the plane point of a complex number and back;
* `arcZ` and its square and norm rows;
* `saddlePin_eq_scaled` — the pin set in scaled coordinates;
* `arcUpPt` / `arcDnPt` — the two arcs as points of `M` (through `(φ j).symm`), with the rows
  `Z (arcUpPt) = arcZ η w`, `f (arcUpPt) = f p - lam0² * η` and `arcUpPt ∈ saddlePin D _ m`;
* `pin_eq_arc` — **the characterisation of the pin**: every point of the pin at the anchor level is
  one of the two arc points.

The hypothesis `‖arcZ η w‖ < 8` (equivalently `lam0 * ‖arcZ η w‖ < ρ j`) puts the chart vector in the
chart's target (through `Work.Drive.N2.windowBall_subset_target`); it is discharged by the numeric
estimates of the core, uniformly for `|w| ≤ m` and small `η`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-! ## The plane coordinates -/

/-- The plane point of a complex number. -/
def cE2 (z : ℂ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z.re, z.im]

/-- The complex number of a plane point. -/
def cplxE2 (v : EuclideanSpace ℝ (Fin 2)) : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I

lemma cplxE2_cE2 (z : ℂ) : cplxE2 (cE2 z) = z := by
  refine Complex.ext ?_ ?_ <;> simp [cplxE2, cE2]

lemma cE2_cplxE2 (v : EuclideanSpace ℝ (Fin 2)) : cE2 (cplxE2 v) = v := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i <;> simp [cplxE2, cE2]

lemma cE2_injective : Function.Injective cE2 := fun z w h => by
  have h' := congrArg cplxE2 h
  rwa [cplxE2_cE2, cplxE2_cE2] at h'

/-- The imaginary part of the square of `u + I v`. -/
lemma sq_im_of_pair (u v : ℝ) :
    ((((u : ℂ) + (v : ℂ) * Complex.I)) ^ 2).im = 2 * u * v := by
  rw [pow_two, Complex.mul_im]
  simp
  ring

lemma cE2_norm (z : ℂ) : ‖cE2 z‖ = ‖z‖ := by
  have h2 : ‖cE2 z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp only [cE2, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (cE2 z), norm_nonneg z]

lemma norm_cplxE2 (v : EuclideanSpace ℝ (Fin 2)) : ‖cplxE2 v‖ = ‖v‖ := by
  rw [← cE2_norm (cplxE2 v), cE2_cplxE2]

/-! ## The model arc `Z ↦ I * sqrt (η - I w)` -/

/-- The model arc: the square root of `-η + I w` in the upper half-plane. -/
def arcZ (η w : ℝ) : ℂ := Complex.I * Complex.sqrt ((η : ℂ) - (w : ℂ) * Complex.I)

lemma complex_sqrt_sq' (x : ℂ) : Complex.sqrt x ^ 2 = x := by
  rw [Complex.sqrt]
  exact Complex.cpow_nat_inv_pow x (by norm_num)

lemma arcZ_sq (η w : ℝ) : (arcZ η w) ^ 2 = -(η : ℂ) + (w : ℂ) * Complex.I := by
  rw [arcZ, mul_pow, complex_sqrt_sq']
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  rw [hI]
  ring

lemma arcZ_sq_re (η w : ℝ) : ((arcZ η w) ^ 2).re = -η := by
  rw [arcZ_sq]; simp

lemma arcZ_sq_im (η w : ℝ) : ((arcZ η w) ^ 2).im = w := by
  rw [arcZ_sq]; simp

/-- The squared modulus of the arc point, through its square: `‖arcZ η w‖² = sqrt (η² + w²)`. -/
lemma normSq_arcZ (η w : ℝ) : Complex.normSq (arcZ η w) = Real.sqrt (η ^ 2 + w ^ 2) := by
  have hre : (arcZ η w).re ^ 2 - (arcZ η w).im ^ 2 = -η := by
    have h := arcZ_sq_re η w
    rw [pow_two, Complex.mul_re] at h
    linarith
  have him : 2 * (arcZ η w).re * (arcZ η w).im = w := by
    have h := arcZ_sq_im η w
    rw [pow_two, Complex.mul_im] at h
    linarith
  have h2 : (Complex.normSq (arcZ η w)) ^ 2 = η ^ 2 + w ^ 2 := by
    rw [Complex.normSq_apply]
    have hsq : ((arcZ η w).re * (arcZ η w).re + (arcZ η w).im * (arcZ η w).im) ^ 2
        = ((arcZ η w).re * (arcZ η w).re - (arcZ η w).im * (arcZ η w).im) ^ 2
          + (2 * (arcZ η w).re * (arcZ η w).im) ^ 2 := by ring
    rw [hsq]
    have h1 : (arcZ η w).re * (arcZ η w).re - (arcZ η w).im * (arcZ η w).im = -η := by
      rw [← pow_two, ← pow_two]; exact hre
    rw [h1, him]
    ring
  have h4 : (Complex.normSq (arcZ η w)) ^ 2 = (Real.sqrt (η ^ 2 + w ^ 2)) ^ 2 := by
    rw [h2, Real.sq_sqrt (by positivity)]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h4 with h5 | h5
  · exact h5
  · have hx0 : Complex.normSq (arcZ η w) = 0 := by
      linarith [Complex.normSq_nonneg (arcZ η w), Real.sqrt_nonneg (η ^ 2 + w ^ 2)]
    have hy0 : Real.sqrt (η ^ 2 + w ^ 2) = 0 := by
      linarith [Complex.normSq_nonneg (arcZ η w), Real.sqrt_nonneg (η ^ 2 + w ^ 2)]
    rw [hx0, hy0]

lemma norm_arcZ_sq (η w : ℝ) : ‖arcZ η w‖ ^ 2 = Real.sqrt (η ^ 2 + w ^ 2) := by
  rw [← Complex.normSq_eq_norm_sq, normSq_arcZ]

lemma arcZ_norm_lt (η w : ℝ) (hη : |η| ≤ 1) (hw : |w| ≤ 2) : ‖arcZ η w‖ < 8 := by
  have h1 : ‖arcZ η w‖ ^ 2 ≤ 3 := by
    rw [norm_arcZ_sq]
    have h2 : η ^ 2 + w ^ 2 ≤ 5 := by
      nlinarith [sq_abs η, sq_abs w, abs_nonneg η, abs_nonneg w]
    calc Real.sqrt (η ^ 2 + w ^ 2) ≤ Real.sqrt 5 := Real.sqrt_le_sqrt h2
      _ ≤ 3 := by
          rw [Real.sqrt_le_iff]
          norm_num
  nlinarith [norm_nonneg (arcZ η w)]

/-! ## The pin set in scaled coordinates -/

section Datum

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- The complex number of the chart coordinates of the datum's marked chart. -/
def chartCplx {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (x : M) : ℂ :=
  cplxE2 (D.φ D.j x)

lemma chartCplx_apply {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (x : M) :
    chartCplx D x = (D.φ D.j x 0 : ℂ) + (D.φ D.j x 1 : ℂ) * Complex.I := rfl

lemma norm_chartCplx {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (x : M) :
    ‖chartCplx D x‖ = ‖D.φ D.j x‖ := norm_cplxE2 _

/-- **The pin set in scaled coordinates.**  With `Z` the scaled chart coordinate (`Zs = lam0 * Z`)
and `lam0 = ρ j / 8`, the pin set is the chart-source part of the level whose scaled invariant
`Im (Z ·)²` is at most `m` and whose scaled norm is at most `8`. -/
lemma saddlePin_eq_scaled {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Z : M → ℂ} {lam0 : ℝ} (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, chartCplx D x = (lam0 : ℂ) * Z x)
    {v m : ℝ} {x : M} :
    x ∈ saddlePin D v m ↔
      x ∈ (D.φ D.j).source ∧ ‖Z x‖ < 8 ∧ f x = v ∧ |((Z x) ^ 2).im| ≤ m := by
  have hρ : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
  have hnorm : ∀ x : M, ‖D.φ D.j x‖ = lam0 * ‖Z x‖ := by
    intro x
    rw [← norm_chartCplx D x, hZrel x, norm_mul, Complex.norm_of_nonneg hlam0pos.le]
  have him : ∀ x : M, (2 : ℝ) * (D.φ D.j x 0) * (D.φ D.j x 1)
      = lam0 ^ 2 * ((Z x) ^ 2).im := by
    intro x
    have h1 : chartCplx D x = (lam0 : ℂ) * Z x := hZrel x
    have h2 : chartCplx D x = (D.φ D.j x 0 : ℂ) + (D.φ D.j x 1 : ℂ) * Complex.I :=
      chartCplx_apply D x
    have h3 : ((chartCplx D x)) ^ 2 = (lam0 : ℂ) ^ 2 * (Z x) ^ 2 := by rw [h1, mul_pow]
    have h4 : ((chartCplx D x)) ^ 2
        = ((D.φ D.j x 0 : ℂ) + (D.φ D.j x 1 : ℂ) * Complex.I) ^ 2 := by rw [h2]
    have h5 := sq_im_of_pair (D.φ D.j x 0) (D.φ D.j x 1)
    have h6 : (((lam0 : ℂ) ^ 2 * (Z x) ^ 2)).im = lam0 ^ 2 * ((Z x) ^ 2).im := by
      rw [Complex.mul_im, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [← h5, ← h4, h3, h6]
  rw [saddlePin, hρ]
  constructor
  · rintro ⟨hsrc, hn, hv, hi⟩
    refine ⟨hsrc, ?_, hv, ?_⟩
    · rw [hnorm x, mul_comm (8 : ℝ) lam0] at hn
      exact lt_of_mul_lt_mul_left hn hlam0pos.le
    · have h2 := him x
      rw [h2, show (8 * lam0) / 8 = lam0 by ring, abs_mul, abs_of_nonneg (sq_nonneg lam0)] at hi
      have h5 : lam0 ^ 2 * |((Z x) ^ 2).im| ≤ lam0 ^ 2 * m := by
        linarith [hi, mul_comm (lam0 ^ 2) m]
      exact le_of_mul_le_mul_left h5 (by positivity)
  · rintro ⟨hsrc, hn, hv, hi⟩
    refine ⟨hsrc, ?_, hv, ?_⟩
    · rw [hnorm x, mul_comm (8 : ℝ) lam0]
      exact mul_lt_mul_of_pos_left hn hlam0pos
    · have h2 := him x
      rw [h2, show (8 * lam0) / 8 = lam0 by ring, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
      rw [show m * lam0 ^ 2 = lam0 ^ 2 * m by ring]
      exact mul_le_mul_of_nonneg_left hi (sq_nonneg lam0)

/-- A chart vector of norm less than `ρ j` lies in the target of the marked chart. -/
lemma cE2_mul_mem_target {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {lam0 η w : ℝ} (hball : ‖arcZ η w‖ < 8) (hlam0 : lam0 = D.ρ D.j / 8) :
    cE2 ((lam0 : ℂ) * arcZ η w) ∈ (D.φ D.j).target := by
  have hpos : 0 < lam0 := by
    rw [hlam0]
    exact div_pos (D.hρ D.j) (by norm_num)
  refine Work.Drive.N2.windowBall_subset_target D D.j ?_
  rw [cE2_norm, norm_mul, Complex.norm_of_nonneg hpos.le, hlam0]
  nlinarith [hball, D.hρ D.j]

/-- **The upper arc of the anchor level, as a point of `M`.**  The chart vector is the scaled one
(`lam0 * arcZ η w`), because the datum's chart coordinates are the *unscaled* `Zs`. -/
def arcUpPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (lam0 η w : ℝ) : M :=
  (D.φ D.j).symm (cE2 ((lam0 : ℂ) * arcZ η w))

/-- **The lower arc of the anchor level, as a point of `M`.** -/
def arcDnPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (lam0 η w : ℝ) : M :=
  (D.φ D.j).symm (cE2 (-((lam0 : ℂ) * arcZ η w)))

lemma phi_arcUpPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {lam0 η w : ℝ}
    (hball : ‖arcZ η w‖ < 8) (hlam0 : lam0 = D.ρ D.j / 8) :
    D.φ D.j (arcUpPt D lam0 η w) = cE2 ((lam0 : ℂ) * arcZ η w) :=
  (D.φ D.j).right_inv (cE2_mul_mem_target D hball hlam0)

lemma arcUpPt_mem_source {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {lam0 η w : ℝ}
    (hball : ‖arcZ η w‖ < 8) (hlam0 : lam0 = D.ρ D.j / 8) :
    arcUpPt D lam0 η w ∈ (D.φ D.j).source :=
  (D.φ D.j).map_target (cE2_mul_mem_target D hball hlam0)

lemma chartCplx_arcUpPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {lam0 η w : ℝ}
    (hball : ‖arcZ η w‖ < 8) (hlam0 : lam0 = D.ρ D.j / 8) :
    chartCplx D (arcUpPt D lam0 η w) = (lam0 : ℂ) * arcZ η w := by
  rw [chartCplx, phi_arcUpPt D hball hlam0, cplxE2_cE2]

lemma Z_arcUpPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ} {lam0 η w : ℝ}
    (hball : ‖arcZ η w‖ < 8) (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, chartCplx D x = (lam0 : ℂ) * Z x) :
    Z (arcUpPt D lam0 η w) = arcZ η w := by
  have h := hZrel (arcUpPt D lam0 η w)
  rw [chartCplx_arcUpPt D hball hlam0] at h
  have hne : (lam0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0pos)
  exact (mul_left_cancel₀ hne h).symm

/-- **The upper arc point lies in the pin** (at the anchor level `f p - lam0² η`). -/
lemma arcUpPt_mem_pin {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 η w m : ℝ} (hball : ‖arcZ η w‖ < 8) (hlam0pos : 0 < lam0)
    (hlam0 : lam0 = D.ρ D.j / 8) (hZrel : ∀ x : M, chartCplx D x = (lam0 : ℂ) * Z x)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hw : |w| ≤ m) :
    arcUpPt D lam0 η w ∈ saddlePin D (f p - lam0 ^ 2 * η) m := by
  rw [saddlePin_eq_scaled D hlam0pos hlam0 hZrel]
  refine ⟨arcUpPt_mem_source D hball hlam0, ?_, ?_, ?_⟩
  · rw [Z_arcUpPt D hball hlam0pos hlam0 hZrel]; exact hball
  · rw [hlev _ (arcUpPt_mem_source D hball hlam0),
      Z_arcUpPt D hball hlam0pos hlam0 hZrel, arcZ_sq_re]
    ring
  · rw [Z_arcUpPt D hball hlam0pos hlam0 hZrel, arcZ_sq_im]
    exact hw

/-- **The characterisation of the pin.**  Every point of the pin at the anchor level
`f = f p - lam0² * η` is one of the two arc points `arcZ η w` (`w` the invariant `Im (Z ·)²`). -/
lemma pin_eq_arc {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 η m : ℝ} (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, chartCplx D x = (lam0 : ℂ) * Z x)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    {x : M} (hx : x ∈ saddlePin D (f p - lam0 ^ 2 * η) m) :
    Z x = arcZ η (((Z x) ^ 2).im) ∨ Z x = -arcZ η (((Z x) ^ 2).im) := by
  obtain ⟨hsrc, _hn, hv, _himle⟩ := (saddlePin_eq_scaled D hlam0pos hlam0 hZrel).mp hx
  have hre : ((Z x) ^ 2).re = -η := by
    have h := hlev x hsrc
    rw [hv] at h
    have h3 : lam0 ^ 2 * ((Z x) ^ 2).re = lam0 ^ 2 * (-η) := by linarith
    exact mul_left_cancel₀ (by positivity : (lam0 : ℝ) ^ 2 ≠ 0) h3
  have hsq : (Z x) ^ 2 = (arcZ η (((Z x) ^ 2).im)) ^ 2 := by
    refine Complex.ext ?_ ?_
    · rw [hre, arcZ_sq_re]
    · rw [arcZ_sq_im]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

end Datum

end

end Work.Drive.N2Lead
