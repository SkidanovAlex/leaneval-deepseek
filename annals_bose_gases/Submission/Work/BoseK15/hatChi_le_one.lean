import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.hatChi_le_one` — the trivial uniform bound on the χ-fields

FS's localization function is normalised so that `∫ χ² = 1` on the unit cell
(`BoxData.chi_int`), `χ ≥ 0` and `χ = 0` off the cell (`BoxData.chi_supp`), and the
cell has volume `1` (`BoxData.cell_vol`).  The two transforms

    `χ̂(p) = ∫ χ(x) cos⟪p,x⟫ dx`,   `χ̂²(p) = ∫ χ²(x) cos⟪p,x⟫ dx`

therefore satisfy `|χ̂(p)| ≤ 1` and `|χ̂²(p)| ≤ 1` for every momentum `p`.

* `|χ̂²(p)| ≤ ∫ χ²|cos| ≤ ∫ χ² = 1` is immediate from `|cos| ≤ 1`.

* For `|χ̂(p)| ≤ ∫ χ|cos| ≤ 1` one cannot use `χ ≤ 1` pointwise; instead the
  arithmetic-geometric mean inequality `2ab ≤ a²+b²` applied to `a = χ`,
  `b = |cos|` gives `2χ|cos| ≤ χ² + cos² ≤ χ² + 1` on the cell, and
  `∫_cell χ² = ∫χ² = 1`, `∫_cell 1 = volume cell = 1` (the factor `1` being
  legitimate only on the cell, where `cos² ≤ 1` is integrable).

Everything is proved for an arbitrary `BoxData` and then specialised to
`corpusBox`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseK15

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about the cell -/

/-- The cell has finite volume (`volume cell = 1`). -/
private lemma cell_volume_ne_top (B : Work.BoseB4.BoxData) : volume B.cell ≠ ⊤ := by
  rw [B.cell_vol]
  exact ENNReal.one_ne_top

/-- `∫_cell χ² = 1`: the normalisation `∫χ² = 1` seen on the cell, where `χ` lives. -/
private lemma setIntegral_chi_sq (B : Work.BoseB4.BoxData) :
    (∫ x in B.cell, (B.chi x) ^ 2) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun x : ℝ³ => (B.chi x) ^ 2) (fun x hx => ?_), B.chi_int]
  have h0 : B.chi x = 0 := by
    by_contra h
    exact hx (B.chi_supp (Function.mem_support.mpr h))
  simp [h0]

/-- `∫_cell 1 = volume cell = 1`. -/
private lemma setIntegral_one_cell (B : Work.BoseB4.BoxData) :
    (∫ _x in B.cell, (1 : ℝ)) = 1 := by
  rw [setIntegral_const, MeasureTheory.Measure.real, B.cell_vol, ENNReal.toReal_one, one_smul]

/-! ## The bound on `χ̂` -/

/-- `χ · |cos⟪p,·⟫|` is integrable on the cell: it is dominated by the integrable `χ`. -/
private lemma integrableOn_chi_mul_abs_cos (B : Work.BoseB4.BoxData) (p : ℝ³) :
    IntegrableOn (fun x : ℝ³ => B.chi x * |Real.cos (inner ℝ p x)|) B.cell volume := by
  have hcont : Continuous (fun x : ℝ³ => B.chi x * |Real.cos (inner ℝ p x)|) :=
    B.chi_cont.mul ((Real.continuous_cos.comp (continuous_const.inner continuous_id)).abs)
  refine (B.chi_integrable.integrableOn).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg _), abs_of_nonneg (B.chi_nonneg x)]
  exact mul_le_of_le_one_right (B.chi_nonneg x) (Real.abs_cos_le_one _)

/-- **The key bound**: `∫_cell χ|cos⟪p,·⟫| ≤ 1`, by AM-GM against `χ² + 1`. -/
private lemma setIntegral_chi_mul_abs_cos_le_one (B : Work.BoseB4.BoxData) (p : ℝ³) :
    (∫ x in B.cell, B.chi x * |Real.cos (inner ℝ p x)|) ≤ 1 := by
  have hA : Integrable (fun x : ℝ³ => 2 * (B.chi x * |Real.cos (inner ℝ p x)|))
      (volume.restrict B.cell) :=
    (integrableOn_chi_mul_abs_cos B p).const_mul 2
  have h1 : IntegrableOn (fun _ : ℝ³ => (1 : ℝ)) B.cell volume :=
    integrableOn_const (s := B.cell) (μ := volume) (C := (1 : ℝ))
      (cell_volume_ne_top B) (by simp)
  have hB : Integrable (fun x : ℝ³ => (B.chi x) ^ 2 + 1) (volume.restrict B.cell) :=
    (B.chi_sq_integrable.integrableOn).add h1
  -- the pointwise AM-GM bound on the cell
  have hmono : (∫ x in B.cell, 2 * (B.chi x * |Real.cos (inner ℝ p x)|))
      ≤ ∫ x in B.cell, ((B.chi x) ^ 2 + 1) := by
    refine integral_mono_ae hA hB (Filter.Eventually.of_forall (fun x => ?_))
    have hsq := two_mul_le_add_sq (B.chi x) |Real.cos (inner ℝ p x)|
    have hcos : |Real.cos (inner ℝ p x)| ^ 2 ≤ 1 := by
      nlinarith [Real.abs_cos_le_one (inner ℝ p x), abs_nonneg (Real.cos (inner ℝ p x))]
    linarith
  have hval : (∫ x in B.cell, ((B.chi x) ^ 2 + 1)) = 2 := by
    rw [integral_add (B.chi_sq_integrable.integrableOn) h1, setIntegral_chi_sq B,
      setIntegral_one_cell B]
    norm_num
  have h2mul : (∫ x in B.cell, 2 * (B.chi x * |Real.cos (inner ℝ p x)|))
      = 2 * ∫ x in B.cell, B.chi x * |Real.cos (inner ℝ p x)| :=
    integral_const_mul 2 _
  rw [hval, h2mul] at hmono
  linarith

/-- `|χ̂(p)| ≤ ∫ χ|cos⟪p,·⟫|`: the triangle inequality for the (real) Bochner integral. -/
private lemma hatChi_abs_le_integral (B : Work.BoseB4.BoxData) (p : ℝ³) :
    |B.hatChi p| ≤ ∫ x, B.chi x * |Real.cos (inner ℝ p x)| := by
  calc |B.hatChi p| = |∫ x, B.chi x * Real.cos (inner ℝ p x)| := rfl
    _ ≤ ∫ x, |B.chi x * Real.cos (inner ℝ p x)| := abs_integral_le_integral_abs
    _ = ∫ x, B.chi x * |Real.cos (inner ℝ p x)| := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [abs_mul, abs_of_nonneg (B.chi_nonneg x)]

/-- `|χ̂(p)| ≤ 1` for an arbitrary `BoxData`: pass to the cell and use the AM-GM bound. -/
private lemma hatChi_abs_le_one (B : Work.BoseB4.BoxData) (p : ℝ³) : |B.hatChi p| ≤ 1 := by
  refine le_trans (hatChi_abs_le_integral B p) ?_
  rw [(setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun x : ℝ³ => B.chi x * |Real.cos (inner ℝ p x)|) (fun x hx => ?_)).symm]
  · exact setIntegral_chi_mul_abs_cos_le_one B p
  · have h0 : B.chi x = 0 := by
      by_contra h
      exact hx (B.chi_supp (Function.mem_support.mpr h))
    simp [h0]

/-! ## The bound on `χ̂²` -/

/-- `|χ̂²(p)| ≤ 1` for an arbitrary `BoxData`: `|cos| ≤ 1` and `∫χ² = 1` suffice. -/
private lemma hatChiSq_abs_le_one (B : Work.BoseB4.BoxData) (p : ℝ³) : |B.hatChiSq p| ≤ 1 := by
  calc |B.hatChiSq p| = |∫ x, (B.chi x) ^ 2 * Real.cos (inner ℝ p x)| := rfl
    _ ≤ ∫ x, |(B.chi x) ^ 2 * Real.cos (inner ℝ p x)| := abs_integral_le_integral_abs
    _ = ∫ x, (B.chi x) ^ 2 * |Real.cos (inner ℝ p x)| := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [abs_mul, abs_of_nonneg (sq_nonneg (B.chi x))]
    _ ≤ ∫ x, (B.chi x) ^ 2 :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)))
          B.chi_sq_integrable
          (Filter.Eventually.of_forall
            (fun x => mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)))
    _ = 1 := B.chi_int

/-! ## The requested statement -/

theorem hatChi_le_one : (∀ p : EuclideanSpace ℝ (Fin 3), |corpusBox.hatChi p| ≤ 1) ∧
    (∀ p : EuclideanSpace ℝ (Fin 3), |corpusBox.hatChiSq p| ≤ 1) :=
  ⟨fun p => hatChi_abs_le_one corpusBox p, fun p => hatChiSq_abs_le_one corpusBox p⟩

end Work.BoseK15
