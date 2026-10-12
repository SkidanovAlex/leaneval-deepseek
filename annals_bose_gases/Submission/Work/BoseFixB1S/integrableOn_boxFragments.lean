import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotFrag
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 1000000

/-! ## Elementary integrability helpers -/

/-- A measurable function which is pointwise bounded on the (finite-measure) box is integrable
there. -/
theorem integrableOn_of_measurable_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : X N → ℝ}
    (hfm : Measurable f) {C : ℝ} (hC : ∀ x ∈ abox N ℓ, |f x| ≤ C) :
    IntegrableOn f (abox N ℓ) volume := by
  refine IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le) hfm.aestronglyMeasurable |C| ?_
  rw [ae_restrict_iff' (abox_measurable N ℓ)]
  refine ae_of_all _ (fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact le_trans (hC x hx) (le_abs_self C)

/-- `c·f·g` is integrable on the box when `f` and `g` are measurable and bounded there. -/
theorem integrableOn_const_mul_mul_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {c Cf Cg : ℝ}
    {f g : X N → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ Cf) (hgb : ∀ x ∈ abox N ℓ, |g x| ≤ Cg) :
    IntegrableOn (fun x : X N => c * f x * g x) (abox N ℓ) volume := by
  refine IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le)
    ((hfm.const_mul c).aestronglyMeasurable.mul hgm.aestronglyMeasurable)
    (|c| * |Cf| * |Cg|) ?_
  rw [ae_restrict_iff' (abox_measurable N ℓ)]
  refine ae_of_all _ (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  refine mul_le_mul ?_ (le_trans (hgb x hx) (le_abs_self Cg)) (abs_nonneg _)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact mul_le_mul (le_refl |c|) (le_trans (hfb x hx) (le_abs_self Cf)) (abs_nonneg _)
    (abs_nonneg _)

/-- `f·g` is integrable on the box when `f` and `g` are measurable and bounded there. -/
theorem integrableOn_mul_mul_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : X N → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ Cf) (hgb : ∀ x ∈ abox N ℓ, |g x| ≤ Cg) :
    IntegrableOn (fun x : X N => f x * g x) (abox N ℓ) volume := by
  simpa using integrableOn_const_mul_mul_of_bound (N := N) (ℓ := ℓ) (c := 1) hℓ hfm hgm hfb hgb

/-- Product bound: `|a·b| ≤ Ca·Cb` for `|a| ≤ Ca`, `|b| ≤ Cb`, `Ca ≥ 0`. -/
theorem abs_mul_le_mul_of_le {a b Ca Cb : ℝ} (ha : |a| ≤ Ca) (hb : |b| ≤ Cb) (hCa : 0 ≤ Ca) :
    |a * b| ≤ Ca * Cb := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hCa

/-- The mean-free box projection `Q_iΨ = σ_i·Ψ − P_iΨ` obeys `|Q_iΨ| ≤ 2C` wherever `|Ψ| ≤ C`
on the box. -/
theorem abs_boxQInd_le_two {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ : X N → ℝ} {C : ℝ}
    (hC : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ abox N ℓ, |UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * C := by
  intro x hx
  have hP : |UBBInputs8.boxPInd volA A i Ψ x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hC x hx
  have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hprod : |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x| ≤ C := by
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| ≤ 1 * C :=
          mul_le_mul hind (hC x hx) (abs_nonneg _) (by norm_num)
      _ = C := one_mul C
  show |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
      - UBBInputs8.boxPInd volA A i Ψ x| ≤ 2 * C
  calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
        - UBBInputs8.boxPInd volA A i Ψ x|
      ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x|
        + |UBBInputs8.boxPInd volA A i Ψ x| := abs_sub _ _
    _ ≤ C + C := add_le_add hprod hP
    _ = 2 * C := by ring

/-! ## The target -/

theorem integrableOn_boxFragments {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w p.1 p.2))
    (homc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => om p.1 p.2))
    (hw1rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w2 x y = w x y * (1 - om x y ^ 2))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (i j : Fin N) :
    MeasureTheory.IntegrableOn (Work.BoseFixB1S.fg0 volA A w2 Φ i j)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (Work.BoseFixB1S.fg1 volA A w2 Φ i j)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (Work.BoseFixB1S.fg2a volA A w2 Φ i j)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (Work.BoseFixB1S.fg2b volA A w2 Φ i j)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (Work.BoseFixB1S.fg2c volA A w1 Φ i j)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (Work.BoseFixB1S.fg3 volA A w1 Φ i j)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (Work.BoseFixB1S.fg4 volA A w om Φ i j)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  -- `Φ` is bounded on the compact box, by `|B|`.
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  have hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ |B| := by
    intro x hx
    have h := hB x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_abs_self B)
  have hΦm : Measurable Φ := hΦc.measurable
  -- the kernel readings are continuous in the configuration, hence bounded on the box
  have hpair : Continuous (fun x : X N => (x i, x j)) := by fun_prop
  have hwcont : Continuous (fun x : X N => w (x i) (x j)) := hwc.comp hpair
  have homcont : Continuous (fun x : X N => om (x i) (x j)) := homc.comp hpair
  have hw1cont : Continuous (fun x : X N => w1 (x i) (x j)) := by
    have h : (fun x : X N => w1 (x i) (x j))
        = fun x => w (x i) (x j) * (1 - om (x i) (x j)) := by
      funext x; exact hw1rel (x i) (x j)
    rw [h]
    exact hwcont.mul (continuous_const.sub homcont)
  have hw2cont : Continuous (fun x : X N => w2 (x i) (x j)) := by
    have h : (fun x : X N => w2 (x i) (x j))
        = fun x => w (x i) (x j) * (1 - om (x i) (x j) ^ 2) := by
      funext x; exact hw2rel (x i) (x j)
    rw [h]
    exact hwcont.mul (continuous_const.sub (homcont.pow 2))
  obtain ⟨Bw, hBw⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hwcont.continuousOn
  obtain ⟨Bw1, hBw1⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hw1cont.continuousOn
  obtain ⟨Bw2, hBw2⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hw2cont.continuousOn
  obtain ⟨Bom, hBom⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn homcont.continuousOn
  have hwb : ∀ x ∈ abox N ℓ, |w (x i) (x j)| ≤ |Bw| := by
    intro x hx
    have h := hBw x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_abs_self Bw)
  have hw1b : ∀ x ∈ abox N ℓ, |w1 (x i) (x j)| ≤ |Bw1| := by
    intro x hx
    have h := hBw1 x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_abs_self Bw1)
  have hw2b : ∀ x ∈ abox N ℓ, |w2 (x i) (x j)| ≤ |Bw2| := by
    intro x hx
    have h := hBw2 x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_abs_self Bw2)
  have homb : ∀ x ∈ abox N ℓ, |om (x i) (x j)| ≤ |Bom| := by
    intro x hx
    have h := hBom x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_abs_self Bom)
  have hwm : Measurable (fun x : X N => w (x i) (x j)) := hwcont.measurable
  have hw1m : Measurable (fun x : X N => w1 (x i) (x j)) := hw1cont.measurable
  have hw2m : Measurable (fun x : X N => w2 (x i) (x j)) := hw2cont.measurable
  have homm : Measurable (fun x : X N => om (x i) (x j)) := homcont.measurable
  -- the box projections of `Φ` and their two-fold composites
  have hPiΦ : ∀ x ∈ abox N ℓ, |UBBInputs8.boxPInd volA A i Φ x| ≤ |B| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb
  have hPjΦ : ∀ x ∈ abox N ℓ, |UBBInputs8.boxPInd volA A j Φ x| ≤ |B| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc j hΦb
  have hQiΦ : ∀ x ∈ abox N ℓ, |UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * |B| :=
    abs_boxQInd_le_two hℓ hvol hA hvolA hAc i hΦb
  have hQjΦ : ∀ x ∈ abox N ℓ, |UBBInputs8.boxQInd volA A j Φ x| ≤ 2 * |B| :=
    abs_boxQInd_le_two hℓ hvol hA hvolA hAc j hΦb
  have hPiPjΦ : ∀ x ∈ abox N ℓ,
      |UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x| ≤ |B| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hPjΦ
  have hPjPiΦ : ∀ x ∈ abox N ℓ,
      |UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x| ≤ |B| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc j hPiΦ
  have hPiQjΦ : ∀ x ∈ abox N ℓ,
      |UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x| ≤ 2 * |B| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hQjΦ
  have hPjQiΦ : ∀ x ∈ abox N ℓ,
      |UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x| ≤ 2 * |B| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc j hQiΦ
  have hQjPiΦ : ∀ x ∈ abox N ℓ,
      |UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x| ≤ 2 * |B| :=
    abs_boxQInd_le_two hℓ hvol hA hvolA hAc j hPiΦ
  have hQjQiΦ : ∀ x ∈ abox N ℓ,
      |UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Φ) x| ≤ 4 * |B| := by
    intro x hx
    have h := abs_boxQInd_le_two hℓ hvol hA hvolA hAc j hQiΦ x hx
    linarith
  -- measurability of the composites
  have hPiPjΦm : Measurable (fun x : X N =>
      UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x) :=
    measurable_boxPInd volA A hA i (measurable_boxPInd volA A hA j hΦm)
  have hPjPiΦm : Measurable (fun x : X N =>
      UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x) :=
    measurable_boxPInd volA A hA j (measurable_boxPInd volA A hA i hΦm)
  have hPiQjΦm : Measurable (fun x : X N =>
      UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x) :=
    measurable_boxPInd volA A hA i (Work.SlotWord.measurable_boxQInd volA A hA j hΦm)
  have hPjQiΦm : Measurable (fun x : X N =>
      UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x) :=
    measurable_boxPInd volA A hA j (Work.SlotWord.measurable_boxQInd volA A hA i hΦm)
  have hQjPiΦm : Measurable (fun x : X N =>
      UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x) :=
    Work.SlotWord.measurable_boxQInd volA A hA j (measurable_boxPInd volA A hA i hΦm)
  have hQjQiΦm : Measurable (fun x : X N =>
      UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Φ) x) :=
    Work.SlotWord.measurable_boxQInd volA A hA j
      (Work.SlotWord.measurable_boxQInd volA A hA i hΦm)
  -- the `Q₄` bracket: measurable and bounded
  have hQ4Bm : Measurable (fun x : X N => boxQ4B volA A om Φ (i, j) x) := by
    simp only [boxQ4B]
    exact hQjQiΦm.add (homm.mul ((hPjPiΦm.add hPjQiΦm).add hQjPiΦm))
  have hQ4Bb : ∀ x ∈ abox N ℓ,
      |boxQ4B volA A om Φ (i, j) x| ≤ 4 * |B| + |Bom| * (5 * |B|) := by
    intro x hx
    have h1 : |UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Φ) x| ≤ 4 * |B| :=
      hQjQiΦ x hx
    have h2 : |UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x| ≤ |B| :=
      hPjPiΦ x hx
    have h3 : |UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x| ≤ 2 * |B| :=
      hPjQiΦ x hx
    have h4 : |UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x| ≤ 2 * |B| :=
      hQjPiΦ x hx
    have h5 : |om (x i) (x j)| ≤ |Bom| := homb x hx
    have hsum : |UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x
        + UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x
        + UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x| ≤ 5 * |B| := by
      have ha : |UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x
          + UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x|
          ≤ |B| + 2 * |B| := by
        calc |UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x
              + UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x|
            ≤ |UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x|
              + |UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x| :=
              abs_add_le (UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x)
                (UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x)
          _ ≤ |B| + 2 * |B| := add_le_add h2 h3
      calc |UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x
            + UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x
            + UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x|
          ≤ |UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x
              + UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x|
            + |UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x| :=
            abs_add_le (UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x
              + UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x)
              (UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x)
        _ ≤ (|B| + 2 * |B|) + 2 * |B| := add_le_add ha h4
        _ = 5 * |B| := by ring
    have hompart : |om (x i) (x j)
        * (UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x
          + UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x
          + UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x)|
        ≤ |Bom| * (5 * |B|) := by
      rw [abs_mul]
      exact mul_le_mul h5 hsum (abs_nonneg _) (abs_nonneg _)
    show |UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Φ) x
        + om (x i) (x j) * (UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x
          + UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x
          + UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x)|
        ≤ 4 * |B| + |Bom| * (5 * |B|)
    exact le_trans (abs_add_le (UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Φ) x)
      (om (x i) (x j) * (UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Φ) x
        + UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x
        + UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x)))
      (add_le_add h1 hompart)
  -- ## the seven fragments
  have hfg0 : IntegrableOn (fg0 volA A w2 Φ i j) (abox N ℓ) volume := by
    show IntegrableOn (fun x : X N =>
      (1 / 2) * (UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x) ^ 2
        * w2 (x i) (x j)) (abox N ℓ) volume
    exact integrableOn_const_mul_mul_of_bound hℓ (hPiPjΦm.pow_const 2) hw2m
      (fun x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hPiPjΦ x hx) 2)
      hw2b
  have hfg1 : IntegrableOn (fg1 volA A w2 Φ i j) (abox N ℓ) volume := by
    have hbnd : ∀ x ∈ abox N ℓ,
        |UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
          * UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x|
          ≤ (2 * |B|) * |B| := fun x hx =>
      abs_mul_le_mul_of_le (hPiQjΦ x hx) (hPiPjΦ x hx) (by positivity)
    have h : IntegrableOn (fun x : X N =>
        2 * (UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
          * UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x)
        * w2 (x i) (x j)) (abox N ℓ) volume :=
      integrableOn_const_mul_mul_of_bound hℓ (hPiQjΦm.mul hPiPjΦm) hw2m hbnd hw2b
    refine h.congr_fun ?_ (abox_measurable N ℓ)
    intro x hx
    simp only [fg1]
    ring
  have hfg2a : IntegrableOn (fg2a volA A w2 Φ i j) (abox N ℓ) volume := by
    have hbnd : ∀ x ∈ abox N ℓ,
        |UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
          * UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Φ) x|
          ≤ (2 * |B|) * (2 * |B|) := fun x hx =>
      abs_mul_le_mul_of_le (hPiQjΦ x hx) (hPjQiΦ x hx) (by positivity)
    exact integrableOn_mul_mul_of_bound hℓ (hPiQjΦm.mul hPjQiΦm) hw2m hbnd hw2b
  have hfg2b : IntegrableOn (fg2b volA A w2 Φ i j) (abox N ℓ) volume := by
    have hbnd : ∀ x ∈ abox N ℓ,
        |UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
          * UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Φ) x|
          ≤ (2 * |B|) * (2 * |B|) := fun x hx =>
      abs_mul_le_mul_of_le (hPiQjΦ x hx) (hQjPiΦ x hx) (by positivity)
    exact integrableOn_mul_mul_of_bound hℓ (hPiQjΦm.mul hQjPiΦm) hw2m hbnd hw2b
  have hfg2c : IntegrableOn (fg2c volA A w1 Φ i j) (abox N ℓ) volume := by
    have hbnd : ∀ x ∈ abox N ℓ,
        |UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x
          * UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Φ) x|
          ≤ |B| * (4 * |B|) := fun x hx =>
      abs_mul_le_mul_of_le (hPiPjΦ x hx) (hQjQiΦ x hx) (by positivity)
    exact integrableOn_mul_mul_of_bound hℓ (hPiPjΦm.mul hQjQiΦm) hw1m hbnd hw1b
  have hfg3 : IntegrableOn (fg3 volA A w1 Φ i j) (abox N ℓ) volume := by
    have hbnd : ∀ x ∈ abox N ℓ,
        |UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
          * UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Φ) x|
          ≤ (2 * |B|) * (4 * |B|) := fun x hx =>
      abs_mul_le_mul_of_le (hPiQjΦ x hx) (hQjQiΦ x hx) (by positivity)
    have h : IntegrableOn (fun x : X N =>
        2 * (UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
          * UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Φ) x)
        * w1 (x i) (x j)) (abox N ℓ) volume :=
      integrableOn_const_mul_mul_of_bound hℓ (hPiQjΦm.mul hQjQiΦm) hw1m hbnd hw1b
    refine h.congr_fun ?_ (abox_measurable N ℓ)
    intro x hx
    simp only [fg3]
    ring
  have hfg4 : IntegrableOn (fg4 volA A w om Φ i j) (abox N ℓ) volume := by
    show IntegrableOn (fun x : X N =>
      (1 / 2) * (boxQ4B volA A om Φ (i, j) x) ^ 2 * w (x i) (x j)) (abox N ℓ) volume
    have hb : ∀ x ∈ abox N ℓ,
        |(boxQ4B volA A om Φ (i, j) x) ^ 2|
          ≤ (4 * |B| + |Bom| * (5 * |B|)) ^ 2 := by
      intro x hx
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hQ4Bb x hx) 2
    exact integrableOn_const_mul_mul_of_bound hℓ (hQ4Bm.pow_const 2) hwm hb hwb
  exact ⟨hfg0, hfg1, hfg2a, hfg2b, hfg2c, hfg3, hfg4⟩

end Work.BoseFixB1S
