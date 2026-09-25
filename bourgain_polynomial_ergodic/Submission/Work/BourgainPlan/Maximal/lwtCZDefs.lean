import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2MaxAux
import Submission.Work.BourgainPlan.Maximal.dyCZ

/-!
# The real `ℓ²`-norm, the Calderón--Zygmund set and the CZ "good part"

Setting for the linearised weak-`(1,1)` bound of the `ℓ²`-valued dyadic maximal function.

* `lwtNorm g x = (Σ_t (g t x)²)^{1/2}` — the real-valued `ℓ²`-norm of a finite family;
* `lwtOm σ c`, `lwtOmStar σ c` — the Calderón--Zygmund set `{dyMax σ > c}` (written as the union
  of the maximal CZ cells) and its one-step (parent) enlargement;
* `lwtCellAvg A p` — the average of `A` over the dyadic cell `p`;
* `lwtGood A σ c` — the *good part* of `A`: equal to `A` off `lwtOm σ c` and to the average of `A`
  over the maximal CZ cell containing the point, on `lwtOm σ c`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace Work.BourgainPlan.Maximal

/-! ## The real `ℓ²`-norm -/

/-- The real-valued `ℓ²`-norm `(Σ_t (g t x)²)^{1/2}` of a finite family. -/
noncomputable def lwtNorm {n : ℕ} (g : Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (∑ t, (g t x) ^ 2)

lemma lwtNorm_nonneg {n : ℕ} (g : Fin n → ℝ → ℝ) (x : ℝ) : 0 ≤ lwtNorm g x :=
  Real.sqrt_nonneg _

lemma lwtNorm_sq {n : ℕ} (g : Fin n → ℝ → ℝ) (x : ℝ) :
    lwtNorm g x ^ 2 = ∑ t, (g t x) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun t _ => sq_nonneg _)

lemma lwtNorm_measurable {n : ℕ} {g : Fin n → ℝ → ℝ} (hg : ∀ t, Measurable (g t)) :
    Measurable (lwtNorm g) :=
  Measurable.sqrt (Finset.measurable_sum _ fun t _ => (hg t).pow_const 2)

/-- `ell2Sigma` is the `ENNReal`-valued lift of the real `ℓ²`-norm. -/
lemma ell2Sigma_eq_ofReal {n : ℕ} (g : Fin n → ℝ → ℝ) (x : ℝ) :
    ell2Sigma g x = ENNReal.ofReal (lwtNorm g x) := by
  unfold ell2Sigma ell2Sq lwtNorm
  have hsum : 0 ≤ ∑ t, (g t x) ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hsum (by norm_num : (0:ℝ) ≤ 1 / 2)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Real.enorm_eq_ofReal_abs, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-! ## The CZ set and its enlargement -/

/-- The Calderón--Zygmund set: the union of the maximal dyadic cells whose `σ`-average exceeds
`c`.  It equals `{x | c < dyMax σ x}` (see `lwtOm_eq_levelSet`). -/
noncomputable def lwtOm (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : Set ℝ :=
  ⋃ p ∈ czMax σ c, dyCell p.1 p.2

/-- The one-step enlargement of the CZ set: the union of the parents of the maximal cells. -/
noncomputable def lwtOmStar (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : Set ℝ :=
  ⋃ p ∈ czMax σ c, dyCell (p.1 + 1) (p.2 / 2)

lemma measurableSet_lwtOm (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : MeasurableSet (lwtOm σ c) :=
  MeasurableSet.biUnion (Set.countable_univ.mono (Set.subset_univ _)) fun p _ =>
    dyCell_measurable _ _

lemma measurableSet_lwtOmStar (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : MeasurableSet (lwtOmStar σ c) :=
  MeasurableSet.biUnion (Set.countable_univ.mono (Set.subset_univ _)) fun p _ =>
    dyCell_measurable _ _

lemma lwtOm_subset_lwtOmStar (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : lwtOm σ c ⊆ lwtOmStar σ c := by
  intro x hx
  rw [lwtOm, mem_iUnion₂] at hx
  obtain ⟨p, hp, hxp⟩ := hx
  exact mem_iUnion₂.mpr ⟨p, hp, dyCell_subset_succ p.1 p.2 hxp⟩

lemma lwtOm_eq_levelSet {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c)
    (hint : ∫⁻ y, σ y < ∞) : lwtOm σ c = {x : ℝ | c < dyMax σ x} :=
  (levelSet_eq_iUnion_czMax hc hint).symm

/-- The cells of `czMax` containing a point are unique. -/
lemma czMax_eq_of_mem {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {p q : ℤ × ℤ}
    (hp : p ∈ czMax σ c) (hq : q ∈ czMax σ c) {y : ℝ}
    (hyp : y ∈ dyCell p.1 p.2) (hyq : y ∈ dyCell q.1 q.2) : p = q := by
  by_contra hne
  exact Set.disjoint_left.mp (czMax_disjoint hp hq hne) hyp hyq

lemma dyCell_volume_eq (n k : ℤ) : volume (dyCell n k) = ENNReal.ofReal ((2 : ℝ) ^ n) := by
  rw [dyCell, Real.volume_Ico, dyCell_len]

/-- The measure of a maximal cell, times the level, is at most the integral of `σ` over it. -/
lemma czMax_cell_lt {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {p : ℤ × ℤ} (hp : p ∈ czMax σ c) :
    c * volume (dyCell p.1 p.2) < ∫⁻ y in dyCell p.1 p.2, σ y := by
  have hmem : c < ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹ * ∫⁻ y in dyCell p.1 p.2, σ y :=
    czMax_mem_czCells hp
  rw [ofReal_zpow_inv] at hmem
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p.1 := zpow_two_pos p.1
  have hA0 : ENNReal.ofReal ((2 : ℝ) ^ p.1) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hAt : ENNReal.ofReal ((2 : ℝ) ^ p.1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 := ENNReal.mul_lt_mul_left hA0 hAt hmem
  have h2 : ((ENNReal.ofReal ((2 : ℝ) ^ p.1))⁻¹ * ∫⁻ y in dyCell p.1 p.2, σ y)
      * ENNReal.ofReal ((2 : ℝ) ^ p.1) = ∫⁻ y in dyCell p.1 p.2, σ y := by
    rw [mul_assoc,
      mul_comm (∫⁻ y in dyCell p.1 p.2, σ y) (ENNReal.ofReal ((2 : ℝ) ^ p.1)),
      ← mul_assoc, ENNReal.inv_mul_cancel hA0 hAt, one_mul]
  rw [h2] at h1
  rw [dyCell_volume_eq]
  exact h1

lemma lwtOm_iUnion_disjoint (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) :
    Pairwise (Function.onFun Disjoint
      (fun p : {p : ℤ × ℤ // p ∈ czMax σ c} => dyCell p.1.1 p.1.2)) := by
  intro p q hpq
  exact czMax_disjoint p.2 q.2 (fun h => hpq (Subtype.ext h))

/-- The total volume of the maximal CZ cells is at most `c⁻¹ ∫ σ`. -/
lemma tsum_czMax_volume_le {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) (hct : c ≠ ⊤) :
    ∑' p : {p : ℤ × ℤ // p ∈ czMax σ c}, volume (dyCell p.1.1 p.1.2) ≤ c⁻¹ * ∫⁻ y, σ y :=
  calc ∑' p : {p : ℤ × ℤ // p ∈ czMax σ c}, volume (dyCell p.1.1 p.1.2)
      ≤ ∑' p : {p : ℤ × ℤ // p ∈ czMax σ c}, c⁻¹ * ∫⁻ y in dyCell p.1.1 p.1.2, σ y := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        calc volume (dyCell p.1.1 p.1.2)
            = c⁻¹ * (c * volume (dyCell p.1.1 p.1.2)) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hc.ne' hct, one_mul]
          _ ≤ c⁻¹ * ∫⁻ y in dyCell p.1.1 p.1.2, σ y :=
              mul_le_mul_right (czMax_cell_lt p.2).le _
    _ = c⁻¹ * ∑' p : {p : ℤ × ℤ // p ∈ czMax σ c}, ∫⁻ y in dyCell p.1.1 p.1.2, σ y :=
        ENNReal.tsum_mul_left
    _ = c⁻¹ * ∫⁻ y in ⋃ p : {p : ℤ × ℤ // p ∈ czMax σ c}, dyCell p.1.1 p.1.2, σ y := by
        rw [lintegral_iUnion (fun p => dyCell_measurable _ _) (lwtOm_iUnion_disjoint σ c)]
    _ ≤ c⁻¹ * ∫⁻ y, σ y := mul_le_mul_right (MeasureTheory.setLIntegral_le_lintegral _ _) _

/-- The measure of the CZ set is at most `c⁻¹ ∫ σ`. -/
lemma volume_lwtOm_le {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) (hct : c ≠ ⊤) :
    volume (lwtOm σ c) ≤ c⁻¹ * ∫⁻ y, σ y := by
  have hsub : lwtOm σ c ⊆ ⋃ p : {p : ℤ × ℤ // p ∈ czMax σ c}, dyCell p.1.1 p.1.2 := by
    intro x hx
    rw [lwtOm, mem_iUnion₂] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  exact le_trans (MeasureTheory.measure_mono hsub)
    (le_trans (MeasureTheory.measure_iUnion_le _) (tsum_czMax_volume_le hc hct))

/-- The measure of the enlargement is at most twice that of the CZ set. -/
lemma volume_lwtOmStar_le {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) (hct : c ≠ ⊤) :
    volume (lwtOmStar σ c) ≤ 2 * (c⁻¹ * ∫⁻ y, σ y) := by
  have hsub : lwtOmStar σ c ⊆
      ⋃ p : {p : ℤ × ℤ // p ∈ czMax σ c}, dyCell (p.1.1 + 1) (p.1.2 / 2) := by
    intro x hx
    rw [lwtOmStar, mem_iUnion₂] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  calc ∑' p : {p : ℤ × ℤ // p ∈ czMax σ c}, volume (dyCell (p.1.1 + 1) (p.1.2 / 2))
      = ∑' p : {p : ℤ × ℤ // p ∈ czMax σ c}, 2 * volume (dyCell p.1.1 p.1.2) := by
        refine tsum_congr fun p => ?_
        rw [dyCell_volume_eq, dyCell_volume_eq, zpow_succ_two,
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2:ℝ) ^ p.1.1), ENNReal.ofReal_ofNat,
          mul_comm]
    _ = 2 * ∑' p : {p : ℤ × ℤ // p ∈ czMax σ c}, volume (dyCell p.1.1 p.1.2) :=
        ENNReal.tsum_mul_left
    _ ≤ 2 * (c⁻¹ * ∫⁻ y, σ y) := mul_le_mul_right (tsum_czMax_volume_le hc hct) _

/-! ## The average over a dyadic cell -/

/-- The average of `A` over the dyadic cell `p = (n,k)`. -/
noncomputable def lwtCellAvg (A : ℝ → ℝ) (p : ℤ × ℤ) : ℝ :=
  ((2 : ℝ) ^ p.1)⁻¹ * ∫ y in dyCell p.1 p.2, A y

lemma lwtCellAvg_nonneg {A : ℝ → ℝ} (hA : ∀ y, 0 ≤ A y) (p : ℤ × ℤ) :
    0 ≤ lwtCellAvg A p := by
  unfold lwtCellAvg
  exact mul_nonneg (by positivity)
    (MeasureTheory.setIntegral_nonneg (dyCell_measurable _ _) fun x _ => hA x)

/-- The `ENNReal` cell average `ofReal(2^n)⁻¹ * ∫⁻ σ` of an `A` with `σ = ofReal ∘ A` is
`ofReal` of the real cell average. -/
lemma ofReal_lwtCellAvg {A : ℝ → ℝ} {σ : ℝ → ℝ≥0∞} {p : ℤ × ℤ} (hA : ∀ y, 0 ≤ A y)
    (hσ : ∀ y, σ y = ENNReal.ofReal (A y)) (hint : IntegrableOn A (dyCell p.1 p.2) volume) :
    ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹ * ∫⁻ y in dyCell p.1 p.2, σ y
      = ENNReal.ofReal (lwtCellAvg A p) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p.1 := zpow_two_pos p.1
  have h1 : ∫⁻ y in dyCell p.1 p.2, σ y
      = ENNReal.ofReal (∫ y in dyCell p.1 p.2, A y) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hA)]
    exact lintegral_congr (fun y => (hσ y))
  rw [h1, lwtCellAvg, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((2:ℝ) ^ p.1)⁻¹),
    ofReal_zpow_inv]

/-! ## The CZ good part -/

/-- The supremum defining the value of the good part on `lwtOm σ c`. -/
noncomputable def lwtGoodSup (A : ℝ → ℝ) (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (y : ℝ) : ℝ :=
  ⨆ q : {q : ℤ × ℤ // q ∈ czMax σ c},
    if y ∈ dyCell q.1.1 q.1.2 then lwtCellAvg A q.1 else 0

/-- The *good part* of `A` for the CZ decomposition of `σ` at level `c`: equal to `A` off
`lwtOm σ c`, and on `lwtOm σ c` equal to the average of `A` over the (unique) maximal CZ cell
containing the point. -/
noncomputable def lwtGood (A : ℝ → ℝ) (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (y : ℝ) : ℝ :=
  if y ∈ lwtOm σ c then lwtGoodSup A σ c y else A y

lemma lwtGood_of_mem {A : ℝ → ℝ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {y : ℝ}
    (hy : y ∈ lwtOm σ c) : lwtGood A σ c y = lwtGoodSup A σ c y := by
  unfold lwtGood
  rw [if_pos hy]

lemma lwtGood_of_notMem {A : ℝ → ℝ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {y : ℝ}
    (hy : y ∉ lwtOm σ c) : lwtGood A σ c y = A y := by
  unfold lwtGood
  rw [if_neg hy]

lemma lwtGoodSup_measurable {A : ℝ → ℝ} (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) :
    Measurable (lwtGoodSup A σ c) :=
  Measurable.iSup fun q : {q : ℤ × ℤ // q ∈ czMax σ c} =>
    Measurable.ite (dyCell_measurable q.1.1 q.1.2) measurable_const measurable_const

lemma lwtGood_measurable {A : ℝ → ℝ} (hA : Measurable A) (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) :
    Measurable (lwtGood A σ c) := by
  have h : lwtGood A σ c = fun y => if y ∈ lwtOm σ c then lwtGoodSup A σ c y else A y := rfl
  rw [h]
  exact Measurable.ite (measurableSet_lwtOm σ c) (lwtGoodSup_measurable σ c) hA

/-- Boundedness of the defining family of `lwtGoodSup`, used to handle the `iSup` in `ℝ`. -/
lemma lwtGoodSup_bddAbove {A : ℝ → ℝ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {y : ℝ}
    (hy : y ∈ lwtOm σ c) (hA : ∀ y, 0 ≤ A y) :
    BddAbove (Set.range fun r : {r : ℤ × ℤ // r ∈ czMax σ c} =>
      if y ∈ dyCell r.1.1 r.1.2 then lwtCellAvg A r.1 else 0) := by
  rw [lwtOm, mem_iUnion₂] at hy
  obtain ⟨p, hp, hyp⟩ := hy
  refine ⟨lwtCellAvg A p, ?_⟩
  rintro _ ⟨r, rfl⟩
  show (if y ∈ dyCell r.1.1 r.1.2 then lwtCellAvg A r.1 else 0) ≤ lwtCellAvg A p
  by_cases hry : y ∈ dyCell r.1.1 r.1.2
  · rw [if_pos hry, czMax_eq_of_mem hp r.2 hyp hry]
  · rw [if_neg hry]
    exact lwtCellAvg_nonneg hA p

/-- On a maximal CZ cell, the good part is the average. -/
lemma lwtGoodSup_eq_lwtCellAvg {A : ℝ → ℝ} (hA : ∀ y, 0 ≤ A y) {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞}
    {p : ℤ × ℤ} (hp : p ∈ czMax σ c) {y : ℝ} (hy : y ∈ dyCell p.1 p.2) :
    lwtGoodSup A σ c y = lwtCellAvg A p := by
  have hyOm : y ∈ lwtOm σ c := mem_iUnion₂.mpr ⟨p, hp, hy⟩
  haveI : Nonempty {q : ℤ × ℤ // q ∈ czMax σ c} := ⟨⟨p, hp⟩⟩
  unfold lwtGoodSup
  refine le_antisymm (ciSup_le ?_) ?_
  · intro q
    by_cases hqy : y ∈ dyCell q.1.1 q.1.2
    · rw [if_pos hqy, czMax_eq_of_mem hp q.2 hy hqy]
    · rw [if_neg hqy]
      exact lwtCellAvg_nonneg hA p
  · have h := le_ciSup (lwtGoodSup_bddAbove hyOm hA) (⟨p, hp⟩ : {q : ℤ × ℤ // q ∈ czMax σ c})
    rwa [if_pos hy] at h

lemma lwtGood_eq_lwtCellAvg {A : ℝ → ℝ} (hA : ∀ y, 0 ≤ A y) {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞}
    {p : ℤ × ℤ} (hp : p ∈ czMax σ c) {y : ℝ} (hy : y ∈ dyCell p.1 p.2) :
    lwtGood A σ c y = lwtCellAvg A p := by
  rw [lwtGood_of_mem (mem_iUnion₂.mpr ⟨p, hp, hy⟩)]
  exact lwtGoodSup_eq_lwtCellAvg hA hp hy

lemma lwtGood_nonneg {A : ℝ → ℝ} (hA : ∀ y, 0 ≤ A y) (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (y : ℝ) :
    0 ≤ lwtGood A σ c y := by
  by_cases hy : y ∈ lwtOm σ c
  · rw [lwtGood_of_mem hy]
    rw [lwtOm, mem_iUnion₂] at hy
    obtain ⟨p, hp, hyp⟩ := hy
    rw [lwtGoodSup_eq_lwtCellAvg hA hp hyp]
    exact lwtCellAvg_nonneg hA p
  · rw [lwtGood_of_notMem hy]; exact hA y

end Work.BourgainPlan.Maximal
