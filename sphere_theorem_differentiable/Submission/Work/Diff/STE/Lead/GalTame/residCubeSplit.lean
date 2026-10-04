import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Lead.GalTame.GalCenter

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory

/-!
# Splitting an integral over the centred cube into the translates of the unit cube

The centred cube `cubeC (Fin n) = (-1/2,1/2]ⁿ` is contained in the cube `(-1,1]ⁿ`, which is the
disjoint union of the `2ⁿ` translates of the half open unit cube `(0,1]ⁿ` by the vectors
`fun i => (ε i : ℝ) - 1`, `ε : Fin n → Fin 2`.  Since `g ≥ 0`, the integral of `g` over the centred
cube is therefore bounded by the sum of the integrals of `g` over those `2ⁿ` translates, which is
exactly what `residCubeSplit` asserts.

The two ingredients are

* `bigCube_indicator_eq_sum`: the pointwise identity
  `1_{(-1,1]ⁿ} g = Σ_ε 1_{∏ᵢ (εᵢ - 1, εᵢ]} g` (the `2ⁿ` half open boxes tile `(-1,1]ⁿ`), and
* `splitCell_indicator_translate`: `1_{∏ᵢ (εᵢ - 1, εᵢ]} g (x + shift ε) = 1_{(0,1]ⁿ} (g (· + shift ε)) x`,
  which converts the integral over the box into the integral over the unit cube by the translation
  invariance of Lebesgue measure.
-/

/-- The two half open intervals `(-1,0]` and `(0,1]` arising as the coordinate factors of the
cells of the partition of `(-1,1]ⁿ`. -/
def cellCoord (a : Fin 2) : Set ℝ := Set.Ioc ((a : ℝ) - 1) (a : ℝ)

/-- The half open box `∏ᵢ (εᵢ - 1, εᵢ]`; these `2ⁿ` boxes tile `(-1,1]ⁿ`. -/
def splitCell {n : ℕ} (ε : Fin n → Fin 2) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i => cellCoord (ε i)

/-- The cube `(-1,1]ⁿ`, the union of the `2ⁿ` cells `splitCell ε`. -/
def bigCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun _ : Fin n => Set.Ioc (-1 : ℝ) 1

/-- The shift `(ε i : ℝ) - 1 ∈ {-1,0}` attached to `ε : Fin n → Fin 2`. -/
def cubeShift {n : ℕ} (ε : Fin n → Fin 2) : Fin n → ℝ := fun i => (ε i : ℝ) - 1

lemma cellCoord_zero : cellCoord (0 : Fin 2) = Set.Ioc (-1 : ℝ) 0 := by
  ext t; simp [cellCoord]

lemma cellCoord_one : cellCoord (1 : Fin 2) = Set.Ioc (0 : ℝ) 1 := by
  ext t; simp [cellCoord]

/-- The two coordinate cells `(-1,0]` and `(0,1]` are disjoint. -/
lemma cellCoord_disjoint (a b : Fin 2) (hab : a ≠ b) : Disjoint (cellCoord a) (cellCoord b) := by
  rw [Set.disjoint_left]
  intro t ha hb
  fin_cases a <;> fin_cases b <;> simp_all [cellCoord] <;> linarith

lemma cellCoord_subset_Ioc (a : Fin 2) : cellCoord a ⊆ Set.Ioc (-1 : ℝ) 1 := by
  intro t ht
  have h0 : (0 : ℝ) ≤ (a : ℝ) := by fin_cases a <;> norm_num
  have h1 : (a : ℝ) ≤ 1 := by fin_cases a <;> norm_num
  rw [cellCoord, Set.mem_Ioc] at ht
  rw [Set.mem_Ioc]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma splitCell_subset_bigCube {n : ℕ} (ε : Fin n → Fin 2) : splitCell ε ⊆ bigCube n := by
  intro x hx i _
  exact cellCoord_subset_Ioc (ε i) (hx i (Set.mem_univ i))

lemma cubeC_subset_bigCube (n : ℕ) : cubeC (Fin n) ⊆ bigCube n := by
  intro x hx i _
  have h := hx i (Set.mem_univ i)
  rw [Set.mem_Ioc] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma measurableSet_bigCube (n : ℕ) : MeasurableSet (bigCube n) := by
  simp only [bigCube]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ioc)

lemma measurableSet_splitCell {n : ℕ} (ε : Fin n → Fin 2) : MeasurableSet (splitCell ε) := by
  simp only [splitCell]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ioc)

lemma measurableSet_unitCube (n : ℕ) : MeasurableSet (Work.Diff.STE.unitCube (ι := Fin n)) := by
  simp only [Work.Diff.STE.unitCube]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ioc)

lemma mem_splitCell_iff {n : ℕ} {ε : Fin n → Fin 2} {y : Fin n → ℝ} :
    y ∈ splitCell ε ↔ ∀ i, (ε i : ℝ) - 1 < y i ∧ y i ≤ (ε i : ℝ) := by
  simp only [splitCell, Set.mem_pi, Set.mem_univ, true_implies, cellCoord, Set.mem_Ioc]

lemma mem_unitCube_iff {n : ℕ} {x : Fin n → ℝ} :
    x ∈ Work.Diff.STE.unitCube (ι := Fin n) ↔ ∀ i, 0 < x i ∧ x i ≤ 1 := by
  simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc]

/-- Translating the half open unit cube by `cubeShift ε` gives the cell `splitCell ε`. -/
lemma add_cubeShift_mem_splitCell_iff {n : ℕ} (ε : Fin n → Fin 2) (x : Fin n → ℝ) :
    x + cubeShift ε ∈ splitCell ε ↔ x ∈ Work.Diff.STE.unitCube (ι := Fin n) := by
  rw [mem_splitCell_iff, mem_unitCube_iff]
  constructor
  · intro h i
    have hi := h i
    rw [Pi.add_apply, show cubeShift ε i = (ε i : ℝ) - 1 from rfl] at hi
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · intro h i
    have hi := h i
    rw [Pi.add_apply, show cubeShift ε i = (ε i : ℝ) - 1 from rfl]
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- The cells `splitCell ε` tile the cube `(-1,1]ⁿ`: the indicator of `bigCube` is the sum of the
indicators of the cells. -/
lemma bigCube_indicator_eq_sum {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (bigCube n).indicator g x = ∑ ε : Fin n → Fin 2, (splitCell ε).indicator g x := by
  by_cases hx : x ∈ bigCube n
  · have hx' : ∀ i, -1 < x i ∧ x i ≤ 1 := by
      intro i; exact hx i (Set.mem_univ i)
    let ε₀ : Fin n → Fin 2 := fun i => if x i ≤ 0 then 0 else 1
    have hxε₀ : x ∈ splitCell ε₀ := by
      rw [mem_splitCell_iff]
      intro i
      by_cases hi : x i ≤ 0
      · have h0 : (ε₀ i : ℝ) = 0 := by
          show (((if x i ≤ 0 then (0 : Fin 2) else 1) : Fin 2) : ℝ) = 0
          simp only [hi, ↓reduceIte]
          norm_num
        rw [h0]
        exact ⟨by linarith [(hx' i).1], hi⟩
      · have h1 : (ε₀ i : ℝ) = 1 := by
          show (((if x i ≤ 0 then (0 : Fin 2) else 1) : Fin 2) : ℝ) = 1
          simp only [hi, ↓reduceIte]
          norm_num
        rw [h1]
        exact ⟨by linarith [not_le.mp hi], (hx' i).2⟩
    rw [Set.indicator_of_mem hx, Finset.sum_eq_single ε₀]
    · exact (Set.indicator_of_mem hxε₀ g).symm
    · intro b _ hb
      refine Set.indicator_of_notMem (fun hxb => ?_) g
      have hex : ∃ i, b i ≠ ε₀ i := by
        by_contra h
        apply hb
        funext i
        by_contra hh
        exact h ⟨i, hh⟩
      obtain ⟨i, hi⟩ := hex
      exact (Set.disjoint_left.mp (cellCoord_disjoint (b i) (ε₀ i) hi))
        (hxb i (Set.mem_univ i)) (hxε₀ i (Set.mem_univ i))
    · intro h; exact absurd (Finset.mem_univ ε₀) h
  · rw [Set.indicator_of_notMem hx]
    symm
    apply Finset.sum_eq_zero
    intro ε _
    exact Set.indicator_of_notMem (fun h => hx (splitCell_subset_bigCube ε h)) g

/-- Translating the integration variable by `cubeShift ε` converts the integral over the cell
`splitCell ε` into an integral over the half open unit cube. -/
lemma splitCell_indicator_translate {n : ℕ} (g : (Fin n → ℝ) → ℝ) (ε : Fin n → Fin 2)
    (x : Fin n → ℝ) :
    (splitCell ε).indicator g (x + cubeShift ε)
      = (Work.Diff.STE.unitCube (ι := Fin n)).indicator (fun y => g (y + cubeShift ε)) x := by
  by_cases hx : x ∈ Work.Diff.STE.unitCube (ι := Fin n)
  · have h1 : (splitCell ε).indicator g (x + cubeShift ε) = g (x + cubeShift ε) :=
      Set.indicator_of_mem ((add_cubeShift_mem_splitCell_iff ε x).mpr hx) g
    have h2 : (Work.Diff.STE.unitCube (ι := Fin n)).indicator
        (fun y => g (y + cubeShift ε)) x = g (x + cubeShift ε) := Set.indicator_of_mem hx _
    rw [h1, h2]
  · have h1 : (splitCell ε).indicator g (x + cubeShift ε) = 0 :=
      Set.indicator_of_notMem (fun h => hx ((add_cubeShift_mem_splitCell_iff ε x).mp h)) g
    have h2 : (Work.Diff.STE.unitCube (ι := Fin n)).indicator
        (fun y => g (y + cubeShift ε)) x = 0 := Set.indicator_of_notMem hx _
    rw [h1, h2]

/-- A continuous function on `ℝⁿ` is integrable over any measurable subset of `(-1,1]ⁿ`. -/
lemma integrableOn_of_subset_bigCube {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : Continuous g)
    {s : Set (Fin n → ℝ)} (hsm : MeasurableSet s) (hs : s ⊆ bigCube n) :
    IntegrableOn g s volume := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hg.continuousOn (s := _))
  have hbig : bigCube n ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1) := by
    intro x hx i _
    have h := hx i (Set.mem_univ i)
    rw [Set.mem_Ioc] at h
    rw [Set.mem_Icc]
    exact ⟨h.1.le, h.2⟩
  refine IntegrableOn.of_bound ?_ (hg.continuousOn.aestronglyMeasurable hsm) M ?_
  · exact lt_of_le_of_lt (measure_mono (hs.trans hbig)) hK.measure_lt_top
  · rw [ae_restrict_iff' hsm]
    exact Filter.Eventually.of_forall (fun x hx => hM x (hbig (hs hx)))

/-- **Splitting the integral over the centred cube.**  For a continuous nonnegative `g`, the
integral over `cubeC (Fin n) = (-1/2,1/2]ⁿ` is at most the sum of the integrals over the `2ⁿ`
translates `(0,1]ⁿ + {(ε i : ℝ) - 1}_i` of the half open unit cube, which together tile the larger
cube `(-1,1]ⁿ ⊇ (-1/2,1/2]ⁿ`. -/
theorem residCubeSplit {n : ℕ} (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) :
    ∫ z in Work.Diff.STE.Lead.GalTame.cubeC (Fin n), g z
      ≤ ∑ ε : Fin n → Fin 2,
          ∫ z in Work.Diff.STE.unitCube (ι := Fin n), g (z + fun i => ((ε i : ℝ) - 1)) := by
  have hIntBig : IntegrableOn g (bigCube n) volume :=
    integrableOn_of_subset_bigCube hg (measurableSet_bigCube n) (subset_refl _)
  have h1 : ∫ z in cubeC (Fin n), g z ≤ ∫ z in bigCube n, g z :=
    setIntegral_mono_set hIntBig (Filter.Eventually.of_forall hg0)
      (Filter.Eventually.of_forall (cubeC_subset_bigCube n))
  have hInt : ∀ ε : Fin n → Fin 2, Integrable ((splitCell ε).indicator g) volume := by
    intro ε
    rw [integrable_indicator_iff (measurableSet_splitCell ε)]
    exact integrableOn_of_subset_bigCube hg (measurableSet_splitCell ε)
      (splitCell_subset_bigCube ε)
  have h2 : ∫ z in bigCube n, g z = ∑ ε : Fin n → Fin 2, ∫ z in splitCell ε, g z := by
    rw [← integral_indicator (measurableSet_bigCube n) (f := g)]
    calc ∫ z, (bigCube n).indicator g z
        = ∫ z, ∑ ε : Fin n → Fin 2, (splitCell ε).indicator g z := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => bigCube_indicator_eq_sum g x)
      _ = ∑ ε : Fin n → Fin 2, ∫ z, (splitCell ε).indicator g z :=
          integral_finsetSum _ (fun ε _ => hInt ε)
      _ = ∑ ε : Fin n → Fin 2, ∫ z in splitCell ε, g z := by
          refine Finset.sum_congr rfl (fun ε _ => ?_)
          exact integral_indicator (measurableSet_splitCell ε) (f := g)
  have h3 : ∑ ε : Fin n → Fin 2, ∫ z in splitCell ε, g z
      = ∑ ε : Fin n → Fin 2, ∫ z in Work.Diff.STE.unitCube (ι := Fin n),
          g (z + cubeShift ε) := by
    refine Finset.sum_congr rfl (fun ε _ => ?_)
    calc ∫ z in splitCell ε, g z
        = ∫ z, (splitCell ε).indicator g z :=
          (integral_indicator (measurableSet_splitCell ε) (f := g)).symm
      _ = ∫ z, (splitCell ε).indicator g (z + cubeShift ε) :=
          (integral_add_right_eq_self ((splitCell ε).indicator g) (cubeShift ε)).symm
      _ = ∫ z, (Work.Diff.STE.unitCube (ι := Fin n)).indicator
              (fun y => g (y + cubeShift ε)) z :=
          integral_congr_ae (Filter.Eventually.of_forall
            (fun x => splitCell_indicator_translate g ε x))
      _ = ∫ z in Work.Diff.STE.unitCube (ι := Fin n), g (z + cubeShift ε) :=
          integral_indicator (measurableSet_unitCube n) (f := fun y => g (y + cubeShift ε))
  calc ∫ z in Work.Diff.STE.Lead.GalTame.cubeC (Fin n), g z
      ≤ ∫ z in bigCube n, g z := h1
    _ = ∑ ε : Fin n → Fin 2, ∫ z in splitCell ε, g z := h2
    _ = ∑ ε : Fin n → Fin 2,
          ∫ z in Work.Diff.STE.unitCube (ι := Fin n), g (z + fun i => ((ε i : ℝ) - 1)) := h3

end Work.Diff.STE.Lead.GalTame
