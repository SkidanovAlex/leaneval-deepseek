import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Order.CompletePartialOrder

open Filter Metric Set MeasureTheory
open scoped Topology BigOperators ENNReal Classical

noncomputable section

namespace Commons.Measure.EuclideanSpace

abbrev E (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

-- 1D interval facts ----------------------------------------
lemma cell_cover_coord {a : ℝ} {N : ℕ} {δ : ℝ} (hδ : 0 < δ) {r : ℝ}
    (hlo : a ≤ r) (hhi : r < a + (N : ℝ) * δ) :
    ∃ k : ℕ, k < N ∧ a + (k : ℝ) * δ ≤ r ∧ r < a + ((k : ℝ) + 1) * δ := by
  let t : ℝ := (r - a) / δ
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (sub_nonneg.mpr hlo) (le_of_lt hδ)
  have htN : t < N := by
    dsimp [t]
    rw [div_lt_iff₀ hδ]
    linarith [hhi]
  let k : ℕ := Nat.floor t
  have hkN : k < N := by
    have hk_le_t : (k : ℝ) ≤ t := Nat.floor_le ht0
    exact_mod_cast lt_of_le_of_lt hk_le_t htN
  refine ⟨k, hkN, ?_, ?_⟩
  · have h1 : (k : ℝ) ≤ t := Nat.floor_le ht0
    have hmul : (k : ℝ) * δ ≤ t * δ := mul_le_mul_of_nonneg_right h1 (le_of_lt hδ)
    dsimp [t] at hmul
    rw [div_mul_cancel₀ (r - a) (ne_of_gt hδ)] at hmul
    linarith
  · have h2 : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
    have hmul : t * δ < ((k : ℝ) + 1) * δ := mul_lt_mul_of_pos_right h2 hδ
    dsimp [t] at hmul
    rw [div_mul_cancel₀ (r - a) (ne_of_gt hδ)] at hmul
    linarith

-- E coordinates ----------------------------------------------
lemma inner_sum_mul {ι : Type*} [Fintype ι] (x y : E ι) :
    inner ℝ x y = ∑ i : ι, x i * y i := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

lemma continuous_coord {ι : Type*} [Fintype ι] (i : ι) :
    Continuous (fun x : E ι => x i) := by
  exact PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : ι => ℝ) i

def pointOf (ι : Type*) [Fintype ι] (c : ι → ℝ) : E ι :=
  WithLp.toLp 2 c

@[simp] lemma pointOf_coord {ι : Type*} [Fintype ι] (c : ι → ℝ) (i : ι) :
    (pointOf ι c) i = c i := by
  simp [pointOf]

lemma volume_euclid_Ico_pi {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (volume : Measure (E ι)) {x : E ι | ∀ i : ι, a i ≤ x i ∧ x i < b i} =
      ∏ i : ι, ENNReal.ofReal (b i - a i) := by
  let T : (ι → ℝ) ≃ᵐ E ι := MeasurableEquiv.toLp 2 (ι → ℝ)
  have hmp : MeasurePreserving (T : (ι → ℝ) → E ι) := PiLp.volume_preserving_toLp ι
  have hEq : (T ⁻¹' ({x : E ι | ∀ i, a i ≤ x i ∧ x i < b i} : Set (E ι))) =
      ({y : ι → ℝ | ∀ i, a i ≤ y i ∧ y i < b i} : Set (ι → ℝ)) := by
    ext y
    simp [T]
  have hmeas : MeasurableSet ({x : E ι | ∀ i, a i ≤ x i ∧ x i < b i} : Set (E ι)) := by
    measurability
  calc
    (volume : Measure (E ι)) {x : E ι | ∀ i, a i ≤ x i ∧ x i < b i}
        = (volume : Measure (ι → ℝ)) {y : ι → ℝ | ∀ i, a i ≤ y i ∧ y i < b i} := by
          rw [← hEq]
          exact (hmp.measure_preimage hmeas.nullMeasurableSet).symm
    _ = ∏ i, ENNReal.ofReal (b i - a i) := by
      have hset : ({y : ι → ℝ | ∀ i, a i ≤ y i ∧ y i < b i} : Set (ι → ℝ)) =
          Set.univ.pi (fun i : ι => Set.Ico (a i) (b i)) := by
        ext y
        simp [Set.mem_pi, Set.mem_Ico]
      rw [hset]
      exact Real.volume_pi_Ico

-- grid and cells -------------------------------------------------
def stepL (L : ℝ) (j : ℕ) : ℝ := 2 * L / (j + 1)

def cubeLo (L : ℝ) (j : ℕ) (k : ℕ) : ℝ := -L + (k : ℝ) * stepL L j

def gridPoint (ι : Type*) [Fintype ι] (L : ℝ) (j : ℕ) (g : ι → Fin (j + 1)) : E ι :=
  pointOf ι (fun i : ι => cubeLo L j (g i).val)

def qcube (ι : Type*) [Fintype ι] (L : ℝ) : Set (E ι) :=
  {x : E ι | ∀ i : ι, -L ≤ x i ∧ x i < L}

def cell (ι : Type*) [Fintype ι] (L : ℝ) (j : ℕ) (g : ι → Fin (j + 1)) : Set (E ι) :=
  {x : E ι | ∀ i : ι, (gridPoint ι L j g) i ≤ x i ∧ x i < (gridPoint ι L j g) i + stepL L j}

lemma cell_coord_iff {ι : Type*} [Fintype ι] (L : ℝ) (j : ℕ) (g : ι → Fin (j + 1)) (x : E ι) :
    x ∈ cell ι L j g ↔
      ∀ i : ι, cubeLo L j (g i).val ≤ x i ∧ x i < cubeLo L j (g i).val + stepL L j := by
  rw [cell]
  simp [gridPoint]

lemma stepL_nonneg {L : ℝ} (hL : 0 ≤ L) (j : ℕ) : 0 ≤ stepL L j := by
  unfold stepL
  positivity

lemma stepL_pos {L : ℝ} (hL : 0 < L) (j : ℕ) : 0 < stepL L j := by
  unfold stepL
  positivity

lemma cubeLo_ge_negL {L : ℝ} (hL : 0 ≤ L) (j k : ℕ) : -L ≤ cubeLo L j k := by
  unfold cubeLo
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hm : 0 ≤ (k : ℝ) * stepL L j := mul_nonneg hk0 (stepL_nonneg hL j)
  linarith

lemma cubeLo_add_step_le {L : ℝ} (hL : 0 ≤ L) {j k : ℕ} (hk : k ≤ j) :
    cubeLo L j k + stepL L j ≤ L := by
  have hs : 0 ≤ stepL L j := stepL_nonneg hL j
  have hk' : ((k : ℝ) + 1) ≤ (j + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ hk)
  have hmul : ((k : ℝ) + 1) * stepL L j ≤ (j + 1 : ℝ) * stepL L j :=
    mul_le_mul_of_nonneg_right hk' hs
  have htot : (j + 1 : ℝ) * stepL L j = 2 * L := by
    unfold stepL
    have hj : (j + 1 : ℝ) ≠ 0 := by positivity
    exact mul_div_cancel₀ (2 * L) hj
  have hkcast : (((k : ℕ) + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
  calc
    cubeLo L j k + stepL L j = -L + (((k : ℕ) + 1 : ℕ) : ℝ) * stepL L j := by
      unfold cubeLo
      rw [hkcast]
      ring
    _ ≤ -L + (j + 1 : ℝ) * stepL L j := by
      rw [hkcast]
      linarith [hmul]
    _ = L := by rw [htot]; ring

lemma cell_subset_qcube {ι : Type*} [Fintype ι] (L : ℝ) (hL : 0 ≤ L) (j : ℕ)
    (g : ι → Fin (j + 1)) : cell ι L j g ⊆ qcube ι L := by
  intro x hx
  have hx' := (cell_coord_iff L j g x).mp hx
  intro i
  have hlow : -L ≤ x i := le_trans (cubeLo_ge_negL hL j (g i).val) (hx' i).1
  have hhi : x i < L := by
    have hb := (hx' i).2
    have hle : cubeLo L j (g i).val + stepL L j ≤ L :=
      cubeLo_add_step_le hL (Nat.le_of_lt_succ (g i).isLt)
    linarith
  exact ⟨hlow, hhi⟩

lemma qcube_cover_coord {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (j : ℕ) {x : E ι} (i : ι)
    (hx : x ∈ qcube ι L) :
    ∃ k : Fin (j + 1), cubeLo L j k.val ≤ x i ∧ x i < cubeLo L j k.val + stepL L j := by
  have hδ : 0 < stepL L j := stepL_pos hL j
  have hlo : -L ≤ x i := (hx i).1
  have hhi' : x i < -L + ((j + 1 : ℕ) : ℝ) * stepL L j := by
    have htot : (j + 1 : ℝ) * stepL L j = 2 * L := by
      unfold stepL
      have hj : (j + 1 : ℝ) ≠ 0 := by positivity
      exact mul_div_cancel₀ (2 * L) hj
    have hcast : (((j + 1 : ℕ) : ℕ) : ℝ) = (j + 1 : ℝ) := by norm_num
    rw [hcast, htot]
    have hxlt : x i < L := (hx i).2
    linarith
  rcases cell_cover_coord (a := -L) (N := j + 1) (δ := stepL L j) hδ hlo hhi' with ⟨k, hkN, hklo, hkhi⟩
  refine ⟨⟨k, hkN⟩, ?_, ?_⟩
  · simpa [cubeLo] using hklo
  · have hkhi2 : x i < cubeLo L j k + stepL L j := by
      unfold cubeLo
      linarith
    simpa using hkhi2

lemma qcube_eq_union_cells {ι : Type*} [Fintype ι] (L : ℝ) (hL : 0 < L) (j : ℕ) :
    qcube ι L = ⋃ g : ι → Fin (j + 1), cell ι L j g := by
  ext x
  constructor
  · intro hx
    let g : ι → Fin (j + 1) := fun i => Classical.choose (qcube_cover_coord (L := L) hL j i hx)
    refine Set.mem_iUnion.mpr ⟨g, ?_⟩
    intro i
    exact (Classical.choose_spec (qcube_cover_coord (L := L) hL j i hx))
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨g, hg⟩
    exact cell_subset_qcube L hL.le j g hg

lemma cell_disjoint {ι : Type*} [Fintype ι] (L : ℝ) (hL : 0 < L) (j : ℕ)
    {g h : ι → Fin (j + 1)} (hgh : g ≠ h) :
    Disjoint (cell ι L j g) (cell ι L j h) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rcases hx with ⟨hxg, hxh⟩
  have hdiff : ∃ i : ι, (g i).val ≠ (h i).val := by
    by_contra hno
    push_neg at hno
    apply hgh
    funext i
    exact Fin.ext (hno i)
  rcases hdiff with ⟨i, hival⟩
  have hxgi := (cell_coord_iff L j g x).mp hxg i
  have hxhi := (cell_coord_iff L j h x).mp hxh i
  have hstep0 : 0 ≤ stepL L j := stepL_nonneg hL.le j
  rcases lt_or_gt_of_ne hival with hlt | hgt
  · have hA : (g i).val + 1 ≤ (h i).val := Nat.succ_le_of_lt hlt
    have hmid : cubeLo L j (g i).val + stepL L j ≤ cubeLo L j (h i).val := by
      unfold cubeLo
      have hk' : (((g i).val + 1 : ℕ) : ℝ) ≤ ((h i).val : ℝ) := by exact_mod_cast hA
      calc
        -L + ((g i).val : ℝ) * stepL L j + stepL L j = -L + (((g i).val + 1 : ℕ) : ℝ) * stepL L j := by
          norm_num
          ring
        _ ≤ -L + ((h i).val : ℝ) * stepL L j := by
          linarith [mul_le_mul_of_nonneg_right hk' hstep0]
    have h1 : x i < cubeLo L j (h i).val := lt_of_lt_of_le hxgi.2 hmid
    exact not_lt_of_ge hxhi.1 h1
  · have hA : (h i).val + 1 ≤ (g i).val := Nat.succ_le_of_lt hgt
    have hmid : cubeLo L j (h i).val + stepL L j ≤ cubeLo L j (g i).val := by
      unfold cubeLo
      have hk' : (((h i).val + 1 : ℕ) : ℝ) ≤ ((g i).val : ℝ) := by exact_mod_cast hA
      calc
        -L + ((h i).val : ℝ) * stepL L j + stepL L j = -L + (((h i).val + 1 : ℕ) : ℝ) * stepL L j := by
          norm_num
          ring
        _ ≤ -L + ((g i).val : ℝ) * stepL L j := by
          linarith [mul_le_mul_of_nonneg_right hk' hstep0]
    have h1 : x i < cubeLo L j (g i).val := lt_of_lt_of_le hxhi.2 hmid
    exact not_lt_of_ge hxgi.1 h1

lemma cell_measurable {ι : Type*} [Fintype ι] (L : ℝ) (j : ℕ) (g : ι → Fin (j + 1)) :
    MeasurableSet (cell ι L j g) := by
  have hset : cell ι L j g =
      {x : E ι | ∀ i : ι, cubeLo L j (g i).val ≤ x i ∧ x i < cubeLo L j (g i).val + stepL L j} := by
    ext x
    exact cell_coord_iff L j g x
  rw [hset]
  measurability

lemma qcube_measurable {ι : Type*} [Fintype ι] (L : ℝ) : MeasurableSet (qcube ι L) := by
  rw [show qcube ι L = {x : E ι | ∀ i : ι, -L ≤ x i ∧ x i < L} by rfl]
  measurability

-- measure identities -------------------------------------------
lemma integral_qcube {ι : Type*} [Fintype ι] {L : ℝ} (g : E ι → ℝ)
    (hg : ∀ x : E ι, x ∉ qcube ι L → g x = 0) :
    (∫ x : E ι, g x) = ∫ x in qcube ι L, g x := by
  have hpt : ∀ x : E ι, g x = Set.indicator (qcube ι L) g x := by
    intro x
    by_cases hx : x ∈ qcube ι L
    · simp [hx]
    · simp [hx, hg x hx]
  calc
    (∫ x : E ι, g x) = ∫ x : E ι, Set.indicator (qcube ι L) g x := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hpt
    _ = ∫ x in qcube ι L, g x := MeasureTheory.integral_indicator (qcube_measurable L)

lemma sum_integral_cell {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (j : ℕ)
    (g : E ι → ℝ) (hg : IntegrableOn g (qcube ι L) volume) :
    ∫ x in qcube ι L, g x = ∑ k : ι → Fin (j + 1), ∫ x in cell ι L j k, g x := by
  have hI : ∫ x in (⋃ k : ι → Fin (j + 1), cell ι L j k), g x =
      ∑' k : ι → Fin (j + 1), ∫ x in cell ι L j k, g x := by
    apply MeasureTheory.integral_iUnion (s := fun k : ι → Fin (j + 1) => cell ι L j k)
    · intro k
      exact cell_measurable L j k
    · intro g h hgh
      exact cell_disjoint L hL j hgh
    · simpa [qcube_eq_union_cells L hL j] using hg
  calc
    ∫ x in qcube ι L, g x = ∫ x in (⋃ k : ι → Fin (j + 1), cell ι L j k), g x := by
      rw [qcube_eq_union_cells L hL j]
    _ = ∑' k : ι → Fin (j + 1), ∫ x in cell ι L j k, g x := hI
    _ = ∑ k : ι → Fin (j + 1), ∫ x in cell ι L j k, g x := by
      rw [tsum_fintype]

-- sample points and cell coordinate bounds ----------------------
lemma coord_abs_le_norm {ι : Type*} [Fintype ι] (u : E ι) (i : ι) : |u i| ≤ ‖u‖ := by
  let b : E ι := pointOf ι (fun j : ι => if j = i then (1 : ℝ) else 0)
  have hinner : inner ℝ u b = u i := by
    rw [inner_sum_mul]
    simp [b]
  have hn : ‖b‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [b]
  calc
    |u i| = |inner ℝ u b| := by rw [hinner]
    _ ≤ ‖u‖ * ‖b‖ := norm_inner_le_norm (𝕜 := ℝ) u b
    _ = ‖u‖ := by rw [hn]; ring

lemma cell_coord_diff_bound {ι : Type*} [Fintype ι] (L : ℝ) (hL : 0 ≤ L) (j : ℕ)
    (g : ι → Fin (j + 1)) {x : E ι} (hx : x ∈ cell ι L j g) (i : ι) :
    |x i - (gridPoint ι L j g) i| ≤ stepL L j := by
  have hi := (cell_coord_iff L j g x).mp hx i
  have hp : (gridPoint ι L j g) i ≤ x i := hi.1
  have hxlt : x i < (gridPoint ι L j g) i + stepL L j := hi.2
  have hxle : x i ≤ (gridPoint ι L j g) i + stepL L j := le_of_lt hxlt
  rw [abs_of_nonneg]
  · linarith
  · linarith

lemma cell_inner_diff_bound {ι : Type*} [Fintype ι] (L : ℝ) (hL : 0 < L) (j : ℕ)
    (g : ι → Fin (j + 1)) (u : E ι) {x : E ι} (hx : x ∈ cell ι L j g) :
    |inner ℝ u (x - gridPoint ι L j g)| ≤ (Fintype.card ι : ℝ) * stepL L j * ‖u‖ := by
  have hs : 0 ≤ stepL L j := stepL_nonneg hL.le j
  have hz : ∀ i : ι, |u i| * |x i - (gridPoint ι L j g) i| ≤ ‖u‖ * stepL L j := by
    intro i
    have h1 : |u i| ≤ ‖u‖ := coord_abs_le_norm u i
    have h2 : |x i - (gridPoint ι L j g) i| ≤ stepL L j := cell_coord_diff_bound L hL.le j g hx i
    have h2' : 0 ≤ |x i - (gridPoint ι L j g) i| := abs_nonneg _
    have h1' : 0 ≤ |u i| := abs_nonneg _
    calc
      |u i| * |x i - (gridPoint ι L j g) i| ≤ ‖u‖ * |x i - (gridPoint ι L j g) i| :=
        mul_le_mul_of_nonneg_right h1 h2'
      _ ≤ ‖u‖ * stepL L j := mul_le_mul_of_nonneg_left h2 (norm_nonneg u)
  calc
    |inner ℝ u (x - gridPoint ι L j g)|
        = |∑ i : ι, u i * (x i - (gridPoint ι L j g) i)| := by
          rw [inner_sum_mul u (x - gridPoint ι L j g)]
          congr 1
    _ ≤ ∑ i : ι, |u i| * |x i - (gridPoint ι L j g) i| := by
          calc
            |∑ i : ι, u i * (x i - (gridPoint ι L j g) i)|
                ≤ ∑ i : ι, |u i * (x i - (gridPoint ι L j g) i)| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ i : ι, |u i| * |x i - (gridPoint ι L j g) i| := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [abs_mul]
    _ ≤ ∑ i : ι, ‖u‖ * stepL L j := Finset.sum_le_sum (fun i _ => hz i)
    _ = (Fintype.card ι : ℝ) * (‖u‖ * stepL L j) := by simp
    _ = (Fintype.card ι : ℝ) * stepL L j * ‖u‖ := by ring



-- ==================== NEW CONTENT BELOW ====================

-- |a| = max 0 a + max 0 (-a)
lemma abs_eq_max_add (a : ℝ) : |a| = max 0 a + max 0 (-a) := by
  by_cases ha : 0 ≤ a
  · have h1 : max 0 a = a := max_eq_right ha
    have h2 : max 0 (-a) = 0 := max_eq_left (neg_nonpos.mpr ha)
    rw [h1, h2, abs_of_nonneg ha]
    ring
  · have ha' : a ≤ 0 := le_of_not_ge ha
    have h1 : max 0 a = 0 := max_eq_left ha'
    have h2 : max 0 (-a) = -a := max_eq_right (neg_nonneg.mpr ha')
    rw [h1, h2, abs_of_nonpos ha']
    ring

lemma max_add_max_neg (a : ℝ) : max 0 a + max 0 (-a) = |a| := by
  rw [abs_eq_max_add]

-- measure of one half-open cell
lemma cell_volume_ennreal {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (j : ℕ)
    (g : ι → Fin (j + 1)) :
    (volume : Measure (E ι)) (cell ι L j g) = ENNReal.ofReal ((stepL L j) ^ Fintype.card ι) := by
  let a : ι → ℝ := fun i => (gridPoint ι L j g) i
  let b : ι → ℝ := fun i => (gridPoint ι L j g) i + stepL L j
  have hset : cell ι L j g = {x : E ι | ∀ i : ι, a i ≤ x i ∧ x i < b i} := by
    ext x
    rw [cell_coord_iff]
    simp [a, b, gridPoint]
  rw [hset, volume_euclid_Ico_pi]
  simp [a, b]
  rw [← ENNReal.ofReal_pow (stepL_nonneg hL j)]

lemma cell_volume_real {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (j : ℕ)
    (g : ι → Fin (j + 1)) :
    (volume : Measure (E ι)).real (cell ι L j g) = (stepL L j) ^ Fintype.card ι := by
  change ((volume : Measure (E ι)) (cell ι L j g)).toReal = (stepL L j) ^ Fintype.card ι
  rw [cell_volume_ennreal hL j g]
  exact ENNReal.toReal_ofReal (pow_nonneg (stepL_nonneg hL j) _)

lemma qcube_volume_ennreal {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) :
    (volume : Measure (E ι)) (qcube ι L) = ENNReal.ofReal ((2 * L) ^ Fintype.card ι) := by
  let a : ι → ℝ := fun _ => -L
  let b : ι → ℝ := fun _ => L
  have hset : qcube ι L = {x : E ι | ∀ i : ι, a i ≤ x i ∧ x i < b i} := by
    ext x
    simp [qcube, a, b]
  rw [hset, volume_euclid_Ico_pi]
  have hprod : (∏ i : ι, ENNReal.ofReal (b i - a i)) = ENNReal.ofReal ((2 * L) ^ Fintype.card ι) := by
    have hLL : ∀ i : ι, b i - a i = 2 * L := by
      intro i
      simp [a, b]
      ring
    simp_rw [hLL]
    rw [Finset.prod_const, Finset.card_univ]
    rw [ENNReal.ofReal_pow (mul_nonneg (by norm_num) hL)]
  exact hprod

lemma qcube_volume_real {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) :
    (volume : Measure (E ι)).real (qcube ι L) = (2 * L) ^ Fintype.card ι := by
  change ((volume : Measure (E ι)) (qcube ι L)).toReal = (2 * L) ^ Fintype.card ι
  rw [qcube_volume_ennreal hL]
  exact ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg (by norm_num) hL) _)

lemma cell_volume_toReal {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (n : ℕ)
    (g : ι → Fin (n + 1)) :
    ((volume : Measure (E ι)) (cell ι L n g)).toReal = (stepL L n) ^ Fintype.card ι := by
  change (volume : Measure (E ι)).real (cell ι L n g) = (stepL L n) ^ Fintype.card ι
  exact cell_volume_real hL n g

lemma qcube_volume_toReal {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) :
    ((volume : Measure (E ι)) (qcube ι L)).toReal = (2 * L) ^ Fintype.card ι := by
  change (volume : Measure (E ι)).real (qcube ι L) = (2 * L) ^ Fintype.card ι
  exact qcube_volume_real hL

-- normalized compact-support data for f
lemma f_support_ge_zero {ι : Type*} [Fintype ι] (f : E ι → ℝ)
    (hfsupp : ∃ R : ℝ, ∀ x : E ι, f x ≠ 0 → ‖x‖ ≤ R) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : E ι, f x ≠ 0 → ‖x‖ ≤ R := by
  rcases hfsupp with ⟨R, hR⟩
  refine ⟨max R 0, ?_, ?_⟩
  · exact le_max_right R 0
  · intro x hx
    exact le_trans (hR x hx) (le_max_left R 0)

lemma f_eq_zero_of_norm_gt {ι : Type*} [Fintype ι] (f : E ι → ℝ)
    {R : ℝ} (hR : ∀ x : E ι, f x ≠ 0 → ‖x‖ ≤ R) {x : E ι} (hx : R < ‖x‖) :
    f x = 0 := by
  by_contra h
  have hle := hR x h
  linarith

-- global uniform bound for |f|
lemma exists_f_abs_bound {ι : Type*} [Fintype ι] (f : E ι → ℝ) (hfc : Continuous f)
    (hfsupp : ∃ R : ℝ, ∀ x : E ι, f x ≠ 0 → ‖x‖ ≤ R) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ x : E ι, |f x| ≤ S := by
  rcases f_support_ge_zero f hfsupp with ⟨R, hR0, hR⟩
  let B : Set (E ι) := Metric.closedBall 0 R
  have hBcomp : IsCompact B := by
    exact isCompact_closedBall (x := (0 : E ι)) (r := R)
  have hcontB : ContinuousOn f B := hfc.continuousOn
  rcases IsCompact.exists_bound_of_continuousOn hBcomp hcontB with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x
  by_cases hxB : x ∈ B
  · calc
      |f x| ≤ C := hC x hxB
      _ ≤ max C 0 := le_max_left C 0
  · have hgt : R < ‖x‖ := by
      simp [B, Metric.mem_closedBall, not_le] at hxB
      exact hxB
    have hz : f x = 0 := f_eq_zero_of_norm_gt f hR hgt
    calc
      |f x| = 0 := by simp [hz]
      _ ≤ max C 0 := le_max_right C 0

-- global uniform continuity of f (f has compact support and is continuous)
lemma f_uniformContinuous {ι : Type*} [Fintype ι] (f : E ι → ℝ) (hfc : Continuous f)
    (hfsupp : ∃ R : ℝ, ∀ x : E ι, f x ≠ 0 → ‖x‖ ≤ R) : UniformContinuous f := by
  rcases f_support_ge_zero f hfsupp with ⟨R, hR0, hR⟩
  let B : Set (E ι) := Metric.closedBall 0 (R + 1)
  have hBcomp : IsCompact B := by
    exact isCompact_closedBall (x := (0 : E ι)) (r := R + 1)
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hBuc : UniformContinuousOn f B :=
    IsCompact.uniformContinuousOn_of_continuous hBcomp hfc.continuousOn
  rcases (Metric.uniformContinuousOn_iff.mp hBuc) ε hε with ⟨δ, hδ0, hδ⟩
  refine ⟨min δ 1, ?_, ?_⟩
  · exact lt_min hδ0 (by norm_num)
  · intro x y hxy
    have hxyδ : dist x y < δ := lt_of_lt_of_le hxy (min_le_left δ 1)
    have hxy1 : dist x y < 1 := lt_of_lt_of_le hxy (min_le_right δ 1)
    by_cases hxB : x ∈ B
    · by_cases hyB : y ∈ B
      · exact hδ x hxB y hyB hxyδ
      · -- x ∈ B, y ∉ B: both are zero
        have hygt : R + 1 < ‖y‖ := by
          simp [B, Metric.mem_closedBall, not_le] at hyB
          exact hyB
        have hxgt : R < ‖x‖ := by
          have htri : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
            have : ‖y‖ = ‖x + (y - x)‖ := by simp
            rw [this]
            exact norm_add_le _ _
          have hxy1' : ‖x - y‖ < 1 := by simpa [dist_eq_norm] using hxy1
          have hdistyx : ‖y - x‖ < 1 := by simpa [norm_sub_rev] using hxy1'
          linarith
        have hz1 : f x = 0 := f_eq_zero_of_norm_gt f hR hxgt
        have hz2 : f y = 0 := f_eq_zero_of_norm_gt f hR (by linarith)
        simp [hz1, hz2, hε]
    · -- x ∉ B
      have hxgt : R + 1 < ‖x‖ := by
        simp [B, Metric.mem_closedBall, not_le] at hxB
        exact hxB
      have hz1 : f x = 0 := f_eq_zero_of_norm_gt f hR (by linarith)
      have hygt : R < ‖y‖ := by
        have htri : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
          have : ‖x‖ = ‖y + (x - y)‖ := by simp
          rw [this]
          exact norm_add_le _ _
        have hdistxy : ‖x - y‖ < 1 := by simpa [dist_eq_norm] using hxy1
        linarith
      have hz2 : f y = 0 := f_eq_zero_of_norm_gt f hR hygt
      simp [hz1, hz2, hε]

-- norm of a vector whose coordinates are all ≤ M
lemma norm_le_sqrt_card_mul {ι : Type*} [Fintype ι] {M : ℝ} (hM : 0 ≤ M) {x : E ι}
    (hx : ∀ i : ι, |x i| ≤ M) : ‖x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * M := by
  have hsq : ‖x‖ ^ 2 ≤ (Fintype.card ι : ℝ) * M ^ 2 := by
    calc
      ‖x‖ ^ 2 = ∑ i : ι, ‖x i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) x
      _ ≤ ∑ i : ι, M ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hM] using hx i)
      _ = (Fintype.card ι : ℝ) * M ^ 2 := by simp
  have hd : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have hsqnonneg : 0 ≤ (Fintype.card ι : ℝ) * M ^ 2 := mul_nonneg hd (sq_nonneg M)
  calc
    ‖x‖ = Real.sqrt (‖x‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg x)]
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * M ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Fintype.card ι : ℝ) * M := by
      rw [Real.sqrt_mul hd (M ^ 2), Real.sqrt_sq_eq_abs M, abs_of_nonneg hM]
    _ = Real.sqrt (Fintype.card ι : ℝ) * M := rfl

lemma norm_sub_le_sqrt_card_of_coord_le {ι : Type*} [Fintype ι] {M : ℝ} (hM : 0 ≤ M)
    {x y : E ι} (hxy : ∀ i : ι, |x i - y i| ≤ M) : ‖x - y‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * M := by
  apply norm_le_sqrt_card_mul hM
  intro i
  simpa [sub_eq_add_neg] using hxy i

-- |inner u x| ≤ card * L * ‖u‖ for x in the cube
lemma qcube_inner_abs_bound {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) {u x : E ι}
    (hx : x ∈ qcube ι L) : |inner ℝ u x| ≤ (Fintype.card ι : ℝ) * L * ‖u‖ := by
  have hxi : ∀ i : ι, |x i| ≤ L := by
    intro i
    have hlow : -L ≤ x i := (hx i).1
    have hhi : x i ≤ L := le_of_lt (hx i).2
    exact abs_le.mpr ⟨by linarith, hhi⟩
  calc
    |inner ℝ u x| = |∑ i : ι, u i * x i| := by rw [inner_sum_mul u x]
    _ ≤ ∑ i : ι, |u i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, ‖u‖ * L := by
      apply Finset.sum_le_sum
      intro i hi
      have hu : |u i| ≤ ‖u‖ := coord_abs_le_norm u i
      have hxL : |x i| ≤ L := hxi i
      calc
        |u i * x i| = |u i| * |x i| := by rw [abs_mul]
        _ ≤ ‖u‖ * |x i| := mul_le_mul_of_nonneg_right hu (abs_nonneg _)
        _ ≤ ‖u‖ * L := mul_le_mul_of_nonneg_left hxL (norm_nonneg u)
    _ = (Fintype.card ι : ℝ) * (‖u‖ * L) := by simp
    _ = (Fintype.card ι : ℝ) * L * ‖u‖ := by ring

lemma inner_smul_real {ι : Type*} [Fintype ι] (u x : E ι) (a : ℝ) :
    inner ℝ u (a • x) = a * inner ℝ u x := by
  simp [inner_smul_right]

-- a ≥ 0: |a * c| = a * |c|
lemma abs_mul_of_nonneg {a c : ℝ} (ha : 0 ≤ a) : |a * c| = a * |c| := by
  rw [abs_mul, abs_of_nonneg ha]

-- global uniform continuity gives explicit moduli
lemma f_modulus {ι : Type*} [Fintype ι] (f : E ι → ℝ) (hfc : Continuous f)
    (hfsupp : ∃ R : ℝ, ∀ x : E ι, f x ≠ 0 → ‖x‖ ≤ R) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : E ι, ‖x - y‖ < δ → |f x - f y| < η := by
  rcases (Metric.uniformContinuous_iff.mp (f_uniformContinuous f hfc hfsupp)) η hη with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, ?_⟩
  intro x y hxy
  exact hδ (by simpa [dist_eq_norm] using hxy)

-- cell diameter: x inside a cell is close to its grid point
lemma norm_sub_gridPoint_cell {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (n : ℕ)
    (g : ι → Fin (n + 1)) {x : E ι} (hx : x ∈ cell ι L n g) :
    ‖x - gridPoint ι L n g‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * stepL L n := by
  apply norm_sub_le_sqrt_card_of_coord_le (stepL_nonneg hL n)
  intro i
  exact cell_coord_diff_bound L hL n g hx i

-- √(card) ≤ card + 1
lemma sqrt_card_le_card_add_one {ι : Type*} [Fintype ι] :
    Real.sqrt (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by
  have hd0 : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have hsq : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 := by
    rw [Real.sq_sqrt hd0]
    nlinarith [sq_nonneg (Fintype.card ι : ℝ)]
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by positivity)] at h

-- ‖x - c‖ ≤ (card+1) * stepL
lemma norm_sub_gridPoint_cell_le {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (n : ℕ)
    (g : ι → Fin (n + 1)) {x : E ι} (hx : x ∈ cell ι L n g) :
    ‖x - gridPoint ι L n g‖ ≤ ((Fintype.card ι : ℝ) + 1) * stepL L n := by
  have h := norm_sub_gridPoint_cell hL n g hx
  calc
    ‖x - gridPoint ι L n g‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * stepL L n := h
    _ ≤ ((Fintype.card ι : ℝ) + 1) * stepL L n := by
      exact mul_le_mul_of_nonneg_right sqrt_card_le_card_add_one (stepL_nonneg hL n)

-- step length becomes eventually < any positive c
lemma exists_forall_stepL_lt {L : ℝ} (hL : 0 < L) {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N, stepL L n < c := by
  have h2L : 0 < 2 * L := by positivity
  rcases exists_nat_gt ((2 * L) / c) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hM1 : (2 * L) / c < (M : ℝ) + 1 := by linarith
  have hn' : (M : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have h1 : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hdenM : 0 < (M : ℝ) + 1 := by positivity
  unfold stepL
  have hle : 2 * L / ((n : ℝ) + 1) ≤ 2 * L / ((M : ℝ) + 1) := by
    exact div_le_div_of_nonneg_left h2L.le hdenM hn'
  have hlt : 2 * L / ((M : ℝ) + 1) < c := by
    rw [div_lt_iff₀ hdenM]
    have hh := (div_lt_iff₀ hc).mp hM1
    linarith
  linarith

-- eventual uniform small oscillation of f on grid cells
lemma exists_forall_cell_f_osc {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (f : E ι → ℝ)
    (hfc : Continuous f) (hfsuppR : ∃ R : ℝ, ∀ x : E ι, f x ≠ 0 → ‖x‖ ≤ R)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (g : ι → Fin (n + 1)) (x : E ι), x ∈ cell ι L n g →
      |f x - f (gridPoint ι L n g)| < η := by
  rcases f_modulus f hfc hfsuppR hη with ⟨δ, hδ0, hδ⟩
  have hδ' : 0 < δ / ((Fintype.card ι : ℝ) + 1) := by positivity
  rcases exists_forall_stepL_lt hL (c := δ / ((Fintype.card ι : ℝ) + 1)) hδ' with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn g x hx
  have hs : stepL L n < δ / ((Fintype.card ι : ℝ) + 1) := hN n hn
  have hdiam := norm_sub_gridPoint_cell_le hL.le n g hx
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hlt : ‖x - gridPoint ι L n g‖ < δ := by
    calc
      ‖x - gridPoint ι L n g‖ ≤ ((Fintype.card ι : ℝ) + 1) * stepL L n := hdiam
      _ < δ := by
        rw [← mul_div_cancel₀ δ (ne_of_gt hden)]
        exact mul_lt_mul_of_pos_left hs hden
  exact hδ x (gridPoint ι L n g) hlt

-- |a*b - c*d| ≤ |a-c|*|b| + |c|*|b-d|
lemma abs_mul_sub_mul_le (a b c d : ℝ) : |a * b - c * d| ≤ |a - c| * |b| + |c| * |b - d| := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by ring_nf
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * |b| + |c| * |b - d| := by rw [abs_mul, abs_mul]

-- pointwise cell difference bound for h_u(x) = |inner u x| * f x
lemma cell_h_diff_bound {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) {n : ℕ}
    (g : ι → Fin (n + 1)) (f : E ι → ℝ) {S : ℝ} (hS : ∀ x : E ι, |f x| ≤ S)
    {u : E ι} {x : E ι} (hx : x ∈ cell ι L n g) :
    |(|inner ℝ u (gridPoint ι L n g)| * f (gridPoint ι L n g)) -
      (|inner ℝ u x| * f x)|
      ≤ S * ((Fintype.card ι : ℝ) * stepL L n * ‖u‖) +
        ((Fintype.card ι : ℝ) * L * ‖u‖) * |f (gridPoint ι L n g) - f x| := by
  set c : E ι := gridPoint ι L n g
  have hxqc : x ∈ qcube ι L := cell_subset_qcube L hL.le n g hx
  have hinst := abs_mul_sub_mul_le |inner ℝ u c| (f c) |inner ℝ u x| (f x)
  have hterm1 : |(|inner ℝ u c| - |inner ℝ u x|)| * |f c| ≤
      S * ((Fintype.card ι : ℝ) * stepL L n * ‖u‖) := by
    have htri := abs_abs_sub_abs_le_abs_sub (inner ℝ u c) (inner ℝ u x)
    have hin : |(|inner ℝ u c| - |inner ℝ u x|)| ≤ (Fintype.card ι : ℝ) * stepL L n * ‖u‖ := by
      calc
        |(|inner ℝ u c| - |inner ℝ u x|)| ≤ |inner ℝ u c - inner ℝ u x| := htri
        _ = |inner ℝ u (c - x)| := by
          rw [← inner_sub_right u c x]
        _ = |inner ℝ u (x - c)| := by
          have hsub : c - x = -(x - c) := by abel
          rw [hsub, inner_neg_right, abs_neg]
        _ ≤ (Fintype.card ι : ℝ) * stepL L n * ‖u‖ := cell_inner_diff_bound L hL n g u hx
    have hnonneg : 0 ≤ (Fintype.card ι : ℝ) * stepL L n * ‖u‖ := by
      have hcard : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (Nat.zero_le _)
      have hs : 0 ≤ stepL L n := stepL_nonneg hL.le n
      have hu : 0 ≤ ‖u‖ := norm_nonneg u
      positivity
    calc
      |(|inner ℝ u c| - |inner ℝ u x|)| * |f c|
          ≤ ((Fintype.card ι : ℝ) * stepL L n * ‖u‖) * |f c| :=
            mul_le_mul_of_nonneg_right hin (abs_nonneg _)
      _ ≤ ((Fintype.card ι : ℝ) * stepL L n * ‖u‖) * S :=
            mul_le_mul_of_nonneg_left (hS c) hnonneg
      _ = S * ((Fintype.card ι : ℝ) * stepL L n * ‖u‖) := by ring
  have hinst' : |(|inner ℝ u c| * f c) - (|inner ℝ u x| * f x)| ≤
      |(|inner ℝ u c| - |inner ℝ u x|)| * |f c| + |inner ℝ u x| * |f c - f x| := by
    simpa using hinst
  have hterm2 : |inner ℝ u x| * |f c - f x| ≤
      ((Fintype.card ι : ℝ) * L * ‖u‖) * |f c - f x| := by
    exact mul_le_mul_of_nonneg_right (qcube_inner_abs_bound hL.le hxqc) (abs_nonneg _)
  calc
    |(|inner ℝ u c| * f c) - (|inner ℝ u x| * f x)|
        ≤ |(|inner ℝ u c| - |inner ℝ u x|)| * |f c| + |inner ℝ u x| * |f c - f x| := hinst'
    _ ≤ S * ((Fintype.card ι : ℝ) * stepL L n * ‖u‖) +
        ((Fintype.card ι : ℝ) * L * ‖u‖) * |f c - f x| := add_le_add hterm1 hterm2

-- continuity of h_u(x) = |inner u x| * f x
lemma hfun_cont {ι : Type*} [Fintype ι] (u : E ι) (f : E ι → ℝ) (hfc : Continuous f) :
    Continuous (fun x : E ι => |inner ℝ u x| * f x) := by
  have h1 : Continuous (fun x : E ι => inner ℝ u x) := by
    exact (innerSL ℝ u).continuous
  exact (Continuous.abs h1).mul hfc

-- h_u is integrable on the cube
lemma hfun_integrableOn_qcube {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (u : E ι)
    (f : E ι → ℝ) (hfc : Continuous f) :
    IntegrableOn (fun x : E ι => |inner ℝ u x| * f x) (qcube ι L) volume := by
  let R := Real.sqrt (Fintype.card ι : ℝ) * L + 1
  let K : Set (E ι) := Metric.closedBall (0 : E ι) R
  have hK : IsCompact K := by
    exact isCompact_closedBall (x := (0 : E ι)) (r := R)
  have hsub : qcube ι L ⊆ K := by
    intro x hx
    have hxi : ∀ i : ι, |x i| ≤ L := by
      intro i
      have hlow : -L ≤ x i := (hx i).1
      have hhi : x i ≤ L := le_of_lt (hx i).2
      exact abs_le.mpr ⟨by linarith, hhi⟩
    have hnorm : ‖x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * L := norm_le_sqrt_card_mul hL.le hxi
    simp [K, R]
    linarith
  exact ((hfun_cont u f hfc).continuousOn.integrableOn_compact hK).mono_set hsub

-- integral of a constant over a cell = cell volume * constant
lemma setIntegral_const_cell {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (n : ℕ)
    (g : ι → Fin (n + 1)) (c : ℝ) :
    (∫ x : E ι in cell ι L n g, c) = (stepL L n) ^ Fintype.card ι * c := by
  rw [MeasureTheory.setIntegral_const]
  change (volume (cell ι L n g)).toReal * c = (stepL L n) ^ Fintype.card ι * c
  rw [cell_volume_toReal hL n g]

-- constant is integrable on a cell
lemma integrableOn_const_cell {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (n : ℕ)
    (g : ι → Fin (n + 1)) (cval : ℝ) :
    IntegrableOn (fun _ : E ι => cval) (cell ι L n g) volume := by
  exact MeasureTheory.integrableOn_const (s := cell ι L n g) (μ := volume) (C := cval)
    (by rw [cell_volume_ennreal hL n g]; exact ENNReal.ofReal_lt_top.ne)
    (by finiteness)

-- |∫_cell cval - ∫_cell G| ≤ vol * B when |cval - G| ≤ B on the cell
lemma setIntegral_const_sub_abs_le {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (n : ℕ)
    (g : ι → Fin (n + 1)) (cval : ℝ) (G : E ι → ℝ)
    (hGcont : Continuous G) (hG : IntegrableOn G (cell ι L n g) volume) {B : ℝ}
    (h : ∀ x : E ι, x ∈ cell ι L n g → |cval - G x| ≤ B) :
    |(∫ x : E ι in cell ι L n g, cval) - (∫ x : E ι in cell ι L n g, G x)|
      ≤ (stepL L n) ^ Fintype.card ι * B := by
  let μ : Measure (E ι) := volume.restrict (cell ι L n g)
  have hconst : Integrable (fun _ : E ι => cval) μ := by
    exact integrableOn_const_cell hL.le n g cval
  have hGμ : Integrable G μ := by exact hG
  have hsub : (∫ x : E ι in cell ι L n g, cval) - (∫ x : E ι in cell ι L n g, G x)
           = ∫ x : E ι in cell ι L n g, cval - G x := by
    simpa [μ] using (MeasureTheory.integral_sub (f := fun _ : E ι => cval) (g := G) hconst hGμ).symm
  have habs : |∫ x : E ι in cell ι L n g, cval - G x| ≤
      ∫ x : E ι in cell ι L n g, |cval - G x| := by
    simpa [μ] using (MeasureTheory.abs_integral_le_integral_abs (μ := μ) (f := fun x => cval - G x))
  have hmeas : MeasurableSet {x : E ι | |cval - G x| ≤ B} := by
    have hgcont : Continuous (fun x : E ι => |cval - G x|) :=
      Continuous.abs (continuous_const.sub hGcont)
    have hcl : IsClosed {x : E ι | |cval - G x| ≤ B} := by
      have hEq : {x : E ι | |cval - G x| ≤ B} = (fun x : E ι => cval - G x) ⁻¹' (Set.Icc (-B) B) := by
        ext x
        simp [abs_le]
      rw [hEq]
      exact isClosed_Icc.preimage (continuous_const.sub hGcont)
    exact hcl.measurableSet
  have hae : (fun x : E ι => |cval - G x|) ≤ᵐ[μ] (fun _ : E ι => B) := by
    change ∀ᵐ x ∂μ, |cval - G x| ≤ B
    rw [show μ = volume.restrict (cell ι L n g) by rfl]
    rw [ae_restrict_iff]
    · apply Filter.Eventually.of_forall
      intro x hx
      exact h x hx
    · exact hmeas
  have hfi : Integrable (fun x : E ι => |cval - G x|) μ := by
    simpa [abs_sub_comm] using (hGμ.sub hconst).abs
  have hgi : Integrable (fun _ : E ι => B) μ := by
    exact integrableOn_const_cell hL.le n g B
  have hmono : ∫ x : E ι in cell ι L n g, |cval - G x| ≤ ∫ x : E ι in cell ι L n g, B := by
    simpa [μ] using (MeasureTheory.integral_mono_ae (μ := μ) (f := fun x => |cval - G x|)
      (g := fun _ : E ι => B) hfi hgi hae)
  have hvol : (∫ x : E ι in cell ι L n g, B) = (volume (cell ι L n g)).toReal * B := by
    rw [MeasureTheory.setIntegral_const]
    rfl
  calc
    |(∫ x : E ι in cell ι L n g, cval) - (∫ x : E ι in cell ι L n g, G x)|
        ≤ ∫ x : E ι in cell ι L n g, |cval - G x| := by
            rw [hsub]
            exact habs
    _ ≤ ∫ x : E ι in cell ι L n g, B := hmono
    _ = (volume (cell ι L n g)).toReal * B := hvol
    _ = (stepL L n) ^ Fintype.card ι * B := by rw [cell_volume_toReal hL.le n g]

-- sum of all cell volumes at level n
lemma sum_cell_vol {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (n : ℕ) :
    (∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι) = (2 * L) ^ Fintype.card ι := by
  calc
    (∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι)
        = (Fintype.card (ι → Fin (n + 1)) : ℝ) * (stepL L n) ^ Fintype.card ι := by simp
    _ = (((n + 1) ^ Fintype.card ι : ℕ) : ℝ) * (stepL L n) ^ Fintype.card ι := by
        rw [Fintype.card_fun, Fintype.card_fin]
    _ = ((n + 1 : ℝ) ^ Fintype.card ι) * (stepL L n) ^ Fintype.card ι := by norm_num
    _ = ((n + 1 : ℝ) * stepL L n) ^ Fintype.card ι := by
        rw [mul_pow]
    _ = (2 * L) ^ Fintype.card ι := by
        congr 1
        unfold stepL
        have hden : (n + 1 : ℝ) ≠ 0 := by positivity
        rw [mul_div_cancel₀ (2 * L) hden]

-- derived pointwise bound on a cell (from cell_h_diff_bound)
lemma cell_h_bound_le {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) {n : ℕ}
    (g : ι → Fin (n + 1)) (f : E ι → ℝ) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ x : E ι, |f x| ≤ S) {u : E ι} (hu : ‖u‖ ≤ 1)
    {η : ℝ} (hη0 : 0 ≤ η) {x : E ι} (hx : x ∈ cell ι L n g)
    (hosc : |f x - f (gridPoint ι L n g)| ≤ η) :
    |(|inner ℝ u (gridPoint ι L n g)| * f (gridPoint ι L n g)) -
      (|inner ℝ u x| * f x)|
      ≤ S * ((Fintype.card ι : ℝ) * stepL L n) + (Fintype.card ι : ℝ) * L * η := by
  let c : E ι := gridPoint ι L n g
  have hraw := cell_h_diff_bound (n := n) hL g f hS (u := u) (x := x) hx
  have hterm1 : S * ((Fintype.card ι : ℝ) * stepL L n * ‖u‖) ≤
      S * ((Fintype.card ι : ℝ) * stepL L n) := by
    have hnon : 0 ≤ (Fintype.card ι : ℝ) * stepL L n := by
      have hcard : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (Nat.zero_le _)
      exact mul_nonneg hcard (stepL_nonneg hL.le n)
    have h1 : (Fintype.card ι : ℝ) * stepL L n * ‖u‖ ≤ (Fintype.card ι : ℝ) * stepL L n := by
      calc
        (Fintype.card ι : ℝ) * stepL L n * ‖u‖ ≤ (Fintype.card ι : ℝ) * stepL L n * 1 :=
          mul_le_mul_of_nonneg_left hu hnon
        _ = (Fintype.card ι : ℝ) * stepL L n := by ring
    exact mul_le_mul_of_nonneg_left h1 hS0
  have hterm2 : ((Fintype.card ι : ℝ) * L * ‖u‖) * |f c - f x| ≤
      (Fintype.card ι : ℝ) * L * η := by
    have hosc' : |f c - f x| ≤ η := by simpa [abs_sub_comm] using hosc
    have hnon2 : 0 ≤ (Fintype.card ι : ℝ) * L * ‖u‖ := by
      have hcard : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (Nat.zero_le _)
      positivity
    have hnon3 : 0 ≤ (Fintype.card ι : ℝ) * L := by positivity
    have hstep1 : ((Fintype.card ι : ℝ) * L * ‖u‖) * |f c - f x| ≤
        ((Fintype.card ι : ℝ) * L * ‖u‖) * η := by
      exact mul_le_mul_of_nonneg_left hosc' hnon2
    have hstep2 : ((Fintype.card ι : ℝ) * L * ‖u‖) * η ≤ (Fintype.card ι : ℝ) * L * η := by
      calc
        ((Fintype.card ι : ℝ) * L * ‖u‖) * η = ((Fintype.card ι : ℝ) * L) * (‖u‖ * η) := by ring
        _ ≤ ((Fintype.card ι : ℝ) * L) * η := by
          exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using mul_le_of_le_one_right hη0 hu) hnon3
    linarith
  calc
    |(|inner ℝ u c| * f c) - (|inner ℝ u x| * f x)|
        ≤ S * ((Fintype.card ι : ℝ) * stepL L n * ‖u‖) +
          ((Fintype.card ι : ℝ) * L * ‖u‖) * |f c - f x| := hraw
    _ ≤ S * ((Fintype.card ι : ℝ) * stepL L n) + (Fintype.card ι : ℝ) * L * η := by
        linarith
-- the uniform cell-sum error bound
lemma cellSum_err_bound {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (f : E ι → ℝ)
    (hfout : ∀ x : E ι, x ∉ qcube ι L → f x = 0)
    (hfc : Continuous f) {S : ℝ} (hS0 : 0 ≤ S) (hS : ∀ x : E ι, |f x| ≤ S)
    {n : ℕ} {u : E ι} (hu : ‖u‖ ≤ 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hosc : ∀ (g : ι → Fin (n + 1)) (x : E ι), x ∈ cell ι L n g →
      |f x - f (gridPoint ι L n g)| ≤ η) :
    |(∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι *
        |inner ℝ u (gridPoint ι L n g)| * f (gridPoint ι L n g)) -
      (∫ x : E ι, |inner ℝ u x| * f x)|
      ≤ (2 * L) ^ Fintype.card ι *
          (S * ((Fintype.card ι : ℝ) * stepL L n) + (Fintype.card ι : ℝ) * L * η) := by
  let hf' : E ι → ℝ := fun x => |inner ℝ u x| * f x
  let B : ℝ := S * ((Fintype.card ι : ℝ) * stepL L n) + (Fintype.card ι : ℝ) * L * η
  let cval : (ι → Fin (n + 1)) → ℝ := fun g => |inner ℝ u (gridPoint ι L n g)| * f (gridPoint ι L n g)
  have hI_cells : (∫ x : E ι, |inner ℝ u x| * f x) =
      ∑ g : ι → Fin (n + 1), ∫ x in cell ι L n g, |inner ℝ u x| * f x := by
    calc
      (∫ x : E ι, |inner ℝ u x| * f x) = ∫ x in qcube ι L, |inner ℝ u x| * f x := by
        apply integral_qcube
        intro x hx
        have hz : f x = 0 := hfout x hx
        simp [hz]
      _ = ∑ g : ι → Fin (n + 1), ∫ x in cell ι L n g, |inner ℝ u x| * f x := by
        exact sum_integral_cell hL n (fun x : E ι => |inner ℝ u x| * f x) (hfun_integrableOn_qcube hL u f hfc)
  have hsigma : (∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι * cval g) =
      ∑ g : ι → Fin (n + 1), ∫ x in cell ι L n g, cval g := by
    apply Finset.sum_congr rfl
    intro g hg
    exact (setIntegral_const_cell hL.le n g (cval g)).symm
  have hcells : ∀ g : ι → Fin (n + 1),
      |(∫ x in cell ι L n g, cval g) - (∫ x in cell ι L n g, hf' x)| ≤ (stepL L n) ^ Fintype.card ι * B := by
    intro g
    have hGint : IntegrableOn hf' (cell ι L n g) volume :=
      (hfun_integrableOn_qcube hL u f hfc).mono_set (cell_subset_qcube L hL.le n g)
    apply setIntegral_const_sub_abs_le hL n g (cval g) hf' (hfun_cont u f hfc) hGint
    intro x hx
    change |cval g - |inner ℝ u x| * f x| ≤ B
    have hb := cell_h_bound_le hL g f hS0 hS hu hη0 hx (hosc g x hx)
    simpa [cval, B] using hb
  have hshape : (∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι *
        |inner ℝ u (gridPoint ι L n g)| * f (gridPoint ι L n g)) =
      (∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι * cval g) := by
    apply Finset.sum_congr rfl
    intro g hg
    dsimp [cval]
    ring
  calc
    |(∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι *
        |inner ℝ u (gridPoint ι L n g)| * f (gridPoint ι L n g)) -
      (∫ x : E ι, |inner ℝ u x| * f x)|
        = |(∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι * cval g) -
            (∑ g : ι → Fin (n + 1), ∫ x in cell ι L n g, hf' x)| := by
            rw [hI_cells, hshape]
    _ = |(∑ g : ι → Fin (n + 1), ∫ x in cell ι L n g, cval g) -
            (∑ g : ι → Fin (n + 1), ∫ x in cell ι L n g, hf' x)| := by rw [hsigma]
    _ ≤ ∑ g : ι → Fin (n + 1), |(∫ x in cell ι L n g, cval g) - (∫ x in cell ι L n g, hf' x)| := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs (fun g => (∫ x in cell ι L n g, cval g) - (∫ x in cell ι L n g, hf' x)) Finset.univ
    _ ≤ ∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι * B := Finset.sum_le_sum (fun g hg => hcells g)
    _ = (∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι) * B := by
        rw [Finset.sum_mul]
    _ = (2 * L) ^ Fintype.card ι * B := by
        rw [sum_cell_vol hL n]
    _ = (2 * L) ^ Fintype.card ι *
        (S * ((Fintype.card ι : ℝ) * stepL L n) + (Fintype.card ι : ℝ) * L * η) := by rfl

-- ============ atoms & the main uniform approximation ============
universe u

abbrev cellIdx (ι : Type u) [Fintype ι] (n : ℕ) : Type u := (ι → Fin (n + 1)) × Fin 2

noncomputable def cellAveK (ι : Type u) [Fintype ι] (n : ℕ) : ℕ := Fintype.card (cellIdx ι n)

noncomputable def atomVec {ι : Type u} [Fintype ι] {L : ℝ} {n : ℕ} (f : E ι → ℝ)
    (p : cellIdx ι n) : E ι :=
  let a : ℝ := (stepL L n) ^ Fintype.card ι * f (gridPoint ι L n p.1)
  if p.2 = 0 then a • gridPoint ι L n p.1 else -(a • gridPoint ι L n p.1)

noncomputable def cellAveW {ι : Type u} [Fintype ι] {L : ℝ} (f : E ι → ℝ) (n : ℕ) :
    Fin (cellAveK ι n) → E ι :=
  fun i => atomVec (L := L) f ((Fintype.equivFin (cellIdx ι n)).symm i)

-- the contribution of the two atoms of one cell
lemma atom_pair_sum {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (f : E ι → ℝ)
    (hf₀ : ∀ x : E ι, 0 ≤ f x) (u : E ι) (g : ι → Fin (n + 1)) :
    (∑ b : Fin 2, max 0 (inner ℝ u (atomVec (L := L) f (g, b)))) =
      (stepL L n) ^ Fintype.card ι * f (gridPoint ι L n g) *
        |inner ℝ u (gridPoint ι L n g)| := by
  let a : ℝ := (stepL L n) ^ Fintype.card ι * f (gridPoint ι L n g)
  let t : ℝ := inner ℝ u (gridPoint ι L n g)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (pow_nonneg (stepL_nonneg hL n) _) (hf₀ (gridPoint ι L n g))
  have hb0 : max 0 (inner ℝ u (atomVec (L := L) f (g, (0 : Fin 2)))) = max 0 (a * t) := by
    dsimp [atomVec]
    simp [a, t, inner_smul_real]
  have hb1 : max 0 (inner ℝ u (atomVec (L := L) f (g, (1 : Fin 2)))) = max 0 (-(a * t)) := by
    have h1ne0 : (1 : Fin 2) ≠ 0 := by decide
    dsimp [atomVec]
    simp [a, t, h1ne0, inner_neg_right, inner_smul_real]
  calc
    (∑ b : Fin 2, max 0 (inner ℝ u (atomVec (L := L) f (g, b))))
        = max 0 (a * t) + max 0 (-(a * t)) := by
            rw [Fin.sum_univ_two, hb0, hb1]
    _ = |a * t| := by rw [abs_eq_max_add (a * t)]
    _ = a * |t| := by rw [abs_mul_of_nonneg ha]
    _ = (stepL L n) ^ Fintype.card ι * f (gridPoint ι L n g) *
        |inner ℝ u (gridPoint ι L n g)| := by
            simp [a, t, mul_assoc]

-- sum over atoms equals the cell Riemann sum
lemma cellAve_sum_eq {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (f : E ι → ℝ)
    (hf₀ : ∀ x : E ι, 0 ≤ f x) (u : E ι) (n : ℕ) :
    (∑ i : Fin (cellAveK ι n), max 0 (inner ℝ u (cellAveW (L := L) f n i))) =
      ∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι *
        |inner ℝ u (gridPoint ι L n g)| * f (gridPoint ι L n g) := by
  let gfun : Fin (cellAveK ι n) → ℝ := fun i => max 0 (inner ℝ u (cellAveW (L := L) f n i))
  calc
    (∑ i : Fin (cellAveK ι n), max 0 (inner ℝ u (cellAveW (L := L) f n i)))
        = ∑ i : Fin (cellAveK ι n), gfun i := by simp [gfun]
    _ = ∑ p : cellIdx ι n, gfun ((Fintype.equivFin (cellIdx ι n)) p) :=
        (Equiv.sum_comp (Fintype.equivFin (cellIdx ι n)) gfun).symm
    _ = ∑ p : cellIdx ι n, max 0 (inner ℝ u (atomVec (L := L) f p)) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [gfun, cellAveW, Equiv.symm_apply_apply]
    _ = ∑ g : ι → Fin (n + 1), ∑ b : Fin 2, max 0 (inner ℝ u (atomVec (L := L) f (g, b))) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι * f (gridPoint ι L n g) *
        |inner ℝ u (gridPoint ι L n g)| := by
        apply Finset.sum_congr rfl
        intro g hg
        exact atom_pair_sum hL f hf₀ u g
    _ = ∑ g : ι → Fin (n + 1), (stepL L n) ^ Fintype.card ι *
        |inner ℝ u (gridPoint ι L n g)| * f (gridPoint ι L n g) := by
        apply Finset.sum_congr rfl
        intro g hg
        ring

-- support-norm bound derived from vanishing outside the cube
lemma f_support_norm_of_qcube {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (f : E ι → ℝ)
    (hfout : ∀ x : E ι, x ∉ qcube ι L → f x = 0) :
    ∃ R : ℝ, ∀ x : E ι, f x ≠ 0 → ‖x‖ ≤ R := by
  refine ⟨Real.sqrt (Fintype.card ι : ℝ) * L, ?_⟩
  intro x hx
  have hq : x ∈ qcube ι L := by
    by_contra hn
    exact hx (hfout x hn)
  exact norm_le_sqrt_card_mul hL.le (x := x) (by
    intro i
    have hlow : -L ≤ x i := (hq i).1
    have hhi : x i ≤ L := le_of_lt (hq i).2
    exact abs_le.mpr ⟨by linarith, hhi⟩)

lemma cellAveUniform {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (f : E ι → ℝ)
    (hf₀ : ∀ x : E ι, 0 ≤ f x) (hfc : Continuous f)
    (hfout : ∀ x : E ι, x ∉ qcube ι L → f x = 0) :
    ∃ (k : ℕ → ℕ) (w : ∀ n : ℕ, Fin (k n) → E ι),
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ u : E ι, ‖u‖ ≤ 1 →
        |(∑ i : Fin (k n), max 0 (inner ℝ u (w n i))) -
          ∫ x : E ι, |inner ℝ u x| * f x| < ε := by
  rcases f_support_norm_of_qcube hL f hfout with ⟨R, hR⟩
  rcases exists_f_abs_bound f hfc ⟨R, hR⟩ with ⟨S, hS0, hS⟩
  let d : ℝ := (Fintype.card ι : ℝ)
  let M2 : ℝ := (2 * L) ^ Fintype.card ι
  let K : ℝ := (S + 1) * (d + 1) * (L + 1)
  have hM2 : 0 < M2 := by dsimp [M2]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨cellAveK ι, fun n i => cellAveW (L := L) f n i, ?_⟩
  intro ε hε
  let τ : ℝ := ε / (4 * M2 * K)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  rcases exists_forall_stepL_lt hL (c := τ) hτ with ⟨N1, hN1⟩
  rcases exists_forall_cell_f_osc hL f hfc ⟨R, hR⟩ hτ with ⟨N2, hN2⟩
  let N : ℕ := max N1 N2
  refine ⟨N, ?_⟩
  intro n hn
  have hn1 : n ≥ N1 := le_trans (le_max_left N1 N2) hn
  have hn2 : n ≥ N2 := le_trans (le_max_right N1 N2) hn
  have hs : stepL L n < τ := hN1 n hn1
  have hosc : ∀ (g : ι → Fin (n + 1)) (x : E ι), x ∈ cell ι L n g →
      |f x - f (gridPoint ι L n g)| ≤ τ := by
    intro g x hx
    exact le_of_lt (hN2 n hn2 g x hx)
  intro u hu
  have hbound := cellSum_err_bound hL f hfout hfc hS0 hS hu (le_of_lt hτ) hosc
  have hsmall : M2 *
      (S * (d * stepL L n) + d * L * τ) < ε := by
    have hs0 : 0 ≤ stepL L n := stepL_nonneg hL.le n
    have hK1 : (S + 1) * (d + 1) ≤ K := by
      dsimp [K]
      have h2 : 1 ≤ L + 1 := by linarith
      have h3 : 0 ≤ (S + 1) * (d + 1) := by positivity
      nlinarith
    have hK2 : (d + 1) * (L + 1) ≤ K := by
      dsimp [K]
      have h2 : 1 ≤ S + 1 := by linarith
      have h3 : 0 ≤ (d + 1) * (L + 1) := by positivity
      nlinarith
    have hterm1 : S * (d * stepL L n) ≤ (S + 1) * (d + 1) * stepL L n := by
      have hcard : 0 ≤ d := by dsimp [d]; exact_mod_cast (Nat.zero_le _)
      have hS1 : 0 ≤ S + 1 := by linarith
      have hd1 : 0 ≤ d + 1 := by linarith
      have hprod : S * d ≤ (S + 1) * (d + 1) := by nlinarith
      calc
        S * (d * stepL L n) = S * d * stepL L n := by ring
        _ ≤ (S + 1) * (d + 1) * stepL L n := by
          exact mul_le_mul_of_nonneg_right hprod hs0
    have hterm2 : d * L * τ ≤ (d + 1) * (L + 1) * τ := by
      have hcard : 0 ≤ d := by dsimp [d]; exact_mod_cast (Nat.zero_le _)
      have hprod : d * L ≤ (d + 1) * (L + 1) := by nlinarith
      calc
        d * L * τ = (d * L) * τ := by ring
        _ ≤ (d + 1) * (L + 1) * τ := by exact mul_le_mul_of_nonneg_right hprod hτ.le
    have hterm1K : S * (d * stepL L n) ≤ K * stepL L n := by
      calc
        S * (d * stepL L n) ≤ (S + 1) * (d + 1) * stepL L n := hterm1
        _ ≤ K * stepL L n := by exact mul_le_mul_of_nonneg_right hK1 hs0
    have hterm2K : d * L * τ ≤ K * τ := by
      calc
        d * L * τ ≤ (d + 1) * (L + 1) * τ := hterm2
        _ ≤ K * τ := by exact mul_le_mul_of_nonneg_right hK2 hτ.le
    have htot : S * (d * stepL L n) + d * L * τ ≤ K * (stepL L n + τ) := by
      nlinarith
    have h2 : K * (stepL L n + τ) < 2 * K * τ := by
      have : stepL L n + τ < τ + τ := by linarith
      calc
        K * (stepL L n + τ) < K * (τ + τ) := mul_lt_mul_of_pos_left this hK
        _ = 2 * K * τ := by ring
    have h3 : M2 * (K * (stepL L n + τ)) < ε := by
      have hpos : 0 < M2 * K := mul_pos hM2 hK
      calc
        M2 * (K * (stepL L n + τ)) < M2 * (2 * K * τ) :=
          mul_lt_mul_of_pos_left h2 hM2
        _ = ε / 2 := by
          dsimp [τ]
          field_simp [ne_of_gt hM2, ne_of_gt hK]
          ring
        _ < ε := by linarith
    calc
      M2 * (S * (d * stepL L n) + d * L * τ) ≤ M2 * (K * (stepL L n + τ)) :=
        mul_le_mul_of_nonneg_left htot hM2.le
      _ < ε := h3
  have hfin : |(∑ i : Fin (cellAveK ι n), max 0 (inner ℝ u (cellAveW (L := L) f n i))) -
      (∫ x : E ι, |inner ℝ u x| * f x)| < ε := by
    rw [cellAve_sum_eq hL.le f hf₀ u n]
    exact lt_of_le_of_lt hbound (by simpa [d, M2] using hsmall)
  simpa using hfin

theorem cellAverageSupport_uniform
    {ι : Type*} [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ)
    (hf₀ : ∀ x : EuclideanSpace ℝ ι, 0 ≤ f x)
    (hfc : Continuous f)
    (hfsupp : ∃ R : ℝ, ∀ x : EuclideanSpace ℝ ι, f x ≠ 0 → ‖x‖ ≤ R) :
    ∃ (k : ℕ → ℕ) (w : ∀ n : ℕ, Fin (k n) → EuclideanSpace ℝ ι),
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ u : EuclideanSpace ℝ ι, ‖u‖ ≤ 1 →
        |(∑ i : Fin (k n), max 0 (inner ℝ u (w n i))) -
          ∫ x : EuclideanSpace ℝ ι, |inner ℝ u x| * f x| < ε := by
  rcases hfsupp with ⟨R, hR⟩
  let R0 : ℝ := max R 0
  let L : ℝ := R0 + 1
  have hL0 : 0 < L := by
    have : 0 ≤ R0 := by dsimp [R0]; exact le_max_right R 0
    dsimp [L]
    linarith
  have hRleR0 : R ≤ R0 := by dsimp [R0]; exact le_max_left R 0
  have hR0 : ∀ x : E ι, f x ≠ 0 → ‖x‖ ≤ R0 := by
    intro x hx
    exact le_trans (hR x hx) hRleR0
  have hfout : ∀ x : E ι, x ∉ qcube ι L → f x = 0 := by
    intro x hx
    by_contra hne
    have hnorm_le : ‖x‖ ≤ R0 := hR0 x hne
    have hnot : ¬ (∀ i : ι, -L ≤ x i ∧ x i < L) := by
      simpa [qcube] using hx
    rw [not_forall] at hnot
    rcases hnot with ⟨i, hi⟩
    have hi' : x i < -L ∨ L ≤ x i := by
      rw [not_and_or] at hi
      rcases hi with h1 | h2
      · left
        exact not_le.mp h1
      · right
        exact not_lt.mp h2
    have habs : L ≤ |x i| := by
      rcases hi' with hlt | hge
      · have hxnonpos : x i ≤ 0 := by linarith
        rw [abs_of_nonpos hxnonpos]
        linarith
      · have hxnonneg : 0 ≤ x i := by linarith
        rw [abs_of_nonneg hxnonneg]
        exact hge
    have hnorm_ge : L ≤ ‖x‖ := le_trans habs (coord_abs_le_norm x i)
    have hLgt : R0 < L := by dsimp [L]; linarith
    linarith
  rcases cellAveUniform hL0 f hf₀ hfc hfout with ⟨k, w, hmain⟩
  refine ⟨k, w, ?_⟩
  intro ε hε
  rcases hmain ε hε with ⟨N, hN⟩
  refine eventually_atTop.2 ?_
  refine ⟨N, ?_⟩
  intro n hn
  exact hN n hn

end Commons.Measure.EuclideanSpace