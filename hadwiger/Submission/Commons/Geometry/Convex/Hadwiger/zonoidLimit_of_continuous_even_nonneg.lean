import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.hausdorffDist_eq_sSup_support
import Submission.Commons.Geometry.Convex.Hadwiger.support_tendsto_of_tendsto
import Submission.Commons.Geometry.Convex.Hadwiger.klain333_fin1
import Submission.Commons.Geometry.Convex.convexBody_complete
import Submission.Commons.Measure.EuclideanSpace.cellAverageSupport_uniform

open Filter Metric Set MeasureTheory
open scoped Topology BigOperators ENNReal Classical

noncomputable section

namespace Commons.Geometry.Convex.Hadwiger

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


/-! ## box zonotopes in a finite-dimensional inner product space -/
section Zono
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]
private def zonoCube (k : ℕ) : Set (Fin k → ℝ) := Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1)

private def zonoLin (k : ℕ) (w : Fin k → V) : (Fin k → ℝ) →ₗ[ℝ] V where
  toFun := fun t => ∑ i : Fin k, t i • w i
  map_add' := by
    intro x y
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

/-- the set `{Σᵢ tᵢ • wᵢ | tᵢ ∈ [0,1]}` (a "box zonotope": Minkowski sum of
the segments `[0, wᵢ]`). -/
def boxZono (k : ℕ) (w : Fin k → V) : Set V := (zonoLin k w) '' (zonoCube k)

lemma boxZono_mem_iff {k : ℕ} (w : Fin k → V) (x : V) :
    x ∈ boxZono k w ↔ ∃ t : Fin k → ℝ, (∀ i : Fin k, t i ∈ Set.Icc (0 : ℝ) 1) ∧
      x = ∑ i : Fin k, t i • w i := by
  unfold boxZono zonoCube
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ?_, rfl⟩
    intro i
    exact (Set.mem_pi.mp ht i (by simp))
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ?_, rfl⟩
    rw [Set.mem_pi]
    intro i hi
    exact ht i

lemma boxZono_zero_mem (k : ℕ) (w : Fin k → V) : (0 : V) ∈ boxZono k w := by
  rw [boxZono_mem_iff]
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i; exact ⟨by norm_num, by norm_num⟩
  · simp

lemma boxZono_convex (k : ℕ) (w : Fin k → V) : Convex ℝ (boxZono k w) := by
  unfold boxZono
  exact Convex.linear_image (convex_pi (fun _ : Fin k => fun _ => convex_Icc (0 : ℝ) 1))
    (zonoLin k w)

lemma boxZono_isCompact (k : ℕ) (w : Fin k → V) : IsCompact (boxZono k w) := by
  unfold boxZono
  refine IsCompact.image ?_ ?_
  · exact isCompact_univ_pi (fun _ : Fin k => isCompact_Icc)
  · simpa using (LinearMap.continuous_of_finiteDimensional (zonoLin k w))

/-- box zonotope as a `ConvexBody` -/
def boxZonoBody (k : ℕ) (w : Fin k → V) : ConvexBody V :=
  ⟨boxZono k w, boxZono_convex k w, boxZono_isCompact k w, ⟨0, boxZono_zero_mem k w⟩⟩

@[simp] lemma boxZonoBody_coe (k : ℕ) (w : Fin k → V) :
    (boxZonoBody k w : Set V) = boxZono k w := rfl

lemma boxZonoBody_mem_iff {k : ℕ} (w : Fin k → V) (x : V) :
    x ∈ (boxZonoBody k w : Set V) ↔ ∃ t : Fin k → ℝ,
      (∀ i : Fin k, t i ∈ Set.Icc (0 : ℝ) 1) ∧ x = ∑ i : Fin k, t i • w i := by
  simp [boxZono_mem_iff]

-- support function of a box zonotope = Σᵢ max 0 ⟨u, wᵢ⟩
lemma boxZono_inner_le (k : ℕ) (w : Fin k → V) (u : V) {x : V}
    (hx : x ∈ boxZono k w) : inner ℝ u x ≤ ∑ i : Fin k, max 0 (inner ℝ u (w i)) := by
  rcases (boxZono_mem_iff w x).mp hx with ⟨t, ht, rfl⟩
  calc
    inner ℝ u (∑ i : Fin k, t i • w i)
        = ∑ i : Fin k, inner ℝ u (t i • w i) := by
            exact map_sum ((innerSL ℝ u) : V →ₗ[ℝ] ℝ) (fun i : Fin k => t i • w i) Finset.univ
    _ = ∑ i : Fin k, t i * inner ℝ u (w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [inner_smul_right]
    _ ≤ ∑ i : Fin k, max 0 (inner ℝ u (w i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hti : t i ∈ Set.Icc (0 : ℝ) 1 := ht i
        have ht0 : 0 ≤ t i := hti.1
        have ht1 : t i ≤ 1 := hti.2
        by_cases ha : 0 ≤ inner ℝ u (w i)
        · calc
            t i * inner ℝ u (w i) ≤ 1 * inner ℝ u (w i) := by gcongr
            _ = inner ℝ u (w i) := by simp
            _ = max 0 (inner ℝ u (w i)) := by rw [max_eq_right ha]
        · have hneg : inner ℝ u (w i) ≤ 0 := le_of_not_ge ha
          have hmul : t i * inner ℝ u (w i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hneg
          calc
            t i * inner ℝ u (w i) ≤ 0 := hmul
            _ = max 0 (inner ℝ u (w i)) := by rw [max_eq_left hneg]

lemma boxZono_inner_eq_max_sum (k : ℕ) (w : Fin k → V) (u : V) :
    ∃ x ∈ boxZono k w, inner ℝ u x = ∑ i : Fin k, max 0 (inner ℝ u (w i)) := by
  let x : V := ∑ i : Fin k, (if 0 < inner ℝ u (w i) then (1 : ℝ) else 0) • w i
  refine ⟨x, ?_, ?_⟩
  · rw [boxZono_mem_iff]
    refine ⟨fun i => if 0 < inner ℝ u (w i) then (1 : ℝ) else 0, ?_, rfl⟩
    intro i
    by_cases hpos : 0 < inner ℝ u (w i) <;> simp [hpos]
  · calc
    inner ℝ u x = ∑ i : Fin k, inner ℝ u ((if 0 < inner ℝ u (w i) then (1 : ℝ) else 0) • w i) := by
        exact map_sum ((innerSL ℝ u) : V →ₗ[ℝ] ℝ)
          (fun i : Fin k => (if 0 < inner ℝ u (w i) then (1 : ℝ) else 0) • w i) Finset.univ
    _ = ∑ i : Fin k, max 0 (inner ℝ u (w i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hpos : 0 < inner ℝ u (w i)
        · have hnonneg : 0 ≤ inner ℝ u (w i) := le_of_lt hpos
          simp [hpos, inner_smul_right, max_eq_right hnonneg]
        · have hle : inner ℝ u (w i) ≤ 0 := le_of_not_gt hpos
          simp [hpos, inner_smul_right, max_eq_left hle]

/-- The support function of a box zonotope is `Σᵢ max 0 ⟨u, wᵢ⟩`. -/
theorem boxZono_support (k : ℕ) (w : Fin k → V) (u : V) :
    HausdorffSupport.support (boxZonoBody k w) u =
      ∑ i : Fin k, max 0 (inner ℝ u (w i)) := by
  unfold HausdorffSupport.support
  have hbdd : BddAbove ((fun x : V => inner ℝ u x) '' boxZono k w) := by
    refine ⟨∑ i : Fin k, max 0 (inner ℝ u (w i)), ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact boxZono_inner_le k w u hx
  apply le_antisymm
  · apply csSup_le
    · exact ⟨(0 : ℝ), (0 : V), boxZono_zero_mem k w, by simp⟩
    · rintro r ⟨x, hx, rfl⟩
      exact boxZono_inner_le k w u hx
  · rcases boxZono_inner_eq_max_sum k w u with ⟨x, hx, hxeq⟩
    rw [← hxeq]
    exact le_csSup hbdd ⟨x, hx, rfl⟩

/-- the set form of the statement is literally the box zonotope set -/
lemma boxZono_eq_set (k : ℕ) (w : Fin k → V) :
    boxZono k w = {x : V | ∃ t : Fin k → ℝ, (∀ i : Fin k, t i ∈ Set.Icc (0 : ℝ) 1) ∧
      x = ∑ i : Fin k, t i • w i} := by
  ext x
  exact boxZono_mem_iff w x


end Zono

end Commons.Geometry.Convex.Hadwiger

/-! ## Euclidean-space zonoid limit (analytic core + convex assembly) -/

namespace Commons.Geometry.Convex.Hadwiger

open HausdorffSupport

lemma max0_smul_of_nonneg {a c : ℝ} (ha : 0 ≤ a) : max 0 (a * c) = a * max 0 c := by
  by_cases hc : 0 ≤ c
  · have : a * max 0 c = a * c := by rw [max_eq_right hc]
    rw [this, max_eq_right]
    exact mul_nonneg ha hc
  · have hc' : c ≤ 0 := le_of_not_ge hc
    have : a * max 0 c = 0 := by rw [max_eq_left hc', mul_zero]
    rw [this, max_eq_left]
    exact mul_nonpos_of_nonneg_of_nonpos ha hc'

end Commons.Geometry.Convex.Hadwiger
namespace Commons.Geometry.Convex.Hadwiger

section EuclidTheorem

open scoped Topology

/-- homogeneity of the finite max-0 support sums -/
lemma maxSum_homog {ι : Type*} [Fintype ι] {k : ℕ} (w : Fin k → EuclideanSpace ℝ ι)
    {u : EuclideanSpace ℝ ι} {a : ℝ} (ha : 0 ≤ a) :
    ∑ i : Fin k, max 0 (inner ℝ (a • u) (w i)) = a * ∑ i : Fin k, max 0 (inner ℝ u (w i)) := by
  calc
    (∑ i : Fin k, max 0 (inner ℝ (a • u) (w i)))
        = ∑ i : Fin k, a * max 0 (inner ℝ u (w i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [inner_smul_left]
          simp
          rw [max0_smul_of_nonneg ha]
    _ = a * ∑ i : Fin k, max 0 (inner ℝ u (w i)) := by
          rw [Finset.mul_sum]

lemma linear_map_sum_smul {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    (φ : E →ₗ[ℝ] V) {k : ℕ} (t : Fin k → ℝ) (x : Fin k → E) :
    φ (∑ i : Fin k, t i • x i) = ∑ i : Fin k, t i • φ (x i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact map_smul φ (t i) (x i)

/-- the Euclidean-space version of the target theorem -/
theorem zonoidLimit_euclideanSpace {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ)
    (hf₀ : ∀ x : EuclideanSpace ℝ ι, 0 ≤ f x)
    (hf_even : ∀ x : EuclideanSpace ℝ ι, f (-x) = f x)
    (hfc : Continuous f)
    (hfsupp : ∃ R : ℝ, ∀ x : EuclideanSpace ℝ ι, f x ≠ 0 → ‖x‖ ≤ R) :
    ∃ (Y : ConvexBody (EuclideanSpace ℝ ι)) (Z : ℕ → ConvexBody (EuclideanSpace ℝ ι))
      (k : ℕ → ℕ) (w : ∀ n : ℕ, Fin (k n) → EuclideanSpace ℝ ι),
      Tendsto Z atTop (𝓝 Y) ∧
      (∀ n : ℕ, (Z n : Set (EuclideanSpace ℝ ι)) =
        {x : EuclideanSpace ℝ ι | ∃ t : Fin (k n) → ℝ,
          (∀ i : Fin (k n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
          x = ∑ i : Fin (k n), t i • w n i}) ∧
      (∀ u : EuclideanSpace ℝ ι,
        sSup ((fun x : EuclideanSpace ℝ ι => inner ℝ u x) '' (Y : Set (EuclideanSpace ℝ ι))) =
          ∫ x : EuclideanSpace ℝ ι, |inner ℝ u x| * f x) := by
  let E := EuclideanSpace ℝ ι
  rcases Commons.Measure.EuclideanSpace.cellAverageSupport_uniform f hf₀ hfc hfsupp with ⟨k, w, hcore⟩
  let Z : ℕ → ConvexBody E := fun n => boxZonoBody (k n) (w n)
  let hF : E → ℝ := fun u => ∫ x : E, |inner ℝ u x| * f x
  have hZsupp : ∀ n u, HausdorffSupport.support (Z n) u = ∑ i : Fin (k n), max 0 (inner ℝ u (w n i)) := by
    intro n u
    exact boxZono_support (V := E) (k n) (w n) u
  have hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ u : E, ‖u‖ ≤ 1 →
      |HausdorffSupport.support (Z n) u - hF u| < ε := by
    intro ε hε
    filter_upwards [hcore ε hε] with n hn u hu
    simpa [hF, hZsupp] using hn u hu
  have hcauchy : CauchySeq Z := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    let ε' : ℝ := ε / 3
    have hε' : 0 < ε' := by dsimp [ε']; linarith
    have hE : ∀ᶠ n in atTop, ∀ u : E, ‖u‖ ≤ 1 → |HausdorffSupport.support (Z n) u - hF u| < ε' :=
      hunif ε' hε'
    rcases Filter.mem_atTop_sets.mp hE with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hdist : dist (Z m) (Z n) =
        sSup {r : ℝ | ∃ u : E, ‖u‖ = 1 ∧ r = |HausdorffSupport.support (Z m) u - HausdorffSupport.support (Z n) u|} := by
      simpa [HausdorffSupport.support] using (hausdorffDist_eq_sSup_support (V := E) (Z m) (Z n))
    rw [hdist]
    have hle : sSup {r : ℝ | ∃ u : E, ‖u‖ = 1 ∧ r = |HausdorffSupport.support (Z m) u - HausdorffSupport.support (Z n) u|} ≤ 2 * ε' := by
      by_cases hSn : ({r : ℝ | ∃ u : E, ‖u‖ = 1 ∧ r = |HausdorffSupport.support (Z m) u - HausdorffSupport.support (Z n) u|} : Set ℝ).Nonempty
      · apply csSup_le hSn
        rintro r ⟨u, hu, rfl⟩
        have h1 : |HausdorffSupport.support (Z m) u - hF u| < ε' := hN m hm u (by rw [hu])
        have h2 : |hF u - HausdorffSupport.support (Z n) u| < ε' := by
          have h2' := hN n hn u (by rw [hu])
          simpa [abs_sub_comm] using h2'
        have hbnd : |HausdorffSupport.support (Z m) u - HausdorffSupport.support (Z n) u| ≤
            |HausdorffSupport.support (Z m) u - hF u| + |hF u - HausdorffSupport.support (Z n) u| :=
          abs_sub_le _ _ _
        have hlt : |HausdorffSupport.support (Z m) u - HausdorffSupport.support (Z n) u| < 2 * ε' :=
          lt_of_le_of_lt hbnd (by linarith)
        linarith
      · have hSempty : ({r : ℝ | ∃ u : E, ‖u‖ = 1 ∧ r = |HausdorffSupport.support (Z m) u - HausdorffSupport.support (Z n) u|} : Set ℝ) = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hSn
        rw [hSempty, Real.sSup_empty]
        linarith
    exact lt_of_le_of_lt hle (by dsimp [ε']; linarith)
  haveI : CompleteSpace (ConvexBody E) := convexBody_complete E
  obtain ⟨Y, hYlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hZdef : ∀ n : ℕ, (Z n : Set E) = boxZono (k n) (w n) := by
    intro n
    rfl
  have hset : ∀ n : ℕ, (Z n : Set E) =
      {x : E | ∃ t : Fin (k n) → ℝ, (∀ i : Fin (k n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
        x = ∑ i : Fin (k n), t i • w n i} := by
    intro n
    rw [hZdef n]
    exact boxZono_eq_set (k n) (w n)
  -- pointwise limit of the support sums, on unit directions
  have hsum_unit : ∀ u : E, ‖u‖ = 1 → Tendsto
      (fun n : ℕ => ∑ i : Fin (k n), max 0 (inner ℝ u (w n i))) atTop (𝓝 (hF u)) := by
    intro u hu
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases Filter.mem_atTop_sets.mp (hunif ε hε) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hb := hN n hn u (le_of_eq hu)
    simpa [Real.dist_eq, hZsupp] using hb
  have hsupplim : ∀ u : E, Tendsto
      (fun n : ℕ => ∑ i : Fin (k n), max 0 (inner ℝ u (w n i))) atTop
      (𝓝 (HausdorffSupport.support Y u)) := by
    intro u
    have hT := support_tendsto_of_tendsto (V := E) (Z := Z) hYlim u
    have hseq : (fun n : ℕ => ∑ i : Fin (k n), max 0 (inner ℝ u (w n i))) =
        (fun n : ℕ => HausdorffSupport.support (Z n) u) := by
      funext n
      exact (hZsupp n u).symm
    simpa [hseq, HausdorffSupport.support] using hT
  have hnorm_inv_smul {u : E} (hu : u ≠ 0) : u = ‖u‖ • ((‖u‖⁻¹) • u) := by
    calc
      u = (‖u‖ * ‖u‖⁻¹) • u := by
        rw [mul_inv_cancel₀]
        · simp
        · exact ne_of_gt (norm_pos_iff.mpr hu)
      _ = ‖u‖ • ((‖u‖⁻¹) • u) := by rw [smul_smul]
  have hsupportY : ∀ u : E, HausdorffSupport.support Y u = hF u := by
    intro u
    by_cases hz : u = 0
    · subst u
      have hsp : HausdorffSupport.support Y (0 : E) = 0 := by
        unfold HausdorffSupport.support
        have him : ((fun x : E => inner ℝ (0 : E) x) '' (Y : Set E)) = {(0 : ℝ)} := by
          ext r
          constructor
          · rintro ⟨x, hx, rfl⟩
            simp
          · rintro rfl
            refine ⟨Classical.choose Y.nonempty, Classical.choose_spec Y.nonempty, ?_⟩
            simp
        rw [him]
        simp
      have hF0 : hF (0 : E) = 0 := by
        dsimp [hF]
        simp
      rw [hsp, hF0]
    · let wd : E := (‖u‖⁻¹) • u
      have hw : ‖wd‖ = 1 := by
        dsimp [wd]
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u))]
        exact inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hz))
      have hseq : (fun n : ℕ => ∑ i : Fin (k n), max 0 (inner ℝ u (w n i))) =
          (fun n : ℕ => ‖u‖ * ∑ i : Fin (k n), max 0 (inner ℝ wd (w n i))) := by
        funext n
        have hu' : u = ‖u‖ • wd := by
          dsimp [wd]
          exact hnorm_inv_smul hz
        calc
          (∑ i : Fin (k n), max 0 (inner ℝ u (w n i)))
              = ∑ i : Fin (k n), max 0 (inner ℝ (‖u‖ • wd) (w n i)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact congrArg (fun v : E => max 0 (inner ℝ v (w n i))) hu'
          _ = ‖u‖ * (∑ i : Fin (k n), max 0 (inner ℝ wd (w n i))) := by
                  exact maxSum_homog (w := w n) (u := wd) (a := ‖u‖) (norm_nonneg u)
      have hFhom : ‖u‖ * hF wd = hF u := by
        dsimp [hF]
        have hpt : ∀ x : E, |inner ℝ u x| * f x = ‖u‖ * (|inner ℝ wd x| * f x) := by
          intro x
          have hu_eq : inner ℝ u x = ‖u‖ * inner ℝ wd x := by
            have hu'' : u = ‖u‖ • wd := by
              dsimp [wd]
              exact hnorm_inv_smul hz
            calc
              inner ℝ u x = inner ℝ (‖u‖ • wd) x := by
                exact congrArg (fun v : E => inner ℝ v x) hu''
              _ = ‖u‖ * inner ℝ wd x := by rw [inner_smul_left]; simp
          rw [hu_eq, abs_mul, abs_of_nonneg (norm_nonneg u)]
          ring
        calc
          ‖u‖ * ∫ x : E, |inner ℝ wd x| * f x
              = ∫ x : E, ‖u‖ * (|inner ℝ wd x| * f x) := by
                rw [MeasureTheory.integral_const_mul]
          _ = ∫ x : E, |inner ℝ u x| * f x := by
                exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => (hpt x).symm))
      have hconvW : Tendsto (fun n : ℕ => ∑ i : Fin (k n), max 0 (inner ℝ wd (w n i))) atTop
          (𝓝 (hF wd)) := hsum_unit wd hw
      have hc1 : Tendsto (fun n : ℕ => ‖u‖ * ∑ i : Fin (k n), max 0 (inner ℝ wd (w n i))) atTop
          (𝓝 (‖u‖ * hF wd)) := hconvW.const_mul ‖u‖
      have hconvU : Tendsto (fun n : ℕ => ∑ i : Fin (k n), max 0 (inner ℝ u (w n i))) atTop
          (𝓝 (hF u)) := by
        simpa [hseq, hFhom] using hc1
      exact tendsto_nhds_unique (hsupplim u) hconvU
  refine ⟨Y, Z, k, w, hYlim, hset, ?_⟩
  intro u
  simpa [HausdorffSupport.support, hF] using hsupportY u

end EuclidTheorem

theorem zonoidLimit_of_continuous_even_nonneg
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (f : V → ℝ)
    (hf₀ : ∀ x : V, 0 ≤ f x) (hf_even : ∀ x : V, f (-x) = f x)
    (hfc : Continuous f) (hfsupp : ∃ R : ℝ, ∀ x : V, f x ≠ 0 → ‖x‖ ≤ R) :
    ∃ (Y : ConvexBody V) (Z : ℕ → ConvexBody V) (k : ℕ → ℕ) (w : ∀ n : ℕ, Fin (k n) → V),
      Filter.Tendsto Z Filter.atTop (nhds Y) ∧
      (∀ n : ℕ, (Z n : Set V) =
        {x : V | ∃ t : Fin (k n) → ℝ, (∀ i : Fin (k n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
          x = ∑ i : Fin (k n), t i • w n i}) ∧
      (∀ u : V, sSup ((fun x : V => inner ℝ u x) '' (Y : Set V)) =
        ∫ x : V, |inner ℝ u x| * f x) := by
  classical
  let d : ℕ := Module.finrank ℝ V
  let E := EuclideanSpace ℝ (Fin d)
  let b := stdOrthonormalBasis ℝ V
  let e : E ≃ₗᵢ[ℝ] V := b.repr.symm
  let fE : E → ℝ := fun y => f (e y)
  have hf0E : ∀ y : E, 0 ≤ fE y := by
    intro y
    dsimp [fE]
    exact hf₀ (e y)
  have hfevenE : ∀ y : E, fE (-y) = fE y := by
    intro y
    dsimp [fE]
    rw [← hf_even (e y)]
    congr 1
    simp
  have hfcE : Continuous fE := by
    dsimp [fE]
    exact hfc.comp e.continuous
  have hsuppE : ∃ R : ℝ, ∀ y : E, fE y ≠ 0 → ‖y‖ ≤ R := by
    rcases hfsupp with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro y hy
    have hne : f (e y) ≠ 0 := by simpa [fE] using hy
    have hb := hR (e y) hne
    have hn : ‖e y‖ = ‖y‖ := by
      exact (e.norm_map y)
    rw [← hn]
    exact hb
  rcases zonoidLimit_euclideanSpace (ι := Fin d) fE hf0E hfevenE hfcE hsuppE with
    ⟨YE, ZE, kE, wE, hTlimE, hsetE, hsuppThmE⟩
  let Y : ConvexBody V := ConvexBody.imageLIE e YE
  let Z : ℕ → ConvexBody V := fun n => ConvexBody.imageLIE e (ZE n)
  let w : ∀ n : ℕ, Fin (kE n) → V := fun n i => e (wE n i)
  refine ⟨Y, Z, kE, w, ?tlim, ?hset, ?hsupp⟩
  · -- Tendsto (imageLIE is an isometry of metric spaces)
    rw [tendsto_iff_dist_tendsto_zero]
    rw [tendsto_iff_dist_tendsto_zero] at hTlimE
    have hd : (fun n : ℕ => dist (Z n) Y) = (fun n : ℕ => dist (ZE n) YE) := by
      funext n
      simpa [Z, Y] using imageLIE_dist e (ZE n) YE
    simpa [hd] using hTlimE
  · intro n
    rw [show (Z n : Set V) = e '' (ZE n : Set E) by simp [Z]]
    rw [hsetE n]
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      rcases hy with ⟨t, ht, hyt⟩
      refine ⟨t, ht, ?_⟩
      calc
        x = e y := hxy.symm
        _ = e (∑ i : Fin (kE n), t i • wE n i) := by rw [hyt]
        _ = ∑ i : Fin (kE n), t i • e (wE n i) := by
              exact linear_map_sum_smul (e : E →ₗ[ℝ] V) t (wE n)
        _ = ∑ i : Fin (kE n), t i • w n i := by simp [w]
    · rintro ⟨t, ht, hxt⟩
      refine ⟨∑ i : Fin (kE n), t i • wE n i, ⟨t, ht, rfl⟩, ?_⟩
      calc
        e (∑ i : Fin (kE n), t i • wE n i) = ∑ i : Fin (kE n), t i • e (wE n i) := by
              exact linear_map_sum_smul (e : E →ₗ[ℝ] V) t (wE n)
        _ = ∑ i : Fin (kE n), t i • w n i := by simp [w]
        _ = x := hxt.symm
  · intro u
    have hie_gen : ∀ a : V, ∀ b : E, inner ℝ (e.symm a) b = inner ℝ a (e b) := by
      intro a b
      have h1 := (LinearIsometryEquiv.inner_map_map (f := e.symm)) a (e b)
      have hs : e.symm (e b) = b := by simp
      simpa [hs] using h1
    have hsuppTrans : sSup ((fun x : V => inner ℝ u x) '' (Y : Set V)) =
        sSup ((fun y : E => inner ℝ (e.symm u) y) '' (YE : Set E)) := by
      have hYco : (Y : Set V) = e '' (YE : Set E) := by simp [Y]
      have him1 : ((fun x : V => inner ℝ u x) '' (Y : Set V)) =
          ((fun y : E => inner ℝ u (e y)) '' (YE : Set E)) := by
        rw [hYco]
        rw [Set.image_image]
      have him2 : ((fun y : E => inner ℝ u (e y)) '' (YE : Set E)) =
          ((fun y : E => inner ℝ (e.symm u) y) '' (YE : Set E)) := by
        apply congrArg (fun g : E → ℝ => g '' (YE : Set E))
        funext y
        exact (hie_gen u y).symm
      rw [him1, him2]
    have hvalE := hsuppThmE (e.symm u)
    rw [hsuppTrans, hvalE]
    have hmp := LinearIsometryEquiv.measurePreserving (f := e)
    have hemb : MeasurableEmbedding (e : E → V) := (e.toHomeomorph).measurableEmbedding
    have hint : (∫ x : V, |inner ℝ u x| * f x) =
        ∫ y : E, |inner ℝ u (e y)| * f (e y) := by
      simpa using (hmp.integral_comp hemb (g := fun x : V => |inner ℝ u x| * f x)).symm
    have hpt : ∀ y : E, |inner ℝ u (e y)| * f (e y) = |inner ℝ (e.symm u) y| * fE y := by
      intro y
      dsimp [fE]
      rw [hie_gen u y]
    have hcon : (∫ y : E, |inner ℝ (e.symm u) y| * fE y) =
        ∫ y : E, |inner ℝ u (e y)| * f (e y) := by
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => (hpt y).symm))
    exact hcon.trans hint.symm
