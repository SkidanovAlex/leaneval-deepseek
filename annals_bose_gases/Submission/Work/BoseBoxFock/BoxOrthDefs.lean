import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.BoxOrthDefs` — the slab decomposition of the box

Vocabulary for `Work.BoseBoxFock.exists_boxOrthFam`.

The box `Λ = boxL ℓ = ℓ • unitCell = {x | ∀ i, |x i| ≤ ℓ/2}` is cut into `N` disjoint
*slabs* perpendicular to the first coordinate: the `k`-th slab is

`eSlice ℓ N k = {x | x 0 ∈ [a k, a (k+1)), |x 1| ≤ ℓ/2, |x 2| ≤ ℓ/2}`,
`a k = -ℓ/2 + k·(ℓ/N)`,

a half-open product set of volume `ℓ³/N`, contained in `Λ`.  Each slab carries the
normalised indicator `eFun ℓ N k = V^{-1/2}·1_{eSlice ℓ N k}` (`V = ℓ³/N`), so that the
`eFun ℓ N k` are an orthonormal family (in `L²(volume)`) of bounded functions supported
in the box.

These are the building blocks of the orthonormal family of `exists_boxOrthFam`: since
`L²(Λ)` is infinite-dimensional, one may add as many orthogonality conditions as one
likes.
-/

noncomputable section

open MeasureTheory Set

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock

/-- `∀ i : Fin 3, P i` as a conjunction of the three coordinates. -/
lemma forall_fin_three {P : Fin 3 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ i => by fin_cases i <;> assumption⟩

/-- The `k`-th division point of `[-ℓ/2, ℓ/2]` into `N` equal parts. -/
def sPt (ℓ : ℝ) (N k : ℕ) : ℝ := -(ℓ / 2) + (k : ℝ) * (ℓ / N)

/-- Lower corner of the `k`-th slab. -/
def sliceLo (ℓ : ℝ) (N : ℕ) (k : ℕ) : Fin 3 → ℝ :=
  fun j => if j = 0 then sPt ℓ N k else -(ℓ / 2)

/-- Upper corner of the `k`-th slab. -/
def sliceHi (ℓ : ℝ) (N : ℕ) (k : ℕ) : Fin 3 → ℝ :=
  fun j => if j = 0 then sPt ℓ N (k + 1) else ℓ / 2

@[simp] lemma sliceLo_0 (ℓ : ℝ) (N k : ℕ) : sliceLo ℓ N k 0 = sPt ℓ N k := if_pos rfl
@[simp] lemma sliceLo_1 (ℓ : ℝ) (N k : ℕ) : sliceLo ℓ N k 1 = -(ℓ / 2) :=
  if_neg (by decide : (1 : Fin 3) ≠ 0)
@[simp] lemma sliceLo_2 (ℓ : ℝ) (N k : ℕ) : sliceLo ℓ N k 2 = -(ℓ / 2) :=
  if_neg (by decide : (2 : Fin 3) ≠ 0)
@[simp] lemma sliceHi_0 (ℓ : ℝ) (N k : ℕ) : sliceHi ℓ N k 0 = sPt ℓ N (k + 1) := if_pos rfl
@[simp] lemma sliceHi_1 (ℓ : ℝ) (N k : ℕ) : sliceHi ℓ N k 1 = ℓ / 2 :=
  if_neg (by decide : (1 : Fin 3) ≠ 0)
@[simp] lemma sliceHi_2 (ℓ : ℝ) (N k : ℕ) : sliceHi ℓ N k 2 = ℓ / 2 :=
  if_neg (by decide : (2 : Fin 3) ≠ 0)

/-- The `k`-th slab as a product set in coordinates. -/
def piSlice (ℓ : ℝ) (N : ℕ) (k : ℕ) : Set (Fin 3 → ℝ) :=
  Set.univ.pi fun j : Fin 3 => Set.Ico (sliceLo ℓ N k j) (sliceHi ℓ N k j)

/-- The `k`-th slab of the box `Λ(ℓ)`: the points of the box whose first coordinate lies
in `[a k, a (k+1))`. -/
def eSlice (ℓ : ℝ) (N : ℕ) (k : Fin N) : Set ℝ³ :=
  {x | x 0 ∈ Set.Ico (sPt ℓ N (k : ℕ)) (sPt ℓ N ((k : ℕ) + 1)) ∧
       x 1 ∈ Set.Ico (-(ℓ / 2)) (ℓ / 2) ∧
       x 2 ∈ Set.Ico (-(ℓ / 2)) (ℓ / 2)}

/-- The volume of a slab: `ℓ³/N`. -/
def slVol (ℓ : ℝ) (N : ℕ) : ℝ := (ℓ / N) * ℓ * ℓ

/-- The normalisation of the slab indicator: `V^{-1/2}`. -/
def slScale (ℓ : ℝ) (N : ℕ) : ℝ := (Real.sqrt (slVol ℓ N))⁻¹

/-- The normalised indicator of the `k`-th slab. -/
def eFun (ℓ : ℝ) (N : ℕ) (k : Fin N) : ℝ³ → ℂ :=
  fun x => ((slScale ℓ N : ℝ) : ℂ) * (eSlice ℓ N k).indicator (fun _ => (1 : ℂ)) x

/-- **Membership in the box is the coordinate bound** (`Λ(ℓ) = ℓ • unitCell`). -/
lemma mem_corpusBox_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ³) :
    x ∈ Work.BoseK15.corpusBox.boxL ℓ ↔ ∀ i, |x i| ≤ ℓ / 2 := by
  have hcancel : ∀ a : ℝ, ℓ * (ℓ⁻¹ * a) = a := by
    intro a; rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ), one_mul]
  have hhalf : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by
    rw [← mul_div_assoc, inv_mul_cancel₀ (ne_of_gt hℓ), one_div]
  have hhalf' : ℓ⁻¹ * (-(ℓ / 2)) = -(1 / 2) := by rw [mul_neg, hhalf]
  rw [Work.BoseB4.BoxData.boxL, Work.BoseK15.corpusBox,
    Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]
  simp only [Work.BoseB4.unitCell, Set.mem_ofPred_eq]
  constructor
  · intro h i
    have hi := h i
    simp only [PiLp.smul_apply, smul_eq_mul] at hi
    rw [abs_le] at hi ⊢
    have h2 : ℓ * (ℓ⁻¹ * x i) ≤ ℓ * (1 / 2) := mul_le_mul_of_nonneg_left hi.2 hℓ.le
    have h3 : ℓ * (-(1 / 2)) ≤ ℓ * (ℓ⁻¹ * x i) := mul_le_mul_of_nonneg_left hi.1 hℓ.le
    rw [hcancel] at h2 h3
    constructor <;> linarith
  · intro h i
    have hi := h i
    rw [abs_le] at hi
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [abs_le]
    have hpos : (0 : ℝ) ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
    have h2 : ℓ⁻¹ * (-(ℓ / 2)) ≤ ℓ⁻¹ * x i := mul_le_mul_of_nonneg_left hi.1 hpos
    have h3 : ℓ⁻¹ * x i ≤ ℓ⁻¹ * (ℓ / 2) := mul_le_mul_of_nonneg_left hi.2 hpos
    rw [hhalf'] at h2
    rw [hhalf] at h3
    constructor <;> linarith

/-- The slab as a product set (the form in which its volume is computed). -/
lemma eSlice_eq_preimage (ℓ : ℝ) (N : ℕ) (k : Fin N) :
    eSlice ℓ N k = (WithLp.ofLp : ℝ³ → (Fin 3 → ℝ)) ⁻¹' piSlice ℓ N (k : ℕ) := by
  ext x
  simp only [eSlice, Set.mem_ofPred_eq, Set.mem_preimage, piSlice, Set.mem_univ_pi,
    forall_fin_three, sliceLo_0, sliceLo_1, sliceLo_2, sliceHi_0, sliceHi_1, sliceHi_2]

lemma measurableSet_piSlice (ℓ : ℝ) (N k : ℕ) : MeasurableSet (piSlice ℓ N k) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico

lemma measurableSet_eSlice (ℓ : ℝ) (N : ℕ) (k : Fin N) : MeasurableSet (eSlice ℓ N k) := by
  rw [eSlice_eq_preimage ℓ N k]
  exact (measurableSet_piSlice ℓ N (k : ℕ)).preimage
    (PiLp.volume_preserving_ofLp (Fin 3)).measurable

/-- **The volume of a slab is `ℓ³/N`.** -/
lemma volume_eSlice {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 0 < N) (k : Fin N) :
    volume (eSlice ℓ N k) = ENNReal.ofReal (slVol ℓ N) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hd : 0 < ℓ / N := div_pos hℓ hNpos
  rw [eSlice_eq_preimage ℓ N k]
  rw [MeasureTheory.MeasurePreserving.measure_preimage
    (PiLp.volume_preserving_ofLp (Fin 3))
    ((measurableSet_piSlice ℓ N (k : ℕ)).nullMeasurableSet)]
  rw [piSlice, Real.volume_pi_Ico, Fin.prod_univ_three]
  have h0 : sliceHi ℓ N (k : ℕ) 0 - sliceLo ℓ N (k : ℕ) 0 = ℓ / N := by
    simp only [sliceHi_0, sliceLo_0, sPt]
    push_cast
    ring
  have h1 : sliceHi ℓ N (k : ℕ) 1 - sliceLo ℓ N (k : ℕ) 1 = ℓ := by
    rw [sliceHi_1, sliceLo_1]; ring
  have h2 : sliceHi ℓ N (k : ℕ) 2 - sliceLo ℓ N (k : ℕ) 2 = ℓ := by
    rw [sliceHi_2, sliceLo_2]; ring
  rw [h0, h1, h2]
  rw [← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul (mul_nonneg hd.le hℓ.le)]
  simp only [slVol]

/-- The `k`-th slab lies in the box. -/
lemma eSlice_subset_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 0 < N) (k : Fin N) :
    eSlice ℓ N k ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro x hx
  rw [mem_corpusBox_boxL hℓ, forall_fin_three]
  obtain ⟨h0, h1, h2⟩ := hx
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hd : 0 < ℓ / N := div_pos hℓ hNpos
  have hlo : -(ℓ / 2) ≤ sPt ℓ N (k : ℕ) := by
    simp only [sPt]
    have h : (0 : ℝ) ≤ ((k : ℕ) : ℝ) * (ℓ / N) :=
      mul_nonneg (Nat.cast_nonneg _) hd.le
    linarith
  have hhi : sPt ℓ N ((k : ℕ) + 1) ≤ ℓ / 2 := by
    simp only [sPt]
    have hk1 : ((k : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
      have h : (k : ℕ) + 1 ≤ N := Nat.succ_le_of_lt k.2
      exact_mod_cast h
    have h3 : (((k : ℕ) + 1 : ℕ) : ℝ) * (ℓ / N) ≤ (N : ℝ) * (ℓ / N) :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hd.le
    have h4 : (N : ℝ) * (ℓ / N) = ℓ := by field_simp
    linarith [h3, h4.le, h4.ge]
  refine ⟨abs_le.mpr ⟨le_trans hlo (Set.mem_Ico.mp h0).1,
    le_trans (le_of_lt (Set.mem_Ico.mp h0).2) hhi⟩, ?_, ?_⟩
  · exact abs_le.mpr ⟨(Set.mem_Ico.mp h1).1, (Set.mem_Ico.mp h1).2.le⟩
  · exact abs_le.mpr ⟨(Set.mem_Ico.mp h2).1, (Set.mem_Ico.mp h2).2.le⟩

/-- Distinct slabs are disjoint (their first-coordinate intervals are half-open and
consecutive). -/
lemma eSlice_disjoint {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 0 < N) {k l : Fin N}
    (hkl : k ≠ l) : eSlice ℓ N k ∩ eSlice ℓ N l = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxk, hxl⟩
  obtain ⟨hk0, -, -⟩ := hxk
  obtain ⟨hl0, -, -⟩ := hxl
  rw [Set.mem_Ico] at hk0 hl0
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hd : 0 < ℓ / N := div_pos hℓ hNpos
  have hmono : ∀ a b : ℕ, a ≤ b → sPt ℓ N a ≤ sPt ℓ N b := by
    intro a b hab
    simp only [sPt]
    have h : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have h2 := mul_le_mul_of_nonneg_right h hd.le
    linarith [h2]
  rcases lt_or_gt_of_ne (fun h : (k : ℕ) = (l : ℕ) => hkl (Fin.ext h)) with hlt | hlt
  · have h2 : sPt ℓ N ((k : ℕ) + 1) ≤ sPt ℓ N (l : ℕ) := hmono _ _ (Nat.succ_le_of_lt hlt)
    linarith [hk0.2, hl0.1]
  · have h2 : sPt ℓ N ((l : ℕ) + 1) ≤ sPt ℓ N (k : ℕ) := hmono _ _ (Nat.succ_le_of_lt hlt)
    linarith [hl0.2, hk0.1]

/-- Pointwise: a slab indicator is real-valued, so it is fixed by `star`. -/
lemma star_eFun (ℓ : ℝ) (N : ℕ) (k : Fin N) (x : ℝ³) :
    (starRingEnd ℂ) (eFun ℓ N k x) = eFun ℓ N k x := by
  classical
  by_cases hx : x ∈ eSlice ℓ N k
  · rw [eFun, Set.indicator_of_mem hx, mul_one]
    exact Complex.conj_ofReal _
  · rw [eFun, Set.indicator_of_notMem hx, mul_zero, map_zero]

/-- The value of a slab indicator on the slab. -/
lemma eFun_of_mem {ℓ : ℝ} {N : ℕ} {k : Fin N} {x : ℝ³} (hx : x ∈ eSlice ℓ N k) :
    eFun ℓ N k x = ((slScale ℓ N : ℝ) : ℂ) := by
  rw [eFun, Set.indicator_of_mem hx, mul_one]

/-- The value of a slab indicator off the slab. -/
lemma eFun_of_notMem {ℓ : ℝ} {N : ℕ} {k : Fin N} {x : ℝ³} (hx : x ∉ eSlice ℓ N k) :
    eFun ℓ N k x = 0 := by
  rw [eFun, Set.indicator_of_notMem hx, mul_zero]

end Work.BoseBoxFock
