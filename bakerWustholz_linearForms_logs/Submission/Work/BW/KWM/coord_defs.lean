import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.KWM.basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Prerequisites for the coordinate case of Minkowski's second theorem
-/

namespace Work.BW.KWM

open MeasureTheory
open scoped Pointwise
open scoped ENNReal

variable {n : ℕ}

/-! ## The coordinate flag -/

/-- The coordinate subspace `{x | x j = 0 for all j ≥ m}`. -/
def cflag (n m : ℕ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {x | ∀ j : Fin n, m ≤ (j : ℕ) → x j = 0}
  zero_mem' := by intro j _; rfl
  add_mem' := by intro x y hx hy j hj; rw [Pi.add_apply, hx j hj, hy j hj, add_zero]
  smul_mem' := by intro c x hx j hj; rw [Pi.smul_apply, hx j hj, smul_zero]

@[simp] theorem mem_cflag {n m : ℕ} {x : Fin n → ℝ} :
    x ∈ cflag n m ↔ ∀ j : Fin n, m ≤ (j : ℕ) → x j = 0 := Iff.rfl

theorem cflag_mono {n : ℕ} {m m' : ℕ} (h : m ≤ m') : cflag n m ≤ cflag n m' :=
  fun _ hx j hj => hx j (le_trans h hj)

/-! ## The integer cube and its low and high parts -/

/-- The integer cube `{v : Fin n → ℤ | ∀ j, |v j| ≤ q}`. -/
def zcube (n q : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(q : ℤ)) (q : ℤ))

def zcubeLo (n q i : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun j : Fin n =>
    if (j : ℕ) < i then Finset.Icc (-(q : ℤ)) (q : ℤ) else {0})

def zcubeHi (n q i : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun j : Fin n =>
    if (j : ℕ) < i then {0} else Finset.Icc (-(q : ℤ)) (q : ℤ))

/-- The identity map `ℤⁿ → ℝⁿ`. -/
def cvec : (Fin n → ℤ) → (Fin n → ℝ) := fun v i => (v i : ℝ)

theorem cvec_injective : Function.Injective (cvec (n := n)) := by
  intro a b h
  funext i
  have h' : ((a i : ℤ) : ℝ) = ((b i : ℤ) : ℝ) := congrFun h i
  exact_mod_cast h'

@[simp] theorem cvec_apply (v : Fin n → ℤ) (i : Fin n) : cvec v i = (v i : ℝ) := rfl

@[simp] theorem cvec_add (a b : Fin n → ℤ) : cvec (a + b) = cvec a + cvec b := by
  ext i; simp [cvec]

@[simp] theorem cvec_sub (a b : Fin n → ℤ) : cvec (a - b) = cvec a - cvec b := by
  ext i; simp [cvec]

noncomputable def rcube (n q : ℕ) : Finset (Fin n → ℝ) := (zcube n q).image cvec

noncomputable def rcubeLo (n q i : ℕ) : Finset (Fin n → ℝ) := (zcubeLo n q i).image cvec

noncomputable def rcubeHi (n q i : ℕ) : Finset (Fin n → ℝ) := (zcubeHi n q i).image cvec

theorem exists_int_of_mem_rcubeHi {q i : ℕ} {x : Fin n → ℝ} (hx : x ∈ rcubeHi n q i) :
    ∃ v : Fin n → ℤ, x = cvec v := by
  rw [rcubeHi] at hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨v, rfl⟩

theorem exists_int_of_mem_rcubeLo {q i : ℕ} {x : Fin n → ℝ} (hx : x ∈ rcubeLo n q i) :
    ∃ v : Fin n → ℤ, x = cvec v := by
  rw [rcubeLo] at hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨v, rfl⟩

theorem exists_int_of_mem_rcube {q : ℕ} {x : Fin n → ℝ} (hx : x ∈ rcube n q) :
    ∃ v : Fin n → ℤ, x = cvec v := by
  rw [rcube] at hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨v, rfl⟩

theorem mem_rcubeHi_apply {q i : ℕ} {x : Fin n → ℝ} (hx : x ∈ rcubeHi n q i) :
    ∀ j : Fin n, (j : ℕ) < i → x j = 0 := by
  rw [rcubeHi] at hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  rw [zcubeHi, Fintype.mem_piFinset] at hv
  intro j hj
  have h := hv j
  rw [if_pos hj] at h
  simpa [cvec] using h

theorem mem_rcubeLo_apply {q i : ℕ} {x : Fin n → ℝ} (hx : x ∈ rcubeLo n q i) :
    ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0 := by
  rw [rcubeLo] at hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  rw [zcubeLo, Fintype.mem_piFinset] at hv
  intro j hj
  have h := hv j
  rw [if_neg (not_lt.mpr hj)] at h
  simpa [cvec] using h

theorem mem_rcube_apply {q : ℕ} {x : Fin n → ℝ} (hx : x ∈ rcube n q) :
    ∀ j : Fin n, |x j| ≤ (q : ℝ) := by
  rw [rcube] at hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  rw [zcube, Fintype.mem_piFinset] at hv
  intro j
  have h := hv j
  rw [Finset.mem_Icc] at h
  rw [abs_le]
  constructor
  · have h1 : (-(q : ℤ) : ℝ) ≤ (v j : ℝ) := by exact_mod_cast h.1
    simpa [cvec] using h1
  · have h2 : ((v j : ℤ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h.2
    simpa [cvec] using h2

theorem card_rcube (q : ℕ) : (rcube n q).card = (2 * q + 1) ^ n := by
  rw [rcube, Finset.card_image_of_injective _ cvec_injective, zcube, Fintype.card_piFinset]
  have h : ∀ k : Fin n, (Finset.Icc (-(q : ℤ)) (q : ℤ)).card = 2 * q + 1 := by
    intro k
    rw [Int.card_Icc]
    have h1 : ((q : ℤ) + 1 - (-(q : ℤ)) : ℤ) = ((2 * q + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, Int.toNat_natCast]
  rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The cube is the sum of its low and high parts. -/
theorem mem_rcube_iff (q i : ℕ) (x : Fin n → ℝ) :
    x ∈ rcube n q ↔ ∃ w ∈ rcubeHi n q i, ∃ m ∈ rcubeLo n q i, x = w + m := by
  constructor
  · intro hx
    rw [rcube, Finset.mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [zcube, Fintype.mem_piFinset] at hv
    refine ⟨cvec (fun k => if (k : ℕ) < i then 0 else v k), ?_,
      cvec (fun k => if (k : ℕ) < i then v k else 0), ?_, ?_⟩
    · rw [rcubeHi, Finset.mem_image]
      refine ⟨(fun k => if (k : ℕ) < i then 0 else v k), ?_, rfl⟩
      rw [zcubeHi, Fintype.mem_piFinset]
      intro k
      split_ifs with hk
      · exact Finset.mem_singleton_self (0 : ℤ)
      · exact hv k
    · rw [rcubeLo, Finset.mem_image]
      refine ⟨(fun k => if (k : ℕ) < i then v k else 0), ?_, rfl⟩
      rw [zcubeLo, Fintype.mem_piFinset]
      intro k
      split_ifs with hk
      · exact hv k
      · exact Finset.mem_singleton_self (0 : ℤ)
    · ext k
      by_cases hk : (k : ℕ) < i <;> simp [cvec, hk]
  · rintro ⟨w, hw, m, hm, rfl⟩
    rw [rcubeHi] at hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [rcubeLo] at hm
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
    rw [rcube, Finset.mem_image]
    refine ⟨v + u, ?_, ?_⟩
    · rw [zcube, Fintype.mem_piFinset]
      intro k
      rw [zcubeHi, Fintype.mem_piFinset] at hv
      rw [zcubeLo, Fintype.mem_piFinset] at hu
      by_cases hk : (k : ℕ) < i
      · have h1 := hu k; rw [if_pos hk] at h1
        have h2 := hv k; rw [if_pos hk] at h2
        have h3 : v k = 0 := Finset.mem_singleton.mp h2
        rw [Pi.add_apply, h3, zero_add]; exact h1
      · have h1 := hv k; rw [if_neg hk] at h1
        have h2 := hu k; rw [if_neg hk] at h2
        have h3 : u k = 0 := Finset.mem_singleton.mp h2
        rw [Pi.add_apply, h3, add_zero]; exact h1
    · rw [cvec_add]

/-! ## Measure lemmas for translates -/

theorem addSet_eq_iUnion {E : Type*} [Add E] (M : Finset E) (A : Set E) :
    Work.BW.addSet (M : Set E) A = ⋃ w ∈ M, (fun x => w + x) '' A := by
  ext x
  rw [Work.BW.mem_addSet]
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem volume_shift (w : Fin n → ℝ) (A : Set (Fin n → ℝ)) :
    volume ((fun x => w + x) '' A) = volume A := by
  have h : (fun x => w + x) ⁻¹' ((fun x => w + x) '' A) = A := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨a, ha, hxa⟩
      have h' : a = x := add_left_cancel hxa
      rw [h'] at ha
      exact ha
    · exact fun hx => ⟨x, hx, rfl⟩
  conv_rhs => rw [← h]
  rw [MeasureTheory.measure_preimage_add]

theorem volume_real_shift (w : Fin n → ℝ) (A : Set (Fin n → ℝ)) :
    volume.real ((fun x => w + x) '' A) = volume.real A := by
  simp only [MeasureTheory.Measure.real_def, volume_shift w A]

theorem measurableSet_shift {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (m : Fin n → ℝ) :
    MeasurableSet ((fun x => m + x) '' A) := by
  have h : (fun x => m + x) '' A = (fun x => -m + x) ⁻¹' A := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa using ha
    · intro hx; exact ⟨-m + x, hx, by abel⟩
  rw [h]; exact hA.preimage (by fun_prop)

/-- The union of translates of a measurable set of finite measure by a finset, if the translates
are almost everywhere disjoint, has measure the cardinality times the measure of the set. -/
theorem volume_real_biUnion_of_aedisjoint (M : Finset (Fin n → ℝ)) (A : Set (Fin n → ℝ))
    (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (hdisj : ∀ w ∈ M, ∀ w' ∈ M, w ≠ w' →
      AEDisjoint volume ((fun x => w + x) '' A) ((fun x => w' + x) '' A)) :
    volume.real (⋃ w ∈ M, (fun x => w + x) '' A) = M.card * volume.real A := by
  have hmeas : ∀ w ∈ M, NullMeasurableSet ((fun x => w + x) '' A) volume :=
    fun w _ => (measurableSet_shift hA w).nullMeasurableSet
  have h := MeasureTheory.measure_biUnion_finset₀ hdisj hmeas
  have hfin' : ∀ w ∈ M, volume ((fun x => w + x) '' A) ≠ ∞ := by
    intro w _
    rw [volume_shift w A]; exact hfin
  rw [MeasureTheory.Measure.real_def, h, ENNReal.toReal_sum hfin']
  have hterm : ∀ w ∈ M, (volume ((fun x => w + x) '' A)).toReal = (volume A).toReal :=
    fun w _ => volume_real_shift w A
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  rw [MeasureTheory.Measure.real_def]

/-- The measure of a union of translates of a measurable set is at most the number of translates
times the measure of the set. -/
theorem volume_real_biUnion_le (M : Finset (Fin n → ℝ)) (A : Set (Fin n → ℝ))
    (hfin : volume A ≠ ∞) :
    volume.real (⋃ w ∈ M, (fun x => w + x) '' A) ≤ M.card * volume.real A := by
  have h := MeasureTheory.measure_biUnion_finset_le (μ := volume) M
    (fun w => (fun x => w + x) '' A)
  rw [Finset.sum_congr rfl (fun w _ => volume_shift w A), Finset.sum_const, nsmul_eq_mul] at h
  rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def]
  refine le_trans (ENNReal.toReal_mono ?_ h) ?_
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin
  · rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

/-- A convex set with empty interior is null. -/
theorem measure_eq_zero_of_convex_interior_empty {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hint : interior C = ∅) : volume C = 0 := by
  have h1 : C ⊆ frontier C := by
    have h2 : closure C = frontier C := by
      rw [closure_eq_interior_union_frontier, hint, Set.empty_union]
    rw [← h2]
    exact subset_closure
  have h3 : volume (frontier C) = 0 := Convex.addHaar_frontier volume hC
  have h4 : volume C ≤ 0 := by
    calc volume C ≤ volume (frontier C) := measure_mono h1
      _ = 0 := h3
  exact le_antisymm h4 (by simp)

/-- If `y` lies in the interior of a translate of `S`, then `y` minus the translation lies in the
interior of `S`. -/
theorem sub_mem_interior_of_mem_interior_shift {u y : Fin n → ℝ} {S : Set (Fin n → ℝ)}
    (h : y ∈ interior ((fun x => u + x) '' S)) : y - u ∈ interior S := by
  rw [mem_interior_iff_mem_nhds] at h ⊢
  rw [Metric.mem_nhds_iff] at h ⊢
  obtain ⟨ε, hε, hball⟩ := h
  refine ⟨ε, hε, fun z hz => ?_⟩
  have h1 : z + u ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    have h2 : z + u - y = z - (y - u) := by abel
    rw [h2]; exact hz
  have h3 := hball h1
  rw [Set.mem_image] at h3
  obtain ⟨s, hs, hsc⟩ := h3
  have h4 : s = z := by
    have h5 := congrArg (fun t : Fin n → ℝ => -u + t) hsc
    simpa [add_assoc, add_comm, add_left_comm] using h5
  rwa [h4] at hs

end Work.BW.KWM
