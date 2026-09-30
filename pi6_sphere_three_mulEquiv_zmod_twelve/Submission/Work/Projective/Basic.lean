import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# Complex projective space: the basic definitions

This is the first module of the *projective* chapter, the "generator side" of the dimension-`4` and
dimension-`8` Hirzebruch signature theorems (`Submission/NOTES.md` §§8.4, 15.4–15.8): the smooth
manifold `ℂPⁿ`, its cohomology ring `ℤ[h]/(h^{n+1})`, its tangent bundle and its Pontryagin
numbers.

Here we set up the underlying object and its standard affine charts:

* `Work.Projective.CPV n = Fin (n+1) → ℂ`, the vector space `ℂ^{n+1}`;
* `Work.Projective.CP n = ℙ ℂ (CPV n)`, complex projective `n`-space, as Mathlib's
  `Projectivization` of `ℂ^{n+1}` (a quotient of the nonzero vectors by scaling);
* the **quotient topology**, making `cpMk n : {v // v ≠ 0} → CP n` a quotient map (this is the
  topology of `ℂPⁿ`; compactness, connectedness and the identification `ℂP¹ ≃ₜ S²` are in
  `Work.Projective.Topology`);
* the **affine chart at `i`**: the open set `chartSet i ⊆ CP n` of points whose `i`-th homogeneous
  coordinate is nonzero, the chart map `chartFun i p = (rep p (i.succAbove k) / rep p i)_k` and its
  inverse `chartInv i w = [⋯ : 1 : ⋯]` (the point with `i`-th coordinate `1` and the coordinates
  `i.succAbove k` equal to `w k`).

## Conventions

* Charts are indexed by `Fin (n+1)` and take values in the model space `Fin n → ℂ` (a normed
  `ℝ`-vector space of real dimension `2n`); `Work.Projective.Model` re-charts everything over
  `EuclideanSpace ℝ (Fin (2*n))`.
* `Fin.succAbove i : Fin n → Fin (n+1)` is the order embedding which skips `i`,
  `Fin.insertNth i x w` is the vector with `i`-th coordinate `x` and `i.succAbove k`-th coordinate
  `w k`, and `Work.Projective.removeAbove i j h` is the index of `j` in that parametrisation:
  `Fin.insertNth i x w j = w (removeAbove i j h)` for `j ≠ i`.

## Main definitions

* `Work.Projective.CP`, `Work.Projective.cpMk`, `Work.Projective.instTopologicalSpaceCP`;
* `Work.Projective.removeAbove`, `Work.Projective.chartFun`, `Work.Projective.chartInv`,
  `Work.Projective.chartSet`.

The charts are assembled into a smooth atlas in `Work.Projective.Atlas`.
-/

open scoped LinearAlgebra.Projectivization Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-- The vector space `ℂ^{n+1}` whose projectivisation is `ℂPⁿ`. -/
abbrev CPV (n : ℕ) : Type := Fin (n + 1) → ℂ

/-- **Complex projective `n`-space** `ℂPⁿ`, the projectivisation of `ℂ^{n+1}`. -/
abbrev CP (n : ℕ) : Type := Projectivization ℂ (CPV n)

/-- The quotient map `ℂ^{n+1} ∖ {0} → ℂPⁿ`. -/
def cpMk (n : ℕ) : {v : CPV n // v ≠ 0} → CP n :=
  fun v => Projectivization.mk' ℂ v

/-- **The topology on `ℂPⁿ`**: the quotient topology of `ℂ^{n+1} ∖ {0}`, so that `cpMk n` is a
quotient map. -/
instance instTopologicalSpaceCP (n : ℕ) : TopologicalSpace (CP n) :=
  TopologicalSpace.coinduced (cpMk n) inferInstance

/-- `cpMk n` is the quotient map defining the topology of `ℂPⁿ`. -/
theorem isQuotientMap_cpMk (n : ℕ) : Topology.IsQuotientMap (cpMk n) :=
  isQuotientMap_quotient_mk'

@[simp] theorem cpMk_apply (n : ℕ) (v : {v : CPV n // v ≠ 0}) :
    cpMk n v = Projectivization.mk ℂ v.1 v.2 :=
  Projectivization.mk'_eq_mk ℂ v

theorem cpMk_surjective (n : ℕ) : Function.Surjective (cpMk n) :=
  (isQuotientMap_cpMk n).surjective

theorem continuous_cpMk (n : ℕ) : Continuous (cpMk n) :=
  continuous_quotient_mk'

/-- Two nonzero vectors defining the same point of `ℂPⁿ` differ by a nonzero scalar. -/
theorem cpMk_eq_iff (n : ℕ) (v w : {v : CPV n // v ≠ 0}) :
    cpMk n v = cpMk n w ↔ ∃ a : ℂ, a • (w : CPV n) = (v : CPV n) := by
  rw [cpMk_apply, cpMk_apply]
  exact Projectivization.mk_eq_mk_iff' ℂ (v : CPV n) (w : CPV n) v.2 w.2

/-- A point of `ℂPⁿ` is nonzero in the coordinate `i` for one representative iff for all. -/
theorem cpMk_eq_iff_coord (n : ℕ) (v w : {v : CPV n // v ≠ 0}) (h : cpMk n v = cpMk n w)
    (i : Fin (n + 1)) : v.1 i ≠ 0 ↔ w.1 i ≠ 0 := by
  obtain ⟨a, ha⟩ := (cpMk_eq_iff n v w).mp h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact v.2 ha.symm
  rw [← ha, Pi.smul_apply]
  exact mul_ne_zero_iff.trans (and_iff_right ha0)

/-! ## Removing one coordinate -/

/-- **The index of `j` in the parametrisation which omits `i`**: for `j ≠ i` this is the index `k`
with `i.succAbove k = j`. -/
def removeAbove {n : ℕ} (i j : Fin (n + 1)) (h : j ≠ i) : Fin n :=
  if hlt : j < i then j.castPred (Fin.ne_last_of_lt (lt_of_lt_of_le hlt (Fin.le_last i)))
  else j.pred (Fin.ne_zero_of_lt (lt_of_le_of_ne (Fin.not_lt.mp hlt) h.symm))

/-- The defining property of `removeAbove`: `insertNth i x w` takes the value `w k` at
`i.succAbove k`, and `removeAbove` inverts `succAbove`. -/
theorem insertNth_apply_of_ne {n : ℕ} (i j : Fin (n + 1)) (h : j ≠ i) (x : ℂ) (w : Fin n → ℂ) :
    (Fin.insertNth (α := fun _ => ℂ) i x w) j = w (removeAbove i j h) := by
  rw [removeAbove]
  by_cases hlt : j < i
  · rw [dif_pos hlt, Fin.insertNth_apply_below hlt]
    simp
  · rw [dif_neg hlt]
    have hgt : i < j := lt_of_le_of_ne (Fin.not_lt.mp hlt) (Ne.symm h)
    rw [Fin.insertNth_apply_above hgt]
    simp

/-- `succAbove` is a section of `removeAbove`. -/
theorem succAbove_removeAbove {n : ℕ} (i j : Fin (n + 1)) (h : j ≠ i) :
    i.succAbove (removeAbove i j h) = j := by
  rw [removeAbove]
  by_cases hlt : j < i
  · rw [dif_pos hlt]
    exact Fin.succAbove_castPred_of_lt i j hlt
  · rw [dif_neg hlt]
    exact Fin.succAbove_pred_of_lt i j (lt_of_le_of_ne (Fin.not_lt.mp hlt) (Ne.symm h))

/-- `removeAbove i` is the inverse of `succAbove i` on the complement of `i`. -/
theorem removeAbove_succAbove {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    removeAbove i (i.succAbove k) (Fin.succAbove_ne i k) = k :=
  Fin.succAbove_right_injective (by rw [succAbove_removeAbove])

/-- Continuity of `w ↦ Fin.insertNth i 1 w`. -/
theorem continuous_insertNth_one {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun w : Fin n → ℂ =>
      (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w : Fin (n + 1) → ℂ)) := by
  have key : (fun w : Fin n → ℂ =>
        (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w : Fin (n + 1) → ℂ))
      = fun w j => if h : j = i then 1 else w (removeAbove i j h) := by
    funext w j
    by_cases h : j = i
    · subst h; simp [Fin.insertNth_apply_same]
    · rw [dif_neg h, insertNth_apply_of_ne i j h]
  rw [key]
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · simp only [dif_pos h]; exact continuous_const
  · simp only [dif_neg h]; exact continuous_apply _

/-! ## The chart maps -/

/-- The chart map at `i`, on the level of nonzero vectors: `v ↦ (v (i.succAbove k) / v i)_k`. -/
def chartFunAux {n : ℕ} (i : Fin (n + 1)) (v : {v : CPV n // v ≠ 0}) : Fin n → ℂ :=
  fun k => v.1 (i.succAbove k) / v.1 i

/-- `chartFunAux` is invariant under scaling, so that it descends to `ℂPⁿ`. -/
theorem chartFunAux_wd {n : ℕ} (i : Fin (n + 1)) (a b : {v : CPV n // v ≠ 0}) (t : ℂ)
    (h : (a : CPV n) = t • (b : CPV n)) : chartFunAux i a = chartFunAux i b := by
  funext k
  have hk : a.1 (i.succAbove k) = t * b.1 (i.succAbove k) := by
    simpa using congrFun h (i.succAbove k)
  have hi : a.1 i = t * b.1 i := by simpa using congrFun h i
  have ht : t ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at h
    exact a.2 h
  simp only [chartFunAux, hk, hi]
  exact mul_div_mul_left _ _ ht

/-- **The chart map at `i`**: `p ↦ (z (i.succAbove k)/z i)_k` for any representative `z` of `p`. -/
def chartFun {n : ℕ} (i : Fin (n + 1)) : CP n → (Fin n → ℂ) :=
  Projectivization.lift (chartFunAux i) (chartFunAux_wd i)

@[simp] theorem chartFun_mk {n : ℕ} (i : Fin (n + 1)) (v : CPV n) (hv : v ≠ 0) :
    chartFun i (Projectivization.mk ℂ v hv) = chartFunAux i ⟨v, hv⟩ := rfl

@[simp] theorem chartFun_cpMk {n : ℕ} (i : Fin (n + 1)) (v : {v : CPV n // v ≠ 0}) :
    chartFun i (cpMk n v) = chartFunAux i v := rfl

/-- `Fin.insertNth i 1 w` is a nonzero vector. -/
theorem insertNth_one_ne_zero {n : ℕ} (i : Fin (n + 1)) (w : Fin n → ℂ) :
    (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w : Fin (n + 1) → ℂ) ≠ 0 := fun h => by
  have hh := congrFun h i
  rw [Fin.insertNth_apply_same, Pi.zero_apply] at hh
  exact one_ne_zero hh

/-- **The inverse chart map at `i`**: the point with `i`-th homogeneous coordinate `1` and
`i.succAbove k`-th coordinate `w k`. -/
def chartInv {n : ℕ} (i : Fin (n + 1)) : (Fin n → ℂ) → CP n :=
  fun w => cpMk n ⟨Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w, insertNth_one_ne_zero i w⟩

theorem chartInv_apply {n : ℕ} (i : Fin (n + 1)) (w : Fin n → ℂ) :
    chartInv i w = cpMk n ⟨Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w,
      insertNth_one_ne_zero i w⟩ := rfl

/-- `chartInv i` is a right inverse of `chartFun i`. -/
theorem chartFun_chartInv {n : ℕ} (i : Fin (n + 1)) (w : Fin n → ℂ) :
    chartFun i (chartInv i w) = w := by
  rw [chartInv_apply, chartFun_cpMk]
  funext k
  simp [chartFunAux, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- `Fin.insertNth i 1 (chartFunAux i v)` is the rescaling `(v i)⁻¹ • v` of `v` (when the `i`-th
coordinate of `v` is nonzero, so that `chartFunAux i v` is a regular parametrisation). -/
theorem insertNth_chartFunAux {n : ℕ} (i : Fin (n + 1)) (v : {v : CPV n // v ≠ 0})
    (hi : v.1 i ≠ 0) :
    Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) (chartFunAux i v) = (v.1 i)⁻¹ • v.1 := by
  funext j
  by_cases h : j = i
  · subst h
    rw [Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul]
    exact (inv_mul_cancel₀ hi).symm
  · rw [insertNth_apply_of_ne i j h, Pi.smul_apply, smul_eq_mul, chartFunAux,
      succAbove_removeAbove]
    field_simp

/-- **`chartInv i` is a left inverse of `chartFun i` on the chart.** -/
theorem chartInv_chartFun {n : ℕ} (i : Fin (n + 1)) (p : CP n)
    (hp : p ∈ Set.range (chartInv i)) : chartInv i (chartFun i p) = p := by
  obtain ⟨w, rfl⟩ := hp
  rw [chartFun_chartInv]

/-- **The chart domain at `i`**: the image of `chartInv i`, i.e. the set of points whose `i`-th
homogeneous coordinate is nonzero. -/
def chartSet {n : ℕ} (i : Fin (n + 1)) : Set (CP n) := Set.range (chartInv i)

theorem chartInv_mem_chartSet {n : ℕ} (i : Fin (n + 1)) (w : Fin n → ℂ) :
    chartInv i w ∈ chartSet i := ⟨w, rfl⟩

/-- A point of `ℂPⁿ` is in the chart at `i` iff its `i`-th coordinate is nonzero, for any
representative. -/
theorem mem_chartSet_iff {n : ℕ} (i : Fin (n + 1)) (v : {v : CPV n // v ≠ 0}) :
    cpMk n v ∈ chartSet i ↔ v.1 i ≠ 0 := by
  constructor
  · rintro ⟨w, hw⟩
    have h1 : cpMk n ⟨Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w,
        insertNth_one_ne_zero i w⟩ = cpMk n v := by
      rw [← chartInv_apply i w, hw]
    obtain ⟨a, ha⟩ := (cpMk_eq_iff n _ v).mp h1
    have hai : (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) i = 1 :=
      Fin.insertNth_apply_same (α := fun _ => ℂ) i 1 w
    have hmul : a * v.1 i = 1 := by
      have := congrFun ha i
      simpa [Pi.smul_apply, hai] using this
    intro hv0
    rw [hv0, mul_zero] at hmul
    exact one_ne_zero hmul.symm
  · intro hi
    refine ⟨chartFunAux i v, ?_⟩
    rw [chartInv_apply]
    refine (cpMk_eq_iff n _ v).mpr ⟨(v.1 i)⁻¹, ?_⟩
    change (v.1 i)⁻¹ • (v : CPV n) =
      Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) (chartFunAux i v)
    rw [insertNth_chartFunAux i v hi]

/-- The chart at `i` covers `ℂPⁿ`. -/
theorem exists_mem_chartSet {n : ℕ} (p : CP n) : ∃ i : Fin (n + 1), p ∈ chartSet i := by
  obtain ⟨v, rfl⟩ := cpMk_surjective n p
  obtain ⟨i, hi⟩ : ∃ i, v.1 i ≠ 0 := by
    by_contra h
    push Not at h
    exact v.2 (funext fun i => h i)
  exact ⟨i, (mem_chartSet_iff i v).mpr hi⟩

/-- The chart domain is the image of `{v | v i ≠ 0}` under the quotient map. -/
theorem chartSet_eq_image {n : ℕ} (i : Fin (n + 1)) :
    chartSet i = cpMk n '' {v : {v : CPV n // v ≠ 0} | v.1 i ≠ 0} := by
  ext p
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨⟨Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w, insertNth_one_ne_zero i w⟩, ?_, rfl⟩
    show (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) i ≠ 0
    rw [Fin.insertNth_apply_same]
    exact one_ne_zero
  · rintro ⟨v, hv, rfl⟩
    exact (mem_chartSet_iff i v).mpr hv

end

end Work.Projective
