import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.mem_hullOf

namespace Work.PL.Generic

variable {n : ℕ} {ι : Type*} [DecidableEq ι]

/-! ### Free/frozen decomposition of a barycentric sum -/

/-- Split a barycentric sum into its free part and its frozen part. -/
theorem sum_free_add_sum_frozen (fz : Finset ι) (f : ι → ℝ) (y : ι → PL.E n) (s : Finset ι) :
    (∑ v ∈ s, f v • y v)
      = (∑ v ∈ s, (if v ∈ fz then 0 else f v) • y v)
        + (∑ v ∈ s, (if v ∈ fz then f v else 0) • y v) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hv : v ∈ fz <;> simp [hv]

/-- Same, for the total mass. -/
theorem sum_free_add_sum_frozen_mass (fz : Finset ι) (f : ι → ℝ) (s : Finset ι) :
    (∑ v ∈ s, f v)
      = (∑ v ∈ s, (if v ∈ fz then 0 else f v))
        + (∑ v ∈ s, (if v ∈ fz then f v else 0)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hv : v ∈ fz <;> simp [hv]

/-- The frozen part of a sum is a sum over the frozen indices. -/
theorem sum_ite_frozen_eq_inter (fz : Finset ι) (f : ι → ℝ) (y : ι → PL.E n) (s : Finset ι) :
    (∑ v ∈ s, (if v ∈ fz then f v else 0) • y v) = ∑ v ∈ s ∩ fz, f v • y v := by
  rw [show (∑ v ∈ s ∩ fz, f v • y v)
        = ∑ v ∈ s ∩ fz, (if v ∈ fz then f v else 0) • y v from
      Finset.sum_congr rfl (fun v hv => by
        rw [Finset.mem_inter] at hv; rw [ite_eq_left hv.2])]
  exact (Finset.sum_subset (Finset.inter_subset_left : s ∩ fz ⊆ s)
    (fun v hvs hvn => by
      have hnf : v ∉ fz := fun h => hvn (Finset.mem_inter.mpr ⟨hvs, h⟩)
      simp [hnf])).symm

/-- Same as `sum_ite_frozen_eq_inter`, for the total mass. -/
theorem sum_ite_frozen_eq_inter_mass (fz : Finset ι) (f : ι → ℝ) (s : Finset ι) :
    (∑ v ∈ s, (if v ∈ fz then f v else 0)) = ∑ v ∈ s ∩ fz, f v := by
  rw [show (∑ v ∈ s ∩ fz, f v)
        = ∑ v ∈ s ∩ fz, (if v ∈ fz then f v else 0) from
      Finset.sum_congr rfl (fun v hv => by
        rw [Finset.mem_inter] at hv; rw [ite_eq_left hv.2])]
  exact (Finset.sum_subset (Finset.inter_subset_left : s ∩ fz ⊆ s)
    (fun v hvs hvn => by
      have hnf : v ∉ fz := fun h => hvn (Finset.mem_inter.mpr ⟨hvs, h⟩)
      simp [hnf])).symm

/-- The free parts of two barycentric representations agree when the coefficients agree off `fz`. -/
theorem free_part_eq (fz : Finset ι) (y : ι → PL.E n) {σ₁ σ₂ : Finset ι} {a b : ι → ℝ}
    (hfree : ∀ v, v ∉ fz → (if v ∈ σ₁ then a v else 0) = (if v ∈ σ₂ then b v else 0)) :
    (∑ v ∈ σ₁, (if v ∈ fz then 0 else a v) • y v)
      = ∑ v ∈ σ₂, (if v ∈ fz then 0 else b v) • y v := by
  set U := σ₁ ∪ σ₂ with hU
  have key : ∀ v, (if v ∈ fz then (0:ℝ) else (if v ∈ σ₁ then a v else 0)) • y v
      = (if v ∈ fz then (0:ℝ) else (if v ∈ σ₂ then b v else 0)) • y v := by
    intro v
    by_cases hv : v ∈ fz
    · simp [hv]
    · simp only [hv, ite_false]
      rw [hfree v hv]
  have e1 : (∑ v ∈ σ₁, (if v ∈ fz then 0 else a v) • y v)
      = ∑ v ∈ U, (if v ∈ fz then (0:ℝ) else (if v ∈ σ₁ then a v else 0)) • y v := by
    rw [← Finset.sum_subset (Finset.subset_union_left : σ₁ ⊆ U)]
    · apply Finset.sum_congr rfl
      intro v hv
      rw [ite_eq_left hv]
    · intro v hvU hvσ
      simp [hvσ]
  have e2 : (∑ v ∈ σ₂, (if v ∈ fz then 0 else b v) • y v)
      = ∑ v ∈ U, (if v ∈ fz then (0:ℝ) else (if v ∈ σ₂ then b v else 0)) • y v := by
    rw [← Finset.sum_subset (Finset.subset_union_right : σ₂ ⊆ U)]
    · apply Finset.sum_congr rfl
      intro v hv
      rw [ite_eq_left hv]
    · intro v hvU hvσ
      simp [hvσ]
  rw [e1, e2]
  exact Finset.sum_congr rfl (fun v _ => key v)

/-- The free masses of two barycentric representations agree when the coefficients agree off `fz`. -/
theorem free_mass_eq (fz : Finset ι) {σ₁ σ₂ : Finset ι} {a b : ι → ℝ}
    (hfree : ∀ v, v ∉ fz → (if v ∈ σ₁ then a v else 0) = (if v ∈ σ₂ then b v else 0)) :
    (∑ v ∈ σ₁, (if v ∈ fz then 0 else a v))
      = ∑ v ∈ σ₂, (if v ∈ fz then 0 else b v) := by
  set U := σ₁ ∪ σ₂ with hU
  have key : ∀ v, (if v ∈ fz then (0:ℝ) else (if v ∈ σ₁ then a v else 0))
      = (if v ∈ fz then (0:ℝ) else (if v ∈ σ₂ then b v else 0)) := by
    intro v
    by_cases hv : v ∈ fz
    · simp [hv]
    · simp only [hv, ite_false]
      rw [hfree v hv]
  have e1 : (∑ v ∈ σ₁, (if v ∈ fz then 0 else a v))
      = ∑ v ∈ U, (if v ∈ fz then (0:ℝ) else (if v ∈ σ₁ then a v else 0)) := by
    rw [← Finset.sum_subset (Finset.subset_union_left : σ₁ ⊆ U)]
    · apply Finset.sum_congr rfl
      intro v hv
      rw [ite_eq_left hv]
    · intro v hvU hvσ
      simp [hvσ]
  have e2 : (∑ v ∈ σ₂, (if v ∈ fz then 0 else b v))
      = ∑ v ∈ U, (if v ∈ fz then (0:ℝ) else (if v ∈ σ₂ then b v else 0)) := by
    rw [← Finset.sum_subset (Finset.subset_union_right : σ₂ ⊆ U)]
    · apply Finset.sum_congr rfl
      intro v hv
      rw [ite_eq_left hv]
    · intro v hvU hvσ
      simp [hvσ]
  rw [e1, e2]
  exact Finset.sum_congr rfl (fun v _ => key v)

/-! ### Main lemma -/

/-- Case B of the pointwise argument for `Work.PL.Generic.gp_pairs`: if the two barycentric
representations of a point agree on all *free* coefficients (viewing coefficients off the support as
`0`), then the point lies in the shared hull or in the intersection of the two frozen faces.
Proof: the free parts of the two sums are equal, so the frozen parts are equal too, with equal total
mass `1 - m`; if `m < 1` divide by it to get a point `z` of `hullOf y (σ₁ ∩ fz) ∩ hullOf y (σ₂ ∩ fz)`
and `x = m·w + (1-m)·z` is a convex combination of points of `hullOf y (σ₁ ∩ σ₂)` (using `hcol` to
place `z` there) — use `Work.PL.Generic.mem_hullOf` for the membership statements. -/
theorem mem_union_of_sum_smul_eq_of_frozen {n : ℕ} {ι : Type*} [DecidableEq ι]
    (fz : Finset ι) (y : ι → PL.E n) {σ₁ σ₂ : Finset ι} {a b : ι → ℝ}
    (ha0 : ∀ v ∈ σ₁, 0 ≤ a v) (has : ∑ v ∈ σ₁, a v = 1)
    (hb0 : ∀ v ∈ σ₂, 0 ≤ b v) (hbs : ∑ v ∈ σ₂, b v = 1)
    (hfree : ∀ v, v ∉ fz → (if v ∈ σ₁ then a v else 0) = (if v ∈ σ₂ then b v else 0))
    (hcol : ∀ z ∈ Work.PL.Generic.hullOf y (σ₁ ∩ fz) ∩ Work.PL.Generic.hullOf y (σ₂ ∩ fz),
      (∃ v ∈ σ₁ ∩ σ₂, v ∉ fz) → z ∈ Work.PL.Generic.hullOf y (σ₁ ∩ σ₂ ∩ fz))
    (heq : ∑ v ∈ σ₁, a v • y v = ∑ v ∈ σ₂, b v • y v) :
    (∑ v ∈ σ₁, a v • y v) ∈ Work.PL.Generic.hullOf y (σ₁ ∩ σ₂) ∪
      (Work.PL.Generic.hullOf y (σ₁ ∩ fz) ∩ Work.PL.Generic.hullOf y (σ₂ ∩ fz)) := by
  classical
  -- Abbreviations for the free/frozen parts and masses of the two representations.
  set W₁ : PL.E n := ∑ v ∈ σ₁, (if v ∈ fz then 0 else a v) • y v with hW₁
  set F₁ : PL.E n := ∑ v ∈ σ₁, (if v ∈ fz then a v else 0) • y v with hF₁
  set W₂ : PL.E n := ∑ v ∈ σ₂, (if v ∈ fz then 0 else b v) • y v with hW₂
  set F₂ : PL.E n := ∑ v ∈ σ₂, (if v ∈ fz then b v else 0) • y v with hF₂
  set m₁ : ℝ := ∑ v ∈ σ₁, (if v ∈ fz then 0 else a v) with hm₁
  set M₁ : ℝ := ∑ v ∈ σ₁, (if v ∈ fz then a v else 0) with hM₁
  set m₂ : ℝ := ∑ v ∈ σ₂, (if v ∈ fz then 0 else b v) with hm₂
  set M₂ : ℝ := ∑ v ∈ σ₂, (if v ∈ fz then b v else 0) with hM₂
  -- Decompositions of the two total sums.
  have hx1 : (∑ v ∈ σ₁, a v • y v) = W₁ + F₁ := by
    rw [hW₁, hF₁]; exact sum_free_add_sum_frozen fz a y σ₁
  have hx2 : (∑ v ∈ σ₂, b v • y v) = W₂ + F₂ := by
    rw [hW₂, hF₂]; exact sum_free_add_sum_frozen fz b y σ₂
  have hmass1 : m₁ + M₁ = 1 := by
    rw [hm₁, hM₁, ← sum_free_add_sum_frozen_mass fz a σ₁]; exact has
  have hmass2 : m₂ + M₂ = 1 := by
    rw [hm₂, hM₂, ← sum_free_add_sum_frozen_mass fz b σ₂]; exact hbs
  -- Purely frozen sums as sums over the frozen indices.
  have hF1int : F₁ = ∑ v ∈ σ₁ ∩ fz, a v • y v := by
    rw [hF₁]; exact sum_ite_frozen_eq_inter fz a y σ₁
  have hF2int : F₂ = ∑ v ∈ σ₂ ∩ fz, b v • y v := by
    rw [hF₂]; exact sum_ite_frozen_eq_inter fz b y σ₂
  have hM1int : M₁ = ∑ v ∈ σ₁ ∩ fz, a v := by
    rw [hM₁]; exact sum_ite_frozen_eq_inter_mass fz a σ₁
  have hM2int : M₂ = ∑ v ∈ σ₂ ∩ fz, b v := by
    rw [hM₂]; exact sum_ite_frozen_eq_inter_mass fz b σ₂
  -- The free parts and masses agree.
  have hW12 : W₁ = W₂ := by rw [hW₁, hW₂]; exact free_part_eq fz y hfree
  have hm12 : m₁ = m₂ := by rw [hm₁, hm₂]; exact free_mass_eq fz hfree
  -- Hence the frozen parts (both vector and mass) agree.
  have hF12 : F₁ = F₂ := by
    have h : W₁ + F₁ = W₂ + F₂ := by rw [← hx1, ← hx2]; exact heq
    rw [hW12] at h
    exact add_left_cancel h
  have hM12 : M₂ = M₁ := by
    have h2' : m₁ + M₂ = 1 := by rw [hm12]; exact hmass2
    have : m₁ + M₂ = m₁ + M₁ := by rw [h2', hmass1]
    exact add_left_cancel this
  -- Vanishing of free coefficients off the other support.
  have hvanish1 : ∀ v, v ∈ σ₁ → v ∉ σ₂ → v ∉ fz → a v = 0 := by
    intro v hv1 hv2 hvf
    have h := hfree v hvf
    rw [ite_eq_left hv1, ite_eq_right hv2] at h
    exact h
  -- Nonnegativity of the restricted coefficients.
  have hc1nn : ∀ v ∈ σ₁ ∩ σ₂, 0 ≤ (if v ∈ fz then 0 else a v) := by
    intro v hv; rw [Finset.mem_inter] at hv
    by_cases hvf : v ∈ fz
    · simp [hvf]
    · rw [ite_eq_right hvf]; exact ha0 v hv.1
  have hfznn1 : ∀ v ∈ σ₁ ∩ fz, 0 ≤ a v := by
    intro v hv; rw [Finset.mem_inter] at hv; exact ha0 v hv.1
  have hfznn2 : ∀ v ∈ σ₂ ∩ fz, 0 ≤ b v := by
    intro v hv; rw [Finset.mem_inter] at hv; exact hb0 v hv.1
  have hM1nn : 0 ≤ M₁ := by rw [hM1int]; exact Finset.sum_nonneg hfznn1
  -- The first free mass/part, written over `σ₁ ∩ σ₂`.
  have hm1S : m₁ = ∑ v ∈ σ₁ ∩ σ₂, (if v ∈ fz then 0 else a v) := by
    rw [hm₁]
    exact (Finset.sum_subset (Finset.inter_subset_left : σ₁ ∩ σ₂ ⊆ σ₁)
      (fun v hvs hvn => by
        have hv2 : v ∉ σ₂ := fun h => hvn (Finset.mem_inter.mpr ⟨hvs, h⟩)
        by_cases hvf : v ∈ fz
        · simp [hvf]
        · rw [ite_eq_right hvf, hvanish1 v hvs hv2 hvf])).symm
  have hW1S : W₁ = ∑ v ∈ σ₁ ∩ σ₂, (if v ∈ fz then 0 else a v) • y v := by
    rw [hW₁]
    exact (Finset.sum_subset (Finset.inter_subset_left : σ₁ ∩ σ₂ ⊆ σ₁)
      (fun v hvs hvn => by
        have hv2 : v ∉ σ₂ := fun h => hvn (Finset.mem_inter.mpr ⟨hvs, h⟩)
        by_cases hvf : v ∈ fz
        · simp [hvf]
        · rw [ite_eq_right hvf, hvanish1 v hvs hv2 hvf, zero_smul])).symm
  have hm1nn : 0 ≤ m₁ := by rw [hm1S]; exact Finset.sum_nonneg hc1nn
  -- Case 1: the free mass vanishes  ⇒  `x` lies in the intersection of the frozen faces.
  have hmem1 : m₁ = 0 →
      (∑ v ∈ σ₁, a v • y v) ∈
        hullOf y (σ₁ ∩ fz) ∩ hullOf y (σ₂ ∩ fz) := by
    intro hm0
    have hc1zero : ∀ v ∈ σ₁ ∩ σ₂, (if v ∈ fz then 0 else a v) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hc1nn).mp (by rw [← hm1S]; exact hm0)
    have hW1zero : W₁ = 0 := by
      rw [hW1S]
      exact Finset.sum_eq_zero (fun v hv => by rw [hc1zero v hv, zero_smul])
    have hxeq : (∑ v ∈ σ₁, a v • y v) = F₁ := by rw [hx1, hW1zero, zero_add]
    have hM1one : M₁ = 1 := by have h := hmass1; rw [hm0, zero_add] at h; exact h
    have hM2one : M₂ = 1 := by
      have h := hmass2; rw [← hm12, hm0, zero_add] at h; exact h
    refine ⟨?_, ?_⟩
    · rw [mem_hullOf]
      exact ⟨a, hfznn1, by rw [← hM1int, hM1one], by rw [← hF1int]; exact hxeq.symm⟩
    · rw [mem_hullOf]
      exact ⟨b, hfznn2, by rw [← hM2int, hM2one], by rw [← hF2int, ← hF12]; exact hxeq.symm⟩
  -- Case 2: the free mass is positive  ⇒  `x` lies in the shared hull.
  have hmem2 : m₁ ≠ 0 →
      (∑ v ∈ σ₁, a v • y v) ∈ hullOf y (σ₁ ∩ σ₂) := by
    intro hm0
    have hm1pos : 0 < m₁ := lt_of_le_of_ne hm1nn (Ne.symm hm0)
    set w : PL.E n := m₁⁻¹ • W₁ with hw
    have hmw : m₁ • w = W₁ := by
      rw [hw]; exact smul_inv_smul₀ (ne_of_gt hm1pos) W₁
    -- `w` is in the shared hull.
    have hwmem : w ∈ hullOf y (σ₁ ∩ σ₂) := by
      rw [mem_hullOf]
      refine ⟨fun v => m₁⁻¹ * (if v ∈ fz then 0 else a v), ?_, ?_, ?_⟩
      · intro v hv
        exact mul_nonneg (inv_nonneg.mpr (le_of_lt hm1pos)) (hc1nn v hv)
      · rw [← Finset.mul_sum, ← hm1S, inv_mul_cancel₀ (ne_of_gt hm1pos)]
      · rw [hw, hW1S, Finset.smul_sum]
        exact Finset.sum_congr rfl (fun v _ => by rw [mul_smul])
    -- There is a free index in `σ₁ ∩ σ₂`.
    have hfreeex : ∃ v ∈ σ₁ ∩ σ₂, v ∉ fz := by
      have hpos : 0 < ∑ v ∈ σ₁ ∩ σ₂, (if v ∈ fz then 0 else a v) := by
        rw [← hm1S]; exact hm1pos
      obtain ⟨v, hv, hvpos⟩ := (Finset.sum_pos_iff_of_nonneg hc1nn).mp hpos
      refine ⟨v, hv, ?_⟩
      intro hvz
      rw [ite_eq_left hvz] at hvpos
      exact lt_irrefl 0 hvpos
    by_cases hM0 : M₁ = 0
    · -- The frozen mass vanishes: `F₁ = 0` and `m₁ = 1`, so `x = w`.
      have hm1one : m₁ = 1 := by have h := hmass1; rw [hM0, add_zero] at h; exact h
      have hF1zero : F₁ = 0 := by
        rw [hF1int]
        exact Finset.sum_eq_zero (fun v hv =>
          by rw [(Finset.sum_eq_zero_iff_of_nonneg hfznn1).mp (by rw [← hM1int]; exact hM0) v hv,
                 zero_smul])
      have hW1w : W₁ = w := by rw [← hmw, hm1one, one_smul]
      have hxw : (∑ v ∈ σ₁, a v • y v) = w := by rw [hx1, hF1zero, add_zero, hW1w]
      rw [hxw]; exact hwmem
    · -- The frozen mass is positive: combine `w` with the normalised frozen point.
      have hM1pos : 0 < M₁ := lt_of_le_of_ne hM1nn (Ne.symm hM0)
      have hzB1 : M₁⁻¹ • F₁ ∈ hullOf y (σ₁ ∩ fz) := by
        rw [mem_hullOf]
        refine ⟨fun v => M₁⁻¹ * a v, ?_, ?_, ?_⟩
        · intro v hv
          exact mul_nonneg (inv_nonneg.mpr (le_of_lt hM1pos)) (hfznn1 v hv)
        · rw [← Finset.mul_sum, ← hM1int, inv_mul_cancel₀ (ne_of_gt hM1pos)]
        · rw [hF1int, Finset.smul_sum]
          exact Finset.sum_congr rfl (fun v _ => by rw [mul_smul])
      have hzB2 : M₁⁻¹ • F₁ ∈ hullOf y (σ₂ ∩ fz) := by
        rw [mem_hullOf]
        refine ⟨fun v => M₁⁻¹ * b v, ?_, ?_, ?_⟩
        · intro v hv
          exact mul_nonneg (inv_nonneg.mpr (le_of_lt hM1pos)) (hfznn2 v hv)
        · rw [← Finset.mul_sum, ← hM2int, hM12, inv_mul_cancel₀ (ne_of_gt hM1pos)]
        · rw [hF12, hF2int, Finset.smul_sum]
          exact Finset.sum_congr rfl (fun v _ => by rw [mul_smul])
      have hzmem : M₁⁻¹ • F₁ ∈ hullOf y (σ₁ ∩ σ₂) :=
        hullOf_mono (Finset.inter_subset_left :
            (σ₁ ∩ σ₂) ∩ fz ⊆ σ₁ ∩ σ₂)
          (hcol (M₁⁻¹ • F₁) ⟨hzB1, hzB2⟩ hfreeex)
      have hxsum : (∑ v ∈ σ₁, a v • y v) = m₁ • w + M₁ • (M₁⁻¹ • F₁) := by
        rw [hx1, ← hmw, smul_inv_smul₀ (ne_of_gt hM1pos)]
      rw [hxsum]
      exact (convex_iff_add_mem.mp (convex_hullOf y (σ₁ ∩ σ₂)))
        hwmem hzmem (le_of_lt hm1pos) hM1nn hmass1
  rw [Set.mem_union]
  by_cases hm0 : m₁ = 0
  · exact Or.inr (hmem1 hm0)
  · exact Or.inl (hmem2 hm0)

end Work.PL.Generic
