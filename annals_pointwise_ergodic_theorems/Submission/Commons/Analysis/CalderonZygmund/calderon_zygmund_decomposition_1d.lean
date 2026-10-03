import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Measure.ae_tendsto_interval_average

namespace Commons.Analysis.CalderonZygmund

open MeasureTheory Set
open scoped ENNReal Interval

/-! ## Dyadic intervals on `ℝ`

We build the standard dyadic cells `[m·2^N/2^k, (m+1)·2^N/2^k)`, indexed by `(k,m) ∈ ℕ × ℤ`.
They are laminar: two cells are disjoint or one is contained in the other, and the cell at
level `k'` containing a cell at level `k ≥ k'` is obtained by (integer) division of the index. -/

/-- Length of the dyadic cell at level `k` (with global scale `2^N`). -/
noncomputable def dlen (N : ℕ) (k : ℕ) : ℝ := (2:ℝ)^N / (2:ℝ)^k

lemma dlen_pos (N k : ℕ) : 0 < dlen N k := by unfold dlen; positivity

lemma dlen_mul_pow (N k k' : ℕ) (h : k ≤ k') :
    dlen N k = (2:ℝ)^(k'-k) * dlen N k' := by
  unfold dlen
  have h2 : (2:ℝ)^k' = (2:ℝ)^k * 2^(k'-k) := by rw [← pow_add]; congr 1; omega
  rw [h2]; field_simp

/-- Left endpoint of the dyadic cell with index `(k,m)`. -/
noncomputable def dlo (N k : ℕ) (m : ℤ) : ℝ := (m:ℝ) * dlen N k
/-- Right endpoint of the dyadic cell with index `(k,m)`. -/
noncomputable def dhi (N k : ℕ) (m : ℤ) : ℝ := ((m:ℝ)+1) * dlen N k

lemma dlo_lt_dhi (N k : ℕ) (m : ℤ) : dlo N k m < dhi N k m := by
  unfold dlo dhi; have := dlen_pos N k; nlinarith

/-- The dyadic cell with index `(k,m)`, as a left-closed right-open interval. -/
noncomputable def dIv (N k : ℕ) (m : ℤ) : Set ℝ := Set.Ico (dlo N k m) (dhi N k m)

lemma dIv_mem_iff (N k : ℕ) (m : ℤ) (x : ℝ) :
    x ∈ dIv N k m ↔ ⌊x / dlen N k⌋ = m := by
  have hL := dlen_pos N k
  rw [dIv, Set.mem_Ico, dlo, dhi, Int.floor_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [le_div_iff₀ hL]; exact_mod_cast h1,
           by rw [div_lt_iff₀ hL]; push_cast; linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [le_div_iff₀ hL] at h1; exact_mod_cast h1,
           by rw [div_lt_iff₀ hL] at h2; push_cast at h2; linarith⟩

/-- **Laminarity**: two intersecting dyadic cells are nested, the finer one inside the coarser. -/
lemma dIv_subset_of_inter (N k k' : ℕ) (m m' : ℤ) (hkk : k ≤ k')
    (hne : (dIv N k m ∩ dIv N k' m').Nonempty) : dIv N k' m' ⊆ dIv N k m := by
  obtain ⟨x, hx1, hx2⟩ := hne
  rw [dIv_mem_iff] at hx1 hx2
  have hd := dlen_mul_pow N k k' hkk
  have hkey : m = m' / (2:ℤ)^(k'-k) := by
    have hq : x / dlen N k = (x / dlen N k') / (2:ℝ)^(k'-k) := by rw [hd]; field_simp
    calc m = ⌊x / dlen N k⌋ := hx1.symm
      _ = ⌊(x / dlen N k') / (2:ℝ)^(k'-k)⌋ := by rw [hq]
      _ = ⌊x / dlen N k'⌋ / (2:ℤ)^(k'-k) := by
          have h := Int.floor_div_natCast (x / dlen N k') (2^(k'-k))
          push_cast at h; exact h
      _ = m' / (2:ℤ)^(k'-k) := by rw [hx2]
  have e1 : (2:ℤ)^(k'-k) * m ≤ m' := by
    rw [hkey]
    have := Int.ediv_mul_le m' (by positivity : (2:ℤ)^(k'-k) ≠ 0); linarith
  have e2' : m' + 1 ≤ (2:ℤ)^(k'-k) * (m+1) := by
    rw [hkey]
    have h := Int.mul_ediv_add_emod m' ((2:ℤ)^(k'-k))
    have hlt := Int.emod_lt_of_pos m' (by positivity : (0:ℤ) < (2:ℤ)^(k'-k))
    have hnn := Int.emod_nonneg m' (by positivity : (2:ℤ)^(k'-k) ≠ 0)
    nlinarith [h, hlt, hnn]
  intro y hy
  rw [dIv_mem_iff] at hy ⊢
  have hq : y / dlen N k = (y / dlen N k') / (2:ℝ)^(k'-k) := by rw [hd]; field_simp
  rw [hq]
  have h := Int.floor_div_natCast (y / dlen N k') (2^(k'-k))
  push_cast at h
  rw [h, hy, hkey]

/-- The cell at level `k` is contained in its ancestor at any coarser level `k' ≤ k`. -/
lemma dIv_subset_ancestor (N k k' : ℕ) (m : ℤ) (h : k' ≤ k) :
    dIv N k m ⊆ dIv N k' (m / (2:ℤ)^(k-k')) := by
  intro y hy
  rw [dIv_mem_iff] at hy ⊢
  have hd := dlen_mul_pow N k' k h
  have hq : y / dlen N k' = (y / dlen N k) / (2:ℝ)^(k-k') := by rw [hd]; field_simp
  rw [hq]
  have hh := Int.floor_div_natCast (y / dlen N k) (2^(k-k'))
  push_cast at hh
  rw [hh, hy]

lemma dlo_le_ancestor (N k k' : ℕ) (m : ℤ) (h : k' ≤ k) :
    dlo N k' (m / (2:ℤ)^(k-k')) ≤ dlo N k m := by
  unfold dlo
  have hd := dlen_mul_pow N k' k h
  rw [hd]
  have h1 : (2:ℤ)^(k-k') * (m / (2:ℤ)^(k-k')) ≤ m := by
    have := Int.ediv_mul_le m (by positivity : (2:ℤ)^(k-k') ≠ 0); linarith
  have h1' : (2:ℝ)^(k-k') * ((m / (2:ℤ)^(k-k') : ℤ) : ℝ) ≤ (m:ℝ) := by exact_mod_cast h1
  have hpos := dlen_pos N k
  nlinarith

lemma dhi_le_ancestor (N k k' : ℕ) (m : ℤ) (h : k' ≤ k) :
    dhi N k m ≤ dhi N k' (m / (2:ℤ)^(k-k')) := by
  unfold dhi
  have hd := dlen_mul_pow N k' k h
  rw [hd]
  have h2 : m + 1 ≤ (2:ℤ)^(k-k') * (m / (2:ℤ)^(k-k') + 1) := by
    have h := Int.mul_ediv_add_emod m ((2:ℤ)^(k-k'))
    have hlt := Int.emod_lt_of_pos m (by positivity : (0:ℤ) < (2:ℤ)^(k-k'))
    have hnn := Int.emod_nonneg m (by positivity : (2:ℤ)^(k-k') ≠ 0)
    nlinarith [h, hlt, hnn]
  have h2' : (m:ℝ) + 1 ≤ (2:ℝ)^(k-k') * (((m / (2:ℤ)^(k-k') : ℤ)) + 1 : ℝ) := by
    push_cast; exact_mod_cast h2
  have hpos := dlen_pos N k
  nlinarith

/-- Integral of `|f|` over the dyadic cell `(k,m)`. -/
noncomputable def dS (f : ℝ → ℝ) (N k : ℕ) (m : ℤ) : ℝ :=
  ∫ x in (dlo N k m)..(dhi N k m), |f x|

/-- The cell `(k,m)` is *selected* if its average of `|f|` exceeds `α`. -/
def dSel (f : ℝ → ℝ) (α : ℝ) (N k : ℕ) (m : ℤ) : Prop := α * dlen N k < dS f N k m

/-- The cell `(k,m)` is *maximal* if it is selected and no selected cell at a coarser level
contains it. -/
def dMax (f : ℝ → ℝ) (α : ℝ) (N k : ℕ) (m : ℤ) : Prop :=
  dSel f α N k m ∧ ∀ k' m', k' < k → dSel f α N k' m' → dIv N k m ⊆ dIv N k' m' → False

lemma dS_nonneg (f : ℝ → ℝ) (N k : ℕ) (m : ℤ) : 0 ≤ dS f N k m :=
  intervalIntegral.integral_nonneg (le_of_lt (dlo_lt_dhi N k m)) (fun x _ => abs_nonneg (f x))

lemma dS_mono_ancestor (f : ℝ → ℝ) (hfint : Integrable (fun x => |f x|))
    (N k k' : ℕ) (m : ℤ) (h : k' ≤ k) :
    dS f N k m ≤ dS f N k' (m / (2:ℤ)^(k-k')) := by
  unfold dS
  exact intervalIntegral.integral_mono_interval (dlo_le_ancestor N k k' m h)
    (le_of_lt (dlo_lt_dhi N k m)) (dhi_le_ancestor N k k' m h)
    (Filter.Eventually.of_forall (fun x => abs_nonneg (f x)))
    hfint.intervalIntegrable

/-- `dS` over any cell is bounded by the total integral of `|f|`. -/
lemma dS_le_M (f : ℝ → ℝ) (hfint : Integrable (fun x => |f x|)) (N k : ℕ) (m : ℤ) :
    dS f N k m ≤ ∫ x, |f x| := by
  unfold dS
  rw [intervalIntegral.integral_of_le (le_of_lt (dlo_lt_dhi N k m))]
  exact setIntegral_le_integral hfint (Filter.Eventually.of_forall (fun x => abs_nonneg (f x)))

/-- Two distinct maximal cells are disjoint. -/
lemma dMax_disjoint (f : ℝ → ℝ) (α : ℝ) (N : ℕ) {k₁ m₁ k₂ m₂}
    (h₁ : dMax f α N k₁ m₁) (h₂ : dMax f α N k₂ m₂) (hne : (k₁,m₁) ≠ (k₂,m₂)) :
    Disjoint (dIv N k₁ m₁) (dIv N k₂ m₂) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx1, hx2⟩
  rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · have hs := dIv_subset_of_inter N k₁ k₂ m₁ m₂ (le_of_lt hlt) ⟨x, hx1, hx2⟩
    exact h₂.2 k₁ m₁ hlt h₁.1 hs
  · subst heq
    rw [dIv_mem_iff] at hx1 hx2
    exact hne (by rw [← hx1, hx2])
  · have hs := dIv_subset_of_inter N k₂ k₁ m₂ m₁ (le_of_lt hgt) ⟨x, hx2, hx1⟩
    exact h₁.2 k₂ m₂ hgt h₂.1 hs

/-- If a maximal cell has level `≥ 1`, its parent cell is not selected. -/
lemma dMax_parent_not_sel (f : ℝ → ℝ) (α : ℝ) (N k : ℕ) (m : ℤ)
    (hk : 1 ≤ k) (h : dMax f α N k m) : ¬ dSel f α N (k-1) (m / 2) := by
  have hkk : k - (k-1) = 1 := by omega
  intro hsel
  exact h.2 (k-1) (m/2) (by omega) (by simpa [hkk] using hsel)
    (by simpa [hkk] using dIv_subset_ancestor N k (k-1) m (by omega))


/-- For every `δ > 0` there is a dyadic level whose cell length is `< δ`. -/
lemma exists_dlen_lt (N : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ k, dlen N k < δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((2:ℝ)^N / δ)
  refine ⟨m, ?_⟩
  have hm2 : (2:ℝ)^N < δ * (2:ℝ)^m := by
    rw [div_lt_iff₀ hδ] at hm
    have h2 : (m:ℝ) ≤ (2:ℝ)^m := by
      exact_mod_cast (le_of_lt (Nat.lt_two_pow_self (n := m)))
    nlinarith [hm, h2, hδ]
  rw [dlen, div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^m)]
  linarith

/-- Given a selected cell through a point, there is a maximal cell through that point. -/
lemma exists_maximal_cell (f : ℝ → ℝ) (α : ℝ) (N : ℕ) {k : ℕ} {m : ℤ} {x : ℝ}
    (hx : x ∈ dIv N k m) (hsel : dSel f α N k m) :
    ∃ k' m', dMax f α N k' m' ∧ x ∈ dIv N k' m' := by
  classical
  let p : ℕ → Prop := fun k' => k' ≤ k ∧ dSel f α N k' (m / (2:ℤ)^(k-k'))
  have hp : ∃ k', p k' := ⟨k, le_rfl, by simpa using hsel⟩
  refine ⟨Nat.find hp, m / (2:ℤ)^(k - Nat.find hp), ?_, ?_⟩
  · obtain ⟨hle, hsd⟩ := Nat.find_spec hp
    refine ⟨hsd, ?_⟩
    intro k'' m'' hlt hsel'' hsub
    have hk''k : k'' ≤ k := le_trans (le_of_lt hlt) hle
    have hx'' : x ∈ dIv N k'' m'' := hsub (dIv_subset_ancestor N k (Nat.find hp) m hle hx)
    have hm'' : m'' = m / (2:ℤ)^(k-k'') := by
      rw [dIv_mem_iff] at hx'' hx
      rw [← hx'']
      have hd := dlen_mul_pow N k'' k hk''k
      have hq : x / dlen N k'' = (x / dlen N k) / (2:ℝ)^(k-k'') := by rw [hd]; field_simp
      rw [hq]
      have hh := Int.floor_div_natCast (x / dlen N k) (2^(k-k''))
      push_cast at hh
      rw [hh, hx]
    have hp'' : p k'' := ⟨hk''k, by rw [← hm'']; exact hsel''⟩
    exact (not_le.mpr hlt) (Nat.find_min' hp hp'')
  · have hle := (Nat.find_spec hp).1
    exact dIv_subset_ancestor N k (Nat.find hp) m hle hx

theorem calderon_zygmund_decomposition_1d
    (f : ℝ → ℝ) (hf : MeasureTheory.Integrable f) (α : ℝ) (hα : 0 < α) :
    ∃ (A c : ℕ → ℝ) (g : ℝ → ℝ) (b : ℕ → ℝ → ℝ),
      (∀ j, A j ≤ c j) ∧
      (∀ j k, j ≠ k → Disjoint (Set.Ioo (A j) (c j)) (Set.Ioo (A k) (c k))) ∧
      (∀ j, α * (c j - A j) ≤ ∫ x in (A j)..(c j), |f x|) ∧
      (∀ j, ∫ x in (A j)..(c j), |f x| ≤ 2 * α * (c j - A j)) ∧
      (∀ j, ∀ x, b j x = if x ∈ Set.Ioo (A j) (c j)
          then f x - (c j - A j)⁻¹ * ∫ t in (A j)..(c j), f t else 0) ∧
      (∀ x, x ∉ ⋃ j, Set.Ioo (A j) (c j) → g x = f x) ∧
      (∀ j, ∀ x ∈ Set.Ioo (A j) (c j),
          g x = (c j - A j)⁻¹ * ∫ t in (A j)..(c j), f t) ∧
      (∀ᵐ x ∂MeasureTheory.volume, x ∉ ⋃ j, Set.Ioo (A j) (c j) → |f x| ≤ α) ∧
      (∀ᵐ x ∂MeasureTheory.volume, |g x| ≤ 2 * α) ∧
      (MeasureTheory.volume (⋃ j, Set.Ioo (A j) (c j))
          ≤ ENNReal.ofReal (α⁻¹ * ∫ x, |f x|)) ∧
      (∀ᵐ x ∂MeasureTheory.volume, f x = g x + ∑' j, b j x) := by
  classical
  have hfabs : Integrable (fun x => |f x|) := hf.abs
  have hαne : α ≠ 0 := ne_of_gt hα
  have hαinv : 0 < α⁻¹ := inv_pos.mpr hα
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (∫ x, |f x|) ≤ α * (2:ℝ)^N := by
    have ht : Filter.Tendsto (fun n : ℕ => α * (2:ℝ)^n) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hα (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
    obtain ⟨N, hN⟩ := (ht.eventually_ge_atTop (∫ x, |f x|)).exists
    exact ⟨N, hN⟩
  have hN0 : ∀ m : ℤ, ¬ dSel f α N 0 m := by
    intro m hsel
    have h1 : dS f N 0 m ≤ ∫ x, |f x| := dS_le_M f hfabs N 0 m
    have h2 : α * dlen N 0 = α * (2:ℝ)^N := by simp [dlen]
    rw [dSel, h2] at hsel
    linarith
  let e : ℕ ≃ ℕ × ℤ := (Denumerable.eqv (ℕ × ℤ)).symm
  let A : ℕ → ℝ := fun j => if dMax f α N (e j).1 (e j).2 then dlo N (e j).1 (e j).2 else 0
  let c : ℕ → ℝ := fun j => if dMax f α N (e j).1 (e j).2 then dhi N (e j).1 (e j).2 else 0
  let b : ℕ → ℝ → ℝ := fun j x =>
    if x ∈ Set.Ioo (A j) (c j) then f x - (c j - A j)⁻¹ * ∫ t in (A j)..(c j), f t else 0
  let g : ℝ → ℝ := fun x => f x - ∑' j, b j x
  have h1 : ∀ j, A j ≤ c j := by
    intro j
    by_cases h : dMax f α N (e j).1 (e j).2
    · simp only [A, c, h, if_true]
      exact le_of_lt (dlo_lt_dhi N (e j).1 (e j).2)
    · simp only [A, c, h, if_false]
      exact le_refl 0
  have h2 : ∀ j k, j ≠ k → Disjoint (Set.Ioo (A j) (c j)) (Set.Ioo (A k) (c k)) := by
    intro j k hjk
    by_cases hj : dMax f α N (e j).1 (e j).2
    · by_cases hk : dMax f α N (e k).1 (e k).2
      · have hneq : e j ≠ e k := fun h => hjk (e.injective h)
        have hdisj := dMax_disjoint f α N hj hk hneq
        simp only [A, c, hj, hk, if_true]
        exact hdisj.mono Set.Ioo_subset_Ico_self Set.Ioo_subset_Ico_self
      · simp only [A, c, hj, hk, if_true, if_false, Set.Ioo_self]
        exact Set.disjoint_empty _
    · simp only [A, c, hj, if_false, Set.Ioo_self]
      exact Set.empty_disjoint _
  have h3 : ∀ j, α * (c j - A j) ≤ ∫ x in (A j)..(c j), |f x| := by
    intro j
    by_cases h : dMax f α N (e j).1 (e j).2
    · simp only [A, c, h, if_true]
      have hlen : dhi N (e j).1 (e j).2 - dlo N (e j).1 (e j).2 = dlen N (e j).1 := by
        simp only [dhi, dlo]; ring
      rw [hlen]
      exact le_of_lt h.1
    · simp only [A, c, h, if_false, sub_zero, mul_zero]
      simp [intervalIntegral.integral_same]
  have h4 : ∀ j, ∫ x in (A j)..(c j), |f x| ≤ 2 * α * (c j - A j) := by
    intro j
    by_cases h : dMax f α N (e j).1 (e j).2
    · simp only [A, c, h, if_true]
      have hk1 : 1 ≤ (e j).1 := by
        rcases Nat.eq_zero_or_pos (e j).1 with h0 | hpos
        · exact absurd (h0 ▸ h.1) (hN0 (e j).2)
        · exact hpos
      have hpar : ¬ dSel f α N ((e j).1 - 1) ((e j).2 / 2) :=
        dMax_parent_not_sel f α N (e j).1 (e j).2 hk1 h
      have hmono : dS f N (e j).1 (e j).2 ≤ dS f N ((e j).1 - 1) ((e j).2 / 2) := by
        have hh := dS_mono_ancestor f hfabs N (e j).1 ((e j).1 - 1) (e j).2 (by omega)
        have hkk : (e j).1 - ((e j).1 - 1) = 1 := by omega
        simpa [hkk] using hh
      have hup : dS f N ((e j).1 - 1) ((e j).2 / 2) ≤ α * dlen N ((e j).1 - 1) :=
        not_lt.mp hpar
      have hlen : dlen N ((e j).1 - 1) = 2 * dlen N (e j).1 := by
        have hkk : (e j).1 - ((e j).1 - 1) = 1 := by omega
        simpa [hkk] using dlen_mul_pow N ((e j).1 - 1) ((e j).1) (by omega)
      have hcl : dhi N (e j).1 (e j).2 - dlo N (e j).1 (e j).2 = dlen N (e j).1 := by
        simp only [dhi, dlo]; ring
      rw [hcl]
      change dS f N (e j).1 (e j).2 ≤ 2 * α * dlen N (e j).1
      rw [hlen] at hup
      nlinarith [hmono, hup]
    · simp only [A, c, h, if_false, sub_zero, mul_zero]
      simp [intervalIntegral.integral_same]
  have h5 : ∀ j, ∀ x, b j x = if x ∈ Set.Ioo (A j) (c j)
      then f x - (c j - A j)⁻¹ * ∫ t in (A j)..(c j), f t else 0 := fun j x => rfl
  have h6 : ∀ x, x ∉ ⋃ j, Set.Ioo (A j) (c j) → g x = f x := by
    intro x hx
    have hb : ∀ j, b j x = 0 := by
      intro j
      simp only [b]
      rw [if_neg]
      intro hmem
      exact hx (Set.mem_iUnion.mpr ⟨j, hmem⟩)
    have hz : (∑' j, b j x) = 0 := by rw [tsum_congr hb, tsum_zero]
    simp only [g]
    rw [hz, sub_zero]
  have h7 : ∀ j, ∀ x ∈ Set.Ioo (A j) (c j),
      g x = (c j - A j)⁻¹ * ∫ t in (A j)..(c j), f t := by
    intro j x hx
    have hbj : b j x = f x - (c j - A j)⁻¹ * ∫ t in (A j)..(c j), f t := by
      simp only [b]; rw [if_pos hx]
    have hbj' : ∀ j', j' ≠ j → b j' x = 0 := by
      intro j' hj'
      have hdisj : Disjoint (Set.Ioo (A j) (c j)) (Set.Ioo (A j') (c j')) := h2 j j' (Ne.symm hj')
      have : x ∉ Set.Ioo (A j') (c j') := fun hmem => (Set.disjoint_left.mp hdisj hx) hmem
      simp only [b]; rw [if_neg this]
    have htsum : (∑' j', b j' x) = b j x := tsum_eq_single j hbj'
    simp only [g]
    rw [htsum, hbj]
    ring
  have hnotD : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∉ Set.range (fun p : ℕ × ℤ => dlo N p.1 p.2) := by
    rw [MeasureTheory.ae_iff]
    rw [show {a : ℝ | ¬ a ∉ Set.range (fun p : ℕ × ℤ => dlo N p.1 p.2)}
        = Set.range (fun p : ℕ × ℤ => dlo N p.1 p.2) from by ext a; simp]
    exact (Set.countable_range (fun p : ℕ × ℤ => dlo N p.1 p.2)).measure_zero MeasureTheory.volume
  have h8 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∉ ⋃ j, Set.Ioo (A j) (c j) → |f x| ≤ α := by
    have hgood := Commons.Analysis.Measure.ae_tendsto_interval_average (fun x => |f x|) hfabs
    filter_upwards [hgood, hnotD] with x hgx hxD
    intro hxnot
    by_contra hcon
    have hgt : α < |f x| := not_le.mp hcon
    obtain ⟨δ, hδpos, hδ⟩ := hgx (|f x| - α) (by linarith)
    obtain ⟨k, hk⟩ := exists_dlen_lt N hδpos
    set m0 : ℤ := ⌊x / dlen N k⌋ with hm0
    have hxcell : x ∈ dIv N k m0 := by rw [dIv_mem_iff, hm0]
    obtain ⟨hxle, hxlt⟩ := Set.mem_Ico.mp hxcell
    have hxne : x ≠ dlo N k m0 := fun h => hxD ⟨(k, m0), h.symm⟩
    have hdlone : dlo N k m0 < x := lt_of_le_of_ne hxle (Ne.symm hxne)
    have ha_pos : 0 < x - dlo N k m0 := by linarith
    have hb_pos : 0 < dhi N k m0 - x := by linarith
    have hab : (x - dlo N k m0) + (dhi N k m0 - x) = dlen N k := by
      have : dhi N k m0 - dlo N k m0 = dlen N k := by simp only [dhi, dlo]; ring
      linarith
    have hbnd := hδ (x - dlo N k m0) (dhi N k m0 - x) ha_pos.le hb_pos.le
      (by rw [hab]; exact hk) (by positivity)
    have hd1 : x - (x - dlo N k m0) = dlo N k m0 := by ring
    have hd2 : x + (dhi N k m0 - x) = dhi N k m0 := by ring
    have hS : (∫ y in (dlo N k m0)..(dhi N k m0), |f y|) = dS f N k m0 := rfl
    rw [hd1, hd2, hab, hS] at hbnd
    have hXgt : α < (dlen N k)⁻¹ * dS f N k m0 := by
      have := (abs_lt.mp hbnd).1
      linarith
    have hsel : dSel f α N k m0 := by
      unfold dSel
      have h := mul_lt_mul_of_pos_right hXgt (dlen_pos N k)
      have he : (dlen N k)⁻¹ * dS f N k m0 * dlen N k = dS f N k m0 := by
        rw [mul_assoc, mul_comm (dS f N k m0) (dlen N k),
          inv_mul_cancel_left₀ (ne_of_gt (dlen_pos N k))]
      rw [he] at h
      linarith
    obtain ⟨k', m', hmax, hx'max⟩ := exists_maximal_cell f α N hxcell hsel
    obtain ⟨j, hj⟩ : ∃ j, e j = (k', m') := ⟨e.symm (k', m'), e.apply_symm_apply _⟩
    refine absurd ?_ hxnot
    rw [Set.mem_iUnion]
    refine ⟨j, ?_⟩
    have hxI := Set.mem_Ico.mp hx'max
    have hxne' : x ≠ dlo N k' m' := fun h => hxD ⟨(k', m'), h.symm⟩
    have hxj : dlo N k' m' < x := lt_of_le_of_ne hxI.1 (Ne.symm hxne')
    have hAj : A j = dlo N k' m' := by simp only [A, hj, hmax, if_true]
    have hcj : c j = dhi N k' m' := by simp only [c, hj, hmax, if_true]
    rw [hAj, hcj]
    exact ⟨hxj, hxI.2⟩
  have h9 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), |g x| ≤ 2 * α := by
    filter_upwards [h8] with x hx
    by_cases hU : x ∈ ⋃ j, Set.Ioo (A j) (c j)
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hU
      rw [h7 j x hj]
      have hpos : 0 < c j - A j := sub_pos.mpr (lt_trans hj.1 hj.2)
      have hfin : |∫ t in (A j)..(c j), f t| ≤ ∫ t in (A j)..(c j), |f t| :=
        intervalIntegral.abs_integral_le_integral_abs (h1 j)
      calc |(c j - A j)⁻¹ * ∫ t in (A j)..(c j), f t|
          = |c j - A j|⁻¹ * |∫ t in (A j)..(c j), f t| := by rw [abs_mul, abs_inv]
        _ = (c j - A j)⁻¹ * |∫ t in (A j)..(c j), f t| := by rw [abs_of_pos hpos]
        _ ≤ (c j - A j)⁻¹ * ∫ t in (A j)..(c j), |f t| :=
            mul_le_mul_of_nonneg_left hfin (by positivity)
        _ ≤ (c j - A j)⁻¹ * (2 * α * (c j - A j)) :=
            mul_le_mul_of_nonneg_left (h4 j) (by positivity)
        _ = 2 * α := by
            rw [mul_comm (2 * α) (c j - A j), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    · rw [h6 x hU]
      exact le_trans (hx hU) (by linarith)
  have hterm : ∀ j, MeasureTheory.volume (Set.Ioo (A j) (c j))
      ≤ ENNReal.ofReal (α⁻¹ * ∫ x in Set.Ioo (A j) (c j), |f x|) := by
    intro j
    rw [Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    by_cases h : dMax f α N (e j).1 (e j).2
    · simp only [A, c, h, if_true]
      have hlen : dhi N (e j).1 (e j).2 - dlo N (e j).1 (e j).2 = dlen N (e j).1 := by
        simp only [dhi, dlo]; ring
      rw [hlen]
      have hInt : ∫ x in Set.Ioo (dlo N (e j).1 (e j).2) (dhi N (e j).1 (e j).2), |f x|
          = dS f N (e j).1 (e j).2 := by
        rw [MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
        exact (intervalIntegral.integral_of_le (le_of_lt (dlo_lt_dhi N (e j).1 (e j).2))).symm
      rw [hInt]
      have hsel := h.1
      unfold dSel at hsel
      have hfac : dlen N (e j).1 = α⁻¹ * (α * dlen N (e j).1) := by
        field_simp
      rw [hfac]
      exact mul_le_mul_of_nonneg_left (le_of_lt hsel) hαinv.le
    · simp only [A, c, h, if_false, sub_zero, Set.Ioo_self]
      simp
  have h10 : MeasureTheory.volume (⋃ j, Set.Ioo (A j) (c j))
      ≤ ENNReal.ofReal (α⁻¹ * ∫ x, |f x|) := by
    have hmeas : ∀ j, MeasurableSet (Set.Ioo (A j) (c j)) := fun j => measurableSet_Ioo
    have hdisj : Pairwise (Function.onFun Disjoint (fun j => Set.Ioo (A j) (c j))) :=
      fun j k hjk => h2 j k hjk
    rw [MeasureTheory.measure_iUnion hdisj hmeas]
    calc ∑' j, MeasureTheory.volume (Set.Ioo (A j) (c j))
        ≤ ∑' j, ENNReal.ofReal (α⁻¹ * ∫ x in Set.Ioo (A j) (c j), |f x|) :=
          ENNReal.tsum_le_tsum hterm
      _ = ∑' j, ENNReal.ofReal α⁻¹ * ENNReal.ofReal (∫ x in Set.Ioo (A j) (c j), |f x|) := by
          apply tsum_congr; intro j
          rw [ENNReal.ofReal_mul hαinv.le]
      _ = ENNReal.ofReal α⁻¹ * ∑' j, ENNReal.ofReal (∫ x in Set.Ioo (A j) (c j), |f x|) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal α⁻¹ * ∑' j, ∫⁻ x in Set.Ioo (A j) (c j), ENNReal.ofReal |f x| := by
          congr 1
          apply tsum_congr; intro j
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := MeasureTheory.volume.restrict (Set.Ioo (A j) (c j)))
            hfabs.integrableOn (Filter.Eventually.of_forall (fun x => abs_nonneg (f x)))]
      _ = ENNReal.ofReal α⁻¹ * ∫⁻ x in ⋃ j, Set.Ioo (A j) (c j), ENNReal.ofReal |f x| := by
          rw [MeasureTheory.lintegral_iUnion hmeas hdisj]
      _ ≤ ENNReal.ofReal α⁻¹ * ∫⁻ x, ENNReal.ofReal |f x| := by
          have hsub : ∫⁻ x in ⋃ j, Set.Ioo (A j) (c j), ENNReal.ofReal |f x|
              ≤ ∫⁻ x, ENNReal.ofReal |f x| := by
            simpa using (MeasureTheory.lintegral_mono_set (μ := MeasureTheory.volume)
              (s := ⋃ j, Set.Ioo (A j) (c j)) (t := Set.univ)
              (f := fun x : ℝ => ENNReal.ofReal |f x|) (Set.subset_univ _))
          exact mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = ENNReal.ofReal α⁻¹ * ENNReal.ofReal (∫ x, |f x|) := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfabs (Filter.Eventually.of_forall (fun x => abs_nonneg (f x)))]
      _ = ENNReal.ofReal (α⁻¹ * ∫ x, |f x|) := by
          rw [ENNReal.ofReal_mul hαinv.le]
  have h11 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      f x = g x + ∑' j, b j x := by
    filter_upwards with x
    simp only [g]
    ring
  exact ⟨A, c, g, b, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end Commons.Analysis.CalderonZygmund