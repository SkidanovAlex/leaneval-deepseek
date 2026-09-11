import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Multi
import Submission.MultiMass
import Submission.MultiW2

/-!
# Discretization helper layer: real analysis on level indices and finite sups (pure, no measure).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators NNReal

namespace Submission

namespace DiscretLvl

/-- the least level k ≤ L with v < (k+1)·ε, else 0 (v used only where such k exists) -/
noncomputable def levelIdx (ε : ℝ) (L : ℕ) (v : ℝ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, k ≤ L ∧ v < (k + 1 : ℕ) * ε then Nat.find h else 0

lemma levelIdx_spec (ε : ℝ) (L : ℕ) (v : ℝ) (h : ∃ k : ℕ, k ≤ L ∧ v < (k + 1 : ℕ) * ε) :
    levelIdx ε L v ≤ L ∧ v < (levelIdx ε L v + 1 : ℕ) * ε := by
  classical
  unfold levelIdx
  rw [dif_pos h]
  exact Nat.find_spec h

lemma levelIdx_le (ε : ℝ) (L : ℕ) (v : ℝ) (h : ∃ k : ℕ, k ≤ L ∧ v < (k + 1 : ℕ) * ε) :
    levelIdx ε L v ≤ L := (levelIdx_spec ε L v h).1

lemma levelIdx_lt (ε : ℝ) (L : ℕ) (v : ℝ) (h : ∃ k : ℕ, k ≤ L ∧ v < (k + 1 : ℕ) * ε) :
    v < (levelIdx ε L v + 1 : ℕ) * ε := (levelIdx_spec ε L v h).2

/-- approximation error of the level of v: |v − k·ε| ≤ ε when 0 ≤ v < (L+1)ε -/
lemma level_error (ε : ℝ) (hε : 0 < ε) (L : ℕ) (v : ℝ) (hv0 : 0 ≤ v) (hve : v < (L + 1 : ℕ) * ε) :
    |v - (levelIdx ε L v : ℝ) * ε| ≤ ε := by
  classical
  have h : ∃ k : ℕ, k ≤ L ∧ v < (k + 1 : ℕ) * ε := by
    exact ⟨L, le_rfl, hve⟩
  let k : ℕ := levelIdx ε L v
  have hklt : v < (k + 1 : ℕ) * ε := by
    simpa [k] using (levelIdx_lt ε L v h)
  have hkltR : v < ((k : ℝ) + 1) * ε := by
    have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
    rwa [hc] at hklt
  have hleA : v - (k : ℝ) * ε ≤ ε := by
    have : v < (k : ℝ) * ε + ε := by nlinarith [hkltR]
    linarith
  have hge : (k : ℝ) * ε ≤ v := by
    by_cases hk0 : k = 0
    · rw [hk0]
      simp
      exact hv0
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hm : k - 1 < k := Nat.sub_lt hkpos (by norm_num)
      have hfind0 : ∀ (m : ℕ), m < Nat.find h → ¬ (m ≤ L ∧ v < (m + 1 : ℕ) * ε) := by
        intro m hm
        exact Nat.find_min h hm
      have hfind : ∀ m : ℕ, m < levelIdx ε L v → ¬ (m ≤ L ∧ v < (m + 1 : ℕ) * ε) := by
        intro m hm
        unfold levelIdx at hm
        rw [dif_pos h] at hm
        exact hfind0 m hm
      have hkle : levelIdx ε L v ≤ L := levelIdx_le ε L v h
      have hnot : ¬ (k - 1 ≤ L ∧ v < (k - 1 + 1 : ℕ) * ε) := by
        simpa [k] using (hfind (k - 1) hm)
      have hnot2 : ¬ v < (k : ℕ) * ε := by
        have hEq : (k - 1 + 1 : ℕ) = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
        intro hx
        exact hnot ⟨by omega, by simpa [hEq] using hx⟩
      have hleN : (k : ℕ) * ε ≤ v := le_of_not_gt hnot2
      -- (k : ℕ) * ε with natural cast = (k : ℝ) * ε:
      simpa using hleN
  have hleB : -ε ≤ v - (k : ℝ) * ε := by linarith [hge]
  rw [abs_le]
  constructor <;> linarith

lemma sup_abs_sub_le (ε : ℝ) {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (hs : s.Nonempty)
    (h : ∀ i ∈ s, |a i - b i| ≤ ε) :
    |(s.image a).max' (by
      rcases hs with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
      - (s.image b).max' (by
      rcases hs with ⟨i, hi⟩
      exact ⟨b i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)| ≤ ε := by
  classical
  let ma : ℝ := (s.image a).max' (by
    rcases hs with ⟨i, hi⟩
    exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  let mb : ℝ := (s.image b).max' (by
    rcases hs with ⟨i, hi⟩
    exact ⟨b i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  have h1 : ma ≤ mb + ε := by
    unfold ma
    apply Finset.max'_le (s.image a) (by
      rcases hs with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) (mb + ε)
    intro y hy
    rcases (Finset.mem_image).1 hy with ⟨i, hi, rfl⟩
    have hab : |a i - b i| ≤ ε := h i hi
    have hab' : a i ≤ b i + ε := by linarith [(abs_le.mp hab).2]
    have hle : b i ≤ mb := by
      unfold mb
      exact Finset.le_max' (s.image b) (b i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    linarith
  have h2 : mb ≤ ma + ε := by
    unfold mb
    apply Finset.max'_le (s.image b) (by
      rcases hs with ⟨i, hi⟩
      exact ⟨b i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) (ma + ε)
    intro y hy
    rcases (Finset.mem_image).1 hy with ⟨i, hi, rfl⟩
    have hab : |a i - b i| ≤ ε := h i hi
    have hab' : b i ≤ a i + ε := by linarith [(abs_le.mp hab).1]
    have hle : a i ≤ ma := by
      unfold ma
      exact Finset.le_max' (s.image a) (a i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    linarith
  rw [abs_le]
  constructor
  · linarith [h2]
  · linarith [h1]


/-- leastness: (levelIdx ε L v : ℝ)·ε ≤ v (needs 0 ≤ v and an existence witness) -/
lemma levelIdx_ge (ε : ℝ) (L : ℕ) (v : ℝ) (hv0 : 0 ≤ v)
    (h : ∃ k : ℕ, k ≤ L ∧ v < (k + 1 : ℕ) * ε) : (levelIdx ε L v : ℝ) * ε ≤ v := by
  classical
  let k : ℕ := levelIdx ε L v
  have hkle : levelIdx ε L v ≤ L := levelIdx_le ε L v h
  have hge : (k : ℝ) * ε ≤ v := by
    by_cases hk0 : k = 0
    · rw [hk0]
      simp
      exact hv0
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hm : k - 1 < k := Nat.sub_lt hkpos (by norm_num)
      have hfind0 : ∀ (m : ℕ), m < Nat.find h → ¬ (m ≤ L ∧ v < (m + 1 : ℕ) * ε) := by
        intro m hm
        exact Nat.find_min h hm
      have hfind : ∀ m : ℕ, m < levelIdx ε L v → ¬ (m ≤ L ∧ v < (m + 1 : ℕ) * ε) := by
        intro m hmm
        unfold levelIdx at hmm
        rw [dif_pos h] at hmm
        exact hfind0 m hmm
      have hnot : ¬ (k - 1 ≤ L ∧ v < (k - 1 + 1 : ℕ) * ε) := by
        simpa [k] using (hfind (k - 1) hm)
      have hnot2 : ¬ v < (k : ℕ) * ε := by
        have hEq : (k - 1 + 1 : ℕ) = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
        have hkle' : k ≤ L := by simpa [k] using hkle
        intro hx
        exact hnot ⟨by omega, by simpa [hEq] using hx⟩
      have hleN : (k : ℕ) * ε ≤ v := le_of_not_gt hnot2
      simpa using hleN
  simpa [k] using hge

/-- level of v in [0,(L+1)ε): the unique k ≤ L with kε ≤ v < (k+1)ε, else 0.
Implemented as a sum of interval indicators so that it is easily measurable. -/
noncomputable def lvl (ε : ℝ) (L : ℕ) (v : ℝ) : ℕ :=
  ∑ k ∈ Finset.range (L + 1),
    if (k : ℝ) * ε ≤ v ∧ v < ((k + 1 : ℕ) : ℝ) * ε then k else 0

/-- in-range v is in at most one level interval -/
lemma lvl_of_unique {ε : ℝ} (hε0 : 0 ≤ ε) (L : ℕ) (v : ℝ) {k : ℕ} (hk : k ≤ L)
    (h1 : (k : ℝ) * ε ≤ v) (h2 : v < ((k + 1 : ℕ) : ℝ) * ε) : lvl ε L v = k := by
  classical
  unfold lvl
  let f : ℕ → ℕ := fun k' => if (k' : ℝ) * ε ≤ v ∧ v < ((k' + 1 : ℕ) : ℝ) * ε then k' else 0
  have hsides : ∀ b ∈ Finset.range (L + 1), b ≠ k → f b = 0 := by
    intro b hbR hne
    unfold f
    by_cases hbk : b < k
    · have hge2 : ¬ ((b : ℝ) * ε ≤ v ∧ v < ((b + 1 : ℕ) : ℝ) * ε) := by
        intro hh
        rcases hh with ⟨hle, hlt⟩
        have hc : ((b + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hbk)
        have hcm : ((b + 1 : ℕ) : ℝ) * ε ≤ (k : ℝ) * ε := by
          exact mul_le_mul_of_nonneg_right hc hε0
        linarith
      rw [if_neg hge2]
    · have hgt : k < b := lt_of_le_of_ne (le_of_not_gt hbk) (by intro hEq; exact hne hEq.symm)
      have hge2 : ¬ ((b : ℝ) * ε ≤ v ∧ v < ((b + 1 : ℕ) : ℝ) * ε) := by
        intro hh
        rcases hh with ⟨hle, hlt⟩
        have hc : ((k + 1 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hgt)
        have hcm : ((k + 1 : ℕ) : ℝ) * ε ≤ (b : ℝ) * ε := by
          exact mul_le_mul_of_nonneg_right hc hε0
        have : v < (b : ℝ) * ε := lt_of_lt_of_le (by simpa using h2) hcm
        linarith
      rw [if_neg hge2]
  have hmain : f k = k := by
    unfold f
    have hc : (k : ℝ) * ε ≤ v ∧ v < ((k + 1 : ℕ) : ℝ) * ε := ⟨h1, h2⟩
    rw [if_pos hc]
  calc
    (∑ k' ∈ Finset.range (L + 1),
      if (k' : ℝ) * ε ≤ v ∧ v < ((k' + 1 : ℕ) : ℝ) * ε then k' else 0) = f k := by
      rw [Finset.sum_eq_single (s := Finset.range (L + 1)) (f := f) k hsides]
      · intro hknot
        exfalso
        exact hknot (by simpa [Nat.lt_iff_add_one_le] using hk)
    _ = k := hmain

/-- error bound for the level map (0 ≤ v < (L+1)ε) -/
lemma lvl_error {ε : ℝ} (hε : 0 < ε) (L : ℕ) (v : ℝ) (hv0 : 0 ≤ v)
    (hve : v < ((L + 1 : ℕ) : ℝ) * ε) : |v - (lvl ε L v : ℝ) * ε| ≤ ε := by
  classical
  have h : ∃ k : ℕ, k ≤ L ∧ v < (k + 1 : ℕ) * ε := ⟨L, le_rfl, by simpa using hve⟩
  have hge := levelIdx_ge ε L v hv0 h
  have hle := levelIdx_le ε L v h
  have hlt := levelIdx_lt ε L v h
  have hl : lvl ε L v = levelIdx ε L v := by
    apply lvl_of_unique (le_of_lt hε) L v hle hge
    simpa using hlt
  have herr := level_error ε hε L v hv0 hve
  rwa [← hl] at herr

end DiscretLvl
end Submission
