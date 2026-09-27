import Submission.Work.PL.Subdiv.Cube.Defs

/-!
# The barycentric ("level") coordinates of the Freudenthal simplex

For the Freudenthal simplex `unitSimp π` of the unit cube, this file provides the `n+1` affine
functionals `lev π k` whose non-negativity cuts out `unitSimp π`, and for which the vertex
`wvec π k` is the barycentric-coordinate point `δ_{kj}`.  Consequently `unitSimp π` is a simplex
with vertex set `unitVerts π`, and every point `y` of `E n` is the combination
`∑ k, lev π k y • wvec π k`.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv.Cube

noncomputable section

variable {n : ℕ}

/-- The level of `y` at position `j` of the order `π`: `y (π j)` for `j < n`, and `1` for
`j ≥ n` (the "top" level). -/
def levf (π : Equiv.Perm (Fin n)) (y : PL.E n) (j : ℕ) : ℝ :=
  if h : j < n then y (π ⟨j, h⟩) else 1

lemma levf_lt (π : Equiv.Perm (Fin n)) (y : PL.E n) {j : ℕ} (h : j < n) :
    levf π y j = y (π ⟨j, h⟩) := by
  simp [levf, h]

lemma levf_ge (π : Equiv.Perm (Fin n)) (y : PL.E n) {j : ℕ} (h : ¬ j < n) :
    levf π y j = 1 := by
  simp [levf, h]

/-- The `k`-th gap of `y` in the order `π`. -/
def lev (π : Equiv.Perm (Fin n)) (k : ℕ) (y : PL.E n) : ℝ :=
  levf π y k - (if k = 0 then 0 else levf π y (k - 1))

@[simp] lemma lev_zero (π : Equiv.Perm (Fin n)) (y : PL.E n) : lev π 0 y = levf π y 0 := by
  simp [lev]

lemma lev_succ (π : Equiv.Perm (Fin n)) (y : PL.E n) (k : ℕ) :
    lev π (k + 1) y = levf π y (k + 1) - levf π y k := by
  simp [lev]

/-- Telescoping: the sum of the gaps up to `N` is the level `N`. -/
lemma sum_lev (π : Equiv.Perm (Fin n)) (y : PL.E n) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), lev π k y = levf π y N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, lev_succ]
    ring

/-- The level function is monotone below the top, for points of the simplex. -/
lemma levf_mono (π : Equiv.Perm (Fin n)) (y : PL.E n) (hy : y ∈ unitSimp π) {j j' : ℕ}
    (hj : j ≤ j') (hj' : j' ≤ n) : levf π y j ≤ levf π y j' := by
  rcases lt_or_ge j n with hjn | hjn
  · rw [levf_lt π y hjn]
    rcases lt_or_ge j' n with hj'n | hj'n
    · rw [levf_lt π y hj'n]
      exact hy.2 ⟨j, hjn⟩ ⟨j', hj'n⟩ (by exact_mod_cast hj)
    · rw [levf_ge π y (not_lt.mpr hj'n)]
      exact (hy.1 (π ⟨j, hjn⟩)).2
  · have h2 : levf π y j' = 1 := levf_ge π y (not_lt.mpr (le_trans hjn hj))
    rw [levf_ge π y (not_lt.mpr hjn), h2]

/-- The gaps are non-negative on the simplex. -/
lemma lev_nonneg (π : Equiv.Perm (Fin n)) (y : PL.E n) (hy : y ∈ unitSimp π) {k : ℕ}
    (hk : k ≤ n) : 0 ≤ lev π k y := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [lev_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · rw [levf_ge π y (by omega)]
      norm_num
    · rw [levf_lt π y hnpos]
      exact (hy.1 _).1
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
    rw [lev_succ]
    have := levf_mono π y hy (j := m) (j' := m + 1) (by omega) (by omega)
    linarith

lemma fin_ext_apply (π : Equiv.Perm (Fin n)) (i : Fin n) {h : (π.symm i : ℕ) < n} :
    π ⟨(π.symm i : ℕ), h⟩ = i := by
  rw [show (⟨(π.symm i : ℕ), h⟩ : Fin n) = π.symm i from Fin.ext rfl, Equiv.apply_symm_apply]

/-- `unitSimp π` is exactly the intersection of the half spaces `lev π k · ≥ 0`. -/
lemma unitSimp_iff_lev (π : Equiv.Perm (Fin n)) (y : PL.E n) :
    y ∈ unitSimp π ↔ ∀ k ≤ n, 0 ≤ lev π k y := by
  constructor
  · intro hy k hk
    exact lev_nonneg π y hy hk
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      have hi : (π.symm i : ℕ) < n := (π.symm i).isLt
      have hlev : y i = ∑ k ∈ Finset.range ((π.symm i : ℕ) + 1), lev π k y := by
        rw [sum_lev π y (π.symm i : ℕ), levf_lt π y hi, fin_ext_apply π i]
      refine ⟨?_, ?_⟩
      · rw [hlev]
        exact Finset.sum_nonneg fun k hk =>
          h k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (Nat.le_of_lt hi))
      · have hn : levf π y n = 1 := levf_ge π y (by omega)
        rw [hlev, ← hn, ← sum_lev π y n]
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt hi))) ?_
        intro k hk _
        exact h k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) le_rfl)
    · intro a b hab
      have h1 : y (π a) = ∑ k ∈ Finset.range ((a : ℕ) + 1), lev π k y := by
        rw [sum_lev π y (a : ℕ), levf_lt π y a.isLt,
            show (⟨(a : ℕ), a.isLt⟩ : Fin n) = a from Fin.ext rfl]
      have h2 : y (π b) = ∑ k ∈ Finset.range ((b : ℕ) + 1), lev π k y := by
        rw [sum_lev π y (b : ℕ), levf_lt π y b.isLt,
            show (⟨(b : ℕ), b.isLt⟩ : Fin n) = b from Fin.ext rfl]
      rw [h1, h2]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ?_) ?_
      · exact Nat.succ_le_succ (by exact_mod_cast hab)
      · intro k hk _
        exact h k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (Nat.le_of_lt b.isLt))

/-- Levels of the vertices: `lev π k (wvec π j) = δ_{kj}`. -/
lemma lev_wvec (π : Equiv.Perm (Fin n)) {k j : ℕ} (hk : k ≤ n) (hj : j ≤ n) :
    lev π k (wvec π j) = if j = k then 1 else 0 := by
  have hlevf : ∀ m, levf π (wvec π j) m = if j ≤ m then 1 else 0 := by
    intro m
    rcases lt_or_ge m n with hm | hm
    · rw [levf_lt π (wvec π j) hm, wvec_at]
    · rw [levf_ge π (wvec π j) (not_lt.mpr hm)]
      have : j ≤ m := le_trans hj hm
      simp [this]
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [lev_zero, hlevf]
    simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
    rw [lev_succ, hlevf, hlevf]
    by_cases h : j ≤ m
    · have hne : j ≠ m + 1 := by omega
      have h1 : j ≤ m + 1 := by omega
      simp [h, hne, h1]
    · by_cases h3 : j = m + 1
      · have h1 : j ≤ m + 1 := by omega
        simp [h, h3, h1]
      · have h1 : ¬ j ≤ m + 1 := by omega
        simp [h, h3, h1]

/-- Reconstruction: any point of `E n` is the combination of the vertices with the level
functionals as coefficients. -/
lemma sum_lev_smul_wvec (π : Equiv.Perm (Fin n)) (y : PL.E n) :
    ∑ k ∈ Finset.range (n + 1), lev π k y • wvec π k = y := by
  ext i
  obtain ⟨a, rfl⟩ : ∃ a, π a = i := ⟨π.symm i, by simp⟩
  have ha : (a : ℕ) < n := a.isLt
  rw [show (∑ k ∈ Finset.range (n + 1), lev π k y • wvec π k) (π a)
      = (∑ k ∈ Finset.range (n + 1), lev π k y • wvec π k).ofLp (π a) from rfl,
    WithLp.ofLp_sum, Finset.sum_apply]
  have hterm : ∀ k, (lev π k y • wvec π k).ofLp (π a)
      = lev π k y * (if k ≤ (a : ℕ) then 1 else 0) := by
    intro k
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, wvec_at]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hsub : Finset.range ((a : ℕ) + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (by omega)
  have hzero : ∀ x ∈ Finset.range (n + 1), x ∉ Finset.range ((a : ℕ) + 1) →
      lev π x y * (if x ≤ (a : ℕ) then 1 else 0) = 0 := by
    intro x _ hx'
    simp only [Finset.mem_range, not_lt] at hx'
    rw [if_neg (Nat.not_le.mpr hx'), mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  have hone : ∀ x ∈ Finset.range ((a : ℕ) + 1),
      lev π x y * (if x ≤ (a : ℕ) then 1 else 0) = lev π x y := by
    intro x hx
    rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)), mul_one]
  rw [Finset.sum_congr rfl hone, sum_lev π y (a : ℕ), levf_lt π y ha,
      show (⟨(a : ℕ), ha⟩ : Fin n) = a from Fin.ext rfl]

end

end Work.PL.Subdiv.Cube
