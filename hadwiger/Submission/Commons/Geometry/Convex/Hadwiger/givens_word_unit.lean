import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic

open scoped BigOperators

namespace Commons.Geometry.Convex.Hadwiger

namespace GivensWordUnit

noncomputable section

def rot {m : ℕ} (e : Fin (m + 1) × ℝ × ℝ) (v : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  fun j => if j = (0 : Fin (m + 1)) then e.2.1 * v 0 - e.2.2 * v e.1
           else if j = e.1 then e.2.2 * v 0 + e.2.1 * v e.1 else v j

lemma rot_ne {m : ℕ} (e : Fin (m + 1) × ℝ × ℝ) (v : Fin (m + 1) → ℝ) {j : Fin (m + 1)}
    (hj0 : j ≠ (0 : Fin (m + 1))) (hjk : j ≠ e.1) : rot e v j = v j := by
  simp [rot, hj0, hjk]

lemma rot_zero {m : ℕ} (e : Fin (m + 1) × ℝ × ℝ) (v : Fin (m + 1) → ℝ) :
    rot e v (0 : Fin (m + 1)) = e.2.1 * v 0 - e.2.2 * v e.1 := by
  simp [rot]

lemma rot_k {m : ℕ} (e : Fin (m + 1) × ℝ × ℝ) (v : Fin (m + 1) → ℝ)
    (hk : e.1 ≠ (0 : Fin (m + 1))) :
    rot e v e.1 = e.2.2 * v 0 + e.2.1 * v e.1 := by
  simp [rot, hk]

lemma rot_zero_k {m : ℕ} (e : Fin (m + 1) × ℝ × ℝ) (v : Fin (m + 1) → ℝ)
    (hk : e.1 ≠ (0 : Fin (m + 1))) (hcd : e.2.1 ^ 2 + e.2.2 ^ 2 = 1) :
    (rot e v (0 : Fin (m + 1))) ^ 2 + (rot e v e.1) ^ 2 = (v 0) ^ 2 + (v e.1) ^ 2 := by
  rw [rot_zero, rot_k e v hk]
  nlinarith [hcd]

lemma sum_pair_erase {m : ℕ} (f : Fin (m + 1) → ℝ) (a : Fin (m + 1)) (ha : a ≠ (0 : Fin (m + 1))) :
    (∑ i : Fin (m + 1), f i) = f 0 + f a +
      ∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1))).erase a, f i := by
  classical
  have h1 : (∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1)) : Finset (Fin (m + 1))), f i) + f 0 =
      ∑ i : Fin (m + 1), f i :=
    Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (m + 1)))) (f := f)
      (a := (0 : Fin (m + 1))) (by simp)
  have ha_univ : a ∈ (Finset.univ.erase (0 : Fin (m + 1)) : Finset (Fin (m + 1))) := by simp [ha]
  have h2 : (∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1))).erase a, f i) + f a =
      ∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1)) : Finset (Fin (m + 1))), f i :=
    Finset.sum_erase_add (s := (Finset.univ.erase (0 : Fin (m + 1)) : Finset (Fin (m + 1)))) (f := f)
      (a := a) ha_univ
  calc
    (∑ i : Fin (m + 1), f i) = (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), f i) + f 0 := by
      rw [h1]
    _ = ((∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1))).erase a, f i) + f a) + f 0 := by rw [h2]
    _ = f 0 + f a + ∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1))).erase a, f i := by
      ring

lemma sum_sq_rot {m : ℕ} (e : Fin (m + 1) × ℝ × ℝ) (v : Fin (m + 1) → ℝ)
    (hk : e.1 ≠ (0 : Fin (m + 1))) (hcd : e.2.1 ^ 2 + e.2.2 ^ 2 = 1) :
    (∑ i : Fin (m + 1), (rot e v i) ^ 2) = ∑ i : Fin (m + 1), (v i) ^ 2 := by
  classical
  let f : Fin (m + 1) → ℝ := fun i => (rot e v i) ^ 2
  let g : Fin (m + 1) → ℝ := fun i => (v i) ^ 2
  have hpair : f (0 : Fin (m + 1)) + f e.1 = g (0 : Fin (m + 1)) + g e.1 := by
    dsimp [f, g]
    exact rot_zero_k e v hk hcd
  rw [sum_pair_erase f e.1 hk, sum_pair_erase g e.1 hk]
  rw [hpair]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≠ e.1 := (Finset.mem_erase.mp hi).1
  have hi0 : i ≠ (0 : Fin (m + 1)) := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  simp [f, g, rot_ne e v hi0 hik]

lemma givens_zero {m : ℕ} (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) (hk : k ≠ (0 : Fin (m + 1))) :
    ∃ e : Fin (m + 1) × ℝ × ℝ,
      e.1 = k ∧ e.2.1 ^ 2 + e.2.2 ^ 2 = 1 ∧
      rot e v k = 0 ∧
      (∀ j : Fin (m + 1), j ≠ (0 : Fin (m + 1)) → j ≠ k → rot e v j = v j) := by
  classical
  by_cases h : (v 0) ^ 2 + (v k) ^ 2 = 0
  · have hv0 : v 0 = 0 := by
      have hnonneg : 0 ≤ (v 0) ^ 2 + (v k) ^ 2 := add_nonneg (sq_nonneg (v 0)) (sq_nonneg (v k))
      have h0le : (v 0) ^ 2 ≤ 0 := by nlinarith
      exact sq_eq_zero_iff.mp (le_antisymm h0le (sq_nonneg (v 0)))
    have hvk : v k = 0 := by
      have hnonneg : 0 ≤ (v 0) ^ 2 + (v k) ^ 2 := add_nonneg (sq_nonneg (v 0)) (sq_nonneg (v k))
      have h0le : (v k) ^ 2 ≤ 0 := by nlinarith
      exact sq_eq_zero_iff.mp (le_antisymm h0le (sq_nonneg (v k)))
    refine ⟨(k, (1 : ℝ), (0 : ℝ)), rfl, by norm_num, ?_, ?_⟩
    · simp [rot, hk, hv0, hvk]
    · intro j hj0 hjk
      simp [rot, hj0, hjk]
  · let r : ℝ := Real.sqrt ((v 0) ^ 2 + (v k) ^ 2)
    let e : Fin (m + 1) × ℝ × ℝ := (k, (v 0) / r, -(v k) / r)
    have hnonneg : 0 ≤ (v 0) ^ 2 + (v k) ^ 2 := add_nonneg (sq_nonneg (v 0)) (sq_nonneg (v k))
    have hpos : 0 < (v 0) ^ 2 + (v k) ^ 2 := lt_of_le_of_ne' hnonneg h
    have hrpos : 0 < r := by
      dsimp [r]
      exact Real.sqrt_pos.mpr hpos
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hrsq : r ^ 2 = (v 0) ^ 2 + (v k) ^ 2 := by
      dsimp [r]
      exact Real.sq_sqrt (le_of_lt hpos)
    refine ⟨e, ?_, ?_, ?_, ?_⟩
    · rfl
    · dsimp [e]
      field_simp [hrne]
      rw [hrsq]
    · dsimp [e]
      simp [rot, hk]
      field_simp [hrne]
      ring
    · intro j hj0 hjk
      dsimp [e]
      simp [rot, hj0, hjk]

lemma exists_word_ks {m : ℕ} (ks : List (Fin (m + 1))) :
    ∀ (w : Fin (m + 1) → ℝ), (∀ k ∈ ks, k ≠ (0 : Fin (m + 1))) →
    ∃ l : List (Fin (m + 1) × ℝ × ℝ),
      (∀ e ∈ l, e.2.1 ^ 2 + e.2.2 ^ 2 = 1) ∧
      (∀ e ∈ l, e.1 ≠ (0 : Fin (m + 1))) ∧
      (∀ k ∈ ks, (List.foldl (fun acc e => rot e acc) w l) k = (0 : ℝ)) ∧
      (∀ j : Fin (m + 1), j ≠ (0 : Fin (m + 1)) → j ∉ ks →
        (List.foldl (fun acc e => rot e acc) w l) j = w j) ∧
      (∑ i : Fin (m + 1), ((List.foldl (fun acc e => rot e acc) w l) i) ^ 2) =
        ∑ i : Fin (m + 1), (w i) ^ 2 := by
  classical
  induction ks with
  | nil =>
      intro w hks
      refine ⟨[], ?_, ?_, ?_, ?_, ?_⟩
      · intro e he; simp at he
      · intro e he; simp at he
      · intro k hk; simp at hk
      · intro j hj0 hjks; simp
      · simp
  | cons k ks_tail ih =>
      intro w hks
      have hk0 : k ≠ (0 : Fin (m + 1)) := hks k (by simp)
      have hks_tail : ∀ k' ∈ ks_tail, k' ≠ (0 : Fin (m + 1)) := by
        intro k' hk'; exact hks k' (by simp [hk'])
      rcases givens_zero w k hk0 with ⟨e, he1, hecd, hezero, heother⟩
      rcases ih (rot e w) hks_tail with ⟨l_rest, hvalid_r, hidx_r, hzero_r, hunch_r, hnorm_r⟩
      have hfold : List.foldl (fun acc e => rot e acc) w (e :: l_rest) =
          List.foldl (fun acc e => rot e acc) (rot e w) l_rest := rfl
      refine ⟨e :: l_rest, ?_, ?_, ?_, ?_, ?_⟩
      · intro e' he'
        simp at he'
        rcases he' with rfl | he'
        · exact hecd
        · exact hvalid_r e' he'
      · intro e' he'
        simp at he'
        rcases he' with rfl | he'
        · rw [he1]
          exact hk0
        · exact hidx_r e' he'
      · intro k' hk'
        simp at hk'
        rcases hk' with hk'eq | hk'in
        · subst k'
          rw [hfold]
          by_cases hk_in : k ∈ ks_tail
          · exact hzero_r k hk_in
          · have h := hunch_r k hk0 hk_in
            rw [h, hezero]
        · rw [hfold]
          exact hzero_r k' hk'in
      · intro j hj0 hjks
        have hjk : j ≠ k := by
          intro hjk
          exact hjks (by simp [hjk])
        have hjt : j ∉ ks_tail := by
          intro hjt
          exact hjks (by simp [hjt])
        rw [hfold]
        rw [hunch_r j hj0 hjt]
        exact heother j hj0 hjk
      · rw [hfold]
        rw [hnorm_r]
        exact sum_sq_rot e w (by rw [he1]; exact hk0) hecd

lemma sum_univ_erase_zero {m : ℕ} (f : Fin (m + 1) → ℝ) :
    (∑ i : Fin (m + 1), f i) =
      f (0 : Fin (m + 1)) + ∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1)) : Finset (Fin (m + 1))), f i := by
  classical
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (m + 1)))) (f := f)
    (a := (0 : Fin (m + 1))) (by simp)
  rw [← h]
  ring

lemma sum_erase_zero_of_forall {m : ℕ} (g : Fin (m + 1) → ℝ)
    (hg : ∀ j : Fin (m + 1), j ≠ (0 : Fin (m + 1)) → g j = 0) :
    (∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1)) : Finset (Fin (m + 1))), g i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact hg i (Finset.mem_erase.mp hi).1

/-- Rotating the vector `-e₀` (first coordinate −1, rest 0) by a half-turn in the
plane spanned by coordinates `0` and `kf ≠ 0` gives `e₀`. -/
lemma rot_minus_e0 {m : ℕ} (kf : Fin (m + 1)) (_hkf0 : kf ≠ (0 : Fin (m + 1))) :
    rot (kf, (-1 : ℝ), (0 : ℝ))
      (fun j : Fin (m + 1) => if j = (0 : Fin (m + 1)) then (-1 : ℝ) else 0) =
      (fun j : Fin (m + 1) => if j = (0 : Fin (m + 1)) then (1 : ℝ) else 0) := by
  classical
  funext j
  by_cases hj : j = (0 : Fin (m + 1))
  · subst j
    simp [rot]
  · by_cases hjf : j = kf
    · subst j
      simp [rot]
    · simp [rot, hj, hjf]

end

end GivensWordUnit

open GivensWordUnit

theorem givens_word_unit (m : ℕ) (hm : 1 ≤ m) (w : Fin (m + 1) → ℝ)
    (hw : (∑ i : Fin (m + 1), w i ^ 2) = 1) :
    ∃ l : List (Fin (m + 1) × ℝ × ℝ),
      (∀ e ∈ l, e.2.1 ^ 2 + e.2.2 ^ 2 = 1) ∧
      (∀ e ∈ l, e.1 ≠ (0 : Fin (m + 1))) ∧
      l.foldl (fun acc (e : Fin (m + 1) × ℝ × ℝ) =>
        fun j : Fin (m + 1) =>
          if j = (0 : Fin (m + 1)) then e.2.1 * acc 0 - e.2.2 * acc e.1
          else if j = e.1 then e.2.2 * acc 0 + e.2.1 * acc e.1 else acc j) w =
        (fun j : Fin (m + 1) => if j = (0 : Fin (m + 1)) then 1 else 0) := by
  classical
  let e0 : Fin (m + 1) → ℝ := fun j => if j = (0 : Fin (m + 1)) then 1 else 0
  let ks : List (Fin (m + 1)) :=
    List.filter (fun k => decide (k ≠ (0 : Fin (m + 1)))) (List.finRange (m + 1))
  have hks : ∀ k ∈ ks, k ≠ (0 : Fin (m + 1)) := by
    intro k hk
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  have hmem_ks : ∀ j : Fin (m + 1), j ≠ (0 : Fin (m + 1)) → j ∈ ks := by
    intro j hj
    exact List.mem_filter.mpr ⟨List.mem_finRange j, decide_eq_true hj⟩
  rcases exists_word_ks ks w hks with ⟨l, hvalid, hidx, hzero, hunch, hnorm⟩
  let u : Fin (m + 1) → ℝ := List.foldl (fun acc e => rot e acc) w l
  have hz : ∀ j : Fin (m + 1), j ≠ (0 : Fin (m + 1)) → u j = 0 := by
    intro j hj
    dsimp [u]
    exact hzero j (hmem_ks j hj)
  have hsq : (∑ i : Fin (m + 1), (u i) ^ 2) = 1 := by
    dsimp [u]
    rw [hnorm, hw]
  have hu0 : u (0 : Fin (m + 1)) = 1 ∨ u (0 : Fin (m + 1)) = -1 := by
    have hsplit := sum_univ_erase_zero (fun i => (u i) ^ 2)
    have hrest : (∑ i ∈ (Finset.univ.erase (0 : Fin (m + 1)) : Finset (Fin (m + 1))), (u i) ^ 2) = 0 := by
      apply sum_erase_zero_of_forall
      intro j hj
      rw [hz j hj]
      norm_num
    have hsq0 : (u (0 : Fin (m + 1))) ^ 2 = 1 := by
      rw [hsplit, hrest, add_zero] at hsq
      exact hsq
    exact (sq_eq_one_iff.mp hsq0)
  by_cases h0 : u (0 : Fin (m + 1)) = 1
  · refine ⟨l, hvalid, hidx, ?_⟩
    change (List.foldl (fun acc e => rot e acc) w l) = e0
    have hu_e0 : u = e0 := by
      funext j
      by_cases hj : j = (0 : Fin (m + 1))
      · subst j
        dsimp [e0]
        exact h0
      · dsimp [e0]
        rw [if_neg hj]
        exact hz j hj
    simpa [u] using hu_e0
  · have hu_neg : u (0 : Fin (m + 1)) = -1 := hu0.resolve_left h0
    let kf : Fin (m + 1) := ⟨1, by omega⟩
    have hkf0 : kf ≠ (0 : Fin (m + 1)) := by
      dsimp [kf]
      exact Fin.ne_of_val_ne (by norm_num)
    let ef : Fin (m + 1) × ℝ × ℝ := (kf, (-1 : ℝ), (0 : ℝ))
    have hvalid_ef : ef.2.1 ^ 2 + ef.2.2 ^ 2 = 1 := by
      dsimp [ef]
      norm_num
    have hidx_ef : ef.1 ≠ (0 : Fin (m + 1)) := by
      dsimp [ef]
      exact hkf0
    have hu_negE0 : u = (fun j : Fin (m + 1) => if j = (0 : Fin (m + 1)) then (-1 : ℝ) else 0) := by
      funext j
      by_cases hj : j = (0 : Fin (m + 1))
      · subst j
        exact hu_neg
      · rw [if_neg hj]
        exact hz j hj
    refine ⟨l ++ [ef], ?_, ?_, ?_⟩
    · intro e he
      rw [List.mem_append] at he
      rcases he with he1 | he2
      · exact hvalid e he1
      · have : e = ef := List.mem_singleton.mp he2
        subst e
        exact hvalid_ef
    · intro e he
      rw [List.mem_append] at he
      rcases he with he1 | he2
      · exact hidx e he1
      · have : e = ef := List.mem_singleton.mp he2
        subst e
        exact hidx_ef
    · change (List.foldl (fun acc e => rot e acc) w (l ++ [ef])) = e0
      rw [List.foldl_append]
      change rot ef (List.foldl (fun acc e => rot e acc) w l) = e0
      change rot ef u = e0
      rw [hu_negE0]
      exact rot_minus_e0 kf hkf0

end Commons.Geometry.Convex.Hadwiger