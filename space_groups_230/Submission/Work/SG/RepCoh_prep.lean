import Mathlib
import Submission.Work.SG.SGRepDefs

/-!
# Flat-vector toolkit for `Work.SG.RepCoh_elim`

Elementary facts about `Data.ldot`, `RC.vadd/vsub/vz/vzero`, `RC.linC` and `RC.wcComb`
that the elimination argument (`RepCoh_elim`) needs.  Nothing here is `sorry`ed.
-/

namespace Work.SG

open Work.SG.RC

/-! ## `Data.ldot` -/

/-- `ldot u v` only sees the first `u.length` coordinates of `v`. -/
theorem ldot_eq_sum_getD (u v : List ℤ) :
    Data.ldot u v = ((List.range u.length).map (fun q => u.getD q 0 * v.getD q 0)).sum := by
  induction u generalizing v with
  | nil => simp [Data.ldot]
  | cons a t ih =>
    cases v with
    | nil => simp [Data.ldot]
    | cons b v' =>
      rw [Data.ldot, List.zipWith_cons_cons, List.sum_cons, List.length_cons,
        List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Data.ldot] at ih ⊢
      rw [ih v']

/-- `ldot` only depends on `v` through its `getD`-coordinates below `u.length`. -/
theorem ldot_congr {u v v' : List ℤ} (h : ∀ q < u.length, v.getD q 0 = v'.getD q 0) :
    Data.ldot u v = Data.ldot u v' := by
  rw [ldot_eq_sum_getD, ldot_eq_sum_getD]
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range] at hq
  rw [h q hq]

/-- Linearity of `ldot` in the first argument for `zipWith (fun a b => a + k * b)`. -/
theorem ldot_zipWith_add_mul (acc row : List ℤ) (k : ℤ) (v : List ℤ)
    (h : acc.length = row.length) :
    Data.ldot (List.zipWith (fun a b => a + k * b) acc row) v
      = Data.ldot acc v + k * Data.ldot row v := by
  induction acc generalizing row v with
  | nil =>
    cases row with
    | nil => simp [Data.ldot]
    | cons b r => simp at h
  | cons a t ih =>
    cases row with
    | nil => simp at h
    | cons b r =>
      cases v with
      | nil => simp [Data.ldot]
      | cons c v' =>
        simp only [List.length_cons] at h
        simp only [Data.ldot, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
        rw [ih r v' (by omega)]
        ring

theorem ldot_vadd (x y v : List ℤ) (h : x.length = y.length) :
    Data.ldot (vadd x y) v = Data.ldot x v + Data.ldot y v := by
  simpa [vadd, one_mul] using ldot_zipWith_add_mul x y 1 v h

theorem ldot_vsub (x y v : List ℤ) (h : x.length = y.length) :
    Data.ldot (vsub x y) v = Data.ldot x v - Data.ldot y v := by
  simpa [vsub, neg_one_mul, sub_eq_add_neg] using ldot_zipWith_add_mul x y (-1) v h

theorem ldot_vz (k : ℤ) (x v : List ℤ) :
    Data.ldot (vz k x) v = k * Data.ldot x v := by
  induction x generalizing v with
  | nil => simp [vz, Data.ldot]
  | cons a t ih =>
    cases v with
    | nil => simp [vz, Data.ldot]
    | cons c v' =>
      simp only [vz, List.map_cons, Data.ldot, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
      rw [ih v']
      ring

/-! ## Second-argument linearity of `ldot` -/

theorem ldot_vz_right (u : List ℤ) (k : ℤ) (x : List ℤ) :
    Data.ldot u (vz k x) = k * Data.ldot u x := by
  induction u generalizing x with
  | nil => simp [Data.ldot]
  | cons a t ih =>
    cases x with
    | nil => simp [vz, Data.ldot]
    | cons b x' =>
      simp only [vz, List.map_cons, Data.ldot, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
      rw [ih x']
      ring

theorem ldot_vadd_right (u x y : List ℤ) (h : x.length = y.length) :
    Data.ldot u (vadd x y) = Data.ldot u x + Data.ldot u y := by
  induction u generalizing x y with
  | nil => simp [Data.ldot]
  | cons a t ih =>
    cases x with
    | nil =>
      cases y with
      | nil => simp [vadd, Data.ldot]
      | cons c y' => simp at h
    | cons b x' =>
      cases y with
      | nil => simp at h
      | cons c y' =>
        simp only [vadd, List.zipWith_cons_cons, Data.ldot, List.sum_cons] at ih ⊢
        rw [ih x' y' (by simpa using h)]
        ring

theorem ldot_vsub_right (u x y : List ℤ) (h : x.length = y.length) :
    Data.ldot u (vsub x y) = Data.ldot u x - Data.ldot u y := by
  induction u generalizing x y with
  | nil => simp [Data.ldot]
  | cons a t ih =>
    cases x with
    | nil =>
      cases y with
      | nil => simp [vsub, Data.ldot]
      | cons c y' => simp at h
    | cons b x' =>
      cases y with
      | nil => simp at h
      | cons c y' =>
        simp only [vsub, List.zipWith_cons_cons, Data.ldot, List.sum_cons] at ih ⊢
        rw [ih x' y' (by simpa using h)]
        ring

theorem ldot_vzero (M : ℕ) (v : List ℤ) : Data.ldot (vzero M) v = 0 := by
  rw [ldot_eq_sum_getD]
  simp [vzero]

theorem ldot_replicate_zero (M : ℕ) (v : List ℤ) :
    Data.ldot (List.replicate M (0 : ℤ)) v = 0 := by
  rw [← vzero]
  exact ldot_vzero M v

/-! ## Coordinate and length facts for the flat vector operations -/

theorem vz_getD (k : ℤ) (x : List ℤ) (q : ℕ) :
    (vz k x).getD q 0 = k * x.getD q 0 := by
  rcases lt_or_ge q x.length with h | h
  · rw [vz, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact h),
      List.getElem_map, List.getD_eq_getElem _ _ h]
  · rw [vz, List.getD_eq_default _ _ (by rw [List.length_map]; exact h),
      List.getD_eq_default _ _ h]
    ring

theorem vz_length (k : ℤ) (x : List ℤ) : (vz k x).length = x.length := by
  simp [vz]

theorem vsub_length (x y : List ℤ) : (vsub x y).length = min x.length y.length := by
  simp [vsub]

theorem vadd_length (x y : List ℤ) : (vadd x y).length = min x.length y.length := by
  simp [vadd]

theorem vsub_getD (x y : List ℤ) {q : ℕ} (hx : q < x.length) (hy : q < y.length) :
    (vsub x y).getD q 0 = x.getD q 0 - y.getD q 0 := by
  rw [vsub, List.getD_eq_getElem _ _ (by rw [List.length_zipWith]; omega),
    List.getElem_zipWith, List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]

theorem vadd_getD (x y : List ℤ) {q : ℕ} (hx : q < x.length) (hy : q < y.length) :
    (vadd x y).getD q 0 = x.getD q 0 + y.getD q 0 := by
  rw [vadd, List.getD_eq_getElem _ _ (by rw [List.length_zipWith]; omega),
    List.getElem_zipWith, List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]

theorem vsub_getD_le (x y : List ℤ) {q : ℕ} (hx : x.length ≤ q) : (vsub x y).getD q 0 = 0 := by
  rw [List.getD_eq_default _ _ (by rw [vsub_length]; omega)]

theorem vzero_getD (M : ℕ) {q : ℕ} (h : q < M) : (vzero M).getD q 0 = 0 := by
  rw [vzero]
  exact List.getD_replicate (0 : ℤ) h

/-! ## `List.range` helpers -/

theorem sum_range_succ_map (f : ℕ → ℤ) (c : ℕ) :
    ((List.range (c+1)).map f).sum = ((List.range c).map f).sum + f c := by
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem map_range_getD (f : ℕ → ℤ) {M q : ℕ} (h : q < M) :
    ((List.range M).map f).getD q 0 = f q := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact h),
    List.getElem_map, List.getElem_range]

theorem append_singleton_getD (ts : List ℤ) (k : ℤ) {q : ℕ} (h : q < ts.length) :
    (ts ++ [k]).getD q 0 = ts.getD q 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; simp; omega),
    List.getElem_append_left (by exact h), List.getD_eq_getElem _ _ h]

theorem append_singleton_getD_self (ts : List ℤ) (k : ℤ) :
    (ts ++ [k]).getD ts.length 0 = k := by
  induction ts with
  | nil => rfl
  | cons a t ih => rw [List.cons_append, List.length_cons, List.getD_cons_succ]; exact ih

/-- Sums over `List.range` agree when the summands agree below the bound. -/
theorem sum_range_congr {f g : ℕ → ℤ} {c : ℕ} (h : ∀ c' < c, f c' = g c') :
    ((List.range c).map f).sum = ((List.range c).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range] at hq
  exact h q hq

/-- Inside the list, `getD` does not depend on the default value. -/
theorem getD_eq_getD_of_lt (l : List ℤ) {q : ℕ} (h : q < l.length) (a b : ℤ) :
    l.getD q a = l.getD q b := by
  rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h]

/-- `n ∣ a` from `a % n = 0`. -/
theorem dvd_of_emod {n a : ℤ} (h : a % n = 0) : n ∣ a := Int.dvd_iff_emod_eq_zero.mpr h

/-- `a % n = 0` from `n ∣ a`. -/
theorem emod_of_dvd {n a : ℤ} (h : n ∣ a) : a % n = 0 := Int.dvd_iff_emod_eq_zero.mp h

/-! ## `RC.wcComb` as an integer combination of rows of `R` -/

/-- The `ldot` of a `wcComb`-style fold with a vector is the fold of the `ldot`s. -/
theorem wcFold_ldot (R : List (List ℤ)) (M : ℕ) (s : List (ℕ × ℤ)) (acc : List ℤ) (v : List ℤ)
    (hacc : acc.length = M) (hRrow : ∀ row ∈ R, row.length = M)
    (hidx : ∀ p ∈ s, p.1 < R.length) :
    Data.ldot (s.foldl (fun a p => List.zipWith (fun x b => x + p.2 * b) a (R.getD p.1 [])) acc) v
      = Data.ldot acc v + (s.map (fun p => p.2 * Data.ldot (R.getD p.1 []) v)).sum := by
  induction s generalizing acc with
  | nil => simp
  | cons p t ih =>
    rw [List.foldl_cons]
    have hp : p.1 < R.length := hidx p (by simp)
    have hrow : (R.getD p.1 []).length = M := by
      rw [List.getD_eq_getElem _ _ hp]; exact hRrow _ (List.getElem_mem hp)
    have hacc' : (List.zipWith (fun x b => x + p.2 * b) acc (R.getD p.1 [])).length = M := by
      rw [List.length_zipWith, hacc, hrow, min_self]
    rw [ih _ hacc' (fun q hq => hidx q (by simp [hq]))]
    rw [ldot_zipWith_add_mul acc (R.getD p.1 []) p.2 v (by rw [hacc, hrow])]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- A `wcComb`-style fold over rows of `R` (all of length `M`) keeps length `M`. -/
theorem wcFold_length (R : List (List ℤ)) (M : ℕ) (s : List (ℕ × ℤ)) (acc : List ℤ)
    (hacc : acc.length = M) (hRrow : ∀ row ∈ R, row.length = M)
    (hidx : ∀ p ∈ s, p.1 < R.length) :
    (s.foldl (fun a p => List.zipWith (fun x b => x + p.2 * b) a (R.getD p.1 [])) acc).length
      = M := by
  induction s generalizing acc with
  | nil => simpa using hacc
  | cons p t ih =>
    rw [List.foldl_cons]
    apply ih
    · have hp : p.1 < R.length := hidx p (by simp)
      have hrow : (R.getD p.1 []).length = M := by
        rw [List.getD_eq_getElem _ _ hp]; exact hRrow _ (List.getElem_mem hp)
      rw [List.length_zipWith, hacc, hrow, min_self]
    · intro q hq; exact hidx q (by simp [hq])

/-- As soon as one row index is out of range the fold collapses to `[]`. -/
theorem wcFold_eq_nil (R : List (List ℤ)) (s : List (ℕ × ℤ)) (acc : List ℤ)
    (hidx : ∃ p ∈ s, R.length ≤ p.1) :
    s.foldl (fun a p => List.zipWith (fun x b => x + p.2 * b) a (R.getD p.1 [])) acc = [] := by
  have hnil : ∀ t : List (ℕ × ℤ),
      t.foldl (fun a p => List.zipWith (fun x b => x + p.2 * b) a (R.getD p.1 [])) [] = [] := by
    intro t
    induction t with
    | nil => rfl
    | cons p t ih => rw [List.foldl_cons, List.zipWith_nil_left, ih]
  induction s generalizing acc with
  | nil => simp at hidx
  | cons p t ih =>
    rw [List.foldl_cons]
    rcases hidx with ⟨q, hq, hbad⟩
    rcases List.mem_cons.mp hq with hqp | hqt
    · subst hqp
      rw [List.getD_eq_default _ _ hbad, List.zipWith_nil_right]
      exact hnil t
    · exact ih _ ⟨q, hqt, hbad⟩

/-- `RC.wcComb M R wc c` is the combination `∑ p.2 • R[p.1]` of rows, when all indices are valid. -/
theorem wcComb_ldot (M : ℕ) (R : List (List ℤ)) (wc : List (List (ℕ × ℤ))) (c : ℕ) (v : List ℤ)
    (hRrow : ∀ row ∈ R, row.length = M)
    (hidx : ∀ p ∈ wc.getD c [], p.1 < R.length) :
    Data.ldot (wcComb M R wc c) v
      = ((wc.getD c []).map (fun p => p.2 * Data.ldot (R.getD p.1 []) v)).sum := by
  change Data.ldot ((wc.getD c []).foldl
    (fun a p => List.zipWith (fun x b => x + p.2 * b) a (R.getD p.1 [])) (vzero M)) v = _
  rw [wcFold_ldot R M (wc.getD c []) (vzero M) v (by simp [vzero]) hRrow hidx, ldot_vzero]
  ring

/-- When all row indices of `wc.getD c []` are valid, `wcComb` has length `M`. -/
theorem wcComb_length (M : ℕ) (R : List (List ℤ)) (wc : List (List (ℕ × ℤ))) (c : ℕ)
    (hRrow : ∀ row ∈ R, row.length = M)
    (hidx : ∀ p ∈ wc.getD c [], p.1 < R.length) :
    (wcComb M R wc c).length = M := by
  change (List.foldl (fun a p => List.zipWith (fun x b => x + p.2 * b) a (R.getD p.1 []))
    (vzero M) (wc.getD c [])).length = M
  exact wcFold_length R M (wc.getD c []) (vzero M) (by simp [vzero]) hRrow hidx

/-- When some row index of `wc.getD c []` is out of range, `wcComb` collapses to `[]`. -/
theorem wcComb_eq_nil (M : ℕ) (R : List (List ℤ)) (wc : List (List (ℕ × ℤ))) (c : ℕ)
    (hidx : ∃ p ∈ wc.getD c [], R.length ≤ p.1) :
    wcComb M R wc c = [] := by
  change List.foldl (fun a p => List.zipWith (fun x b => x + p.2 * b) a (R.getD p.1 []))
    (vzero M) (wc.getD c []) = []
  exact wcFold_eq_nil R (wc.getD c []) (vzero M) hidx

end Work.SG
