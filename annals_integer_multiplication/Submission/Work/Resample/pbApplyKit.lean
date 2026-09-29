import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.encodeNatBridge

/-!
# `Work.Resample.pbApplyAlongT`: shared definitions

Definitions and elementary lemmas shared between `Work.Resample.pbApplyAlongT` and the helper
lemmas it delegates:

* `ppMB` — the polynomial overhead `(A*B*(m+n+1)+1) * (L + (A*B*(m+n+1)).size + 1) * (…size+1)`
  of `Work.Resample.ApplyAlongWord` (the middle term of its cost);
* `ppSA` — `isz A + isz m + isz n + isz B` (the last term's bracket);
* `unOfList` — a left inverse of `ofList` on `cons`-chains, used to read a value back out as a
  list of values.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The polynomial overhead of `ApplyAlongWord`: the middle factor of its cost. -/
def ppMB (A B m n L : ℕ) : ℕ :=
  (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1)
    * ((A * B * (m + n + 1)).size + 1)

/-- The bracket `isz A + isz m + isz n + isz B` of the last term of the budget of
`ApplyAlongWord`. -/
def ppSA (A m n B : ℕ) : ℕ := isz A + isz m + isz n + isz B

/-- `a ≤ a * (b+1)`. -/
private theorem le_mul_succ (a b : ℕ) : a ≤ a * (b + 1) := by
  have h : a * 1 ≤ a * (b + 1) := Nat.mul_le_mul_left a (by omega)
  simpa using h

theorem ppMB_pos (A B m n L : ℕ) : 1 ≤ ppMB A B m n L := by
  have h1 : 0 < A * B * (m + n + 1) + 1 := by omega
  have h2 : 0 < L + (A * B * (m + n + 1)).size + 1 := by omega
  have h3 : 0 < (A * B * (m + n + 1)).size + 1 := by omega
  unfold ppMB
  exact Nat.mul_pos (Nat.mul_pos h1 h2) h3

/-- A product `c*d` with `c ≤ A*B*(m+n+1)` and `d ≤ L + (A*B*(m+n+1)).size + 1` is bounded by
`ppMB`. -/
theorem mul_le_ppMB {A B m n L c d : ℕ} (hc : c ≤ A * B * (m + n + 1))
    (hd : d ≤ L + (A * B * (m + n + 1)).size + 1) : c * d ≤ ppMB A B m n L := by
  have h2 : (A * B * (m + n + 1)) * (L + (A * B * (m + n + 1)).size + 1) ≤
      (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1) ≤
      (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1)
        * ((A * B * (m + n + 1)).size + 1) := le_mul_succ _ _
  unfold ppMB
  exact le_trans (le_trans (Nat.mul_le_mul hc hd) h2) h3

/-- `c*(L+1) ≤ ppMB` when `c ≤ A*B*(m+n+1)`. -/
theorem mul_L_le_ppMB {A B m n L c : ℕ} (hc : c ≤ A * B * (m + n + 1)) :
    c * (L + 1) ≤ ppMB A B m n L :=
  mul_le_ppMB hc (by omega)

/-- `c*((A*B*(m+n+1)).size + 1) ≤ ppMB` when `c ≤ A*B*(m+n+1)`. -/
theorem mul_size_le_ppMB {A B m n L c : ℕ} (hc : c ≤ A * B * (m + n + 1)) :
    c * ((A * B * (m + n + 1)).size + 1) ≤ ppMB A B m n L :=
  mul_le_ppMB hc (by omega)

/-- `c ≤ ppMB` when `c ≤ A*B*(m+n+1)`. -/
theorem le_ppMB {A B m n L c : ℕ} (hc : c ≤ A * B * (m + n + 1)) : c ≤ ppMB A B m n L := by
  have h1 : c ≤ c * (L + (A * B * (m + n + 1)).size + 1) := le_mul_succ _ _
  have h2 := mul_le_ppMB (A := A) (B := B) (m := m) (n := n) (L := L) hc
    (d := L + (A * B * (m + n + 1)).size + 1) (le_refl _)
  exact le_trans h1 h2

/-- Decoding a value into a list; `ofList`'s inverse on `cons`-chains. -/
def unOfList : Val → List Val
  | .nil => []
  | .cons a b => a :: unOfList b
  | .int _ => []

theorem unOfList_ofList (l : List Val) : unOfList (ofList l) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show x :: unOfList (ofList xs) = x :: xs
    rw [ih]

theorem ofList_unOfList_ofList (l : List Val) : ofList (unOfList (ofList l)) = ofList l := by
  rw [unOfList_ofList]

/-- The size of a `cons` value. -/
theorem vsz_cons' (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  show (a.enc ++ b.enc).length + 1 = a.enc.length + b.enc.length + 1
  rw [List.length_append]

/-- `vsz (ofList xs)` is bounded by the number of elements times the maximal element size. -/
theorem vsz_ofList_le' {xs : List Val} {B : ℕ} (h : ∀ x ∈ xs, vsz x ≤ B) :
    vsz (ofList xs) ≤ (xs.length + 1) * (B + 1) := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
    have hx : vsz x ≤ B := h x (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ B := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    have hcons : ofList (x :: t) = Val.cons x (ofList t) := rfl
    rw [hcons, vsz_cons', List.length_cons]
    have key : (t.length + 1 + 1) * (B + 1) = (t.length + 1) * (B + 1) + (B + 1) := by ring
    omega

/-- The size of `Val.int A` (as a value) is `isz A`. -/
theorem vsz_int_nat (A : ℕ) : vsz (Val.int (A : ℤ)) = isz A := by
  show (Val.int (A : ℤ)).enc.length = isz (A : ℤ)
  rw [Work.IntLib.vsz_int]

theorem isz_nat_size (n : ℕ) : isz (n : ℤ) = n.size + 2 := by
  rw [isz, Int.natAbs_natCast]

theorem isz_le_add (n : ℕ) : isz (n : ℤ) ≤ n + 2 := by
  rw [isz_nat_size]
  exact Nat.add_le_add_right ((Nat.size_le).mpr Nat.lt_two_pow_self) 2

end Work.Resample

namespace Work.Resample

open HvdH

/-! ## Pure list facts about `slices` / `unslices` and `flatten` -/


/-! ## Pure list facts about `slices` / `unslices` and `flatten` -/

theorem getD_map_range' {α : Type} (f : ℕ → α) (d : α) {k i : ℕ} (hi : i < k) :
    ((List.range k).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem flatten_slices_length {α : Type} [Inhabited α] (A m B : ℕ) (es : List α) :
    (List.flatten (HvdH.slices A m B es)).length = A * m * B := by
  simp only [HvdH.slices]
  rw [List.length_flatten, List.map_map]
  have hmap : ((List.range (A * B)).map (List.length ∘ fun s =>
      (List.range m).map fun j => es.getD ((s / B * m + j) * B + s % B) (default : α)))
      = (List.range (A * B)).map (fun _ => m) := by
    apply List.map_congr_left
    intro s _
    simp only [Function.comp_apply, List.length_map, List.length_range]
  rw [hmap, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem slices_idx_lt {A m B : ℕ} (es : List Val) (h : es.length = A * m * B) {s j : ℕ}
    (hs : s < A * B) (hj : j < m) : (s / B * m + j) * B + s % B < es.length := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0, Nat.mul_zero] at hs
      omega
    · exact h0
  have h1 : s / B < A := (Nat.div_lt_iff_lt_mul hB).mpr hs
  have h2 : s / B * m + j + 1 ≤ A * m := by
    have h3 : s / B + 1 ≤ A := Nat.succ_le_of_lt h1
    have h4 : s / B * m + j + 1 ≤ (s / B + 1) * m := by
      have h5 : (s / B + 1) * m = s / B * m + m := by ring
      omega
    have h6 : (s / B + 1) * m ≤ A * m := Nat.mul_le_mul_right m h3
    exact le_trans h4 h6
  have h7 : (s / B * m + j + 1) * B ≤ A * m * B := Nat.mul_le_mul_right B h2
  have h10 : s % B < B := Nat.mod_lt _ hB
  have h8 : (s / B * m + j) * B + s % B < (s / B * m + j + 1) * B := by
    have h9 : (s / B * m + j + 1) * B = (s / B * m + j) * B + B := by ring
    omega
  have h11 : (s / B * m + j) * B + s % B < A * m * B := lt_of_lt_of_le h8 h7
  have h12 : A * m * B = es.length := h.symm
  rw [h12] at h11
  exact h11

theorem mem_slices_getD (A m B : ℕ) (es : List Val) (h : es.length = A * m * B) {s : ℕ}
    (hs : s < A * B) {x : Val} (hx : x ∈ (HvdH.slices A m B es).getD s []) : x ∈ es := by
  rw [HvdH.slices] at hx
  rw [getD_map_range' _ _ hs] at hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  rw [List.getD_eq_getElem _ _ (slices_idx_lt es h hs (List.mem_range.mp hj))]
  simp

theorem mem_flatten_slices (A m B : ℕ) (es : List Val) (h : es.length = A * m * B)
    {x : Val} (hx : x ∈ List.flatten (HvdH.slices A m B es)) : x ∈ es := by
  rw [List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  obtain ⟨s, hs, hsl⟩ := List.mem_iff_getElem.mp hl
  have hlenL : (HvdH.slices A m B es).length = A * B := by simp [HvdH.slices]
  have hsAB : s < A * B := by rwa [hlenL] at hs
  have hs' : s < (HvdH.slices A m B es).length := by rw [hlenL]; exact hsAB
  have hls : l = (HvdH.slices A m B es).getD s [] := by
    rw [← hsl]
    exact (List.getD_eq_getElem _ _ hs').symm
  rw [hls] at hxl
  exact mem_slices_getD A m B es h hsAB hxl

theorem getD_flatten_blocks_aux : ∀ (outs : List (List Val)) (n : ℕ),
    (∀ l ∈ outs, l.length = n) → ∀ (s j : ℕ), s < outs.length → j < n →
    (List.flatten outs).getD (s * n + j) default = (outs.getD s []).getD j default := by
  intro outs
  induction outs with
  | nil => intro n hsl s j hs hj; simp at hs
  | cons l ls ih =>
    intro n hsl s j hs hj
    have hl : l.length = n := hsl l (by simp)
    have hls : ∀ l' ∈ ls, l'.length = n := fun l' h' => hsl l' (by simp [h'])
    have hls' : ∀ l' ∈ ls, l'.length = n := hls
    cases s with
    | zero =>
      rw [List.flatten_cons, Nat.zero_mul, Nat.zero_add]
      rw [List.getD_append _ _ _ _ (by omega : j < l.length)]
      rfl
    | succ s' =>
      have hs' : s' < ls.length := by simpa using hs
      rw [List.flatten_cons]
      have hidx : (s' + 1) * n + j = n + (s' * n + j) := by ring
      rw [hidx, List.getD_append_right _ _ _ _ (by omega : l.length ≤ n + (s' * n + j))]
      have hsub : n + (s' * n + j) - l.length = s' * n + j := by omega
      rw [hsub]
      simp only [List.getD_cons_succ]
      exact ih n hls' s' j hs' hj

theorem getD_flatten_blocks {outs : List (List Val)} {n : ℕ} (hsl : ∀ l ∈ outs, l.length = n)
    {s j : ℕ} (hs : s < outs.length) (hj : j < n) :
    (List.flatten outs).getD (s * n + j) default = (outs.getD s []).getD j default :=
  getD_flatten_blocks_aux outs n hsl s j hs hj

theorem flatten_slices_getD (A B n : ℕ) (es : List Val) {idx : ℕ} (hidx : idx < A * n * B) :
    (List.flatten (HvdH.slices A B n es)).getD idx default =
      es.getD (((idx / B) / n * B + idx % B) * n + (idx / B) % n) default := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0, Nat.mul_zero] at hidx; omega
    · exact h0
  have hlen : (HvdH.slices A B n es).length = A * n := by simp [HvdH.slices]
  have hs : idx / B < (HvdH.slices A B n es).length := by
    rw [hlen, Nat.div_lt_iff_lt_mul hB]
    exact hidx
  have hmod : idx % B < B := Nat.mod_lt _ hB
  have hsl : ∀ l ∈ HvdH.slices A B n es, l.length = B := by
    intro l hl
    rw [HvdH.slices, List.mem_map] at hl
    obtain ⟨s, _, rfl⟩ := hl
    simp
  have hblk := getD_flatten_blocks (outs := HvdH.slices A B n es) (n := B) hsl hs hmod
  have hsplit : idx / B * B + idx % B = idx := by
    rw [Nat.mul_comm (idx / B) B]
    exact Nat.div_add_mod idx B
  rw [hsplit] at hblk
  rw [hblk]
  unfold HvdH.slices
  rw [getD_map_range' _ _ (by rw [← hlen]; exact hs)]
  rw [getD_map_range' _ _ hmod]

theorem flatten_slices_unslices {A n B : ℕ} {outs : List (List Val)} (hlen : outs.length = A * B)
    (hsl : ∀ l ∈ outs, l.length = n) :
    List.flatten (HvdH.slices A B n (List.flatten outs)) = HvdH.unslices A n B outs := by
  rcases Nat.eq_zero_or_pos B with hB0 | hB
  · subst hB0
    simp [HvdH.slices, HvdH.unslices]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have h2 : List.flatten outs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      rw [List.mem_flatten] at hx
      obtain ⟨l, hl, hxl⟩ := hx
      have h3 := hsl l hl
      rw [List.eq_nil_of_length_eq_zero h3] at hxl
      exact List.not_mem_nil hxl
    rw [h2]
    simp [HvdH.slices, HvdH.unslices]
  · apply List.ext_getElem
    · rw [flatten_slices_length]
      simp only [HvdH.unslices, List.length_map, List.length_range]
      ring
    · intro idx h1 h2
      rw [List.getElem_eq_getD (h := h1) default, List.getElem_eq_getD (h := h2) default]
      have hABn : A * n * B = A * B * n := by ring
      have hidx : idx < A * n * B := by
        rw [hABn]
        rw [flatten_slices_length] at h1
        exact h1
      rw [flatten_slices_getD A B n (List.flatten outs) hidx]
      simp only [HvdH.unslices]
      rw [getD_map_range' _ _ (by simpa [HvdH.unslices] using h2)]
      have hq : (idx / B) / n * B + idx % B < outs.length := by
        rw [hlen]
        have h3 : (idx / B) / n < A := by
          rw [Nat.div_lt_iff_lt_mul hn, Nat.div_lt_iff_lt_mul hB]
          exact hidx
        have h4 : idx % B < B := Nat.mod_lt _ hB
        calc (idx / B) / n * B + idx % B < (idx / B) / n * B + B := by omega
          _ = ((idx / B) / n + 1) * B := by ring
          _ ≤ A * B := Nat.mul_le_mul_right B (by omega)
      rw [getD_flatten_blocks hsl hq (Nat.mod_lt _ hn)]
      have hdiv : (idx / B) / n * B + idx % B = idx / (n * B) * B + idx % B := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm B n]
      rw [hdiv]

/-! ## Size bounds for the budget -/

private theorem vsz_ofList_eq (l : List Val) : vsz (ofList l) = (l.map (fun x => vsz x + 1)).sum + 1 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [show ofList (x :: t) = Val.cons x (ofList t) from rfl, vsz_cons', ih,
      List.map_cons, List.sum_cons]
    ring

theorem sum_map_add_le (l : List Val) (L : ℕ) (h : ∀ x ∈ l, vsz x ≤ L) :
    (l.map (fun x => vsz x + 1)).sum ≤ l.length * (L + 1) := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have hx : vsz x ≤ L := h x (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ L := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [show (t.length + 1) * (L + 1) = t.length * (L + 1) + (L + 1) from by ring,
      Nat.add_comm (t.length * (L + 1)) (L + 1)]
    exact Nat.add_le_add (by omega : vsz x + 1 ≤ L + 1) ih'

/-- Tight bound: `vsz (ofList l) = Σ (vsz x + 1) + 1 ≤ l.length * (L+1) + 1`. -/
theorem vsz_ofList_le_tight {l : List Val} {L : ℕ} (h : ∀ x ∈ l, vsz x ≤ L) :
    vsz (ofList l) ≤ l.length * (L + 1) + 1 := by
  rw [vsz_ofList_eq]
  have h2 := sum_map_add_le l L h
  omega

theorem ppP_succ_le (A B m n L : ℕ) : A * B * (m + n + 1) + 1 ≤ 2 * ppMB A B m n L := by
  have h1 : A * B * (m + n + 1) ≤ ppMB A B m n L := le_ppMB (le_refl _)
  have h2 : 1 ≤ ppMB A B m n L := ppMB_pos A B m n L
  omega

theorem isz_le_ppMB {A B m n L i : ℕ} (hi : i ≤ A * B * (m + n + 1))
    (hP : 1 ≤ A * B * (m + n + 1)) : isz (i : ℤ) ≤ ppMB A B m n L := by
  rw [isz_nat_size]
  have h1 : i.size + 2 ≤ (A * B * (m + n + 1)).size + 2 :=
    Nat.add_le_add_right (Nat.size_le_size hi) 2
  have h2 : (A * B * (m + n + 1)).size + 2
      ≤ 2 * ((A * B * (m + n + 1)).size + 1) := by omega
  have h3 : 2 * ((A * B * (m + n + 1)).size + 1) ≤ ppMB A B m n L := by
    unfold ppMB
    have h4 : 2 ≤ A * B * (m + n + 1) + 1 := by omega
    have h5 : (A * B * (m + n + 1)).size + 1 ≤ L + (A * B * (m + n + 1)).size + 1 := by omega
    calc 2 * ((A * B * (m + n + 1)).size + 1)
        ≤ (A * B * (m + n + 1) + 1) * ((A * B * (m + n + 1)).size + 1) :=
          Nat.mul_le_mul_right _ h4
      _ ≤ (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1) :=
          Nat.mul_le_mul_left _ h5
      _ ≤ (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1)
            * ((A * B * (m + n + 1)).size + 1) := le_mul_succ _ _
  exact le_trans h1 (le_trans h2 h3)

theorem vsz_ofList_es_le {A B m n L : ℕ} {es : List Val} (hlen : es.length = A * m * B)
    (hsz : ∀ x ∈ es, vsz x ≤ L) (hmn : m ≤ m + n + 1) : vsz (ofList es) ≤ 2 * ppMB A B m n L := by
  have h1 : vsz (ofList es) ≤ A * m * B * (L + 1) + 1 := by
    have h := vsz_ofList_le_tight hsz
    rwa [hlen] at h
  have h3 : A * m * B ≤ A * B * (m + n + 1) := by
    have he : A * m * B = A * B * m := by ring
    rw [he]; exact Nat.mul_le_mul_left (A * B) hmn
  have h4 : A * m * B * (L + 1) ≤ A * B * (m + n + 1) * (L + 1) := Nat.mul_le_mul_right _ h3
  have h5 : A * B * (m + n + 1) * (L + 1) ≤ ppMB A B m n L := mul_L_le_ppMB (le_refl _)
  have h6 : 1 ≤ ppMB A B m n L := ppMB_pos A B m n L
  omega

theorem vsz_ofList_map_ofList_le {xs : List (List Val)} {n L : ℕ}
    (hlen : ∀ l ∈ xs, l.length = n) (hL : ∀ x ∈ xs.flatten, vsz x ≤ L) :
    vsz (ofList (xs.map ofList)) ≤ xs.length * (n * (L + 1) + 2) + 1 := by
  have h1 : ∀ x ∈ xs.map ofList, vsz x ≤ n * (L + 1) + 1 := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    have h2 : ∀ y ∈ l, vsz y ≤ L := fun y hy => hL y (List.mem_flatten.mpr ⟨l, hl, hy⟩)
    have h3 := vsz_ofList_le_tight h2
    rw [hlen l hl] at h3
    exact h3
  have h4 := vsz_ofList_le_tight h1
  rw [List.length_map] at h4
  exact h4

theorem vsz_ofList_map_ofList_le_ppMB {A B m n L : ℕ} {xs : List (List Val)}
    (hxs : xs.length = A * B) (hlen : ∀ l ∈ xs, l.length = n)
    (hL : ∀ x ∈ xs.flatten, vsz x ≤ L) :
    vsz (ofList (xs.map ofList)) ≤ 4 * ppMB A B m n L := by
  have h1 := vsz_ofList_map_ofList_le hlen hL
  rw [hxs] at h1
  have h2 : n * (L + 1) + 2 ≤ 3 * ((m + n + 1) * (L + 1)) := by
    have h3 : 2 * (L + 1) ≤ 2 * ((m + n + 1) * (L + 1)) := by
      calc 2 * (L + 1) ≤ 2 * (m + n + 1) * (L + 1) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 * ((m + n + 1) * (L + 1)) := by ring
    have h5 : n * (L + 1) ≤ (m + n + 1) * (L + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    calc n * (L + 1) + 2 ≤ n * (L + 1) + 2 * (L + 1) := by
          have h6 : 2 ≤ 2 * (L + 1) := by omega
          omega
      _ ≤ (m + n + 1) * (L + 1) + 2 * ((m + n + 1) * (L + 1)) := Nat.add_le_add h5 h3
      _ = 3 * ((m + n + 1) * (L + 1)) := by ring
  have h6 : A * B * (n * (L + 1) + 2) ≤ 3 * (A * B * (m + n + 1) * (L + 1)) := by
    calc A * B * (n * (L + 1) + 2) ≤ A * B * (3 * ((m + n + 1) * (L + 1))) :=
          Nat.mul_le_mul_left _ h2
      _ = 3 * (A * B * (m + n + 1) * (L + 1)) := by ring
  have h7 : A * B * (m + n + 1) * (L + 1) ≤ ppMB A B m n L := mul_L_le_ppMB (le_refl _)
  have h8 : 1 ≤ ppMB A B m n L := ppMB_pos A B m n L
  calc vsz (ofList (List.map ofList xs)) ≤ A * B * (n * (L + 1) + 2) + 1 := h1
    _ ≤ 3 * (A * B * (m + n + 1) * (L + 1)) + 1 := by
        exact Nat.add_le_add_right h6 1
    _ ≤ 3 * ppMB A B m n L + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left 3 h7) 1
    _ ≤ 3 * ppMB A B m n L + ppMB A B m n L := Nat.add_le_add_left h8 _
    _ = 4 * ppMB A B m n L := by ring

theorem mul_iszm_le_ppMB {A B m n L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (_hm : 1 ≤ m) (hn : 1 ≤ n) :
    (A * B + 1) * isz (m : ℤ) ≤ 4 * ppMB A B m n L := by
  have h1 : isz (m : ℤ) ≤ m + n + 1 := by
    rw [isz_nat_size]
    have h2 : m.size ≤ m := (Nat.size_le).mpr Nat.lt_two_pow_self
    omega
  have hAB : 1 ≤ A * B := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h3 : m + n + 1 ≤ A * B * (m + n + 1) := by
    calc m + n + 1 = 1 * (m + n + 1) := (Nat.one_mul _).symm
      _ ≤ A * B * (m + n + 1) := Nat.mul_le_mul_right _ hAB
  have h4 : (A * B + 1) * (m + n + 1) ≤ 2 * (A * B * (m + n + 1)) := by
    calc (A * B + 1) * (m + n + 1) = A * B * (m + n + 1) + (m + n + 1) := by ring
      _ ≤ A * B * (m + n + 1) + A * B * (m + n + 1) := Nat.add_le_add_left h3 _
      _ = 2 * (A * B * (m + n + 1)) := by ring
  have h5 : A * B * (m + n + 1) ≤ ppMB A B m n L := le_ppMB (le_refl _)
  have h6 : 1 ≤ ppMB A B m n L := ppMB_pos A B m n L
  calc (A * B + 1) * isz (m : ℤ) ≤ (A * B + 1) * (m + n + 1) := Nat.mul_le_mul_left _ h1
    _ ≤ 2 * (A * B * (m + n + 1)) := h4
    _ ≤ 2 * ppMB A B m n L := Nat.mul_le_mul_left 2 h5
    _ ≤ 4 * ppMB A B m n L := by omega

theorem mul_AB_Lmnm_le_ppMB {A B m n L : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    A * B * ((m + n + 1) * (L + 1) + 2) ≤ 3 * ppMB A B m n L := by
  have hmn : 1 ≤ m + n + 1 := by omega
  have hL1 : 1 ≤ L + 1 := by omega
  have h1 : (m + n + 1) * (L + 1) + 2 ≤ 2 * ((m + n + 1) * (L + 1)) := by
    have h2 : 2 ≤ (m + n + 1) * (L + 1) := by
      calc (2 : ℕ) = 2 * 1 := by ring
        _ ≤ (m + n + 1) * (L + 1) := Nat.mul_le_mul (by omega : 2 ≤ m + n + 1) hL1
    calc (m + n + 1) * (L + 1) + 2 ≤ (m + n + 1) * (L + 1) + (m + n + 1) * (L + 1) :=
          Nat.add_le_add_left h2 _
      _ = 2 * ((m + n + 1) * (L + 1)) := by ring
  have h3 : A * B * ((m + n + 1) * (L + 1) + 2) ≤ 2 * ((m + n + 1) * (L + 1)) * (A * B) := by
    calc A * B * ((m + n + 1) * (L + 1) + 2) ≤ A * B * (2 * ((m + n + 1) * (L + 1))) :=
          Nat.mul_le_mul_left _ h1
      _ = 2 * ((m + n + 1) * (L + 1)) * (A * B) := by ring
  have h4 : A * B * (m + n + 1) * (L + 1) ≤ ppMB A B m n L := mul_L_le_ppMB (le_refl _)
  have h5 : 1 ≤ ppMB A B m n L := ppMB_pos A B m n L
  calc A * B * ((m + n + 1) * (L + 1) + 2)
      ≤ A * B * (2 * ((m + n + 1) * (L + 1))) := Nat.mul_le_mul_left _ h1
    _ = 2 * (A * B * (m + n + 1) * (L + 1)) := by ring
    _ ≤ 2 * ppMB A B m n L := Nat.mul_le_mul_left 2 h4
    _ ≤ 3 * ppMB A B m n L := by omega

end Work.Resample
