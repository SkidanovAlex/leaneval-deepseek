import Submission.Work.PTCert.Checks.C1All

/-!
# PTCert — shared helper layer for the certificate-1 assembly (`Work.PTCert.cert1Final`)

This file collects, in one place, the objects and the small structural lemmas that the pieces of
`cert1Final` (symmetry, row tables, LDL data, class sums) all need:

* `cert1pv`, `cert1res`, `cert1SC` — the C1 value / residual tables and the denominator `2^80`;
* `allL_iff`, `allR_iff` — the meaning of the kernel `allL` / `allR` combinators;
* `cert1SymCond` — the body of `SymHyp cert1pv` as a standalone predicate;
* `ngE`'s values, the chunk lists `klList` / `tlList` and the flatten-indexing lemma
  `getD_flatten_of_le`, `classSumOK_iff`, `ldlDataOK_iff`.

Everything here is proved from the kernel theorems in `Submission.Work.PTCert.Checks.C1All`
(none of the big data definitions is unfolded by `decide`).
-/

/-!
## Recipes for the four families of pieces of certificate 1

`cert1Final` (in `cert1Final.lean`) assembles the C1 certificate from the following lemmas, each of
which is *only* about the kernel checks in `Submission.Work.PTCert.Checks.C1All`:

* `cert1Sym`  : `∀ r < 18, ∀ g < ngE r, cert1SymCond r g`.  Unfold `SymHyp`/`cert1SymCond` and the
  kernel check `symOK` (`KernelCert.lean`); the checks `C1K.sym_ok{r}_{j}` give, for every `g` of a
  contiguous chunk `[a, …, b]` of `[0, ngE r)`, the equality of the two `p8 valT` entries.  The chunks
  are `List.range`-shaped: `[0,1,…,n-1] = List.range n` (`decide +kernel`); `allL_range_iff` turns
  `allL (List.range n) p = true` into `∀ k < n, p k = true`, and `Nat.beq_eq` + `congrArg sv` finish.
  Useful facts: `ngE_vals` (the values `ngE r`), `symHyp_cert1pv_iff`.
* `cert1RowCheck` : the singleton `rowCheck` facts for `r < 18`, `t < 611`, needed by `RowTabSound`.
  Same recipe as `cert1Sym`: `C1K.rw_ok{r}_{j}` covers the chunk `[153j, 153j+153)` of `[0, 611)`
  (`rowCheck` is `allL` over the chunk), using `allL_range_iff` and the `rfl`-facts
  `olTs.getD r (NT.leaf 0) = olT{r}`, `D1.rowTs.getD r (NT.leaf 0) = rowT{r}`.
* `cert1Ldl{k}` : `LdlData D1.rowTs k`.  Take `Cs := Cs{k}`, `Ws := Ws{k}`,
  `segs := [the segment lists of C1K.ldl_ok{k}_{j}, in order]` (extract them mechanically from the
  `Checks/C1/L{k}_*.lean` sources), and `accs` the function `j ↦ acc{k}_{j}` (junk `[]` beyond the last
  index).  Then `segs.flatten = List.range (nK k)` and `accs 0 = List.replicate 4 (List.replicate (nK k) 0)`
  are small `decide +kernel` facts (the `acc{k}_0` is the zero accumulator), the chain is the
  `ldl_ok` theorems (rewrite `segs.getD j []` and `accs j` by `rfl`, e.g. with `interval_cases j`), and
  the shape clause comes from `C1K.ldldata_ok{k}` through `ldlDataOK_iff`.
* `cert1ClassSum` : unfold `C1K.cs_ok{j}` with `classSumOK_iff` (`kl := kl{j}`, `tl := tl{j}`,
  `c0 := 500 j`), use `foldr_add_eq_sum` to pass to `.map … |>.sum`, and locate the chunk of a class
  `cl < 7229` with `klist_chunk_lt` / `klist_chunk_ge` (and the `tlist` variants).  `cl < 7000`: the
  chunk is `cl / 500` and the offset `cl % 500` (`Nat.div_add_mod`); `cl ≥ 7000`: chunk `14`, offset
  `cl - 7000`.  All chunks `0..13` have length `500` (`klList14_getD_len`), the last has length `229`.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1
open scoped BigOperators

noncomputable section

/-- The value table of certificate 1 (C1): `key 2048 r + g ↦ P(x₀_r, group g)`. -/
def cert1pv : ℕ → ℤ := fun k => sv (p8 valT k)

/-- The residual table of certificate 1. -/
def cert1res : ℕ → ℤ := fun c => sv (p8 resT c)

/-- The common denominator `2^80` of certificate 1. -/
def cert1SC : ℤ := 1208925819614629174706176

/-- `sv` is injective. -/
lemma sv_inj {a b : ℕ} (h : sv a = sv b) : a = b := by
  have := congrArg (fun z : ℤ => z + (OFF : ℤ)) h
  simpa [sv] using this

@[simp] lemma cert1pv_apply (k : ℕ) : cert1pv k = sv (p8 valT k) := rfl

@[simp] lemma cert1res_apply (c : ℕ) : cert1res c = sv (p8 resT c) := rfl

lemma bool_and_iff {a b : Bool} : (a && b) = true ↔ a = true ∧ b = true :=
  iff_of_eq (Bool.and_eq_true a b)

/-- `allL l p = true` means `p` holds at every element of `l`. -/
lemma allL_iff {l : List ℕ} {p : ℕ → Bool} : allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allL]
  | cons a t ih =>
    rw [show allL (a :: t) p = (p a && allL t p) from rfl, bool_and_iff, ih]
    simp

/-- `allR n p = true` means `p k` for all `k < n`. -/
lemma allR_iff {n : ℕ} {p : ℕ → Bool} : allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
    rw [show allR (n + 1) p = (p n && allR n p) from rfl, bool_and_iff, ih]
    constructor
    · rintro ⟨hp, h⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h k hk
      · exact hp
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

/-- `allL` on `List.range n` is the "for all `k < n`" quantifier. -/
lemma allL_range_iff {n : ℕ} {p : ℕ → Bool} :
    allL (List.range n) p = true ↔ ∀ k < n, p k = true := by
  rw [allL_iff]
  constructor
  · intro h k hk; exact h k (List.mem_range.mpr hk)
  · intro h a ha; exact h a (List.mem_range.mp ha)

/-- Every element of a segment chunk really is a row of the row table: the `j`-th entry of
`segs.getD j []` is its index. -/
lemma cert1SC_pos : 0 < cert1SC := by decide +kernel

/-! ## The values of `ngE` (the group counts of the rows) -/

lemma ngE_vals :
    ngE 0 = 18 ∧ ngE 1 = 399 ∧ ngE 2 = 399 ∧ ngE 3 = 215 ∧ ngE 4 = 248 ∧ ngE 5 = 1332 ∧
    ngE 6 = 682 ∧ ngE 7 = 399 ∧ ngE 8 = 399 ∧ ngE 9 = 399 ∧ ngE 10 = 399 ∧ ngE 11 = 1332 ∧
    ngE 12 = 1332 ∧ ngE 13 = 1332 ∧ ngE 14 = 1332 ∧ ngE 15 = 712 ∧ ngE 16 = 682 ∧
    ngE 17 = 1621 := by decide +kernel

/-! ## The body of `SymHyp cert1pv` -/

/-- The symmetry condition of the key `(r, g)`: the transpose consistency of the value table. -/
def cert1SymCond (r g : ℕ) : Prop :=
  cert1pv (keyOf r g) =
    cert1pv (keyOf (rinfo ((em (grepE r g) - 1) / 32) / 128)
      (labE (rinfo ((em (grepE r g) - 1) / 32) / 128)
        (actC cmT (piIT.get (rinfo ((em (grepE r g) - 1) / 32) % 128))
          (actC cmT (ntab ((em (grepE r g) - 1) % 32)) (x0c r)))))

/-- `SymHyp cert1pv` is exactly the pointwise condition `cert1SymCond`. -/
lemma symHyp_cert1pv_iff : SymHyp cert1pv ↔ ∀ r < 18, ∀ g < ngE r, cert1SymCond r g :=
  Iff.rfl

/-! ## The two class-partitions and their chunk structure -/

/-- The classes of certificate 1, grouped by the kernel check chunks. -/
def klList : List (List (List ℕ)) := [kl0, kl1, kl2, kl3, kl4, kl5, kl6, kl7, kl8, kl9, kl10, kl11, kl12, kl13, kl14]

/-- The target-pair lists of certificate 1, grouped by the kernel check chunks. -/
def tlList : List (List (List ℕ)) := [tl0, tl1, tl2, tl3, tl4, tl5, tl6, tl7, tl8, tl9, tl10, tl11, tl12, tl13, tl14]

lemma klist_eq_flatten : klist = klList.flatten := by
  simp only [klist, klList, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

lemma tlist_eq_flatten : tlist = tlList.flatten := by
  simp only [tlist, tlList, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

lemma klList_len (j : ℕ) (hj : j < 14) : (klList.getD j []).length = 500 := by
  interval_cases j <;> decide +kernel

lemma tlList_len (j : ℕ) (hj : j < 14) : (tlList.getD j []).length = 500 := by
  interval_cases j <;> decide +kernel

lemma klList_len_last : (klList.getD 14 []).length = 229 := by decide +kernel

lemma tlList_len_last : (tlList.getD 14 []).length = 229 := by decide +kernel

/-- **Indexing into a concatenation of equal-width chunks**: if the first `j+1` chunks of `Ls` all
have length `w`, then the `(w * j + i)`-th entry of the flatten lies in the `j`-th chunk. -/
lemma getD_flatten_of_le {α : Type*} (a : α) (w : ℕ) :
    ∀ (Ls : List (List α)) (j i : ℕ),
      (∀ j' ≤ j, j' < Ls.length → (Ls.getD j' []).length = w) → i < w →
      Ls.flatten.getD (w * j + i) a = (Ls.getD j []).getD i a := by
  intro Ls
  induction Ls with
  | nil =>
    intro j i _ hi
    simp
  | cons L Ls ih =>
    intro j i hlen hi
    have hL : L.length = w := hlen 0 (Nat.zero_le j) (by simp)
    cases j with
    | zero =>
      have : ((L :: Ls).flatten).getD (w * 0 + i) a = L.getD i a := by
        have hmul0 : w * 0 + i = i := by ring
        rw [List.flatten_cons, hmul0,
          List.getD_append L Ls.flatten a i (by omega)]
      rw [this, List.getD_cons_zero]
    | succ j =>
      have hLw : L.length ≤ w * (j + 1) + i := by
        rw [hL]; nlinarith [Nat.zero_le j, Nat.zero_le i]
      have hflat : ((L :: Ls).flatten).getD (w * (j + 1) + i) a
          = Ls.flatten.getD (w * j + i) a := by
        rw [List.flatten_cons]
        rw [List.getD_append_right L Ls.flatten a (w * (j + 1) + i) hLw]
        congr 1
        rw [hL, Nat.mul_succ, Nat.add_assoc, Nat.add_comm w i, ← Nat.add_assoc,
          Nat.add_sub_cancel]
      rw [hflat, List.getD_cons_succ]
      refine ih j i ?_ hi
      intro j' hj' hlt
      have h1 : ((L :: Ls).getD (j' + 1) []).length = w :=
        hlen (j' + 1) (by omega) (by simpa using hlt)
      simpa using h1

/-- `List.headD` is the `0`-th `getD`. -/
lemma headD_eq_getD {α : Type*} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

/-- `(l.drop n).getD m a = l.getD (n + m) a`. -/
lemma getD_drop {α : Type*} (l : List α) (a : α) :
    ∀ n m : ℕ, (l.drop n).getD m a = l.getD (n + m) a := by
  intro n
  induction n generalizing l with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    cases l with
    | nil => simp
    | cons x xs =>
      rw [List.drop_succ_cons, ih xs m]
      rw [show n + 1 + m = (n + m) + 1 by omega, List.getD_cons_succ]

/-- A right fold adding the values of `f` is the sum of the mapped list. -/
lemma foldr_add_eq_sum (l : List ℕ) (f : ℕ → ℤ) :
    l.foldr (fun k acc => acc + f k) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.foldr_cons, ih, List.map_cons, List.sum_cons, add_comm]

/-- The `14` class chunks of equal width `500`. -/
def klList14 : List (List (List ℕ)) := [kl0, kl1, kl2, kl3, kl4, kl5, kl6, kl7, kl8, kl9, kl10, kl11, kl12, kl13]

/-- The `14` target-pair chunks of equal width `500`. -/
def tlList14 : List (List (List ℕ)) := [tl0, tl1, tl2, tl3, tl4, tl5, tl6, tl7, tl8, tl9, tl10, tl11, tl12, tl13]

lemma klList14_mem_len : ∀ L ∈ klList14, L.length = 500 := by
  intro L hL
  simp only [klList14, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

lemma tlList14_mem_len : ∀ L ∈ tlList14, L.length = 500 := by
  intro L hL
  simp only [tlList14, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

lemma klList14_getD_len (j : ℕ) (hj : j < 14) : (klList14.getD j []).length = 500 := by
  interval_cases j <;> decide +kernel

lemma tlList14_getD_len (j : ℕ) (hj : j < 14) : (tlList14.getD j []).length = 500 := by
  interval_cases j <;> decide +kernel

/-- The length of the flatten of a list of chunks of common width. -/
lemma length_flatten_of_forall {α : Type*} (w : ℕ) (Ls : List (List α))
    (h : ∀ L ∈ Ls, L.length = w) : Ls.flatten.length = w * Ls.length := by
  induction Ls with
  | nil => simp
  | cons L Ls ih =>
    rw [List.flatten_cons, List.length_append, ih (fun L' hL' => h L' (by simp [hL'])),
      List.length_cons, h L (by simp), Nat.mul_succ]
    ring

lemma klList14_flatten_len : klList14.flatten.length = 7000 := by
  rw [length_flatten_of_forall 500 klList14 klList14_mem_len]
  decide +kernel

lemma tlList14_flatten_len : tlList14.flatten.length = 7000 := by
  rw [length_flatten_of_forall 500 tlList14 tlList14_mem_len]
  decide +kernel

lemma klist_eq : klist = klList14.flatten ++ kl14 := by
  simp only [klist, klList14, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

lemma tlist_eq : tlist = tlList14.flatten ++ tl14 := by
  simp only [tlist, tlList14, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

/-- The chunk decomposition of a class index in the first `14` chunks. -/
lemma klist_chunk_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    klist.getD (500 * j + i) [] = (klList14.getD j []).getD i [] := by
  rw [klist_eq, List.getD_append klList14.flatten kl14 [] (500 * j + i) (by
    rw [klList14_flatten_len]; nlinarith [Nat.zero_le i, Nat.zero_le j])]
  exact getD_flatten_of_le [] 500 klList14 j i (fun j' _ _ => klList14_getD_len j' (by omega)) hi

lemma tlist_chunk_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    tlist.getD (500 * j + i) [] = (tlList14.getD j []).getD i [] := by
  rw [tlist_eq, List.getD_append tlList14.flatten tl14 [] (500 * j + i) (by
    rw [tlList14_flatten_len]; nlinarith [Nat.zero_le i, Nat.zero_le j])]
  exact getD_flatten_of_le [] 500 tlList14 j i (fun j' _ _ => tlList14_getD_len j' (by omega)) hi

/-- The chunk decomposition of a class index in the last chunk. -/
lemma klist_chunk_ge (i : ℕ) (hi : i < 229) : klist.getD (7000 + i) [] = kl14.getD i [] := by
  have hlen : klList14.flatten.length ≤ 7000 + i := by rw [klList14_flatten_len]; omega
  rw [klist_eq, List.getD_append_right klList14.flatten kl14 [] (7000 + i) hlen]
  rw [klList14_flatten_len, show 7000 + i - 7000 = i by omega]

lemma tlist_chunk_ge (i : ℕ) (hi : i < 229) : tlist.getD (7000 + i) [] = tl14.getD i [] := by
  have hlen : tlList14.flatten.length ≤ 7000 + i := by rw [tlList14_flatten_len]; omega
  rw [tlist_eq, List.getD_append_right tlList14.flatten tl14 [] (7000 + i) hlen]
  rw [tlList14_flatten_len, show 7000 + i - 7000 = i by omega]

/-- Unfolding `classSumOK` at a cons. -/
lemma classSumOK_cons (ks : List ℕ) (krest : List (List ℕ)) (tl : List (List ℕ)) (c0 : ℕ) :
    classSumOK valT multT resT qC1 20 cert1SC (ks :: krest) tl c0 =
      (decide (20 * (ks.foldr (fun k acc => acc + (multE k : ℤ) * cert1pv k) 0)
        - cert1SC * ((tl.headD []).foldr (fun p acc => acc + qC1 p) 0) + cert1res c0 = 0)
        && classSumOK valT multT resT qC1 20 cert1SC krest (tl.drop 1) (c0 + 1)) := rfl

/-- Unfolding `classSumOK` at `nil`. -/
lemma classSumOK_nil (tl : List (List ℕ)) (c0 : ℕ) :
    classSumOK valT multT resT qC1 20 cert1SC [] tl c0 = true := rfl

/-- The weighted key sum of a class. -/
def cert1u (cl : ℕ) : ℤ := ((klist.getD cl []).map (fun k => (multE k : ℤ) * cert1pv k)).sum

/-- The target-pair sum of a class. -/
def cert1tq (cl : ℕ) : ℤ := ((tlist.getD cl []).map qC1).sum

lemma cert1u_chunk_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    cert1u (500 * j + i)
      = (((klList14.getD j []).getD i []).map (fun k => (multE k : ℤ) * cert1pv k)).sum := by
  rw [cert1u, klist_chunk_lt j i hj hi]

lemma cert1u_chunk_ge (i : ℕ) (hi : i < 229) :
    cert1u (7000 + i) = ((kl14.getD i []).map (fun k => (multE k : ℤ) * cert1pv k)).sum := by
  rw [cert1u, klist_chunk_ge i hi]

lemma cert1tq_chunk_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    cert1tq (500 * j + i) = (((tlList14.getD j []).getD i []).map qC1).sum := by
  rw [cert1tq, tlist_chunk_lt j i hj hi]

lemma cert1tq_chunk_ge (i : ℕ) (hi : i < 229) :
    cert1tq (7000 + i) = ((tl14.getD i []).map qC1).sum := by
  rw [cert1tq, tlist_chunk_ge i hi]

/-- `classSumOK` says precisely: for every class of the chunk, `20 * u - 2^80 * tq + res = 0`. -/
lemma classSumOK_iff (kl tl : List (List ℕ)) (c0 : ℕ) :
    classSumOK valT multT resT qC1 20 cert1SC kl tl c0 = true ↔
      ∀ i < kl.length,
        20 * ((kl.getD i []).foldr (fun k acc => acc + (multE k : ℤ) * cert1pv k) 0)
          - cert1SC * ((tl.getD i []).foldr (fun p acc => acc + qC1 p) 0) + cert1res (c0 + i) = 0 := by
  induction kl generalizing tl c0 with
  | nil => simp [classSumOK]
  | cons ks krest ih =>
    rw [classSumOK_cons, bool_and_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      rcases i with _ | j
      · rw [headD_eq_getD] at h0
        simpa using h0
      · have hj : j < krest.length := by simpa using hi
        have h := (ih (tl.drop 1) (c0 + 1)).mp h1 j hj
        rw [getD_drop tl [] 1 j, Nat.add_assoc,
          show (1 : ℕ) + j = j + 1 by omega] at h
        exact h
    · intro h
      refine ⟨?_, ?_⟩
      · have hh := h 0 (by simp)
        rw [headD_eq_getD]
        simpa using hh
      · exact (ih (tl.drop 1) (c0 + 1)).mpr (fun j hj => by
          rw [getD_drop tl [] 1 j, Nat.add_assoc,
            show (1 : ℕ) + j = j + 1 by omega]
          exact h (j + 1) (by simpa using hj))

/-! ## The LDL check -/

/-- `ldlDataOK` says precisely: four ψ-blocks, `n` weights (positive) and `n` lower-triangular
factor rows. -/
lemma ldlDataOK_iff (Cs : List (List (List ℤ))) (Ws : List (List ℤ)) (n : ℕ) :
    ldlDataOK Cs Ws n = true ↔
      ∀ ψ < 4, (Ws.getD ψ []).length = n ∧ (Cs.getD ψ []).length = n ∧
        ∀ i < n, 0 < (Ws.getD ψ []).getD i 1 ∧ ((Cs.getD ψ []).getD i []).length ≤ i + 1 := by
  unfold ldlDataOK
  rw [allR_iff]
  constructor
  · intro h ψ hψ
    have h' := h ψ hψ
    rw [bool_and_iff, bool_and_iff, Nat.beq_eq, Nat.beq_eq, allR_iff] at h'
    refine ⟨h'.1.1, h'.1.2, fun i hi => ?_⟩
    have hi' := h'.2 i hi
    simpa [bool_and_iff, decide_eq_true_iff, Nat.ble_eq] using hi'
  · intro h ψ hψ
    have h' := h ψ hψ
    rw [bool_and_iff, bool_and_iff, Nat.beq_eq, Nat.beq_eq, allR_iff]
    refine ⟨⟨h'.1, h'.2.1⟩, fun i hi => ?_⟩
    have hi' := h'.2.2 i hi
    simpa [bool_and_iff, decide_eq_true_iff, Nat.ble_eq] using hi'

end

end Work.PTCert
