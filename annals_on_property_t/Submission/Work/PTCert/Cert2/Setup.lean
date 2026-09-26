import Mathlib
import Submission.Work.PTCert.Checks.C2All
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.targetExpansions
import Submission.Work.PTCert.targetInvariance

/-!
# PTCert — set-up for the assembly of the `C2` certificate (`Work.PTCert.cert2Final`)

`cert2Final` turns the kernel-checked data of the second certificate (`q = qC2`, `μ = 7/25`,
common denominator `200`, scaling constant `SC = 2 ^ 80`, residual bound `(23/100)·2^80·200`)
into `SAut5Adj2OpCert`, i.e.  `∃ μ > 0, Adj₅ + 2·Op₅ − μ·Δ₅ ∈ Σ²`.

The assembly instantiates the semantic Props of `Glue3.lean`
(`PsdAssembly`, `RowTabSound`, `FinalStep`, `ClassSem`, `KleinSem`) with
* the value table `valZ`, the residual table `resZ` and the target table `qZ` below,
* the row tables `D2.rowTs`,
and discharges their *data* hypotheses from the kernel checks of `Checks/C2/` (namespace
`Submission.PTCert.C2K`).

## The pieces

* `symHypC2` — `SymHyp valZ`, from `sym_ok{r}_{j}` (`symOK` over consecutive chunks of the
  group keys `g < ngE r`).  `ngE r = ngL.getD r 0 = [18,399,399,215,248,1332,682,399,399,399,
  399,1332,1332,1332,1332,712,682,1621]`, and the chunks are

  | row | chunks `(lo, len)` |
  |-----|--------------------|
  | 0 | (0,18) |
  | 1,2 | (0,399) |
  | 3 | (0,215) |
  | 4 | (0,248) |
  | 5 | (0,700), (700,632) |
  | 6 | (0,682) |
  | 7,8,9,10 | (0,399) |
  | 11,12,13,14 | (0,700), (700,632) |
  | 15 | (0,700), (700,12) |
  | 16 | (0,682) |
  | 17 | (0,700), (700,700), (1400,221) |

  `SymHyp valZ` is the `p8`-equality produced by `symOK` transported along `sv`
  (`Nat.beq_eq`, `congrArg sv`); remember `em`, `rinfo`, `grepE`, `labE`, `keyOf`, `x0c`,
  `ntab` are the `G`-level names of exactly the expressions occurring in `symOK`.

* `rowCheckC2` — the singleton `rowCheck`s, from `rw_ok{r}_{j}` (`rowCheck valT olT{r} rowT{r} r`
  over chunks of `t < 611`: the four chunks `[0,153)`, `[153,306)`, `[306,459)`, `[459,611)`,
  each row).  Feeding these to the hypothesis `RowTabSound` gives `RowTabHyp valZ rowTs`.
  Note `olTs.getD r (NT.leaf 0)` and `rowTs.getD r (NT.leaf 0)` are definitionally `olT{r}`
  and `rowT{r}`.

* `ldlDataC2` — `∀ k ≤ 4, LdlData rowTs k`, from `ldldata_ok{k}` (shape/positivity clauses,
  with `nK k = (ksL.getD k []).length = 161, 88, 59, 27, 6` for `k = 0..4`) and the chains
  `ldl_ok{k}_{j}` (`ldlSeg … Cs{k} Ws{k} segs_j acc{k}_j = some acc{k}_{j+1}`).  Take
  `Cs := Cs{k}`, `Ws := Ws{k}`, `segs` the list of the consecutive index segments of the
  chain **in the order of the checks** (they flatten to `List.range (nK k)`), and
  `accs j :=` the `j`-th accumulator witness (`acc{k}_0, acc{k}_1, …`, by a `match` on `j`).
  Then `segs.getD j []` and `accs j` are definitionally the literals of `ldl_ok{k}_{j}`, so
  that check can be used directly (after `interval_cases j`).

  Number of segments: `k = 0`: 137, `k = 1`: 24, `k = 2`: 8, `k = 3`: 2, `k = 4`: 1.  The
  segment lists are, e.g. for `k = 0`, `[0,1,2],[3,4],…,[13],[14],…,[135],[136,137],…,
  [153,…,160]`; the `accs` witnesses for `k = 0` are `acc0_0 … acc0_137`.

* `classEqC2` — the per-class coefficient identity of `FinalStep`, from `cs_ok{j}`
  (`classSumOK valT multT resT qZ 200 (2^80) kl{j} tl{j} (500*j)`, `j < 15`).  Unfolding
  `classSumOK` (a `List.rec` over `kl{j}` consuming `tl{j}` in lockstep) gives, for each
  `i < (kl{j}).length`, `200 · Σ_{k ∈ kl{j}[i]} multE k · valZ k − 2^80 · Σ_{p ∈ tl{j}[i]} qZ p
  + resZ (500*j+i) = 0`; `List.foldr (fun k acc => acc + f k) 0` is `(List.map f).sum`.
  Since `klist = kl0 ++ (kl1 ++ … ++ (kl14 ++ []))` **by definition** and `(kl{j}).length = 500`
  for `j ≤ 13`, `(kl14).length = 229` (`tl{j}` likewise), a class `cl < ncls = 7229` is
  `500*j + i` with `j = cl/500`, `i = cl%500`, and `klist.getD cl [] = (kl j).getD i []`,
  `tlist.getD cl [] = (tl j).getD i []` (split the nested `++` with `List.getD_append` /
  `List.getD_append_right` and the `decide +kernel`-checked chunk lengths).

* `resC2` — residual symmetry (`ressym_ok : resSymOK resT iclT (List.range 7229) = true`),
  `Σ res = 0` and the absorption bound
  (`resbound_ok : resBoundOK resT (List.range 7229) resBound = true` with
  `resBound = 55610587702272942036484096 = (23/100)·2^80·200`; convert the `List.foldr` over
  `List.range 7229` into a `Finset.sum` over `Finset.range ncls`).

* `qTableC2` — the table `qT` agrees with `qC2` on all `p < 6561`: the checks
  `q_ok{j} : qTabOK qT qC2 (List.range' (81*j) 81) = true` for `j < 81` give
  `∀ p ∈ List.range' (81*j) 81, qZ p = qC2 p`, and every `p < 6561` lies in the chunk
  `j = p/81`.  Hence `targetSum qZ 200 = targetSum qC2 200` (`Finset.sum_congr` over
  `Finset.range 6561`).

## Reusable facts (`allL`/`allR`)

`allL`, `allR`, `allIdx` are the kernel recursors of `KernelShared.lean`; their plain
meanings are the lemmas below.  A kernel check over a chunk `[lo, lo+len)` is turned into a
statement about `List.range' lo len` with `allL_range'_of_allL`, whose list-equality
hypothesis is closed and small — prove it with `by decide +kernel` (it is a comparison of
numerals, **not** a re-run of the check):

```
have h := allL_range'_of_allL sym_ok17_1 (lo := 700) (n := 700) (by decide +kernel)
-- h : ∀ i < 700, P (700 + i) = true
```

(the list argument of `allL_range'_of_allL` is inferred from the check theorem, so the chunk
never has to be written out).  For a chunk starting at `0` use `allL_range_of_allL` with
`List.range n`.
-/

set_option autoImplicit false
set_option maxRecDepth 400000

noncomputable section

namespace Work.PTCert.Cert2

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D2
open scoped BigOperators

/-- The value table of the `C2` certificate: `valZ k` is the (signed) integer attached to the
key `k = 2048 r + g`. -/
def valZ : ℕ → ℤ := fun k => sv (p8 valT k)

/-- The residual table of the `C2` certificate. -/
def resZ : ℕ → ℤ := fun c => sv (p8 resT c)

/-- The verified target table of the `C2` certificate. -/
def qZ : ℕ → ℤ := fun p => sv (p8 qT p)

/-- The common denominator of the `C2` certificate. -/
def denZ : ℤ := 200

/-- The scaling constant `2 ^ 80` of the `C2` certificate. -/
def scZ : ℤ := 1208925819614629174706176


lemma denZ_pos : 0 < denZ := by norm_num [denZ]

lemma scZ_pos : 0 < scZ := by norm_num [scZ]

/-! ## Soundness of the kernel recursors -/

lemma allL_eq_true (l : List ℕ) (p : ℕ → Bool) :
    allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allL]
  | cons a l ih =>
    rw [show allL (a :: l) p = (p a && allL l p) from rfl, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h1
      · exact h2 b hb
    · intro h
      exact ⟨h a (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

lemma allR_eq_true (n : ℕ) (p : ℕ → Bool) :
    allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
    rw [show allR (n + 1) p = (p n && allR n p) from rfl, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

lemma allIdx_eq_true (l : List ℕ) (p : ℕ → ℕ → Bool) (i0 : ℕ) :
    allIdx l p i0 = true ↔ ∀ j < l.length, p (i0 + j) (l.getD j 0) = true := by
  induction l generalizing i0 with
  | nil => simp [allIdx]
  | cons a l ih =>
    rw [show allIdx (a :: l) p i0 = (p i0 a && allIdx l p (i0 + 1)) from rfl,
      Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases j with _ | j
      · simpa using h1
      · have hj' : j < l.length := by simpa using hj
        have h := h2 j hj'
        rw [List.getD_cons_succ, show i0 + (j + 1) = i0 + 1 + j from by omega]
        exact h
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
      have h2 := h (j + 1) (by simpa using hj)
      rw [show i0 + (j + 1) = i0 + 1 + j from by omega, List.getD_cons_succ] at h2
      exact h2

lemma allL_of_mem {l : List ℕ} {p : ℕ → Bool} (h : allL l p = true) {a : ℕ} (ha : a ∈ l) :
    p a = true := (allL_eq_true l p).mp h a ha

lemma allR_of_lt {n : ℕ} {p : ℕ → Bool} (h : allR n p = true) {k : ℕ} (hk : k < n) :
    p k = true := (allR_eq_true n p).mp h k hk



/-! ## List bookkeeping (self-contained copies of the standard chunk lemmas) -/

/-- `sv` is injective. -/
lemma sv_inj {a b : ℕ} (h : sv a = sv b) : a = b := by
  have := congrArg (fun z : ℤ => z + (OFF : ℤ)) h
  simpa [sv] using this

lemma headD_eq_getD {α : Type*} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

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

/-- The first `14` class chunks of the certificate, each of width `500`. -/
def klChunks : List (List (List ℕ)) :=
  [kl0, kl1, kl2, kl3, kl4, kl5, kl6, kl7, kl8, kl9, kl10, kl11, kl12, kl13]

/-- The first `14` target-pair chunks, each of width `500`. -/
def tlChunks : List (List (List ℕ)) :=
  [tl0, tl1, tl2, tl3, tl4, tl5, tl6, tl7, tl8, tl9, tl10, tl11, tl12, tl13]

lemma klist_split : klist = klChunks.flatten ++ kl14 := by
  simp only [klist, klChunks, List.flatten_cons, List.flatten_nil, List.append_assoc,
    List.append_nil]

lemma tlist_split : tlist = tlChunks.flatten ++ tl14 := by
  simp only [tlist, tlChunks, List.flatten_cons, List.flatten_nil, List.append_assoc,
    List.append_nil]

lemma klChunks_getD_len (j : ℕ) (hj : j < 14) : (klChunks.getD j []).length = 500 := by
  interval_cases j <;> decide +kernel

lemma tlChunks_getD_len (j : ℕ) (hj : j < 14) : (tlChunks.getD j []).length = 500 := by
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

lemma klChunks_mem_len : ∀ L ∈ klChunks, L.length = 500 := by
  intro L hL
  simp only [klChunks, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

lemma tlChunks_mem_len : ∀ L ∈ tlChunks, L.length = 500 := by
  intro L hL
  simp only [tlChunks, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

lemma klChunks_flatten_len : klChunks.flatten.length = 7000 := by
  rw [length_flatten_of_forall 500 klChunks klChunks_mem_len]
  decide +kernel

lemma tlChunks_flatten_len : tlChunks.flatten.length = 7000 := by
  rw [length_flatten_of_forall 500 tlChunks tlChunks_mem_len]
  decide +kernel

/-- **Indexing into a concatenation of equal-width chunks**: if the first `j+1` chunks of `Ls`
all have length `w`, then the `(w * j + i)`-th entry of the flatten lies in the `j`-th chunk. -/
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

/-- The chunk decomposition of a class index in the first `14` chunks. -/
lemma klist_chunk_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    klist.getD (500 * j + i) [] = (klChunks.getD j []).getD i [] := by
  rw [klist_split, List.getD_append klChunks.flatten kl14 [] (500 * j + i) (by
    rw [klChunks_flatten_len]; nlinarith [Nat.zero_le i, Nat.zero_le j])]
  exact getD_flatten_of_le [] 500 klChunks j i (fun j' _ _ => klChunks_getD_len j' (by omega)) hi

lemma tlist_chunk_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    tlist.getD (500 * j + i) [] = (tlChunks.getD j []).getD i [] := by
  rw [tlist_split, List.getD_append tlChunks.flatten tl14 [] (500 * j + i) (by
    rw [tlChunks_flatten_len]; nlinarith [Nat.zero_le i, Nat.zero_le j])]
  exact getD_flatten_of_le [] 500 tlChunks j i (fun j' _ _ => tlChunks_getD_len j' (by omega)) hi

/-- The chunk decomposition of a class index in the last chunk. -/
lemma klist_chunk_ge (i : ℕ) (hi : i < 229) : klist.getD (7000 + i) [] = kl14.getD i [] := by
  have hlen : klChunks.flatten.length ≤ 7000 + i := by rw [klChunks_flatten_len]; omega
  rw [klist_split, List.getD_append_right klChunks.flatten kl14 [] (7000 + i) hlen]
  rw [klChunks_flatten_len, show 7000 + i - 7000 = i by omega]

lemma tlist_chunk_ge (i : ℕ) (hi : i < 229) : tlist.getD (7000 + i) [] = tl14.getD i [] := by
  have hlen : tlChunks.flatten.length ≤ 7000 + i := by rw [tlChunks_flatten_len]; omega
  rw [tlist_split, List.getD_append_right tlChunks.flatten tl14 [] (7000 + i) hlen]
  rw [tlChunks_flatten_len, show 7000 + i - 7000 = i by omega]

/-! ## Soundness of the per-certificate checks -/

/-- Unfolding `classSumOK` at a cons (C2 instance). -/
lemma classSumOK_cons_c2 (ks : List ℕ) (krest : List (List ℕ)) (tl : List (List ℕ)) (c0 : ℕ) :
    classSumOK valT multT resT (fun p => sv (p8 qT p)) denZ scZ (ks :: krest) tl c0 =
      (decide (denZ * (ks.foldr (fun k acc => acc + (multE k : ℤ) * sv (p8 valT k)) 0)
        - scZ * ((tl.headD []).foldr (fun p acc => acc + sv (p8 qT p)) 0) + sv (p8 resT c0) = 0)
        && classSumOK valT multT resT (fun p => sv (p8 qT p)) denZ scZ krest (tl.drop 1) (c0 + 1)) :=
  rfl

/-- **Class sums of the `C2` certificate.**  If the kernel check `classSumOK` passes on the chunk
`kl` / `tl` starting at class `c0`, then every class `c0 + i` of the chunk satisfies the exact
coefficient identity of `FinalStep`. -/
lemma classSumOK_iff_c2 (kl tl : List (List ℕ)) (c0 : ℕ) :
    classSumOK valT multT resT (fun p => sv (p8 qT p)) denZ scZ kl tl c0 = true ↔
      ∀ i < kl.length,
        denZ * ((kl.getD i []).foldr (fun k acc => acc + (multE k : ℤ) * sv (p8 valT k)) 0)
          - scZ * ((tl.getD i []).foldr (fun p acc => acc + sv (p8 qT p)) 0)
          + sv (p8 resT (c0 + i)) = 0 := by
  induction kl generalizing tl c0 with
  | nil => simp [classSumOK]
  | cons ks krest ih =>
    rw [classSumOK_cons_c2, Bool.and_eq_true, decide_eq_true_iff, ih]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      rcases i with _ | j
      · rw [headD_eq_getD] at h0
        simpa using h0
      · have hj : j < krest.length := by simpa using hi
        have h := h1 j hj
        rw [getD_drop tl [] 1 j, Nat.add_assoc,
          show (1 : ℕ) + j = j + 1 by omega] at h
        simpa using h
    · intro h
      refine ⟨?_, ?_⟩
      · have hh := h 0 (by simp)
        rw [headD_eq_getD]
        simpa using hh
      · intro j hj
        have hh := h (j + 1) (by simpa using hj)
        rw [getD_drop tl [] 1 j, show (1 : ℕ) + j = j + 1 by omega]
        rw [show c0 + (j + 1) = c0 + 1 + j by omega] at hh
        simpa using hh

/-- The meaning of the residual symmetry check. -/
lemma resSymOK_iff (cs : List ℕ) :
    resSymOK resT iclT cs = true ↔
      ∀ c ∈ cs, resZ (icls c) = resZ c ∧ icls (icls c) = c := by
  unfold resSymOK
  rw [allL_eq_true]
  constructor
  · intro h c hc
    have h' := h c hc
    rw [Bool.and_eq_true] at h'
    have h1 : p8 resT (icls c) = p8 resT c := by
      have hh := h'.1
      rw [Nat.beq_eq] at hh
      exact hh
    have h2 : icls (icls c) = c := by
      have hh := h'.2
      rw [Nat.beq_eq] at hh
      exact hh
    exact ⟨congrArg sv h1, h2⟩
  · intro h c hc
    obtain ⟨h1, h2⟩ := h c hc
    have h1' : p8 resT (icls c) = p8 resT c := sv_inj h1
    have h2' : w34 iclT (icls c) / 1048576 = c := h2
    show (Nat.beq (p8 resT (icls c)) (p8 resT c)
      && Nat.beq (w34 iclT (icls c) / 1048576) c) = true
    rw [h1', h2', Nat.beq_refl, Nat.beq_refl, Bool.and_self]

/-- The meaning of the residual bound check. -/
lemma resBoundOK_iff (cs : List ℕ) (bound : ℤ) :
    resBoundOK resT cs bound = true ↔
      cs.foldr (fun c acc => acc + resZ c) 0 = 0 ∧
        16 * (cs.foldr (fun c acc => acc + |resZ c|) 0) ≤ bound := by
  unfold resBoundOK
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  exact Iff.rfl

/-- The meaning of the target table check. -/
lemma qTabOK_iff (ps : List ℕ) :
    qTabOK qT qC2 ps = true ↔ ∀ p ∈ ps, qZ p = qC2 p := by
  unfold qTabOK
  rw [allL_eq_true]
  constructor
  · intro h p hp
    exact of_decide_eq_true (h p hp)
  · intro h p hp
    exact decide_eq_true (h p hp)


/-- A kernel check over the chunk `List.range n` upgrades to all `i < n`. -/
lemma allL_range_of_allL {l : List ℕ} {P : ℕ → Bool} {n : ℕ}
    (h : allL l P = true) (hl : l = List.range n) : ∀ i < n, P i = true := by
  rw [hl] at h
  rw [allL_eq_true] at h
  intro i hi
  exact h i (List.mem_range.mpr hi)

/-- A kernel check over the chunk `List.range' lo n` upgrades to all `i < n`, at `lo + i`. -/
lemma allL_range'_of_allL {l : List ℕ} {P : ℕ → Bool} {lo n : ℕ}
    (h : allL l P = true) (hl : l = List.range' lo n) : ∀ i < n, P (lo + i) = true := by
  rw [hl] at h
  rw [allL_eq_true] at h
  intro i hi
  exact h (lo + i) (List.mem_range'.mpr ⟨i, hi, by ring⟩)

/-! ## The target table `qT` against the closed form `qC2` -/

/-- `allL` over a concatenation. -/
lemma allL_append {l1 l2 : List ℕ} {p : ℕ → Bool} :
    allL (l1 ++ l2) p = true ↔ allL l1 p = true ∧ allL l2 p = true := by
  induction l1 with
  | nil => simp [allL]
  | cons a t ih =>
    rw [List.cons_append,
      show allL (a :: (t ++ l2)) p = (p a && allL (t ++ l2) p) from rfl,
      show allL (a :: t) p = (p a && allL t p) from rfl,
      Bool.and_eq_true, Bool.and_eq_true, ih]
    tauto

/-- The conjunction of two chunk checks. -/
lemma allL_append_of {l1 l2 : List ℕ} {p : ℕ → Bool}
    (h1 : allL l1 p = true) (h2 : allL l2 p = true) : allL (l1 ++ l2) p = true :=
  allL_append.mpr ⟨h1, h2⟩

/-- The table `qT` agrees with the closed form `qC2` on all `p < 6561`.  The `81` kernel checks
`C2K.q_ok{j}` are chained over the concatenation of their chunks (whose concatenation is
`List.range 6561`, a closed list equality checked by the kernel). -/
lemma qZ_eq_qC2_of_lt (p : ℕ) (hp : p < 6561) : qZ p = qC2 p := by
  have hcat := allL_append_of C2K.q_ok0
      (allL_append_of C2K.q_ok1
      (allL_append_of C2K.q_ok2
      (allL_append_of C2K.q_ok3
      (allL_append_of C2K.q_ok4
      (allL_append_of C2K.q_ok5
      (allL_append_of C2K.q_ok6
      (allL_append_of C2K.q_ok7
      (allL_append_of C2K.q_ok8
      (allL_append_of C2K.q_ok9
      (allL_append_of C2K.q_ok10
      (allL_append_of C2K.q_ok11
      (allL_append_of C2K.q_ok12
      (allL_append_of C2K.q_ok13
      (allL_append_of C2K.q_ok14
      (allL_append_of C2K.q_ok15
      (allL_append_of C2K.q_ok16
      (allL_append_of C2K.q_ok17
      (allL_append_of C2K.q_ok18
      (allL_append_of C2K.q_ok19
      (allL_append_of C2K.q_ok20
      (allL_append_of C2K.q_ok21
      (allL_append_of C2K.q_ok22
      (allL_append_of C2K.q_ok23
      (allL_append_of C2K.q_ok24
      (allL_append_of C2K.q_ok25
      (allL_append_of C2K.q_ok26
      (allL_append_of C2K.q_ok27
      (allL_append_of C2K.q_ok28
      (allL_append_of C2K.q_ok29
      (allL_append_of C2K.q_ok30
      (allL_append_of C2K.q_ok31
      (allL_append_of C2K.q_ok32
      (allL_append_of C2K.q_ok33
      (allL_append_of C2K.q_ok34
      (allL_append_of C2K.q_ok35
      (allL_append_of C2K.q_ok36
      (allL_append_of C2K.q_ok37
      (allL_append_of C2K.q_ok38
      (allL_append_of C2K.q_ok39
      (allL_append_of C2K.q_ok40
      (allL_append_of C2K.q_ok41
      (allL_append_of C2K.q_ok42
      (allL_append_of C2K.q_ok43
      (allL_append_of C2K.q_ok44
      (allL_append_of C2K.q_ok45
      (allL_append_of C2K.q_ok46
      (allL_append_of C2K.q_ok47
      (allL_append_of C2K.q_ok48
      (allL_append_of C2K.q_ok49
      (allL_append_of C2K.q_ok50
      (allL_append_of C2K.q_ok51
      (allL_append_of C2K.q_ok52
      (allL_append_of C2K.q_ok53
      (allL_append_of C2K.q_ok54
      (allL_append_of C2K.q_ok55
      (allL_append_of C2K.q_ok56
      (allL_append_of C2K.q_ok57
      (allL_append_of C2K.q_ok58
      (allL_append_of C2K.q_ok59
      (allL_append_of C2K.q_ok60
      (allL_append_of C2K.q_ok61
      (allL_append_of C2K.q_ok62
      (allL_append_of C2K.q_ok63
      (allL_append_of C2K.q_ok64
      (allL_append_of C2K.q_ok65
      (allL_append_of C2K.q_ok66
      (allL_append_of C2K.q_ok67
      (allL_append_of C2K.q_ok68
      (allL_append_of C2K.q_ok69
      (allL_append_of C2K.q_ok70
      (allL_append_of C2K.q_ok71
      (allL_append_of C2K.q_ok72
      (allL_append_of C2K.q_ok73
      (allL_append_of C2K.q_ok74
      (allL_append_of C2K.q_ok75
      (allL_append_of C2K.q_ok76
      (allL_append_of C2K.q_ok77
      (allL_append_of C2K.q_ok78
      (allL_append_of C2K.q_ok79
      (C2K.q_ok80))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have h : ∀ i < 6561, decide (qZ i = qC2 i) = true :=
    allL_range_of_allL (n := 6561) hcat (by decide +kernel)
  have h2 : decide (qZ p = qC2 p) = true := h p hp
  simpa using h2

/-- The target sum of the verified table is the target sum of the closed form. -/
lemma targetSum_qZ_eq : targetSum qZ 200 = targetSum qC2 200 := by
  unfold targetSum
  exact Finset.sum_congr rfl
    (fun p hp => by rw [qZ_eq_qC2_of_lt p (Finset.mem_range.mp hp)])

end Work.PTCert.Cert2

end
