import Mathlib
import Submission.Work.Transform.pwBase
import Submission.Work.Transform.pwMaxDefs

/-!
# `Work.Transform.Pw`: a `pwList`-free toolkit for the parameter-word assembly

`Submission/Work/Transform/pwList.lean` cannot be imported together with
`Submission/Work/Transform/pwMaxDefs.lean` (both declare `Work.Transform.Pw.bit_ne_gM`, whose
auxiliary match declaration clashes).  Since the assembly of `Work.Transform.paramWord` needs both
the max phase and the elementary `ofList`/size facts, this module re-proves the few facts of
`pwList` that the assembly uses, plus the size bundle `pk_sizes` (stated for
`S = ts.sum + p + 1`), the frame-marker fact `pk_intList_ne_gM` and the "drop the first cell" word
`pk_pwDropCell`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform.Pw

open HvdH
open Work.Kernel

/-! ## Encoding facts for `Val.int` and `ofList` -/

/-- The sign glyph of an integer. -/
def pk_sg (z : ℤ) : Glyph := if z < 0 then Glyph.neg else Glyph.pos

theorem pk_sg_ne_iend (z : ℤ) : pk_sg z ≠ Glyph.iend := by
  unfold pk_sg
  by_cases h : z < 0
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

theorem pk_sg_ne_gM (z : ℤ) : pk_sg z ≠ gM := by
  unfold pk_sg gM
  by_cases h : z < 0
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

theorem pk_sg_ne_nil (z : ℤ) : pk_sg z ≠ Glyph.nil := by
  unfold pk_sg
  by_cases h : z < 0
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

theorem pk_enc_int' (z : ℤ) :
    (Val.int z).enc = pk_sg z ::
      ((Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend]) :=
  rfl

theorem pk_cons_enc_eq (a b : Val) : (Val.cons a b).enc = Glyph.cons :: (a.enc ++ b.enc) := rfl

theorem pk_ofList_cons (a : Val) (as : List Val) : ofList (a :: as) = Val.cons a (ofList as) := rfl

theorem pk_nil_ne_gM : Glyph.nil ≠ gM := by decide

theorem pk_cons_ne_gM : Glyph.cons ≠ gM := by decide

/-- No glyph of an integer value is the frame marker `gM`. -/
theorem pk_int_enc_ne_gM (z : ℤ) : ∀ g ∈ (Val.int z).enc, g ≠ gM := by
  intro g hg
  rw [pk_enc_int'] at hg
  rcases List.mem_cons.mp hg with rfl | hg'
  · exact pk_sg_ne_gM z
  rcases List.mem_append.mp hg' with h1 | h2
  · obtain ⟨b, -, hb⟩ := List.mem_map.mp h1
    rw [← hb]; exact bit_ne_gM b
  · rw [List.mem_singleton] at h2; rw [h2]; exact fun h => nomatch h

/-- No glyph of the encoding of an integer list is the frame marker `gM`. -/
theorem pk_intList_ne_gM (ms : List ℕ) : ∀ g ∈ (intList ms).enc, g ≠ gM := by
  induction ms with
  | nil =>
    intro g hg
    rw [mx_intList_nil] at hg
    simp at hg
    subst hg
    exact pk_nil_ne_gM
  | cons t ms ih =>
    intro g hg
    rw [mx_intList_cons, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact pk_cons_ne_gM
    · rcases List.mem_append.mp hg with h1 | h2
      · exact pk_int_enc_ne_gM _ g h1
      · exact ih g h2

/-! ## The named coercion-free version of `intList` -/

/-- Named version of `Val.int` on `ℕ` (keeps maps free of coercions). -/
def pk_iVal (t : ℕ) : Val := Val.int (t : ℤ)

/-- Named version of `isz (t : ℤ)`. -/
def pk_iszN (t : ℕ) : ℕ := isz (t : ℤ)

theorem pk_iszN_eq (t : ℕ) : pk_iszN t = t.size + 2 := by
  simp only [pk_iszN]
  rw [Work.IntLib.isz_eq]
  simp

theorem pk_intList_eq_iVal (ms : List ℕ) : intList ms = ofList (ms.map pk_iVal) := by
  unfold intList pk_iVal
  congr 1
  rw [List.bind_eq_flatMap]
  change List.map (fun n : ℤ => Val.int n) (List.flatMap (pure ∘ (fun a : ℕ => (a : ℤ))) ms)
      = List.map (fun t : ℕ => Val.int (t : ℤ)) ms
  rw [List.flatMap_pure_eq_map, List.map_map]
  rfl

/-! ## Sizes -/

theorem pk_size_le_self (t : ℕ) : t.size ≤ t := by
  rw [Nat.size_le]; exact Nat.lt_two_pow_self

theorem pk_vsz_ofList (xs : List Val) : vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [ofList, List.foldr_cons, List.map_cons, List.sum_cons, List.length_cons, vsz,
      Val.enc, List.length_cons, List.length_append] at *
    omega

/-- Reversing the *value* `ofList xs` does not change its size. -/
theorem pk_vsz_ofList_reverse (xs : List Val) :
    vsz (ofList xs.reverse) = vsz (ofList xs) := by
  rw [pk_vsz_ofList, pk_vsz_ofList, List.map_reverse, List.sum_reverse, List.length_reverse]

theorem pk_vsz_iVal (ms : List ℕ) :
    vsz (ofList (ms.map pk_iVal)) = (ms.map pk_iszN).sum + ms.length + 1 := by
  rw [pk_vsz_ofList]
  have h1 : ((ms.map pk_iVal).map vsz) = ms.map pk_iszN := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, pk_iVal, pk_iszN]
    exact Work.IntLib.vsz_int (t : ℤ)
  rw [h1, List.length_map]

theorem pk_sum_iszN (ms : List ℕ) (h : ∀ t ∈ ms, 0 < t) :
    (ms.map pk_iszN).sum = (ms.map (fun t : ℕ => t.size)).sum + 2 * ms.length := by
  induction ms with
  | nil => simp
  | cons a as ih =>
    have has : ∀ t ∈ as, 0 < t := fun t ht => h t (by simp [ht])
    have ih' := ih has
    simp only [List.map_cons, List.sum_cons, List.length_cons, pk_iszN_eq] at ih' ⊢
    rw [ih']; ring

theorem pk_sum_size_le (ms : List ℕ) (h : ∀ t ∈ ms, 0 < t) :
    (ms.map (fun t : ℕ => t.size)).sum ≤ ms.sum := by
  induction ms with
  | nil => simp
  | cons a as ih =>
    have has : ∀ t ∈ as, 0 < t := fun t ht => h t (by simp [ht])
    have hs : a.size ≤ a := pk_size_le_self a
    have ih' := ih has
    simp only [List.map_cons, List.sum_cons] at ih' ⊢
    exact Nat.add_le_add hs ih'

theorem pk_length_le_sum (ms : List ℕ) (h : ∀ t ∈ ms, 0 < t) : ms.length ≤ ms.sum := by
  induction ms with
  | nil => simp
  | cons a as ih =>
    have has : ∀ t ∈ as, 0 < t := fun t ht => h t (by simp [ht])
    have ha : 1 ≤ a := h a (by simp)
    have ih' := ih has
    have h1 : as.length + 1 ≤ as.sum + a := Nat.add_le_add ih' ha
    simp only [List.length_cons, List.sum_cons]
    omega

theorem pk_vsz_intList_le (ms : List ℕ) (h : ∀ t ∈ ms, 0 < t) :
    vsz (intList ms) ≤ 4 * ms.sum + 4 := by
  rw [pk_intList_eq_iVal, pk_vsz_iVal, pk_sum_iszN ms h]
  have h1 := pk_sum_size_le ms h
  have h2 := pk_length_le_sum ms h
  omega

/-- `t ∈ l.dropLast` gives `t ∈ l`. -/
theorem pk_mem_dropLast {l : List ℕ} {t : ℕ} (h : t ∈ l.dropLast) : t ∈ l :=
  (List.dropLast_prefix l).subset h

/-- The sum of the `dropLast` is at most the sum. -/
theorem pk_sum_dropLast_le : ∀ l : List ℕ, l.dropLast.sum ≤ l.sum
  | [] => by simp
  | [a] => by simp
  | a :: b :: t => by
    rw [List.dropLast_cons_cons]
    have := pk_sum_dropLast_le (b :: t)
    simp only [List.sum_cons] at *
    omega

/-- The last entry of a nonempty list belongs to it. -/
theorem pk_getLastD_mem (ts : List ℕ) (h : ts ≠ []) : ts.getLastD 0 ∈ ts := by
  induction ts with
  | nil => exact absurd rfl h
  | cons a t ih =>
    rcases t with _ | ⟨b, u⟩
    · simp
    · have hu : (b :: u) ≠ [] := by simp
      have := ih hu
      simpa [List.getLastD] using List.mem_cons_of_mem a this

/-! ## `lmax` -/

theorem pk_lmax_mem (ms : List ℕ) (h : ms ≠ []) : lmax ms ∈ ms := by
  induction ms with
  | nil => exact absurd rfl h
  | cons a as ih =>
    by_cases hnil : as = []
    · subst hnil; simp [lmax]
    · rcases le_total a (lmax as) with hle | hle
      · have h1 : lmax (a :: as) = lmax as := max_eq_right hle
        rw [h1]; exact List.mem_cons_of_mem a (ih hnil)
      · have h1 : lmax (a :: as) = a := max_eq_left hle
        rw [h1]; exact List.mem_cons_self

theorem pk_lmax_le_sum (ms : List ℕ) (h : ms ≠ []) (hp : ∀ t ∈ ms, 0 < t) :
    lmax ms ≤ ms.sum :=
  List.le_sum_of_mem (pk_lmax_mem ms h)

/-! ## Reversal identities for the `dropLast` step -/

theorem pk_rev_map_tail (ms : List ℕ) (f : ℕ → Val) :
    ((ms.map f).reverse).tail = ((ms.dropLast).map f).reverse := by
  rw [List.tail_reverse, List.map_dropLast]

theorem pk_rev_map_cons (ms : List ℕ) (f : ℕ → Val) (h : ms ≠ []) :
    (ms.map f).reverse = f (ms.getLastD 0) :: ((ms.dropLast).map f).reverse := by
  induction ms with
  | nil => exact absurd rfl h
  | cons a as ih =>
    rcases as with _ | ⟨b, bs⟩
    · simp [List.getLastD]
    · have has : (b :: bs) ≠ [] := by simp
      have ih' := ih has
      have hdl : (a :: b :: bs).dropLast = a :: (b :: bs).dropLast :=
        List.dropLast_cons_of_ne_nil has
      calc ((a :: b :: bs).map f).reverse
          = (f a :: ((b :: bs).map f)).reverse := by rw [List.map_cons]
        _ = ((b :: bs).map f).reverse ++ [f a] := by rw [List.reverse_cons]
        _ = (f ((b :: bs).getLastD 0) :: (((b :: bs).dropLast).map f).reverse) ++ [f a] := by
              rw [ih']
        _ = f ((a :: b :: bs).getLastD 0) :: (((a :: b :: bs).dropLast).map f).reverse := by
              rw [hdl, List.map_cons, List.reverse_cons]
              simp [List.append_assoc, List.getLastD, List.getLast?_cons]

/-! ## Dropping the first cell of a `cons`-list -/

/-- Program of `pk_pwDropCell`: pop the leading `cons`, discard up to the head's `iend`, pop it. -/
def pk_dropCellProg (src : Stk) (rA rB : Reg) : Cmd :=
  .seq (.pop src rA) (.seq (dLoop src Glyph.iend rB) (.pop src rA))

theorem pk_pwDropCell (src : Stk) : ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (z : ℤ) (xs : List Val) (below : List Glyph) (s : State),
      s.stk src = (ofList (Val.int z :: xs)).enc ++ gM :: below →
      ∃ s' n, Eval main prog s s' n ∧ n ≤ K * (isz z + 1) ∧
        s'.stk src = (ofList xs).enc ++ gM :: below ∧
        (∀ j : Stk, j ≠ src → s'.stk j = s.stk j) := by
  refine ⟨pk_dropCellProg src 0 1, 5, ?_⟩
  intro main z xs below s hstk
  rw [pk_ofList_cons, pk_cons_enc_eq, pk_enc_int'] at hstk
  set bits := Computability.encodeNat z.natAbs with hbitsdef
  set gbits : List Glyph := bits.map Glyph.bit with hgbits
  set below' : List Glyph := (ofList xs).enc ++ gM :: below with hbelow
  have hstk1 : s.stk src = Glyph.cons :: ((pk_sg z :: gbits) ++ Glyph.iend :: below') := by
    rw [hstk, hbelow, hgbits, hbitsdef]; simp [List.cons_append, List.append_assoc]
  set s1 := State.tPop s src 0 with hs1
  have e1 : Eval main (.pop src (0 : Reg)) s s1 1 := by
    rw [hs1]; exact eval_pop main src 0 s
  have hs1stk : s1.stk src = (pk_sg z :: gbits) ++ Glyph.iend :: below' := by
    rw [hs1, tPop_stk, if_pos rfl, hstk1]; rfl
  have hne : ∀ g ∈ (pk_sg z :: gbits : List Glyph), g ≠ Glyph.iend := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact pk_sg_ne_iend z
    · obtain ⟨b, -, hb⟩ := List.mem_map.mp hg'
      rw [← hb]; exact bit_ne_iend b
  set s2 := dSt src Glyph.iend 1 below' s1 with hs2
  have e2 : Eval main (dLoop src Glyph.iend (1 : Reg)) s1 s2
      (4 * (pk_sg z :: gbits).length + 7) := by
    rw [hs2]; exact dLoop_eval main src Glyph.iend 1 iend_ne_eos _ _ s1 hs1stk hne
  have hs2stk : s2.stk src = Glyph.iend :: below' := by rw [hs2, dSt_stk_k]
  set s3 := State.tPop s2 src 0 with hs3
  have e3 : Eval main (.pop src (0 : Reg)) s2 s3 1 := by
    rw [hs3]; exact eval_pop main src 0 s2
  have hs3stk : s3.stk src = below' := by rw [hs3, tPop_stk, if_pos rfl, hs2stk]; rfl
  refine ⟨s3, 1 + ((4 * (pk_sg z :: gbits).length + 7) + 1), ?_, ?_, ?_, ?_⟩
  · exact Eval.seq e1 (Eval.seq e2 e3)
  · have hsz : gbits.length = z.natAbs.size := by
      rw [hgbits, List.length_map, hbitsdef]; exact Work.IntLib.encodeNat_length _
    have hisz : isz z = z.natAbs.size + 2 := Work.IntLib.isz_eq z
    simp only [List.length_cons] at *
    omega
  · rw [hs3stk, hbelow]
  · intro j hj
    rw [hs3, tPop_stk, if_neg hj, hs2, dSt_stk_ne' _ _ _ _ _ hj,
      hs1, tPop_stk, if_neg hj]

/-! ## Pushing a constant glyph -/

theorem pk_pushGlyphWord (k : Stk) (g : Glyph) : ∃ (prog : Cmd),
    ∀ (main : Cmd) (s : State),
      ∃ s' n, Eval main prog s s' n ∧ n ≤ 2 ∧ s'.stk k = g :: s.stk k ∧
        (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  refine ⟨.seq (.set 0 g) (.push k 0), ?_⟩
  intro main s
  refine ⟨State.tPush (State.tSet s 0 g) k 0, 2, Eval.seq (eval_set main 0 g s)
    (eval_push main k 0 (State.tSet s 0 g)), by omega, ?_, ?_⟩
  · simp [State.tPush, State.tSet, State.updStk, State.updReg]
  · intro j hj; simp [State.tPush, State.tSet, State.updStk, State.updReg, hj]

/-! ## The size bundle for the assembly -/

theorem pk_sizes (ts : List ℕ) (p : ℕ) (hts : ts ≠ []) (hpos : ∀ t ∈ ts, 0 < t) :
    (1 ≤ ts.sum) ∧
    (vsz (intList ts) + 1 ≤ 5 * (ts.sum + p + 1)) ∧
    (vsz (intList ts.dropLast) + 1 ≤ 5 * (ts.sum + p + 1)) ∧
    (vsz (intList ts.reverse) + 1 ≤ 5 * (ts.sum + p + 1)) ∧
    (vsz (Val.int (p : ℤ)) + 1 ≤ 2 * (ts.sum + p + 1)) ∧
    (ts.sum + 1 ≤ ts.sum + p + 1) ∧
    (isz (((ts.getLastD 0 : ℕ) : ℤ)) + 1 ≤ 3 * (ts.sum + p + 1)) ∧
    ((lmax ts).size + 1 ≤ 2 * (ts.sum + p + 1)) ∧
    (vsz (Val.int ((lmax ts) : ℤ)) + vsz (intList ts.dropLast) + vsz (intList ts)
      + vsz (Val.int (p : ℤ)) + 1 ≤ 20 * (ts.sum + p + 1)) ∧
    ((ts.dropLast).sum ≤ ts.sum) := by
  have hsum1 : 1 ≤ ts.sum := by
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil ts hts
    exact le_trans (hpos t ht) (List.le_sum_of_mem ht)
  have hdl_sum : (ts.dropLast).sum ≤ ts.sum := pk_sum_dropLast_le ts
  have hdl_pos : ∀ t ∈ ts.dropLast, 0 < t := fun t ht => hpos t (pk_mem_dropLast ht)
  have hrev_pos : ∀ t ∈ ts.reverse, 0 < t := fun t ht => hpos t (List.mem_reverse.mp ht)
  have hrev_sum : (ts.reverse).sum ≤ ts.sum := by rw [List.sum_reverse]
  have h1 := pk_vsz_intList_le ts hpos
  have h2 := pk_vsz_intList_le ts.dropLast hdl_pos
  have h3 := pk_vsz_intList_le ts.reverse hrev_pos
  have h4 : vsz (Val.int (p : ℤ)) = p.size + 2 := by
    unfold vsz; rw [Work.IntLib.vsz_int, Work.IntLib.isz_eq]; simp
  have hp_sz : p.size ≤ p := pk_size_le_self p
  have h5 : isz (((ts.getLastD 0 : ℕ) : ℤ)) = (ts.getLastD 0).size + 2 := by
    rw [Work.IntLib.isz_eq]; simp
  have hlast : ts.getLastD 0 ≤ ts.sum := List.le_sum_of_mem (pk_getLastD_mem ts hts)
  have h6 : (ts.getLastD 0).size ≤ ts.sum := le_trans (pk_size_le_self _) hlast
  have h7 : vsz (Val.int ((lmax ts) : ℤ)) = (lmax ts).size + 2 := by
    unfold vsz; rw [Work.IntLib.vsz_int, Work.IntLib.isz_eq]; simp
  have h8 : (lmax ts).size ≤ ts.sum :=
    le_trans (pk_size_le_self _) (pk_lmax_le_sum ts hts hpos)
  refine ⟨hsum1, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, hdl_sum⟩ <;> omega

end Work.Transform.Pw
