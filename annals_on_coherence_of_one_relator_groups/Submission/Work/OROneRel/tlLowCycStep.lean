/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The step structure of the low window `[0, p+q-1]` of the two-letter band

For the two-letter weight `tlW p q` (`a = 0 ↦ q`, `b = 1 ↦ -p`) the *edges of the window*
`winE (tlW p q) 0 (p+q-1)` are exactly the `p+q` edges

  `(cycGen i, i)`  for  `i ∈ {0, …, p+q-1}`,

where `cycGen i = a` below the level `p` and `cycGen i = b` at or above `p`.  Each level `i` of the
window therefore has exactly two outgoing traversals: the *forward* one, spelled by the positive
letter `cycGen i` and leading to `cycStep i`, and the *backward* one, spelled by the negative letter
`cycGen (cycPred i)` and leading to `cycPred i` (the other neighbour of `i` on the cycle).

This file contains the definitions `cycGen`, `cycStep`, `cycPred` (and the forward/backward cycle
prefixes `cycFwdList`, `cycBwdList`), together with the elementary arithmetic of the cycle: the
identification with `cycLevel`/`cycLetter`, the membership of the window, the forced-letter lemmas
`letter_pos_winE` / `letter_neg_winE` and their head specialisations, and the telescoping weight
`lsig (tlW p q) (cycFwdList p q k m) = cycLevel p q (k+m) - cycLevel p q k`.

Everything here is *proved*; the combinatorial crux (a reduced word of the window is a forward or
backward cycle prefix) is delegated, and the assembly is in
`Submission/Work/OROneRel/tlWin_low_zpowers_lemma.lean`.
-/
import Mathlib
import Submission.Work.OROneRel.tlLowCycDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.decorGetElemCover

namespace Work.OROneRel

/-! ## The two steps of the low window -/

/-- The forward generator of the low window at the level `i`: `a` (index `0`) for `i < p`, `b`
(index `1`) for `i ≥ p`. -/
def cycGen (p q : ℕ) (i : ℤ) : Fin 2 := if i < (p : ℤ) then 0 else 1

/-- The level reached by the forward step from the level `i` of the low window. -/
def cycStep (p q : ℕ) (i : ℤ) : ℤ := if i < (p : ℤ) then i + (q : ℤ) else i - (p : ℤ)

/-- The level reached by the backward step from the level `i` of the low window (the other
neighbour of `i` on the cycle). -/
def cycPred (p q : ℕ) (i : ℤ) : ℤ := if (q : ℤ) ≤ i then i - (q : ℤ) else i + (p : ℤ)

/-- The forward cycle prefix of length `m` starting at the index `k`. -/
def cycFwdList (p q : ℕ) (k : ℤ) (m : ℕ) : List (Fin 2 × Bool) :=
  (List.range m).map (fun j : ℕ => (cycLetter p q (k + (j : ℤ)), true))

/-- The backward cycle prefix of length `m` starting at the index `k`. -/
def cycBwdList (p q : ℕ) (k : ℤ) (m : ℕ) : List (Fin 2 × Bool) :=
  (List.range m).map (fun j : ℕ => (cycLetter p q (k - 1 - (j : ℤ)), false))

/-- The element spelled by the forward cycle prefix of length `m`. -/
noncomputable def cycFwdWord (p q : ℕ) (m : ℕ) : FreeGroup (Fin 2) :=
  FreeGroup.mk (cycFwdList p q 0 m)

/-- The element spelled by the backward cycle prefix of length `m`. -/
noncomputable def cycBwdWord (p q : ℕ) (m : ℕ) : FreeGroup (Fin 2) :=
  FreeGroup.mk (cycBwdList p q 0 m)

/-! ## Elementary list arithmetic -/

/-- Additivity of the weight (local copy, to avoid the duplicated `lsig_append` of the workspace). -/
theorem lsig_append_cyc {α : Type*} (c : α → ℤ) (L₁ L₂ : List (α × Bool)) :
    lsig c (L₁ ++ L₂) = lsig c L₁ + lsig c L₂ := by
  simp [lsig, List.map_append, List.sum_append]

/-! ## The weight of the two generators -/

theorem tlLowW_zero (p q : ℕ) : tlW p q (0 : Fin 2) = (q : ℤ) := by
  simp [tlW]

theorem tlLowW_one (p q : ℕ) : tlW p q (1 : Fin 2) = -(p : ℤ) := by
  simp only [tlW]
  rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

/-! ## The identification with `cycLevel` and `cycLetter` -/

theorem cycGen_cycLevel (p q : ℕ) (k : ℤ) : cycGen p q (cycLevel p q k) = cycLetter p q k := rfl

theorem cycGen_eq_zero_iff (p q : ℕ) (i : ℤ) : cycGen p q i = 0 ↔ i < (p : ℤ) := by
  unfold cycGen
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    exact absurd h (by decide)
  · intro h
    rw [if_pos h]

theorem cycGen_eq_one_iff (p q : ℕ) (i : ℤ) : cycGen p q i = 1 ↔ (p : ℤ) ≤ i := by
  unfold cycGen
  constructor
  · intro h
    by_contra hc
    rw [if_pos (not_le.mp hc)] at h
    exact absurd h (by decide)
  · intro h
    rw [if_neg (not_lt.mpr h)]

theorem tlW_cycGen (p q : ℕ) (i : ℤ) : tlW p q (cycGen p q i) = cycStep p q i - i := by
  by_cases h : i < (p : ℤ)
  · simp only [cycGen, cycStep, if_pos h, tlLowW_zero]
    ring
  · simp only [cycGen, cycStep, if_neg h, tlLowW_one]
    ring

theorem cycStep_cycLevel (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ) :
    cycStep p q (cycLevel p q k) = cycLevel p q (k + 1) := by
  by_cases h : cycLevel p q k < (p : ℤ)
  · rw [cycStep, if_pos h]
    exact (cycLevel_succ_below p q hp hq h).symm
  · rw [cycStep, if_neg h]
    exact (cycLevel_succ_above p q hp hq (le_of_not_gt h)).symm

theorem cycLevel_step_succ (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ) :
    cycLevel p q (k + 1) = cycStep p q (cycLevel p q k) :=
  (cycStep_cycLevel p q hp hq k).symm

/-- The weight of the letter of the cycle at index `i` is the level increment of the forward step
followed by the cycle at that index. -/
theorem tlW_cycLetter_step (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (i : ℤ) :
    tlW p q (cycLetter p q i) = cycLevel p q (i + 1) - cycLevel p q i := by
  rw [← cycGen_cycLevel, tlW_cycGen, cycStep_cycLevel p q hp hq]

/-- The level of the cycle at index `k` plus the weight of the forward letter there is the level of
the cycle at index `k+1`. -/
theorem cycLevel_add_tlW_cycLetter (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ) :
    cycLevel p q k + tlW p q (cycLetter p q k) = cycLevel p q (k + 1) := by
  rw [tlW_cycLetter_step p q hp hq]
  ring

/-- The level of the cycle at index `k` minus the weight of the (negative) backward letter there is
the level of the cycle at index `k-1`. -/
theorem cycLevel_sub_tlW_cycLetter (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ) :
    cycLevel p q k - tlW p q (cycLetter p q (k - 1)) = cycLevel p q (k - 1) := by
  have h := cycLevel_add_tlW_cycLetter p q hp hq (k - 1)
  have hk : k - 1 + 1 = k := by ring
  rw [hk] at h
  linarith

/-! ## The two steps are inverse on the window -/

theorem cycStep_mem_window (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {i : ℤ}
    (h0 : 0 ≤ i) (h1 : i ≤ (p : ℤ) + (q : ℤ) - 1) :
    0 ≤ cycStep p q i ∧ cycStep p q i ≤ (p : ℤ) + (q : ℤ) - 1 := by
  by_cases h : i < (p : ℤ)
  · rw [cycStep, if_pos h]
    constructor <;> linarith
  · rw [cycStep, if_neg h]
    constructor <;> linarith

theorem cycPred_mem_window (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {i : ℤ}
    (h0 : 0 ≤ i) (h1 : i ≤ (p : ℤ) + (q : ℤ) - 1) :
    0 ≤ cycPred p q i ∧ cycPred p q i ≤ (p : ℤ) + (q : ℤ) - 1 := by
  by_cases h : (q : ℤ) ≤ i
  · rw [cycPred, if_pos h]
    constructor <;> linarith
  · rw [cycPred, if_neg h]
    constructor <;> linarith

theorem cycPred_cycStep (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {i : ℤ}
    (h0 : 0 ≤ i) (h1 : i ≤ (p : ℤ) + (q : ℤ) - 1) : cycPred p q (cycStep p q i) = i := by
  by_cases h : i < (p : ℤ)
  · have hs : cycStep p q i = i + (q : ℤ) := by rw [cycStep, if_pos h]
    rw [hs, cycPred, if_pos (by linarith)]
    ring
  · have hs : cycStep p q i = i - (p : ℤ) := by rw [cycStep, if_neg h]
    rw [hs, cycPred, if_neg (by linarith)]
    ring

theorem cycStep_cycPred (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {i : ℤ}
    (h0 : 0 ≤ i) (h1 : i ≤ (p : ℤ) + (q : ℤ) - 1) : cycStep p q (cycPred p q i) = i := by
  by_cases h : (q : ℤ) ≤ i
  · have hs : cycPred p q i = i - (q : ℤ) := by rw [cycPred, if_pos h]
    rw [hs, cycStep, if_pos (by linarith)]
    ring
  · have hs : cycPred p q i = i + (p : ℤ) := by rw [cycPred, if_neg h]
    rw [hs, cycStep, if_neg (by linarith)]
    ring

theorem cycPred_cycLevel (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ) :
    cycPred p q (cycLevel p q k) = cycLevel p q (k - 1) := by
  have hb := cycLevel_bounds p q hp (k - 1)
  have hb' : cycLevel p q (k - 1) ≤ (p : ℤ) + (q : ℤ) - 1 := by
    have h := hb.2
    simp only [tlN] at h
    linarith
  have hstep : cycLevel p q k = cycStep p q (cycLevel p q (k - 1)) := by
    rw [cycStep_cycLevel p q hp hq (k - 1)]
    congr 1
    ring
  rw [hstep]
  exact cycPred_cycStep p q hp hq hb.1 hb'

/-! ## The window edges at a level: the forced letter -/

theorem letter_pos_winE (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {a : Fin 2} {i : ℤ}
    (h0 : 0 ≤ i) (h1 : i ≤ (p : ℤ) + (q : ℤ) - 1) :
    (a, i) ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) ↔ a = cycGen p q i := by
  rw [mem_winE]
  constructor
  · rintro ⟨-, -, h2, h3⟩
    have h2' : 0 ≤ i + tlW p q a := h2
    have h3' : i + tlW p q a ≤ (p : ℤ) + (q : ℤ) - 1 := h3
    by_cases ha : a = 0
    · have hlt : i < (p : ℤ) := by
        rw [ha, tlLowW_zero] at h3'
        linarith
      rw [ha, show cycGen p q i = 0 from (cycGen_eq_zero_iff p q i).mpr hlt]
    · have ha1 : a = 1 := by
        apply Fin.ext
        have hval : a.val ≠ 0 := fun h => ha (Fin.ext h)
        have := a.isLt
        omega
      have hle : (p : ℤ) ≤ i := by
        rw [ha1, tlLowW_one] at h2'
        linarith
      rw [ha1, show cycGen p q i = 1 from (cycGen_eq_one_iff p q i).mpr hle]
  · intro h
    have hwin := cycStep_mem_window p q hp hq h0 h1
    have hval : i + tlW p q (cycGen p q i) = cycStep p q i := by
      rw [tlW_cycGen]
      ring
    refine ⟨h0, h1, ?_, ?_⟩ <;> rw [h, hval] <;> [exact hwin.1; exact hwin.2]

theorem letter_neg_winE (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {a : Fin 2} {i : ℤ}
    (h0 : 0 ≤ i) (h1 : i ≤ (p : ℤ) + (q : ℤ) - 1) :
    (a, i - tlW p q a) ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) ↔
      a = cycGen p q (cycPred p q i) := by
  rw [mem_winE]
  constructor
  · rintro ⟨h4, h5, h6, h7⟩
    have h4' : 0 ≤ i - tlW p q a := h4
    have h5' : i - tlW p q a ≤ (p : ℤ) + (q : ℤ) - 1 := h5
    by_cases ha : a = 0
    · have hle : (q : ℤ) ≤ i := by
        rw [ha, tlLowW_zero] at h4'
        linarith
      have hlt : i - (q : ℤ) < (p : ℤ) := by
        rw [ha, tlLowW_zero] at h5'
        linarith
      rw [ha, show cycPred p q i = i - (q : ℤ) from by rw [cycPred, if_pos hle],
        show cycGen p q (i - (q : ℤ)) = 0 from
          (cycGen_eq_zero_iff p q (i - (q : ℤ))).mpr hlt]
    · have ha1 : a = 1 := by
        apply Fin.ext
        have hval : a.val ≠ 0 := fun h => ha (Fin.ext h)
        have := a.isLt
        omega
      have hq' : i < (q : ℤ) := by
        rw [ha1, tlLowW_one] at h5'
        linarith
      have hnot : ¬ ((q : ℤ) ≤ i) := by linarith
      have hge : (p : ℤ) ≤ i + (p : ℤ) := by linarith
      rw [ha1, show cycPred p q i = i + (p : ℤ) from by rw [cycPred, if_neg hnot],
        show cycGen p q (i + (p : ℤ)) = 1 from
          (cycGen_eq_one_iff p q (i + (p : ℤ))).mpr hge]
  · intro h
    have hpred := cycPred_mem_window p q hp hq h0 h1
    have hval : i - tlW p q a = cycPred p q i := by
      rw [h, tlW_cycGen, cycStep_cycPred p q hp hq h0 h1]
      ring
    have hsum : (i - tlW p q a) + tlW p q a = i := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hval]; exact hpred.1
    · rw [hval]; exact hpred.2
    · rw [hsum]; exact h0
    · rw [hsum]; exact h1

/-- **The head letter of a positive-headed window word.**  If the edges of the decorated walk of
`(a, true) :: t` started at the cycle index `k` all lie in the window, then `a` is the letter of the
cycle at the index `k`. -/
theorem head_pos_letter (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {k : ℤ} {a : Fin 2}
    {t : List (Fin 2 × Bool)}
    (hwin : ∀ e ∈ decor (tlW p q) (cycLevel p q k) ((a, true) :: t),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1)) :
    a = cycLetter p q k := by
  have hmem : ((a, cycLevel p q k), true) ∈
      decor (tlW p q) (cycLevel p q k) ((a, true) :: t) := by
    rw [decor_cons_l]
    simp
  have h := hwin _ hmem
  have hb := cycLevel_bounds p q hp k
  have hb' : cycLevel p q k ≤ (p : ℤ) + (q : ℤ) - 1 := by
    have h := hb.2
    simp only [tlN] at h
    linarith
  have h2 := (letter_pos_winE p q hp hq hb.1 hb').mp
    (show (a, cycLevel p q k) ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) from h)
  rw [h2, cycGen_cycLevel]

/-- **The head letter of a negative-headed window word.**  If the edges of the decorated walk of
`(a, false) :: t` started at the cycle index `k` all lie in the window, then `a` is the letter of the
cycle at the index `k-1`. -/
theorem head_neg_letter (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {k : ℤ} {a : Fin 2}
    {t : List (Fin 2 × Bool)}
    (hwin : ∀ e ∈ decor (tlW p q) (cycLevel p q k) ((a, false) :: t),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1)) :
    a = cycLetter p q (k - 1) := by
  have hmem : ((a, cycLevel p q k - tlW p q a), false) ∈
      decor (tlW p q) (cycLevel p q k) ((a, false) :: t) := by
    rw [decor_cons_l]
    simp
  have h := hwin _ hmem
  have hb := cycLevel_bounds p q hp k
  have hb' : cycLevel p q k ≤ (p : ℤ) + (q : ℤ) - 1 := by
    have h := hb.2
    simp only [tlN] at h
    linarith
  have h2 := (letter_neg_winE p q hp hq hb.1 hb').mp
    (show (a, cycLevel p q k - tlW p q a) ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) from h)
  rw [h2, cycPred_cycLevel p q hp hq k, cycGen_cycLevel]

/-! ## The telescoping weight of the cycle prefixes -/

theorem lsig_cycFwdList (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ) (m : ℕ) :
    lsig (tlW p q) (cycFwdList p q k m) = cycLevel p q (k + (m : ℤ)) - cycLevel p q k := by
  induction m with
  | zero => simp [cycFwdList, lsig]
  | succ m ih =>
    have hsplit : cycFwdList p q k (m + 1)
        = cycFwdList p q k m ++ [(cycLetter p q (k + (m : ℤ)), true)] := by
      simp only [cycFwdList, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [hsplit, lsig_append_cyc, ih]
    have hsingle : lsig (tlW p q) [(cycLetter p q (k + (m : ℤ)), true)]
        = tlW p q (cycLetter p q (k + (m : ℤ))) := by simp [lsig]
    rw [hsingle, tlW_cycLetter_step p q hp hq]
    push_cast
    ring_nf

theorem lsig_cycBwdList (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ) (m : ℕ) :
    lsig (tlW p q) (cycBwdList p q k m) = cycLevel p q (k - (m : ℤ)) - cycLevel p q k := by
  induction m with
  | zero => simp [cycBwdList, lsig]
  | succ m ih =>
    have hsplit : cycBwdList p q k (m + 1)
        = cycBwdList p q k m ++ [(cycLetter p q (k - 1 - (m : ℤ)), false)] := by
      simp only [cycBwdList, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [hsplit, lsig_append_cyc, ih]
    have hsingle : lsig (tlW p q) [(cycLetter p q (k - 1 - (m : ℤ)), false)]
        = -tlW p q (cycLetter p q (k - 1 - (m : ℤ))) := by simp [lsig]
    rw [hsingle, tlW_cycLetter_step p q hp hq]
    push_cast
    ring_nf

/-! ## The decoration of a cycle prefix -/

theorem decor_cycFwdList (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℤ) (m : ℕ) :
    decor (tlW p q) (cycLevel p q k) (cycFwdList p q k m)
      = (List.range m).map (fun j : ℕ =>
          (((cycLetter p q (k + (j : ℤ))), cycLevel p q (k + (j : ℤ))), true)) := by
  induction m with
  | zero => simp [cycFwdList, decor]
  | succ m ih =>
    have hsplit : cycFwdList p q k (m + 1)
        = cycFwdList p q k m ++ [(cycLetter p q (k + (m : ℤ)), true)] := by
      simp only [cycFwdList, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [hsplit, decor_append, ih, lsig_cycFwdList p q hp hq k m]
    have hlv : cycLevel p q k + (cycLevel p q (k + (m : ℤ)) - cycLevel p q k)
        = cycLevel p q (k + (m : ℤ)) := by ring
    rw [hlv]
    have hlast : decor (tlW p q) (cycLevel p q (k + (m : ℤ)))
        [(cycLetter p q (k + (m : ℤ)), true)]
        = [(((cycLetter p q (k + (m : ℤ))), cycLevel p q (k + (m : ℤ))), true)] := rfl
    rw [hlast, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-! ## The cycle word as a forward prefix -/

theorem cycFwdList_zero_shift (p q : ℕ) (m : ℕ) :
    cycFwdList p q 0 m = (List.range m).map (fun j : ℕ => (cycLetter p q (j : ℤ), true)) := by
  simp only [cycFwdList]
  exact List.map_congr_left (fun j _ => by simp)

theorem cycWord_eq_cycFwdWord (p q : ℕ) : cycWord p q = cycFwdWord p q (p + q) := by
  simp only [cycWord, cycFwdWord, cycList, cycFwdList]
  congr 1
  exact List.map_congr_left (fun j _ => by simp)

/-! ## Divisibility from the vanishing of the level -/

theorem cycLevel_eq_zero_iff_dvd_nat {p q : ℕ} (hp : 1 ≤ p) (hcop : Nat.Coprime p q) {m : ℕ} :
    cycLevel p q (m : ℤ) = 0 ↔ (p + q) ∣ m := by
  rw [cycLevel_eq_zero_iff p q hp hcop (m : ℤ), tlN_cast]
  constructor
  · rintro ⟨c, hc⟩
    have hpos : (0 : ℤ) < ((p + q : ℕ) : ℤ) := by
      have : 0 < p + q := by omega
      exact_mod_cast this
    have hnn : 0 ≤ c := by
      by_contra hc0
      push_neg at hc0
      have hlt : ((p + q : ℕ) : ℤ) * c < 0 := mul_neg_of_pos_of_neg hpos hc0
      rw [← hc] at hlt
      linarith [Int.natCast_nonneg m]
    refine ⟨c.toNat, ?_⟩
    have h2 : ((p + q : ℕ) : ℤ) * (c.toNat : ℤ) = (m : ℤ) := by
      have hcn : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hnn
      rw [hcn, hc]
    have h3 : (((p + q) * c.toNat : ℕ) : ℤ) = (m : ℤ) := by
      push_cast
      exact h2
    exact_mod_cast h3.symm
  · rintro ⟨c, rfl⟩
    exact ⟨(c : ℤ), by push_cast; ring⟩

theorem cycLevel_eq_zero_iff_dvd_nat_neg {p q : ℕ} (hp : 1 ≤ p) (hcop : Nat.Coprime p q)
    {m : ℕ} : cycLevel p q (-(m : ℤ)) = 0 ↔ (p + q) ∣ m := by
  rw [cycLevel_eq_zero_iff p q hp hcop (-(m : ℤ)), tlN_cast]
  constructor
  · rintro ⟨c, hc⟩
    have hpos : (0 : ℤ) < ((p + q : ℕ) : ℤ) := by
      have : 0 < p + q := by omega
      exact_mod_cast this
    have hnn : 0 ≤ -c := by
      by_contra hc0
      push_neg at hc0
      have hpos' : 0 < c := by linarith
      have hlt : 0 < ((p + q : ℕ) : ℤ) * c := mul_pos hpos hpos'
      rw [← hc] at hlt
      linarith [Int.natCast_nonneg m]
    refine ⟨(-c).toNat, ?_⟩
    have h2 : ((p + q : ℕ) : ℤ) * (((-c).toNat : ℤ)) = (m : ℤ) := by
      have hcn : (((-c).toNat : ℤ)) = -c := Int.toNat_of_nonneg hnn
      rw [hcn]
      linarith [hc]
    have h3 : (((p + q) * (-c).toNat : ℕ) : ℤ) = (m : ℤ) := by
      push_cast
      exact h2
    exact_mod_cast h3.symm
  · rintro ⟨c, rfl⟩
    exact ⟨-(c : ℤ), by push_cast; ring⟩

/-! ## The reduced word of an element -/

theorem tlLow_wordOf_isReduced {α : Type*} (u : FreeGroup α) :
    FreeGroup.IsReduced (wordOf u) := by
  rw [wordOf]
  exact @FreeGroup.isReduced_toWord α (Classical.decEq α) u

end Work.OROneRel
