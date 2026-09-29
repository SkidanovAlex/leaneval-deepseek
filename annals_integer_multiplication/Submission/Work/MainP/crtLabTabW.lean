import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.MainP.crtLabSetupAux
import Submission.Work.MainP.labArith
import Submission.Work.MainP.labFold
import Submission.Work.MainP.crtLabSum
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.reverseWord
import Submission.Work.MainP.crtStepDiv
-- import Submission.Work.MainP.labCostBoundW

/-!
# `crtLabTabW`: the place-value table word of the CRT label word

From `int S :: intList ss` (with `S = ss.prod`) this file's word produces `ofList (canon ss 0)` —
the list of entries `triple 0 (suf (j+1)) (suf j)` — at cost
`O (vsz (intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1))`.

Program (stacks: 0 = values, 7 = the modulus pile, 14, 15 = scratch):

1. `roll 1` — bring the modulus list `intList ss` on top;
2. `mvVal 0 7 14 15` — move it to the pile (stack 7);
3. `pushVal nil`, `swap` — `int S :: nil :: rest` on the value stack;
4. the fold `Work.MainP.labFold step` — walk the moduli from the pile, dividing the running product
   `P` by the current modulus `t` and consing `triple 0 (P/t) P` onto the accumulator;
5. `drop` — remove the final running product `1`;
6. `Work.Layout.reverseWord` — the walk prepends, so reverse the accumulator.

The per-round step is `Work.MainP.crtStepDiv` (`int t :: int P :: ofList ACC :: acc ↦
int (P/t) :: ofList (triple 0 (P/t) P :: ACC) :: acc`), and the final arithmetic is
`Work.MainP.labCostBoundW`.  Both are proved in separate modules because
`Submission/Work/MainP/labStep.lean` and `Submission/Work/MainP/labFoldDefs.lean` both define
`Work.MainP.labProg`, so no module may import `labStep` together with `labFold`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Small helpers -/

theorem pl_encs_singleton (v : Val) : encs [v] = v.enc := by simp [encs]

theorem pl_vsz_ofList_reverse (xs : List Val) : vsz (ofList xs.reverse) = vsz (ofList xs) := by
  rw [vsz_ofList, vsz_ofList, List.map_reverse, List.sum_reverse, List.length_reverse]

theorem pl_vsz_int_one : vsz (Val.int ((1 : ℕ) : ℤ)) = 3 := by
  rw [Work.MainP.vsz_int, Work.IntLib.isz_eq]
  decide

theorem pl_prod_one_le {l : List ℕ} (h : ∀ t ∈ l, 1 ≤ t) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons t l ih =>
      rw [List.prod_cons]
      have ht : 1 ≤ t := h t (by simp)
      have hl : 1 ≤ l.prod := ih (fun x hx => h x (by simp [hx]))
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ t * l.prod := Nat.mul_le_mul ht hl

/-- A suffix product is at most the whole product (all factors are `≥ 1`). -/
theorem pl_suf_le_prod {ss : List ℕ} (hpos : ∀ s ∈ ss, 1 ≤ s) (i : ℕ) : suf ss i ≤ ss.prod := by
  have hsplit : ss.prod = (ss.take i).prod * (ss.drop i).prod := by
    rw [← List.prod_append, List.take_append_drop]
  have h1 : 1 ≤ (ss.take i).prod := pl_prod_one_le (fun a ha => hpos a (List.mem_of_mem_take ha))
  rw [suf, hsplit]
  exact Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one h1)

theorem pl_suf_le_S {ss : List ℕ} (hpos : ∀ s ∈ ss, 1 ≤ s) {S : ℕ} (hS : S = ss.prod) (i : ℕ) :
    suf ss i ≤ S := by
  rw [hS]; exact pl_suf_le_prod hpos i

/-- The cost of `roll 1` on `int S :: intList l :: rest`. -/
theorem pl_roll_cost (Kroll S : ℕ) (l : List ℕ) (rest : List Val) :
    (fun vs => Kroll * (1 + 1) * ((List.map HvdH.vsz (List.take (1 + 1) vs)).sum + 1))
      (HvdH.Val.int (S : ℤ) :: HvdH.intList l :: rest)
    ≤ Kroll * 2 * (S.size + 2 + HvdH.vsz (HvdH.intList l) + 1) := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Work.MainP.vsz_int, Work.MainP.isz_natCast, Work.MainP.iszN]
  exact le_of_eq (by ring)

/-- Pointwise bound of the fold's per-round budget by the one used in the final cost estimate. -/
theorem pl_summand_le (Ks : ℕ) {ss : List ℕ} (hpos : ∀ s ∈ ss, 1 ≤ s) {S : ℕ}
    (hS : S = ss.prod) (i : ℕ) :
    Ks * ((ss.getD i 0).size + 1) * ((suf ss i).size + 1) + Ks * ((suf ss i).size + 2)
      + (ss.getD i 0).size + 1
    ≤ Ks * ((ss.getD i 0).size + 1) * (S.size + 1) + Ks * (S.size + 2)
      + (ss.getD i 0).size + 1 := by
  have hsz : (suf ss i).size ≤ S.size := Nat.size_le_size (pl_suf_le_S hpos hS i)
  have h1 : Ks * ((ss.getD i 0).size + 1) * ((suf ss i).size + 1)
      ≤ Ks * ((ss.getD i 0).size + 1) * (S.size + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : Ks * ((suf ss i).size + 2) ≤ Ks * (S.size + 2) := Nat.mul_le_mul_left _ (by omega)
  have hAB : Ks * ((ss.getD i 0).size + 1) * ((suf ss i).size + 1) + Ks * ((suf ss i).size + 2)
      ≤ Ks * ((ss.getD i 0).size + 1) * (S.size + 1) + Ks * (S.size + 2) :=
    Nat.add_le_add h1 h2
  omega

/-! ## Cost arithmetic -/

theorem pl_len_le_vsz (ss : List ℕ) : ss.length + 1 ≤ vsz (intList ss) := by
  induction ss with
  | nil => simp [intList, ofList, HvdH.vsz, Val.enc]
  | cons t l ih =>
      rw [List.length_cons, Work.MainP.intList_cons, Work.MainP.vsz_cons, Work.MainP.vsz_intNat]
      have h : 1 ≤ Work.MainP.iszN t := by simp [Work.MainP.iszN]
      omega

theorem pl_sum_le_vsz (ss : List ℕ) :
    (∑ i ∈ Finset.range ss.length, ((ss.getD i 0).size + 1)) ≤ vsz (intList ss) := by
  induction ss with
  | nil => simp [intList, ofList, HvdH.vsz, Val.enc]
  | cons t l ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [Work.MainP.intList_cons, Work.MainP.vsz_cons, Work.MainP.vsz_intNat]
      have h : Work.MainP.iszN t = t.size + 2 := rfl
      omega

/-- The pure arithmetic closing the cost estimate of the place-value table word. -/
theorem pl_cost_step (Kroll Kpush Kswap Kf Ks Kdrop Krev A B n C0 D R : ℕ)
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hn : n + 1 ≤ A)
    (hR : A * (B + 1) + (n + 1) * (B + 1) + 1 ≤ R)
    (hC0 : C0 ≤ (n + 1) * (3 * (B + 2) + 4) + 1)
    (hD : D ≤ 3 * (Ks * (B + 1)) * A + A) :
    Kroll * 2 * (B + 2 + A + 1) + 16 * (A + 1) + Kpush * 2 + Kswap * (B + 4)
      + Kf * (1 + D) + Kdrop * 4 + Krev * (C0 + 1)
      ≤ 64 * (Kroll + Kpush + Kswap + Kf + Kf * Ks + Kdrop + Krev + 1) * R := by
  have hAB1 : A * (B + 1) ≤ R := by omega
  have hR1 : 1 ≤ R := by omega
  have hRA : A ≤ R := by
    have h1 : A ≤ A * (B + 1) := by
      calc A = A * 1 := by ring
        _ ≤ A * (B + 1) := Nat.mul_le_mul_left A (by omega)
    omega
  have hRB : B + 1 ≤ R := by
    have h1 : B + 1 ≤ (n + 1) * (B + 1) := Nat.le_mul_of_pos_left (B + 1) (by omega)
    omega
  have hAB : B + 2 + A + 1 ≤ 4 * R := by omega
  have hB4 : B + 4 ≤ 5 * R := by omega
  have hA2 : A + 1 ≤ 2 * R := by omega
  have hC0' : C0 + 1 ≤ 9 * R := by
    have h1 : 3 * (B + 2) + 4 ≤ 7 * (B + 1) := by omega
    have h2 : (n + 1) * (3 * (B + 2) + 4) ≤ (n + 1) * (7 * (B + 1)) :=
      Nat.mul_le_mul_left _ h1
    have h3 : (n + 1) * (7 * (B + 1)) ≤ 7 * (A * (B + 1)) := by
      have h3a : (n + 1) * (7 * (B + 1)) ≤ A * (7 * (B + 1)) :=
        Nat.mul_le_mul_right (7 * (B + 1)) hn
      have h3b : A * (7 * (B + 1)) = 7 * (A * (B + 1)) := by ring
      omega
    have h4 : 7 * (A * (B + 1)) ≤ 7 * R := Nat.mul_le_mul_left 7 hAB1
    omega
  have hD0 : 3 * (Ks * (B + 1)) * A ≤ 3 * Ks * R := by
    have h1 : 3 * (Ks * (B + 1)) * A = 3 * Ks * (A * (B + 1)) := by ring
    rw [h1]
    exact Nat.mul_le_mul_left (3 * Ks) hAB1
  have hD' : 1 + D ≤ (3 * Ks + 2) * R := by
    nlinarith [hD, hD0, hRA, hR1, Nat.zero_le Ks, Nat.zero_le R]
  have t1 : Kroll * 2 * (B + 2 + A + 1) ≤ 8 * Kroll * R := by
    nlinarith [hAB, Nat.zero_le Kroll]
  have t2 : 16 * (A + 1) ≤ 32 * R := by nlinarith [hA2]
  have t3 : Kpush * 2 ≤ 2 * Kpush * R := by nlinarith [hR1, Nat.zero_le Kpush]
  have t4 : Kswap * (B + 4) ≤ 5 * Kswap * R := by nlinarith [hB4, Nat.zero_le Kswap]
  have t5 : Kf * (1 + D) ≤ 5 * (Kf * Ks + Kf) * R := by
    nlinarith [hD', Nat.zero_le Kf, Nat.zero_le Ks, Nat.zero_le R, Nat.zero_le D]
  have t6 : Kdrop * 4 ≤ 4 * Kdrop * R := by nlinarith [hR1, Nat.zero_le Kdrop]
  have t7 : Krev * (C0 + 1) ≤ 9 * Krev * R := by nlinarith [hC0', Nat.zero_le Krev]
  have hQ : 8 * Kroll + 32 + 2 * Kpush + 5 * Kswap + 5 * (Kf * Ks + Kf) + 4 * Kdrop + 9 * Krev
      ≤ 64 * (Kroll + Kpush + Kswap + Kf + Kf * Ks + Kdrop + Krev + 1) := by omega
  have hdist : 8 * Kroll * R + 32 * R + 2 * Kpush * R + 5 * Kswap * R
      + 5 * (Kf * Ks + Kf) * R + 4 * Kdrop * R + 9 * Krev * R
      = (8 * Kroll + 32 + 2 * Kpush + 5 * Kswap + 5 * (Kf * Ks + Kf) + 4 * Kdrop + 9 * Krev) * R := by
    ring
  have hsum7 : Kroll * 2 * (B + 2 + A + 1) + 16 * (A + 1) + Kpush * 2 + Kswap * (B + 4)
      + Kf * (1 + D) + Kdrop * 4 + Krev * (C0 + 1)
      ≤ 8 * Kroll * R + 32 * R + 2 * Kpush * R + 5 * Kswap * R
        + 5 * (Kf * Ks + Kf) * R + 4 * Kdrop * R + 9 * Krev * R := by
    linarith [t1, t2, t3, t4, t5, t6, t7]
  rw [hdist] at hsum7
  exact le_trans hsum7 (Nat.mul_le_mul_right R hQ)

theorem pl_labCostBound (Kroll Kpush Kswap Kf Ks Kdrop Krev : ℕ) :
    ∃ K : ℕ, ∀ (ss : List ℕ) (S : ℕ), (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
      Kroll * 2 * (S.size + 2 + HvdH.vsz (HvdH.intList ss) + 1)
      + 16 * (HvdH.vsz (HvdH.intList ss) + 1)
      + Kpush * 2
      + Kswap * (S.size + 4)
      + Kf * (1 + ∑ i ∈ Finset.range ss.length,
          (Ks * ((ss.getD i 0).size + 1) * (S.size + 1) + Ks * (S.size + 2)
            + (ss.getD i 0).size + 1))
      + Kdrop * 4
      + Krev * (HvdH.vsz (HvdH.ofList (Work.MainP.canon ss 0)) + 1)
      ≤ K * (HvdH.vsz (HvdH.intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1) + 1) := by
  refine ⟨64 * (Kroll + Kpush + Kswap + Kf + Kf * Ks + Kdrop + Krev + 1), ?_⟩
  intro ss S hpos hS
  subst hS
  have hA1 : 1 ≤ HvdH.vsz (HvdH.intList ss) := Work.MainP.one_le_vsz _
  have hB1 : 1 ≤ (ss.prod).size := by
    have h : 1 ≤ ss.prod := pl_prod_one_le hpos
    have h2 := Nat.size_le_size h
    rw [Nat.size_one] at h2
    exact h2
  have hlen : ss.length + 1 ≤ HvdH.vsz (HvdH.intList ss) := pl_len_le_vsz ss
  have hsum : (∑ i ∈ Finset.range ss.length, ((ss.getD i 0).size + 1))
      ≤ HvdH.vsz (HvdH.intList ss) := pl_sum_le_vsz ss
  have hc0 : HvdH.vsz (HvdH.ofList (Work.MainP.canon ss 0))
      ≤ (ss.length + 1) * (3 * ((ss.prod).size + 2) + 4) + 1 := by
    have h := (crtLabSum (ss := ss) (S := ss.prod) rfl hpos 0).2.2.2.2.2
    rwa [Work.MainP.Est_zero] at h
  have hD : (∑ i ∈ Finset.range ss.length,
        (Ks * ((ss.getD i 0).size + 1) * ((ss.prod).size + 1) + Ks * ((ss.prod).size + 2)
          + (ss.getD i 0).size + 1))
      ≤ 3 * (Ks * ((ss.prod).size + 1)) * HvdH.vsz (HvdH.intList ss)
        + HvdH.vsz (HvdH.intList ss) := by
    have hpw : ∀ i ∈ Finset.range ss.length,
        (Ks * ((ss.getD i 0).size + 1) * ((ss.prod).size + 1) + Ks * ((ss.prod).size + 2)
          + (ss.getD i 0).size + 1)
        ≤ (3 * (Ks * ((ss.prod).size + 1)) + 1) * ((ss.getD i 0).size + 1) := by
      intro i _
      have hRHS : (3 * (Ks * ((ss.prod).size + 1)) + 1) * ((ss.getD i 0).size + 1)
          = 3 * ((Ks * ((ss.prod).size + 1)) * ((ss.getD i 0).size + 1))
            + ((ss.getD i 0).size + 1) := by ring
      have ha : Ks * ((ss.getD i 0).size + 1) * ((ss.prod).size + 1)
          = (Ks * ((ss.prod).size + 1)) * ((ss.getD i 0).size + 1) := by ring
      have h2 : Ks * ((ss.prod).size + 2)
          ≤ 2 * ((Ks * ((ss.prod).size + 1)) * ((ss.getD i 0).size + 1)) := by
        have h2a : Ks * ((ss.prod).size + 2) ≤ Ks * (2 * ((ss.prod).size + 1)) :=
          Nat.mul_le_mul_left Ks (by omega)
        have h2b : Ks * (2 * ((ss.prod).size + 1)) = 2 * (Ks * ((ss.prod).size + 1)) := by ring
        rw [h2b] at h2a
        calc Ks * ((ss.prod).size + 2)
            ≤ 2 * (Ks * ((ss.prod).size + 1)) := h2a
          _ = (2 * (Ks * ((ss.prod).size + 1))) * 1 := by ring
          _ ≤ (2 * (Ks * ((ss.prod).size + 1))) * ((ss.getD i 0).size + 1) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = 2 * ((Ks * ((ss.prod).size + 1)) * ((ss.getD i 0).size + 1)) := by ring
      rw [hRHS, ha]
      omega
    calc (∑ i ∈ Finset.range ss.length,
          (Ks * ((ss.getD i 0).size + 1) * ((ss.prod).size + 1) + Ks * ((ss.prod).size + 2)
            + (ss.getD i 0).size + 1))
        ≤ ∑ i ∈ Finset.range ss.length,
            (3 * (Ks * ((ss.prod).size + 1)) + 1) * ((ss.getD i 0).size + 1) :=
          Finset.sum_le_sum hpw
      _ = (3 * (Ks * ((ss.prod).size + 1)) + 1)
            * (∑ i ∈ Finset.range ss.length, ((ss.getD i 0).size + 1)) := by
          rw [← Finset.mul_sum]
      _ ≤ (3 * (Ks * ((ss.prod).size + 1)) + 1) * HvdH.vsz (HvdH.intList ss) :=
          Nat.mul_le_mul_left _ hsum
      _ = 3 * (Ks * ((ss.prod).size + 1)) * HvdH.vsz (HvdH.intList ss)
            + HvdH.vsz (HvdH.intList ss) := by ring
  exact pl_cost_step Kroll Kpush Kswap Kf Ks Kdrop Krev _ _ _ _ _ _
    hA1 hB1 hlen (le_refl _) hc0 hD

/-! ## The task -/

theorem crtLabTabW (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (ss : List ℕ) (S : ℕ),
    (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
    HvdH.WordR main prog
      (fun vs => ∃ rest, vs = HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: rest)
      (fun vs out => ∃ rest, vs = HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: rest ∧
        out = HvdH.ofList (Work.MainP.canon ss 0) :: rest)
      (fun _ => K * (HvdH.vsz (HvdH.intList ss) * (S.size + 1) + (ss.length + 1) * (S.size + 1) + 1)) := by
  obtain ⟨rollP, Kroll, hroll⟩ := hK.roll
  obtain ⟨pushVP, Kpush, hpush⟩ := hK.pushVal
  obtain ⟨swapP, Kswap, hswap⟩ := hK.swap
  obtain ⟨dropP, Kdrop, hdrop⟩ := hK.drop
  obtain ⟨stepP, Ks, hstep⟩ := crtStepDiv hK hI
  obtain ⟨foldP, Kf, hfold⟩ := labFold stepP
  obtain ⟨revP, Krev, hrev⟩ := Work.Layout.reverseWord
  obtain ⟨Kc, hKc⟩ := pl_labCostBound Kroll Kpush Kswap Kf Ks Kdrop Krev
  refine ⟨Work.Layout.seqs [rollP 1, Work.Layout.mvVal 0 7 14 15, pushVP HvdH.Val.nil,
    swapP, foldP, dropP, revP], Kc, ?_⟩
  intro main ss S hpos hS vs hpre s R hs0
  obtain ⟨rest, rfl⟩ := hpre
  -- ============================================================
  -- (1) `roll 1`: the modulus list moves to the top
  -- ============================================================
  obtain ⟨out₁, s₁, n₁, hpost₁, hev₁, hn₁, hstk₁, hoth₁⟩ :=
    hroll main 1 (HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: rest) (by simp) s R hs0
  have hout₁ : out₁ = HvdH.intList ss :: HvdH.Val.int (S : ℤ) :: rest := by
    rw [hpost₁]; simp
  have hb₁ : n₁ ≤ Kroll * 2 * (S.size + 2 + HvdH.vsz (HvdH.intList ss) + 1) :=
    le_trans hn₁ (pl_roll_cost Kroll S ss rest)
  have hstk₁' : s₁.stk 0 = (HvdH.intList ss).enc ++
      ((HvdH.Val.int (S : ℤ)).enc ++ (HvdH.encs rest ++ R)) := by
    rw [hstk₁, hout₁]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  -- ============================================================
  -- (2) move the list value to the pile (stack 7)
  -- ============================================================
  obtain ⟨s₂, n₂, hev₂, hn₂, hstk₂0, hstk₂7, hstk₂14, hstk₂15, hoth₂⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 7) (c := 14) (d := 15)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₁.reg) (X := s₁.stk) (v := HvdH.intList ss)
      (A := (HvdH.Val.int (S : ℤ)).enc ++ (HvdH.encs rest ++ R)) (B := s₁.stk 7)
      hstk₁' rfl
  have hb₂ : n₂ ≤ 16 * (HvdH.vsz (HvdH.intList ss) + 1) := hn₂
  -- ============================================================
  -- (3) push `nil`: the empty accumulator
  -- ============================================================
  obtain ⟨out₃, s₃, n₃, hpost₃, hev₃, hn₃, hstk₃, hoth₃⟩ :=
    hpush main HvdH.Val.nil (HvdH.Val.int (S : ℤ) :: rest) trivial s₂ R (by
      rw [hstk₂0]
      simp only [Work.Kernel.encs_cons, List.append_assoc])
  have hout₃ : out₃ = HvdH.Val.nil :: HvdH.Val.int (S : ℤ) :: rest := hpost₃
  have hb₃ : n₃ ≤ Kpush * 2 := by
    have h := hn₃
    change n₃ ≤ Kpush * (HvdH.vsz HvdH.Val.nil + 1) at h
    have h2 : HvdH.vsz HvdH.Val.nil + 1 ≤ 2 := by simp [HvdH.vsz, Val.enc]
    exact le_trans h (Nat.mul_le_mul_left Kpush h2)
  have hstk₃' : s₃.stk 0 = (HvdH.Val.nil).enc ++
      ((HvdH.Val.int (S : ℤ)).enc ++ (HvdH.encs rest ++ R)) := by
    rw [hstk₃, hout₃]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  -- ============================================================
  -- (4) swap: `int S :: nil :: rest`
  -- ============================================================
  obtain ⟨out₄, s₄, n₄, hpost₄, hev₄, hn₄, hstk₄, hoth₄⟩ :=
    hswap main (HvdH.Val.nil :: HvdH.Val.int (S : ℤ) :: rest) (by simp) s₃ R (by
      rw [hstk₃']
      simp only [Work.Kernel.encs_cons, List.append_assoc])
  obtain ⟨a₄, b₄, rest₄, hvs₄, hout₄⟩ := hpost₄
  have hout₄' : out₄ = HvdH.Val.int (S : ℤ) :: HvdH.Val.nil :: rest := by
    rw [hout₄]
    simp only [List.cons.injEq] at hvs₄
    obtain ⟨ha, hb, hr⟩ := hvs₄
    subst ha; subst hb; rw [← hr]
  have hb₄ : n₄ ≤ Kswap * (S.size + 4) := by
    have h := hn₄
    change n₄ ≤ Kswap * (HvdH.vsz (HvdH.Val.nil) + HvdH.vsz (HvdH.Val.int (S : ℤ)) + 1) at h
    have h2 : HvdH.vsz (HvdH.Val.nil) + HvdH.vsz (HvdH.Val.int (S : ℤ)) + 1 ≤ S.size + 4 := by
      rw [HvdH.vsz, Val.enc, List.length_cons, List.length_nil, Work.MainP.vsz_int,
        Work.MainP.isz_natCast, Work.MainP.iszN]
      omega
    exact le_trans h (Nat.mul_le_mul_left Kswap h2)
  have hstk₄' : s₄.stk 0 = (HvdH.Val.int (S : ℤ)).enc ++
      ((HvdH.Val.nil).enc ++ (HvdH.encs rest ++ R)) := by
    rw [hstk₄, hout₄']
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  -- ============================================================
  -- (5) the walk
  -- ============================================================
  have hstep' : ∀ i, i < ss.length → ∀ acc' : List Val,
      WordR main stepP
        (fun vs => vs = Val.int ((ss.getD i 0 : ℕ) : ℤ) :: Val.int ((suf ss i : ℕ) : ℤ) ::
          ofList (((canon ss 0).take i).reverse) :: acc')
        (fun _ out => out = Val.int ((suf ss (i+1) : ℕ) : ℤ) ::
          ofList (((canon ss 0).take (i+1)).reverse) :: acc')
        (fun _ => Ks * ((ss.getD i 0).size + 1) * ((suf ss i).size + 1) +
          Ks * ((suf ss i).size + 2)) := by
    intro i hi acc'
    have hmem : ss.getD i 0 ∈ ss := by
      rw [List.getD_eq_getElem ss 0 hi]; exact List.getElem_mem hi
    have h1 := hstep main (ss.getD i 0) (suf ss i) (hpos _ hmem)
      (((canon ss 0).take i).reverse) acc'
    have hdiv : ((suf ss i / ss.getD i 0 : ℕ) : ℤ) = ((suf ss (i+1) : ℕ) : ℤ) := by
      have h2 : suf ss i = ss.getD i 0 * suf ss (i+1) := by
        rw [suf_succ hi, List.getD_eq_getElem ss 0 hi]
      have h3 : 0 < ss.getD i 0 := by
        rw [List.getD_eq_getElem ss 0 hi]
        exact lt_of_lt_of_le Nat.zero_lt_one (hpos ss[i] (List.getElem_mem hi))
      rw [h2, Nat.mul_div_cancel_left (suf ss (i+1)) h3]
    have hAC : ((canon ss 0).take (i+1)).reverse =
        entry ss i :: ((canon ss 0).take i).reverse := by
      rw [take_canon_succ ss hi, List.reverse_append, List.reverse_singleton, List.singleton_append]
    refine hK.conseq main stepP _ _ _ _ _ _ h1 (fun vs hvs => hvs) ?_ ?_
    · intro vs out hvs hout
      rw [hout, hdiv, hAC]
      rfl
    · intro vs _
      exact le_of_eq (by ring)
  set Y7 : List Glyph := s₁.stk 7 with hY7
  have hpre₅7 : s₄.stk 7 = (HvdH.intList ss).enc ++ Y7 := by
    rw [hoth₄ 7 (by decide), hoth₃ 7 (by decide), hstk₂7]
  have hpre₅ : s₄.stk 0 = (HvdH.Val.int (suf ss 0)).enc ++
      (HvdH.ofList (((canon ss 0).take 0).reverse)).enc ++ HvdH.encs rest ++ R := by
    have h4 : s₄.stk 0 = (HvdH.Val.int (S : ℤ)).enc ++ (HvdH.Val.nil).enc ++
        HvdH.encs rest ++ R := by
      simpa only [List.append_assoc] using hstk₄'
    rw [h4, show suf ss 0 = S from by simp [hS],
      show ((canon ss 0).take 0).reverse = ([] : List Val) from by
        rw [List.take_zero, List.reverse_nil]]
    rfl
  obtain ⟨s₅, n₅, hev₅, hn₅, hstk₅, hstk₅7, hoth₅⟩ :=
    hfold main ss (fun i => suf ss i) (fun i => ((canon ss 0).take i).reverse)
      (fun i => Ks * ((ss.getD i 0).size + 1) * ((suf ss i).size + 1)
        + Ks * ((suf ss i).size + 2))
      hstep' rest R Y7 s₄.reg s₄.stk hpre₅ hpre₅7
  have hstk₅' : s₅.stk 0 = (HvdH.Val.int ((1 : ℕ) : ℤ)).enc ++
      (HvdH.ofList ((Work.MainP.canon ss 0).reverse)).enc ++ HvdH.encs rest ++ R := by
    rw [hstk₅,
      show suf ss ss.length = (1 : ℕ) from suf_length ss,
      show ((canon ss 0).take ss.length).reverse = (Work.MainP.canon ss 0).reverse from by
        rw [show ss.length = (Work.MainP.canon ss 0).length from
          (Work.MainP.canon_length ss 0).symm, List.take_length]]
  have hb₅ : n₅ ≤ Kf * (1 + ∑ i ∈ Finset.range ss.length,
      (Ks * ((ss.getD i 0).size + 1) * (S.size + 1) + Ks * (S.size + 2)
        + (ss.getD i 0).size + 1)) := by
    refine le_trans hn₅ (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ 1))
    exact Finset.sum_le_sum (fun i _ => pl_summand_le Ks hpos hS i)
  -- ============================================================
  -- (6) drop the final running product
  -- ============================================================
  obtain ⟨out₆, s₆, n₆, hpost₆, hev₆, hn₆, hstk₆, hoth₆⟩ :=
    hdrop main (HvdH.Val.int ((1 : ℕ) : ℤ) :: HvdH.ofList ((Work.MainP.canon ss 0).reverse) :: rest)
      (by simp) s₅ R (by
        rw [hstk₅']
        simp only [Work.Kernel.encs_cons, List.append_assoc])
  obtain ⟨v₆, rest₆, hvs₆, hout₆⟩ := hpost₆
  have hout₆' : out₆ = HvdH.ofList ((Work.MainP.canon ss 0).reverse) :: rest := by
    rw [hout₆]
    simp only [List.cons.injEq] at hvs₆
    obtain ⟨hv, hr⟩ := hvs₆
    rw [← hr]
  have hb₆ : n₆ ≤ Kdrop * 4 := by
    have h := hn₆
    change n₆ ≤ Kdrop * (HvdH.vsz (HvdH.Val.int ((1 : ℕ) : ℤ)) + 1) at h
    rw [pl_vsz_int_one] at h
    exact h
  have hstk₆' : s₆.stk 0 = (HvdH.ofList ((Work.MainP.canon ss 0).reverse)).enc ++
      (HvdH.encs rest ++ R) := by
    rw [hstk₆, hout₆']
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  -- ============================================================
  -- (7) reverse the accumulator
  -- ============================================================
  obtain ⟨out₇, s₇, n₇, hpost₇, hev₇, hn₇, hstk₇, hoth₇⟩ :=
    hrev main ((Work.MainP.canon ss 0).reverse)
      (HvdH.ofList ((Work.MainP.canon ss 0).reverse) :: rest) ⟨rest, rfl⟩ s₆ R (by
        rw [hstk₆']
        simp only [Work.Kernel.encs_cons, List.append_assoc])
  obtain ⟨r₇, hr₇, hout₇⟩ := hpost₇
  have hout₇' : out₇ = HvdH.ofList (Work.MainP.canon ss 0) :: rest := by
    have hr : r₇ = rest := by
      injection hr₇ with _ h
      exact h.symm
    rw [hout₇, hr, List.reverse_reverse]
  have hb₇ : n₇ ≤ Krev * (HvdH.vsz (HvdH.ofList (Work.MainP.canon ss 0)) + 1) := by
    have h := hn₇
    change n₇ ≤ Krev * (HvdH.vsz (HvdH.ofList ((Work.MainP.canon ss 0).reverse)) + 1) at h
    rw [pl_vsz_ofList_reverse] at h
    exact h
  -- ============================================================
  -- the Eval chain and the cost
  -- ============================================================
  have hevRoll : Work.Layout.Ev main (rollP 1) s s₁ n₁ := ⟨n₁, hev₁, le_rfl⟩
  have hevMv : Work.Layout.Ev main (Work.Layout.mvVal 0 7 14 15) s₁ s₂ n₂ := by
    simpa using hev₂
  have hevPush : Work.Layout.Ev main (pushVP HvdH.Val.nil) s₂ s₃ n₃ := ⟨n₃, hev₃, le_rfl⟩
  have hevSwap : Work.Layout.Ev main swapP s₃ s₄ n₄ := ⟨n₄, hev₄, le_rfl⟩
  have hevFold : Work.Layout.Ev main foldP s₄ s₅ n₅ := by simpa using hev₅
  have hevDrop : Work.Layout.Ev main dropP s₅ s₆ n₆ := ⟨n₆, hev₆, le_rfl⟩
  have hevRev : Work.Layout.Ev main revP s₆ s₇ n₇ := ⟨n₇, hev₇, le_rfl⟩
  have hall : Work.Layout.Ev main (Work.Layout.seqs [rollP 1, Work.Layout.mvVal 0 7 14 15,
      pushVP HvdH.Val.nil, swapP, foldP, dropP, revP]) s s₇
      (n₁ + (n₂ + (n₃ + (n₄ + (n₅ + (n₆ + n₇)))))) :=
    Work.Layout.Ev.seqs_cons hevRoll
      (Work.Layout.Ev.seqs_cons hevMv
        (Work.Layout.Ev.seqs_cons hevPush
          (Work.Layout.Ev.seqs_cons hevSwap
            (Work.Layout.Ev.seqs_cons hevFold
              (Work.Layout.Ev.seqs_cons hevDrop hevRev)))))
  obtain ⟨nE, hevE, hnE⟩ := hall
  have htot : nE ≤ Kroll * 2 * (S.size + 2 + HvdH.vsz (HvdH.intList ss) + 1)
      + 16 * (HvdH.vsz (HvdH.intList ss) + 1) + Kpush * 2 + Kswap * (S.size + 4)
      + Kf * (1 + ∑ i ∈ Finset.range ss.length,
          (Ks * ((ss.getD i 0).size + 1) * (S.size + 1) + Ks * (S.size + 2)
            + (ss.getD i 0).size + 1))
      + Kdrop * 4 + Krev * (HvdH.vsz (HvdH.ofList (Work.MainP.canon ss 0)) + 1) := by
    omega
  refine ⟨HvdH.ofList (Work.MainP.canon ss 0) :: rest, s₇, nE, ⟨rest, rfl, rfl⟩, hevE,
    le_trans htot (hKc ss S hpos hS), ?_, ?_⟩
  · rw [hstk₇, hout₇']
  · intro k hk
    rw [hoth₇ k hk, hoth₆ k hk]
    by_cases hk7 : k = 7
    · rw [hk7, hstk₅7, hY7, hoth₁ 7 (by decide)]
    · rw [hoth₅ k hk hk7, hoth₄ k hk, hoth₃ k hk]
      by_cases hk14 : k = 14
      · rw [hk14, hstk₂14, hoth₁ 14 (by decide)]
      · by_cases hk15 : k = 15
        · rw [hk15, hstk₂15, hoth₁ 15 (by decide)]
        · rw [hoth₂ k hk hk7 hk14 hk15, hoth₁ k hk]

end Work.MainP
