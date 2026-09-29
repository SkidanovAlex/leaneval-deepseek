import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.roll
import Submission.Work.Layout.Base
import Submission.Work.IntLib.Raw
import Submission.Work.Transform.pwBase
import Submission.Work.Transform.pwKit
import Submission.Work.Transform.pwCopyListBlock
import Submission.Work.Transform.pwRevAcc
import Submission.Work.Transform.pwMaxPhase

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform

open HvdH
open Work.Kernel

/-! ## Helpers for the assembly of the parameter word -/

/-- `j ∉ S` and `a ∈ S` give `j ≠ a` (used to discharge the frame conditions of the phase words). -/
theorem pwAux_neq {j a : HvdH.Stk} {S : Finset HvdH.Stk} (h : j ∉ S) (ha : a ∈ S) : j ≠ a :=
  fun hh => h (hh.symm ▸ ha)

/-- Cost step: `n ≤ K*(X+1)`, `X+1 ≤ c*S`, `c*K ≤ Kt` give `n ≤ Kt*S`. -/
theorem pwAux_cost_step {n K X c S Kt : ℕ} (hn : n ≤ K * (X + 1)) (hX : X + 1 ≤ c * S)
    (hK : c * K ≤ Kt) : n ≤ Kt * S := by
  calc n ≤ K * (X + 1) := hn
    _ ≤ K * (c * S) := Nat.mul_le_mul_left K hX
    _ = (c * K) * S := by ring
    _ ≤ Kt * S := Nat.mul_le_mul_right S hK

/-- Accumulation step for the cost of a `seq` of phase words. -/
theorem pwAux_acc {a b Kt S i : ℕ} (ha : a ≤ (i * Kt) * S) (hb : b ≤ Kt * S) :
    a + b ≤ ((i + 1) * Kt) * S := by
  have h : a + b ≤ (i * Kt) * S + Kt * S := Nat.add_le_add ha hb
  calc a + b ≤ (i * Kt) * S + Kt * S := h
    _ = ((i + 1) * Kt) * S := by ring

/-- `a ≤ a^K` for `a ≥ 1`, `K ≥ 1`. -/
theorem pwAux_le_self_pow (a K : ℕ) (ha : 1 ≤ a) (hK : 1 ≤ K) : a ≤ a ^ K := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  clear hK
  induction k with
  | zero => simpa using ha
  | succ j ih =>
    calc a ≤ a ^ (j + 1) := ih
      _ ≤ a ^ (j + 1) * a := by
            have h : a ^ (j + 1) * 1 ≤ a ^ (j + 1) * a := Nat.mul_le_mul_left _ ha
            simpa using h
      _ = a ^ (j + 1 + 1) := (pow_succ a (j + 1)).symm

/-- Final absorption: a cost bound `n ≤ C*(s+p+1)` with `C ≤ K` and `1 ≤ s` is dominated by
the target `K * (s * (p+1)^K) + K`. -/
theorem pwAux_absorb {n C K s p : ℕ} (hs : 1 ≤ s) (hC : C ≤ K)
    (hn : n ≤ C * (s + p + 1)) : n ≤ K * (s * (p + 1) ^ K) + K := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have hC0 : C = 0 := by omega
    subst hC0
    simp only [Nat.zero_mul, Nat.zero_add] at hn
    have hn0 : n = 0 := by omega
    subst hn0
    simp
  · have hp_le : ∀ q : ℕ, q ≤ s * q := by
      intro q
      have h := Nat.mul_le_mul_right q hs
      simpa [Nat.mul_comm] using h
    have hsp : s + p ≤ s * (p + 1) ^ K := by
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp; simp
      · have h1 : p + 1 ≤ (p + 1) ^ K := pwAux_le_self_pow (p + 1) K (by omega) (by omega)
        have h2 : s * (p + 1) ≤ s * (p + 1) ^ K := Nat.mul_le_mul_left s h1
        have h3 : s * (p + 1) = s * p + s := by ring
        have h4 : p ≤ s * p := hp_le p
        omega
    calc n ≤ C * (s + p + 1) := hn
      _ ≤ K * (s + p + 1) := Nat.mul_le_mul_right _ hC
      _ ≤ K * (s * (p + 1) ^ K + 1) := Nat.mul_le_mul_left K (by omega)
      _ = K * (s * (p + 1) ^ K) + K := by ring

set_option maxHeartbeats 400000 in
/-- The frame condition of the assembled word, from the eight explicit restorations plus the
generic invariant for the stacks outside `{0,…,8}`. -/
theorem pwAux_frame (u s : HvdH.State)
    (h1 : u.stk 1 = s.stk 1) (h2 : u.stk 2 = s.stk 2) (h3 : u.stk 3 = s.stk 3)
    (h4 : u.stk 4 = s.stk 4) (h5 : u.stk 5 = s.stk 5) (h6 : u.stk 6 = s.stk 6)
    (h7 : u.stk 7 = s.stk 7) (h8 : u.stk 8 = s.stk 8)
    (hg : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) → u.stk j = s.stk j) :
    ∀ k : HvdH.Stk, k ≠ 0 → u.stk k = s.stk k := by
  intro k hk
  by_cases hmem : k ∈ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk)
  · have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      tauto
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4, h5, h6, h7, h8]
  · exact hg k hmem

set_option maxHeartbeats 2000000 in
/-- The parameter word of Theorem 3.1: from the input `int p :: intList ts :: cvecVal zs`
compute `r = lmax ts` (the largest entry, = the last one for an ascending list) and
`ts' = ts.dropLast` (the first `D-1` entries); everything else is preserved.
`ts.sum` is `Σ tᵢ`, `ts.prod` is `∏ tᵢ`.  Cost `K·(ts.sum·(p+1)^K + 1)`. -/
theorem paramWord : HvdH.KernelLib → HvdH.IntLib → ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p : ℕ) (ts : List ℕ) (zs : List (ℤ × ℤ)) (R : List HvdH.Val),
      ts ≠ [] → (∀ t ∈ ts, 0 < t) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.intList ts :: HvdH.cvecVal zs :: R)
        (fun vs out => out = HvdH.Val.int p :: HvdH.Val.int (HvdH.lmax ts) ::
          HvdH.intList ts.dropLast :: HvdH.intList ts :: HvdH.cvecVal zs :: R)
        (fun _ => K * ((ts.sum : ℕ) * (p + 1) ^ K) + K) := by
  intro _ _
  -- #### the phase words
  obtain ⟨pcp1, Kcp1, hcp1⟩ :=
    pwCopyListBlock (0 : HvdH.Stk) 1 7 (by decide) (by decide) (by decide)
  obtain ⟨pcp3, Kcp3, hcp3⟩ :=
    pwCopyListBlock (0 : HvdH.Stk) 3 7 (by decide) (by decide) (by decide)
  obtain ⟨pmx, Kmx, hmx⟩ := pwMaxPhase (1 : HvdH.Stk) 2 (by decide)
  obtain ⟨pra1, Kra1, hra1⟩ := pwRevAcc (3 : HvdH.Stk) 4 5 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨pra2, Kra2, hra2⟩ := pwRevAcc (4 : HvdH.Stk) 5 6 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨pdc, Kdc, hdc⟩ := Pw.pk_pwDropCell (4 : HvdH.Stk)
  obtain ⟨pus2, hpus2⟩ := Pw.pk_pushGlyphWord (2 : HvdH.Stk) Pw.gM
  obtain ⟨pus7, hpus7⟩ := Pw.pk_pushGlyphWord (7 : HvdH.Stk) Pw.gM
  obtain ⟨puse, hpuse⟩ := Pw.pk_pushGlyphWord (0 : HvdH.Stk) HvdH.Glyph.iend
  obtain ⟨pusp, hpusp⟩ := Pw.pk_pushGlyphWord (0 : HvdH.Stk) HvdH.Glyph.pos
  let Kt : ℕ := 1000 * (Kcp1 + Kcp3 + Kmx + Kra1 + Kra2 + Kdc + 1) + 10000
  have hKtdef : Kt = 1000 * (Kcp1 + Kcp3 + Kmx + Kra1 + Kra2 + Kdc + 1) + 10000 := rfl
  -- #### the assembled program
  let q1 : HvdH.Cmd := Work.Kernel.roll_prog 1
  let q2 : HvdH.Cmd := .seq q1 pcp1
  let q3 : HvdH.Cmd := .seq q2 pcp3
  let q4 : HvdH.Cmd := .seq q3 pus2
  let q5 : HvdH.Cmd := .seq q4 pmx
  let q6 : HvdH.Cmd := .seq q5 (.pop (1 : HvdH.Stk) (0 : HvdH.Reg))
  let q7 : HvdH.Cmd := .seq q6 (Pw.revMarked (2 : HvdH.Stk) 8 (0 : HvdH.Reg) 1)
  let q8 : HvdH.Cmd := .seq q7 pra1
  let q9 : HvdH.Cmd := .seq q8 (.pop (3 : HvdH.Stk) (0 : HvdH.Reg))
  let q10 : HvdH.Cmd := .seq q9 pdc
  let q11 : HvdH.Cmd := .seq q10 pra2
  let q12 : HvdH.Cmd := .seq q11 (.pop (4 : HvdH.Stk) (0 : HvdH.Reg))
  let q13 : HvdH.Cmd := .seq q12 pus7
  let q14 : HvdH.Cmd := .seq q13 (Pw.tLoop (5 : HvdH.Stk) Pw.gM (7 : HvdH.Stk) (0 : HvdH.Reg))
  let q15 : HvdH.Cmd := .seq q14 (.pop (5 : HvdH.Stk) (0 : HvdH.Reg))
  let q16 : HvdH.Cmd := .seq q15 (Pw.tLoop (7 : HvdH.Stk) Pw.gM (0 : HvdH.Stk) (0 : HvdH.Reg))
  let q17 : HvdH.Cmd := .seq q16 (.pop (7 : HvdH.Stk) (0 : HvdH.Reg))
  let q18 : HvdH.Cmd := .seq q17 puse
  let q19 : HvdH.Cmd := .seq q18 (Pw.tLoop (8 : HvdH.Stk) Pw.gM (0 : HvdH.Stk) (0 : HvdH.Reg))
  let q20 : HvdH.Cmd := .seq q19 pusp
  let q21 : HvdH.Cmd := .seq q20 (.pop (8 : HvdH.Stk) (0 : HvdH.Reg))
  let q22 : HvdH.Cmd := .seq q21 (Work.Kernel.roll_prog 3)
  refine ⟨q22, 22 * Kt, ?_⟩
  intro main p ts zs R hts hpos vs hvs s Rg hs0
  subst hvs
  -- #### side conditions
  obtain ⟨hsum1, hvszTs, hvszDL, hvszRev, hvszP, hSle, hiszLast, hlmaxSz, hcomb, hdlSum⟩ :=
    Pw.pk_sizes ts p hts hpos
  have hS1 : 1 ≤ ts.sum + p + 1 := by omega
  have hS2 : 2 ≤ ts.sum + p + 1 := by omega
  have hKt1 : 1 ≤ Kt := by rw [hKtdef]; omega
  have hKtS : 1 ≤ Kt * (ts.sum + p + 1) := by
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by omega))
  have hKtS2 : 2 ≤ Kt * (ts.sum + p + 1) := by
    have h := Nat.mul_le_mul hKt1 hS2
    simpa using h
  -- #### Phase 1: `roll 1` brings `intList ts` to the top
  obtain ⟨u1, N1r, hEv1, hn1raw, h1_0raw, hoth1⟩ :=
    Work.Kernel.roll_prog_ev main 1
      (HvdH.Val.int p :: HvdH.intList ts :: HvdH.cvecVal zs :: R) Rg s (by simp) hs0
  obtain ⟨n1, hev1, hn1N⟩ := hEv1
  have hevq1 : Eval main q1 s u1 n1 := hev1
  have h1_0 : u1.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [h1_0raw]
    have hlist : (HvdH.Val.int p :: HvdH.intList ts :: HvdH.cvecVal zs :: R).getD 1 HvdH.Val.nil
        :: (HvdH.Val.int p :: HvdH.intList ts :: HvdH.cvecVal zs :: R).eraseIdx 1
        = HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R := by
      simp
    rw [hlist]
  have hinv1 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u1.stk j = s.stk j := by
    intro j hj
    exact hoth1 j (fun h => hj (by simp [h]))
  have hn1 : n1 ≤ Kt * (ts.sum + p + 1) := by
    have h0 := le_trans hn1N hn1raw
    have ht : ((HvdH.Val.int p :: HvdH.intList ts :: HvdH.cvecVal zs :: R).take 2).map HvdH.vsz
        = [HvdH.vsz (HvdH.Val.int p), HvdH.vsz (HvdH.intList ts)] := by simp
    rw [ht, List.sum_cons, List.sum_cons, List.sum_nil, Nat.add_zero] at h0
    have hX : HvdH.vsz (HvdH.Val.int p) + HvdH.vsz (HvdH.intList ts) + 1
        ≤ 7 * (ts.sum + p + 1) := by omega
    refine pwAux_cost_step (K := 128) ?_ hX ?_
    · nlinarith only [h0]
    · rw [hKtdef]; omega
  have hN1 : n1 ≤ (1 * Kt) * (ts.sum + p + 1) := by simpa using hn1
  -- #### Phase 2: copy the `intList ts` block to stack 1
  have hsrc2 : u1.stk 0 = (HvdH.ofList (ts.map Pw.pk_iVal)).enc
      ++ (encs (HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg) := by
    rw [h1_0, Pw.pk_intList_eq_iVal, encs_cons, List.append_assoc]
  obtain ⟨u2, n2, hev2, hn2raw, h2_0raw, h2_1raw, h2_7raw, hoth2⟩ :=
    hcp1 main (ts.map Pw.pk_iVal) (encs (HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg) u1
      (fun x hx => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
        exact ⟨(t : ℤ), rfl⟩) hsrc2
  have hevq2 : Eval main q2 s u2 (n1 + n2) := Eval.seq hevq1 hev2
  have h2_0 : u2.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [h2_0raw]
    simp only [Pw.pk_intList_eq_iVal, encs_cons, List.append_assoc]
  have h2_1 : u2.stk 1 = (HvdH.ofList (ts.map Pw.pk_iVal)).enc ++ Pw.gM :: s.stk 1 := by
    rw [h2_1raw, hoth1 1 (by decide)]
  have h2_7 : u2.stk 7 = s.stk 7 := by rw [h2_7raw, hoth1 7 (by decide)]
  have hinv2 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u2.stk j = s.stk j := by
    intro j hj
    rw [hoth2 j (fun h => hj (by simp [h])) (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))]
    exact hinv1 j hj
  have hn2 : n2 ≤ Kt * (ts.sum + p + 1) := by
    have hn2' : n2 ≤ Kcp1 * (HvdH.vsz (HvdH.intList ts) + 1) := by
      have h := hn2raw
      rw [← Pw.pk_intList_eq_iVal] at h
      exact h
    refine pwAux_cost_step hn2' hvszTs ?_
    rw [hKtdef]; omega
  have hN2 : n1 + n2 ≤ (2 * Kt) * (ts.sum + p + 1) := pwAux_acc hN1 hn2
  -- #### Phase 3: copy the `intList ts` block to stack 3
  have hsrc3 : u2.stk 0 = (HvdH.ofList (ts.map Pw.pk_iVal)).enc
      ++ (encs (HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg) := by
    rw [h2_0, Pw.pk_intList_eq_iVal, encs_cons, List.append_assoc]
  obtain ⟨u3, n3, hev3, hn3raw, h3_0raw, h3_3raw, h3_7raw, hoth3⟩ :=
    hcp3 main (ts.map Pw.pk_iVal) (encs (HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg) u2
      (fun x hx => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
        exact ⟨(t : ℤ), rfl⟩) hsrc3
  have hevq3 : Eval main q3 s u3 (n1 + n2 + n3) := Eval.seq hevq2 hev3
  have h3_0 : u3.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [h3_0raw]
    simp only [Pw.pk_intList_eq_iVal, encs_cons, List.append_assoc]
  have h3_0' : u3.stk 0 = (HvdH.ofList (ts.map Pw.pk_iVal)).enc
      ++ (encs (HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg) := by
    rw [h3_0, Pw.pk_intList_eq_iVal, encs_cons, List.append_assoc]
  have h3_3 : u3.stk 3 = (HvdH.ofList (ts.map Pw.pk_iVal)).enc ++ Pw.gM :: s.stk 3 := by
    rw [h3_3raw, hoth2 3 (by decide) (by decide) (by decide), hoth1 3 (by decide)]
  have h3_7 : u3.stk 7 = u2.stk 7 := h3_7raw
  have hinv3 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u3.stk j = s.stk j := by
    intro j hj
    rw [hoth3 j (fun h => hj (by simp [h])) (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))]
    exact hinv2 j hj
  have hn3 : n3 ≤ Kt * (ts.sum + p + 1) := by
    have hn3' : n3 ≤ Kcp3 * (HvdH.vsz (HvdH.intList ts) + 1) := by
      have h := hn3raw
      rw [← Pw.pk_intList_eq_iVal] at h
      exact h
    refine pwAux_cost_step hn3' hvszTs ?_
    rw [hKtdef]; omega
  have hN3 : n1 + n2 + n3 ≤ (3 * Kt) * (ts.sum + p + 1) := pwAux_acc hN2 hn3
  -- #### Phase 4: push the running-maximum marker on stack 2
  obtain ⟨u4, n4, hev4, hn4raw, h4_2raw, hoth4⟩ := hpus2 main u3
  have hevq4 : Eval main q4 s u4 (n1 + n2 + n3 + n4) := Eval.seq hevq3 hev4
  have h3_2 : u3.stk 2 = s.stk 2 := by
    rw [hoth3 2 (by decide) (by decide) (by decide), hoth2 2 (by decide) (by decide) (by decide),
      hoth1 2 (by decide)]
  have h4_2 : u4.stk 2 = Pw.gM :: s.stk 2 := by rw [h4_2raw, h3_2]
  have h4_0 : u4.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hoth4 0 (by decide)]; exact h3_0
  have hinv4 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u4.stk j = s.stk j := by
    intro j hj
    rw [hoth4 j (fun h => hj (by simp [h]))]
    exact hinv3 j hj
  have hn4 : n4 ≤ Kt * (ts.sum + p + 1) := by
    have h := hKtS2
    omega
  have hN4 : n1 + n2 + n3 + n4 ≤ (4 * Kt) * (ts.sum + p + 1) := pwAux_acc hN3 hn4
  -- #### Phase 5: the max phase
  have h5pre : u4.stk 1 = (HvdH.intList ts).enc ++ Pw.gM :: s.stk 1 := by
    rw [hoth4 1 (by decide), hoth3 1 (by decide) (by decide) (by decide), h2_1,
      ← Pw.pk_intList_eq_iVal]
  obtain ⟨u5, n5, hev5, hn5raw, h5_1, h5_2, hoth5⟩ :=
    hmx main ts (s.stk 1) (s.stk 2) u4 hpos h5pre h4_2
  have hevq5 : Eval main q5 s u5 (n1 + n2 + n3 + n4 + n5) := Eval.seq hevq4 hev5
  have h5_0 : u5.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hoth5 0 (by decide) (by decide)]; exact h4_0
  have hinv5 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u5.stk j = s.stk j := by
    intro j hj
    rw [hoth5 j (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))]
    exact hinv4 j hj
  have hn5 : n5 ≤ Kt * (ts.sum + p + 1) := by
    have hX : ts.sum + 1 ≤ 1 * (ts.sum + p + 1) := by omega
    refine pwAux_cost_step (K := Kmx) ?_ hX ?_
    · simpa using hn5raw
    · rw [hKtdef]; omega
  have hN5 : n1 + n2 + n3 + n4 + n5 ≤ (5 * Kt) * (ts.sum + p + 1) := pwAux_acc hN4 hn5
  -- #### Phase 6: pop the marker of stack 1
  set u6 : HvdH.State := State.tPop u5 (1 : HvdH.Stk) 0 with hu6
  have hev6 : Eval main (.pop (1 : HvdH.Stk) (0 : HvdH.Reg)) u5 u6 1 := by
    rw [hu6]; exact Work.Kernel.eval_pop main 1 0 u5
  have hevq6 : Eval main q6 s u6 (n1 + n2 + n3 + n4 + n5 + 1) := Eval.seq hevq5 hev6
  have h6_1 : u6.stk 1 = s.stk 1 := by
    rw [hu6, Pw.tPop_stk, if_pos rfl, h5_1, List.tail_cons]
  have h6_0 : u6.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hu6, Pw.tPop_stk, if_neg (by decide)]; exact h5_0
  have hoth6 : ∀ j : HvdH.Stk, j ≠ 1 → u6.stk j = u5.stk j := by
    intro j hj
    rw [hu6, Pw.tPop_stk, if_neg hj]
  have hinv6 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u6.stk j = s.stk j := by
    intro j hj
    rw [hoth6 j (fun h => hj (by simp [h]))]
    exact hinv5 j hj
  have hN6 : n1 + n2 + n3 + n4 + n5 + 1 ≤ (6 * Kt) * (ts.sum + p + 1) :=
    pwAux_acc hN5 (by simpa using hKtS)
  -- #### Phase 7: `revMarked 2 8` moves the maximum bits to stack 8
  have h7pre : u6.stk 2 = (Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit
      ++ Pw.gM :: s.stk 2 := by
    rw [hoth6 2 (by decide)]; exact h5_2
  have hgs7 : ∀ g ∈ (Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit, g ≠ Pw.gM :=
    fun g hg => Pw.map_bit_ne_gM _ g hg
  obtain ⟨u7, n7, hev7, hn7raw, h7_2, h7_8, hoth7⟩ :=
    Pw.revMarked_eval main (2 : HvdH.Stk) 8 0 1 (by decide)
      ((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit) (s.stk 2)
      hgs7 u6 h7pre
  have hevq7 : Eval main q7 s u7 (n1 + n2 + n3 + n4 + n5 + 1 + n7) := Eval.seq hevq6 hev7
  have h6_8 : u6.stk 8 = s.stk 8 := by
    rw [hoth6 8 (by decide), hoth5 8 (by decide) (by decide), hoth4 8 (by decide),
      hoth3 8 (by decide) (by decide) (by decide), hoth2 8 (by decide) (by decide) (by decide),
      hoth1 8 (by decide)]
  have h7_8' : u7.stk 8 = ((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse
      ++ Pw.gM :: s.stk 8 := by rw [h7_8, h6_8]
  have h7_0 : u7.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hoth7 0 (by decide) (by decide)]; exact h6_0
  have hinv7 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u7.stk j = s.stk j := by
    intro j hj
    rw [hoth7 j (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))]
    exact hinv6 j hj
  have hn7 : n7 ≤ Kt * (ts.sum + p + 1) := by
    have hlen : ((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).length
        = (HvdH.lmax ts).size := by
      rw [List.length_map]; exact Pw.mx_encodeNat_length _
    have h' : n7 ≤ 14 * ((HvdH.lmax ts).size + 1) := by
      have h := hn7raw
      rw [hlen] at h
      omega
    refine pwAux_cost_step h' hlmaxSz ?_
    rw [hKtdef]; omega
  have hN7 : n1 + n2 + n3 + n4 + n5 + 1 + n7 ≤ (7 * Kt) * (ts.sum + p + 1) :=
    pwAux_acc hN6 hn7
  -- #### Phase 8: `revAcc 3 4` reverses `intList ts` onto stack 4
  have h8pre : u7.stk 3 = (HvdH.ofList (ts.map Pw.pk_iVal)).enc ++ Pw.gM :: s.stk 3 := by
    rw [hoth7 3 (by decide) (by decide), hoth6 3 (by decide), hoth5 3 (by decide) (by decide),
      hoth4 3 (by decide), h3_3]
  obtain ⟨u8, n8, hev8, hn8raw, h8_3, h8_4, hoth8⟩ :=
    hra1 main (ts.map Pw.pk_iVal) (s.stk 3) u7
      (fun x hx => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
        exact ⟨(t : ℤ), rfl⟩) h8pre
  have hevq8 : Eval main q8 s u8 (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8) := Eval.seq hevq7 hev8
  have h8_3' : u8.stk 3 = Pw.gM :: s.stk 3 := h8_3
  have h7_4 : u7.stk 4 = s.stk 4 := by
    rw [hoth7 4 (by decide) (by decide), hoth6 4 (by decide), hoth5 4 (by decide) (by decide),
      hoth4 4 (by decide), hoth3 4 (by decide) (by decide) (by decide),
      hoth2 4 (by decide) (by decide) (by decide), hoth1 4 (by decide)]
  have h8_4' : u8.stk 4 = (HvdH.ofList ((ts.map Pw.pk_iVal).reverse)).enc ++ Pw.gM :: s.stk 4 := by
    rw [h8_4, h7_4]
  have h8_0 : u8.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hoth8 0 (by decide) (by decide)]; exact h7_0
  have hinv8 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u8.stk j = s.stk j := by
    intro j hj
    rw [hoth8 j (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))]
    exact hinv7 j hj
  have hn8 : n8 ≤ Kt * (ts.sum + p + 1) := by
    have hn8' : n8 ≤ Kra1 * (HvdH.vsz (HvdH.intList ts) + 1) := by
      have h := hn8raw
      change n8 ≤ Kra1 * (HvdH.vsz (HvdH.ofList (ts.map Pw.pk_iVal)) + 1) at h
      rw [← Pw.pk_intList_eq_iVal] at h
      exact h
    refine pwAux_cost_step hn8' hvszTs ?_
    rw [hKtdef]; omega
  have hN8 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 ≤ (8 * Kt) * (ts.sum + p + 1) :=
    pwAux_acc hN7 hn8
  -- #### Phase 9: pop the marker of stack 3
  set u9 : HvdH.State := State.tPop u8 (3 : HvdH.Stk) 0 with hu9
  have hev9 : Eval main (.pop (3 : HvdH.Stk) (0 : HvdH.Reg)) u8 u9 1 := by
    rw [hu9]; exact Work.Kernel.eval_pop main 3 0 u8
  have hevq9 : Eval main q9 s u9 (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1) :=
    Eval.seq hevq8 hev9
  have h9_3 : u9.stk 3 = s.stk 3 := by
    rw [hu9, Pw.tPop_stk, if_pos rfl, h8_3', List.tail_cons]
  have h9_0 : u9.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hu9, Pw.tPop_stk, if_neg (by decide)]; exact h8_0
  have hoth9 : ∀ j : HvdH.Stk, j ≠ 3 → u9.stk j = u8.stk j := by
    intro j hj
    rw [hu9, Pw.tPop_stk, if_neg hj]
  have hinv9 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u9.stk j = s.stk j := by
    intro j hj
    rw [hoth9 j (fun h => hj (by simp [h]))]
    exact hinv8 j hj
  have hN9 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 ≤ (9 * Kt) * (ts.sum + p + 1) :=
    pwAux_acc hN8 (by simpa using hKtS)
  -- #### Phase 10: drop the first cell of the reversed list (the last entry of `ts`)
  have h10pre : u9.stk 4 = (HvdH.ofList (Pw.pk_iVal (ts.getLastD 0)
      :: ((ts.dropLast).map Pw.pk_iVal).reverse)).enc ++ Pw.gM :: s.stk 4 := by
    have hsplit := Pw.pk_rev_map_cons ts Pw.pk_iVal hts
    rw [hoth9 4 (by decide), h8_4', hsplit]
  obtain ⟨u10, n10, hev10, hn10raw, h10_4, hoth10⟩ :=
    hdc main ((ts.getLastD 0 : ℕ) : ℤ) (((ts.dropLast).map Pw.pk_iVal).reverse) (s.stk 4) u9
      h10pre
  have hevq10 : Eval main q10 s u10
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10) := Eval.seq hevq9 hev10
  have h10_0 : u10.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hoth10 0 (by decide)]; exact h9_0
  have hinv10 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u10.stk j = s.stk j := by
    intro j hj
    rw [hoth10 j (fun h => hj (by simp [h]))]
    exact hinv9 j hj
  have hn10 : n10 ≤ Kt * (ts.sum + p + 1) := by
    refine pwAux_cost_step hn10raw hiszLast ?_
    rw [hKtdef]; omega
  have hN10 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10
      ≤ (10 * Kt) * (ts.sum + p + 1) := pwAux_acc hN9 hn10
  -- #### Phase 11: `revAcc 4 5` turns the reversed `dropLast` back
  have h11pre : u10.stk 4 = (HvdH.ofList (((ts.dropLast).map Pw.pk_iVal).reverse)).enc
      ++ Pw.gM :: s.stk 4 := by
    rw [h10_4]
  obtain ⟨u11, n11, hev11, hn11raw, h11_4, h11_5, hoth11⟩ :=
    hra2 main (((ts.dropLast).map Pw.pk_iVal).reverse) (s.stk 4) u10
      (fun x hx => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
        exact ⟨(t : ℤ), rfl⟩) h11pre
  have hevq11 : Eval main q11 s u11
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11) := Eval.seq hevq10 hev11
  have h10_5 : u10.stk 5 = s.stk 5 := by
    rw [hoth10 5 (by decide), hoth9 5 (by decide), hoth8 5 (by decide) (by decide),
      hoth7 5 (by decide) (by decide), hoth6 5 (by decide), hoth5 5 (by decide) (by decide),
      hoth4 5 (by decide), hoth3 5 (by decide) (by decide) (by decide),
      hoth2 5 (by decide) (by decide) (by decide), hoth1 5 (by decide)]
  have h11_5' : u11.stk 5 = (HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc ++ Pw.gM :: s.stk 5 := by
    rw [h11_5, h10_5, List.reverse_reverse]
  have h11_4' : u11.stk 4 = Pw.gM :: s.stk 4 := h11_4
  have h11_0 : u11.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hoth11 0 (by decide) (by decide)]; exact h10_0
  have hinv11 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u11.stk j = s.stk j := by
    intro j hj
    rw [hoth11 j (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))]
    exact hinv10 j hj
  have hn11 : n11 ≤ Kt * (ts.sum + p + 1) := by
    have hn11' : n11 ≤ Kra2 * (HvdH.vsz (HvdH.intList ts.dropLast) + 1) := by
      have h := hn11raw
      change n11 ≤ Kra2 * (HvdH.vsz (HvdH.ofList (((ts.dropLast).map Pw.pk_iVal).reverse)) + 1) at h
      rw [Pw.pk_vsz_ofList_reverse, ← Pw.pk_intList_eq_iVal] at h
      exact h
    refine pwAux_cost_step hn11' hvszDL ?_
    rw [hKtdef]; omega
  have hN11 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11
      ≤ (11 * Kt) * (ts.sum + p + 1) := pwAux_acc hN10 hn11
  -- #### Phase 12: pop the marker of stack 4
  set u12 : HvdH.State := State.tPop u11 (4 : HvdH.Stk) 0 with hu12
  have hev12 : Eval main (.pop (4 : HvdH.Stk) (0 : HvdH.Reg)) u11 u12 1 := by
    rw [hu12]; exact Work.Kernel.eval_pop main 4 0 u11
  have hevq12 : Eval main q12 s u12
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1) := Eval.seq hevq11 hev12
  have h12_4 : u12.stk 4 = s.stk 4 := by
    rw [hu12, Pw.tPop_stk, if_pos rfl, h11_4', List.tail_cons]
  have h12_0 : u12.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hu12, Pw.tPop_stk, if_neg (by decide)]; exact h11_0
  have hoth12 : ∀ j : HvdH.Stk, j ≠ 4 → u12.stk j = u11.stk j := by
    intro j hj
    rw [hu12, Pw.tPop_stk, if_neg hj]
  have hinv12 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u12.stk j = s.stk j := by
    intro j hj
    rw [hoth12 j (fun h => hj (by simp [h]))]
    exact hinv11 j hj
  have hN12 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1
      ≤ (12 * Kt) * (ts.sum + p + 1) := pwAux_acc hN11 (by simpa using hKtS)
  -- #### Phase 13: push the marker for the block move on stack 7
  obtain ⟨u13, n13, hev13, hn13raw, h13_7raw, hoth13⟩ := hpus7 main u12
  have hevq13 : Eval main q13 s u13
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13) := Eval.seq hevq12 hev13
  have h12_7 : u12.stk 7 = s.stk 7 := by
    rw [hoth12 7 (by decide), hoth11 7 (by decide) (by decide), hoth10 7 (by decide),
      hoth9 7 (by decide), hoth8 7 (by decide) (by decide), hoth7 7 (by decide) (by decide),
      hoth6 7 (by decide), hoth5 7 (by decide) (by decide), hoth4 7 (by decide), h3_7, h2_7]
  have h13_7 : u13.stk 7 = Pw.gM :: s.stk 7 := by rw [h13_7raw, h12_7]
  have h13_0 : u13.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hoth13 0 (by decide)]; exact h12_0
  have hinv13 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u13.stk j = s.stk j := by
    intro j hj
    rw [hoth13 j (fun h => hj (by simp [h]))]
    exact hinv12 j hj
  have hn13 : n13 ≤ Kt * (ts.sum + p + 1) := by
    have h := hKtS2; omega
  have hN13 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      ≤ (13 * Kt) * (ts.sum + p + 1) := pwAux_acc hN12 hn13
  -- #### Phase 14: move the `dropLast` block (stack 5) to stack 7
  have h14pre : u13.stk 5 = (HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc ++ Pw.gM :: s.stk 5 := by
    rw [hoth13 5 (by decide), hoth12 5 (by decide), h11_5']
  have hne14 : ∀ g ∈ (HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc, g ≠ Pw.gM := by
    intro g hg
    rw [← Pw.pk_intList_eq_iVal] at hg
    exact Pw.pk_intList_ne_gM ts.dropLast g hg
  have hev14 : Eval main (Pw.tLoop (5 : HvdH.Stk) Pw.gM (7 : HvdH.Stk) (0 : HvdH.Reg)) u13
      (Pw.tSt (5 : HvdH.Stk) Pw.gM (7 : HvdH.Stk) (0 : HvdH.Reg)
        ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc) (s.stk 5) u13)
      (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) :=
    Pw.tLoop_eval main 5 Pw.gM 7 0 (by decide) Pw.gM_ne_eos _ _ u13 h14pre hne14
  set u14 : HvdH.State := Pw.tSt (5 : HvdH.Stk) Pw.gM (7 : HvdH.Stk) (0 : HvdH.Reg)
    ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc) (s.stk 5) u13 with hu14
  have hevq14 : Eval main q14 s u14
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
        + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7)) := by
    rw [hu14]
    exact Eval.seq hevq13 hev14
  have h14_5 : u14.stk 5 = Pw.gM :: s.stk 5 := by
    rw [hu14]; exact Pw.tSt_stk_k _ _ _ _ _ _ _ (by decide)
  have h14_7 : u14.stk 7 = ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse
      ++ Pw.gM :: s.stk 7 := by
    rw [hu14, Pw.tSt_stk_dst, h13_7]
  have h14_0 : u14.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hu14, Pw.tSt_stk_ne _ _ _ _ _ _ _ (by decide) (by decide)]; exact h13_0
  have hoth14 : ∀ j : HvdH.Stk, j ≠ 5 → j ≠ 7 → u14.stk j = u13.stk j := by
    intro j h1 h2
    rw [hu14]; exact Pw.tSt_stk_ne _ _ _ _ _ _ _ h1 h2
  have hinv14 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u14.stk j = s.stk j := by
    intro j hj
    rw [hoth14 j (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))]
    exact hinv13 j hj
  have hn14 : 5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7
      ≤ Kt * (ts.sum + p + 1) := by
    have hlen : ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length
        = HvdH.vsz (HvdH.intList ts.dropLast) := by
      rw [Pw.pk_intList_eq_iVal]; rfl
    have h' : 5 * HvdH.vsz (HvdH.intList ts.dropLast) + 7
        ≤ 7 * (HvdH.vsz (HvdH.intList ts.dropLast) + 1) := by omega
    rw [hlen] at *
    refine pwAux_cost_step h' hvszDL ?_
    rw [hKtdef]; omega
  have hN14 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7)
      ≤ (14 * Kt) * (ts.sum + p + 1) := pwAux_acc hN13 hn14
  -- #### Phase 15: pop the marker of stack 5
  set u15 : HvdH.State := State.tPop u14 (5 : HvdH.Stk) 0 with hu15
  have hev15 : Eval main (.pop (5 : HvdH.Stk) (0 : HvdH.Reg)) u14 u15 1 := by
    rw [hu15]; exact Work.Kernel.eval_pop main 5 0 u14
  have hevq15 : Eval main q15 s u15
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
        + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1) :=
    Eval.seq hevq14 hev15
  have h15_5 : u15.stk 5 = s.stk 5 := by
    rw [hu15, Pw.tPop_stk, if_pos rfl, h14_5, List.tail_cons]
  have h15_0 : u15.stk 0 = encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hu15, Pw.tPop_stk, if_neg (by decide)]; exact h14_0
  have hoth15 : ∀ j : HvdH.Stk, j ≠ 5 → u15.stk j = u14.stk j := by
    intro j hj
    rw [hu15, Pw.tPop_stk, if_neg hj]
  have hinv15 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u15.stk j = s.stk j := by
    intro j hj
    rw [hoth15 j (fun h => hj (by simp [h]))]
    exact hinv14 j hj
  have hN15 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
      ≤ (15 * Kt) * (ts.sum + p + 1) := pwAux_acc hN14 (by simpa using hKtS)
  -- #### Phase 16: move the `dropLast` block onto stack 0
  have h16pre : u15.stk 7 = ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse
      ++ Pw.gM :: s.stk 7 := by
    rw [hoth15 7 (by decide), h14_7]
  have hne16 : ∀ g ∈ ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse, g ≠ Pw.gM := by
    intro g hg
    exact hne14 g (List.mem_reverse.mp hg)
  have hev16 : Eval main (Pw.tLoop (7 : HvdH.Stk) Pw.gM (0 : HvdH.Stk) (0 : HvdH.Reg)) u15
      (Pw.tSt (7 : HvdH.Stk) Pw.gM (0 : HvdH.Stk) (0 : HvdH.Reg)
        (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse) (s.stk 7) u15)
      (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) :=
    Pw.tLoop_eval main 7 Pw.gM 0 0 (by decide) Pw.gM_ne_eos _ _ u15 h16pre hne16
  set u16 : HvdH.State := Pw.tSt (7 : HvdH.Stk) Pw.gM (0 : HvdH.Stk) (0 : HvdH.Reg)
    (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse) (s.stk 7) u15 with hu16
  have hevq16 : Eval main q16 s u16
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
        + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
        + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7)) := by
    rw [hu16]
    exact Eval.seq hevq15 hev16
  have h16_7 : u16.stk 7 = Pw.gM :: s.stk 7 := by
    rw [hu16]; exact Pw.tSt_stk_k _ _ _ _ _ _ _ (by decide)
  have h16_0raw : u16.stk 0 = ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse.reverse
      ++ (encs (HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg) := by
    rw [hu16, Pw.tSt_stk_dst, h15_0]
  have h16_0 : u16.stk 0 = encs (HvdH.intList ts.dropLast :: HvdH.intList ts
      :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [h16_0raw, List.reverse_reverse, ← Pw.pk_intList_eq_iVal]
    simp only [encs_cons, List.append_assoc]
  have hoth16 : ∀ j : HvdH.Stk, j ≠ 7 → j ≠ 0 → u16.stk j = u15.stk j := by
    intro j h1 h2
    rw [hu16]; exact Pw.tSt_stk_ne _ _ _ _ _ _ _ h1 h2
  have hinv16 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u16.stk j = s.stk j := by
    intro j hj
    rw [hoth16 j (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))]
    exact hinv15 j hj
  have hn16 : 5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7
      ≤ Kt * (ts.sum + p + 1) := by
    have hlen : (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length
        = HvdH.vsz (HvdH.intList ts.dropLast) := by
      rw [List.length_reverse, Pw.pk_intList_eq_iVal]; rfl
    rw [hlen]
    have h' : 5 * HvdH.vsz (HvdH.intList ts.dropLast) + 7
        ≤ 7 * (HvdH.vsz (HvdH.intList ts.dropLast) + 1) := by omega
    refine pwAux_cost_step h' hvszDL ?_
    rw [hKtdef]; omega
  have hN16 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
      + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7)
      ≤ (16 * Kt) * (ts.sum + p + 1) := pwAux_acc hN15 hn16
  -- #### Phase 17: pop the marker of stack 7
  set u17 : HvdH.State := State.tPop u16 (7 : HvdH.Stk) 0 with hu17
  have hev17 : Eval main (.pop (7 : HvdH.Stk) (0 : HvdH.Reg)) u16 u17 1 := by
    rw [hu17]; exact Work.Kernel.eval_pop main 7 0 u16
  have hevq17 : Eval main q17 s u17
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
        + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
        + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1) :=
    Eval.seq hevq16 hev17
  have h17_7 : u17.stk 7 = s.stk 7 := by
    rw [hu17, Pw.tPop_stk, if_pos rfl, h16_7, List.tail_cons]
  have h17_0 : u17.stk 0 = encs (HvdH.intList ts.dropLast :: HvdH.intList ts
      :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hu17, Pw.tPop_stk, if_neg (by decide)]; exact h16_0
  have hoth17 : ∀ j : HvdH.Stk, j ≠ 7 → u17.stk j = u16.stk j := by
    intro j hj
    rw [hu17, Pw.tPop_stk, if_neg hj]
  have hinv17 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u17.stk j = s.stk j := by
    intro j hj
    rw [hoth17 j (fun h => hj (by simp [h]))]
    exact hinv16 j hj
  have hN17 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
      + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1
      ≤ (17 * Kt) * (ts.sum + p + 1) := pwAux_acc hN16 (by simpa using hKtS)
  -- #### Phase 18: push `iend`
  obtain ⟨u18, n18, hev18, hn18raw, h18_0raw, hoth18⟩ := hpuse main u17
  have hevq18 : Eval main q18 s u18
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
        + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
        + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1
        + n18) := Eval.seq hevq17 hev18
  have h18_0 : u18.stk 0 = HvdH.Glyph.iend :: encs (HvdH.intList ts.dropLast
      :: HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [h18_0raw, h17_0, List.cons_append]
  have hinv18 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u18.stk j = s.stk j := by
    intro j hj
    rw [hoth18 j (fun h => hj (by simp [h]))]
    exact hinv17 j hj
  have hn18 : n18 ≤ Kt * (ts.sum + p + 1) := by
    have h := hKtS2; omega
  have hN18 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
      + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1 + n18
      ≤ (18 * Kt) * (ts.sum + p + 1) := pwAux_acc hN17 hn18
  -- #### Phase 19: move the maximum bits onto stack 0
  have h18_8 : u18.stk 8 = ((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse
      ++ Pw.gM :: s.stk 8 := by
    rw [hoth18 8 (by decide), hoth17 8 (by decide), hoth16 8 (by decide) (by decide),
      hoth15 8 (by decide), hoth14 8 (by decide) (by decide), hoth13 8 (by decide),
      hoth12 8 (by decide), hoth11 8 (by decide) (by decide), hoth10 8 (by decide),
      hoth9 8 (by decide), hoth8 8 (by decide) (by decide), h7_8']
  have hne19 : ∀ g ∈ ((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse,
      g ≠ Pw.gM := by
    intro g hg
    exact Pw.map_bit_ne_gM _ g (List.mem_reverse.mp hg)
  have hev19 : Eval main (Pw.tLoop (8 : HvdH.Stk) Pw.gM (0 : HvdH.Stk) (0 : HvdH.Reg)) u18
      (Pw.tSt (8 : HvdH.Stk) Pw.gM (0 : HvdH.Stk) (0 : HvdH.Reg)
        (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse) (s.stk 8) u18)
      (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7) :=
    Pw.tLoop_eval main 8 Pw.gM 0 0 (by decide) Pw.gM_ne_eos _ _ u18 h18_8 hne19
  set u19 : HvdH.State := Pw.tSt (8 : HvdH.Stk) Pw.gM (0 : HvdH.Stk) (0 : HvdH.Reg)
    (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse) (s.stk 8) u18 with hu19
  have hevq19 : Eval main q19 s u19
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
        + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
        + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1
        + n18
        + (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7)) := by
    rw [hu19]
    exact Eval.seq hevq18 hev19
  have h19_8 : u19.stk 8 = Pw.gM :: s.stk 8 := by
    rw [hu19]; exact Pw.tSt_stk_k _ _ _ _ _ _ _ (by decide)
  have h19_0 : u19.stk 0 = (Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit
      ++ (HvdH.Glyph.iend :: encs (HvdH.intList ts.dropLast :: HvdH.intList ts
        :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg) := by
    rw [hu19, Pw.tSt_stk_dst, h18_0, List.reverse_reverse]
  have hoth19 : ∀ j : HvdH.Stk, j ≠ 8 → j ≠ 0 → u19.stk j = u18.stk j := by
    intro j h1 h2
    rw [hu19]; exact Pw.tSt_stk_ne _ _ _ _ _ _ _ h1 h2
  have hinv19 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u19.stk j = s.stk j := by
    intro j hj
    rw [hoth19 j (fun h => hj (by simp [h])) (fun h => hj (by simp [h]))]
    exact hinv18 j hj
  have hn19 : 5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7
      ≤ Kt * (ts.sum + p + 1) := by
    have hlen : (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length
        = (HvdH.lmax ts).size := by
      rw [List.length_reverse, List.length_map]; exact Pw.mx_encodeNat_length _
    rw [hlen]
    have h' : 5 * (HvdH.lmax ts).size + 7 ≤ 7 * ((HvdH.lmax ts).size + 1) := by omega
    refine pwAux_cost_step h' hlmaxSz ?_
    rw [hKtdef]; omega
  have hN19 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
      + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1 + n18
      + (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7)
      ≤ (19 * Kt) * (ts.sum + p + 1) := pwAux_acc hN18 hn19
  -- #### Phase 20: push the sign `pos`
  obtain ⟨u20, n20, hev20, hn20raw, h20_0raw, hoth20⟩ := hpusp main u19
  have hevq20 : Eval main q20 s u20
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
        + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
        + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1
        + n18
        + (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7)
        + n20) := Eval.seq hevq19 hev20
  have h20_0 : u20.stk 0 = encs (HvdH.Val.int (HvdH.lmax ts) :: HvdH.intList ts.dropLast
      :: HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [h20_0raw, h19_0]
    simp only [encs_cons, Pw.mx_enc_int_nat, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append]
  have hinv20 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u20.stk j = s.stk j := by
    intro j hj
    rw [hoth20 j (fun h => hj (by simp [h]))]
    exact hinv19 j hj
  have hn20 : n20 ≤ Kt * (ts.sum + p + 1) := by
    have h := hKtS2; omega
  have hN20 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
      + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1 + n18
      + (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7)
      + n20 ≤ (20 * Kt) * (ts.sum + p + 1) := pwAux_acc hN19 hn20
  -- #### Phase 21: pop the marker of stack 8
  set u21 : HvdH.State := State.tPop u20 (8 : HvdH.Stk) 0 with hu21
  have hev21 : Eval main (.pop (8 : HvdH.Stk) (0 : HvdH.Reg)) u20 u21 1 := by
    rw [hu21]; exact Work.Kernel.eval_pop main 8 0 u20
  have hevq21 : Eval main q21 s u21
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
        + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
        + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1
        + n18
        + (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7)
        + n20 + 1) := Eval.seq hevq20 hev21
  have h21_8 : u21.stk 8 = s.stk 8 := by
    rw [hu21, Pw.tPop_stk, if_pos rfl, hoth20 8 (by decide), h19_8, List.tail_cons]
  have h21_0 : u21.stk 0 = encs (HvdH.Val.int (HvdH.lmax ts) :: HvdH.intList ts.dropLast
      :: HvdH.intList ts :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [hu21, Pw.tPop_stk, if_neg (by decide)]; exact h20_0
  have hoth21 : ∀ j : HvdH.Stk, j ≠ 8 → u21.stk j = u20.stk j := by
    intro j hj
    rw [hu21, Pw.tPop_stk, if_neg hj]
  have hinv21 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u21.stk j = s.stk j := by
    intro j hj
    rw [hoth21 j (fun h => hj (by simp [h]))]
    exact hinv20 j hj
  have hN21 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
      + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1 + n18
      + (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7)
      + n20 + 1 ≤ (21 * Kt) * (ts.sum + p + 1) := pwAux_acc hN20 (by simpa using hKtS)
  -- #### Phase 22: `roll 3` puts `int p` back on top
  obtain ⟨u22, N22r, hEv22, hn22raw, h22_0raw, hoth22⟩ :=
    Work.Kernel.roll_prog_ev main 3
      (HvdH.Val.int (HvdH.lmax ts) :: HvdH.intList ts.dropLast :: HvdH.intList ts
        :: HvdH.Val.int p :: HvdH.cvecVal zs :: R) Rg u21 (by simp) h21_0
  obtain ⟨n22, hev22, hn22N⟩ := hEv22
  have hevq22 : Eval main q22 s u22
      (n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
        + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
        + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1
        + n18
        + (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7)
        + n20 + 1 + n22) := Eval.seq hevq21 hev22
  have h22_0 : u22.stk 0 = encs (HvdH.Val.int p :: HvdH.Val.int (HvdH.lmax ts)
      :: HvdH.intList ts.dropLast :: HvdH.intList ts :: HvdH.cvecVal zs :: R) ++ Rg := by
    rw [h22_0raw]
    have hlist : (HvdH.Val.int (HvdH.lmax ts) :: HvdH.intList ts.dropLast :: HvdH.intList ts
          :: HvdH.Val.int p :: HvdH.cvecVal zs :: R).getD 3 HvdH.Val.nil
        :: (HvdH.Val.int (HvdH.lmax ts) :: HvdH.intList ts.dropLast :: HvdH.intList ts
          :: HvdH.Val.int p :: HvdH.cvecVal zs :: R).eraseIdx 3
        = HvdH.Val.int p :: HvdH.Val.int (HvdH.lmax ts) :: HvdH.intList ts.dropLast
          :: HvdH.intList ts :: HvdH.cvecVal zs :: R := by
      simp
    rw [hlist]
  have hn22 : n22 ≤ Kt * (ts.sum + p + 1) := by
    have h0 := le_trans hn22N hn22raw
    have ht : ((HvdH.Val.int (HvdH.lmax ts) :: HvdH.intList ts.dropLast :: HvdH.intList ts
          :: HvdH.Val.int p :: HvdH.cvecVal zs :: R).take 4).map HvdH.vsz
        = [HvdH.vsz (HvdH.Val.int (HvdH.lmax ts)), HvdH.vsz (HvdH.intList ts.dropLast),
            HvdH.vsz (HvdH.intList ts), HvdH.vsz (HvdH.Val.int p)] := by simp
    rw [ht, List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons, List.sum_nil,
      Nat.add_zero] at h0
    refine pwAux_cost_step (K := 256) ?_ hcomb ?_
    · nlinarith only [h0]
    · rw [hKtdef]; omega
  have hN22 : n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
      + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1 + n18
      + (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7)
      + n20 + 1 + n22 ≤ (22 * Kt) * (ts.sum + p + 1) := pwAux_acc hN21 hn22
  have hinv22 : ∀ j : HvdH.Stk, j ∉ ({0,1,2,3,4,5,6,7,8} : Finset HvdH.Stk) →
      u22.stk j = s.stk j := by
    intro j hj
    rw [hoth22 j (fun h => hj (by simp [h]))]
    exact hinv21 j hj
  -- #### the explicit facts for the remaining scratch stacks
  have hf1 : u22.stk 1 = s.stk 1 := by
    rw [hoth22 1 (by decide), hoth21 1 (by decide), hoth20 1 (by decide),
      hoth19 1 (by decide) (by decide), hoth18 1 (by decide), hoth17 1 (by decide),
      hoth16 1 (by decide) (by decide), hoth15 1 (by decide),
      hoth14 1 (by decide) (by decide), hoth13 1 (by decide), hoth12 1 (by decide),
      hoth11 1 (by decide) (by decide), hoth10 1 (by decide), hoth9 1 (by decide),
      hoth8 1 (by decide) (by decide), hoth7 1 (by decide) (by decide), h6_1]
  have hf2 : u22.stk 2 = s.stk 2 := by
    rw [hoth22 2 (by decide), hoth21 2 (by decide), hoth20 2 (by decide),
      hoth19 2 (by decide) (by decide), hoth18 2 (by decide), hoth17 2 (by decide),
      hoth16 2 (by decide) (by decide), hoth15 2 (by decide),
      hoth14 2 (by decide) (by decide), hoth13 2 (by decide), hoth12 2 (by decide),
      hoth11 2 (by decide) (by decide), hoth10 2 (by decide), hoth9 2 (by decide),
      hoth8 2 (by decide) (by decide), h7_2]
  have hf3 : u22.stk 3 = s.stk 3 := by
    rw [hoth22 3 (by decide), hoth21 3 (by decide), hoth20 3 (by decide),
      hoth19 3 (by decide) (by decide), hoth18 3 (by decide), hoth17 3 (by decide),
      hoth16 3 (by decide) (by decide), hoth15 3 (by decide),
      hoth14 3 (by decide) (by decide), hoth13 3 (by decide), hoth12 3 (by decide),
      hoth11 3 (by decide) (by decide), hoth10 3 (by decide), h9_3]
  have hf4 : u22.stk 4 = s.stk 4 := by
    rw [hoth22 4 (by decide), hoth21 4 (by decide), hoth20 4 (by decide),
      hoth19 4 (by decide) (by decide), hoth18 4 (by decide), hoth17 4 (by decide),
      hoth16 4 (by decide) (by decide), hoth15 4 (by decide),
      hoth14 4 (by decide) (by decide), hoth13 4 (by decide), h12_4]
  have hf5 : u22.stk 5 = s.stk 5 := by
    rw [hoth22 5 (by decide), hoth21 5 (by decide), hoth20 5 (by decide),
      hoth19 5 (by decide) (by decide), hoth18 5 (by decide), hoth17 5 (by decide),
      hoth16 5 (by decide) (by decide), h15_5]
  have hf6 : u22.stk 6 = s.stk 6 := by
    rw [hoth22 6 (by decide), hoth21 6 (by decide), hoth20 6 (by decide),
      hoth19 6 (by decide) (by decide), hoth18 6 (by decide), hoth17 6 (by decide),
      hoth16 6 (by decide) (by decide), hoth15 6 (by decide),
      hoth14 6 (by decide) (by decide), hoth13 6 (by decide), hoth12 6 (by decide),
      hoth11 6 (by decide) (by decide), hoth10 6 (by decide), hoth9 6 (by decide),
      hoth8 6 (by decide) (by decide), hoth7 6 (by decide) (by decide), hoth6 6 (by decide),
      hoth5 6 (by decide) (by decide), hoth4 6 (by decide),
      hoth3 6 (by decide) (by decide) (by decide), hoth2 6 (by decide) (by decide) (by decide),
      hoth1 6 (by decide)]
  have hf7 : u22.stk 7 = s.stk 7 := by
    rw [hoth22 7 (by decide), hoth21 7 (by decide), hoth20 7 (by decide),
      hoth19 7 (by decide) (by decide), hoth18 7 (by decide), h17_7]
  have hf8 : u22.stk 8 = s.stk 8 := by
    rw [hoth22 8 (by decide), h21_8]
  -- #### conclusion
  refine ⟨HvdH.Val.int p :: HvdH.Val.int (HvdH.lmax ts) :: HvdH.intList ts.dropLast
      :: HvdH.intList ts :: HvdH.cvecVal zs :: R, u22,
    n1 + n2 + n3 + n4 + n5 + 1 + n7 + n8 + 1 + n10 + n11 + 1 + n13
      + (5 * ((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).length + 7) + 1
      + (5 * (((HvdH.ofList ((ts.dropLast).map Pw.pk_iVal)).enc).reverse).length + 7) + 1 + n18
      + (5 * (((Computability.encodeNat (HvdH.lmax ts)).map HvdH.Glyph.bit).reverse).length + 7)
      + n20 + 1 + n22, rfl, hevq22, ?_, h22_0, ?_⟩
  · -- cost
    refine pwAux_absorb (C := 22 * Kt) (K := 22 * Kt) hsum1 le_rfl ?_
    exact hN22
  · -- frame: every stack other than 0 is restored
    exact pwAux_frame u22 s hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hinv22

end Work.Transform
