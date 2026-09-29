import Mathlib
import Submission.Work.IntLib.Shift.Defs
import Submission.Work.IntLib.Shift.Loop

/-!
# `IntLib` / shift words: the `shl` epilogue

`finishShl` emits the encoding of the answer on stack 0.  Given an accumulator region of
`gZero` glyphs (the bits of `|a| · 2^k`) and the magnitude region `B` of `a` (unchanged when
`a = 0` or when the `shl` loop has consumed it), it produces the glyph word

  `sign :: (Acur ++ B ++ [iend])`  above the untouched tail `T0 ++ Rj` of stack 0,

and restores all the scratch stacks (markers of `sM`, `sA`, `sSg`, `sT` only), in cost bounded
by `O(|B| + |Acur|)` (both regions are simply drained onto stack 0).

The three `drain` steps are the `drain_ev` lemma of `Shift/Base.lean`; the cost bound
`10 * |B| + 5 * |Acur| + 60` is very loose (the true constant is `10 |B| + 5 |Acur| + 27`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace Shift

open HvdH

theorem finishShl_ev (main : HvdH.Cmd) (sg : HvdH.Glyph) (B Acur T0 Rj JM JA JSg JT : List HvdH.Glyph) (s : HvdH.State)
    (hB : ∀ h ∈ B, ∀ r : HvdH.Stk, h ≠ Work.IntLib.Shift.gmk r)
    (hAz : ∀ h ∈ Acur, h = Work.IntLib.Shift.gZero)
    (hM : s.stk Work.IntLib.Shift.sM = B ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: JM)
    (hA : s.stk Work.IntLib.Shift.sA = Acur ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sA :: JA)
    (hSg : s.stk Work.IntLib.Shift.sSg = sg :: Work.IntLib.Shift.gmk Work.IntLib.Shift.sSg :: JSg)
    (hT : s.stk Work.IntLib.Shift.sT = Work.IntLib.Shift.gmk Work.IntLib.Shift.sT :: JT)
    (h0 : s.stk 0 = T0 ++ Rj) (hne : B ≠ []) :
    ∃ (s' : HvdH.State) (n : ℕ), HvdH.Eval main Work.IntLib.Shift.finishShl s s' n ∧
      n ≤ 10 * B.length + 5 * Acur.length + 60 ∧
      s'.stk 0 = (sg :: (Acur ++ B ++ [HvdH.Glyph.iend])) ++ T0 ++ Rj ∧
      s'.stk Work.IntLib.Shift.sM = Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: JM ∧
      s'.stk Work.IntLib.Shift.sA = Work.IntLib.Shift.gmk Work.IntLib.Shift.sA :: JA ∧
      s'.stk Work.IntLib.Shift.sSg = Work.IntLib.Shift.gmk Work.IntLib.Shift.sSg :: JSg ∧
      s'.stk Work.IntLib.Shift.sT = Work.IntLib.Shift.gmk Work.IntLib.Shift.sT :: JT ∧
      s'.stk Work.IntLib.Shift.sK = s.stk Work.IntLib.Shift.sK ∧
      s'.stk Work.IntLib.Shift.sP = s.stk Work.IntLib.Shift.sP ∧
      s'.stk Work.IntLib.Shift.sT2 = s.stk Work.IntLib.Shift.sT2 := by
  -- `B` is nonempty: its head is the value read by the initial `peek`, and it is not a marker.
  cases B with
  | nil => exact absurd rfl hne
  | cons b0 B' =>
    have hb0M : b0 ≠ gmk sM := hB b0 (by simp) sM
    have hG1 : ∀ h ∈ b0 :: B', h ≠ gmk sM := fun h hh => hB h hh sM
    have hG2 : ∀ h ∈ (b0 :: B').reverse, h ≠ gmk sT :=
      fun h hh => hB h (List.mem_reverse.mp hh) sT
    have hGA : ∀ h ∈ Acur, h ≠ gmk sA := by
      intro h hh
      rw [hAz h hh]
      exact bit_ne_gmk sA false
    -- step 1: `peek sM rY` reads the head of `B`, which is not the marker of `sM`
    set s1 : State := ⟨Function.update s.reg rY b0, s.stk⟩ with hs1
    have hpeek : Ev main (.peek sM rY) s s1 1 := by
      rw [hs1]
      simpa [hM] using ev_peek_st main sM rY s
    have hne1 : s1.reg rY ≠ gmk sM := by
      rw [hs1]; simpa using hb0M
    -- step 2: push the `iend` of the answer encoding
    set s2 : State := ⟨Function.update s1.reg rY Glyph.iend,
      Function.update s1.stk 0 (Glyph.iend :: s1.stk 0)⟩ with hs2
    have hpush2 : Ev main (pushC 0 Glyph.iend rY) s1 s2 2 := by
      rw [hs2]; exact ev_pushC_st main 0 Glyph.iend rY s1
    have hs2_0 : s2.stk 0 = Glyph.iend :: T0 ++ Rj := by
      rw [hs2]; simp +decide [hs1, h0]
    have hs2_M : s2.stk sM = b0 :: B' ++ gmk sM :: JM := by
      rw [hs2]; simp +decide [hs1, hM]
    have hs2_T : s2.stk sT = gmk sT :: JT := by
      rw [hs2]; simp +decide [hs1, hT]
    have hs2_A : s2.stk sA = Acur ++ gmk sA :: JA := by
      rw [hs2]; simp +decide [hs1, hA]
    have hs2_Sg : s2.stk sSg = sg :: gmk sSg :: JSg := by
      rw [hs2]; simp +decide [hs1, hSg]
    have hs2_other : ∀ j : Stk, j ≠ 0 → s2.stk j = s1.stk j := by
      intro j hj; rw [hs2]; simp +decide [hj]
    -- step 3: drain the magnitude region `B` of `sM` onto `sT`
    obtain ⟨s3, n3, he3, hn3, hr3, hsM3, hsT3, ho3⟩ :=
      drain_ev main sM sT (gmk sM) rZ rJ (by decide) (by decide)
        (b0 :: B') JM (s2.stk sT) s2.reg s2.stk hG1 (by rw [hs2_M, List.cons_append]) rfl
    have h0_3 : s3.stk 0 = Glyph.iend :: T0 ++ Rj := by
      rw [ho3 0 (by decide) (by decide), hs2_0]
    have hs3_T : s3.stk sT = (b0 :: B').reverse ++ gmk sT :: JT := by
      rw [hsT3, hs2_T]
    have hs3_A : s3.stk sA = Acur ++ gmk sA :: JA := by
      rw [ho3 sA (by decide) (by decide), hs2_A]
    have hs3_Sg : s3.stk sSg = sg :: gmk sSg :: JSg := by
      rw [ho3 sSg (by decide) (by decide), hs2_Sg]
    -- step 4: drain `sT` (now `B` reversed) onto stack 0, recovering `B`
    obtain ⟨s4, n4, he4, hn4, hr4, hsT4, h0_4, ho4⟩ :=
      drain_ev main sT 0 (gmk sT) rZ rJ (by decide) (by decide)
        (b0 :: B').reverse JT (s3.stk 0) s3.reg s3.stk hG2 (by rw [hs3_T]) rfl
    have h0_4' : s4.stk 0 = (b0 :: B') ++ Glyph.iend :: T0 ++ Rj := by
      rw [h0_4, List.reverse_reverse, h0_3]
      simp only [List.append_assoc]
    have hs4_M : s4.stk sM = gmk sM :: JM := by
      rw [ho4 sM (by decide) (by decide), hsM3]
    have hs4_A : s4.stk sA = Acur ++ gmk sA :: JA := by
      rw [ho4 sA (by decide) (by decide), hs3_A]
    have hs4_Sg : s4.stk sSg = sg :: gmk sSg :: JSg := by
      rw [ho4 sSg (by decide) (by decide), hs3_Sg]
    -- step 5: drain the accumulator region `Acur` onto stack 0 (all of its glyphs are `gZero`,
    -- so reversing it does not change it)
    obtain ⟨s5, n5, he5, hn5, hr5, hsA5, h0_5, ho5⟩ :=
      drain_ev main sA 0 (gmk sA) rZ rJ (by decide) (by decide)
        Acur JA (s4.stk 0) s4.reg s4.stk hGA (by rw [hs4_A]) rfl
    have hAcur_rev : Acur.reverse = Acur := by
      have h1 : AllEq gZero Acur := fun g hg => hAz g hg
      calc Acur.reverse = List.replicate Acur.reverse.length gZero := h1.reverse.eq_replicate
        _ = List.replicate Acur.length gZero := by rw [List.length_reverse]
        _ = Acur := h1.eq_replicate.symm
    have h0_5' : s5.stk 0 = Acur ++ (b0 :: B') ++ Glyph.iend :: T0 ++ Rj := by
      rw [h0_5, h0_4', hAcur_rev]
      simp only [List.append_assoc]
    have hs5_Sg : s5.stk sSg = sg :: gmk sSg :: JSg := by
      rw [ho5 sSg (by decide) (by decide), hs4_Sg]
    -- step 6: pop the sign glyph of `sSg` and push it onto stack 0
    set s6 : State := ⟨Function.update s5.reg rY ((s5.stk sSg).headD .eos),
      Function.update s5.stk sSg ((s5.stk sSg).tail)⟩ with hs6
    have hpop : Eval main (.pop sSg rY) s5 s6 1 := by rw [hs6]; exact Eval.pop sSg rY s5
    have hreg6 : s6.reg rY = sg := by rw [hs6]; simp +decide [hs5_Sg]
    have hs6_0 : s6.stk 0 = Acur ++ (b0 :: B') ++ Glyph.iend :: T0 ++ Rj := by
      rw [hs6]; simp +decide [h0_5']
    have hs6_Sg : s6.stk sSg = gmk sSg :: JSg := by
      rw [hs6]; simp +decide [hs5_Sg]
    have hs6_other : ∀ j : Stk, j ≠ sSg → s6.stk j = s5.stk j := by
      intro j hj; rw [hs6]; simp +decide [hj]
    set s7 : State := ⟨s6.reg, Function.update s6.stk 0 (s6.reg rY :: s6.stk 0)⟩ with hs7
    have hpush0 : Eval main (.push 0 rY) s6 s7 1 := by rw [hs7]; exact Eval.push 0 rY s6
    have hs7_other : ∀ j : Stk, j ≠ 0 → s7.stk j = s6.stk j := by
      intro j hj; rw [hs7]; simp +decide [hj]
    -- the resulting stack 0
    have hs7_0 : s7.stk 0 = (sg :: (Acur ++ (b0 :: B') ++ [Glyph.iend])) ++ T0 ++ Rj := by
      rw [hs7]
      simp +decide [hreg6, hs6_0, List.cons_append, List.append_assoc]
    -- the restored scratch stacks
    have hs7_M : s7.stk sM = gmk sM :: JM := by
      rw [hs7_other sM (by decide), hs6_other sM (by decide), ho5 sM (by decide) (by decide), hs4_M]
    have hs7_A : s7.stk sA = gmk sA :: JA := by
      rw [hs7_other sA (by decide), hs6_other sA (by decide), hsA5]
    have hs7_Sg : s7.stk sSg = gmk sSg :: JSg := by
      rw [hs7_other sSg (by decide), hs6_Sg]
    have hs7_T : s7.stk sT = gmk sT :: JT := by
      rw [hs7_other sT (by decide), hs6_other sT (by decide), ho5 sT (by decide) (by decide), hsT4]
    have hpres : ∀ j : Stk, j ≠ 0 → j ≠ sM → j ≠ sT → j ≠ sA → j ≠ sSg → s7.stk j = s.stk j := by
      intro j h0j hMj hTj hAj hSj
      rw [hs7_other j h0j, hs6_other j hSj, ho5 j hAj h0j, ho4 j hTj h0j, ho3 j hMj hTj,
        hs2_other j h0j, hs1]
    have hs7_K : s7.stk sK = s.stk sK :=
      hpres sK (by decide) (by decide) (by decide) (by decide) (by decide)
    have hs7_P : s7.stk sP = s.stk sP :=
      hpres sP (by decide) (by decide) (by decide) (by decide) (by decide)
    have hs7_T2 : s7.stk sT2 = s.stk sT2 :=
      hpres sT2 (by decide) (by decide) (by decide) (by decide) (by decide)
    -- assemble the run: `peek`, the (false) `ite`, then the six straight-line steps
    obtain ⟨np, hpeekE, hnp⟩ := hpeek
    obtain ⟨np2, hpush2E, hnp2⟩ := hpush2
    have hbody : Eval main (seqs [pushC 0 Glyph.iend rY, drain sM sT (gmk sM) rZ rJ,
        drain sT 0 (gmk sT) rZ rJ, drain sA 0 (gmk sA) rZ rJ, .pop sSg rY, .push 0 rY])
        s1 s7 (np2 + (n3 + (n4 + (n5 + (1 + 1))))) :=
      Eval.seq hpush2E (Eval.seq he3 (Eval.seq he4 (Eval.seq he5 (Eval.seq hpop hpush0))))
    have hite : Eval main (.ite rY (gmk sM)
        (seqs [pushC 0 Glyph.iend rY, pushC 0 Glyph.pos rY])
        (seqs [pushC 0 Glyph.iend rY, drain sM sT (gmk sM) rZ rJ, drain sT 0 (gmk sT) rZ rJ,
          drain sA 0 (gmk sA) rZ rJ, .pop sSg rY, .push 0 rY])) s1 s7
        (np2 + (n3 + (n4 + (n5 + (1 + 1)))) + 1) :=
      Eval.iteF hne1 hbody
    have hfin : Eval main finishShl s s7 (np + (np2 + (n3 + (n4 + (n5 + (1 + 1)))) + 1)) := by
      have h := Eval.seq hpeekE hite
      rw [finishShl, seqs_pair]
      exact h
    refine ⟨s7, np + (np2 + (n3 + (n4 + (n5 + (1 + 1)))) + 1), hfin, ?_, hs7_0, hs7_M, hs7_A,
      hs7_Sg, hs7_T, hs7_K, hs7_P, hs7_T2⟩
    -- cost: 1 + 1 + 2 + (5 (|B|+1) + 2) + (5 (|B|+1) + 2) + (5 (|Acur|+1) + 2) + 1 + 1
    simp only [List.length_cons, List.length_reverse] at *
    omega

end Shift
end Work.IntLib
