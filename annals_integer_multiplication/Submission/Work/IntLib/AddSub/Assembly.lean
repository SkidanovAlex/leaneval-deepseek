import Mathlib
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.Basic
import Submission.Work.IntLib.AddSub.Touches
import Submission.Work.IntLib.AddSub.ValLemmas
import Submission.Work.IntLib.AddSub.Arith
import Submission.Work.IntLib.AddSub.asw_subLoop_spec
import Submission.Work.IntLib.AddSub.asw_finish_spec
import Submission.Work.IntLib.AddSub.asw_setup_gen_spec
import Submission.Work.IntLib.AddSub.asw_stripLoop_spec
import Submission.Work.IntLib.AddSub.asw_addLoop_proof

/-!
# `IntLib` / add–sub: assembly

* `asw_same_spec` / `asw_diff_spec` — the two sign branches;
* `asw_prog_spec` — `asw_setup ; asw_dispatch ; asw_cleanup`, the whole word;
* `asw_word` — the `WordR` statement for `int a :: int b :: rest`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace AddSub

open HvdH

/-! ## Helpers -/

theorem not_mem_map_bit_gmk (l : List Bool) (k : Stk) :
    ∀ h ∈ l.map Glyph.bit, h ≠ gmk k := by
  intro h hh
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hh
  intro hc
  exact absurd hc (by simp [gmk])

theorem not_mem_rev_map_bit_gmk (l : List Bool) (k : Stk) :
    ∀ h ∈ (l.map Glyph.bit).reverse, h ≠ gmk k := by
  intro h hh
  exact not_mem_map_bit_gmk l k h (List.mem_reverse.mp hh)

theorem sgb_cases {b : ℤ} {flip : Bool} {sgb : Glyph}
    (h : sgb = (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b)) :
    sgb = Glyph.pos ∨ sgb = Glyph.neg := by
  rw [h]; cases flip
  · exact sgnGlyph_cases b
  · exact flipGlyph_cases _ (sgnGlyph_cases b)

/-- The sign-flip sub-program of `asw_setup` (used for subtraction). -/
theorem asw_flipCmd_ev {main : Cmd} :
    ∀ (g : Reg → Glyph) (X : Stk → List Glyph), (g rB = Glyph.pos ∨ g rB = Glyph.neg) →
      ∃ s' n, Ev main asw_flipCmd ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk = X ∧
        s'.reg rB = flipGlyph (g rB) := by
  intro g X hg
  rcases hg with h | h
  · have h1 : Ev main (.set rB Glyph.neg) ⟨g, X⟩ ⟨Function.update g rB Glyph.neg, X⟩ 1 :=
      ev_set' main rB Glyph.neg g X
    refine ⟨_, 2, Ev.iteT (by simpa using h) h1, by omega, rfl, ?_⟩
    simp only [upReg_same, flipGlyph, if_pos h]
  · have h1 : Ev main (.set rB Glyph.pos) ⟨g, X⟩ ⟨Function.update g rB Glyph.pos, X⟩ 1 :=
      ev_set' main rB Glyph.pos g X
    have hne : ¬ (g rB = Glyph.pos) := by rw [h]; decide
    refine ⟨_, 2, Ev.iteF (by simpa using hne) h1, by omega, rfl, ?_⟩
    simp only [upReg_same, flipGlyph, if_neg hne]

/-! ## The same-sign branch -/

theorem asw_same_spec {main : Cmd} :
    ∀ (a b : ℤ) (flip : Bool) (ba bb : List Bool) (sga sgb : Glyph)
      (R1 R2 R3 R4 R5 R6 R7 : List Glyph) (R : List Glyph)
      (g : Reg → Glyph) (X : Stk → List Glyph),
      X 0 = R → X sA = ba.map Glyph.bit ++ gmk sA :: R1 →
      X sB = bb.map Glyph.bit ++ gmk sB :: R2 →
      X sSgA = sga :: gmk sSgA :: R3 → X sSgB = sgb :: gmk sSgB :: R4 →
      X sO1 = gmk sO1 :: R5 → X sO2 = gmk sO2 :: R6 → X sBuf = gmk sBuf :: R7 →
      sga = sgnGlyph a → (sgb = (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b)) →
      ofBits ba = a.natAbs → ofBits bb = b.natAbs → sga = sgb →
      ∃ s' n, Ev main asw_same ⟨g, X⟩ s' n ∧ n ≤ asw_C ba.length bb.length ∧
        s'.stk 0 = (Val.int (a + (if flip then -b else b))).enc ++ R ∧
        s'.stk sA = gmk sA :: R1 ∧ s'.stk sB = gmk sB :: R2 ∧
        s'.stk sSgA = gmk sSgA :: R3 ∧ s'.stk sSgB = gmk sSgB :: R4 ∧
        s'.stk sO1 = gmk sO1 :: R5 ∧ s'.stk sO2 = gmk sO2 :: R6 ∧
        s'.stk sBuf = gmk sBuf :: R7 := by
  intro a b flip ba bb sga sgb R1 R2 R3 R4 R5 R6 R7 R g X
    h0 hA hB hSgA hSgB hO1 hO2 hBuf hga hgb hba hbb heq
  let g1 : Reg → Glyph := Function.update g rC (Glyph.bit false)
  have e1 : Ev main (.set rC (.bit false)) ⟨g, X⟩ ⟨g1, X⟩ 1 := ev_set' main rC (.bit false) g X
  let g2 : Reg → Glyph := Function.update g1 rF gGo
  have e2 : Ev main (.set rF gGo) ⟨g1, X⟩ ⟨g2, X⟩ 1 := ev_set' main rF gGo g1 X
  obtain ⟨s3, n3, e3, hn3, h3a, h3b, h3c, h3d, em', h3o, h3v⟩ :=
    asw_addLoop_spec (main := main) sA sB sO1 (by decide) (by decide) (by decide)
      ba bb [] false R1 R2 R5 g2 X
      (by simp only [g2, g1, upReg_ne (by decide : rC ≠ rF), upReg_same])
      (by simp only [g2, upReg_same]) hA hB (by simpa using hO1)
  have hlen3 : em'.length ≤ n3 := by
    have hL := Ev.stk_length_le e3 sO1
    simp only [stk_mk] at hL
    rw [h3o, hO1] at hL
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_cons] at hL
    omega
  have fr3 : ∀ j : Stk, j ∉ ({sA, sB, sO1} : Finset Stk) → s3.stk j = X j := by
    intro j hj
    exact Ev.frame e3 (cmdTouches_asw_addLoop sA sB sO1) hj
  have h3SgA : s3.stk sSgA = sga :: gmk sSgA :: R3 := by
    rw [fr3 sSgA (by decide)]; exact hSgA
  have h30 : s3.stk 0 = R := by rw [fr3 0 (by decide)]; exact h0
  obtain ⟨s4, n4, e4, hn4, f4o, f4sg, em'', h4is, h4v, h4stk⟩ :=
    asw_finish_spec (main := main) sSgA sO1 (by decide) (by decide) (by decide)
      em' sga R5 R3 R s3.reg s3.stk h3o h3SgA h30 (by rw [hga]; exact sgnGlyph_cases a)
  let g5 : Reg → Glyph := Function.update s4.reg rU ((s4.stk sSgB).headD Glyph.eos)
  let X5 : Stk → List Glyph := Function.update s4.stk sSgB (s4.stk sSgB).tail
  have e5 : Ev main (.pop sSgB rU) s4 ⟨g5, X5⟩ 1 := ev_pop' main sSgB rU s4.reg s4.stk
  have hmain : Ev main asw_same ⟨g, X⟩ ⟨g5, X5⟩ (1 + (1 + (n3 + (n4 + 1)))) := by
    unfold asw_same
    simp only [seqs]
    exact Ev.seq e1 (Ev.seq e2 (Ev.seq e3 (Ev.seq e4 e5)))
  have fr4 : ∀ j : Stk, j ∉ ({sSgA, sO1, (0 : Stk)} : Finset Stk) → s4.stk j = s3.stk j := by
    intro j hj
    exact Ev.frame e4 (cmdTouches_asw_finish sSgA sO1) hj
  have fr5 : ∀ j : Stk, j ≠ sSgB → X5 j = s4.stk j := by
    intro j hj
    show (Function.update s4.stk sSgB (s4.stk sSgB).tail) j = s4.stk j
    rw [Function.update_of_ne hj]
  have hv : ofBits em'' = a.natAbs + b.natAbs := by
    have h1 : ofBits em' = ofBits ba + ofBits bb := by
      rw [h3v]; simp
    rw [h4v, h1, hba, hbb]
  have hz : sgz sga * ((ofBits em'' : ℕ) : ℤ) = a + (if flip then -b else b) := by
    rw [hv, Nat.cast_add]
    exact same_val a b flip (m1 := a.natAbs) (m2 := b.natAbs) (sga := sga) (sgb := sgb)
      (by rfl) (by rfl) hga heq hgb
  have henc := enc_bits_sign h4is (rfl : ofBits em'' = ofBits em'') (sgg := sga)
    (by rw [hga]; exact sgnGlyph_cases a)
  rw [hz] at henc
  have h4SgB : s4.stk sSgB = sgb :: gmk sSgB :: R4 := by
    rw [fr4 sSgB (by decide), fr3 sSgB (by decide)]; exact hSgB
  refine ⟨⟨g5, X5⟩, _, hmain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h2 : n4 ≤ 5 * (em'.length + 1) + 60 := hn4
    have h3 : n3 ≤ 31 * (ba.length + bb.length + 2) := hn3
    unfold asw_C
    omega
  · show X5 0 = (Val.int (a + (if flip then -b else b))).enc ++ R
    rw [fr5 0 (by decide), h4stk]
    calc (if em'' = [] then Glyph.pos else sga) :: (em''.map Glyph.bit ++ [Glyph.iend] ++ R)
        = ((if em'' = [] then Glyph.pos else sga) ::
            (em''.map Glyph.bit ++ [Glyph.iend])) ++ R := by rw [List.cons_append]
      _ = (Val.int (a + (if flip then -b else b))).enc ++ R := by rw [henc]
  · show X5 sA = gmk sA :: R1
    rw [fr5 sA (by decide), fr4 sA (by decide)]; exact h3a
  · show X5 sB = gmk sB :: R2
    rw [fr5 sB (by decide), fr4 sB (by decide)]; exact h3b
  · show X5 sSgA = gmk sSgA :: R3
    rw [fr5 sSgA (by decide)]; exact f4sg
  · show X5 sSgB = gmk sSgB :: R4
    show (Function.update s4.stk sSgB (s4.stk sSgB).tail) sSgB = gmk sSgB :: R4
    rw [Function.update_self, h4SgB]; rfl
  · show X5 sO1 = gmk sO1 :: R5
    rw [fr5 sO1 (by decide)]; exact f4o
  · show X5 sO2 = gmk sO2 :: R6
    rw [fr5 sO2 (by decide), fr4 sO2 (by decide), fr3 sO2 (by decide)]; exact hO2
  · show X5 sBuf = gmk sBuf :: R7
    rw [fr5 sBuf (by decide), fr4 sBuf (by decide), fr3 sBuf (by decide)]; exact hBuf

/-! ## The opposite-sign branch -/

theorem asw_diff_spec {main : Cmd} :
    ∀ (a b : ℤ) (flip : Bool) (ba bb : List Bool) (sga sgb : Glyph)
      (R1 R2 R3 R4 R5 R6 R7 : List Glyph) (R : List Glyph)
      (g : Reg → Glyph) (X : Stk → List Glyph),
      X 0 = R → X sA = ba.map Glyph.bit ++ gmk sA :: R1 →
      X sB = bb.map Glyph.bit ++ gmk sB :: R2 →
      X sSgA = sga :: gmk sSgA :: R3 → X sSgB = sgb :: gmk sSgB :: R4 →
      X sO1 = gmk sO1 :: R5 → X sO2 = gmk sO2 :: R6 → X sBuf = gmk sBuf :: R7 →
      sga = sgnGlyph a → (sgb = (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b)) →
      ofBits ba = a.natAbs → ofBits bb = b.natAbs → sga ≠ sgb →
      ∃ s' n, Ev main asw_diff ⟨g, X⟩ s' n ∧ n ≤ asw_C ba.length bb.length ∧
        s'.stk 0 = (Val.int (a + (if flip then -b else b))).enc ++ R ∧
        s'.stk sA = gmk sA :: R1 ∧ s'.stk sB = gmk sB :: R2 ∧
        s'.stk sSgA = gmk sSgA :: R3 ∧ s'.stk sSgB = gmk sSgB :: R4 ∧
        s'.stk sO1 = gmk sO1 :: R5 ∧ s'.stk sO2 = gmk sO2 :: R6 ∧
        s'.stk sBuf = gmk sBuf :: R7 := by
  intro a b flip ba bb sga sgb R1 R2 R3 R4 R5 R6 R7 R g X
    h0 hA hB hSgA hSgB hO1 hO2 hBuf hga hgb hba hbb hne
  obtain ⟨s1, n1, e1v, hn1, h1a, h1b, e1, e2, bw1, bw2, h1o1, h1o2, h1c, h1d, h1v1, h1v2⟩ :=
    asw_subLoop_spec (main := main) sA sB sO1 sO2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ba bb R1 R2 (gmk sO1 :: R5) (gmk sO2 :: R6) g X
      hA hB (by simpa using hO1) (by simpa using hO2)
  have hl1 : e1.length ≤ n1 := by
    have hL := Ev.stk_length_le e1v sO1
    simp only [stk_mk] at hL
    rw [h1o1, hO1] at hL
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_cons] at hL
    omega
  have hl2 : e2.length ≤ n1 := by
    have hL := Ev.stk_length_le e1v sO2
    simp only [stk_mk] at hL
    rw [h1o2, hO2] at hL
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_cons] at hL
    omega
  have hd1 : ((ofBits e1 : ℕ) : ℤ) =
      ((a.natAbs : ℤ) - (b.natAbs : ℤ)) + 2 ^ e1.length * bw1.toNat := by
    rw [h1v1, hba, hbb]
  have hd2 : ((ofBits e2 : ℕ) : ℤ) =
      -(((a.natAbs : ℤ) - (b.natAbs : ℤ))) + 2 ^ e2.length * bw2.toNat := by
    rw [h1v2, hba, hbb]; ring
  have hdv := diff_val a b flip (sga := sga) (sgb := sgb)
    (m1 := ofBits e1) (m2 := ofBits e2) (n1 := e1.length) (n2 := e2.length)
    (bw1 := bw1) (bw2 := bw2) hd1 hd2 (ofBits_lt_two_pow e1) (ofBits_lt_two_pow e2)
    hga hgb hne
  have fr1 : ∀ j : Stk, j ∉ ({sA, sB, sO1, sO2} : Finset Stk) → s1.stk j = X j := by
    intro j hj
    exact Ev.frame e1v (cmdTouches_asw_subLoop sA sB sO1 sO2) hj
  have h1SgA : s1.stk sSgA = sga :: gmk sSgA :: R3 := by rw [fr1 sSgA (by decide)]; exact hSgA
  have h1SgB : s1.stk sSgB = sgb :: gmk sSgB :: R4 := by rw [fr1 sSgB (by decide)]; exact hSgB
  have h10 : s1.stk 0 = R := by rw [fr1 0 (by decide)]; exact h0
  by_cases hbw : bw1 = false
  · -- first branch: sign of `a`, output `sO1`
    have hcond : (⟨s1.reg, s1.stk⟩ : State).reg rC = Glyph.bit false := by
      show s1.reg rC = Glyph.bit false
      rw [h1c, hbw]
    obtain ⟨s2, n2, e2v, hn2, f2o, f2sg, em'', h2is, h2v, h2stk⟩ :=
      asw_finish_spec (main := main) sSgA sO1 (by decide) (by decide) (by decide)
        e1 sga R5 R3 R s1.reg s1.stk h1o1 h1SgA h10 (by rw [hga]; exact sgnGlyph_cases a)
    have fr2 : ∀ j : Stk, j ∉ ({sSgA, sO1, (0 : Stk)} : Finset Stk) → s2.stk j = s1.stk j := by
      intro j hj
      exact Ev.frame e2v (cmdTouches_asw_finish sSgA sO1) hj
    have h2o2 : s2.stk sO2 = (e2.map Glyph.bit).reverse ++ gmk sO2 :: R6 := by
      rw [fr2 sO2 (by decide)]; exact h1o2
    obtain ⟨s3, n3, e3v, hn3, f3o, -⟩ :=
      asw_clearAt_ev (main := main) sO2 (gmk sO2) rT rF (by decide)
        ((e2.map Glyph.bit).reverse) R6 s2.reg s2.stk
        (not_mem_rev_map_bit_gmk e2 sO2) h2o2
    have hr3 : ∀ j : Stk, j ≠ sO2 → s3.stk j = s2.stk j := by
      intro j hj
      exact Ev.frame e3v (cmdTouches_asw_clearAt sO2 (gmk sO2) rT rF)
        (by simp only [Finset.mem_singleton]; exact hj)
    let g4 : Reg → Glyph := Function.update s3.reg rU ((s3.stk sSgB).headD Glyph.eos)
    let X4 : Stk → List Glyph := Function.update s3.stk sSgB (s3.stk sSgB).tail
    have e4v : Ev main (.pop sSgB rU) s3 ⟨g4, X4⟩ 1 := ev_pop' main sSgB rU s3.reg s3.stk
    have h3SgB : s3.stk sSgB = sgb :: gmk sSgB :: R4 := by
      rw [hr3 sSgB (by decide), fr2 sSgB (by decide)]; exact h1SgB
    have hmain : Ev main asw_diff ⟨g, X⟩ ⟨g4, X4⟩ (n1 + (n2 + (n3 + 1) + 1)) := by
      unfold asw_diff
      simp only [seqs]
      exact Ev.seq e1v (Ev.iteT hcond (Ev.seq e2v (Ev.seq e3v e4v)))
    have hr4 : ∀ j : Stk, j ≠ sSgB → X4 j = s3.stk j := by
      intro j hj
      show (Function.update s3.stk sSgB (s3.stk sSgB).tail) j = s3.stk j
      rw [Function.update_of_ne hj]
    have hz : sgz sga * ((ofBits em'' : ℕ) : ℤ) = a + (if flip then -b else b) := by
      have h := hdv.1 hbw
      rw [h2v]; exact h
    have henc := enc_bits_sign h2is (rfl : ofBits em'' = ofBits em'') (sgg := sga)
      (by rw [hga]; exact sgnGlyph_cases a)
    rw [hz] at henc
    refine ⟨⟨g4, X4⟩, _, hmain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h1' : n2 ≤ 5 * (e1.length + 1) + 60 := hn2
      have h2' : n3 ≤ 5 * ((e2.map Glyph.bit).reverse.length + 1) + 2 := hn3
      have h3' : n1 ≤ 31 * (ba.length + bb.length + 2) := hn1
      simp only [List.length_reverse, List.length_map] at h2'
      unfold asw_C
      omega
    · show X4 0 = (Val.int (a + (if flip then -b else b))).enc ++ R
      rw [hr4 0 (by decide), hr3 0 (by decide), h2stk]
      calc (if em'' = [] then Glyph.pos else sga) :: (em''.map Glyph.bit ++ [Glyph.iend] ++ R)
          = ((if em'' = [] then Glyph.pos else sga) ::
              (em''.map Glyph.bit ++ [Glyph.iend])) ++ R := by rw [List.cons_append]
        _ = (Val.int (a + (if flip then -b else b))).enc ++ R := by rw [henc]
    · show X4 sA = gmk sA :: R1
      rw [hr4 sA (by decide), hr3 sA (by decide), fr2 sA (by decide)]; exact h1a
    · show X4 sB = gmk sB :: R2
      rw [hr4 sB (by decide), hr3 sB (by decide), fr2 sB (by decide)]; exact h1b
    · show X4 sSgA = gmk sSgA :: R3
      rw [hr4 sSgA (by decide), hr3 sSgA (by decide)]; exact f2sg
    · show X4 sSgB = gmk sSgB :: R4
      show (Function.update s3.stk sSgB (s3.stk sSgB).tail) sSgB = gmk sSgB :: R4
      rw [Function.update_self, h3SgB]; rfl
    · show X4 sO1 = gmk sO1 :: R5
      rw [hr4 sO1 (by decide), hr3 sO1 (by decide)]; exact f2o
    · show X4 sO2 = gmk sO2 :: R6
      rw [hr4 sO2 (by decide), f3o]
    · show X4 sBuf = gmk sBuf :: R7
      rw [hr4 sBuf (by decide), hr3 sBuf (by decide), fr2 sBuf (by decide),
        fr1 sBuf (by decide)]; exact hBuf
  · -- second branch: sign of `b`, output `sO2`
    have hbwT : bw1 = true := by cases bw1 <;> simp_all
    have hcond : (⟨s1.reg, s1.stk⟩ : State).reg rC ≠ Glyph.bit false := by
      show s1.reg rC ≠ Glyph.bit false
      rw [h1c, hbwT]; decide
    obtain ⟨s2, n2, e2v, hn2, f2o, f2sg, em'', h2is, h2v, h2stk⟩ :=
      asw_finish_spec (main := main) sSgB sO2 (by decide) (by decide) (by decide)
        e2 sgb R6 R4 R s1.reg s1.stk h1o2 h1SgB h10 (sgb_cases hgb)
    have fr2 : ∀ j : Stk, j ∉ ({sSgB, sO2, (0 : Stk)} : Finset Stk) → s2.stk j = s1.stk j := by
      intro j hj
      exact Ev.frame e2v (cmdTouches_asw_finish sSgB sO2) hj
    have h2o1 : s2.stk sO1 = (e1.map Glyph.bit).reverse ++ gmk sO1 :: R5 := by
      rw [fr2 sO1 (by decide)]; exact h1o1
    obtain ⟨s3, n3, e3v, hn3, f3o, -⟩ :=
      asw_clearAt_ev (main := main) sO1 (gmk sO1) rT rF (by decide)
        ((e1.map Glyph.bit).reverse) R5 s2.reg s2.stk
        (not_mem_rev_map_bit_gmk e1 sO1) h2o1
    have hr3 : ∀ j : Stk, j ≠ sO1 → s3.stk j = s2.stk j := by
      intro j hj
      exact Ev.frame e3v (cmdTouches_asw_clearAt sO1 (gmk sO1) rT rF)
        (by simp only [Finset.mem_singleton]; exact hj)
    let g4 : Reg → Glyph := Function.update s3.reg rU ((s3.stk sSgA).headD Glyph.eos)
    let X4 : Stk → List Glyph := Function.update s3.stk sSgA (s3.stk sSgA).tail
    have e4v : Ev main (.pop sSgA rU) s3 ⟨g4, X4⟩ 1 := ev_pop' main sSgA rU s3.reg s3.stk
    have h3SgA : s3.stk sSgA = sga :: gmk sSgA :: R3 := by
      rw [hr3 sSgA (by decide), fr2 sSgA (by decide)]; exact h1SgA
    have hmain : Ev main asw_diff ⟨g, X⟩ ⟨g4, X4⟩ (n1 + (n2 + (n3 + 1) + 1)) := by
      unfold asw_diff
      simp only [seqs]
      exact Ev.seq e1v (Ev.iteF hcond (Ev.seq e2v (Ev.seq e3v e4v)))
    have hr4 : ∀ j : Stk, j ≠ sSgA → X4 j = s3.stk j := by
      intro j hj
      show (Function.update s3.stk sSgA (s3.stk sSgA).tail) j = s3.stk j
      rw [Function.update_of_ne hj]
    have hz : sgz sgb * ((ofBits em'' : ℕ) : ℤ) = a + (if flip then -b else b) := by
      have h := hdv.2 hbwT
      rw [h2v]; exact h
    have henc := enc_bits_sign h2is (rfl : ofBits em'' = ofBits em'') (sgg := sgb) (sgb_cases hgb)
    rw [hz] at henc
    refine ⟨⟨g4, X4⟩, _, hmain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h1' : n2 ≤ 5 * (e2.length + 1) + 60 := hn2
      have h2' : n3 ≤ 5 * ((e1.map Glyph.bit).reverse.length + 1) + 2 := hn3
      have h3' : n1 ≤ 31 * (ba.length + bb.length + 2) := hn1
      simp only [List.length_reverse, List.length_map] at h2'
      unfold asw_C
      omega
    · show X4 0 = (Val.int (a + (if flip then -b else b))).enc ++ R
      rw [hr4 0 (by decide), hr3 0 (by decide), h2stk]
      calc (if em'' = [] then Glyph.pos else sgb) :: (em''.map Glyph.bit ++ [Glyph.iend] ++ R)
          = ((if em'' = [] then Glyph.pos else sgb) ::
              (em''.map Glyph.bit ++ [Glyph.iend])) ++ R := by rw [List.cons_append]
        _ = (Val.int (a + (if flip then -b else b))).enc ++ R := by rw [henc]
    · show X4 sA = gmk sA :: R1
      rw [hr4 sA (by decide), hr3 sA (by decide), fr2 sA (by decide)]; exact h1a
    · show X4 sB = gmk sB :: R2
      rw [hr4 sB (by decide), hr3 sB (by decide), fr2 sB (by decide)]; exact h1b
    · show X4 sSgA = gmk sSgA :: R3
      show (Function.update s3.stk sSgA (s3.stk sSgA).tail) sSgA = gmk sSgA :: R3
      rw [Function.update_self, h3SgA]; rfl
    · show X4 sSgB = gmk sSgB :: R4
      rw [hr4 sSgB (by decide), hr3 sSgB (by decide)]; exact f2sg
    · show X4 sO1 = gmk sO1 :: R5
      rw [hr4 sO1 (by decide), f3o]
    · show X4 sO2 = gmk sO2 :: R6
      rw [hr4 sO2 (by decide), hr3 sO2 (by decide)]; exact f2o
    · show X4 sBuf = gmk sBuf :: R7
      rw [hr4 sBuf (by decide), hr3 sBuf (by decide), fr2 sBuf (by decide),
        fr1 sBuf (by decide)]; exact hBuf

/-! ## The whole program -/

theorem asw_prog_spec {main : Cmd} (fp : Cmd) (φ : Glyph → Glyph) (flip : Bool)
    (hφ : ∀ g : Glyph, φ g = (if flip then flipGlyph g else g))
    (hfp : ∀ (g : Reg → Glyph) (X : Stk → List Glyph),
      (g rB = Glyph.pos ∨ g rB = Glyph.neg) →
      ∃ s' n, Ev main fp ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk = X ∧ s'.reg rB = φ (g rB))
    (hfpS : cmdTouches fp ⊆ ({0, sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk)) :
    ∀ (a b : ℤ) (R : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      X 0 = (Val.int a).enc ++ (Val.int b).enc ++ R →
      ∃ s' n, Ev main (seqs [asw_setup fp, asw_dispatch, asw_cleanup]) ⟨g, X⟩ s' n ∧
        n ≤ 4000 * (isz a + isz b) + 4000 ∧
        s'.stk 0 = (Val.int (a + (if flip then -b else b))).enc ++ R ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = X k) := by
  intro a b R g X hX
  obtain ⟨s1, n1, e1, hn1, h10, h1A, h1B, h1SgA, h1SgB, h1Buf, h1O1, h1O2⟩ :=
    asw_setup_gen_spec (main := main) fp φ hfp a b R g X hX
  let g2a : Reg → Glyph := Function.update s1.reg rA ((s1.stk sSgA).headD Glyph.eos)
  let g2 : Reg → Glyph := Function.update g2a rB ((s1.stk sSgB).headD Glyph.eos)
  have ep1 : Ev main (.peek sSgA rA) s1 ⟨g2a, s1.stk⟩ 1 := ev_peek' main sSgA rA s1.reg s1.stk
  have ep2 : Ev main (.peek sSgB rB) ⟨g2a, s1.stk⟩ ⟨g2, s1.stk⟩ 1 :=
    ev_peek' main sSgB rB g2a s1.stk
  have hg2a : g2a rA = sgnGlyph a := by
    have h : g2a rA = (s1.stk sSgA).headD Glyph.eos := by simp only [g2a, upReg_same]
    rw [h, h1SgA]
    simp only [List.headD_cons]
    rfl
  have hg2b : g2 rB = (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) := by
    have h : g2 rB = (s1.stk sSgB).headD Glyph.eos := by
      simp only [g2, upReg_ne (by decide : rB ≠ rA), upReg_same]
    rw [h, h1SgB]
    simp only [List.headD_cons]
    exact hφ (sgnGlyph b)
  have hg2a' : g2 rA = sgnGlyph a := by
    have h : g2 rA = g2a rA := by simp only [g2, upReg_ne (by decide : rA ≠ rB)]
    rw [h, hg2a]
  have hS8 : cmdTouches (seqs [asw_setup fp, asw_dispatch, asw_cleanup])
      ⊆ ({0, sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) := by
    have h1 : cmdTouches (asw_setup fp) ⊆ ({0, sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) :=
      (cmdTouches_asw_setup fp).trans (Finset.union_subset (Finset.Subset.refl _) hfpS)
    have h2 : cmdTouches asw_dispatch ⊆ ({0, sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) :=
      cmdTouches_asw_dispatch.trans (by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj ⊢
        tauto)
    have h3 : cmdTouches asw_cleanup ⊆ ({0, sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) :=
      cmdTouches_asw_cleanup.trans (by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj ⊢
        tauto)
    intro j hj
    simp only [seqs, cmdTouches, Finset.mem_union] at hj
    tauto
  -- cleanup step, given the output of either branch
  have cleanup_step : ∀ (s3 : State),
      s3.stk 0 = (Val.int (a + (if flip then -b else b))).enc ++ R →
      s3.stk sBuf = gmk sBuf :: X sBuf → s3.stk sA = gmk sA :: X sA →
      s3.stk sB = gmk sB :: X sB → s3.stk sO1 = gmk sO1 :: X sO1 →
      s3.stk sO2 = gmk sO2 :: X sO2 → s3.stk sSgA = gmk sSgA :: X sSgA →
      s3.stk sSgB = gmk sSgB :: X sSgB →
      ∃ s4 n4, Ev main asw_cleanup s3 s4 n4 ∧ n4 ≤ 65 ∧ s4.stk 0 = s3.stk 0 ∧
        s4.stk sBuf = X sBuf ∧ s4.stk sA = X sA ∧ s4.stk sB = X sB ∧
        s4.stk sO1 = X sO1 ∧ s4.stk sO2 = X sO2 ∧
        s4.stk sSgA = X sSgA ∧ s4.stk sSgB = X sSgB := by
    intro s3 k0 kB kA kB' kO1 kO2 kSgA kSgB
    obtain ⟨s4, n4, e4, hn4, f1, f2, f3, f4, f5, f6, f7⟩ :=
      asw_cleanup_ev (main := main) ([] : List Glyph) ([] : List Glyph) ([] : List Glyph)
        ([] : List Glyph) ([] : List Glyph) ([] : List Glyph) ([] : List Glyph)
        (X sBuf) (X sA) (X sB) (X sO1) (X sO2) (X sSgA) (X sSgB)
        s3.reg s3.stk (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        kB kA kB' kO1 kO2 kSgA kSgB
    have hfr : s4.stk 0 = s3.stk 0 := by
      exact Ev.frame e4 (cmdTouches_asw_cleanup) (by decide)
    exact ⟨s4, n4, e4, by omega, hfr, f1, f2, f3, f4, f5, f6, f7⟩
  have hSgBφ : φ (if b < 0 then Glyph.neg else Glyph.pos)
      = (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) := by
    rw [hφ]; rfl
  -- the four sign cases
  rcases sgnGlyph_cases a with hApos | hAneg
  · have hrA : g2 rA = Glyph.pos := by rw [hg2a', hApos]
    rcases sgb_cases hg2b with hBpos | hBneg
    · have hBpos' : (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) = Glyph.pos :=
        hg2b ▸ hBpos
      have heq : sgnGlyph a = (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) := by
        rw [hApos, hBpos']
      have hrB : g2 rB = Glyph.pos := hBpos
      obtain ⟨s3, n3, e3, hn3, h30, h3A, h3B, h3SgA, h3SgB, h3O1, h3O2, h3Buf⟩ :=
        asw_same_spec (main := main) a b flip ((a.natAbs).bits) ((b.natAbs).bits)
          (sgnGlyph a) (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b)
          (X sA) (X sB) (X sSgA) (X sSgB) (X sO1) (X sO2) (X sBuf) R g2 s1.stk
          h10 h1A h1B h1SgA (by rw [h1SgB, hSgBφ]) h1O1 h1O2 h1Buf rfl rfl
          (ofBits_bits_eq a.natAbs) (ofBits_bits_eq b.natAbs) heq
      have hite : Ev main (.ite rA Glyph.pos (.ite rB Glyph.pos asw_same asw_diff)
          (.ite rB Glyph.pos asw_diff asw_same)) ⟨g2, s1.stk⟩ s3 (n3 + 1 + 1) :=
        Ev.iteT (by simpa using hrA) (Ev.iteT (by simpa using hrB) e3)
      have hdisp : Ev main asw_dispatch s1 s3 (1 + (1 + (n3 + 1 + 1))) := by
        unfold asw_dispatch; simp only [seqs]; exact Ev.seq ep1 (Ev.seq ep2 hite)
      obtain ⟨s4, n4, e4, hn4, f0, fBuf, fA, fB, fO1, fO2, fSgA, fSgB⟩ :=
        cleanup_step s3 h30 h3Buf h3A h3B h3O1 h3O2 h3SgA h3SgB
      refine ⟨s4, _, Ev.seq e1 (Ev.seq hdisp e4), ?_, ?_, ?_⟩
      · have h1 : n1 ≤ 10 * (isz a + isz b) + 200 := hn1
        have h3 : n4 ≤ 65 := hn4
        have h4 : (a.natAbs).bits.length ≤ isz a := by
          rw [isz, Nat.size_eq_bits_len]; omega
        have h5 : (b.natAbs).bits.length ≤ isz b := by
          rw [isz, Nat.size_eq_bits_len]; omega
        have h2 : n3 ≤ asw_C ((a.natAbs).bits.length) ((b.natAbs).bits.length) := hn3
        unfold asw_C at h2
        omega
      · rw [f0, h30]
      · intro k hk
        by_cases hk' : k ∈ ({sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
          rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact fBuf
          · exact fA
          · exact fB
          · exact fO1
          · exact fO2
          · exact fSgA
          · exact fSgB
        · have hframe := Ev.frame (Ev.seq e1 (Ev.seq hdisp e4)) hS8 (by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk' ⊢
            tauto)
          simpa using hframe
    · have hBneg' : (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) = Glyph.neg :=
        hg2b ▸ hBneg
      have hne : sgnGlyph a ≠ (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) := by
        rw [hApos, hBneg']; decide
      have hrB : g2 rB ≠ Glyph.pos := by rw [hBneg]; decide
      obtain ⟨s3, n3, e3, hn3, h30, h3A, h3B, h3SgA, h3SgB, h3O1, h3O2, h3Buf⟩ :=
        asw_diff_spec (main := main) a b flip ((a.natAbs).bits) ((b.natAbs).bits)
          (sgnGlyph a) (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b)
          (X sA) (X sB) (X sSgA) (X sSgB) (X sO1) (X sO2) (X sBuf) R g2 s1.stk
          h10 h1A h1B h1SgA (by rw [h1SgB, hSgBφ]) h1O1 h1O2 h1Buf rfl rfl
          (ofBits_bits_eq a.natAbs) (ofBits_bits_eq b.natAbs) hne
      have hite : Ev main (.ite rA Glyph.pos (.ite rB Glyph.pos asw_same asw_diff)
          (.ite rB Glyph.pos asw_diff asw_same)) ⟨g2, s1.stk⟩ s3 (n3 + 1 + 1) :=
        Ev.iteT (by simpa using hrA) (Ev.iteF (by simpa using hrB) e3)
      have hdisp : Ev main asw_dispatch s1 s3 (1 + (1 + (n3 + 1 + 1))) := by
        unfold asw_dispatch; simp only [seqs]; exact Ev.seq ep1 (Ev.seq ep2 hite)
      obtain ⟨s4, n4, e4, hn4, f0, fBuf, fA, fB, fO1, fO2, fSgA, fSgB⟩ :=
        cleanup_step s3 h30 h3Buf h3A h3B h3O1 h3O2 h3SgA h3SgB
      refine ⟨s4, _, Ev.seq e1 (Ev.seq hdisp e4), ?_, ?_, ?_⟩
      · have h1 : n1 ≤ 10 * (isz a + isz b) + 200 := hn1
        have h3 : n4 ≤ 65 := hn4
        have h4 : (a.natAbs).bits.length ≤ isz a := by
          rw [isz, Nat.size_eq_bits_len]; omega
        have h5 : (b.natAbs).bits.length ≤ isz b := by
          rw [isz, Nat.size_eq_bits_len]; omega
        have h2 : n3 ≤ asw_C ((a.natAbs).bits.length) ((b.natAbs).bits.length) := hn3
        unfold asw_C at h2
        omega
      · rw [f0, h30]
      · intro k hk
        by_cases hk' : k ∈ ({sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
          rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact fBuf
          · exact fA
          · exact fB
          · exact fO1
          · exact fO2
          · exact fSgA
          · exact fSgB
        · have hframe := Ev.frame (Ev.seq e1 (Ev.seq hdisp e4)) hS8 (by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk' ⊢
            tauto)
          simpa using hframe
  · have hrA : g2 rA ≠ Glyph.pos := by rw [hg2a', hAneg]; decide
    rcases sgb_cases hg2b with hBpos | hBneg
    · have hBpos' : (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) = Glyph.pos :=
        hg2b ▸ hBpos
      have hne : sgnGlyph a ≠ (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) := by
        rw [hAneg, hBpos']; decide
      have hrB : g2 rB = Glyph.pos := hBpos
      obtain ⟨s3, n3, e3, hn3, h30, h3A, h3B, h3SgA, h3SgB, h3O1, h3O2, h3Buf⟩ :=
        asw_diff_spec (main := main) a b flip ((a.natAbs).bits) ((b.natAbs).bits)
          (sgnGlyph a) (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b)
          (X sA) (X sB) (X sSgA) (X sSgB) (X sO1) (X sO2) (X sBuf) R g2 s1.stk
          h10 h1A h1B h1SgA (by rw [h1SgB, hSgBφ]) h1O1 h1O2 h1Buf rfl rfl
          (ofBits_bits_eq a.natAbs) (ofBits_bits_eq b.natAbs) hne
      have hite : Ev main (.ite rA Glyph.pos (.ite rB Glyph.pos asw_same asw_diff)
          (.ite rB Glyph.pos asw_diff asw_same)) ⟨g2, s1.stk⟩ s3 (n3 + 1 + 1) :=
        Ev.iteF (by simpa using hrA) (Ev.iteT (by simpa using hrB) e3)
      have hdisp : Ev main asw_dispatch s1 s3 (1 + (1 + (n3 + 1 + 1))) := by
        unfold asw_dispatch; simp only [seqs]; exact Ev.seq ep1 (Ev.seq ep2 hite)
      obtain ⟨s4, n4, e4, hn4, f0, fBuf, fA, fB, fO1, fO2, fSgA, fSgB⟩ :=
        cleanup_step s3 h30 h3Buf h3A h3B h3O1 h3O2 h3SgA h3SgB
      refine ⟨s4, _, Ev.seq e1 (Ev.seq hdisp e4), ?_, ?_, ?_⟩
      · have h1 : n1 ≤ 10 * (isz a + isz b) + 200 := hn1
        have h3 : n4 ≤ 65 := hn4
        have h4 : (a.natAbs).bits.length ≤ isz a := by
          rw [isz, Nat.size_eq_bits_len]; omega
        have h5 : (b.natAbs).bits.length ≤ isz b := by
          rw [isz, Nat.size_eq_bits_len]; omega
        have h2 : n3 ≤ asw_C ((a.natAbs).bits.length) ((b.natAbs).bits.length) := hn3
        unfold asw_C at h2
        omega
      · rw [f0, h30]
      · intro k hk
        by_cases hk' : k ∈ ({sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
          rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact fBuf
          · exact fA
          · exact fB
          · exact fO1
          · exact fO2
          · exact fSgA
          · exact fSgB
        · have hframe := Ev.frame (Ev.seq e1 (Ev.seq hdisp e4)) hS8 (by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk' ⊢
            tauto)
          simpa using hframe
    · have hBneg' : (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) = Glyph.neg :=
        hg2b ▸ hBneg
      have heq : sgnGlyph a = (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b) := by
        rw [hAneg, hBneg']
      have hrB : g2 rB ≠ Glyph.pos := by rw [hBneg]; decide
      obtain ⟨s3, n3, e3, hn3, h30, h3A, h3B, h3SgA, h3SgB, h3O1, h3O2, h3Buf⟩ :=
        asw_same_spec (main := main) a b flip ((a.natAbs).bits) ((b.natAbs).bits)
          (sgnGlyph a) (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b)
          (X sA) (X sB) (X sSgA) (X sSgB) (X sO1) (X sO2) (X sBuf) R g2 s1.stk
          h10 h1A h1B h1SgA (by rw [h1SgB, hSgBφ]) h1O1 h1O2 h1Buf rfl rfl
          (ofBits_bits_eq a.natAbs) (ofBits_bits_eq b.natAbs) heq
      have hite : Ev main (.ite rA Glyph.pos (.ite rB Glyph.pos asw_same asw_diff)
          (.ite rB Glyph.pos asw_diff asw_same)) ⟨g2, s1.stk⟩ s3 (n3 + 1 + 1) :=
        Ev.iteF (by simpa using hrA) (Ev.iteF (by simpa using hrB) e3)
      have hdisp : Ev main asw_dispatch s1 s3 (1 + (1 + (n3 + 1 + 1))) := by
        unfold asw_dispatch; simp only [seqs]; exact Ev.seq ep1 (Ev.seq ep2 hite)
      obtain ⟨s4, n4, e4, hn4, f0, fBuf, fA, fB, fO1, fO2, fSgA, fSgB⟩ :=
        cleanup_step s3 h30 h3Buf h3A h3B h3O1 h3O2 h3SgA h3SgB
      refine ⟨s4, _, Ev.seq e1 (Ev.seq hdisp e4), ?_, ?_, ?_⟩
      · have h1 : n1 ≤ 10 * (isz a + isz b) + 200 := hn1
        have h3 : n4 ≤ 65 := hn4
        have h4 : (a.natAbs).bits.length ≤ isz a := by
          rw [isz, Nat.size_eq_bits_len]; omega
        have h5 : (b.natAbs).bits.length ≤ isz b := by
          rw [isz, Nat.size_eq_bits_len]; omega
        have h2 : n3 ≤ asw_C ((a.natAbs).bits.length) ((b.natAbs).bits.length) := hn3
        unfold asw_C at h2
        omega
      · rw [f0, h30]
      · intro k hk
        by_cases hk' : k ∈ ({sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
          rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact fBuf
          · exact fA
          · exact fB
          · exact fO1
          · exact fO2
          · exact fSgA
          · exact fSgB
        · have hframe := Ev.frame (Ev.seq e1 (Ev.seq hdisp e4)) hS8 (by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk' ⊢
            tauto)
          simpa using hframe

/-! ## The word -/

theorem asw_word (flip : Bool) :
    ∃ K : ℕ, ∀ main, WordR main (asw_prog flip)
      (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest ∧ True)
      (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧
        out = .int (a + (if flip then -b else b)) :: rest)
      (binCost (fun a b => K * (isz a + isz b))) := by
  refine ⟨5000, fun main vs hP s R hR => ?_⟩
  obtain ⟨a, b, rest, hvs, -⟩ := hP
  subst hvs
  have hcontent : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ (encs rest ++ R) := by
    simpa [encs] using hR
  have hφ' : ∀ g : Glyph, (fun g : Glyph => if flip then flipGlyph g else g) g
      = (if flip then flipGlyph g else g) := by
    intro g; rfl
  have hfp : ∀ (g : Reg → Glyph) (X : Stk → List Glyph),
      (g rB = Glyph.pos ∨ g rB = Glyph.neg) →
      ∃ s' n, Ev main (asw_fp flip) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk = X ∧
        s'.reg rB = (fun g : Glyph => if flip then flipGlyph g else g) (g rB) := by
    intro g X hg
    cases flip
    · exact ⟨⟨g, X⟩, 1, ev_skip' main g X, by omega, rfl, rfl⟩
    · exact asw_flipCmd_ev (main := main) g X hg
  have hfpS : cmdTouches (asw_fp flip)
      ⊆ ({0, sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) := by
    cases flip
    · intro j hj
      simp only [asw_fp, cond_false, cmdTouches, Finset.notMem_empty] at hj
    · simpa [asw_fp, cond_true] using
        (cmdTouches_asw_flipCmd : cmdTouches asw_flipCmd ⊆ (∅ : Finset Stk)).trans
          (Finset.empty_subset _)
  obtain ⟨s', n, hev, hn, h0, hk⟩ :=
    asw_prog_spec (main := main) (asw_fp flip) (fun g : Glyph => if flip then flipGlyph g else g)
      flip hφ' hfp hfpS
      a b (encs rest ++ R) s.reg s.stk hcontent
  obtain ⟨n', heval, hn'⟩ := hev
  refine ⟨.int (a + (if flip then -b else b)) :: rest, s', n', ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨a, b, rest, rfl, rfl⟩
  · have hprog : asw_prog flip = seqs [asw_setup (asw_fp flip), asw_dispatch, asw_cleanup] := rfl
    rw [hprog]; exact heval
  · show n' ≤ 5000 * (isz a + isz b)
    have h1 : 2 ≤ isz a := by unfold isz; omega
    have h2 : 2 ≤ isz b := by unfold isz; omega
    omega
  · rw [h0]; simp [encs]
  · intro k hk0
    exact hk k hk0

end AddSub
end Work.IntLib
