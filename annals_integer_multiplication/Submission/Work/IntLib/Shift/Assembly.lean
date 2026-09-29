import Mathlib
import Submission.Work.IntLib.Shift.AssemblyAux
import Submission.Work.IntLib.Shift.parse_ev
import Submission.Work.IntLib.Shift.cleanup_ev
import Submission.Work.IntLib.Shift.finishShl_ev
import Submission.Work.IntLib.Shift.finishShr_ev
import Submission.Work.IntLib.Shift.ShlLoop
import Submission.Work.IntLib.Shift.ShrLoop
import Submission.Work.IntLib.Shift.bitsMulTwoPow
import Submission.Work.IntLib.Shift.bitsDivTwoPow
import Submission.Work.IntLib.Shift.incListFacts
import Submission.Work.IntLib.Shift.natOfMSBFacts
import Submission.Work.IntLib.Shift.shlCostBound
import Submission.Work.IntLib.Shift.shrCostBound
import Submission.Work.IntLib.Shift.tdivPow2
import Submission.Work.IntLib.Shift.fdivPow2
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.encodeNatBridge

/-!
# `IntLib` / shift words: the value-level assembly

The three `WordR` specifications of `shlProg`, `shrTProg`, `shrFProg` (see `Defs.lean`), which give
the `shl`, `shrT` and `shrF` fields of `HvdH.IntLib`.

Each proof chains the four phases of the program (`parse`, the main loop, the `finish` word, and
`cleanup`), first with `Ev` bounds and then with the *value-level* identification of the content of
stack 0 with `Val.enc (.int (f a k))`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace Shift

open HvdH

/-! ## List and integer helpers -/

theorem encs_cons (v : Val) (rest : List Val) : encs (v :: rest) = v.enc ++ encs rest := by
  simp [HvdH.encs]

theorem encs_int_cons (a k : ℤ) (rest : List Val) :
    encs (Val.int a :: Val.int k :: rest) = (Val.int a).enc ++ (Val.int k).enc ++ encs rest := by
  rw [encs_cons, encs_cons, ← List.append_assoc]

/-- The glyph of the sign of an integer, as in `Val.enc`. -/
abbrev sgnG (z : ℤ) : Glyph := if z < 0 then Glyph.neg else Glyph.pos

/-- The integer represented by a sign glyph. -/
abbrev sgzG (g : Glyph) : ℤ := if g = Glyph.pos then 1 else -1

theorem sgnG_def (z : ℤ) : sgnG z = (if z < 0 then Glyph.neg else Glyph.pos) := rfl

theorem sgnG_ne_gmk (z : ℤ) (j : Stk) : sgnG z ≠ gmk j := by
  rw [sgnG_def]
  by_cases h : z < 0
  · rw [if_pos h]; exact (gmk_ne_neg j).symm
  · rw [if_neg h]; exact (gmk_ne_pos j).symm

/-- `Val.enc` of an integer, in terms of `sgnG`. -/
theorem enc_int_sgnG (z : ℤ) :
    (Val.int z).enc
      = sgnG z :: ((Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend]) := by
  rw [enc_int, sgnG_def]

theorem enc_int_sgnG_of_bits {v : ℤ} {sg : Glyph} {em : List Bool}
    (hsg : sg = sgnG v) (hem : em = v.natAbs.bits) :
    sg :: (em.map Glyph.bit ++ [Glyph.iend]) = (Val.int v).enc := by
  rw [hsg, hem, enc_int_sgnG, encodeNat_eq_bits]

theorem toNat_eq_natAbs_of_nonneg {k : ℤ} (hk : 0 ≤ k) : k.toNat = k.natAbs := by
  have h1 : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
  have h2 : ((k.natAbs : ℕ) : ℤ) = k := Int.natAbs_of_nonneg hk
  omega

theorem natAbs_mul_two_pow (a : ℤ) (n : ℕ) : (a * 2 ^ n).natAbs = a.natAbs * 2 ^ n := by
  rw [Int.natAbs_mul, Int.natAbs_pow]
  simp

theorem sgnG_mul_two_pow (a : ℤ) (n : ℕ) : sgnG (a * 2 ^ n) = sgnG a := by
  simp only [sgnG_def]
  have hp : (0 : ℤ) < 2 ^ n := by positivity
  by_cases ha : a < 0
  · have h : a * 2 ^ n < 0 := by nlinarith
    rw [if_pos h, if_pos ha]
  · have h : ¬ (a * 2 ^ n < 0) := by
      have h0 : 0 ≤ a := not_lt.mp ha
      nlinarith
    rw [if_neg h, if_neg ha]

theorem ofBits_eq_zero_iff (l : List Bool) : ofBits l = 0 ↔ ∀ b ∈ l, b = false := by
  induction l with
  | nil => simp [ofBits]
  | cons b t ih =>
    have hstep : (ofBits (b :: t) = 0) ↔ (b = false ∧ ofBits t = 0) := by
      rw [ofBits_cons]
      constructor
      · intro h
        have hb : b = false := by
          cases b with
          | false => rfl
          | true => simp only [Bool.toNat_true] at h; omega
        refine ⟨hb, ?_⟩
        rw [hb] at h
        simp only [Bool.toNat_false, Nat.zero_add] at h
        omega
      · rintro ⟨rfl, h⟩
        simp only [ofBits_cons, h, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    rw [hstep, ih]
    constructor
    · rintro ⟨hb, ht⟩ x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · exact ht x hx
    · intro h
      exact ⟨h b List.mem_cons_self, fun x hx => h x (List.mem_cons_of_mem b hx)⟩

theorem not_true_mem_of_ofBits_eq_zero {l : List Bool} (h : ofBits l = 0) : ¬ true ∈ l := by
  intro hmem
  have h' : true = false := (ofBits_eq_zero_iff l).mp h true hmem
  cases h'

theorem true_mem_bits_iff (n : ℕ) : true ∈ n.bits ↔ n ≠ 0 := by
  constructor
  · intro h hn
    subst hn
    rw [Nat.zero_bits] at h
    exact absurd h List.not_mem_nil
  · intro hn
    rcases isBits_bits n with h | h
    · exact absurd h (bits_ne_nil_iff.mpr hn)
    · rw [List.getLast?_eq_some_iff] at h
      obtain ⟨l, hl⟩ := h
      rw [hl]
      exact List.mem_append_right _ (List.mem_singleton_self true)

theorem natOfMSB_zero_reverse (n : ℕ) : natOfMSB 0 n.bits.reverse = n := by
  rw [natOfMSB_eq]
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [List.reverse_reverse, ofBits_bits]

theorem allZeroNil : AllZero ([] : List Glyph) := fun _ hg => absurd hg List.not_mem_nil

theorem mem_set4 {j : Stk} (h1 : j ≠ sK) (h2 : j ≠ sP) (h3 : j ≠ sA) (h4 : j ≠ sT2) :
    j ∉ ({sK, sP, sA, sT2} : Finset Stk) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨h1, h2, h3, h4⟩

theorem mem_set4shr {j : Stk} (h1 : j ≠ sK) (h2 : j ≠ sP) (h3 : j ≠ sM) (h4 : j ≠ sT2) :
    j ∉ ({sK, sP, sM, sT2} : Finset Stk) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨h1, h2, h3, h4⟩

/-- The stacks a command may modify (with multiplicity); `j ∉ cmdStkList c` is decidable when
`j` is a variable and `c` a concrete program. -/
def cmdStkList : Cmd → List Stk
  | .skip => []
  | .pop k _ => [k]
  | .peek _ _ => []
  | .push k _ => [k]
  | .set _ _ => []
  | .mov _ _ => []
  | .seq c₁ c₂ => cmdStkList c₁ ++ cmdStkList c₂
  | .ite _ _ c₁ c₂ => cmdStkList c₁ ++ cmdStkList c₂
  | .loop _ _ body => cmdStkList body
  | .self => List.finRange 16

theorem Eval_stk_frame {main : Cmd} {c : Cmd} {s s' : State} {n : ℕ} (h : Eval main c s s' n) :
    ∀ j : Stk, j ∉ cmdStkList c → s'.stk j = s.stk j := by
  induction h with
  | skip u => intro j _; rfl
  | pop k r u => intro j hj; exact Function.update_of_ne (by simpa [cmdStkList] using hj) _ _
  | peek k r u => intro j _; rfl
  | push k r u => intro j hj; exact Function.update_of_ne (by simpa [cmdStkList] using hj) _ _
  | set r g u => intro j _; rfl
  | mov dst src u => intro j _; rfl
  | seq h1 h2 ih1 ih2 =>
      intro j hj
      simp only [cmdStkList] at hj
      rw [ih2 j (fun hh => hj (List.mem_append_right _ hh)),
        ih1 j (fun hh => hj (List.mem_append_left _ hh))]
  | iteT hr h1 ih1 =>
      intro j hj
      simp only [cmdStkList] at hj
      exact ih1 j (fun hh => hj (List.mem_append_left _ hh))
  | iteF hr h1 ih1 =>
      intro j hj
      simp only [cmdStkList] at hj
      exact ih1 j (fun hh => hj (List.mem_append_right _ hh))
  | loopF hr => intro j _; rfl
  | loopT hr h1 h2 ih1 ih2 =>
      intro j hj
      simp only [cmdStkList] at hj
      rw [ih2 j hj, ih1 j hj]
  | self h1 ih1 =>
      intro j hj
      simp only [cmdStkList] at hj
      exact absurd (List.mem_finRange j) hj

theorem finishShl_stks (a : Stk) :
    a ∈ cmdStkList finishShl ↔ a = 0 ∨ a = sM ∨ a = sT ∨ a = sA ∨ a = sSg := by
  fin_cases a <;> decide

theorem finishShr_stks (a : Stk) :
    a ∈ cmdStkList finishShr ↔ a = 0 ∨ a = sM ∨ a = sT ∨ a = sSg := by
  fin_cases a <;> decide

theorem finishShl_frame {main : Cmd} {s s' : State} {n : ℕ} (h : Eval main finishShl s s' n) :
    ∀ j : Stk, j ≠ 0 → j ≠ sM → j ≠ sT → j ≠ sA → j ≠ sSg → s'.stk j = s.stk j := by
  intro j h0 h1 h2 h3 h4
  refine Eval_stk_frame h j (fun hmem => ?_)
  rw [finishShl_stks j] at hmem
  rcases hmem with hh | hh | hh | hh | hh
  · exact h0 hh
  · exact h1 hh
  · exact h2 hh
  · exact h3 hh
  · exact h4 hh

theorem finishShr_frame {main : Cmd} {s s' : State} {n : ℕ} (h : Eval main finishShr s s' n) :
    ∀ j : Stk, j ≠ 0 → j ≠ sM → j ≠ sT → j ≠ sSg → s'.stk j = s.stk j := by
  intro j h0 h1 h2 h3
  refine Eval_stk_frame h j (fun hmem => ?_)
  rw [finishShr_stks j] at hmem
  rcases hmem with hh | hh | hh | hh
  · exact h0 hh
  · exact h1 hh
  · exact h2 hh
  · exact h3 hh

theorem val_lt_of_ne {j : Stk} (h0 : j ≠ 0) (h1 : j ≠ sSg) (h2 : j ≠ sM) (h3 : j ≠ sK)
    (h4 : j ≠ sP) (h5 : j ≠ sA) (h6 : j ≠ sT) (h7 : j ≠ sT2) : 7 < j.val := by
  have e0 : j.val ≠ 0 := Fin.val_ne_iff.mpr h0
  have e1 : j.val ≠ 1 := Fin.val_ne_iff.mpr h1
  have e2 : j.val ≠ 2 := Fin.val_ne_iff.mpr h2
  have e3 : j.val ≠ 3 := Fin.val_ne_iff.mpr h3
  have e4 : j.val ≠ 4 := Fin.val_ne_iff.mpr h4
  have e5 : j.val ≠ 5 := Fin.val_ne_iff.mpr h5
  have e6 : j.val ≠ 6 := Fin.val_ne_iff.mpr h6
  have e7 : j.val ≠ 7 := Fin.val_ne_iff.mpr h7
  have hlt : j.val < 16 := j.isLt
  omega

theorem shlWordProg (main : Cmd) :
    WordR main shlProg
      (fun vs => ∃ a k rest, vs = .int a :: .int k :: rest ∧ 0 ≤ k)
      (fun vs out => ∃ a k rest, vs = .int a :: .int k :: rest ∧
        out = .int (a * 2 ^ k.toNat) :: rest)
      (binCost (fun a k => 4000 * (isz a + k.toNat + isz k))) := by
  intro vs hpre s R h0
  obtain ⟨a, k, rest, rfl, hk⟩ := hpre
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int k).enc ++ encs rest ++ R := by
    rw [h0, encs_int_cons]
  obtain ⟨s1, n1, he1, hb1, h01, hSg1, hM1, hK1, hP1, hA1, hT1, hT21, hfr1⟩ :=
    parse_ev main a k rest R s h0'
  -- cost bookkeeping
  have hsa : isz a = a.natAbs.size + 2 := isz_eq a
  have hsk : isz k = k.natAbs.size + 2 := isz_eq k
  have hBal : (a.natAbs.bits).length = a.natAbs.size := Nat.size_eq_bits_len a.natAbs
  have hkbl : (k.natAbs.bits).length = k.natAbs.size := Nat.size_eq_bits_len k.natAbs
  have hnat : natOfMSB 0 (k.natAbs.bits.reverse) = k.toNat := by
    rw [natOfMSB_zero_reverse]
    exact (toNat_eq_natAbs_of_nonneg hk).symm
  have hscost : shlCost 0 (k.natAbs.bits.reverse) ≤ 2 * k.toNat + k.natAbs.size + 2 := by
    have h := shlCostBound 0 (k.natAbs.bits.reverse)
    rw [hnat, List.length_reverse, Nat.size_eq_bits_len] at h
    omega
  -- the main loop
  have hset : Ev main (.set rO gGo) s1 ⟨Function.update s1.reg rO gGo, s1.stk⟩ 1 :=
    ev_set_st main rO gGo s1
  obtain ⟨s2, n2, P', A', he2, hb2, hrO2, hK2, hP2, hPU2, hPlen2, hA2, hAU2, hAlen2, hT22, ho2⟩ :=
    shlLoop_ev main (k.natAbs.bits.reverse) 0 ⟨Function.update s1.reg rO gGo, s1.stk⟩
      (s.stk sK) (s.stk sP) (s.stk sA) (s.stk sT2) [] []
      hK1 hP1 AllUnit.nil rfl hA1 allZeroNil rfl hT21 (upReg_same (g := s1.reg) rO gGo)
  have hPlen2' : P'.length = k.toNat := by rw [hPlen2, hnat]
  have hAlen2' : A'.length = k.toNat := by rw [hAlen2, hnat]
  have hfr2 : ∀ j : Stk, j ∉ ({sK, sP, sA, sT2} : Finset Stk) → s2.stk j = s1.stk j := by
    intro j hj
    rw [ho2 j hj]
  have hsM2 : s2.stk sM = (a.natAbs.bits).map Glyph.bit ++ gmk sM :: s.stk sM := by
    rw [hfr2 sM (mem_set4 (j := sM) (by decide) (by decide) (by decide) (by decide)), hM1]
  have hsSg2 : s2.stk sSg
      = (if a < 0 then Glyph.neg else Glyph.pos) :: gmk sSg :: s.stk sSg := by
    rw [hfr2 sSg (mem_set4 (j := sSg) (by decide) (by decide) (by decide) (by decide)), hSg1]
  have hsT2 : s2.stk sT = gmk sT :: s.stk sT := by
    rw [hfr2 sT (mem_set4 (j := sT) (by decide) (by decide) (by decide) (by decide)), hT1]
  have h0_2 : s2.stk 0 = encs rest ++ R := by
    rw [hfr2 0 (mem_set4 (j := 0) (by decide) (by decide) (by decide) (by decide)), h01]
  have e_loop : Ev main shlLoop s1 s2 (105 * (shlCost 0 (k.natAbs.bits.reverse) + 1) + 1) := by
    rw [shlLoop, seqs_pair]
    exact Ev.seq' hset ⟨n2, he2, hb2⟩ (by omega)
  by_cases hBa : a.natAbs.bits = []
  · -- magnitude zero: `finishShl` takes its empty branch
    have ha0 : a = 0 := by
      have h0z : a.natAbs = 0 := by
        by_contra h
        exact (bits_ne_nil_iff.mpr h) hBa
      exact Int.natAbs_eq_zero.mp h0z
    have hM2 : s2.stk sM = gmk sM :: s.stk sM := by
      rw [hsM2, hBa]; rfl
    obtain ⟨s3, n3, he3, hb3, h03, hfr3⟩ :=
      finishShl_zero_ev main s2 (encs rest) R (s.stk sM) hM2 h0_2
    have eSg : s3.stk sSg = [sgnG a] ++ gmk sSg :: s.stk sSg := by
      rw [hfr3 sSg (by decide), hsSg2, sgnG_def]; rfl
    have eM : s3.stk sM = ([] : List Glyph) ++ gmk sM :: s.stk sM := by
      rw [hfr3 sM (by decide), hM2]; rfl
    have eK : s3.stk sK = ([] : List Glyph) ++ gmk sK :: s.stk sK := by
      rw [hfr3 sK (by decide), hK2]; rfl
    have eP : s3.stk sP = P' ++ gmk sP :: s.stk sP := by
      rw [hfr3 sP (by decide), hP2]
    have eA : s3.stk sA = A' ++ gmk sA :: s.stk sA := by
      rw [hfr3 sA (by decide), hA2]
    have eT : s3.stk sT = ([] : List Glyph) ++ gmk sT :: s.stk sT := by
      rw [hfr3 sT (by decide), hsT2]; rfl
    have eT2 : s3.stk sT2 = ([] : List Glyph) ++ gmk sT2 :: s.stk sT2 := by
      rw [hfr3 sT2 (by decide), hT22]; rfl
    obtain ⟨s4, n4, he4, hb4, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, hf4⟩ :=
      cleanup_ev main [sgnG a] [] [] P' A' [] []
        (s.stk sSg) (s.stk sM) (s.stk sK) (s.stk sP) (s.stk sA) (s.stk sT) (s.stk sT2) s3
        (fun h hh => by rw [List.mem_singleton] at hh; rw [hh]; exact sgnG_ne_gmk a sSg)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => by rw [hPU2 h hh]; exact unit_ne_markerP)
        (fun h hh => by rw [hAU2 h hh]; exact zero_ne_markerA)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => absurd hh List.not_mem_nil)
        eSg eM eK eP eA eT eT2
    have hb4' : n4 ≤ 5 * (P'.length + A'.length + 8) + 40 := by
      simp only [List.length_singleton, List.length_nil] at hb4
      omega
    have e3 : Ev main finishShl s2 s3 6 := ⟨n3, he3, hb3⟩
    have e4 : Ev main cleanup s3 s4 (5 * (P'.length + A'.length + 8) + 40) := ⟨n4, he4, hb4'⟩
    have e_inner : Ev main (.seq finishShl cleanup) s2 s4
        (6 + (5 * (P'.length + A'.length + 8) + 40)) :=
      Ev.seq' e3 e4 (by omega)
    have e_mid : Ev main (.seq shlLoop (.seq finishShl cleanup)) s1 s4
        ((105 * (shlCost 0 (k.natAbs.bits.reverse) + 1) + 1)
          + (6 + (5 * (P'.length + A'.length + 8) + 40))) :=
      Ev.seq' e_loop e_inner (by omega)
    have e_all : Ev main shlProg s s4 (4000 * (isz a + k.toNat + isz k)) := by
      rw [shlProg]
      show Ev main (.seq parse (.seq shlLoop (.seq finishShl cleanup))) s s4
        (4000 * (isz a + k.toNat + isz k))
      refine Ev.seq' ⟨n1, he1, hb1⟩ e_mid (by omega)
    obtain ⟨n, hev, hnle⟩ := e_all
    have henc0 : (Val.int (0 : ℤ)).enc = (Glyph.pos :: [Glyph.iend] : List Glyph) := by
      rw [enc_int, show ((0 : ℤ).natAbs) = 0 from rfl, encodeNat_eq_bits, Nat.zero_bits,
        if_neg (by norm_num : ¬ ((0 : ℤ) < 0))]
      rfl
    have h0_4 : s4.stk 0 = s3.stk 0 :=
      hf4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hstk0 : s4.stk 0 = encs (.int (a * 2 ^ k.toNat) :: rest) ++ R := by
      have hz : a * 2 ^ k.toNat = 0 := by rw [ha0]; ring
      rw [h0_4, h03, hz, encs_cons, henc0, List.append_assoc]
    refine ⟨.int (a * 2 ^ k.toNat) :: rest, s4, n, ⟨a, k, rest, rfl, rfl⟩, hev, hnle, hstk0, ?_⟩
    intro j hj0
    by_cases h1 : j = sSg
    · rw [h1]; exact hSg4
    by_cases h2 : j = sM
    · rw [h2]; exact hM4
    by_cases h3 : j = sK
    · rw [h3]; exact hK4
    by_cases h4 : j = sP
    · rw [h4]; exact hP4
    by_cases h5 : j = sA
    · rw [h5]; exact hA4
    by_cases h6 : j = sT
    · rw [h6]; exact hT4
    by_cases h7 : j = sT2
    · rw [h7]; exact hT24
    · have hgt : 7 < j.val := val_lt_of_ne hj0 h1 h2 h3 h4 h5 h6 h7
      rw [hf4 j h1 h2 h3 h4 h5 h6 h7, hfr3 j hj0, hfr2 j (mem_set4 h3 h4 h5 h7),
        hfr1 j hgt]
  · -- nonzero magnitude
    have ha_ne : a.natAbs ≠ 0 := by
      intro h
      exact hBa (by rw [h]; rfl)
    have hne : (a.natAbs.bits).map Glyph.bit ≠ [] := by
      intro h
      exact hBa (List.map_eq_nil_iff.mp h)
    obtain ⟨s3, n3, he3, hb3, h03, hM3, hA3, hSg3, hT3, hK3, hP3, hT23⟩ :=
      finishShl_ev main (sgnG a) ((a.natAbs.bits).map Glyph.bit) A' (encs rest) R
        (s.stk sM) (s.stk sA) (s.stk sSg) (s.stk sT) s2
        (noMark_bitsG a.natAbs.bits) hAU2 hsM2 hA2 hsSg2 hsT2 h0_2 hne
    have hfr3 : ∀ j : Stk, j ≠ 0 → j ≠ sM → j ≠ sT → j ≠ sA → j ≠ sSg →
        s3.stk j = s2.stk j := finishShl_frame he3
    have eSg : s3.stk sSg = ([] : List Glyph) ++ gmk sSg :: s.stk sSg := by
      rw [hSg3]; rfl
    have eM : s3.stk sM = ([] : List Glyph) ++ gmk sM :: s.stk sM := by
      rw [hM3]; rfl
    have eK : s3.stk sK = ([] : List Glyph) ++ gmk sK :: s.stk sK := by
      rw [hK3, hK2]; rfl
    have eP : s3.stk sP = P' ++ gmk sP :: s.stk sP := by
      rw [hP3, hP2]
    have eA : s3.stk sA = ([] : List Glyph) ++ gmk sA :: s.stk sA := by
      rw [hA3]; rfl
    have eT : s3.stk sT = ([] : List Glyph) ++ gmk sT :: s.stk sT := by
      rw [hT3]; rfl
    have eT2 : s3.stk sT2 = ([] : List Glyph) ++ gmk sT2 :: s.stk sT2 := by
      rw [hT23, hT22]; rfl
    obtain ⟨s4, n4, he4, hb4, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, hf4⟩ :=
      cleanup_ev main [] [] [] P' [] [] []
        (s.stk sSg) (s.stk sM) (s.stk sK) (s.stk sP) (s.stk sA) (s.stk sT) (s.stk sT2) s3
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => by rw [hPU2 h hh]; exact unit_ne_markerP)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => absurd hh List.not_mem_nil)
        eSg eM eK eP eA eT eT2
    have hb4' : n4 ≤ 5 * (P'.length + A'.length + 8) + 40 := by
      simp only [List.length_nil] at hb4
      omega
    have hmapB : ((a.natAbs.bits).map Glyph.bit).length = (a.natAbs.bits).length :=
      List.length_map Glyph.bit
    have e3 : Ev main finishShl s2 s3
        (10 * ((a.natAbs.bits).map Glyph.bit).length + 5 * A'.length + 60) := ⟨n3, he3, hb3⟩
    have e4 : Ev main cleanup s3 s4 (5 * (P'.length + A'.length + 8) + 40) := ⟨n4, he4, hb4'⟩
    have e_inner : Ev main (.seq finishShl cleanup) s2 s4
        ((10 * ((a.natAbs.bits).map Glyph.bit).length + 5 * A'.length + 60)
          + (5 * (P'.length + A'.length + 8) + 40)) :=
      Ev.seq' e3 e4 (by omega)
    have e_mid : Ev main (.seq shlLoop (.seq finishShl cleanup)) s1 s4
        ((105 * (shlCost 0 (k.natAbs.bits.reverse) + 1) + 1)
          + ((10 * ((a.natAbs.bits).map Glyph.bit).length + 5 * A'.length + 60)
            + (5 * (P'.length + A'.length + 8) + 40))) :=
      Ev.seq' e_loop e_inner (by omega)
    have e_all : Ev main shlProg s s4 (4000 * (isz a + k.toNat + isz k)) := by
      rw [shlProg]
      show Ev main (.seq parse (.seq shlLoop (.seq finishShl cleanup))) s s4
        (4000 * (isz a + k.toNat + isz k))
      refine Ev.seq' ⟨n1, he1, hb1⟩ e_mid (by omega)
    obtain ⟨n, hev, hnle⟩ := e_all
    have hbits : (a * 2 ^ k.toNat).natAbs.bits
        = List.replicate k.toNat false ++ a.natAbs.bits := by
      rw [natAbs_mul_two_pow]
      exact bitsMulTwoPow a.natAbs k.toNat ha_ne
    have hA'' : A' = List.replicate k.toNat (Glyph.bit false) := by
      rw [AllEq.eq_replicate hAU2, hAlen2']
      rfl
    have hmap : A' ++ (a.natAbs.bits).map Glyph.bit
        = (List.replicate k.toNat false ++ a.natAbs.bits).map Glyph.bit := by
      rw [hA'', ← List.map_replicate, ← List.map_append]
    have henc : sgnG a :: (A' ++ (a.natAbs.bits).map Glyph.bit ++ [Glyph.iend])
        = (Val.int (a * 2 ^ k.toNat)).enc := by
      rw [hmap]
      exact enc_int_sgnG_of_bits (sgnG_mul_two_pow a k.toNat).symm hbits.symm
    have h0_4 : s4.stk 0 = s3.stk 0 :=
      hf4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hstk0 : s4.stk 0 = encs (.int (a * 2 ^ k.toNat) :: rest) ++ R := by
      rw [h0_4, h03, encs_cons, henc, List.append_assoc]
    refine ⟨.int (a * 2 ^ k.toNat) :: rest, s4, n, ⟨a, k, rest, rfl, rfl⟩, hev, hnle, hstk0, ?_⟩
    intro j hj0
    by_cases h1 : j = sSg
    · rw [h1]; exact hSg4
    by_cases h2 : j = sM
    · rw [h2]; exact hM4
    by_cases h3 : j = sK
    · rw [h3]; exact hK4
    by_cases h4 : j = sP
    · rw [h4]; exact hP4
    by_cases h5 : j = sA
    · rw [h5]; exact hA4
    by_cases h6 : j = sT
    · rw [h6]; exact hT4
    by_cases h7 : j = sT2
    · rw [h7]; exact hT24
    · have hgt : 7 < j.val := val_lt_of_ne hj0 h1 h2 h3 h4 h5 h6 h7
      rw [hf4 j h1 h2 h3 h4 h5 h6 h7, hfr3 j hj0 h2 h6 h5 h1,
        hfr2 j (mem_set4 h3 h4 h5 h7), hfr1 j hgt]


/-! ## Sign and division helpers for the `shr` words -/

theorem sgzG_pos : sgzG Glyph.pos = 1 := by decide

theorem sgzG_neg : sgzG Glyph.neg = -1 := by decide

theorem sgnG_neg_of_neg {a : ℤ} (h : a < 0) : sgnG a = Glyph.neg := by
  rw [sgnG_def, if_pos h]

theorem sgnG_pos_of_nonneg {a : ℤ} (h : 0 ≤ a) : sgnG a = Glyph.pos := by
  rw [sgnG_def, if_neg (not_lt.mpr h)]

theorem sgnG_eq_neg_iff (a : ℤ) : sgnG a = Glyph.neg ↔ a < 0 := by
  rw [sgnG_def]
  by_cases ha : a < 0
  · rw [if_pos ha]
    exact ⟨fun _ => ha, fun _ => rfl⟩
  · rw [if_neg ha]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h ha⟩

theorem sgnG_eq_pos_iff (a : ℤ) : sgnG a = Glyph.pos ↔ 0 ≤ a := by
  rw [sgnG_def]
  by_cases ha : a < 0
  · rw [if_pos ha]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
  · rw [if_neg ha]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem tdivPow2' (a : ℤ) (n : ℕ) :
    a.tdiv ((2 : ℤ) ^ n) = sgzG (sgnG a) * ((a.natAbs / 2 ^ n : ℕ) : ℤ) := by
  rw [tdivPow2]
  by_cases ha : a < 0
  · rw [sgnG_neg_of_neg ha, sgzG_neg, if_pos ha]
  · rw [sgnG_pos_of_nonneg (not_lt.mp ha), sgzG_pos, if_neg ha]

theorem fdivPow2' (a : ℤ) (n : ℕ) :
    a.fdiv ((2 : ℤ) ^ n) = sgzG (sgnG a) *
      (((a.natAbs / 2 ^ n) + (if a < 0 ∧ a.natAbs % 2 ^ n ≠ 0 then 1 else 0) : ℕ) : ℤ) := by
  rw [fdivPow2]
  by_cases ha : a < 0
  · by_cases hc : a.natAbs % 2 ^ n = 0
    · have hnc2 : ¬ (a < 0 ∧ a.natAbs % 2 ^ n ≠ 0) := fun h => h.2 hc
      simp only [sgnG_neg_of_neg ha, sgzG_neg, if_pos ha, if_pos hc, if_neg hnc2,
        Nat.add_zero, neg_one_mul]
    · have hc2 : a < 0 ∧ a.natAbs % 2 ^ n ≠ 0 := ⟨ha, hc⟩
      simp only [sgnG_neg_of_neg ha, sgzG_neg, if_pos ha, if_neg hc, if_pos hc2, neg_one_mul]
  · have hnc2 : ¬ (a < 0 ∧ a.natAbs % 2 ^ n ≠ 0) := fun h => ha h.1
    simp only [sgnG_pos_of_nonneg (not_lt.mp ha), sgzG_pos, if_neg ha, if_neg hnc2,
      Nat.add_zero, one_mul]

/-- Truncated division by a power of two, as the sign times `ofBits` of the remaining bits. -/
theorem tdiv_eq_sg_mul (a : ℤ) (n : ℕ) (B : List Bool) (hq : ofBits B = a.natAbs / 2 ^ n) :
    a.tdiv ((2 : ℤ) ^ n) = sgzG (sgnG a) * (ofBits B : ℤ) := by
  rw [tdivPow2', ← hq]

/-- Floor division by a power of two, as the sign times `ofBits` of the incremented remaining
bits (the increment is the ceiling rounding, needed when `a < 0` and a `true` bit is dropped). -/
theorem fdiv_inc (a : ℤ) (n : ℕ) (B : List Bool) (cond : Prop) [Decidable cond]
    (hq : ofBits B = a.natAbs / 2 ^ n)
    (hcond : cond ↔ (a < 0 ∧ a.natAbs % 2 ^ n ≠ 0)) :
    a.fdiv ((2 : ℤ) ^ n) = sgzG (sgnG a) * (ofBits (if cond then incList B else B) : ℤ) := by
  rw [fdivPow2']
  by_cases ha : a < 0
  · by_cases hc : a.natAbs % 2 ^ n = 0
    · have hnc : ¬ cond := fun h => (hcond.mp h).2 hc
      have hnc2 : ¬ (a < 0 ∧ a.natAbs % 2 ^ n ≠ 0) := fun h => h.2 hc
      simp only [if_neg hnc, if_neg hnc2, hq, Nat.add_zero]
    · have hc' : cond := hcond.mpr ⟨ha, hc⟩
      have hc2 : a < 0 ∧ a.natAbs % 2 ^ n ≠ 0 := ⟨ha, hc⟩
      simp only [if_pos hc', if_pos hc2, ofBits_incList, hq]
  · have hnc : ¬ cond := fun h => ha ((hcond.mp h).1)
    have hnc2 : ¬ (a < 0 ∧ a.natAbs % 2 ^ n ≠ 0) := fun h => ha h.1
    simp only [if_neg hnc, if_neg hnc2, hq, Nat.add_zero]

theorem true_mem_iff_ofBits_ne_zero (l : List Bool) : true ∈ l ↔ ofBits l ≠ 0 := by
  constructor
  · intro h h0
    have h' : true = false := (ofBits_eq_zero_iff l).mp h0 true h
    cases h'
  · intro h
    by_contra hc
    exact h ((ofBits_eq_zero_iff l).mpr (fun b hb => by
      cases b with
      | false => rfl
      | true => exact absurd hb hc))

theorem incList_length_le (B : List Bool) : (incList B).length ≤ B.length + 1 := by
  induction B with
  | nil => simp [incList]
  | cons b bs ih =>
      cases b with
      | false => simp [incList]
      | true =>
          simp only [incList_true, List.length_cons]
          omega

/-! ## The common epilogue of the `shr` words: `finishShr` then `cleanup` -/

/-- The last two phases of `shrTProg`/`shrFProg`: rebuild the answer encoding on stack 0 from the
remaining magnitude region `B` and restore all scratch stacks.  The answer is `.int v` where
`v = sgzG (sgnG a) * ofBits B`. -/
theorem shrFinish_ev (main : Cmd) (s : State) (a : ℤ) (B : List Bool)
    (T0 Rj JSg JM JK JP JA JT JT2 Preg T2reg Areg SKreg : List Glyph) (v : ℤ)
    (hM0 : s.stk sM = B.map Glyph.bit ++ gmk sM :: JM)
    (hSg0 : s.stk sSg = sgnG a :: gmk sSg :: JSg)
    (hT0 : s.stk sT = gmk sT :: JT)
    (h00 : s.stk 0 = T0 ++ Rj)
    (hP0 : s.stk sP = Preg ++ gmk sP :: JP)
    (hA0 : s.stk sA = Areg ++ gmk sA :: JA)
    (hT20 : s.stk sT2 = T2reg ++ gmk sT2 :: JT2)
    (hK0 : s.stk sK = SKreg ++ gmk sK :: JK)
    (huP : ∀ h ∈ Preg, h = gUnit) (huT2 : ∀ h ∈ T2reg, h = gUnit)
    (huA : ∀ h ∈ Areg, h = gZero) (huSK : ∀ h ∈ SKreg, h ≠ gmk sK)
    (hBis : IsBits B) (hv : v = sgzG (sgnG a) * (ofBits B : ℤ)) :
    ∃ (s' : State) (n : ℕ), Eval main (.seq finishShr cleanup) s s' n ∧
      n ≤ 10 * B.length + 40
        + (5 * (Preg.length + T2reg.length + Areg.length + SKreg.length + 8) + 40) ∧
      s'.stk 0 = (Val.int v).enc ++ T0 ++ Rj ∧
      s'.stk sSg = JSg ∧ s'.stk sM = JM ∧ s'.stk sK = JK ∧ s'.stk sP = JP ∧
      s'.stk sA = JA ∧ s'.stk sT = JT ∧ s'.stk sT2 = JT2 ∧
      (∀ j : Stk, j ≠ 0 → j ∉ ({sSg, sM, sK, sP, sA, sT, sT2} : Finset Stk) →
        s'.stk j = s.stk j) := by
  have henc0 : (Val.int (0 : ℤ)).enc = (Glyph.pos :: [Glyph.iend] : List Glyph) := by
    rw [enc_int, show ((0 : ℤ).natAbs) = 0 from rfl, encodeNat_eq_bits, Nat.zero_bits,
      if_neg (by norm_num : ¬ ((0 : ℤ) < 0))]
    rfl
  by_cases hB0 : B = []
  · -- empty magnitude region: `finishShr` takes its `then` branch
    have hM' : s.stk sM = gmk sM :: JM := by
      simp only [hM0, hB0, List.map_nil, List.nil_append]
    obtain ⟨s3, n3, he3, hb3, h03, hfr3⟩ := finishShr_zero_ev main s T0 Rj JM hM' h00
    have hv0 : v = 0 := by rw [hv, hB0]; simp [ofBits]
    have eSg : s3.stk sSg = [sgnG a] ++ gmk sSg :: JSg := by
      simp only [hfr3 sSg (by decide), hSg0, List.cons_append, List.nil_append]
    have eM : s3.stk sM = ([] : List Glyph) ++ gmk sM :: JM := by
      simp only [hfr3 sM (by decide), hM', List.nil_append]
    have eK : s3.stk sK = SKreg ++ gmk sK :: JK := by
      rw [hfr3 sK (by decide), hK0]
    have eP : s3.stk sP = Preg ++ gmk sP :: JP := by
      rw [hfr3 sP (by decide), hP0]
    have eA : s3.stk sA = Areg ++ gmk sA :: JA := by
      rw [hfr3 sA (by decide), hA0]
    have eT : s3.stk sT = ([] : List Glyph) ++ gmk sT :: JT := by
      simp only [hfr3 sT (by decide), hT0, List.nil_append]
    have eT2 : s3.stk sT2 = T2reg ++ gmk sT2 :: JT2 := by
      rw [hfr3 sT2 (by decide), hT20]
    obtain ⟨s4, n4, he4, hb4, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, hf4⟩ :=
      cleanup_ev main [sgnG a] [] SKreg Preg Areg [] T2reg
        JSg JM JK JP JA JT JT2 s3
        (fun h hh => by rw [List.mem_singleton] at hh; rw [hh]; exact sgnG_ne_gmk a sSg)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => huSK h hh)
        (fun h hh => by rw [huP h hh]; exact unit_ne_markerP)
        (fun h hh => by rw [huA h hh]; exact zero_ne_markerA)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => by rw [huT2 h hh]; exact unit_ne_markerT2)
        eSg eM eK eP eA eT eT2
    have hb4' : n4 ≤ 5 * (Preg.length + T2reg.length + Areg.length + SKreg.length + 8) + 40 := by
      simp only [List.length_singleton, List.length_nil] at hb4
      omega
    have e3 : Ev main finishShr s s3 (10 * B.length + 40) :=
      ⟨n3, he3, by simp only [hB0, List.length_nil] at hb3 ⊢; omega⟩
    have e4 : Ev main cleanup s3 s4
        (5 * (Preg.length + T2reg.length + Areg.length + SKreg.length + 8) + 40) :=
      ⟨n4, he4, hb4'⟩
    have eseq : Ev main (.seq finishShr cleanup) s s4
        (10 * B.length + 40
          + (5 * (Preg.length + T2reg.length + Areg.length + SKreg.length + 8) + 40)) :=
      Ev.seq' e3 e4 (by omega)
    obtain ⟨n, hev, hnle⟩ := eseq
    refine ⟨s4, n, hev, hnle, ?_, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, ?_⟩
    · show s4.stk 0 = (Val.int v).enc ++ T0 ++ Rj
      rw [show s4.stk 0 = s3.stk 0 from
          hf4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h03, hv0, henc0]
    · intro j hj0 hjS
      have h43 : s4.stk j = s3.stk j := hf4 j (fun h => hjS (by rw [h]; decide))
        (fun h => hjS (by rw [h]; decide)) (fun h => hjS (by rw [h]; decide))
        (fun h => hjS (by rw [h]; decide)) (fun h => hjS (by rw [h]; decide))
        (fun h => hjS (by rw [h]; decide)) (fun h => hjS (by rw [h]; decide))
      have h32 : s3.stk j = s.stk j := hfr3 j hj0
      rw [h43, h32]
  · -- nonempty magnitude region: `finishShr` takes its `else` branch
    have hne : B.map Glyph.bit ≠ [] := by intro h; exact hB0 (List.map_eq_nil_iff.mp h)
    obtain ⟨s3, n3, he3, hb3, h03, hM3, hSg3, hT3, hK3, hP3, hA3, hT23⟩ :=
      finishShr_ev main (sgnG a) (B.map Glyph.bit) T0 Rj JM JSg JT s
        (noMark_bitsG B) hM0 hSg0 hT0 h00 hne
    have hfr3 : ∀ j : Stk, j ≠ 0 → j ≠ sM → j ≠ sT → j ≠ sSg → s3.stk j = s.stk j :=
      finishShr_frame he3
    have hm : (ofBits B : ℤ) ≠ 0 := by
      have hmNat : ofBits B ≠ 0 := fun h => hB0 ((ofBits_eq_zero_iff_of_isBits B hBis).mp h)
      intro h
      exact hmNat (by exact_mod_cast h)
    have hsign : sgnG v = sgnG a := by
      by_cases ha : a < 0
      · have hsa : sgnG a = Glyph.neg := sgnG_neg_of_neg ha
        have hz : sgzG (sgnG a) = -1 := by rw [hsa]; exact sgzG_neg
        have hv' : v = -((ofBits B : ℕ) : ℤ) := by rw [hv, hz]; ring
        have hvlt : v < 0 := by rw [hv']; omega
        rw [sgnG_neg_of_neg hvlt, hsa]
      · have hsa : sgnG a = Glyph.pos := sgnG_pos_of_nonneg (not_lt.mp ha)
        have hz : sgzG (sgnG a) = 1 := by rw [hsa]; exact sgzG_pos
        have hv' : v = ((ofBits B : ℕ) : ℤ) := by rw [hv, hz]; ring
        have hvpos : ¬ (v < 0) := by rw [hv']; omega
        rw [sgnG_pos_of_nonneg (not_lt.mp hvpos), hsa]
    have hbits : B = v.natAbs.bits := by
      have h1 : v.natAbs = ofBits B := by
        by_cases ha : a < 0
        · have hsa : sgnG a = Glyph.neg := sgnG_neg_of_neg ha
          have hz : sgzG (sgnG a) = -1 := by rw [hsa]; exact sgzG_neg
          rw [hv, hz, neg_one_mul, Int.natAbs_neg, Int.natAbs_natCast]
        · have hsa : sgnG a = Glyph.pos := sgnG_pos_of_nonneg (not_lt.mp ha)
          have hz : sgzG (sgnG a) = 1 := by rw [hsa]; exact sgzG_pos
          rw [hv, hz, one_mul, Int.natAbs_natCast]
      rw [h1, bits_ofBits_of_isBits B hBis]
    have henc : sgnG a :: (B.map Glyph.bit ++ [Glyph.iend]) = (Val.int v).enc :=
      enc_int_sgnG_of_bits hsign.symm hbits
    have eSg : s3.stk sSg = ([] : List Glyph) ++ gmk sSg :: JSg := by
      simp only [hSg3, List.nil_append]
    have eM : s3.stk sM = ([] : List Glyph) ++ gmk sM :: JM := by
      simp only [hM3, List.nil_append]
    have eK : s3.stk sK = SKreg ++ gmk sK :: JK := by
      rw [hK3, hK0]
    have eP : s3.stk sP = Preg ++ gmk sP :: JP := by
      rw [hP3, hP0]
    have eA : s3.stk sA = Areg ++ gmk sA :: JA := by
      rw [hA3, hA0]
    have eT : s3.stk sT = ([] : List Glyph) ++ gmk sT :: JT := by
      simp only [hT3, List.nil_append]
    have eT2 : s3.stk sT2 = T2reg ++ gmk sT2 :: JT2 := by
      rw [hT23, hT20]
    obtain ⟨s4, n4, he4, hb4, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, hf4⟩ :=
      cleanup_ev main [] [] SKreg Preg Areg [] T2reg
        JSg JM JK JP JA JT JT2 s3
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => huSK h hh)
        (fun h hh => by rw [huP h hh]; exact unit_ne_markerP)
        (fun h hh => by rw [huA h hh]; exact zero_ne_markerA)
        (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => by rw [huT2 h hh]; exact unit_ne_markerT2)
        eSg eM eK eP eA eT eT2
    have hb4' : n4 ≤ 5 * (Preg.length + T2reg.length + Areg.length + SKreg.length + 8) + 40 := by
      simp only [List.length_nil] at hb4
      omega
    have e3 : Ev main finishShr s s3 (10 * B.length + 40) :=
      ⟨n3, he3, by rw [List.length_map] at hb3; omega⟩
    have e4 : Ev main cleanup s3 s4
        (5 * (Preg.length + T2reg.length + Areg.length + SKreg.length + 8) + 40) :=
      ⟨n4, he4, hb4'⟩
    have eseq : Ev main (.seq finishShr cleanup) s s4
        (10 * B.length + 40
          + (5 * (Preg.length + T2reg.length + Areg.length + SKreg.length + 8) + 40)) :=
      Ev.seq' e3 e4 (by omega)
    obtain ⟨n, hev, hnle⟩ := eseq
    refine ⟨s4, n, hev, hnle, ?_, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, ?_⟩
    · show s4.stk 0 = (Val.int v).enc ++ T0 ++ Rj
      rw [show s4.stk 0 = s3.stk 0 from
          hf4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h03, henc]
    · intro j hj0 hjS
      have h43 : s4.stk j = s3.stk j := hf4 j (fun h => hjS (by rw [h]; decide))
        (fun h => hjS (by rw [h]; decide)) (fun h => hjS (by rw [h]; decide))
        (fun h => hjS (by rw [h]; decide)) (fun h => hjS (by rw [h]; decide))
        (fun h => hjS (by rw [h]; decide)) (fun h => hjS (by rw [h]; decide))
      have h32 : s3.stk j = s.stk j :=
        hfr3 j hj0 (fun h => hjS (by rw [h]; decide)) (fun h => hjS (by rw [h]; decide))
          (fun h => hjS (by rw [h]; decide))
      rw [h43, h32]

/-! ## `shrTWordProg`: the `shrT` word -/

theorem shrTWordProg (main : Cmd) :
    WordR main shrTProg
      (fun vs => ∃ a k rest, vs = .int a :: .int k :: rest ∧ 0 ≤ k)
      (fun vs out => ∃ a k rest, vs = .int a :: .int k :: rest ∧
        out = .int (Int.tdiv a (2 ^ k.toNat)) :: rest)
      (binCost (fun a k => 4000 * (isz a + isz k))) := by
  intro vs hpre s R h0
  obtain ⟨a, k, rest, rfl, hk⟩ := hpre
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int k).enc ++ encs rest ++ R := by
    rw [h0, encs_int_cons]
  obtain ⟨s1, n1, he1, hb1, h01, hSg1, hM1, hK1, hP1, hA1, hT1, hT21, hfr1⟩ :=
    parse_ev main a k rest R s h0'
  have hsa : isz a = a.natAbs.size + 2 := isz_eq a
  have hsk : isz k = k.natAbs.size + 2 := isz_eq k
  have hBal : (a.natAbs.bits).length = a.natAbs.size := Nat.size_eq_bits_len a.natAbs
  have hkbl : (k.natAbs.bits).length = k.natAbs.size := Nat.size_eq_bits_len k.natAbs
  have hnat : natOfMSB 0 (k.natAbs.bits.reverse) = k.toNat := by
    rw [natOfMSB_zero_reverse]
    exact (toNat_eq_natAbs_of_nonneg hk).symm
  obtain ⟨s2, n2, p', B, SK, he2, hb2, hrO2, hK2, hK2u, hK2l, hM2, ho2, hres2⟩ :=
    shrLoop_ev main (k.natAbs.bits.reverse) (a.natAbs.bits) s1 (s.stk sK) (s.stk sP)
      (s.stk sM) (s.stk sT2) hK1 hP1 hM1 hT21
  have hfr2 : ∀ j : Stk, j ∉ ({sK, sP, sM, sT2} : Finset Stk) → s2.stk j = s1.stk j := by
    intro j hj
    rw [ho2 j hj]
  have hsSg2 : s2.stk sSg
      = (if a < 0 then Glyph.neg else Glyph.pos) :: gmk sSg :: s.stk sSg := by
    rw [hfr2 sSg (mem_set4shr (by decide) (by decide) (by decide) (by decide)), hSg1]
  have hsA2 : s2.stk sA = gmk sA :: s.stk sA := by
    rw [hfr2 sA (mem_set4shr (by decide) (by decide) (by decide) (by decide)), hA1]
  have hsT2 : s2.stk sT = gmk sT :: s.stk sT := by
    rw [hfr2 sT (mem_set4shr (by decide) (by decide) (by decide) (by decide)), hT1]
  have h0_2 : s2.stk 0 = encs rest ++ R := by
    rw [hfr2 0 (mem_set4shr (by decide) (by decide) (by decide) (by decide)), h01]
  have hloopc : shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length
      ≤ 400 * ((a.natAbs.bits).length + (k.natAbs.bits).length + 2) := by
    have h := shrLoopCost_le 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length
    rw [List.length_reverse] at h
    exact h
  have hSKle : SK.length ≤ k.natAbs.size := by
    have h := hK2l
    rw [List.length_reverse, hkbl] at h
    exact h
  rcases hres2 with ⟨hp', hBs, hD, hP2, hT2d, hp'le⟩
    | ⟨hBs, hD, hlen1, hlen2, -, P2, T2c, hP2, hT2d, hP2u, hT2u, hlenP2⟩
  · -- the loop processed all the bits of `k`
    have hp'k : p' = k.toNat := by rw [hp', hnat]
    have hBk : B = (a.natAbs.bits).drop k.toNat := by rw [hBs, hp'k]
    have hBis : IsBits B := by
      rw [hBk, ← bitsDivTwoPow]
      exact isBits_bits (a.natAbs / 2 ^ k.toNat)
    have hofBits : ofBits B = a.natAbs / 2 ^ k.toNat := by
      rw [hBk, ← bitsDivTwoPow]
      exact ofBits_bits (a.natAbs / 2 ^ k.toNat)
    have hp'le' : p' ≤ a.natAbs.size := by
      rw [← hBal]
      exact hp'le
    have hBle : B.length ≤ a.natAbs.size := by
      rw [hBk, List.length_drop, ← hBal]
      omega
    obtain ⟨s4, n4, he4, hb4, hstk4, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, hfr4⟩ :=
      shrFinish_ev main s2 a B (encs rest) R (s.stk sSg) (s.stk sM) (s.stk sK) (s.stk sP)
        (s.stk sA) (s.stk sT) (s.stk sT2) (List.replicate p' gUnit) [] [] SK
        (Int.tdiv a (2 ^ k.toNat)) hM2 hsSg2 hsT2 h0_2 hP2 hsA2 hT2d hK2
        (allUnit_replicate p') (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => absurd hh List.not_mem_nil) hK2u hBis
        (by rw [tdivPow2', ← hofBits])
    have hb4' : n4 ≤ 10 * B.length + 40 + (5 * (p' + SK.length + 8) + 40) := by
      simp only [List.length_replicate, List.length_nil] at hb4
      omega
    have e3 : Ev main shrLoop s1 s2
        (shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length + 3) := ⟨n2, he2, hb2⟩
    have e4 : Ev main (.seq finishShr cleanup) s2 s4
        (10 * B.length + 40 + (5 * (p' + SK.length + 8) + 40)) := ⟨n4, he4, hb4'⟩
    have e_mid : Ev main (.seq shrLoop (.seq finishShr cleanup)) s1 s4
        ((shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length + 3)
          + (10 * B.length + 40 + (5 * (p' + SK.length + 8) + 40))) :=
      Ev.seq' e3 e4 (by omega)
    have e_all : Ev main shrTProg s s4 (4000 * (isz a + isz k)) := by
      rw [shrTProg]
      show Ev main (.seq parse (.seq shrLoop (.seq finishShr cleanup))) s s4
        (4000 * (isz a + isz k))
      refine Ev.seq' ⟨n1, he1, hb1⟩ e_mid (by omega)
    obtain ⟨n, hev, hnle⟩ := e_all
    refine ⟨.int (Int.tdiv a (2 ^ k.toNat)) :: rest, s4, n, ⟨a, k, rest, rfl, rfl⟩,
      hev, hnle, ?_, ?_⟩
    · show s4.stk 0 = encs (.int (Int.tdiv a (2 ^ k.toNat)) :: rest) ++ R
      rw [hstk4, encs_cons]
    · intro j hj0
      by_cases h1 : j = sSg
      · rw [h1]; exact hSg4
      by_cases h2 : j = sM
      · rw [h2]; exact hM4
      by_cases h3 : j = sK
      · rw [h3]; exact hK4
      by_cases h4 : j = sP
      · rw [h4]; exact hP4
      by_cases h5 : j = sA
      · rw [h5]; exact hA4
      by_cases h6 : j = sT
      · rw [h6]; exact hT4
      by_cases h7 : j = sT2
      · rw [h7]; exact hT24
      · have hv : j ∉ ({sSg, sM, sK, sP, sA, sT, sT2} : Finset Stk) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
        have hgt : 7 < j.val := val_lt_of_ne hj0 h1 h2 h3 h4 h5 h6 h7
        have h45 : s4.stk j = s2.stk j := hfr4 j hj0 hv
        have h21 : s2.stk j = s1.stk j := hfr2 j (mem_set4shr h3 h4 h2 h7)
        have h10 : s1.stk j = s.stk j := hfr1 j hgt
        rw [h45, h21, h10]
  · -- the loop stopped as soon as the bits of `|a|` ran out
    have hlen2' : 2 * p' ≤ k.toNat := by rw [← hnat]; exact hlen2
    have hBle : (a.natAbs.bits).length ≤ k.toNat := by omega
    have hlt : a.natAbs < 2 ^ k.toNat := by
      have h1 := ofBits_lt_two_pow (a.natAbs.bits)
      rw [ofBits_bits] at h1
      have h2 : 2 ^ (a.natAbs.bits).length ≤ 2 ^ k.toNat :=
        Nat.pow_le_pow_right (by norm_num) hBle
      omega
    have hofBits : ofBits B = a.natAbs / 2 ^ k.toNat := by
      have hdiv : a.natAbs / 2 ^ k.toNat = 0 := Nat.div_eq_of_lt hlt
      rw [hBs, hdiv]
      rfl
    have hBis : IsBits B := by rw [hBs]; exact isBits_nil
    obtain ⟨s4, n4, he4, hb4, hstk4, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, hfr4⟩ :=
      shrFinish_ev main s2 a B (encs rest) R (s.stk sSg) (s.stk sM) (s.stk sK) (s.stk sP)
        (s.stk sA) (s.stk sT) (s.stk sT2) P2 T2c [] SK
        (Int.tdiv a (2 ^ k.toNat)) hM2 hsSg2 hsT2 h0_2 hP2 hsA2 hT2d hK2
        hP2u hT2u (fun h hh => absurd hh List.not_mem_nil) hK2u hBis
        (by rw [tdivPow2', ← hofBits])
    have hb4' : n4 ≤ 10 * B.length + 40 + (5 * (P2.length + T2c.length + SK.length + 8) + 40) := by
      simp only [List.length_nil] at hb4
      omega
    have hBl : B.length = 0 := by rw [hBs]; rfl
    have hP2le : P2.length + T2c.length ≤ a.natAbs.size + 2 := by
      rw [← hBal]
      exact hlenP2
    have e3 : Ev main shrLoop s1 s2
        (shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length + 3) := ⟨n2, he2, hb2⟩
    have e4 : Ev main (.seq finishShr cleanup) s2 s4
        (10 * B.length + 40 + (5 * (P2.length + T2c.length + SK.length + 8) + 40)) :=
      ⟨n4, he4, hb4'⟩
    have e_mid : Ev main (.seq shrLoop (.seq finishShr cleanup)) s1 s4
        ((shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length + 3)
          + (10 * B.length + 40 + (5 * (P2.length + T2c.length + SK.length + 8) + 40))) :=
      Ev.seq' e3 e4 (by omega)
    have e_all : Ev main shrTProg s s4 (4000 * (isz a + isz k)) := by
      rw [shrTProg]
      show Ev main (.seq parse (.seq shrLoop (.seq finishShr cleanup))) s s4
        (4000 * (isz a + isz k))
      refine Ev.seq' ⟨n1, he1, hb1⟩ e_mid (by omega)
    obtain ⟨n, hev, hnle⟩ := e_all
    refine ⟨.int (Int.tdiv a (2 ^ k.toNat)) :: rest, s4, n, ⟨a, k, rest, rfl, rfl⟩,
      hev, hnle, ?_, ?_⟩
    · show s4.stk 0 = encs (.int (Int.tdiv a (2 ^ k.toNat)) :: rest) ++ R
      rw [hstk4, encs_cons]
    · intro j hj0
      by_cases h1 : j = sSg
      · rw [h1]; exact hSg4
      by_cases h2 : j = sM
      · rw [h2]; exact hM4
      by_cases h3 : j = sK
      · rw [h3]; exact hK4
      by_cases h4 : j = sP
      · rw [h4]; exact hP4
      by_cases h5 : j = sA
      · rw [h5]; exact hA4
      by_cases h6 : j = sT
      · rw [h6]; exact hT4
      by_cases h7 : j = sT2
      · rw [h7]; exact hT24
      · have hv : j ∉ ({sSg, sM, sK, sP, sA, sT, sT2} : Finset Stk) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
        have hgt : 7 < j.val := val_lt_of_ne hj0 h1 h2 h3 h4 h5 h6 h7
        have h45 : s4.stk j = s2.stk j := hfr4 j hj0 hv
        have h21 : s2.stk j = s1.stk j := hfr2 j (mem_set4shr h3 h4 h2 h7)
        have h10 : s1.stk j = s.stk j := hfr1 j hgt
        rw [h45, h21, h10]

/-! ## `shrFWordProg`: the `shrF` word -/

theorem shrFWordProg (main : Cmd) :
    WordR main shrFProg
      (fun vs => ∃ a k rest, vs = .int a :: .int k :: rest ∧ 0 ≤ k)
      (fun vs out => ∃ a k rest, vs = .int a :: .int k :: rest ∧
        out = .int (Int.fdiv a (2 ^ k.toNat)) :: rest)
      (binCost (fun a k => 4000 * (isz a + isz k))) := by
  intro vs hpre s R h0
  obtain ⟨a, k, rest, rfl, hk⟩ := hpre
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int k).enc ++ encs rest ++ R := by
    rw [h0, encs_int_cons]
  obtain ⟨s1, n1, he1, hb1, h01, hSg1, hM1, hK1, hP1, hA1, hT1, hT21, hfr1⟩ :=
    parse_ev main a k rest R s h0'
  have hsa : isz a = a.natAbs.size + 2 := isz_eq a
  have hsk : isz k = k.natAbs.size + 2 := isz_eq k
  have hBal : (a.natAbs.bits).length = a.natAbs.size := Nat.size_eq_bits_len a.natAbs
  have hkbl : (k.natAbs.bits).length = k.natAbs.size := Nat.size_eq_bits_len k.natAbs
  have hnat : natOfMSB 0 (k.natAbs.bits.reverse) = k.toNat := by
    rw [natOfMSB_zero_reverse]
    exact (toNat_eq_natAbs_of_nonneg hk).symm
  obtain ⟨s2, n2, p', B, SK, he2, hb2, hrO2, hK2, hK2u, hK2l, hM2, ho2, hres2⟩ :=
    shrLoop_ev main (k.natAbs.bits.reverse) (a.natAbs.bits) s1 (s.stk sK) (s.stk sP)
      (s.stk sM) (s.stk sT2) hK1 hP1 hM1 hT21
  have hfr2 : ∀ j : Stk, j ∉ ({sK, sP, sM, sT2} : Finset Stk) → s2.stk j = s1.stk j := by
    intro j hj
    rw [ho2 j hj]
  have hsSg2 : s2.stk sSg
      = (if a < 0 then Glyph.neg else Glyph.pos) :: gmk sSg :: s.stk sSg := by
    rw [hfr2 sSg (mem_set4shr (by decide) (by decide) (by decide) (by decide)), hSg1]
  have hsA2 : s2.stk sA = gmk sA :: s.stk sA := by
    rw [hfr2 sA (mem_set4shr (by decide) (by decide) (by decide) (by decide)), hA1]
  have hsT2 : s2.stk sT = gmk sT :: s.stk sT := by
    rw [hfr2 sT (mem_set4shr (by decide) (by decide) (by decide) (by decide)), hT1]
  have h0_2 : s2.stk 0 = encs rest ++ R := by
    rw [hfr2 0 (mem_set4shr (by decide) (by decide) (by decide) (by decide)), h01]
  have hloopc : shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length
      ≤ 400 * ((a.natAbs.bits).length + (k.natAbs.bits).length + 2) := by
    have h := shrLoopCost_le 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length
    rw [List.length_reverse] at h
    exact h
  have hSKle : SK.length ≤ k.natAbs.size := by
    have h := hK2l
    rw [List.length_reverse, hkbl] at h
    exact h
  -- the conditional magnitude increment
  obtain ⟨s2', n2', he2', hb2', hM2', hT2', hfr2'⟩ :=
    incIf_ev main s2 B (s.stk sM) (s.stk sT) hM2 hsT2
  have hinc : n2' ≤ 12 * (B.length + 1) + 34 := hb2'
  have hsSg2' : s2'.stk sSg
      = (if a < 0 then Glyph.neg else Glyph.pos) :: gmk sSg :: s.stk sSg := by
    rw [hfr2' sSg (by decide) (by decide), hsSg2]
  have hsT2' : s2'.stk sT = gmk sT :: s.stk sT := hT2'
  have hsA2' : s2'.stk sA = gmk sA :: s.stk sA := by
    rw [hfr2' sA (by decide) (by decide), hsA2]
  have h0_2' : s2'.stk 0 = encs rest ++ R := by
    rw [hfr2' 0 (by decide) (by decide), h0_2]
  rcases hres2 with ⟨hp', hBs, hD, hP2, hT2d, hp'le⟩
    | ⟨hBs, hD, hlen1, hlen2, -, P2, T2c, hP2, hT2d, hP2u, hT2u, hlenP2⟩
  · -- the loop processed all the bits of `k`
    have hp'k : p' = k.toNat := by rw [hp', hnat]
    have hBk : B = (a.natAbs.bits).drop k.toNat := by rw [hBs, hp'k]
    have hBis : IsBits B := by
      rw [hBk, ← bitsDivTwoPow]
      exact isBits_bits (a.natAbs / 2 ^ k.toNat)
    have hofBits : ofBits B = a.natAbs / 2 ^ k.toNat := by
      rw [hBk, ← bitsDivTwoPow]
      exact ofBits_bits (a.natAbs / 2 ^ k.toNat)
    have hp'le' : p' ≤ a.natAbs.size := by
      rw [← hBal]
      exact hp'le
    have hBle : B.length ≤ a.natAbs.size := by
      rw [hBk, List.length_drop, ← hBal]
      omega
    have hh : (s2.stk sSg).headD .eos = sgnG a := by rw [hsSg2]; rfl
    have hrd : (s2.reg rD = gAny) ↔ true ∈ (a.natAbs.bits).take k.toNat := by
      rw [hD, hp'k]
    have hmod : true ∈ (a.natAbs.bits).take k.toNat ↔ a.natAbs % 2 ^ k.toNat ≠ 0 := by
      rw [← (ofBits_take_drop_bits a.natAbs k.toNat).1]
      exact true_mem_iff_ofBits_ne_zero _
    have hcond : ((s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny)
        ↔ (a < 0 ∧ a.natAbs % 2 ^ k.toNat ≠ 0) := by
      constructor
      · intro h
        exact ⟨(sgnG_eq_neg_iff a).mp (by rw [← hh]; exact h.1), hmod.mp (hrd.mp h.2)⟩
      · intro h
        refine ⟨?_, hrd.mpr (hmod.mpr h.2)⟩
        rw [hh]
        exact (sgnG_eq_neg_iff a).mpr h.1
    have hBisq : IsBits (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
        then incList B else B) := by
      by_cases hc : ((s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny)
      · rw [if_pos hc]; exact isBits_incList B hBis
      · rw [if_neg hc]; exact hBis
    have hfdiv : Int.fdiv a (2 ^ k.toNat)
        = sgzG (sgnG a)
          * (ofBits (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
              then incList B else B) : ℤ) :=
      fdiv_inc a k.toNat B _ hofBits hcond
    have hP2' : s2'.stk sP = List.replicate p' gUnit ++ gmk sP :: s.stk sP := by
      rw [hfr2' sP (by decide) (by decide), hP2]
    have hT2d' : s2'.stk sT2 = gmk sT2 :: s.stk sT2 := by
      rw [hfr2' sT2 (by decide) (by decide), hT2d]
    have hK2' : s2'.stk sK = SK ++ gmk sK :: s.stk sK := by
      rw [hfr2' sK (by decide) (by decide), hK2]
    have hBsqle : (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
        then incList B else B).length ≤ B.length + 1 := by
      by_cases hc : ((s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny)
      · rw [if_pos hc]; exact incList_length_le B
      · rw [if_neg hc]; omega
    obtain ⟨s4, n4, he4, hb4, hstk4, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, hfr4⟩ :=
      shrFinish_ev main s2' a
        (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny then incList B else B)
        (encs rest) R (s.stk sSg) (s.stk sM) (s.stk sK) (s.stk sP)
        (s.stk sA) (s.stk sT) (s.stk sT2) (List.replicate p' gUnit) [] [] SK
        (Int.fdiv a (2 ^ k.toNat)) hM2' hsSg2' hsT2' h0_2' hP2' hsA2' hT2d' hK2'
        (allUnit_replicate p') (fun h hh => absurd hh List.not_mem_nil)
        (fun h hh => absurd hh List.not_mem_nil) hK2u hBisq hfdiv
    have hb4' : n4 ≤ 10 * (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
        then incList B else B).length + 40 + (5 * (p' + SK.length + 8) + 40) := by
      simp only [List.length_replicate, List.length_nil] at hb4
      omega
    have e3 : Ev main shrLoop s1 s2
        (shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length + 3) := ⟨n2, he2, hb2⟩
    have e4 : Ev main incIf s2 s2' (12 * (B.length + 1) + 34) := ⟨n2', he2', hinc⟩
    have e5 : Ev main (.seq finishShr cleanup) s2' s4
        (10 * (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
          then incList B else B).length + 40 + (5 * (p' + SK.length + 8) + 40)) :=
      ⟨n4, he4, hb4'⟩
    have e_mid2 : Ev main (.seq incIf (.seq finishShr cleanup)) s2 s4
        ((12 * (B.length + 1) + 34)
          + (10 * (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
            then incList B else B).length + 40 + (5 * (p' + SK.length + 8) + 40))) :=
      Ev.seq' e4 e5 (by omega)
    have e_mid : Ev main (.seq shrLoop (.seq incIf (.seq finishShr cleanup))) s1 s4
        ((shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length + 3)
          + ((12 * (B.length + 1) + 34)
            + (10 * (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
              then incList B else B).length + 40 + (5 * (p' + SK.length + 8) + 40)))) :=
      Ev.seq' e3 e_mid2 (by omega)
    have e_all : Ev main shrFProg s s4 (4000 * (isz a + isz k)) := by
      rw [shrFProg]
      show Ev main (.seq parse (.seq shrLoop (.seq incIf (.seq finishShr cleanup)))) s s4
        (4000 * (isz a + isz k))
      refine Ev.seq' ⟨n1, he1, hb1⟩ e_mid (by omega)
    obtain ⟨n, hev, hnle⟩ := e_all
    refine ⟨.int (Int.fdiv a (2 ^ k.toNat)) :: rest, s4, n, ⟨a, k, rest, rfl, rfl⟩,
      hev, hnle, ?_, ?_⟩
    · show s4.stk 0 = encs (.int (Int.fdiv a (2 ^ k.toNat)) :: rest) ++ R
      rw [hstk4, encs_cons]
    · intro j hj0
      by_cases h1 : j = sSg
      · rw [h1]; exact hSg4
      by_cases h2 : j = sM
      · rw [h2]; exact hM4
      by_cases h3 : j = sK
      · rw [h3]; exact hK4
      by_cases h4 : j = sP
      · rw [h4]; exact hP4
      by_cases h5 : j = sA
      · rw [h5]; exact hA4
      by_cases h6 : j = sT
      · rw [h6]; exact hT4
      by_cases h7 : j = sT2
      · rw [h7]; exact hT24
      · have hv : j ∉ ({sSg, sM, sK, sP, sA, sT, sT2} : Finset Stk) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
        have hgt : 7 < j.val := val_lt_of_ne hj0 h1 h2 h3 h4 h5 h6 h7
        have h45 : s4.stk j = s2'.stk j := hfr4 j hj0 hv
        have h52 : s2'.stk j = s2.stk j := hfr2' j h2 h6
        have h21 : s2.stk j = s1.stk j := hfr2 j (mem_set4shr h3 h4 h2 h7)
        have h10 : s1.stk j = s.stk j := hfr1 j hgt
        rw [h45, h52, h21, h10]
  · -- the loop stopped as soon as the bits of `|a|` ran out
    have hlen2' : 2 * p' ≤ k.toNat := by rw [← hnat]; exact hlen2
    have hBle : (a.natAbs.bits).length ≤ k.toNat := by omega
    have hlt : a.natAbs < 2 ^ k.toNat := by
      have h1 := ofBits_lt_two_pow (a.natAbs.bits)
      rw [ofBits_bits] at h1
      have h2 : 2 ^ (a.natAbs.bits).length ≤ 2 ^ k.toNat :=
        Nat.pow_le_pow_right (by norm_num) hBle
      omega
    have hofBits : ofBits B = a.natAbs / 2 ^ k.toNat := by
      have hdiv : a.natAbs / 2 ^ k.toNat = 0 := Nat.div_eq_of_lt hlt
      rw [hBs, hdiv]
      rfl
    have hBis : IsBits B := by rw [hBs]; exact isBits_nil
    have hmod2 : a.natAbs % 2 ^ k.toNat = a.natAbs := Nat.mod_eq_of_lt hlt
    have hh : (s2.stk sSg).headD .eos = sgnG a := by rw [hsSg2]; rfl
    have hcond : ((s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny)
        ↔ (a < 0 ∧ a.natAbs % 2 ^ k.toNat ≠ 0) := by
      constructor
      · intro h
        refine ⟨(sgnG_eq_neg_iff a).mp (by rw [← hh]; exact h.1), ?_⟩
        rw [hmod2]
        exact (true_mem_bits_iff a.natAbs).mp (hD.mp h.2)
      · intro h
        refine ⟨?_, hD.mpr ((true_mem_bits_iff a.natAbs).mpr ?_)⟩
        · rw [hh]
          exact (sgnG_eq_neg_iff a).mpr h.1
        · rw [← hmod2]
          exact h.2
    have hBisq : IsBits (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
        then incList B else B) := by
      by_cases hc : ((s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny)
      · rw [if_pos hc]; exact isBits_incList B hBis
      · rw [if_neg hc]; exact hBis
    have hfdiv : Int.fdiv a (2 ^ k.toNat)
        = sgzG (sgnG a)
          * (ofBits (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
              then incList B else B) : ℤ) :=
      fdiv_inc a k.toNat B _ hofBits hcond
    have hP2' : s2'.stk sP = P2 ++ gmk sP :: s.stk sP := by
      rw [hfr2' sP (by decide) (by decide), hP2]
    have hT2d' : s2'.stk sT2 = T2c ++ gmk sT2 :: s.stk sT2 := by
      rw [hfr2' sT2 (by decide) (by decide), hT2d]
    have hK2' : s2'.stk sK = SK ++ gmk sK :: s.stk sK := by
      rw [hfr2' sK (by decide) (by decide), hK2]
    have hBsqle : (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
        then incList B else B).length ≤ B.length + 1 := by
      by_cases hc : ((s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny)
      · rw [if_pos hc]; exact incList_length_le B
      · rw [if_neg hc]; omega
    obtain ⟨s4, n4, he4, hb4, hstk4, hSg4, hM4, hK4, hP4, hA4, hT4, hT24, hfr4⟩ :=
      shrFinish_ev main s2' a
        (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny then incList B else B)
        (encs rest) R (s.stk sSg) (s.stk sM) (s.stk sK) (s.stk sP)
        (s.stk sA) (s.stk sT) (s.stk sT2) P2 T2c [] SK
        (Int.fdiv a (2 ^ k.toNat)) hM2' hsSg2' hsT2' h0_2' hP2' hsA2' hT2d' hK2'
        hP2u hT2u (fun h hh => absurd hh List.not_mem_nil) hK2u hBisq hfdiv
    have hb4' : n4 ≤ 10 * (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
        then incList B else B).length + 40
        + (5 * (P2.length + T2c.length + SK.length + 8) + 40) := by
      simp only [List.length_nil] at hb4
      omega
    have hBl : B.length = 0 := by rw [hBs]; rfl
    have hP2le : P2.length + T2c.length ≤ a.natAbs.size + 2 := by
      rw [← hBal]
      exact hlenP2
    have e3 : Ev main shrLoop s1 s2
        (shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length + 3) := ⟨n2, he2, hb2⟩
    have e4 : Ev main incIf s2 s2' (12 * (B.length + 1) + 34) := ⟨n2', he2', hinc⟩
    have e5 : Ev main (.seq finishShr cleanup) s2' s4
        (10 * (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
          then incList B else B).length + 40
          + (5 * (P2.length + T2c.length + SK.length + 8) + 40)) :=
      ⟨n4, he4, hb4'⟩
    have e_mid2 : Ev main (.seq incIf (.seq finishShr cleanup)) s2 s4
        ((12 * (B.length + 1) + 34)
          + (10 * (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
            then incList B else B).length + 40
            + (5 * (P2.length + T2c.length + SK.length + 8) + 40))) :=
      Ev.seq' e4 e5 (by omega)
    have e_mid : Ev main (.seq shrLoop (.seq incIf (.seq finishShr cleanup))) s1 s4
        ((shrLoopCost 0 (k.natAbs.bits.reverse) (a.natAbs.bits).length + 3)
          + ((12 * (B.length + 1) + 34)
            + (10 * (if (s2.stk sSg).headD .eos = Glyph.neg ∧ s2.reg rD = gAny
              then incList B else B).length + 40
              + (5 * (P2.length + T2c.length + SK.length + 8) + 40)))) :=
      Ev.seq' e3 e_mid2 (by omega)
    have e_all : Ev main shrFProg s s4 (4000 * (isz a + isz k)) := by
      rw [shrFProg]
      show Ev main (.seq parse (.seq shrLoop (.seq incIf (.seq finishShr cleanup)))) s s4
        (4000 * (isz a + isz k))
      refine Ev.seq' ⟨n1, he1, hb1⟩ e_mid (by omega)
    obtain ⟨n, hev, hnle⟩ := e_all
    refine ⟨.int (Int.fdiv a (2 ^ k.toNat)) :: rest, s4, n, ⟨a, k, rest, rfl, rfl⟩,
      hev, hnle, ?_, ?_⟩
    · show s4.stk 0 = encs (.int (Int.fdiv a (2 ^ k.toNat)) :: rest) ++ R
      rw [hstk4, encs_cons]
    · intro j hj0
      by_cases h1 : j = sSg
      · rw [h1]; exact hSg4
      by_cases h2 : j = sM
      · rw [h2]; exact hM4
      by_cases h3 : j = sK
      · rw [h3]; exact hK4
      by_cases h4 : j = sP
      · rw [h4]; exact hP4
      by_cases h5 : j = sA
      · rw [h5]; exact hA4
      by_cases h6 : j = sT
      · rw [h6]; exact hT4
      by_cases h7 : j = sT2
      · rw [h7]; exact hT24
      · have hv : j ∉ ({sSg, sM, sK, sP, sA, sT, sT2} : Finset Stk) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
        have hgt : 7 < j.val := val_lt_of_ne hj0 h1 h2 h3 h4 h5 h6 h7
        have h45 : s4.stk j = s2'.stk j := hfr4 j hj0 hv
        have h52 : s2'.stk j = s2.stk j := hfr2' j h2 h6
        have h21 : s2.stk j = s1.stk j := hfr2 j (mem_set4shr h3 h4 h2 h7)
        have h10 : s1.stk j = s.stk j := hfr1 j hgt
        rw [h45, h52, h21, h10]

end Shift
end Work.IntLib
