import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.IntLib.UR.Main
import Submission.Work.IntLib.urRebuildK32
import Submission.Work.IntLib.unaryCopySC
import Submission.Work.IntLib.loopBodyStep
import Submission.Work.IntLib.preSetupPhaseV2
import Submission.Work.IntLib.preMainPhaseV2
import Submission.Work.IntLib.postPhaseV3
import Submission.Work.IntLib.outOrderFull
import Submission.Work.IntLib.outOrderLen
import Submission.Work.IntLib.lsumBound
import Submission.Work.IntLib.chunkCostN

/-!
# Assembly of the `chunk` word

`chunkWord_chunk` is the first conjunct of `Work.IntLib.chunkWord`: the program
`chunkProg copyProg (UR.urProg sR sN sCN sCT) (UR.urProg sR sB sCB sCT)` (with `copyProg` the
`unaryCopy` gadget for the pair of counters `sCB`, `sCW`) maps the value stack
`int x :: int b :: int N :: rest` to `intList (chunks x b N) :: rest` in
`O(isz x + N*(b+1) + isz b + isz N)` steps.

The proof chains the phases (`preSetupPhaseV2`, the `N = 0` / `N ≠ 0` branch, `postPhaseV3`)
through the `Ev` composition lemmas, and finishes with `chunkCostN` (loop arithmetic) resp. a
short arithmetic estimate for the `N = 0` branch.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## Small helpers -/

theorem encs_cons' (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := by
  simp [encs]

theorem encs_three (x b N : ℕ) (rest : List Val) :
    encs (.int x :: .int b :: .int N :: rest) =
      Val.enc (.int (x : ℤ)) ++ Val.enc (.int (b : ℤ)) ++ Val.enc (.int (N : ℤ)) ++ encs rest := by
  simp only [encs_cons', List.append_assoc]

theorem encs_nil_cons (vs : List Val) : encs (.nil :: vs) = [Glyph.nil] ++ encs vs := by
  simp [encs_cons', Val.enc]

theorem two_le_iszEv (z : ℤ) : 2 ≤ isz z := by
  simp [HvdH.isz]

theorem mem_nil_false {α : Type*} {a : α} (h : a ∈ ([] : List α)) : False := by cases h

theorem mem_of_noMark {l : List Glyph} {g : Glyph} (h : Shift.NoMark l) (hg : g ∈ l) (k : Stk) :
    g ≠ Shift.gmk k := by
  have h' : ∀ g ∈ l, ∀ k : Stk, g ≠ Shift.gmk k := h
  exact h' g hg k

theorem noMark_enc_mem (v : Val) {g : Glyph} (hg : g ∈ v.enc) (k : Stk) : g ≠ Shift.gmk k :=
  mem_of_noMark (noMark_enc v) hg k

theorem noMark_int_mem (z : ℤ) {g : Glyph} (hg : g ∈ Val.enc (.int z)) (k : Stk) :
    g ≠ Shift.gmk k := noMark_enc_mem (.int z) hg k

theorem Yinit_sCT (b N : ℕ) (X₀ : Stk → List Glyph) :
    Yinit b N X₀ sCT = Shift.gmk sCT :: X₀ sCT := by
  have h1 : ¬ (sCT = sB) := by decide
  have h2 : ¬ (sCT = sN) := by decide
  have h3 : ¬ (sCT = sCB) := by decide
  simp only [Yinit, h1, h2, h3, ↓reduceIte]

theorem lStk_init_sX (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) :
    lStk x b N (Yinit b N X₀) k sX
      = (streamOf x).drop (cg x k) ++ Shift.gmk sX :: X₀ sX := by
  rw [lStk_sX, Yinit_other b N X₀ (by decide) (by decide) (by decide) (by decide)]

theorem lStk_init_sR (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) :
    lStk x b N (Yinit b N X₀) k sR
      = ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++ Shift.gmk sR :: X₀ sR := by
  rw [lStk_sR, Yinit_other b N X₀ (by decide) (by decide) (by decide) (by decide)]

theorem lStk_init_sS (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) :
    lStk x b N (Yinit b N X₀) k sS
      = (outOrder (pbits x b N) b k).reverse ++ Shift.gmk sS :: X₀ sS := by
  rw [lStk_sS, Yinit_other b N X₀ (by decide) (by decide) (by decide) (by decide)]

theorem lStk_init_sZ (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) :
    lStk x b N (Yinit b N X₀) k sZ = Shift.gmk sZ :: X₀ sZ := by
  rw [lStk_sZ, Yinit_other b N X₀ (by decide) (by decide) (by decide) (by decide)]

theorem lStk_init_sB (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) :
    lStk x b N (Yinit b N X₀) k sB = Val.enc (.int (b : ℤ)) ++ Shift.gmk sB :: X₀ sB := by
  rw [lStk_other x b N (Yinit b N X₀) k (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), Yinit_sB]

theorem lStk_init_sN (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) :
    lStk x b N (Yinit b N X₀) k sN = Val.enc (.int (N : ℤ)) ++ Shift.gmk sN :: X₀ sN := by
  rw [lStk_other x b N (Yinit b N X₀) k (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), Yinit_sN]

theorem lStk_init_sCT (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) :
    lStk x b N (Yinit b N X₀) k sCT = Shift.gmk sCT :: X₀ sCT := by
  rw [lStk_other x b N (Yinit b N X₀) k (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), Yinit_sCT]

theorem lStk_init_sCB (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) :
    lStk x b N (Yinit b N X₀) k sCB
      = (List.replicate b gTok ++ [gEnd]) ++ Shift.gmk sCB :: X₀ sCB := by
  rw [lStk_other x b N (Yinit b N X₀) k (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), Yinit_sCB]
  simp [Unary, List.append_assoc]

theorem lStk_init_sCW (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) (h : wcnt b k = 0) :
    lStk x b N (Yinit b N X₀) k sCW = [gEnd] ++ Shift.gmk sCW :: X₀ sCW := by
  rw [lStk_sCW, h, Yinit_other b N X₀ (by decide) (by decide) (by decide) (by decide)]
  rfl

theorem lStk_init_sCN (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) (h : N - k / b = 0) :
    lStk x b N (Yinit b N X₀) k sCN = [gEnd] ++ Shift.gmk sCN :: X₀ sCN := by
  rw [lStk_sCN, h, Yinit_other b N X₀ (by decide) (by decide) (by decide) (by decide)]
  rfl

theorem lStk_init_other (x b N : ℕ) (X₀ : Stk → List Glyph) (k : ℕ) {j : Stk}
    (h1 : j ≠ sX) (h2 : j ≠ sB) (h3 : j ≠ sN) (h4 : j ≠ sR) (h5 : j ≠ sS) (h6 : j ≠ sCW)
    (h7 : j ≠ sCB) (h8 : j ≠ sCT) (h9 : j ≠ sCN) (h10 : j ≠ sZ) :
    lStk x b N (Yinit b N X₀) k j = X₀ j := by
  rw [lStk_other x b N (Yinit b N X₀) k h1 h4 h5 h6 h9 h10,
      Yinit_other b N X₀ h2 h3 h7 h8]

/-! ## The assembly -/

theorem chunkWord_chunk : ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (x b N : ℕ), 1 ≤ b →
    x < 2 ^ (b * N) →
    HvdH.WordR main p (fun vs => ∃ rest, vs = .int x :: .int b :: .int N :: rest)
      (fun vs out => ∃ rest, vs = .int x :: .int b :: .int N :: rest ∧
        out = HvdH.intList (HvdH.chunks x b N) :: rest)
      (fun _ => K * (HvdH.isz x + N * (b + 1) + HvdH.isz b + HvdH.isz N)) := by
  obtain ⟨copyProg, KC, hcopySC⟩ := unaryCopySC
  refine ⟨chunkProg copyProg (UR.urProg sR sN sCN sCT) (UR.urProg sR sB sCB sCT),
    4 * (KC + 1000), ?_⟩
  intro main x b N hb hxN vs hPre s R hstk0
  obtain ⟨rest, rfl⟩ := hPre
  -- the contents below everything the word touches
  set X₀ : Stk → List Glyph := Function.update s.stk 0 (encs rest ++ R) with hX₀
  have hX₀0 : X₀ 0 = encs rest ++ R := by rw [hX₀]; exact Function.update_self ..
  have hX₀ne : ∀ j : Stk, j ≠ 0 → X₀ j = s.stk j := by
    intro j hj; rw [hX₀]; exact Function.update_of_ne hj _ _
  have hinit : Xinit x b N X₀ = s.stk := by
    funext j
    by_cases hj : j = 0
    · subst hj
      simp only [Xinit, ↓reduceIte]
      rw [hX₀0, hstk0, encs_three]
      simp only [List.append_assoc]
    · simp only [Xinit, hj, hX₀ne j hj, ↓reduceIte]
  have hstate : (⟨s.reg, Xinit x b N X₀⟩ : State) = s := by rw [hinit]
  -- the rebuild gadget, used twice
  have hrebuildN : ∀ (g : Reg → Glyph) (X : Stk → List Glyph) (bs : List Bool)
      (Gs Gt Gc Gs' : List Glyph),
      X sR = (Glyph.iend :: (bs.reverse.map Glyph.bit ++ [Glyph.pos])) ++ Shift.gmk sR :: Gs →
      X sN = Gt → X sCN = Gc → X sCT = Gs' →
      ∃ s' n, Ev main (UR.urProg sR sN sCN sCT) ⟨g, X⟩ s' n ∧
        n ≤ 32 * (bs.length + ofBits bs + 1) ∧
        s'.stk sR = Shift.gmk sR :: Gs ∧
        s'.stk sN = (Glyph.pos :: (bs.map Glyph.bit ++ [Glyph.iend])) ++ Gt ∧
        s'.stk sCN = Unary (ofBits bs) Gc ∧ s'.stk sCT = Gs' ∧
        (∀ k, k ≠ sR → k ≠ sN → k ≠ sCN → k ≠ sCT → s'.stk k = X k) := by
    intro g X bs Gs Gt Gc Gs' ha ht hc htr
    exact urRebuildK32 main sR sN sCN sCT (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) g X bs Gs Gt Gc Gs' ha ht hc htr
  have hrebuildB : ∀ (g : Reg → Glyph) (X : Stk → List Glyph) (bs : List Bool)
      (Gs Gt Gc Gs' : List Glyph),
      X sR = (Glyph.iend :: (bs.reverse.map Glyph.bit ++ [Glyph.pos])) ++ Shift.gmk sR :: Gs →
      X sB = Gt → X sCB = Gc → X sCT = Gs' →
      ∃ s' n, Ev main (UR.urProg sR sB sCB sCT) ⟨g, X⟩ s' n ∧
        n ≤ 32 * (bs.length + ofBits bs + 1) ∧
        s'.stk sR = Shift.gmk sR :: Gs ∧
        s'.stk sB = (Glyph.pos :: (bs.map Glyph.bit ++ [Glyph.iend])) ++ Gt ∧
        s'.stk sCB = Unary (ofBits bs) Gc ∧ s'.stk sCT = Gs' ∧
        (∀ k, k ≠ sR → k ≠ sB → k ≠ sCB → k ≠ sCT → s'.stk k = X k) := by
    intro g X bs Gs Gt Gc Gs' ha ht hc htr
    exact urRebuildK32 main sR sB sCB sCT (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) g X bs Gs Gt Gc Gs' ha ht hc htr
  -- ### the pre-phase
  obtain ⟨s1, n1, hev1, hn1, h10, h1X, h1B, h1N, h1R, h1S, h1CW, h1CB, h1CT, h1CN, h1Z, h1oth⟩ :=
    preSetupPhaseV2 main (UR.urProg sR sN sCN sCT) 32 hrebuildN x b N X₀ s.reg
  rw [hstate] at hev1
  -- ### the branch test `peek sCN rC_ch`
  set sP : State := ⟨Function.update s1.reg rC_ch ((s1.stk sCN).headD Glyph.eos), s1.stk⟩ with hsPdef
  have hevP : Ev main (.peek sCN rC_ch) s1 sP 1 := by
    rw [hsPdef]; exact ev_peek' main sCN rC_ch s1.reg s1.stk
  have hsPstk : sP.stk = s1.stk := by rw [hsPdef]
  have hsPreg : sP.reg rC_ch = (s1.stk sCN).headD Glyph.eos := by
    rw [hsPdef]
    show Function.update s1.reg rC_ch ((s1.stk sCN).headD Glyph.eos) rC_ch = (s1.stk sCN).headD Glyph.eos
    exact Function.update_self ..
  have hhead : (s1.stk sCN).headD Glyph.eos = if N = 0 then gEnd else gTok := by
    rw [h1CN]
    exact headD_replicate_cons N gEnd Glyph.eos (Shift.gmk sCN :: X₀ sCN)
  -- the pre-phase output, read on `sP.stk`
  have q0 : sP.stk 0 = X₀ 0 := by rw [hsPstk]; exact h10
  have qX : sP.stk sX = Val.enc (.int (x : ℤ)) ++ Shift.gmk sX :: X₀ sX := by
    rw [hsPstk]; exact h1X
  have qB : sP.stk sB = Val.enc (.int (b : ℤ)) ++ Shift.gmk sB :: X₀ sB := by
    rw [hsPstk]; exact h1B
  have qN : sP.stk sN = Val.enc (.int (N : ℤ)) ++ Shift.gmk sN :: X₀ sN := by
    rw [hsPstk]; exact h1N
  have qR : sP.stk sR = Shift.gmk sR :: X₀ sR := by rw [hsPstk]; exact h1R
  have qS : sP.stk sS = Shift.gmk sS :: X₀ sS := by rw [hsPstk]; exact h1S
  have qW : sP.stk sCW = gEnd :: Shift.gmk sCW :: X₀ sCW := by rw [hsPstk]; exact h1CW
  have qCB : sP.stk sCB = Shift.gmk sCB :: X₀ sCB := by rw [hsPstk]; exact h1CB
  have qCT : sP.stk sCT = Shift.gmk sCT :: X₀ sCT := by rw [hsPstk]; exact h1CT
  have qCN : sP.stk sCN = Unary N (Shift.gmk sCN :: X₀ sCN) := by rw [hsPstk]; exact h1CN
  have qZ : sP.stk sZ = Shift.gmk sZ :: X₀ sZ := by rw [hsPstk]; exact h1Z
  have qoth : ∀ j : Stk, j ≠ 0 → j ≠ sX → j ≠ sB → j ≠ sN → j ≠ sR → j ≠ sS →
      j ≠ sCW → j ≠ sCB → j ≠ sCT → j ≠ sCN → j ≠ sZ → sP.stk j = X₀ j := by
    intro j h1 h2 h3 h4 h5 h6 h7 h8 h9 h10' h11
    rw [hsPstk]; exact h1oth j h1 h2 h3 h4 h5 h6 h7 h8 h9 h10' h11
  have hSafeNil : ∀ (l : Glyph), (∀ h ∈ ([] : List Glyph), h ≠ l) :=
    fun l h hh => (mem_nil_false hh).elim
  by_cases hN0 : N = 0
  · -- ################### N = 0 ###################
    subst hN0
    have hrCg : sP.reg rC_ch = gEnd := by rw [hsPreg, hhead]; simp
    have hevITE : Ev main (.ite rC_ch gEnd (.skip)
        (preMainProg (UR.urProg sR sB sCB sCT) (loopProg copyProg))) sP sP 2 :=
      Ev.iteT hrCg (ev_skip main sP)
    have hSafeS0 : ∀ h ∈ ([] : List Glyph) ++ [Glyph.nil], h ≠ Shift.gmk sS := by
      intro h hh
      rw [List.nil_append, List.mem_singleton] at hh
      subst hh
      exact (Shift.gmk_ne_nil sS).symm
    have hSafeX0 : ∀ h ∈ Val.enc (.int (x : ℤ)), h ≠ Shift.gmk sX :=
      fun h hh => noMark_int_mem (x : ℤ) hh sX
    have hSafeB0 : ∀ h ∈ Val.enc (.int (b : ℤ)), h ≠ Shift.gmk sB :=
      fun h hh => noMark_int_mem (b : ℤ) hh sB
    have hSafeN0 : ∀ h ∈ Val.enc (.int (0 : ℤ)), h ≠ Shift.gmk sN :=
      fun h hh => noMark_int_mem (0 : ℤ) hh sN
    have hSafeW0 : ∀ h ∈ [gEnd], h ≠ Shift.gmk sCW := by
      intro h hh; rw [List.mem_singleton] at hh; subst hh; exact end_ne_gmk (by decide)
    have hSafeN20 : ∀ h ∈ [gEnd], h ≠ Shift.gmk sCN := by
      intro h hh; rw [List.mem_singleton] at hh; subst hh; exact end_ne_gmk (by decide)
    obtain ⟨s4, n3, hev3, hn3, hstk4, hoth4⟩ :=
      postPhaseV3 main X₀ [] (Val.enc (.int (x : ℤ))) (Val.enc (.int (b : ℤ)))
        (Val.enc (.int (0 : ℤ))) [] [gEnd] [] [] [gEnd] [] sP.reg sP.stk
        q0 qS qX qB qN qR qW qCB qCT qCN qZ qoth
        hSafeS0 hSafeX0 hSafeB0 hSafeN0
        (hSafeNil (Shift.gmk sR)) hSafeW0 (hSafeNil (Shift.gmk sCB)) (hSafeNil (Shift.gmk sCT))
        hSafeN20 (hSafeNil (Shift.gmk sZ))
    have hlenX : (Val.enc (.int (x : ℤ))).length = isz (x : ℤ) := Work.IntLib.vsz_int _
    have hlenB : (Val.enc (.int (b : ℤ))).length = isz (b : ℤ) := Work.IntLib.vsz_int _
    have hlenN : (Val.enc (.int (0 : ℤ))).length = isz (0 : ℤ) := Work.IntLib.vsz_int _
    have hn3' : n3 ≤ 5 * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ) + 24) := by
      have h := hn3
      simp only [List.length_nil, List.length_singleton, hlenX, hlenB, hlenN] at h
      omega
    -- composition
    have e_post : Ev main postProg sP s4 (n3 + 1) :=
      Ev.seqs_cons (cs := []) hev3 (Ev.seqs_nil (main := main) (s := s4))
    have e_ite : Ev main (seqs [.ite rC_ch gEnd (.skip)
        (preMainProg (UR.urProg sR sB sCB sCT) (loopProg copyProg)), postProg]) sP s4
        (2 + (n3 + 1)) := Ev.seqs_cons hevITE e_post
    have e_peek : Ev main (seqs [.peek sCN rC_ch, .ite rC_ch gEnd (.skip)
        (preMainProg (UR.urProg sR sB sCB sCT) (loopProg copyProg)), postProg]) s1 s4
        (1 + (2 + (n3 + 1))) := Ev.seqs_cons hevP e_ite
    have e_all : Ev main (chunkProg copyProg (UR.urProg sR sN sCN sCT)
        (UR.urProg sR sB sCB sCT)) s s4 (n1 + (1 + (2 + (n3 + 1)))) := by
      show Ev main (seqs [preSetupProg (UR.urProg sR sN sCN sCT), .peek sCN rC_ch,
        .ite rC_ch gEnd (.skip) (preMainProg (UR.urProg sR sB sCB sCT) (loopProg copyProg)),
        postProg]) s s4 (n1 + (1 + (2 + (n3 + 1))))
      exact Ev.seqs_cons hev1 e_peek
    obtain ⟨n, heval, hn⟩ := e_all
    refine ⟨HvdH.intList (HvdH.chunks x b 0) :: rest, s4, n, ⟨rest, rfl, rfl⟩, heval, ?_, ?_, ?_⟩
    · -- cost
      have hzero : (0 : ℕ) * (b + 1) = 0 := Nat.zero_mul _
      rw [hzero] at hn1 ⊢
      have h1b : n1 ≤ 264 * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ) + 1) := by
        have h := hn1; simp only [Nat.add_zero] at h; exact h
      have htot : n ≤ n1 + n3 + 12 := by omega
      have hmul : 4000 * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ))
          ≤ (4 * (KC + 1000)) * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ)) :=
        Nat.mul_le_mul_right _ (by omega)
      have hlin : 269 * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ)) + 396
          ≤ 4000 * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ)) := by
        have hpos : 0 < isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ) := by
          have h1 := two_le_iszEv (x : ℤ); have h2 := two_le_iszEv (b : ℤ)
          have h3 := two_le_iszEv (0 : ℤ); omega
        have h396 : 396 ≤ 396 * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ)) := by
          calc (396 : ℕ) = 396 * 1 := by ring
            _ ≤ 396 * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ)) :=
                Nat.mul_le_mul_left 396 (by omega)
        omega
      show n ≤ (4 * (KC + 1000)) * (isz (x : ℤ) + 0 + isz (b : ℤ) + isz (0 : ℤ))
      calc n ≤ 269 * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ)) + 396 := by omega
        _ ≤ 4000 * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ)) := hlin
        _ ≤ (4 * (KC + 1000)) * (isz (x : ℤ) + isz (b : ℤ) + isz (0 : ℤ)) := hmul
    · -- stack 0
      rw [hstk4, hX₀0]
      show ([Glyph.nil] : List Glyph) ++ (encs rest ++ R) =
        encs (intList (chunks x b 0) :: rest) ++ R
      have hc : chunks x b 0 = ([] : List ℕ) := rfl
      have hi : intList ([] : List ℕ) = Val.nil := rfl
      rw [hc, hi, encs_nil_cons]
      simp only [List.append_assoc]
    · -- frame
      intro k hk
      rw [hoth4 k hk, hX₀ne k hk]
  · -- ################### N ≠ 0 ###################
    have hN1 : 1 ≤ N := by omega
    have hpos : 0 < b * N := Nat.mul_pos (by omega) (by omega)
    have hrCne : sP.reg rC_ch ≠ gEnd := by
      rw [hsPreg, hhead, if_neg hN0]
      exact gTok_ne_gEnd
    have hloop : ∀ (Y : Stk → List Glyph) (g : Reg → Glyph) (Ca : List Glyph),
        Y sCB = Unary b Ca → (∀ r : Reg, r ≠ rG → g r = Glyph.eos) →
        Ev main (loopProg copyProg) (⟨g, lStk x b N Y 0⟩ : State) (lSt x b N Y (b * N))
          (1 + (lsum b KC (b * N) + 1)) := by
      intro Y g Ca hCB hg
      refine loop_ev main copyProg KC Ca ?_ x b N hb hxN hpos Y hCB g hg
      intro x' b' N' hb' hxN' Y' hCB' k hk
      exact loopBodyStep main copyProg KC (hcopySC main) x' b' N' hb' hxN' Ca Y' hCB' k hk
    obtain ⟨s3, n2, hev2, hn2, hs3⟩ :=
      preMainPhaseV2 main (UR.urProg sR sB sCB sCT) (loopProg copyProg) 32
        (fun b N => 1 + (lsum b KC (b * N) + 1)) x b N hb hN1 hxN hrebuildB hloop X₀ sP.reg sP.stk
        q0 qX qB qN qR qS qW qCB qCT qCN qZ qoth
    subst hs3
    have hw0 : wcnt b (b * N) = 0 := wcnt_eq_of_eq (Nat.mul_mod_right b N)
    have hCN0 : N - (b * N) / b = 0 := by
      rw [Nat.mul_div_right N (by omega)]; omega
    set Sval : List Glyph := (outOrder (pbits x b N) b (b * N)).reverse with hSvaldef
    set Gx : List Glyph := (streamOf x).drop (cg x (b * N)) with hGxdef
    set Rq : List Glyph := ((streamOf x).take (cg x (b * N))).reverse ++ [Glyph.pos] with hRqdef
    set Rr : List Glyph := List.replicate b gTok ++ [gEnd] with hRrdef
    have hYSval : lStk x b N (Yinit b N X₀) (b * N) sS = Sval ++ Shift.gmk sS :: X₀ sS := by
      rw [lStk_init_sS, hSvaldef]
    have hYGx : lStk x b N (Yinit b N X₀) (b * N) sX = Gx ++ Shift.gmk sX :: X₀ sX := by
      rw [lStk_init_sX, hGxdef]
    have hYRq : lStk x b N (Yinit b N X₀) (b * N) sR = Rq ++ Shift.gmk sR :: X₀ sR := by
      rw [lStk_init_sR, hRqdef]
    have hYRr : lStk x b N (Yinit b N X₀) (b * N) sCB = Rr ++ Shift.gmk sCB :: X₀ sCB := by
      rw [lStk_init_sCB, hRrdef]
    have hYw : lStk x b N (Yinit b N X₀) (b * N) sCW = [gEnd] ++ Shift.gmk sCW :: X₀ sCW :=
      lStk_init_sCW x b N X₀ (b * N) hw0
    have hYN : lStk x b N (Yinit b N X₀) (b * N) sCN = [gEnd] ++ Shift.gmk sCN :: X₀ sCN :=
      lStk_init_sCN x b N X₀ (b * N) hCN0
    have hYB : lStk x b N (Yinit b N X₀) (b * N) sB
        = Val.enc (.int (b : ℤ)) ++ Shift.gmk sB :: X₀ sB := lStk_init_sB x b N X₀ (b * N)
    have hYNv : lStk x b N (Yinit b N X₀) (b * N) sN
        = Val.enc (.int (N : ℤ)) ++ Shift.gmk sN :: X₀ sN := lStk_init_sN x b N X₀ (b * N)
    have hYCT : lStk x b N (Yinit b N X₀) (b * N) sCT = [] ++ Shift.gmk sCT :: X₀ sCT := by
      rw [lStk_init_sCT]; rfl
    have hYZ : lStk x b N (Yinit b N X₀) (b * N) sZ = [] ++ Shift.gmk sZ :: X₀ sZ := by
      rw [lStk_init_sZ]; rfl
    have hYoth : ∀ j : Stk, j ≠ 0 → j ≠ sX → j ≠ sB → j ≠ sN → j ≠ sR → j ≠ sS →
        j ≠ sCW → j ≠ sCB → j ≠ sCT → j ≠ sCN → j ≠ sZ →
        lStk x b N (Yinit b N X₀) (b * N) j = X₀ j :=
      fun j _ h2 h3 h4 h5 h6 h7 h8 h9 h10' h11 =>
        lStk_init_other x b N X₀ (b * N) h2 h3 h4 h5 h6 h7 h8 h9 h10' h11
    have hY0 : lStk x b N (Yinit b N X₀) (b * N) 0 = X₀ 0 :=
      lStk_init_other x b N X₀ (b * N) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    -- sizes
    have hlenB0 : (Val.enc (.int (b : ℤ))).length = isz (b : ℤ) := Work.IntLib.vsz_int _
    have hlenN0 : (Val.enc (.int (N : ℤ))).length = isz (N : ℤ) := Work.IntLib.vsz_int _
    have hSvalLen : Sval.length ≤ N * (b + 3) := by
      rw [hSvaldef, List.length_reverse]
      exact outOrderLen x b N hb hxN
    have hGxLen : Gx.length ≤ isz (x : ℤ) := by
      rw [hGxdef, isz_natCast]
      have h1 : ((streamOf x).drop (cg x (b * N))).length ≤ (streamOf x).length :=
        List.Sublist.length_le (List.drop_sublist _ _)
      rw [streamOf_length] at h1
      omega
    have hRqLen : Rq.length ≤ isz (x : ℤ) := by
      rw [hRqdef, isz_natCast, List.length_append, List.length_reverse, List.length_singleton]
      have h1 : ((streamOf x).take (cg x (b * N))).length ≤ (streamOf x).length :=
        List.Sublist.length_le (List.take_sublist _ _)
      rw [streamOf_length] at h1
      omega
    have hRrLen : Rr.length = b + 1 := by
      rw [hRrdef, List.length_append, List.length_replicate, List.length_singleton]
    -- safety conditions
    have hSafeS : ∀ h ∈ Sval ++ [Glyph.nil], h ≠ Shift.gmk sS := by
      intro h hh
      rw [hSvaldef, List.mem_append] at hh
      rcases hh with hh | hh
      · rw [List.mem_reverse] at hh
        have h2 : h ∈ Val.enc (intList (chunks x b N)) := by
          rw [← outOrderFull x b N hb]
          exact List.mem_append.mpr (Or.inl hh)
        exact noMark_enc_mem _ h2 sS
      · rw [List.mem_singleton] at hh
        subst hh
        exact fun hc => Shift.gmk_ne_nil sS hc.symm
    have hSafeX : ∀ h ∈ Gx, h ≠ Shift.gmk sX := by
      intro h hh
      rw [hGxdef] at hh
      have hh' : h ∈ streamOf x := (List.drop_sublist _ _).subset hh
      simp only [streamOf, List.mem_append, List.mem_map, List.mem_singleton] at hh'
      rcases hh' with ⟨c, -, rfl⟩ | rfl <;> (intro hc; cases hc)
    have hSafeB : ∀ h ∈ Val.enc (.int (b : ℤ)), h ≠ Shift.gmk sB :=
      fun h hh => noMark_int_mem (b : ℤ) hh sB
    have hSafeN : ∀ h ∈ Val.enc (.int (N : ℤ)), h ≠ Shift.gmk sN :=
      fun h hh => noMark_int_mem (N : ℤ) hh sN
    have hSafeR : ∀ h ∈ Rq, h ≠ Shift.gmk sR := by
      intro h hh
      rw [hRqdef, List.mem_append] at hh
      rcases hh with hh | hh
      · rw [List.mem_reverse] at hh
        have hh' : h ∈ streamOf x := (List.take_sublist _ _).subset hh
        simp only [streamOf, List.mem_append, List.mem_map, List.mem_singleton] at hh'
        rcases hh' with ⟨c, -, rfl⟩ | rfl <;> (intro hc; cases hc)
      · rw [List.mem_singleton] at hh
        subst hh
        intro hc; cases hc
    have hSafeW : ∀ h ∈ [gEnd], h ≠ Shift.gmk sCW := by
      intro h hh; rw [List.mem_singleton] at hh; subst hh; exact end_ne_gmk (by decide)
    have hSafeCB : ∀ h ∈ Rr, h ≠ Shift.gmk sCB := by
      intro h hh
      rw [hRrdef, List.mem_append] at hh
      rcases hh with hh | hh
      · rw [List.mem_replicate] at hh
        obtain ⟨-, rfl⟩ := hh
        intro hc; cases hc
      · rw [List.mem_singleton] at hh
        subst hh
        intro hc; cases hc
    have hSafeCT : ∀ h ∈ ([] : List Glyph), h ≠ Shift.gmk sCT :=
      fun h hh => (mem_nil_false hh).elim
    have hSafeCN : ∀ h ∈ [gEnd], h ≠ Shift.gmk sCN := by
      intro h hh; rw [List.mem_singleton] at hh; subst hh; exact end_ne_gmk (by decide)
    have hSafeZ : ∀ h ∈ ([] : List Glyph), h ≠ Shift.gmk sZ :=
      fun h hh => (mem_nil_false hh).elim
    -- the post-phase
    obtain ⟨s4, n3, hev3, hn3, hstk4, hoth4⟩ :=
      postPhaseV3 main X₀ Sval Gx (Val.enc (.int (b : ℤ))) (Val.enc (.int (N : ℤ))) Rq [gEnd] Rr []
        [gEnd] [] (lSt x b N (Yinit b N X₀) (b * N)).reg
        (lStk x b N (Yinit b N X₀) (b * N))
        hY0 hYSval hYGx hYB hYNv hYRq hYw hYRr hYCT hYN hYZ hYoth
        hSafeS hSafeX hSafeB hSafeN hSafeR hSafeW hSafeCB hSafeCT hSafeCN hSafeZ
    -- composition
    have e_post : Ev main postProg (lSt x b N (Yinit b N X₀) (b * N)) s4 (n3 + 1) :=
      Ev.seqs_cons (cs := []) hev3 (Ev.seqs_nil (main := main) (s := s4))
    have e_ite : Ev main (seqs [.ite rC_ch gEnd (.skip)
        (preMainProg (UR.urProg sR sB sCB sCT) (loopProg copyProg)), postProg]) sP s4
        ((n2 + 1) + (n3 + 1)) :=
      Ev.seqs_cons (Ev.iteF hrCne hev2) e_post
    have e_peek : Ev main (seqs [.peek sCN rC_ch, .ite rC_ch gEnd (.skip)
        (preMainProg (UR.urProg sR sB sCB sCT) (loopProg copyProg)), postProg]) s1 s4
        (1 + ((n2 + 1) + (n3 + 1))) :=
      Ev.seqs_cons hevP e_ite
    have e_all : Ev main (chunkProg copyProg (UR.urProg sR sN sCN sCT)
        (UR.urProg sR sB sCB sCT)) s s4 (n1 + (1 + ((n2 + 1) + (n3 + 1)))) := by
      show Ev main (seqs [preSetupProg (UR.urProg sR sN sCN sCT), .peek sCN rC_ch,
        .ite rC_ch gEnd (.skip) (preMainProg (UR.urProg sR sB sCB sCT) (loopProg copyProg)),
        postProg]) s s4 (n1 + (1 + ((n2 + 1) + (n3 + 1))))
      exact Ev.seqs_cons hev1 e_peek
    obtain ⟨n, heval, hn⟩ := e_all
    refine ⟨HvdH.intList (HvdH.chunks x b N) :: rest, s4, n, ⟨rest, rfl, rfl⟩, heval, ?_, ?_, ?_⟩
    · -- cost
      have hn1' : n1 ≤ 264 * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1) := hn1
      have hn2' : n2 ≤ 164 * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1)
          + (lsum b KC (b * N) + 2) := by
        have hA : (1 : ℕ) + (lsum b KC (b * N) + 1) = lsum b KC (b * N) + 2 := by omega
        have hB : (2 * 32 + 100) * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1)
            = 164 * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1) := by
          norm_num
        rw [hA, hB] at hn2
        exact hn2
      have hcl : lsum b KC (b * N) + 2 ≤ (KC + 134) * (N * (b + 1)) + 2 :=
        Nat.add_le_add_right (lsumBound b N KC hb) 2
      have hn3' : n3 ≤ 5 * (N * (b + 3) + isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ)
          + isz (x : ℤ) + 1 + (b + 1) + 0 + 1 + 0 + 22) := by
        have h := hn3
        simp only [List.length_nil, List.length_singleton] at h
        omega
      have htot : n ≤ n1 + n2 + n3 + 12 := by omega
      exact chunkCostN x b N KC hb hN1 n n1 n2 n3 (lsum b KC (b * N) + 2)
        hn1' hn2' hcl hn3' htot
    · -- stack 0
      rw [hstk4, hSvaldef, List.reverse_reverse, hX₀0, encs_cons', outOrderFull x b N hb]
      simp only [List.append_assoc]
    · -- frame
      intro k hk
      rw [hoth4 k hk, hX₀ne k hk]

end Work.IntLib
