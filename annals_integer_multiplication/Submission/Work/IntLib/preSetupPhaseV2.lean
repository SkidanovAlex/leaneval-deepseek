import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Move
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.Layout.mvVal_ev_full

/-!
# IntLib: the pre-setup phase of the `chunk` word

`preSetupProg rebuildN` pushes the frame markers of the ten stacks it uses, sets up the `gEnd`
sentinel on `sCW`, moves the three input values `x`, `b`, `N` off the value stack onto `sX`, `sB`
and `sN`, and then rebuilds the unary counter of `N` on `sCN` (via the auxiliary `rebuildN`).

This file proves the cost and correctness of that phase; `preSetupPhaseV2` is the `Ev`-level
statement used by `chunkProg`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## Basic `Ev` facts for the pieces -/

/-- `mkStep k r` pushes the frame marker of stack `k`. -/
theorem mkStep_ev (main : Cmd) (k : Stk) (r : Reg) (g : Reg → Glyph) (X : Stk → List Glyph) :
    Ev main (mkStep k r) ⟨g, X⟩
      ⟨Function.update g r (Shift.gmk k), Function.update X k (Shift.gmk k :: X k)⟩ 2 := by
  have h1 : Ev main (.set r (Shift.gmk k)) ⟨g, X⟩ ⟨Function.update g r (Shift.gmk k), X⟩ 1 :=
    ev_set' main r (Shift.gmk k) g X
  have h2 : Ev main (.push k r) ⟨Function.update g r (Shift.gmk k), X⟩
      ⟨Function.update g r (Shift.gmk k), Function.update X k (Shift.gmk k :: X k)⟩ 1 := by
    simpa using ev_push' main k r (Function.update g r (Shift.gmk k)) X
  rw [mkStep]
  exact Ev.seq' h1 h2 (by norm_num)

/-- `.set r c` followed by `.push k r` pushes `c` on stack `k`. -/
theorem setPush_ev (main : Cmd) (r : Reg) (c : Glyph) (k : Stk) (g : Reg → Glyph)
    (X : Stk → List Glyph) :
    ∃ g', Ev main (seqs [Cmd.set r c, .push k r]) ⟨g, X⟩
      ⟨g', Function.update X k (c :: X k)⟩ 2 := by
  have h1 : Ev main (.set r c) ⟨g, X⟩ ⟨Function.update g r c, X⟩ 1 := ev_set' main r c g X
  have h2 : Ev main (.push k r) ⟨Function.update g r c, X⟩
      ⟨Function.update g r c, Function.update X k (c :: X k)⟩ 1 := by
    simpa using ev_push' main k r (Function.update g r c) X
  refine ⟨Function.update g r c, ?_⟩
  exact Ev.seq' h1 h2 (by norm_num)

/-! ## Pushing the markers of a list of stacks -/

/-- Push the frame marker of every stack of `L` onto that stack, in order. -/
def markAll : List Stk → (Stk → List Glyph) → Stk → List Glyph
  | [], X => X
  | k :: L, X => markAll L (Function.update X k (Shift.gmk k :: X k))

theorem markAll_notMem : ∀ (L : List Stk) (X : Stk → List Glyph) (j : Stk),
    j ∉ L → markAll L X j = X j := by
  intro L
  induction L with
  | nil => intro X j _; rfl
  | cons k L ih =>
      intro X j hj
      show markAll L (Function.update X k (Shift.gmk k :: X k)) j = X j
      rw [ih (Function.update X k (Shift.gmk k :: X k)) j (fun h => hj (List.mem_cons_of_mem k h))]
      exact Function.update_of_ne (fun h : j = k => hj (by rw [← h]; exact List.mem_cons_self ..)) _ _

theorem markAll_mem : ∀ (L : List Stk) (X : Stk → List Glyph) (j : Stk), L.Nodup → j ∈ L →
    markAll L X j = Shift.gmk j :: X j := by
  intro L
  induction L with
  | nil => intro X j _ hj; exact (List.not_mem_nil hj).elim
  | cons k L ih =>
      intro X j hnd hj
      rcases List.mem_cons.mp hj with hjk | hj'
      · rw [hjk]
        show markAll L (Function.update X k (Shift.gmk k :: X k)) k = Shift.gmk k :: X k
        rw [markAll_notMem L (Function.update X k (Shift.gmk k :: X k)) k (List.nodup_cons.mp hnd).1,
          Function.update_self]
      · show markAll L (Function.update X k (Shift.gmk k :: X k)) j = _
        rw [ih (Function.update X k (Shift.gmk k :: X k)) j (List.nodup_cons.mp hnd).2 hj']
        congr 1
        exact Function.update_of_ne
          (fun h : j = k => (List.nodup_cons.mp hnd).1 (by rw [← h]; exact hj')) _ _

/-- Pushing the markers of all the stacks of `L`. -/
theorem keys_ev (main : Cmd) (r : Reg) (L : List Stk) (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ (g' : Reg → Glyph), Ev main (seqs (L.map (fun k => mkStep k r))) ⟨g, X⟩ ⟨g', markAll L X⟩
      (2 * L.length + 1) := by
  induction L generalizing g X with
  | nil => exact ⟨g, ev_skip main (⟨g, X⟩ : State)⟩
  | cons k L ih =>
      have h1 := mkStep_ev main k r g X
      obtain ⟨g', h2⟩ := ih (Function.update g r (Shift.gmk k))
        (Function.update X k (Shift.gmk k :: X k))
      refine ⟨g', ?_⟩
      refine (Ev.seqs_cons (C₁ := 2) (C₂ := 2 * L.length + 1)
        (cs := L.map (fun k => mkStep k r)) h1 h2).mono ?_
      simp only [List.length_cons]; omega

/-! ## Composition of `seqs` -/

theorem ev_seqs_append {main : Cmd} : ∀ (l₁ l₂ : List Cmd) (s t u : State) (C₁ C₂ : ℕ),
    Ev main (seqs l₁) s t C₁ → Ev main (seqs l₂) t u C₂ → Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ s t u C₁ C₂ h₁ h₂
      obtain ⟨n, he, -⟩ := h₁
      cases he
      exact h₂.mono (by omega)
  | cons c cs ih =>
      intro l₂ s t u C₁ C₂ h₁ h₂
      cases cs with
      | nil =>
        cases l₂ with
        | nil =>
          obtain ⟨n, he, -⟩ := h₂
          cases he
          exact h₁.mono (by omega)
        | cons d ds => exact Ev.seq h₁ h₂
      | cons d ds =>
        obtain ⟨n₁, e₁, hl₁⟩ := h₁
        rw [show seqs (c :: d :: ds) = .seq c (seqs (d :: ds)) from rfl] at e₁
        cases e₁ with
        | seq e e' =>
          have hrec : Ev main (seqs ((d :: ds) ++ l₂)) _ u (_ + C₂) :=
            ih l₂ _ _ u _ C₂ ⟨_, e', le_rfl⟩ h₂
          exact (Ev.seq ⟨_, e, le_rfl⟩ hrec).mono (by omega)

theorem ev_seqs_append' {main : Cmd} {l₁ l₂ : List Cmd} {s t u : State} {C₁ C₂ : ℕ}
    (h₁ : Ev main (seqs l₁) s t C₁) (h₂ : Ev main (seqs l₂) t u C₂) :
    Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) :=
  ev_seqs_append l₁ l₂ s t u C₁ C₂ h₁ h₂

/-! ## Frames -/

/-- `Y` agrees with `X` on every stack outside the list `L`. -/
def Fr (L : List Stk) (X Y : Stk → List Glyph) : Prop := ∀ j, j ∉ L → Y j = X j

theorem Fr.refl (L : List Stk) (X : Stk → List Glyph) : Fr L X X := fun _ _ => rfl

theorem Fr.trans {L M : List Stk} {X Y Z : Stk → List Glyph} (h1 : Fr L X Y) (h2 : Fr M Y Z) :
    Fr (L ++ M) X Z := by
  intro j hj
  rw [h2 j (fun h => hj (List.mem_append_right L h)), h1 j (fun h => hj (List.mem_append_left M h))]

/-- The frame of a `mvVal` (which restores its two scratch stacks). -/
theorem Fr.pair {X Y : Stk → List Glyph} {a b c d : Stk}
    (h : ∀ j, j ≠ a → j ≠ b → j ≠ c → j ≠ d → Y j = X j) (hc : Y c = X c) (hd : Y d = X d) :
    Fr [a, b] X Y := by
  intro j hj
  have hja : j ≠ a := fun hh => hj (by simp [hh])
  have hjb : j ≠ b := fun hh => hj (by simp [hh])
  by_cases h1 : j = c
  · rw [h1]; exact hc
  by_cases h2 : j = d
  · rw [h2]; exact hd
  · exact h j hja hjb h1 h2

/-! ## Encoding lemmas -/

/-- The encoding of `int N` (for `N : ℕ`) is `pos :: bits ++ [iend]`. -/
theorem enc_int_eq_ps (N : ℕ) :
    Val.enc (Val.int (N : ℤ)) = Glyph.pos :: (N.bits.map Glyph.bit ++ [Glyph.iend]) := by
  rw [Work.IntLib.enc_int]
  have hsign : (if (N : ℤ) < 0 then Glyph.neg else Glyph.pos) = Glyph.pos := by
    have h : ¬ ((N : ℤ) < 0) := by omega
    simp only [h, ↓reduceIte]
  rw [hsign, Int.natAbs_natCast, Work.IntLib.encodeNat_eq_bits]

/-- The reversed encoding of `int N`. -/
theorem enc_int_rev_ps (N : ℕ) :
    (Val.enc (Val.int (N : ℤ))).reverse =
      Glyph.iend :: (N.bits.reverse.map Glyph.bit ++ [Glyph.pos]) := by
  rw [enc_int_eq_ps]
  rw [List.reverse_cons, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
  rw [← List.map_reverse]
  rfl

/-- `vsz` of an integer value is `isz`. -/
theorem vsz_int_eq (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

/-! ## The pre-setup phase -/

theorem preSetupPhaseV2 (main : HvdH.Cmd) (rebuildN : HvdH.Cmd) (KR : ℕ)
    (hrebuildN : ∀ (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (bs : List Bool)
      (Gs Gt Gc Gs' : List HvdH.Glyph),
      X Work.IntLib.sR = (HvdH.Glyph.iend :: (bs.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos])) ++ Work.IntLib.Shift.gmk Work.IntLib.sR :: Gs →
      X Work.IntLib.sN = Gt → X Work.IntLib.sCN = Gc → X Work.IntLib.sCT = Gs' →
      ∃ s' n, Work.Layout.Ev main rebuildN ⟨g, X⟩ s' n ∧ n ≤ KR * (bs.length + Work.IntLib.ofBits bs + 1) ∧
        s'.stk Work.IntLib.sR = Work.IntLib.Shift.gmk Work.IntLib.sR :: Gs ∧
        s'.stk Work.IntLib.sN = (HvdH.Glyph.pos :: (bs.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend])) ++ Gt ∧
        s'.stk Work.IntLib.sCN = Work.IntLib.Unary (Work.IntLib.ofBits bs) Gc ∧ s'.stk Work.IntLib.sCT = Gs' ∧
        (∀ k, k ≠ Work.IntLib.sR → k ≠ Work.IntLib.sN → k ≠ Work.IntLib.sCN → k ≠ Work.IntLib.sCT → s'.stk k = X k))
    (x b N : ℕ) (X₀ : HvdH.Stk → List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) :
    ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main (Work.IntLib.preSetupProg rebuildN) ⟨g, Work.IntLib.Xinit x b N X₀⟩ s' n ∧
      n ≤ (2 * KR + 200) * (HvdH.isz x + HvdH.isz b + HvdH.isz N + N * (b + 1) + 1) ∧
      s'.stk 0 = X₀ 0 ∧
      s'.stk Work.IntLib.sX = HvdH.Val.enc (HvdH.Val.int (x : ℤ)) ++ Work.IntLib.Shift.gmk Work.IntLib.sX :: X₀ Work.IntLib.sX ∧
      s'.stk Work.IntLib.sB = HvdH.Val.enc (HvdH.Val.int (b : ℤ)) ++ Work.IntLib.Shift.gmk Work.IntLib.sB :: X₀ Work.IntLib.sB ∧
      s'.stk Work.IntLib.sN = HvdH.Val.enc (HvdH.Val.int (N : ℤ)) ++ Work.IntLib.Shift.gmk Work.IntLib.sN :: X₀ Work.IntLib.sN ∧
      s'.stk Work.IntLib.sR = Work.IntLib.Shift.gmk Work.IntLib.sR :: X₀ Work.IntLib.sR ∧
      s'.stk Work.IntLib.sS = Work.IntLib.Shift.gmk Work.IntLib.sS :: X₀ Work.IntLib.sS ∧
      s'.stk Work.IntLib.sCW = Work.IntLib.gEnd :: Work.IntLib.Shift.gmk Work.IntLib.sCW :: X₀ Work.IntLib.sCW ∧
      s'.stk Work.IntLib.sCB = Work.IntLib.Shift.gmk Work.IntLib.sCB :: X₀ Work.IntLib.sCB ∧
      s'.stk Work.IntLib.sCT = Work.IntLib.Shift.gmk Work.IntLib.sCT :: X₀ Work.IntLib.sCT ∧
      s'.stk Work.IntLib.sCN = Work.IntLib.Unary N (Work.IntLib.Shift.gmk Work.IntLib.sCN :: X₀ Work.IntLib.sCN) ∧
      s'.stk Work.IntLib.sZ = Work.IntLib.Shift.gmk Work.IntLib.sZ :: X₀ Work.IntLib.sZ ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.sX → j ≠ Work.IntLib.sB → j ≠ Work.IntLib.sN → j ≠ Work.IntLib.sR →
        j ≠ Work.IntLib.sS → j ≠ Work.IntLib.sCW → j ≠ Work.IntLib.sCB → j ≠ Work.IntLib.sCT → j ≠ Work.IntLib.sCN →
        j ≠ Work.IntLib.sZ → s'.stk j = X₀ j) := by
  -- the initial stack function
  let E : Stk → List Glyph := Xinit x b N X₀
  have hE0 : E 0 = Val.enc (Val.int (x : ℤ)) ++
      (Val.enc (Val.int (b : ℤ)) ++ (Val.enc (Val.int (N : ℤ)) ++ X₀ 0)) := by
    show Xinit x b N X₀ 0 = _
    simp [Xinit, List.append_assoc]
  have hEj : ∀ j : Stk, j ≠ 0 → E j = X₀ j := by
    intro j hj
    show Xinit x b N X₀ j = X₀ j
    simp [Xinit, hj]
  -- (1) the ten frame markers
  obtain ⟨g1, he1⟩ := keys_ev main rH [sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] g E
  let X1 : Stk → List Glyph := markAll [sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] E
  have hLnd : ([sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] : List Stk).Nodup := by decide
  have h1val : ∀ k : Stk, k ∈ ([sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] : List Stk) →
      X1 k = Shift.gmk k :: E k := fun k hk => markAll_mem _ E k hLnd hk
  have h1fr : ∀ j : Stk, j ∉ ([sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] : List Stk) →
      X1 j = E j := fun j hj => markAll_notMem _ E j hj
  -- (2) the `gEnd` sentinel on `sCW`
  obtain ⟨g2, he2⟩ := setPush_ev main rH gEnd sCW g1 X1
  let X2 : Stk → List Glyph := Function.update X1 sCW (gEnd :: X1 sCW)
  have h2sCW : X2 sCW = gEnd :: X1 sCW := by
    show Function.update X1 sCW (gEnd :: X1 sCW) sCW = _
    rw [Function.update_self]
  have h2fr : ∀ j : Stk, j ≠ sCW → X2 j = X1 j := by
    intro j hj
    show Function.update X1 sCW (gEnd :: X1 sCW) j = X1 j
    exact Function.update_of_ne hj _ _
  -- (3) move `x`
  have h3a : X2 0 = Val.enc (Val.int (x : ℤ)) ++
      (Val.enc (Val.int (b : ℤ)) ++ (Val.enc (Val.int (N : ℤ)) ++ X₀ 0)) := by
    rw [h2fr 0 (by decide), h1fr 0 (by decide)]
    exact hE0
  have h3b : X2 sX = X1 sX := h2fr sX (by decide)
  obtain ⟨s3, n3, he3, hn3, h3_0, h3_sX, h3_1, h3_2, h3_oth⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := sX) (c := sT1) (d := sT2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := g2) (X := X2) (v := Val.int (x : ℤ))
      (A := Val.enc (Val.int (b : ℤ)) ++ (Val.enc (Val.int (N : ℤ)) ++ X₀ 0))
      (B := X1 sX) h3a h3b
  -- (4) move `b`
  have h4a : s3.stk 0 = Val.enc (Val.int (b : ℤ)) ++ (Val.enc (Val.int (N : ℤ)) ++ X₀ 0) := h3_0
  have h4b : s3.stk sB = X1 sB := by
    rw [h3_oth sB (by decide) (by decide) (by decide) (by decide), h2fr sB (by decide)]
  obtain ⟨s4, n4, he4, hn4, h4_0, h4_sB, h4_1, h4_2, h4_oth⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := sB) (c := sT1) (d := sT2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s3.reg) (X := s3.stk) (v := Val.int (b : ℤ))
      (A := Val.enc (Val.int (N : ℤ)) ++ X₀ 0) (B := X1 sB) h4a h4b
  -- (5) move `N`
  have h5a : s4.stk 0 = Val.enc (Val.int (N : ℤ)) ++ X₀ 0 := h4_0
  have h5b : s4.stk sN = X1 sN := by
    rw [h4_oth sN (by decide) (by decide) (by decide) (by decide),
        h3_oth sN (by decide) (by decide) (by decide) (by decide), h2fr sN (by decide)]
  obtain ⟨s5, n5, he5, hn5, h5_0, h5_sN, h5_1, h5_2, h5_oth⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := sN) (c := sT1) (d := sT2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s4.reg) (X := s4.stk) (v := Val.int (N : ℤ)) (A := X₀ 0) (B := X1 sN) h5a h5b
  -- (6) drain the encoding of `N` from `sN` to `sR`
  have h6a : s5.stk sN = Val.enc (Val.int (N : ℤ)) ++ Shift.gmk sN :: E sN := by
    rw [h5_sN, h1val sN (by decide)]
  have h6safe : ∀ h ∈ Val.enc (Val.int (N : ℤ)), h ≠ Shift.gmk sN :=
    fun h hh => noMark_enc_int (N : ℤ) h hh sN
  have h6b : s5.stk sR = X1 sR := by
    rw [h5_oth sR (by decide) (by decide) (by decide) (by decide), h4_oth sR (by decide) (by decide) (by decide) (by decide),
        h3_oth sR (by decide) (by decide) (by decide) (by decide), h2fr sR (by decide)]
  obtain ⟨s6, n6, he6, hn6, h6reg, h6_sN, h6_sR, h6_oth⟩ :=
    Shift.drain_ev main sN sR (Shift.gmk sN) rH rK (by decide) (by decide)
      (Val.enc (Val.int (N : ℤ))) (E sN) (X1 sR) s5.reg s5.stk h6safe h6a h6b
  -- (7) rebuild the unary counter of `N`
  have h7a : s6.stk sR =
      (Glyph.iend :: (N.bits.reverse.map Glyph.bit ++ [Glyph.pos])) ++ Shift.gmk sR :: X₀ sR := by
    rw [h6_sR, enc_int_rev_ps N, h1val sR (by decide), hEj sR (by decide)]
  have h7b : s6.stk sN = Shift.gmk sN :: X₀ sN := by
    rw [h6_sN, hEj sN (by decide)]
  have h7c : s6.stk sCN = Shift.gmk sCN :: X₀ sCN := by
    rw [h6_oth sCN (by decide) (by decide), h5_oth sCN (by decide) (by decide) (by decide) (by decide),
        h4_oth sCN (by decide) (by decide) (by decide) (by decide),
        h3_oth sCN (by decide) (by decide) (by decide) (by decide),
        h2fr sCN (by decide), h1val sCN (by decide), hEj sCN (by decide)]
  have h7d : s6.stk sCT = Shift.gmk sCT :: X₀ sCT := by
    rw [h6_oth sCT (by decide) (by decide), h5_oth sCT (by decide) (by decide) (by decide) (by decide),
        h4_oth sCT (by decide) (by decide) (by decide) (by decide),
        h3_oth sCT (by decide) (by decide) (by decide) (by decide),
        h2fr sCT (by decide), h1val sCT (by decide), hEj sCT (by decide)]
  obtain ⟨s7, n7, he7, hn7, h8_sR, h8_sN, h8_sCN, h8_sCT, h8_oth⟩ :=
    hrebuildN s6.reg s6.stk N.bits (X₀ sR) (Shift.gmk sN :: X₀ sN)
      (Shift.gmk sCN :: X₀ sCN) (Shift.gmk sCT :: X₀ sCT) h7a h7b h7c h7d
  -- frames of the setup phase
  have fr1 : Fr ([sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] : List Stk) E X1 :=
    fun j hj => h1fr j hj
  have fr2 : Fr [sCW] X1 X2 := by
    intro j hj
    exact h2fr j (fun h => hj (by rw [h]; exact List.mem_cons_self ..))
  have fr3 : Fr [0, sX] X2 s3.stk := Fr.pair h3_oth h3_1 h3_2
  have fr4 : Fr [0, sB] s3.stk s4.stk := Fr.pair h4_oth h4_1 h4_2
  have fr5 : Fr [0, sN] s4.stk s5.stk := Fr.pair h5_oth h5_1 h5_2
  have fr6 : Fr [sN, sR] s5.stk s6.stk := by
    intro j hj
    have h1 : j ≠ sN := fun h => hj (by rw [h]; exact List.mem_cons_self ..)
    have h2 : j ≠ sR := fun h => hj (by rw [h]; exact List.mem_cons_of_mem sN (List.mem_cons_self ..))
    exact h6_oth j h1 h2
  have frAll : Fr (([sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] : List Stk) ++ [sCW] ++ [(0 : Stk), sX]
      ++ [(0 : Stk), sB] ++ [(0 : Stk), sN] ++ [sN, sR]) E s6.stk :=
    Fr.trans (Fr.trans (Fr.trans (Fr.trans (Fr.trans fr1 fr2) fr3) fr4) fr5) fr6
  -- the final values
  have hv0 : s7.stk 0 = X₀ 0 := by
    rw [h8_oth 0 (by decide) (by decide) (by decide) (by decide),
        h6_oth 0 (by decide) (by decide), h5_0]
  have hvX : s7.stk sX = Val.enc (Val.int (x : ℤ)) ++ Shift.gmk sX :: X₀ sX := by
    rw [h8_oth sX (by decide) (by decide) (by decide) (by decide),
        h6_oth sX (by decide) (by decide), h5_oth sX (by decide) (by decide) (by decide) (by decide),
        h4_oth sX (by decide) (by decide) (by decide) (by decide), h3_sX, h1val sX (by decide), hEj sX (by decide)]
  have hvB : s7.stk sB = Val.enc (Val.int (b : ℤ)) ++ Shift.gmk sB :: X₀ sB := by
    rw [h8_oth sB (by decide) (by decide) (by decide) (by decide),
        h6_oth sB (by decide) (by decide), h5_oth sB (by decide) (by decide) (by decide) (by decide),
        h4_sB, h1val sB (by decide), hEj sB (by decide)]
  have hvN : s7.stk sN = Val.enc (Val.int (N : ℤ)) ++ Shift.gmk sN :: X₀ sN := by
    rw [h8_sN, enc_int_eq_ps N]
  have hvR : s7.stk sR = Shift.gmk sR :: X₀ sR := h8_sR
  have hvS : s7.stk sS = Shift.gmk sS :: X₀ sS := by
    rw [h8_oth sS (by decide) (by decide) (by decide) (by decide),
        h6_oth sS (by decide) (by decide), h5_oth sS (by decide) (by decide) (by decide) (by decide),
        h4_oth sS (by decide) (by decide) (by decide) (by decide),
        h3_oth sS (by decide) (by decide) (by decide) (by decide), h2fr sS (by decide),
        h1val sS (by decide), hEj sS (by decide)]
  have hvCW : s7.stk sCW = Work.IntLib.gEnd :: Shift.gmk sCW :: X₀ sCW := by
    rw [h8_oth sCW (by decide) (by decide) (by decide) (by decide),
        h6_oth sCW (by decide) (by decide), h5_oth sCW (by decide) (by decide) (by decide) (by decide),
        h4_oth sCW (by decide) (by decide) (by decide) (by decide),
        h3_oth sCW (by decide) (by decide) (by decide) (by decide), h2sCW,
        h1val sCW (by decide), hEj sCW (by decide)]
  have hvCB : s7.stk sCB = Shift.gmk sCB :: X₀ sCB := by
    rw [h8_oth sCB (by decide) (by decide) (by decide) (by decide),
        h6_oth sCB (by decide) (by decide), h5_oth sCB (by decide) (by decide) (by decide) (by decide),
        h4_oth sCB (by decide) (by decide) (by decide) (by decide),
        h3_oth sCB (by decide) (by decide) (by decide) (by decide), h2fr sCB (by decide),
        h1val sCB (by decide), hEj sCB (by decide)]
  have hvCT : s7.stk sCT = Shift.gmk sCT :: X₀ sCT := h8_sCT
  have hvCN : s7.stk sCN = Unary N (Shift.gmk sCN :: X₀ sCN) := by
    rw [h8_sCN, Work.IntLib.ofBits_bits N]
  have hvZ : s7.stk sZ = Shift.gmk sZ :: X₀ sZ := by
    rw [h8_oth sZ (by decide) (by decide) (by decide) (by decide),
        h6_oth sZ (by decide) (by decide), h5_oth sZ (by decide) (by decide) (by decide) (by decide),
        h4_oth sZ (by decide) (by decide) (by decide) (by decide),
        h3_oth sZ (by decide) (by decide) (by decide) (by decide), h2fr sZ (by decide),
        h1val sZ (by decide), hEj sZ (by decide)]
  have hvoth : ∀ j : Stk, j ≠ 0 → j ≠ sX → j ≠ sB → j ≠ sN → j ≠ sR → j ≠ sS → j ≠ sCW →
      j ≠ sCB → j ≠ sCT → j ≠ sCN → j ≠ sZ → s7.stk j = X₀ j := by
    intro j h0 hX hB hN hR hS hCW hCB hCT hCN hZ
    have hj10 : j ∉ ([sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] : List Stk) := by
      simp only [List.mem_cons, List.mem_nil_iff]
      tauto
    have hj3 : j ∉ ([(0 : Stk), sX] : List Stk) := by
      simp only [List.mem_cons, List.mem_nil_iff]
      tauto
    have hjbig : j ∉ (([sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ] : List Stk) ++ [sCW]
        ++ [(0 : Stk), sX] ++ [(0 : Stk), sB] ++ [(0 : Stk), sN] ++ [sN, sR]) := by
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]
      tauto
    have hj5 : j ∉ ([(0 : Stk), sN] : List Stk) := by
      simp only [List.mem_cons, List.mem_nil_iff]
      tauto
    have hj4 : j ∉ ([(0 : Stk), sB] : List Stk) := by
      simp only [List.mem_cons, List.mem_nil_iff]
      tauto
    calc s7.stk j = s6.stk j := h8_oth j hR hN hCN hCT
      _ = s5.stk j := h6_oth j hN hR
      _ = s4.stk j := fr5 j hj5
      _ = s3.stk j := fr4 j hj4
      _ = X2 j := fr3 j hj3
      _ = X1 j := h2fr j hCW
      _ = E j := h1fr j hj10
      _ = X₀ j := hEj j h0
  -- the program, split into the five phases
  let l1 : List Cmd := List.map (fun k => mkStep k rH) [sX, sB, sN, sR, sS, sCW, sCB, sCT, sCN, sZ]
  let l2 : List Cmd := [Cmd.set rH gEnd, Cmd.push sCW rH]
  let l3 : List Cmd := [mvVal 0 sX sT1 sT2, mvVal 0 sB sT1 sT2, mvVal 0 sN sT1 sT2]
  let l4 : List Cmd := [Shift.drain sN sR (Shift.gmk sN) rH rK]
  let l5 : List Cmd := [rebuildN]
  have hprog : preSetupProg rebuildN = seqs (l1 ++ l2 ++ l3 ++ l4 ++ l5) := rfl
  -- cost of the five phases
  have hA : Ev main (seqs l1) ⟨g, E⟩ ⟨g1, X1⟩ 21 := he1.mono (by decide)
  have hB : Ev main (seqs l2) ⟨g1, X1⟩ ⟨g2, X2⟩ 2 := he2
  have hC1 : Ev main (mvVal 0 sX sT1 sT2) ⟨g2, X2⟩ ⟨s3.reg, s3.stk⟩
      (16 * (isz (x : ℤ) + 1)) :=
    he3.mono (by
      have hv : vsz (Val.int (x : ℤ)) = isz (x : ℤ) := vsz_int_eq _
      rw [hv] at hn3
      exact hn3)
  have hC2 : Ev main (mvVal 0 sB sT1 sT2) ⟨s3.reg, s3.stk⟩ ⟨s4.reg, s4.stk⟩
      (16 * (isz (b : ℤ) + 1)) :=
    he4.mono (by
      have hv : vsz (Val.int (b : ℤ)) = isz (b : ℤ) := vsz_int_eq _
      rw [hv] at hn4
      exact hn4)
  have hC3 : Ev main (mvVal 0 sN sT1 sT2) ⟨s4.reg, s4.stk⟩ ⟨s5.reg, s5.stk⟩
      (16 * (isz (N : ℤ) + 1)) :=
    he5.mono (by
      have hv : vsz (Val.int (N : ℤ)) = isz (N : ℤ) := vsz_int_eq _
      rw [hv] at hn5
      exact hn5)
  have hC12 : Ev main (seqs ([mvVal 0 sX sT1 sT2] ++ [mvVal 0 sB sT1 sT2])) ⟨g2, X2⟩
      ⟨s4.reg, s4.stk⟩ (16 * (isz (x : ℤ) + 1) + 16 * (isz (b : ℤ) + 1)) :=
    ev_seqs_append _ _ _ _ _ _ _ hC1 hC2
  have hC : Ev main (seqs l3) ⟨g2, X2⟩ ⟨s5.reg, s5.stk⟩
      ((16 * (isz (x : ℤ) + 1) + 16 * (isz (b : ℤ) + 1)) + 16 * (isz (N : ℤ) + 1)) :=
    ev_seqs_append _ _ _ _ _ _ _ hC12 hC3
  have hD : Ev main (seqs l4) ⟨s5.reg, s5.stk⟩ ⟨s6.reg, s6.stk⟩
      (5 * (isz (N : ℤ) + 1) + 2) :=
    ⟨n6, he6, by
      have hh := hn6
      rw [Work.IntLib.vsz_int] at hh
      exact hh⟩
  have hE7 : Ev main (seqs l5) ⟨s6.reg, s6.stk⟩ ⟨s7.reg, s7.stk⟩
      (KR * (N.size + N + 1)) :=
    he7.mono (by
      have hh := hn7
      rw [Nat.size_eq_bits_len, Work.IntLib.ofBits_bits] at hh
      exact hh)
  have hAll : Ev main (seqs (l1 ++ l2 ++ l3 ++ l4 ++ l5)) ⟨g, E⟩ ⟨s7.reg, s7.stk⟩
      (21 + 2 + (16 * (isz (x : ℤ) + 1) + 16 * (isz (b : ℤ) + 1) + 16 * (isz (N : ℤ) + 1))
        + (5 * (isz (N : ℤ) + 1) + 2) + KR * (N.size + N + 1)) := by
    have h12 : Ev main (seqs (l1 ++ l2)) ⟨g, E⟩ ⟨g2, X2⟩ (21 + 2) := ev_seqs_append' hA hB
    have h123 : Ev main (seqs (l1 ++ l2 ++ l3)) ⟨g, E⟩ ⟨s5.reg, s5.stk⟩
        (21 + 2 + (16 * (isz (x : ℤ) + 1) + 16 * (isz (b : ℤ) + 1) + 16 * (isz (N : ℤ) + 1))) :=
      ev_seqs_append' h12 hC
    have h1234 : Ev main (seqs (l1 ++ l2 ++ l3 ++ l4)) ⟨g, E⟩ ⟨s6.reg, s6.stk⟩
        (21 + 2 + (16 * (isz (x : ℤ) + 1) + 16 * (isz (b : ℤ) + 1) + 16 * (isz (N : ℤ) + 1))
          + (5 * (isz (N : ℤ) + 1) + 2)) :=
      ev_seqs_append' h123 hD
    exact ev_seqs_append' h1234 hE7
  -- the final bound
  set T : ℕ := 21 + 2 + (16 * (isz (x : ℤ) + 1) + 16 * (isz (b : ℤ) + 1) + 16 * (isz (N : ℤ) + 1))
      + (5 * (isz (N : ℤ) + 1) + 2) + KR * (N.size + N + 1) with hT
  have hAllT : Ev main (seqs (l1 ++ l2 ++ l3 ++ l4 ++ l5)) ⟨g, E⟩ ⟨s7.reg, s7.stk⟩ T := by
    rw [hT]
    exact hAll
  refine ⟨s7, T, ?_, ?_, hv0, hvX, hvB, hvN, hvR, hvS, hvCW, hvCB, hvCT, hvCN, hvZ, hvoth⟩
  · rw [hprog]
    exact hAllT
  · rw [hT]
    have hN1 : N ≤ N * (b + 1) := Nat.le_mul_of_pos_right N (by omega)
    have hN2 : N.size ≤ N + 1 := Nat.size_le.mpr (by
      calc N < 2 ^ N := Nat.lt_two_pow_self
        _ ≤ 2 ^ N * 2 := Nat.le_mul_of_pos_right _ (by norm_num)
        _ = 2 ^ (N + 1) := by rw [pow_succ])
    have h1 : N.size + N + 1 ≤
        2 * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1) := by omega
    have h2 : KR * (N.size + N + 1) ≤
        2 * KR * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1) := by
      calc KR * (N.size + N + 1)
          ≤ KR * (2 * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1)) :=
            Nat.mul_le_mul_left KR h1
        _ = 2 * KR * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1) := by ring
    have h3 : 21 + 2 + ((16 * (isz (x : ℤ) + 1) + 16 * (isz (b : ℤ) + 1)) + 16 * (isz (N : ℤ) + 1))
        + (5 * (isz (N : ℤ) + 1) + 2) ≤
        200 * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1) := by omega
    calc 21 + 2 + (16 * (isz (x : ℤ) + 1) + 16 * (isz (b : ℤ) + 1) + 16 * (isz (N : ℤ) + 1))
          + (5 * (isz (N : ℤ) + 1) + 2) + KR * (N.size + N + 1)
        ≤ 200 * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1)
          + 2 * KR * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1) := by omega
      _ = (2 * KR + 200) * (isz (x : ℤ) + isz (b : ℤ) + isz (N : ℤ) + N * (b + 1) + 1) := by ring

end Work.IntLib
