import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auLoopDefs
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.wmLoopSent
import Submission.Work.Resample.auRoundRec
import Submission.Work.Resample.auWinBound
import Submission.Work.Resample.auLoopList
import Submission.Work.Resample.auLoopAux

/-!
# The streaming-window loop of the resampling word (paper Lemma 4.9, Thm 4.1)

`auLoopWord` runs the one-round word `auRoundRec` over the `t` records of the (re-encoded) weight
table, driving it with the sentinel-based do-while `wmLoopSent`: each round slides the window on
stack `0`, consumes the next element of the run on stack `2` (only when the slide is `1`) and pushes
the round's chunk `cons (ofList WTS) (ofList W)` onto stack `3`; the loop stops when the sentinel
`m1 = Val.nil` is the head value of stack `1`, and the window is then dropped from stack `0`.

This module contains the glue (invariant, exit predicate, one-round step) and the final assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH



/-! ## Size helpers -/

theorem vsz_cons_val_au (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc]

theorem vsz_pos_au (v : Val) : 1 ≤ vsz v := by
  cases v with
  | int z => simp [vsz, Val.enc]
  | nil => simp [vsz, Val.enc]
  | cons a b => rw [vsz_cons_val_au]; omega


/-- `headD` of an append, when the first list is nonempty. -/
theorem headD_append_of_ne_nil {α : Type} (l₁ l₂ : List α) (d : α) (h : l₁ ≠ []) :
    (l₁ ++ l₂).headD d = l₁.headD d := by
  cases l₁ with
  | nil => exact absurd rfl h
  | cons a as => rfl

/-- `a ≤ a * X` for `X ≥ 1`. -/
theorem le_mul_of_one_le_right (a X : ℕ) (h : 1 ≤ X) : a ≤ a * X := by
  have := Nat.mul_le_mul (le_refl a) h
  simpa using this

/-- `a ≤ X * a` for `X ≥ 1`. -/
theorem le_mul_of_one_le_left (a X : ℕ) (h : 1 ≤ X) : a ≤ X * a := by
  have := Nat.mul_le_mul h (le_refl a)
  simpa using this

/-- `vsz` of a list value. -/
theorem vsz_ofList_le_au (W : List Val) (B : ℕ) (h : ∀ v ∈ W, vsz v ≤ B) :
    vsz (ofList W) ≤ 3 * ((W.length + 1) * (B + 1) + 1) := by
  induction W with
  | nil => simp [ofList, vsz, Val.enc] <;> omega
  | cons v vs ih =>
    have hv : vsz v ≤ B := h v (by simp)
    have hvs : ∀ w ∈ vs, vsz w ≤ B := fun w hw => h w (by simp [hw])
    have hih := ih hvs
    rw [show ofList (v :: vs) = .cons v (ofList vs) from rfl, vsz_cons_val_au, List.length_cons]
    nlinarith [hv, hih]

/-! ## The invariant -/

/-- The chunks produced by the first `i` rounds, in stack order (newest on top). -/
def auChunks (WTS W : ℕ → List Val) (i : ℕ) : List Val :=
  ((List.range i).map (fun k => Val.cons (ofList (WTS k)) (ofList (W k)))).reverse

/-- The loop invariant after `i` rounds. -/
def auLI (g : ℕ → ℕ) (WTS W : ℕ → List Val) (ELEM REC P : List Val) (m1 m2 m3 : Val)
    (a0 : Stk → List Val) (i : ℕ) : List Val → (Stk → List Val) → Prop :=
  fun vs a => vs = ofList (W i) :: P ∧ a 1 = REC.drop i ++ [m1] ∧
    a 2 = ELEM.drop (((List.range i).map g).sum) ++ [m2] ∧
    a 3 = auChunks WTS W i ++ [m3] ∧
    (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → a k = a0 k)

/-- The state in which the loop stops: `t` rounds done, the sentinel on stack `1`. -/
def auLF (g : ℕ → ℕ) (WTS W : ℕ → List Val) (ELEM P : List Val) (m1 m2 m3 : Val)
    (a0 : Stk → List Val) (t L B : ℕ) : List Val → (Stk → List Val) → Prop :=
  fun vs a => ∃ Wt : List Val, vs = ofList Wt :: P ∧ Wt.length = L ∧
    (∀ v ∈ Wt, vsz v ≤ B) ∧ a 1 = [m1] ∧
    a 2 = ELEM.drop (((List.range t).map g).sum) ++ [m2] ∧
    a 3 = auChunks WTS W t ++ [m3] ∧
    (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → a k = a0 k)

/-! ## One round of the loop -/

theorem auLoopStep (hk : HvdH.KernelLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (L B t i : ℕ) (g : ℕ → ℕ)
      (WTS : ℕ → List HvdH.Val) (ELEM REC P : List HvdH.Val) (W : ℕ → List HvdH.Val)
      (m1 m2 m3 : HvdH.Val) (a0 : HvdH.Stk → List HvdH.Val),
      i < t →
      (∀ k, g k ≤ 1) →
      REC.length = t →
      (∀ k < t, REC.getD k .nil = HvdH.Val.cons (auSeqFlg (g k))
        (HvdH.Val.cons (.int (g k : ℤ)) (HvdH.ofList (WTS k)))) →
      (∀ k ≤ t, (W k).length = L) →
      (∀ k < t, W (k+1) = ((W k).drop (g k) ++
        [ELEM.getD (((List.range k).map g).sum) .nil]).take L) →
      (∀ k < t, (WTS k).length = L) →
      (∀ v ∈ W i, HvdH.vsz v ≤ B) →
      (∀ v ∈ WTS i, HvdH.vsz v ≤ B) →
      (∀ v ∈ ELEM, HvdH.vsz v ≤ B) →
      HvdH.vsz m2 ≤ B →
      (((List.range t).map g).sum ≤ ELEM.length) →
      Work.Resample.WordM main prog (auLI g WTS W ELEM REC P m1 m2 m3 a0 i)
        (fun _ _ out b => auLI g WTS W ELEM REC P m1 m2 m3 a0 (i+1) out b)
        (fun _ _ => K * ((L + 1) * (B + 1) + 1)) := by
  obtain ⟨prog, K, hspec⟩ := auRoundRec hk hl
  refine ⟨prog, K, ?_⟩
  intro main L B t i g WTS ELEM REC P W m1 m2 m3 a0 hi hg hREClen hREC hWlen hWrec hWTSlen
    hWi hWTSi hELEM hm2 hsum
  have hspec' := hspec main L (g i) B (W i) (WTS i) P (REC.drop (i+1) ++ [m1])
      ((ELEM.drop (((List.range i).map g).sum) ++ [m2]).tail)
      (auChunks WTS W i ++ [m3])
      ((ELEM.drop (((List.range i).map g).sum) ++ [m2]).headD .nil)
      (hg i) (hWlen i (le_of_lt hi)) (hWTSlen i hi) hWi hWTSi
      (auLoopAux.2.1 ELEM m2 (((List.range i).map g).sum) B hELEM hm2)
  refine Work.Resample.WordM.conseq hspec' ?_ ?_ ?_
  · intro vs a hI
    obtain ⟨hvs, ha1, ha2, ha3, hfr⟩ := hI
    refine ⟨hvs, ?_, ?_, ha3⟩
    · rw [ha1]
      have hiREC : i < REC.length := by rw [hREClen]; exact hi
      rw [auLoopList.1 REC i .nil hiREC, hREC i hi]
      rfl
    · rw [ha2]
      exact (auLoopAux.1 ELEM m2 (((List.range i).map g).sum)).symm
  · intro vs a out b hI hp
    obtain ⟨hvs, ha1, ha2, ha3, hfr⟩ := hI
    obtain ⟨hout, hb1, hb2, hb3, hfrb⟩ := hp
    refine ⟨?_, hb1, ?_, ?_, ?_⟩
    · -- the new window
      rw [hout, hWrec i hi]
      have hle : ((List.range i).map g).sum + g i ≤ ELEM.length := by
        have hstep := auLoopList.2.2.2.1 g i
        have hmono := auLoopList.2.2.2.2.1 g (i+1) t (by omega)
        omega
      have hkey := auLoopAux.2.2.1 ELEM m2 (((List.range i).map g).sum) (g i) L (W i)
        (hg i) (hWlen i (le_of_lt hi)) hle
      rw [hkey]
    · -- stack 2
      rw [hb2]
      by_cases hg1 : g i = 1
      · have hne : ELEM.drop (((List.range i).map g).sum) ≠ [] := by
          rw [ne_eq, List.drop_eq_nil_iff]
          have hstep := auLoopList.2.2.2.1 g i
          have hmono := auLoopList.2.2.2.2.1 g (i+1) t (by omega)
          omega
        rw [if_pos hg1, auLoopAux.2.2.2 ELEM m2 (((List.range i).map g).sum) hne]
        have hstep := auLoopList.2.2.2.1 g i
        rw [hstep, hg1]
      · have hg0 : g i = 0 := by
          have hgi : g i ≤ 1 := hg i
          omega
        rw [if_neg hg1, auLoopAux.1 ELEM m2 (((List.range i).map g).sum)]
        have hstep := auLoopList.2.2.2.1 g i
        rw [hstep, hg0, Nat.add_zero]
    · -- stack 3
      rw [hb3]
      simp only [auChunks]
      rw [auLoopList.2.2.2.2.2 (fun k => Val.cons (ofList (WTS k)) (ofList (W k))) i]
      rfl
    · intro k hk0 hk1 hk2 hk3
      rw [hfrb k hk0 hk1 hk2 hk3, hfr k hk0 hk1 hk2 hk3]
  · intro vs a _; exact le_rfl

/-! ## The loop -/

theorem auLoopWord (hk : HvdH.KernelLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (L B t : ℕ)
      (g : ℕ → ℕ) (WTS : ℕ → List HvdH.Val) (ELEM REC P : List HvdH.Val)
      (W : ℕ → List HvdH.Val) (m1 m2 m3 : HvdH.Val),
      m1 = HvdH.Val.nil →
      (∀ k, g k ≤ 1) →
      REC.length = t →
      (∀ k < t, REC.getD k .nil = HvdH.Val.cons (Work.Resample.auSeqFlg (g k))
        (HvdH.Val.cons (.int (g k : ℤ)) (HvdH.ofList (WTS k)))) →
      (∀ k ≤ t, (W k).length = L) →
      (∀ k < t, W (k+1) = ((W k).drop (g k) ++
        [ELEM.getD (((List.range k).map g).sum) .nil]).take L) →
      (∀ k < t, (WTS k).length = L) →
      (∀ v ∈ W 0, HvdH.vsz v ≤ B) →
      (∀ k < t, ∀ v ∈ WTS k, HvdH.vsz v ≤ B) →
      (∀ v ∈ ELEM, HvdH.vsz v ≤ B) →
      HvdH.vsz m2 ≤ B →
      (((List.range t).map g).sum ≤ ELEM.length) →
      Work.Resample.WordM main prog
        (fun vs a => vs = HvdH.ofList (W 0) :: P ∧ a 1 = REC ++ [m1] ∧
          a 2 = ELEM ++ [m2] ∧ a 3 = [m3])
        (fun vs a out b => out = P ∧ b 1 = [m1] ∧
          b 2 = ELEM.drop (((List.range t).map g).sum) ++ [m2] ∧
          b 3 = ((List.range t).map (fun k => HvdH.Val.cons (HvdH.ofList (WTS k))
            (HvdH.ofList (W k)))).reverse ++ [m3] ∧
          (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → b k = a k))
        (fun vs a => K * (t + 1) * ((L + 1) * (B + 1) + 1)) := by
  obtain ⟨recP, Krec, hStep⟩ := auLoopStep hk hl
  obtain ⟨comb, KL, hLoop⟩ := wmLoopSent 1 (by decide)
  obtain ⟨dropP, Kdrop, hDrop⟩ := hk.drop
  refine ⟨HvdH.Cmd.seq (comb recP) dropP, Krec + 2 * KL + 4 * Kdrop + 4, ?_⟩
  intro main L B t g WTS ELEM REC P W m1 m2 m3 hm1 hg hREClen hREC hWlen hWrec hWTSlen
    hW0 hWTSB hELEMB hm2B hsum
  intro vs a hpre s R Bg h0 hk0
  obtain ⟨hvs0, ha1_0, ha2_0, ha3_0⟩ := hpre
  have hwin : ∀ k ≤ t, ∀ v ∈ W k, vsz v ≤ B :=
    auWinBound t L B g ELEM W hg hWrec hWlen hW0 hELEMB
  have hI0 : auLI g WTS W ELEM REC P m1 m2 m3 a 0 vs a := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using hvs0
    · rw [ha1_0]; simp
    · rw [ha2_0]; simp
    · rw [ha3_0]; simp [auChunks]
    · intro k _ _ _ _; rfl
  have hbody : ∀ i vs' a', auLI g WTS W ELEM REC P m1 m2 m3 a i vs' a' → i < t →
      Work.Resample.WordM main recP (fun w b => w = vs' ∧ b = a')
        (fun _ _ out b => auLI g WTS W ELEM REC P m1 m2 m3 a (i+1) out b)
        (fun _ _ => Krec * ((L + 1) * (B + 1) + 1)) := by
    intro i vs' a' hI hi
    have hstep := hStep main L B t i g WTS ELEM REC P W m1 m2 m3 a hi hg hREClen hREC hWlen
      hWrec hWTSlen (hwin i (le_of_lt hi)) (hWTSB i hi) hELEMB hm2B hsum
    refine Work.Resample.WordM.conseq hstep ?_ ?_ ?_
    · intro vs'' a'' hwa
      rw [hwa.1, hwa.2]
      exact hI
    · intro vs'' a'' out b _ hp
      exact hp
    · intro vs'' a'' _; exact le_rfl
  have hcont : ∀ i vs' a', auLI g WTS W ELEM REC P m1 m2 m3 a i vs' a' → i < t →
      a' 1 ≠ [] ∧ (encs (a' 1)).headD Glyph.eos ≠ Glyph.nil := by
    intro i vs' a' hI hi
    obtain ⟨_, ha1, _, _, _⟩ := hI
    have hiREC : i < REC.length := by rw [hREClen]; exact hi
    have hdrop : REC.drop i = REC.getD i .nil :: REC.drop (i+1) :=
      auLoopList.1 REC i .nil hiREC
    have hhead : (encs (REC.drop i)).headD Glyph.eos = Glyph.cons := by
      rw [hdrop, hREC i hi, Work.Kernel.encs_cons]
      rfl
    have hne : encs (REC.drop i) ≠ [] := by
      intro h
      have hlen : 0 < (encs (REC.drop i)).length := by
        rw [hdrop, hREC i hi, Work.Kernel.encs_cons, List.length_append]
        have hpos : 0 < (Val.cons (auSeqFlg (g i)) (Val.cons (.int (g i : ℤ))
            (ofList (WTS i)))).enc.length := vsz_pos_au _
        omega
      rw [h] at hlen
      simp at hlen
    constructor
    · rw [ha1, hdrop]; simp
    · have hA : (encs (a' 1)).headD Glyph.eos = Glyph.cons := by
        rw [ha1, Work.Kernel.encs_append, headD_append_of_ne_nil _ _ _ hne, hhead]
      rw [hA]
      have : Glyph.cons ≠ Glyph.nil := by decide
      exact this
  have hexit : ∀ vs' a', auLI g WTS W ELEM REC P m1 m2 m3 a t vs' a' →
      (encs (a' 1)).headD Glyph.eos = Glyph.nil := by
    intro vs' a' hI
    obtain ⟨_, ha1, _, _, _⟩ := hI
    have hdrop : REC.drop t = [] := by
      rw [List.drop_eq_nil_iff]; omega
    rw [ha1, hdrop, List.nil_append, hm1]
    rfl
  have hF : ∀ vs' a', auLI g WTS W ELEM REC P m1 m2 m3 a t vs' a' →
      auLF g WTS W ELEM P m1 m2 m3 a t L B vs' a' := by
    intro vs' a' hI
    obtain ⟨hvs, ha1, ha2, ha3, hfr⟩ := hI
    refine ⟨W t, hvs, hWlen t le_rfl, hwin t le_rfl, ?_, ha2, ha3, hfr⟩
    have hdrop : REC.drop t = [] := by
      rw [List.drop_eq_nil_iff]; omega
    rw [ha1, hdrop, List.nil_append]
  have hloop := hLoop main recP (auLI g WTS W ELEM REC P m1 m2 m3 a)
    (auLF g WTS W ELEM P m1 m2 m3 a t L B) (Krec * ((L + 1) * (B + 1) + 1)) t
    hbody hcont hexit hF
  obtain ⟨outL, bL, sL, nL, hFL, hevL, hcL, h0L, hkL⟩ := hloop vs a hI0 s R Bg h0 hk0
  obtain ⟨Wt, hvsL, hWtlen, hWtB, hbL1, hbL2, hbL3, hfrL⟩ := hFL
  have hdropM := Work.Resample.WordM.ofWordR (hDrop main)
  have hneL : outL ≠ [] := by rw [hvsL]; simp
  obtain ⟨outD, bD, sD, nD, hPD, hevD, hcD, h0D, hkD⟩ := hdropM outL bL hneL sL R Bg h0L hkL
  obtain ⟨⟨v, rest, hsplit, houtD⟩, hbD⟩ := hPD
  have hsplit' : HvdH.ofList Wt :: P = v :: rest := by rw [← hvsL]; exact hsplit
  injection hsplit' with _ hrest
  have houtP : outD = P := by rw [houtD, hrest]
  have hheadL : outL.headD .nil = HvdH.ofList Wt := by rw [hvsL]; rfl
  have hWtSz : HvdH.vsz (HvdH.ofList Wt) ≤ 3 * ((L + 1) * (B + 1) + 1) := by
    have h := vsz_ofList_le_au Wt B hWtB
    rwa [hWtlen] at h
  refine ⟨outD, bD, sD, nL + nD, ?_, HvdH.Eval.seq hevL hevD, ?_, h0D, ?_⟩
  · refine ⟨houtP, ?_, ?_, ?_, ?_⟩
    · rw [hbD, hbL1]
    · rw [hbD, hbL2]
    · rw [hbD, hbL3]; rfl
    · intro k hk1 hk2 hk3 hk4
      rw [hbD, hfrL k hk1 hk2 hk3 hk4]
  · have hX : 1 ≤ (L + 1) * (B + 1) + 1 := by omega
    have ht : 1 ≤ t + 1 := by omega
    have hcD' : nD ≤ Kdrop * (HvdH.vsz (HvdH.ofList Wt) + 1) := by
      have h1 : nD ≤ Kdrop * (HvdH.vsz (outL.headD .nil) + 1) := hcD
      rwa [hheadL] at h1
    have hd2 : Kdrop * (HvdH.vsz (HvdH.ofList Wt) + 1) ≤
        (t + 1) * ((L + 1) * (B + 1) + 1) * (4 * Kdrop) := by
      have hs : HvdH.vsz (HvdH.ofList Wt) + 1 ≤ 4 * ((L + 1) * (B + 1) + 1) := by
        have h2 : HvdH.vsz (HvdH.ofList Wt) ≤ 3 * ((L + 1) * (B + 1) + 1) := hWtSz
        omega
      calc Kdrop * (HvdH.vsz (HvdH.ofList Wt) + 1)
          ≤ Kdrop * (4 * ((L + 1) * (B + 1) + 1)) := Nat.mul_le_mul_left _ hs
        _ = 4 * Kdrop * ((L + 1) * (B + 1) + 1) := by ring
        _ ≤ 4 * Kdrop * ((L + 1) * (B + 1) + 1) * (t + 1) :=
              le_mul_of_one_le_right _ _ ht
        _ = (t + 1) * ((L + 1) * (B + 1) + 1) * (4 * Kdrop) := by ring
    have hl2 : nL ≤ (t + 1) * ((L + 1) * (B + 1) + 1) * (Krec + 2 * KL) := by
      have h3 : Krec * ((L + 1) * (B + 1) + 1) + KL +
          KL * ((L + 1) * (B + 1) + 1) ≤
          ((L + 1) * (B + 1) + 1) * (Krec + 2 * KL) := by
        have ha : Krec * ((L + 1) * (B + 1) + 1) =
            ((L + 1) * (B + 1) + 1) * Krec := by ring
        have hb : KL ≤ ((L + 1) * (B + 1) + 1) * KL :=
          le_mul_of_one_le_left KL ((L + 1) * (B + 1) + 1) hX
        have hc : KL * ((L + 1) * (B + 1) + 1) =
            ((L + 1) * (B + 1) + 1) * KL := by ring
        calc Krec * ((L + 1) * (B + 1) + 1) + KL + KL * ((L + 1) * (B + 1) + 1)
            ≤ ((L + 1) * (B + 1) + 1) * Krec + ((L + 1) * (B + 1) + 1) * KL +
              ((L + 1) * (B + 1) + 1) * KL :=
              Nat.add_le_add (Nat.add_le_add (le_of_eq ha) hb) (le_of_eq hc)
          _ = ((L + 1) * (B + 1) + 1) * (Krec + 2 * KL) := by ring
      calc nL ≤ (t + 1) * (Krec * ((L + 1) * (B + 1) + 1) + KL) + KL := hcL
        _ ≤ (t + 1) * (Krec * ((L + 1) * (B + 1) + 1) + KL) +
              KL * ((L + 1) * (B + 1) + 1) * (t + 1) := by
              apply Nat.add_le_add_left
              calc KL ≤ KL * ((L + 1) * (B + 1) + 1) :=
                    le_mul_of_one_le_right KL ((L + 1) * (B + 1) + 1) hX
                _ ≤ KL * ((L + 1) * (B + 1) + 1) * (t + 1) :=
                    le_mul_of_one_le_right _ _ ht
        _ = (t + 1) * (Krec * ((L + 1) * (B + 1) + 1) + KL +
              KL * ((L + 1) * (B + 1) + 1)) := by ring
        _ ≤ (t + 1) * (((L + 1) * (B + 1) + 1) * (Krec + 2 * KL)) :=
              Nat.mul_le_mul_left _ h3
        _ = (t + 1) * ((L + 1) * (B + 1) + 1) * (Krec + 2 * KL) := by ring
    calc nL + nD
        ≤ (t + 1) * ((L + 1) * (B + 1) + 1) * (Krec + 2 * KL) +
          (t + 1) * ((L + 1) * (B + 1) + 1) * (4 * Kdrop) :=
            Nat.add_le_add hl2 (le_trans hcD' hd2)
      _ = (t + 1) * ((L + 1) * (B + 1) + 1) * (Krec + 2 * KL + 4 * Kdrop) := by ring
      _ ≤ (t + 1) * ((L + 1) * (B + 1) + 1) * (Krec + 2 * KL + 4 * Kdrop + 4) :=
            Nat.mul_le_mul_left _ (by omega)
      _ = (Krec + 2 * KL + 4 * Kdrop + 4) * (t + 1) * ((L + 1) * (B + 1) + 1) := by ring
  · intro k hk0
    rw [hkD k hk0]

end Work.Resample
