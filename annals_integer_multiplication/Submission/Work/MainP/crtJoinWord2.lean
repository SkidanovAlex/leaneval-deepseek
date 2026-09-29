import Mathlib
import Submission.Work.MainP.crtDefs
import Submission.Work.MainP.crtJoinDefs
import Submission.Work.MainP.crtJoinElems
import Submission.Work.MainP.crtJoinPhase
import Submission.Work.MainP.crtJoinAlg

set_option autoImplicit false

namespace Work.MainP

open HvdH


/-! ## The master program and its evaluation -/

/-- The whole word: set up, consume the first list, reset the `jdelim` register, consume the second
list, interleave. -/
def crtJoinProg : HvdH.Cmd :=
  .seq jsetup (.seq (consumeListN 2 6) (.seq (.set 5 jdelim) (.seq (consumeListN 3 7) joinPhase)))

/-- State after `jsetup`. -/
def afterSetup (s : HvdH.State) : HvdH.State :=
  (((s.updStk 6 (jcb :: s.stk 6)).updStk 7 (jcb :: s.stk 7)).updReg 5 jdelim).updReg 3 jtok

theorem state_ext {s t : HvdH.State} (h : ∀ r, s.reg r = t.reg r) (h2 : ∀ k, s.stk k = t.stk k) :
    s = t := by
  cases s with
  | mk r k =>
    cases t with
    | mk r' k' =>
      simp only [HvdH.State.mk.injEq]
      exact ⟨funext h, funext h2⟩

theorem eval_pushR (main : HvdH.Cmd) (s : HvdH.State) (k : HvdH.Stk) (r : HvdH.Reg) (g : HvdH.Glyph)
    (h : s.reg r = g) : HvdH.Eval main (.push k r) s (s.updStk k (g :: s.stk k)) 1 := by
  simpa [h, HvdH.State.tPush, HvdH.State.updStk] using HvdH.Eval.push k r s

theorem afterSetup_stk6 (s : HvdH.State) : (afterSetup s).stk 6 = jcb :: s.stk 6 := by
  simp [afterSetup, HvdH.State.updStk_apply]

theorem afterSetup_stk7 (s : HvdH.State) : (afterSetup s).stk 7 = jcb :: s.stk 7 := by
  simp [afterSetup, HvdH.State.updStk_apply]

theorem afterSetup_stk_other (s : HvdH.State) {k : HvdH.Stk} (h6 : k ≠ 6) (h7 : k ≠ 7) :
    (afterSetup s).stk k = s.stk k := by
  simp [afterSetup, HvdH.State.updStk_apply, h6, h7]

theorem afterSetup_reg5 (s : HvdH.State) : (afterSetup s).reg 5 = jdelim := by
  simp [afterSetup, HvdH.State.updReg_apply]

theorem eval_jsetup (main : HvdH.Cmd) (s : HvdH.State) :
    HvdH.Eval main jsetup s (afterSetup s) 5 := by
  let A1 : State := s.updReg 5 jdelim
  let A2 : State := A1.updReg 3 jcb
  let A3 : State := A2.updStk 6 (jcb :: A2.stk 6)
  let A4 : State := A3.updStk 7 (jcb :: A3.stk 7)
  let A5 : State := A4.updReg 3 jtok
  have e1 : Eval main (.set 5 jdelim) s A1 1 := Eval.set 5 jdelim s
  have e2 : Eval main (.set 3 jcb) A1 A2 1 := Eval.set 3 jcb A1
  have hreg3 : A2.reg 3 = jcb := by simp [A2, A1, HvdH.State.updReg_apply]
  have e3 : Eval main (.push 6 3) A2 A3 1 := by
    simpa [A3] using eval_pushR main A2 6 3 jcb hreg3
  have hreg3' : A3.reg 3 = jcb := by simp [A3, A2, A1, HvdH.State.updStk_reg, HvdH.State.updReg_apply]
  have e4 : Eval main (.push 7 3) A3 A4 1 := by
    simpa [A4] using eval_pushR main A3 7 3 jcb hreg3'
  have e5 : Eval main (.set 3 jtok) A4 A5 1 := Eval.set 3 jtok A4
  have hchain : Eval main jsetup s A5 5 := by
    unfold jsetup
    exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))
  have hA5 : A5 = afterSetup s := by
    apply state_ext
    · intro r
      simp only [A1, A2, A3, A4, A5, afterSetup, HvdH.State.updReg_apply, HvdH.State.updStk_reg]
      split_ifs <;> simp_all
    · intro k
      simp only [A1, A2, A3, A4, A5, afterSetup, HvdH.State.updStk_apply, HvdH.State.updReg_stk]
      split_ifs <;> simp_all
  rw [← hA5]
  exact hchain

/-! ## The composition of the three phases -/

theorem crtJoinProg_eval (main : HvdH.Cmd) (s0 : HvdH.State) (Gs Ws : List (List HvdH.Glyph))
    (t : List HvdH.Glyph)
    (hs0 : s0.stk 0 = listEncR Gs ++ listEncR Ws ++ t)
    (hlen : Ws.length = Gs.length)
    (hG : ∀ G ∈ Gs, HvdH.PendOK G 1) (hGne : ∀ G ∈ Gs, G ≠ [])
    (hW : ∀ W ∈ Ws, HvdH.PendOK W 1) (hWne : ∀ W ∈ Ws, W ≠ []) :
    ∃ (s' : HvdH.State) (n : ℕ),
      n ≤ 5 + (30 * ((Gs.map List.length).sum + Gs.length + 1) + 10) + 1 +
            (30 * ((Ws.map List.length).sum + Ws.length + 1) + 10) +
            (20 * ((Ws.map List.length).sum + (Gs.map List.length).sum + Ws.length + Gs.length + 1) + 10) ∧
      HvdH.Eval main crtJoinProg s0 s' n ∧
      s'.stk 0 = outGlyphs Ws Gs ++ t ∧
      ∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = s0.stk k := by
  have h1 : Eval main jsetup s0 (afterSetup s0) 5 := eval_jsetup main s0
  -- phase 1
  have hpre1 : clPre (afterSetup s0) 2 6 Gs (listEncR Ws ++ t) (s0.stk 2) (s0.stk 6)
      = afterSetup s0 := by
    apply state_ext
    · intro r
      simp only [clPre, afterSetup, HvdH.State.updReg_apply, HvdH.State.updStk_reg]
      split_ifs <;> simp_all
    · intro k
      simp only [clPre, afterSetup, HvdH.State.updReg_stk, HvdH.State.updStk_apply]
      split_ifs <;> simp_all [hs0, List.append_assoc]
  obtain ⟨s1, n1, hn1, hev1, h1_0, h1_2, h1_6, h1_fr⟩ :=
    crtJoinElems main (afterSetup s0) 2 6 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) Gs (listEncR Ws ++ t) (s0.stk 2) (s0.stk 6) hG hGne
  rw [hpre1] at hev1
  -- phase 2
  have hset2 : Eval main (.set 5 jdelim) s1 (s1.updReg 5 jdelim) 1 := Eval.set 5 jdelim s1
  have hs1_3 : s1.stk 3 = s0.stk 3 := by
    rw [h1_fr 3 (by decide) (by decide) (by decide)]
    exact afterSetup_stk_other s0 (by decide) (by decide)
  have hs1_7 : s1.stk 7 = jcb :: s0.stk 7 := by
    rw [h1_fr 7 (by decide) (by decide) (by decide)]
    exact afterSetup_stk7 s0
  have hs1_1 : s1.stk 1 = s0.stk 1 := by
    rw [h1_fr 1 (by decide) (by decide) (by decide)]
    exact afterSetup_stk_other s0 (by decide) (by decide)
  have hpre2 : clPre (s1.updReg 5 jdelim) 3 7 Ws t (s0.stk 3) (s0.stk 7)
      = s1.updReg 5 jdelim := by
    apply state_ext
    · intro r
      simp only [clPre, HvdH.State.updReg_apply]
      split_ifs <;> simp_all
    · intro k
      simp only [clPre, HvdH.State.updStk_apply, HvdH.State.updReg_stk]
      split_ifs <;> simp_all [h1_0, hs1_3, hs1_7, List.append_assoc]
  obtain ⟨s2, n2, hn2, hev2, h2_0, h2_3, h2_7, h2_fr⟩ :=
    crtJoinElems main (s1.updReg 5 jdelim) 3 7 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) Ws t (s0.stk 3) (s0.stk 7) hW hWne
  rw [hpre2] at hev2
  -- phase 3
  have hs2_2 : s2.stk 2 = bufReg Gs ++ s0.stk 2 := by
    rw [h2_fr 2 (by decide) (by decide) (by decide)]
    exact h1_2
  have hs2_6 : s2.stk 6 = cntReg Gs ++ (jcb :: s0.stk 6) := by
    rw [h2_fr 6 (by decide) (by decide) (by decide)]
    exact h1_6
  have hs2_other : ∀ k : HvdH.Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → k ≠ 6 → k ≠ 7 →
      s2.stk k = s0.stk k := by
    intro k hk0 hk2 hk3 hk6 hk7
    rw [h2_fr k hk0 hk3 hk7]
    simp only [HvdH.State.updReg_stk]
    rw [h1_fr k (by omega) (by omega) (by omega)]
    exact afterSetup_stk_other s0 (by omega) (by omega)
  have hjp : jpPre ⟨s2.reg, s0.stk⟩ Ws Gs t = s2 := by
    apply state_ext
    · intro r; simp [jpPre]
    · intro k
      simp only [jpPre, HvdH.State.updStk_apply, HvdH.State.updStk_reg]
      split_ifs <;> simp_all [h2_0, hs2_2, h2_3, hs2_6, h2_7, hs2_other, List.append_assoc]
  obtain ⟨s3, n3, hn3, hev3, h3_0, h3_fr⟩ := crtJoinPhase main ⟨s2.reg, s0.stk⟩ Ws Gs t hlen hGne
  rw [hjp] at hev3
  refine ⟨s3, 5 + (n1 + (1 + (n2 + n3))), ?_, ?_, ?_, ?_⟩
  · omega
  · unfold crtJoinProg
    exact Eval.seq h1 (Eval.seq hev1 (Eval.seq hset2 (Eval.seq hev2 hev3)))
  · exact h3_0
  · intro k hk
    exact h3_fr k hk

/-! ## The target theorem -/

theorem crtJoinWord2 (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (xs ws : List HvdH.Val),
    xs.length = ws.length →
    HvdH.WordR main prog
      (fun vs => ∃ rest, vs = HvdH.ofList xs :: HvdH.ofList ws :: rest)
      (fun vs out => ∃ rest, vs = HvdH.ofList xs :: HvdH.ofList ws :: rest ∧
        out = HvdH.ofList (Work.MainP.zipRec xs ws) :: rest)
      (fun vs => K * (HvdH.vsz (HvdH.ofList xs) + HvdH.vsz (HvdH.ofList ws) + 1)) := by
  refine ⟨crtJoinProg, 200, ?_⟩
  intro main xs ws hlen vs hpre s R hR
  obtain ⟨rest, rfl⟩ := hpre
  obtain ⟨halg_eq, halg0, halg2, halgC, halgP⟩ := crtJoinAlg xs ws hlen
  have hs0 : s.stk 0 = listEncR (xs.map HvdH.Val.enc) ++ listEncR (ws.map HvdH.Val.enc) ++
      (HvdH.encs rest ++ R) := by
    rw [hR, Work.Kernel.encs_cons, Work.Kernel.encs_cons, listEncR_map_enc, listEncR_map_enc]
    simp only [List.append_assoc]
  have hG : ∀ G ∈ xs.map HvdH.Val.enc, HvdH.PendOK G 1 := by
    intro G hG
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hG
    exact (halgP x (List.mem_append_left _ hx)).1
  have hGne : ∀ G ∈ xs.map HvdH.Val.enc, G ≠ [] := by
    intro G hG
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hG
    exact (halgP x (List.mem_append_left _ hx)).2
  have hW : ∀ W ∈ ws.map HvdH.Val.enc, HvdH.PendOK W 1 := by
    intro W hW
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hW
    exact (halgP x (List.mem_append_right _ hx)).1
  have hWne : ∀ W ∈ ws.map HvdH.Val.enc, W ≠ [] := by
    intro W hW
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hW
    exact (halgP x (List.mem_append_right _ hx)).2
  have hlen' : (ws.map HvdH.Val.enc).length = (xs.map HvdH.Val.enc).length := by simp [hlen]
  obtain ⟨s', n, hn, hev, hs'0, hs'fr⟩ :=
    crtJoinProg_eval main s (xs.map HvdH.Val.enc) (ws.map HvdH.Val.enc)
      (HvdH.encs rest ++ R) hs0 hlen' hG hGne hW hWne
  refine ⟨HvdH.ofList (Work.MainP.zipRec xs ws) :: rest, s', n, ⟨rest, rfl, rfl⟩, hev, ?_, ?_, ?_⟩
  · change n ≤ 200 * (HvdH.vsz (HvdH.ofList xs) + HvdH.vsz (HvdH.ofList ws) + 1)
    have hf : (List.length ∘ HvdH.Val.enc) = HvdH.vsz := by funext v; rfl
    have hmap_x : (xs.map HvdH.Val.enc).map List.length = xs.map HvdH.vsz := by rw [List.map_map, hf]
    have hmap_w : (ws.map HvdH.Val.enc).map List.length = ws.map HvdH.vsz := by rw [List.map_map, hf]
    rw [hmap_x, hmap_w] at hn
    simp only [List.length_map] at hn
    rw [vsz_ofList xs, vsz_ofList ws]
    omega
  · rw [hs'0, ← halg_eq, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · intro k hk
    exact hs'fr k hk

end Work.MainP
