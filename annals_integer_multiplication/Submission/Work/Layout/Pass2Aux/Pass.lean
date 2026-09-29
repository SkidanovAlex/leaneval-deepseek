import Mathlib
import Submission.Work.Layout.Pass2Aux
import Submission.Work.Layout.Pass2Aux.Facts
import Submission.Work.Layout.Pass2Aux.Pure

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# The one-pass lemma

`passTail_ev` proves that the loop of `Sk.pass` followed by its leftover move computes `Sk.passGo`,
with cost bounded by the potential `passW`; `pass_ev` adds the leading `peek Y rF`.
-/

namespace Work.Layout

open HvdH
open scoped List

/-- the `cons`-value hypothesis in the weaker form used by the movers -/
theorem consForm {rs : List (List Val)}
    (h : ∀ r ∈ rs, ∀ v ∈ r, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') :
    ∀ r ∈ rs, ∀ v ∈ r, ∃ a b : Val, v = Val.cons a b :=
  fun r hr v hv => let ⟨k, v', hh⟩ := h r hr v hv; ⟨Val.int k, v', hh⟩

/-- the `cons`-value hypothesis in the flat form used by `headD_runEncB_pos` -/
theorem flatConsForm {qs : List (List Val)}
    (h : ∀ v ∈ qs.flatten, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') :
    ∀ v ∈ qs.flatten, ∃ a b : Val, v = Val.cons a b :=
  fun v hv => let ⟨k, v', hh⟩ := h v hv; ⟨Val.int k, v', hh⟩

/-- dropping four head runs -/
theorem sublist_tails2 (p p' : List Val) (ps2 : List (List Val)) (q q' q'' : List Val)
    (qs3 : List (List Val)) :
    (ps2 ++ (q'' :: qs3)) <+ ((p :: p' :: ps2) ++ (q :: q' :: q'' :: qs3)) :=
  ((sublist_head_left p' ps2 (q'' :: qs3)).trans
    ((sublist_head_left p (p' :: ps2) (q'' :: qs3)).trans
      (((List.sublist_cons_self q' (q'' :: qs3)).trans
        (List.sublist_cons_self q (q' :: q'' :: qs3))).append_left (p :: p' :: ps2))))

/-- discharge a disequality of two stacks from the `Nodup` hypothesis `hdis` -/
macro "nodis" : tactic => `(tactic| (intro hh; subst hh; simp_all [List.nodup_cons]))

/-- discharge a non-membership in a list of stacks from the `Nodup` hypothesis `hdis` -/
macro "nodis_mem" : tactic => `(tactic| (
  intro hmem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  repeat' (first
    | (rcases hmem with h | hmem
       ; first | (exact absurd h (by nodis)) | (exact absurd hmem (by nodis)))
    | (exact absurd hmem (by nodis)))))

/-- the `cons`-value hypothesis for a single run -/
theorem consForm1 {r : List Val}
    (h : ∀ v ∈ r, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') :
    ∀ v ∈ r, ∃ a b : Val, v = Val.cons a b :=
  fun v hv => let ⟨k, v', hh⟩ := h v hv; ⟨Val.int k, v', hh⟩

/-- leaving a loop after one more (failing) test -/
theorem ev_loop_exit {main : Cmd} {r : Reg} {c : Glyph} {body : Cmd} {s s' : State} {n : ℕ}
    (h : s.reg r = c) (hev : Ev main body s s' n) (hne : s'.reg r ≠ c) :
    Ev main (.loop r c body) s s' (n + 1 + 1) :=
  Ev.loopT h hev (Ev.loopF (body := body) (s := s') hne)

theorem runEncB_cons_append (r : List Val) (rs : List (List Val)) (J : List Glyph) :
    Sk.runEncB (r :: rs) ++ J = encs r ++ gMark :: (Sk.runEncB rs ++ J) := by
  rw [runEncB_cons, List.append_assoc, List.cons_append]

/-- the frame of a `mergePair` call, widened to all stacks outside `{SX,SY,dest}` -/
theorem mergePair_frame {X Y T D SA SB : Stk} {X' : Stk → List Glyph} {s1 : State}
    (hfr : ∀ j : Stk, j ≠ X → j ≠ Y → j ≠ T → j ≠ D → j ≠ SA → j ≠ SB → s1.stk j = X' j)
    (hT : s1.stk T = X' T) (hSA : s1.stk SA = X' SA) (hSB : s1.stk SB = X' SB) :
    ∀ k : Stk, k ≠ X → k ≠ Y → k ≠ D → s1.stk k = X' k := by
  intro k hkX hkY hkD
  by_cases h1 : k = T
  · rw [h1]; exact hT
  by_cases h2 : k = SA
  · rw [h2]; exact hSA
  by_cases h3 : k = SB
  · rw [h3]; exact hSB
  · exact hfr k hkX hkY h1 hkD h2 h3

/-! ## The two branches of the body of `Sk.pass` -/

/-- the `X`-empty branch of the body of `Sk.pass`: nothing to move -/
theorem ev_false_skip {main : Cmd} {X D T2 t d : Stk} {g : Reg → Glyph} {Y' : Stk → List Glyph}
    (h : (Y' X).headD Glyph.eos = Sk.gBnd) :
    ∃ s' : State, Ev main (.seq (.peek X Sk.rH)
        (.seq (.ite Sk.rH Glyph.cons (Sk.moveRun X D T2 t d) .skip) (.set Sk.rF gMark)))
      ⟨g, Y'⟩ s' 4 ∧ s'.stk = Y' ∧ s'.reg Sk.rF = gMark := by
  have h1 : Ev main (.peek X Sk.rH) ⟨g, Y'⟩ ⟨Function.update g Sk.rH Sk.gBnd, Y'⟩ 1 :=
    ev_peek_at h
  have h2 : Ev main (.ite Sk.rH Glyph.cons (Sk.moveRun X D T2 t d) .skip)
      ⟨Function.update g Sk.rH Sk.gBnd, Y'⟩ ⟨Function.update g Sk.rH Sk.gBnd, Y'⟩ 2 :=
    Ev.iteF (by simp only [reg_mk, Function.update_self]; exact gBnd_ne_cons) (ev_skip main _)
  have h3 : Ev main (.set Sk.rF gMark) ⟨Function.update g Sk.rH Sk.gBnd, Y'⟩
      ⟨Function.update (Function.update g Sk.rH Sk.gBnd) Sk.rF gMark, Y'⟩ 1 := ev_set_at
  exact ⟨_, (Ev.seq h1 (Ev.seq h2 h3)).mono (by omega), by simp, by simp only [reg_mk, Function.update_self]⟩

/-- the branch of the body of `Sk.pass` where the leftover run of `X` is moved to `D` -/
theorem ev_false_move {main : Cmd} {X D T2 t d : Stk} {g : Reg → Glyph} {Y' : Stk → List Glyph}
    {r : List Val} {rs : List (List Val)} {J JD : List Glyph} (hne : r ≠ [])
    (hcons : ∀ v ∈ r, ∃ a b : Val, v = Val.cons a b)
    (hX : Y' X = Sk.runEncB (r :: rs) ++ J) (hD : Y' D = JD)
    (hXD : X ≠ D) (hXT : X ≠ T2) (hXt : X ≠ t) (hXd : X ≠ d) (hDT : D ≠ T2) (hDt : D ≠ t)
    (hDd : D ≠ d) (hTt : T2 ≠ t) (hTd : T2 ≠ d) (htd : t ≠ d) :
    ∃ s' : State, Ev main (.seq (.peek X Sk.rH)
        (.seq (.ite Sk.rH Glyph.cons (Sk.moveRun X D T2 t d) .skip) (.set Sk.rF gMark)))
      ⟨g, Y'⟩ s' (6 + 50 * (runsz r + 1)) ∧
      s'.stk X = Sk.runEncB rs ++ J ∧ s'.stk D = encs r ++ gMark :: JD ∧
      (∀ k : Stk, k ≠ X → k ≠ D → s'.stk k = Y' k) ∧
      s'.reg Sk.rF = gMark := by
  have htop : (Y' X).headD Glyph.eos = Glyph.cons := by
    rw [hX]; exact headD_runEncB_cons hne hcons
  obtain ⟨s1, n1, hev1, hn1, hX1, hD1, hT2v, htv, hdv, hfr1⟩ :=
    moveRunEv (main := main) (S := X) (D := D) (T := T2) (t := t) (d := d) hXD hXT hXt hXd hDT
      hDt hDd hTt hTd htd hne hcons (hS := by rw [hX, runEncB_cons_append]) (hD := hD)
  have h1 : Ev main (.peek X Sk.rH) ⟨g, Y'⟩ ⟨Function.update g Sk.rH Glyph.cons, Y'⟩ 1 :=
    ev_peek_at htop
  have h2 : Ev main (.ite Sk.rH Glyph.cons (Sk.moveRun X D T2 t d) .skip)
      ⟨Function.update g Sk.rH Glyph.cons, Y'⟩ s1 (n1 + 1) :=
    Ev.iteT (by simp only [reg_mk, Function.update_self]) hev1
  have h3 : Ev main (.set Sk.rF gMark) s1 ⟨Function.update s1.reg Sk.rF gMark, s1.stk⟩ 1 :=
    ev_set_at
  refine ⟨_, (Ev.seq h1 (Ev.seq h2 h3)).mono ?_, ?_, ?_, ?_, ?_⟩
  · have hn1' : n1 ≤ 50 * (runsz r + 1) := hn1
    omega
  · exact hX1
  · exact hD1
  · intro k hkX hkD
    by_cases h1 : k = T2
    · rw [h1]; exact hT2v
    by_cases h2 : k = t
    · rw [h2]; exact htv
    by_cases h3 : k = d
    · rw [h3]; exact hdv
    · rw [hfr1 k hkX hkD h1 h2 h3]
  · simp only [reg_mk, Function.update_self]

/-- the `X`-empty post-loop move of `Sk.pass`: nothing to move -/
theorem ev_post_skip {main pLt pSz : Cmd} {X Y C D T1 T2 SA SB F1 F2 t d : Stk}
    {g : Reg → Glyph} {Y' : Stk → List Glyph} (h : (Y' X).headD Glyph.eos = Sk.gBnd) :
    ∃ s' : State, Ev main (passPostCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, Y'⟩ s' 4 ∧
      s'.stk = Y' := by
  have h1 : Ev main (.peek X Sk.rH) ⟨g, Y'⟩ ⟨Function.update g Sk.rH Sk.gBnd, Y'⟩ 1 :=
    ev_peek_at h
  have h2 : Ev main (.ite Sk.rH Glyph.cons (Sk.moveRun X C T1 t d) .skip)
      ⟨Function.update g Sk.rH Sk.gBnd, Y'⟩ ⟨Function.update g Sk.rH Sk.gBnd, Y'⟩ 2 :=
    Ev.iteF (by simp only [reg_mk, Function.update_self]; exact gBnd_ne_cons) (ev_skip main _)
  exact ⟨_, (Ev.seq h1 h2).mono (by omega), by simp⟩

/-- the post-loop move of `Sk.pass` when a leftover run is present on `X` -/
theorem ev_post_move {main pLt pSz : Cmd} {X Y C D T1 T2 SA SB F1 F2 t d : Stk}
    {g : Reg → Glyph} {Y' : Stk → List Glyph} {r : List Val} {rs : List (List Val)}
    {J JC : List Glyph} (hne : r ≠ []) (hcons : ∀ v ∈ r, ∃ a b : Val, v = Val.cons a b)
    (hX : Y' X = Sk.runEncB (r :: rs) ++ J) (hC : Y' C = JC)
    (hXC : X ≠ C) (hXT : X ≠ T1) (hXt : X ≠ t) (hXd : X ≠ d) (hCT : C ≠ T1) (hCt : C ≠ t)
    (hCd : C ≠ d) (hTt : T1 ≠ t) (hTd : T1 ≠ d) (htd : t ≠ d) :
    ∃ s' : State, Ev main (passPostCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, Y'⟩ s'
        (4 + 50 * (runsz r + 1)) ∧
      s'.stk X = Sk.runEncB rs ++ J ∧ s'.stk C = encs r ++ gMark :: JC ∧
      (∀ k : Stk, k ≠ X → k ≠ C → s'.stk k = Y' k) := by
  have htop : (Y' X).headD Glyph.eos = Glyph.cons := by
    rw [hX]; exact headD_runEncB_cons hne hcons
  obtain ⟨s1, n1, hev1, hn1, hX1, hC1, hT1v, htv, hdv, hfr1⟩ :=
    moveRunEv (main := main) (S := X) (D := C) (T := T1) (t := t) (d := d) hXC hXT hXt hXd hCT
      hCt hCd hTt hTd htd hne hcons (hS := by rw [hX, runEncB_cons_append]) (hD := hC)
  have h1 : Ev main (.peek X Sk.rH) ⟨g, Y'⟩ ⟨Function.update g Sk.rH Glyph.cons, Y'⟩ 1 :=
    ev_peek_at htop
  have h2 : Ev main (.ite Sk.rH Glyph.cons (Sk.moveRun X C T1 t d) .skip)
      ⟨Function.update g Sk.rH Glyph.cons, Y'⟩ s1 (n1 + 1) :=
    Ev.iteT (by simp only [reg_mk, Function.update_self]) hev1
  refine ⟨_, (Ev.seq h1 h2).mono ?_, ?_, ?_, ?_⟩
  · have hn1' : n1 ≤ 50 * (runsz r + 1) := hn1
    omega
  · exact hX1
  · exact hC1
  · intro k hkX hkC
    by_cases h1 : k = T1
    · rw [h1]; exact hT1v
    by_cases h2 : k = t
    · rw [h2]; exact htv
    by_cases h3 : k = d
    · rw [h3]; exact hdv
    · rw [hfr1 k hkX hkC h1 h2 h3]

/-! ## The main loop lemma -/

/-- the pairwise disequalities needed by the post-loop move in the `ps = [p, p', p'']` case -/
theorem hdis_ne_D {X Y C D T1 T2 SA SB F1 F2 t d : Stk}
    (hdis : ([X, Y, C, D, T1, T2, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    X ≠ C ∧ X ≠ T1 ∧ X ≠ t ∧ X ≠ d ∧ C ≠ T1 ∧ C ≠ t ∧ C ≠ d ∧ T1 ≠ t ∧ T1 ≠ d ∧
      t ≠ d ∧ Y ≠ X ∧ Y ≠ C ∧ D ≠ X ∧ D ≠ C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nodis


theorem passTail_ev {main pLt pSz : Cmd} {KLt KSz : ℕ}
    (hMP : Sk.MergePairAll main pLt pSz KLt KSz)
    {X Y C D T1 T2 SA SB F1 F2 t d : Stk}
    (hdis : ([X, Y, C, D, T1, T2, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    ∀ (k : ℕ) (ps qs ac ad : List (List Val)) (JX JY JC JD : List Glyph) (g : Reg → Glyph)
      (X' : Stk → List Glyph),
      (ps.length = qs.length ∨ ps.length = qs.length + 1) → qs ≠ [] →
      X' X = Sk.runEncB ps ++ JX → X' Y = Sk.runEncB qs ++ JY →
      X' C = Sk.runEncB ac ++ JC → X' D = Sk.runEncB ad ++ JD →
      RunsNe (ps ++ qs) → RunsRec (ps ++ qs) → RunsSort (ps ++ qs) → PairKeys ps qs →
      g Sk.rF = Glyph.cons → qs.length = k →
      ∃ (s₁ : State) (n₁ : ℕ) (s' : State) (n₂ : ℕ),
        Ev main (passLoopCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s₁ n₁ ∧
        Ev main (passPostCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) s₁ s' n₂ ∧
        n₁ + n₂ + 20 ≤ passW (Sk.MPc KLt KSz) ps qs ∧
        s'.stk X = Sk.runEncB ([] : List (List Val)) ++ JX ∧
        s'.stk Y = Sk.runEncB ([] : List (List Val)) ++ JY ∧
        s'.stk C = Sk.runEncB (Sk.passGo true ps qs ac ad).1 ++ JC ∧
        s'.stk D = Sk.runEncB (Sk.passGo true ps qs ac ad).2 ++ JD ∧
        (∀ k : Stk, k ≠ X → k ≠ Y → k ≠ C → k ≠ D → s'.stk k = X' k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ps qs ac ad JX JY JC JD g X' hlen hqs hX hY hC hD hNe hRec hSort hKeys hrf hk
    have hnd1 : ([X, Y, T1, C, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup := by
      have h := hdis
      simp only [List.nodup_cons, List.nodup_nil, and_true] at h ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nodis_mem
    have hnd2 : ([X, Y, T2, D, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup := by
      have h := hdis
      simp only [List.nodup_cons, List.nodup_nil, and_true] at h ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nodis_mem
    have hMP1 : Sk.MergePairSpec main pLt pSz X Y T1 C SA SB F1 F2 t d KLt KSz :=
      hMP X Y T1 C SA SB F1 F2 t d hnd1
    have hMP2 : Sk.MergePairSpec main pLt pSz X Y T2 D SA SB F1 F2 t d KLt KSz :=
      hMP X Y T2 D SA SB F1 F2 t d hnd2
    rcases qs with _ | ⟨q, qs1⟩
    · exact absurd rfl hqs
    rcases ps with _ | ⟨p, ps1⟩
    · rcases hlen with h | h <;> (simp only [List.length_nil, List.length_cons] at h) <;> omega
    have hp_ne : p ≠ [] := hNe p (by simp)
    have hq_ne : q ≠ [] := hNe q (by simp)
    have hp_rec : ∀ v ∈ p, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
      hRec p (by simp)
    have hq_rec : ∀ v ∈ q, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
      hRec q (by simp)
    have hp_sort : p.Pairwise (fun a b => pairKey a < pairKey b) := hSort p (by simp)
    have hq_sort : q.Pairwise (fun a b => pairKey a < pairKey b) := hSort q (by simp)
    have hpq_nd : ((p ++ q).map pairKey).Nodup := hKeys p (by simp) q (by simp)
    rcases qs1 with _ | ⟨q', qs2⟩
    · -- `qs = [q]`
      have hlen1 : ps1.length = 0 ∨ ps1.length = 1 := by
        rcases hlen with h | h
        · left; simp only [List.length_cons, List.length_nil] at h; omega
        · right; simp only [List.length_cons, List.length_nil] at h; omega
      have hXA : X' X = encs p ++ gMark :: (Sk.runEncB ps1 ++ JX) := by
        rw [hX, runEncB_cons_append]
      have hYA : X' Y = encs q ++ gMark :: (Sk.runEncB ([] : List (List Val)) ++ JY) := by
        rw [hY, runEncB_cons_append]
      obtain ⟨s1, n1, hev1, hn1, hX1, hY1, hT1v, hC1, hSA1, hSB1, hfr1⟩ :=
        hMP1 p q (Sk.runEncB ps1 ++ JX) (Sk.runEncB ([] : List (List Val)) ++ JY) (X' T1)
          (Sk.runEncB ac ++ JC)
          (X' SA) (X' SB) g X' hXA hYA rfl hC rfl rfl hp_ne hq_ne hp_rec hq_rec hp_sort hq_sort
          hpq_nd
      have hC1' : s1.stk C = Sk.runEncB (Sk.merge2 p q :: ac) ++ JC := by
        rw [hC1, runEncB_cons_append]
      have hDB : s1.stk D = X' D :=
        mergePair_frame (X := X) (Y := Y) (T := T1) (D := C) (SA := SA) (SB := SB)
          (X' := X') (s1 := s1) hfr1 hT1v hSA1 hSB1 D (by nodis) (by nodis) (by nodis)
      have hYtop1 : (s1.stk Y).headD Glyph.eos = Sk.gBnd := by rw [hY1]; rfl
      rcases ps1 with _ | ⟨p', ps2⟩
      · -- Case A : `ps = [p]`
        have hXtop1 : (s1.stk X).headD Glyph.eos = Sk.gBnd := by rw [hX1]; rfl
        have hgo : Sk.passGo true [p] [q] ac ad = (Sk.merge2 p q :: ac, ad) := by
          rw [passGo_true_cons, passGo_nil]
        obtain ⟨s2, hev2, hstk2, hreg2⟩ :=
          ev_false_skip (main := main) (X := X) (D := D) (T2 := T2) (t := t) (d := d)
            (g := Function.update s1.reg Sk.rH Sk.gBnd) (Y' := s1.stk) hXtop1
        have hevPeek : Ev main (.peek Y Sk.rH) s1
            ⟨Function.update s1.reg Sk.rH Sk.gBnd, s1.stk⟩ 1 :=
          ev_peek_at hYtop1
        have hevIte : Ev main (.ite Sk.rH Glyph.cons
              ((Sk.mergePair pLt pSz X Y T2 D SA SB F1 F2 t d).seq (Cmd.peek Y Sk.rF))
              ((Cmd.peek X Sk.rH).seq ((Cmd.ite Sk.rH Glyph.cons (Sk.moveRun X D T2 t d)
                Cmd.skip).seq (Cmd.set Sk.rF gMark))))
            ⟨Function.update s1.reg Sk.rH Sk.gBnd, s1.stk⟩ s2 (4 + 1) :=
          Ev.iteF (by simp only [reg_mk, Function.update_self]; exact gBnd_ne_cons) hev2
        have hevBody : Ev main (Sk.passBody pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s2
            (n1 + (1 + (4 + 1))) := by
          unfold Sk.passBody
          exact Ev.seq hev1 (Ev.seq hevPeek hevIte)
        have hreg2' : s2.reg Sk.rF ≠ Glyph.cons := by rw [hreg2]; exact gMark_ne_cons
        have hevLoop : Ev main (passLoopCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s2
            ((n1 + (1 + (4 + 1))) + 1 + 1) :=
          ev_loop_exit hrf hevBody hreg2'
        have hXtop2 : (s2.stk X).headD Glyph.eos = Sk.gBnd := by rw [hstk2, hX1]; rfl
        obtain ⟨s3, hev3, hstk3⟩ :=
          ev_post_skip (main := main) (pLt := pLt) (pSz := pSz) (X := X) (Y := Y) (C := C)
            (D := D) (T1 := T1) (T2 := T2) (SA := SA) (SB := SB) (F1 := F1) (F2 := F2) (t := t)
            (d := d) (g := s2.reg) (Y' := s2.stk) hXtop2
        refine ⟨s2, _, s3, _, hevLoop, hev3, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [passW_single_single]
          have h1 : n1 ≤ Sk.MPc KLt KSz * mergeCost p q := hn1
          nlinarith [h1]
        · rw [hstk3, hstk2]; exact hX1
        · rw [hstk3, hstk2]; exact hY1
        · rw [hstk3, hstk2, hgo, hC1']
        · rw [hstk3, hstk2, hgo]
          exact hDB.trans hD
        · intro j hjX hjY hjC hjD
          rw [hstk3, hstk2]
          exact mergePair_frame (X := X) (Y := Y) (T := T1) (D := C) (SA := SA) (SB := SB)
            (X' := X') (s1 := s1) hfr1 hT1v hSA1 hSB1 j hjX hjY hjC
      · -- Case B : `ps = [p, p']`
        have hps2 : ps2 = [] := by
          rcases hlen1 with h | h
          · simp only [List.length_cons, List.length_nil] at h; omega
          · exact List.eq_nil_of_length_eq_zero
              (by simp only [List.length_cons, List.length_nil] at h; omega)
        subst hps2
        have hpB_ne : p' ≠ [] := hNe p' (by simp)
        have hpB_rec : ∀ v ∈ p', ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
          hRec p' (by simp)
        have hX1b : s1.stk X = Sk.runEncB (p' :: []) ++ JX := hX1
        obtain ⟨s2, hev2, hX2, hD2, hfr2, hreg2⟩ :=
          ev_false_move (main := main) (X := X) (D := D) (T2 := T2) (t := t) (d := d)
            (g := Function.update s1.reg Sk.rH Sk.gBnd) (Y' := s1.stk) (r := p')
            (rs := ([] : List (List Val))) (J := JX) (JD := X' D)
            hpB_ne (consForm1 hpB_rec) hX1b hDB (by nodis) (by nodis) (by nodis) (by nodis) (by nodis)
            (by nodis) (by nodis) (by nodis) (by nodis) (by nodis)
        have hevPeek : Ev main (.peek Y Sk.rH) s1
            ⟨Function.update s1.reg Sk.rH Sk.gBnd, s1.stk⟩ 1 :=
          ev_peek_at hYtop1
        have hevIte : Ev main (.ite Sk.rH Glyph.cons
              ((Sk.mergePair pLt pSz X Y T2 D SA SB F1 F2 t d).seq (Cmd.peek Y Sk.rF))
              ((Cmd.peek X Sk.rH).seq ((Cmd.ite Sk.rH Glyph.cons (Sk.moveRun X D T2 t d)
                Cmd.skip).seq (Cmd.set Sk.rF gMark))))
            ⟨Function.update s1.reg Sk.rH Sk.gBnd, s1.stk⟩ s2
            (6 + 50 * (runsz p' + 1) + 1) :=
          Ev.iteF (by simp only [reg_mk, Function.update_self]; exact gBnd_ne_cons) hev2
        have hevBody : Ev main (Sk.passBody pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s2
            (n1 + (1 + (6 + 50 * (runsz p' + 1) + 1))) := by
          unfold Sk.passBody
          exact Ev.seq hev1 (Ev.seq hevPeek hevIte)
        have hreg2' : s2.reg Sk.rF ≠ Glyph.cons := by rw [hreg2]; exact gMark_ne_cons
        have hevLoop : Ev main (passLoopCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s2
            ((n1 + (1 + (6 + 50 * (runsz p' + 1) + 1))) + 1 + 1) :=
          ev_loop_exit hrf hevBody hreg2'
        have hXtop2 : (s2.stk X).headD Glyph.eos = Sk.gBnd := by rw [hX2]; rfl
        obtain ⟨s3, hev3, hstk3⟩ :=
          ev_post_skip (main := main) (pLt := pLt) (pSz := pSz) (X := X) (Y := Y) (C := C)
            (D := D) (T1 := T1) (T2 := T2) (SA := SA) (SB := SB) (F1 := F1) (F2 := F2) (t := t)
            (d := d) (g := s2.reg) (Y' := s2.stk) hXtop2
        have hgo : Sk.passGo true [p, p'] [q] ac ad = (Sk.merge2 p q :: ac, p' :: ad) := by
          rw [passGo_true_cons, passGo_false_nil]
        refine ⟨s2, _, s3, _, hevLoop, hev3, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [passW_two_single]
          have h1 : n1 ≤ Sk.MPc KLt KSz * mergeCost p q := hn1
          nlinarith [h1]
        · rw [hstk3, hX2]
        · rw [hstk3]; rw [hfr2 Y (by nodis) (by nodis)]; exact hY1
        · rw [hstk3, hgo, hfr2 C (by nodis) (by nodis), hC1']
        · rw [hstk3, hgo, hD2, runEncB_cons_append, hD]
        · intro j hjX hjY hjC hjD
          rw [hstk3]
          exact (hfr2 j hjX hjD).trans
            (mergePair_frame (X := X) (Y := Y) (T := T1) (D := C) (SA := SA) (SB := SB)
              (X' := X') (s1 := s1) hfr1 hT1v hSA1 hSB1 j hjX hjY hjC)
    · -- `qs` has length at least 2
      rcases ps1 with _ | ⟨p', ps2⟩
      · exfalso
        rcases hlen with h | h <;> (simp only [List.length_cons, List.length_nil] at h) <;> omega
      have hlen' : ps2.length = qs2.length ∨ ps2.length = qs2.length + 1 := by
        rcases hlen with h | h
        · left; simp only [List.length_cons] at h; omega
        · right; simp only [List.length_cons] at h; omega
      have hp'_ne : p' ≠ [] := hNe p' (by simp)
      have hq'_ne : q' ≠ [] := hNe q' (by simp)
      have hp'_rec : ∀ v ∈ p', ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
        hRec p' (by simp)
      have hq'_rec : ∀ v ∈ q', ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
        hRec q' (by simp)
      have hp'_sort : p'.Pairwise (fun a b => pairKey a < pairKey b) := hSort p' (by simp)
      have hq'_sort : q'.Pairwise (fun a b => pairKey a < pairKey b) := hSort q' (by simp)
      have hpq'_nd : ((p' ++ q').map pairKey).Nodup := hKeys p' (by simp) q' (by simp)
      have hXA : X' X = encs p ++ gMark :: (Sk.runEncB (p' :: ps2) ++ JX) := by
        rw [hX, runEncB_cons_append]
      have hYA : X' Y = encs q ++ gMark :: (Sk.runEncB (q' :: qs2) ++ JY) := by
        rw [hY, runEncB_cons_append]
      obtain ⟨s1, n1, hev1, hn1, hX1, hY1, hT1v, hC1, hSA1, hSB1, hfr1⟩ :=
        hMP1 p q (Sk.runEncB (p' :: ps2) ++ JX) (Sk.runEncB (q' :: qs2) ++ JY) (X' T1)
          (Sk.runEncB ac ++ JC) (X' SA) (X' SB) g X' hXA hYA rfl hC rfl rfl hp_ne hq_ne hp_rec
          hq_rec hp_sort hq_sort hpq_nd
      have hC1' : s1.stk C = Sk.runEncB (Sk.merge2 p q :: ac) ++ JC := by
        rw [hC1, runEncB_cons_append]
      have hD1b : s1.stk D = Sk.runEncB ad ++ JD :=
        (mergePair_frame (X := X) (Y := Y) (T := T1) (D := C) (SA := SA) (SB := SB)
          (X' := X') (s1 := s1) hfr1 hT1v hSA1 hSB1 D (by nodis) (by nodis)
          (by nodis)).trans hD
      have hYtop1 : (s1.stk Y).headD Glyph.eos = Glyph.cons := by
        rw [hY1]; exact headD_runEncB_cons hq'_ne (consForm1 hq'_rec)
      have hXA2 : s1.stk X = encs p' ++ gMark :: (Sk.runEncB ps2 ++ JX) := by
        rw [hX1, runEncB_cons_append]
      have hYA2 : s1.stk Y = encs q' ++ gMark :: (Sk.runEncB qs2 ++ JY) := by
        rw [hY1, runEncB_cons_append]
      obtain ⟨s2, n2, hev2, hn2, hX2, hY2, hT2v, hD2, hSA2, hSB2, hfr2⟩ :=
        hMP2 p' q' (Sk.runEncB ps2 ++ JX) (Sk.runEncB qs2 ++ JY) (s1.stk T2)
          (Sk.runEncB ad ++ JD) (s1.stk SA) (s1.stk SB)
          (Function.update s1.reg Sk.rH Glyph.cons) s1.stk hXA2 hYA2 rfl hD1b rfl rfl
          hp'_ne hq'_ne hp'_rec hq'_rec hp'_sort hq'_sort hpq'_nd
      have hD2' : s2.stk D = Sk.runEncB (Sk.merge2 p' q' :: ad) ++ JD := by
        rw [hD2, runEncB_cons_append]
      have hC2' : s2.stk C = Sk.runEncB (Sk.merge2 p q :: ac) ++ JC :=
        (hfr2 C (by nodis) (by nodis) (by nodis) (by nodis) (by nodis) (by nodis)).trans hC1'
      rcases qs2 with _ | ⟨q'', qs3⟩
      · -- `qs = [q, q']`
        have hYtop2 : (s2.stk Y).headD Glyph.eos = Sk.gBnd := by rw [hY2]; rfl
        have hevPeek : Ev main (.peek Y Sk.rH) s1
            ⟨Function.update s1.reg Sk.rH Glyph.cons, s1.stk⟩ 1 :=
          ev_peek_at hYtop1
        have hevTrue : Ev main (.seq (Sk.mergePair pLt pSz X Y T2 D SA SB F1 F2 t d)
            (.peek Y Sk.rF)) ⟨Function.update s1.reg Sk.rH Glyph.cons, s1.stk⟩
            ⟨Function.update s2.reg Sk.rF Sk.gBnd, s2.stk⟩ (n2 + 1) :=
          Ev.seq hev2 (ev_peek_at hYtop2)
        have hevIte : Ev main (.ite Sk.rH Glyph.cons
              ((Sk.mergePair pLt pSz X Y T2 D SA SB F1 F2 t d).seq (Cmd.peek Y Sk.rF))
              ((Cmd.peek X Sk.rH).seq ((Cmd.ite Sk.rH Glyph.cons (Sk.moveRun X D T2 t d)
                Cmd.skip).seq (Cmd.set Sk.rF gMark))))
            ⟨Function.update s1.reg Sk.rH Glyph.cons, s1.stk⟩
            ⟨Function.update s2.reg Sk.rF Sk.gBnd, s2.stk⟩ ((n2 + 1) + 1) :=
          Ev.iteT (by simp only [reg_mk, Function.update_self]) hevTrue
        have hevBody : Ev main (Sk.passBody pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩
            ⟨Function.update s2.reg Sk.rF Sk.gBnd, s2.stk⟩ (n1 + (1 + ((n2 + 1) + 1))) := by
          unfold Sk.passBody
          exact Ev.seq hev1 (Ev.seq hevPeek hevIte)
        have hreg2 : (Function.update s2.reg Sk.rF Sk.gBnd) Sk.rF ≠ Glyph.cons := by
          simp only [reg_mk, Function.update_self]; exact gBnd_ne_cons
        have hevLoop : Ev main (passLoopCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩
            ⟨Function.update s2.reg Sk.rF Sk.gBnd, s2.stk⟩ ((n1 + (1 + ((n2 + 1) + 1))) + 1 + 1) :=
          ev_loop_exit hrf hevBody hreg2
        rcases ps2 with _ | ⟨p'', ps3⟩
        · -- `ps = [p, p']`
          have hXtop3 : (s2.stk X).headD Glyph.eos = Sk.gBnd := by rw [hX2]; rfl
          obtain ⟨s3, hev3, hstk3⟩ :=
            ev_post_skip (main := main) (pLt := pLt) (pSz := pSz) (X := X) (Y := Y) (C := C)
              (D := D) (T1 := T1) (T2 := T2) (SA := SA) (SB := SB) (F1 := F1) (F2 := F2) (t := t)
              (d := d) (g := (Function.update s2.reg Sk.rF Sk.gBnd)) (Y' := s2.stk) hXtop3
          have hgo : Sk.passGo true [p, p'] [q, q'] ac ad
              = (Sk.merge2 p q :: ac, Sk.merge2 p' q' :: ad) := by
            rw [passGo_true_cons, passGo_false_cons, passGo_nil]
          refine ⟨_, _, s3, _, hevLoop, hev3, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [passW_two_two]
            have h1 : n1 ≤ Sk.MPc KLt KSz * mergeCost p q := hn1
            have h2 : n2 ≤ Sk.MPc KLt KSz * mergeCost p' q' := hn2
            nlinarith [h1, h2]
          · rw [hstk3, hX2]
          · rw [hstk3, hY2]
          · rw [hstk3, hC2', hgo]
          · rw [hstk3, hD2', hgo]
          · intro j hjX hjY hjC hjD
            rw [hstk3]
            exact (mergePair_frame (X := X) (Y := Y) (T := T2) (D := D) (SA := SA) (SB := SB)
                     hfr2 hT2v hSA2 hSB2 j hjX hjY hjD).trans
                  (mergePair_frame (X := X) (Y := Y) (T := T1) (D := C) (SA := SA) (SB := SB)
                     (X' := X') (s1 := s1) hfr1 hT1v hSA1 hSB1 j hjX hjY hjC)
        · -- `ps = [p, p', p'']`
          have hps3 : ps3 = [] := by
            rcases hlen' with h | h
            · simp only [List.length_cons, List.length_nil] at h; omega
            · exact List.eq_nil_of_length_eq_zero
                (by simp only [List.length_cons, List.length_nil] at h; omega)
          subst hps3
          have hp''_ne : p'' ≠ [] := hNe p'' (by simp)
          have hp''_rec : ∀ v ∈ p'', ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
            hRec p'' (by simp)
          have hX2b : s2.stk X = Sk.runEncB (p'' :: []) ++ JX := hX2
          obtain ⟨hXC, hXT1, hXt, hXd, hCT1, hCt, hCd, hT1t, hT1d, htd, hYX, hYC, hDX, hDC⟩ :=
            hdis_ne_D hdis
          obtain ⟨s3, hev3, hX3, hC3, hfr3⟩ :=
            ev_post_move (main := main) (pLt := pLt) (pSz := pSz) (X := X) (Y := Y) (C := C)
              (D := D) (T1 := T1) (T2 := T2) (SA := SA) (SB := SB) (F1 := F1) (F2 := F2)
              (t := t) (d := d) (g := Function.update s2.reg Sk.rF Sk.gBnd) (Y' := s2.stk)
              (r := p'') (rs := ([] : List (List Val))) (J := JX)
              (JC := Sk.runEncB (Sk.merge2 p q :: ac) ++ JC)
              hp''_ne (consForm1 hp''_rec) hX2b hC2' hXC hXT1 hXt hXd hCT1 hCt hCd hT1t hT1d htd
          have hgo : Sk.passGo true [p, p', p''] [q, q'] ac ad
              = (p'' :: Sk.merge2 p q :: ac, Sk.merge2 p' q' :: ad) := by
            rw [passGo_true_cons, passGo_false_cons, passGo_true_nil]
          have hC3' : s3.stk C = Sk.runEncB (p'' :: Sk.merge2 p q :: ac) ++ JC := by
            rw [hC3]; simp only [runEncB_cons_append]
          refine ⟨_, _, s3, _, hevLoop, hev3, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [passW_three_two]
            have h1 : n1 ≤ Sk.MPc KLt KSz * mergeCost p q := hn1
            have h2 : n2 ≤ Sk.MPc KLt KSz * mergeCost p' q' := hn2
            nlinarith [h1, h2]
          · rw [hX3]
          · rw [hfr3 Y hYX hYC, hY2]
          · rw [hC3', hgo]
          · rw [hfr3 D hDX hDC, hD2', hgo]
          · intro j hjX hjY hjC hjD
            rw [hfr3 j hjX hjC]
            exact (mergePair_frame (X := X) (Y := Y) (T := T2) (D := D) (SA := SA) (SB := SB)
                     hfr2 hT2v hSA2 hSB2 j hjX hjY hjD).trans
                  (mergePair_frame (X := X) (Y := Y) (T := T1) (D := C) (SA := SA) (SB := SB)
                     (X' := X') (s1 := s1) hfr1 hT1v hSA1 hSB1 j hjX hjY hjC)
      · -- the recursive case
        have hlt : (q'' :: qs3).length < k := by
          rw [← hk]
          simp only [List.length_cons] at hk ⊢
          omega
        have hqs2 : (q'' :: qs3) ≠ [] := by simp
        have hsub1 : (ps2 ++ (q'' :: qs3)) <+ ((p :: p' :: ps2) ++ (q :: q' :: q'' :: qs3)) :=
          sublist_tails2 p p' ps2 q q' q'' qs3
        have hNe3 : RunsNe (ps2 ++ (q'' :: qs3)) := hNe.sublist hsub1
        have hSort3 : RunsSort (ps2 ++ (q'' :: qs3)) := hSort.sublist hsub1
        have hRec3 : RunsRec (ps2 ++ (q'' :: qs3)) := hRec.sublist hsub1
        have hKeys3 : PairKeys ps2 (q'' :: qs3) :=
          hKeys.sublist (sublist_drop_two p p' ps2) (sublist_drop_two q q' (q'' :: qs3))
        have hq2_ne : q'' ≠ [] := hNe q'' (by simp)
        have hq2_rec : ∀ v ∈ q'', ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
          hRec q'' (by simp)
        have hYtop2 : (s2.stk Y).headD Glyph.eos = Glyph.cons := by
          rw [hY2, runEncB_cons_append]; exact headD_encs_cons_p2 hq2_ne (consForm1 hq2_rec)
        have hevPeek : Ev main (.peek Y Sk.rH) s1
            ⟨Function.update s1.reg Sk.rH Glyph.cons, s1.stk⟩ 1 :=
          ev_peek_at hYtop1
        have hevTrue : Ev main (.seq (Sk.mergePair pLt pSz X Y T2 D SA SB F1 F2 t d)
            (.peek Y Sk.rF)) ⟨Function.update s1.reg Sk.rH Glyph.cons, s1.stk⟩
            ⟨Function.update s2.reg Sk.rF Glyph.cons, s2.stk⟩ (n2 + 1) :=
          Ev.seq hev2 (ev_peek_at hYtop2)
        have hevIte : Ev main (.ite Sk.rH Glyph.cons
              ((Sk.mergePair pLt pSz X Y T2 D SA SB F1 F2 t d).seq (Cmd.peek Y Sk.rF))
              ((Cmd.peek X Sk.rH).seq ((Cmd.ite Sk.rH Glyph.cons (Sk.moveRun X D T2 t d)
                Cmd.skip).seq (Cmd.set Sk.rF gMark))))
            ⟨Function.update s1.reg Sk.rH Glyph.cons, s1.stk⟩
            ⟨Function.update s2.reg Sk.rF Glyph.cons, s2.stk⟩ ((n2 + 1) + 1) :=
          Ev.iteT (by simp only [reg_mk, Function.update_self]) hevTrue
        have hevBody : Ev main (Sk.passBody pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩
            ⟨Function.update s2.reg Sk.rF Glyph.cons, s2.stk⟩ (n1 + (1 + ((n2 + 1) + 1))) := by
          unfold Sk.passBody
          exact Ev.seq hev1 (Ev.seq hevPeek hevIte)
        have hrf2 : (Function.update s2.reg Sk.rF Glyph.cons) Sk.rF = Glyph.cons := by
          simp only [Function.update_self]
        obtain ⟨s₃, m₁, s', m₂, hevR, hevP, hcostR, hXr, hYr, hCr, hDr, hfrR⟩ :=
          ih (q'' :: qs3).length hlt ps2 (q'' :: qs3) (Sk.merge2 p q :: ac) (Sk.merge2 p' q' :: ad)
            JX JY JC JD (Function.update s2.reg Sk.rF Glyph.cons) s2.stk hlen' hqs2 hX2 hY2
            hC2' hD2' hNe3 hRec3 hSort3 hKeys3 hrf2 rfl
        have hevLoop : Ev main (passLoopCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s₃
            ((n1 + (1 + ((n2 + 1) + 1))) + m₁ + 1) :=
          Ev.loopT hrf hevBody hevR
        have hgo : Sk.passGo true (p :: p' :: ps2) (q :: q' :: q'' :: qs3) ac ad
            = Sk.passGo true ps2 (q'' :: qs3) (Sk.merge2 p q :: ac) (Sk.merge2 p' q' :: ad) := by
          rw [passGo_true_cons, passGo_false_cons]
        refine ⟨s₃, _, s', _, hevLoop, hevP, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hstep := passW_step (Sk.MPc KLt KSz) p p' ps2 q q' (q'' :: qs3)
          have h1 : n1 ≤ Sk.MPc KLt KSz * mergeCost p q := hn1
          have h2 : n2 ≤ Sk.MPc KLt KSz * mergeCost p' q' := hn2
          rw [hstep]
          nlinarith [h1, h2, hcostR]
        · rw [hXr]
        · rw [hYr]
        · rw [hCr, hgo]
        · rw [hDr, hgo]
        · intro j hjX hjY hjC hjD
          rw [hfrR j hjX hjY hjC hjD]
          exact (mergePair_frame (X := X) (Y := Y) (T := T2) (D := D) (SA := SA) (SB := SB)
                   hfr2 hT2v hSA2 hSB2 j hjX hjY hjD).trans
                (mergePair_frame (X := X) (Y := Y) (T := T1) (D := C) (SA := SA) (SB := SB)
                   (X' := X') (s1 := s1) hfr1 hT1v hSA1 hSB1 j hjX hjY hjC)

/-! ## `Sk.pass` -/

theorem pass_ev {main pLt pSz : Cmd} {KLt KSz : ℕ}
    (hMP : Sk.MergePairAll main pLt pSz KLt KSz)
    {X Y C D T1 T2 SA SB F1 F2 t d : Stk}
    (hdis : ([X, Y, C, D, T1, T2, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    ∀ (ps qs ac ad : List (List Val)) (JX JY JC JD : List Glyph) (g : Reg → Glyph)
      (X' : Stk → List Glyph),
      (ps.length = qs.length ∨ ps.length = qs.length + 1) →
      X' X = Sk.runEncB ps ++ JX → X' Y = Sk.runEncB qs ++ JY →
      X' C = Sk.runEncB ac ++ JC → X' D = Sk.runEncB ad ++ JD →
      RunsNe (ps ++ qs) → RunsRec (ps ++ qs) → RunsSort (ps ++ qs) → PairKeys ps qs →
      ∃ s' n, Ev main (Sk.pass pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s' n ∧
        n ≤ passW (Sk.MPc KLt KSz) ps qs ∧
        s'.stk X = Sk.runEncB ([] : List (List Val)) ++ JX ∧
        s'.stk Y = Sk.runEncB ([] : List (List Val)) ++ JY ∧
        s'.stk C = Sk.runEncB (Sk.passGo true ps qs ac ad).1 ++ JC ∧
        s'.stk D = Sk.runEncB (Sk.passGo true ps qs ac ad).2 ++ JD ∧
        (∀ k : Stk, k ≠ X → k ≠ Y → k ≠ C → k ≠ D → s'.stk k = X' k) := by
  intro ps qs ac ad JX JY JC JD g X' hlen hX hY hC hD hNe hRec hSort hKeys
  by_cases hqs : qs = []
  · subst hqs
    have hlen' : ps.length ≤ 1 := by
      rcases hlen with h | h <;> (simp only [List.length_nil] at h) <;> omega
    rcases ps with _ | ⟨p, ps1⟩
    · -- `ps = qs = []`
      have hYtop : (X' Y).headD Glyph.eos = Sk.gBnd := by rw [hY]; rfl
      have hXtop : (X' X).headD Glyph.eos = Sk.gBnd := by rw [hX]; rfl
      have h1 : Ev main (.peek Y Sk.rF) ⟨g, X'⟩ ⟨Function.update g Sk.rF Sk.gBnd, X'⟩ 1 :=
        ev_peek_at hYtop
      have hloop : Ev main (passLoopCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d)
          ⟨Function.update g Sk.rF Sk.gBnd, X'⟩ ⟨Function.update g Sk.rF Sk.gBnd, X'⟩ 1 :=
        Ev.loopF (by simp only [reg_mk, Function.update_self]; exact gBnd_ne_cons)
      obtain ⟨s', hev', hstk'⟩ :=
        ev_post_skip (main := main) (pLt := pLt) (pSz := pSz) (X := X) (Y := Y) (C := C)
          (D := D) (T1 := T1) (T2 := T2) (SA := SA) (SB := SB) (F1 := F1) (F2 := F2) (t := t)
          (d := d) (g := Function.update g Sk.rF Sk.gBnd) (Y' := X') hXtop
      have hevAll : Ev main (Sk.pass pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s'
          (1 + (1 + 4)) := by
        rw [pass_eq]
        exact Ev.seq h1 (Ev.seq hloop hev')
      have hgo : Sk.passGo true ([] : List (List Val)) ([] : List (List Val)) ac ad = (ac, ad) := by
        rw [passGo_nil]
      refine ⟨s', _, hevAll, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [passW_nil_nil]; omega
      · rw [hstk', hX]
      · rw [hstk', hY]
      · rw [hstk', hgo, hC]
      · rw [hstk', hgo, hD]
      · intro j hjX hjY hjC hjD
        rw [hstk']
    · rcases ps1 with _ | ⟨p', ps2⟩
      · -- `ps = [p]`
        have hp_ne : p ≠ [] := hNe p (by simp)
        have hp_rec : ∀ v ∈ p, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
          hRec p (by simp)
        have hYtop : (X' Y).headD Glyph.eos = Sk.gBnd := by rw [hY]; rfl
        have h1 : Ev main (.peek Y Sk.rF) ⟨g, X'⟩ ⟨Function.update g Sk.rF Sk.gBnd, X'⟩ 1 :=
          ev_peek_at hYtop
        have hloop : Ev main (passLoopCmd pLt pSz X Y C D T1 T2 SA SB F1 F2 t d)
            ⟨Function.update g Sk.rF Sk.gBnd, X'⟩ ⟨Function.update g Sk.rF Sk.gBnd, X'⟩ 1 :=
          Ev.loopF (by simp only [reg_mk, Function.update_self]; exact gBnd_ne_cons)
        obtain ⟨s', hev', hX', hC', hfr'⟩ :=
          ev_post_move (main := main) (pLt := pLt) (pSz := pSz) (X := X) (Y := Y) (C := C)
            (D := D) (T1 := T1) (T2 := T2) (SA := SA) (SB := SB) (F1 := F1) (F2 := F2) (t := t)
            (d := d) (g := Function.update g Sk.rF Sk.gBnd) (Y' := X') (r := p)
            (rs := ([] : List (List Val))) (J := JX) (JC := Sk.runEncB ac ++ JC)
            hp_ne (consForm1 hp_rec) hX hC (by nodis) (by nodis) (by nodis) (by nodis)
            (by nodis) (by nodis) (by nodis) (by nodis) (by nodis) (by nodis)
        have hevAll : Ev main (Sk.pass pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s'
            (1 + (1 + (4 + 50 * (runsz p + 1)))) := by
          rw [pass_eq]
          exact Ev.seq h1 (Ev.seq hloop hev')
        have hgo : Sk.passGo true [p] ([] : List (List Val)) ac ad = (p :: ac, ad) := by
          rw [passGo_true_nil]
        refine ⟨s', _, hevAll, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [passW_single_nil]; omega
        · rw [hX']
        · rw [hfr' Y (by nodis) (by nodis), hY]
        · rw [hC', hgo, ← runEncB_cons_append]
        · rw [hfr' D (by nodis) (by nodis), hD, hgo]
        · intro j hjX hjY hjC hjD
          rw [hfr' j hjX hjC]
      · exfalso
        have h := hlen'
        simp only [List.length_cons, List.length_nil] at h
        omega
  · -- `qs ≠ []`
    have hNe_qs : RunsNe qs := hNe.sublist (List.sublist_append_right ps qs)
    have hRec_qs : ∀ v ∈ qs.flatten, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' := by
      intro v hv
      obtain ⟨r, hr, hvr⟩ := List.mem_flatten.mp hv
      exact hRec r (List.mem_append_right ps hr) v hvr
    have hYtop : (X' Y).headD Glyph.eos = Glyph.cons := by
      rw [hY]; exact headD_runEncB_pos hNe_qs (flatConsForm hRec_qs) hqs
    have h1 : Ev main (.peek Y Sk.rF) ⟨g, X'⟩ ⟨Function.update g Sk.rF Glyph.cons, X'⟩ 1 :=
      ev_peek_at hYtop
    obtain ⟨s₁, n₁, s', n₂, hev₁, hev₂, hcost, hXr, hYr, hCr, hDr, hfr⟩ :=
      passTail_ev hMP hdis qs.length ps qs ac ad JX JY JC JD
        (Function.update g Sk.rF Glyph.cons) X' hlen hqs hX hY hC hD hNe hRec hSort hKeys
        (Function.update_self _ _ _) rfl
    have hevAll : Ev main (Sk.pass pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, X'⟩ s'
        (1 + (n₁ + n₂)) := by
      rw [pass_eq]
      exact Ev.seq h1 (Ev.seq hev₁ hev₂)
    refine ⟨s', _, hevAll, ?_, hXr, hYr, hCr, hDr, hfr⟩
    · omega

end Work.Layout
