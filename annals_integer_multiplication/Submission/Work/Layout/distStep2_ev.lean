import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Layout

open Work.Layout.Sk HvdH

/-- `(ofList (x :: xs)).enc` exposes the leading `cons` glyph. -/
theorem ofList_enc_cons_ds (x : Val) (xs : List Val) :
    (ofList (x :: xs)).enc = Glyph.cons :: (x.enc ++ (ofList xs).enc) := by
  simp only [ofList, List.foldr_cons]
  rfl

/-- `runEnc` of a list of runs, split off the first run. -/
theorem runEnc_cons (r : List Val) (rs : List (List Val)) :
    runEnc (r :: rs) = encs r ++ gMark :: runEnc rs := by
  simp only [runEnc, List.map_cons, List.flatten_cons, List.append_assoc, List.singleton_append]

/-- `runEnc` of a single one-element run. -/
theorem runEnc_single (v : Val) (rs : List (List Val)) :
    runEnc ([v] :: rs) = v.enc ++ gMark :: runEnc rs := by
  rw [runEnc_cons]; simp [encs]

/-- One execution of `distBody X Y t d`: move the top two values of the `cons`-chain on stack 0
alternately to `X` and `Y`, each terminated by a run marker `gMark`, preserving everything else
(including the scratch stacks `t`, `d`). -/
theorem distStep2_ev {main : Cmd} {X Y t d : Stk}
    (hXY : X ≠ Y) (hXt : X ≠ t) (hXd : X ≠ d) (hYt : Y ≠ t) (hYd : Y ≠ d) (htd : t ≠ d)
    (hX0 : X ≠ 0) (hY0 : Y ≠ 0) (ht0 : t ≠ 0) (hd0 : d ≠ 0)
    {a b : Val} {rest : List Val} {ax ay : List (List Val)} {A J1 J2 : List Glyph}
    {g : Reg → Glyph} {S : Stk → List Glyph}
    (h0 : S 0 = (ofList (a :: b :: rest)).enc ++ A)
    (hX : S X = runEnc ax ++ gBnd :: J1) (hY : S Y = runEnc ay ++ gBnd :: J2) :
    ∃ s' n, Ev main (distBody X Y t d) ⟨g, S⟩ s' n ∧ n ≤ 20 * (vsz a + vsz b) + 50 ∧
      s'.stk 0 = (ofList rest).enc ++ A ∧
      s'.stk X = runEnc ([a] :: ax) ++ gBnd :: J1 ∧
      s'.stk Y = runEnc ([b] :: ay) ++ gBnd :: J2 ∧
      s'.stk t = S t ∧ s'.stk d = S d ∧
      s'.reg rH = ((ofList rest).enc ++ A).headD Glyph.eos ∧
      (∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s'.stk k = S k) := by
  have h0X : (0 : Stk) ≠ X := hX0.symm
  have h0Y : (0 : Stk) ≠ Y := hY0.symm
  have h0t : (0 : Stk) ≠ t := ht0.symm
  have h0d : (0 : Stk) ≠ d := hd0.symm
  have hS0 : S 0 = Glyph.cons :: (a.enc ++ ((ofList (b :: rest)).enc ++ A)) := by
    rw [h0, ofList_enc_cons_ds]; simp only [List.cons_append, List.append_assoc]
  have hA2 : (ofList (b :: rest)).enc ++ A
      = Glyph.cons :: (b.enc ++ ((ofList rest).enc ++ A)) := by
    rw [ofList_enc_cons_ds]; simp only [List.cons_append, List.append_assoc]
  have hgoalX : runEnc ([a] :: ax) ++ gBnd :: J1
      = a.enc ++ (gMark :: (runEnc ax ++ gBnd :: J1)) := by
    rw [runEnc_single]; simp only [List.append_assoc, List.cons_append]
  have hgoalY : runEnc ([b] :: ay) ++ gBnd :: J2
      = b.enc ++ (gMark :: (runEnc ay ++ gBnd :: J2)) := by
    rw [runEnc_single]; simp only [List.append_assoc, List.cons_append]
  -- ## Step 1: `pop 0 rI`
  obtain ⟨s1, n1, he1, hn1, h1_0, h1_X, h1_Y, h1_t, h1_d, h1_fr⟩ :
      ∃ s1 n1, Ev main (.pop 0 rI) ⟨g, S⟩ s1 n1 ∧ n1 ≤ 1 ∧
        s1.stk 0 = a.enc ++ ((ofList (b :: rest)).enc ++ A) ∧
        s1.stk X = S X ∧ s1.stk Y = S Y ∧ s1.stk t = S t ∧ s1.stk d = S d ∧
        (∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s1.stk k = S k) := by
    refine ⟨_, 1, ev_pop' main 0 rI g S, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Function.update_self, hS0, List.tail_cons]
    · simp only [Function.update_of_ne hX0]
    · simp only [Function.update_of_ne hY0]
    · simp only [Function.update_of_ne ht0]
    · simp only [Function.update_of_ne hd0]
    · intro k hk _ _ _ _
      simp only [Function.update_of_ne hk]
  -- ## Step 2: `pushConst X gMark`
  obtain ⟨s2, n2, he2, hn2, h2_X, h2_fr, _, _⟩ :=
    pushConst_ev (main := main) (k := X) (cst := gMark) (g := s1.reg) (X := s1.stk)
  have h2_0 : s2.stk 0 = a.enc ++ ((ofList (b :: rest)).enc ++ A) := by
    rw [h2_fr 0 h0X]; exact h1_0
  have h2_X' : s2.stk X = gMark :: (runEnc ax ++ gBnd :: J1) := by
    rw [h2_X, h1_X, hX]
  have h2_Y : s2.stk Y = S Y := by rw [h2_fr Y hXY.symm, h1_Y]
  have h2_t : s2.stk t = S t := by rw [h2_fr t hXt.symm, h1_t]
  have h2_d : s2.stk d = S d := by rw [h2_fr d hXd.symm, h1_d]
  have h2_fr' : ∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s2.stk k = S k := by
    intro k hk0 hkX hkY hkt hkd
    rw [h2_fr k hkX]; exact h1_fr k hk0 hkX hkY hkt hkd
  -- ## Step 3: `mvVal 0 X t d`
  obtain ⟨s3, n3, he3, hn3, h3_0, h3_X, h3_t, h3_d, h3_fr⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := X) (c := t) (d := d)
      h0X h0t h0d hXt hXd htd (g := s2.reg) (X := s2.stk) (v := a)
      (A := (ofList (b :: rest)).enc ++ A) (B := gMark :: (runEnc ax ++ gBnd :: J1)) h2_0 h2_X'
  have h3_Y : s3.stk Y = S Y := by
    rw [h3_fr Y hY0 hXY.symm hYt hYd, h2_Y]
  have h3_t' : s3.stk t = S t := by rw [h3_t, h2_t]
  have h3_d' : s3.stk d = S d := by rw [h3_d, h2_d]
  have h3_fr' : ∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s3.stk k = S k := by
    intro k hk0 hkX hkY hkt hkd
    rw [h3_fr k hk0 hkX hkt hkd]; exact h2_fr' k hk0 hkX hkY hkt hkd
  -- ## Step 4: `peek 0 rH`
  have hpeek : (s3.stk 0).headD Glyph.eos = Glyph.cons := by rw [h3_0, hA2]; rfl
  obtain ⟨s4, n4, he4, hn4, h4_rH, h4_eq⟩ :
      ∃ s4 n4, Ev main (.peek 0 rH) s3 s4 n4 ∧ n4 ≤ 1 ∧
        s4.reg rH = Glyph.cons ∧ s4.stk = s3.stk := by
    refine ⟨_, 1, ev_peek' main 0 rH s3.reg s3.stk, le_rfl, ?_, rfl⟩
    simp only [Function.update_self]
    exact hpeek
  have h4_0 : s4.stk 0 = (ofList (b :: rest)).enc ++ A := by rw [h4_eq]; exact h3_0
  have h4_X : s4.stk X = a.enc ++ (gMark :: (runEnc ax ++ gBnd :: J1)) := by
    rw [h4_eq]; exact h3_X
  have h4_Y : s4.stk Y = S Y := by rw [h4_eq]; exact h3_Y
  have h4_t : s4.stk t = S t := by rw [h4_eq]; exact h3_t'
  have h4_d : s4.stk d = S d := by rw [h4_eq]; exact h3_d'
  have h4_fr : ∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s4.stk k = S k := by
    intro k hk0 hkX hkY hkt hkd; rw [h4_eq]; exact h3_fr' k hk0 hkX hkY hkt hkd
  -- ## Step 5: `pop 0 rI` (inside the `cons` branch)
  obtain ⟨s5, n5, he5, hn5, h5_0, h5_X, h5_Y, h5_t, h5_d, h5_fr⟩ :
      ∃ s5 n5, Ev main (.pop 0 rI) s4 s5 n5 ∧ n5 ≤ 1 ∧
        s5.stk 0 = b.enc ++ ((ofList rest).enc ++ A) ∧
        s5.stk X = a.enc ++ (gMark :: (runEnc ax ++ gBnd :: J1)) ∧
        s5.stk Y = S Y ∧ s5.stk t = S t ∧ s5.stk d = S d ∧
        (∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s5.stk k = S k) := by
    refine ⟨_, 1, ev_pop' main 0 rI s4.reg s4.stk, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Function.update_self, h4_0, hA2, List.tail_cons]
    · simp only [Function.update_of_ne hX0, h4_X]
    · simp only [Function.update_of_ne hY0, h4_Y]
    · simp only [Function.update_of_ne ht0, h4_t]
    · simp only [Function.update_of_ne hd0, h4_d]
    · intro k hk0 hkX hkY hkt hkd
      simp only [Function.update_of_ne hk0, h4_fr k hk0 hkX hkY hkt hkd]
  -- ## Step 6: `pushConst Y gMark`
  obtain ⟨s6, n6, he6, hn6, h6_Y, h6_fr, _, _⟩ :=
    pushConst_ev (main := main) (k := Y) (cst := gMark) (g := s5.reg) (X := s5.stk)
  have h6_0 : s6.stk 0 = b.enc ++ ((ofList rest).enc ++ A) := by
    rw [h6_fr 0 h0Y]; exact h5_0
  have h6_X : s6.stk X = a.enc ++ (gMark :: (runEnc ax ++ gBnd :: J1)) := by
    rw [h6_fr X hXY]; exact h5_X
  have h6_Y' : s6.stk Y = gMark :: (runEnc ay ++ gBnd :: J2) := by
    rw [h6_Y, h5_Y, hY]
  have h6_t : s6.stk t = S t := by rw [h6_fr t hYt.symm, h5_t]
  have h6_d : s6.stk d = S d := by rw [h6_fr d hYd.symm, h5_d]
  have h6_fr' : ∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s6.stk k = S k := by
    intro k hk0 hkX hkY hkt hkd
    rw [h6_fr k hkY]; exact h5_fr k hk0 hkX hkY hkt hkd
  -- ## Step 7: `mvVal 0 Y t d`
  obtain ⟨s7, n7, he7, hn7, h7_0, h7_Y, h7_t, h7_d, h7_fr⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := Y) (c := t) (d := d)
      h0Y h0t h0d hYt hYd htd (g := s6.reg) (X := s6.stk) (v := b)
      (A := (ofList rest).enc ++ A) (B := gMark :: (runEnc ay ++ gBnd :: J2)) h6_0 h6_Y'
  have h7_X : s7.stk X = a.enc ++ (gMark :: (runEnc ax ++ gBnd :: J1)) := by
    rw [h7_fr X hX0 hXY hXt hXd]; exact h6_X
  have h7_t' : s7.stk t = S t := by rw [h7_t, h6_t]
  have h7_d' : s7.stk d = S d := by rw [h7_d, h6_d]
  have h7_fr' : ∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s7.stk k = S k := by
    intro k hk0 hkX hkY hkt hkd
    rw [h7_fr k hk0 hkY hkt hkd]; exact h6_fr' k hk0 hkX hkY hkt hkd
  -- ## Step 8: `peek 0 rH`
  obtain ⟨sF, n8, he8, hn8, hF_rH, hF_eq⟩ :
      ∃ sF n8, Ev main (.peek 0 rH) s7 sF n8 ∧ n8 ≤ 1 ∧
        sF.reg rH = ((ofList rest).enc ++ A).headD Glyph.eos ∧ sF.stk = s7.stk := by
    refine ⟨_, 1, ev_peek' main 0 rH s7.reg s7.stk, le_rfl, ?_, rfl⟩
    simp only [Function.update_self, h7_0]
  have hF_0 : sF.stk 0 = (ofList rest).enc ++ A := by rw [hF_eq]; exact h7_0
  have hF_X : sF.stk X = a.enc ++ (gMark :: (runEnc ax ++ gBnd :: J1)) := by
    rw [hF_eq]; exact h7_X
  have hF_Y : sF.stk Y = b.enc ++ (gMark :: (runEnc ay ++ gBnd :: J2)) := by
    rw [hF_eq]; exact h7_Y
  have hF_t : sF.stk t = S t := by rw [hF_eq]; exact h7_t'
  have hF_d : sF.stk d = S d := by rw [hF_eq]; exact h7_d'
  have hF_fr : ∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → sF.stk k = S k := by
    intro k hk0 hkX hkY hkt hkd; rw [hF_eq]; exact h7_fr' k hk0 hkX hkY hkt hkd
  -- ## Assembly
  have hbr : Ev main (.seq (.pop 0 rI) (.seq (pushConst Y gMark) (.seq (mvVal 0 Y t d)
      (.peek 0 rH)))) s4 sF (n5 + (n6 + (n7 + n8))) :=
    Ev.seq he5 (Ev.seq he6 (Ev.seq he7 he8))
  have hite : Ev main (.ite rH Glyph.cons
      (.seq (.pop 0 rI) (.seq (pushConst Y gMark) (.seq (mvVal 0 Y t d) (.peek 0 rH))))
      (.set rH Glyph.nil)) s4 sF ((n5 + (n6 + (n7 + n8))) + 1) :=
    Ev.iteT h4_rH hbr
  have hmain : Ev main (distBody X Y t d) ⟨g, S⟩ sF
      (n1 + (n2 + (n3 + (n4 + ((n5 + (n6 + (n7 + n8))) + 1))))) := by
    simp only [distBody]
    exact Ev.seq he1 (Ev.seq he2 (Ev.seq he3 (Ev.seq he4 hite)))
  refine ⟨sF, n1 + (n2 + (n3 + (n4 + ((n5 + (n6 + (n7 + n8))) + 1)))), hmain, ?_,
    hF_0, ?_, ?_, hF_t, hF_d, hF_rH, hF_fr⟩
  · omega
  · rw [hF_X, ← hgoalX]
  · rw [hF_Y, ← hgoalY]

end Work.Layout
