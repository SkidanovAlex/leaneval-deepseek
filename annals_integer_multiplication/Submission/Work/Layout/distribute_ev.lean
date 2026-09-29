import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.distStep2_ev

/-!
# Layout area: `distribute`, the alternating split of a `cons`-chain

`distribute X Y t d` walks the `cons`-chain `ofList xs` on stack 0 and moves its elements alternately
to `X` and `Y`, each followed by a run marker `gMark`; the result is that `X` holds the run encoding
of `altSplit xs`'s first component and `Y` that of the second, above their previous contents.

The proof splits into

* `distAux_step1_ev` and `Work.Layout.distStep2_ev` (separate module): one iteration of the loop body
  `distBody` when one, resp. at least two, elements remain;
* `distAux_loop`: the loop invariant, by strong induction on the length of the remaining chain (one
  iteration consumes one or two elements);
* the assembly `distribute_ev`.
-/

namespace Work.Layout

open Work.Layout.Sk HvdH

variable {main : Cmd}

theorem distAux_ofList_enc_cons_ds (a : Val) (rest : List Val) :
    (ofList (a :: rest)).enc = Glyph.cons :: (a.enc ++ (ofList rest).enc) := by
  simp [ofList, Val.enc]

theorem distAux_headD_ofList_cons (a : Val) (rest : List Val) (A : List Glyph) :
    ((ofList (a :: rest)).enc ++ A).headD Glyph.eos = Glyph.cons := by
  rw [distAux_ofList_enc_cons_ds]; rfl

theorem distAux_headD_ofList_nil (A : List Glyph) :
    ((ofList ([] : List Val)).enc ++ A).headD Glyph.eos = Glyph.nil := by
  simp [ofList, Val.enc]

theorem distAux_runEnc_cons (r : List Val) (rs : List (List Val)) :
    runEnc (r :: rs) = encs r ++ (gMark :: runEnc rs) := by
  simp [runEnc, encs, List.flatten_cons, List.map_cons]

theorem distAux_vsz_ofList_cons (a : Val) (rest : List Val) :
    vsz (ofList (a :: rest)) = vsz a + vsz (ofList rest) + 1 := by
  simp [ofList, vsz, Val.enc]

/-- one element left -/
theorem distAux_step1_ev {X Y t d : Stk}
    (hXY : X ≠ Y) (hXt : X ≠ t) (hXd : X ≠ d) (hYt : Y ≠ t) (hYd : Y ≠ d) (htd : t ≠ d)
    (hX0 : X ≠ 0) (hY0 : Y ≠ 0) (ht0 : t ≠ 0) (hd0 : d ≠ 0)
    {a : Val} {ax ay : List (List Val)} {A J1 J2 : List Glyph}
    {g : Reg → Glyph} {S : Stk → List Glyph}
    (h0 : S 0 = (ofList [a]).enc ++ A)
    (hX : S X = runEnc ax ++ gBnd :: J1) (hY : S Y = runEnc ay ++ gBnd :: J2) :
    ∃ s' n, Ev main (distBody X Y t d) ⟨g, S⟩ s' n ∧ n ≤ 20 * vsz a + 30 ∧
      s'.stk 0 = Glyph.nil :: A ∧
      s'.stk X = runEnc ([a] :: ax) ++ gBnd :: J1 ∧
      s'.stk Y = runEnc ay ++ gBnd :: J2 ∧
      s'.stk t = S t ∧ s'.stk d = S d ∧
      s'.reg rH = Glyph.nil ∧
      (∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s'.stk k = S k) := by
  set g₁ : Reg → Glyph := Function.update g rI Glyph.cons with hg₁
  set S₁ : Stk → List Glyph := Function.update S 0 (a.enc ++ (Glyph.nil :: A)) with hS₁
  have hS0 : S 0 = Glyph.cons :: ((a.enc ++ [Glyph.nil]) ++ A) := by
    rw [h0]; simp [ofList, Val.enc]
  have hpop : Ev main (.pop 0 rI) ⟨g, S⟩ ⟨g₁, S₁⟩ 1 := by
    have h := ev_pop' main (0 : Stk) rI g S
    rw [hS0] at h
    rw [List.append_assoc] at h
    simpa [hg₁, hS₁] using h
  have hS₁0 : S₁ 0 = a.enc ++ (Glyph.nil :: A) := by rw [hS₁, Function.update_self]
  have hS₁X : S₁ X = S X := by rw [hS₁]; exact Function.update_of_ne hX0 _ _
  have hS₁Y : S₁ Y = S Y := by rw [hS₁]; exact Function.update_of_ne hY0 _ _
  have hS₁t : S₁ t = S t := by rw [hS₁]; exact Function.update_of_ne ht0 _ _
  have hS₁d : S₁ d = S d := by rw [hS₁]; exact Function.update_of_ne hd0 _ _
  obtain ⟨s2, n2, hpc, hn2, h2X, h2f, -, -⟩ :=
    pushConst_ev (main := main) (k := X) (cst := gMark) (g := g₁) (X := S₁)
  have h2X' : s2.stk X = gMark :: (runEnc ax ++ gBnd :: J1) := by rw [h2X, hS₁X, hX]
  obtain ⟨s3, n3, hmv, hn3, h30, h3X, h3t, h3d, h3f⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := X) (c := t) (d := d)
      (Ne.symm hX0) (Ne.symm ht0) (Ne.symm hd0) hXt hXd htd
      (g := s2.reg) (X := s2.stk) (v := a)
      (ha := (h2f 0 (Ne.symm hX0)).trans hS₁0) (hb := h2X')
  have hpeek : Ev main (.peek 0 rH) s3 ⟨Function.update s3.reg rH Glyph.nil, s3.stk⟩ 1 := by
    have h := ev_peek' main (0 : Stk) rH s3.reg s3.stk
    rw [h30] at h
    rw [List.headD_cons] at h
    exact h
  have hset : Ev main (.set rH Glyph.nil) ⟨Function.update s3.reg rH Glyph.nil, s3.stk⟩
      ⟨Function.update (Function.update s3.reg rH Glyph.nil) rH Glyph.nil, s3.stk⟩ 1 :=
    ev_set' main rH Glyph.nil _ _
  have hite : Ev main (.ite rH Glyph.cons
        (.seq (.pop 0 rI) (.seq (pushConst Y gMark) (.seq (mvVal 0 Y t d) (.peek 0 rH))))
        (.set rH Glyph.nil))
      ⟨Function.update s3.reg rH Glyph.nil, s3.stk⟩
      ⟨Function.update (Function.update s3.reg rH Glyph.nil) rH Glyph.nil, s3.stk⟩ 2 :=
    Ev.iteF (by show Function.update s3.reg rH Glyph.nil rH ≠ Glyph.cons
                rw [Function.update_self]; decide)
      (hset.mono (le_refl 1))
  have hpeek_ite : Ev main (.seq (.peek 0 rH) (.ite rH Glyph.cons
        (.seq (.pop 0 rI) (.seq (pushConst Y gMark) (.seq (mvVal 0 Y t d) (.peek 0 rH))))
        (.set rH Glyph.nil)))
      s3 ⟨Function.update (Function.update s3.reg rH Glyph.nil) rH Glyph.nil, s3.stk⟩ 3 :=
    Ev.seq' hpeek hite (le_refl 3)
  have hmv_rest : Ev main (.seq (mvVal 0 X t d) (.seq (.peek 0 rH) (.ite rH Glyph.cons
        (.seq (.pop 0 rI) (.seq (pushConst Y gMark) (.seq (mvVal 0 Y t d) (.peek 0 rH))))
        (.set rH Glyph.nil))))
      ⟨s2.reg, s2.stk⟩ ⟨Function.update (Function.update s3.reg rH Glyph.nil) rH Glyph.nil, s3.stk⟩
      (n3 + 3) := Ev.seq' hmv hpeek_ite (by omega)
  have hpc_rest : Ev main (.seq (pushConst X gMark) (.seq (mvVal 0 X t d)
        (.seq (.peek 0 rH) (.ite rH Glyph.cons
          (.seq (.pop 0 rI) (.seq (pushConst Y gMark) (.seq (mvVal 0 Y t d) (.peek 0 rH))))
          (.set rH Glyph.nil)))))
      ⟨g₁, S₁⟩ ⟨Function.update (Function.update s3.reg rH Glyph.nil) rH Glyph.nil, s3.stk⟩
      (2 + (n3 + 3)) := Ev.seq' hpc hmv_rest (by omega)
  have hbody : Ev main (distBody X Y t d) ⟨g, S⟩
      ⟨Function.update (Function.update s3.reg rH Glyph.nil) rH Glyph.nil, s3.stk⟩
      (1 + (2 + (n3 + 3))) := by
    unfold distBody
    exact Ev.seq' hpop hpc_rest (by omega)
  refine ⟨⟨Function.update (Function.update s3.reg rH Glyph.nil) rH Glyph.nil, s3.stk⟩,
    1 + (2 + (n3 + 3)), hbody, by omega, h30, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3X, distAux_runEnc_cons]
    simp [encs, List.append_assoc]
  · rw [h3f Y hY0 hXY.symm hYt hYd, h2f Y hXY.symm, hS₁Y, hY]
  · rw [h3t, h2f t hXt.symm, hS₁t]
  · rw [h3d, h2f d hXd.symm, hS₁d]
  · rfl
  · intro k hk0 hkX hkY hkt hkd
    rw [h3f k hk0 hkX hkt hkd, h2f k hkX, hS₁]
    exact Function.update_of_ne hk0 _ _

theorem distAux_vsz_ofList_nil : vsz (ofList ([] : List Val)) = 1 := rfl

/-- Cost arithmetic for the final assembly (kept out of the large context so that `omega` sees a
clean goal). -/
theorem distAux_cost_le (n1 v : ℕ) (h1 : n1 ≤ 30 * (v + 1) + 1) : 1 + (n1 + 1) ≤ 60 * (v + 1) := by
  omega

theorem distAux_runEncB_eq (rs : List (List Val)) (J : List Glyph) :
    runEncB rs ++ J = runEnc rs ++ (gBnd :: J) := by
  simp [runEncB, List.append_assoc]

/-- The `distribute` loop: complete invariant, by strong induction on the length of the remaining
`cons`-chain (one iteration consumes one or two elements). -/
theorem distAux_loop {main : Cmd} {X Y t d : Stk}
    (hXY : X ≠ Y) (hXt : X ≠ t) (hXd : X ≠ d) (hYt : Y ≠ t) (hYd : Y ≠ d) (htd : t ≠ d)
    (hX0 : X ≠ 0) (hY0 : Y ≠ 0) (ht0 : t ≠ 0) (hd0 : d ≠ 0) :
    ∀ (rest : List Val) (ax ay : List (List Val)) (g : Reg → Glyph) (S : Stk → List Glyph)
      (A J1 J2 : List Glyph),
      S 0 = (ofList rest).enc ++ A →
      S X = runEnc ax ++ gBnd :: J1 →
      S Y = runEnc ay ++ gBnd :: J2 →
      g rH = ((ofList rest).enc ++ A).headD Glyph.eos →
      ∃ s' m, Ev main (.loop rH Glyph.cons (distBody X Y t d)) ⟨g, S⟩ s' m ∧
        m ≤ 30 * (vsz (ofList rest) + 1) + 1 ∧
        s'.stk 0 = Glyph.nil :: A ∧
        s'.stk X = runEnc (altGo rest ax ay).1 ++ gBnd :: J1 ∧
        s'.stk Y = runEnc (altGo rest ax ay).2 ++ gBnd :: J2 ∧
        s'.stk t = S t ∧ s'.stk d = S d ∧
        s'.reg rH = Glyph.nil ∧
        (∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s'.stk k = S k) := by
  intro rest0
  have key : ∀ n, ∀ rest : List Val, rest.length ≤ n →
      ∀ (ax ay : List (List Val)) (g : Reg → Glyph) (S : Stk → List Glyph)
        (A J1 J2 : List Glyph),
        S 0 = (ofList rest).enc ++ A →
        S X = runEnc ax ++ gBnd :: J1 →
        S Y = runEnc ay ++ gBnd :: J2 →
        g rH = ((ofList rest).enc ++ A).headD Glyph.eos →
        ∃ s' m, Ev main (.loop rH Glyph.cons (distBody X Y t d)) ⟨g, S⟩ s' m ∧
          m ≤ 30 * (vsz (ofList rest) + 1) + 1 ∧
          s'.stk 0 = Glyph.nil :: A ∧
          s'.stk X = runEnc (altGo rest ax ay).1 ++ gBnd :: J1 ∧
          s'.stk Y = runEnc (altGo rest ax ay).2 ++ gBnd :: J2 ∧
          s'.stk t = S t ∧ s'.stk d = S d ∧
          s'.reg rH = Glyph.nil ∧
          (∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → k ≠ t → k ≠ d → s'.stk k = S k) := by
    intro n
    induction n with
    | zero =>
        intro rest hlen ax ay g S A J1 J2 h0 hX hY hreg
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hrest
        refine ⟨⟨g, S⟩, 1, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
        · exact Ev.loopF (by
            show g rH ≠ Glyph.cons
            rw [hreg, distAux_headD_ofList_nil]; decide)
        · simp [distAux_vsz_ofList_nil]
        · show S 0 = Glyph.nil :: A
          rw [h0]; rfl
        · exact hX
        · exact hY
        · show g rH = Glyph.nil
          rw [hreg]; exact distAux_headD_ofList_nil A
        · intro k _ _ _ _ _; rfl
    | succ n ih =>
        intro rest hlen ax ay g S A J1 J2 h0 hX hY hreg
        cases rest with
        | nil =>
            refine ⟨⟨g, S⟩, 1, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
            · exact Ev.loopF (by
                show g rH ≠ Glyph.cons
                rw [hreg, distAux_headD_ofList_nil]; decide)
            · simp [distAux_vsz_ofList_nil]
            · show S 0 = Glyph.nil :: A
              rw [h0]; rfl
            · exact hX
            · exact hY
            · show g rH = Glyph.nil
              rw [hreg]; exact distAux_headD_ofList_nil A
            · intro k _ _ _ _ _; rfl
        | cons a tl =>
            cases tl with
            | nil =>
                obtain ⟨s1, c1, hb, hc1, h10, h1X, h1Y, h1t, h1d, h1r, h1f⟩ :=
                  distAux_step1_ev (main := main) hXY hXt hXd hYt hYd htd hX0 hY0 ht0 hd0
                    (a := a) (ax := ax) (ay := ay) (A := A) (J1 := J1) (J2 := J2)
                    (g := g) (S := S) h0 hX hY
                have hr : g rH = Glyph.cons := by
                  rw [hreg]; exact distAux_headD_ofList_cons a [] A
                refine ⟨s1, c1 + 1 + 1, ?_, ?_, h10, ?_, ?_, h1t, h1d, h1r, h1f⟩
                · exact Ev.loopT hr hb (Ev.loopF (by rw [h1r]; decide))
                · have h1 : c1 ≤ 20 * vsz a + 30 := hc1
                  have hv : 1 ≤ vsz a := one_le_vsz a
                  have hvz : vsz (ofList ([a] : List Val)) = vsz a + 1 + 1 := by
                    rw [distAux_vsz_ofList_cons a [], distAux_vsz_ofList_nil]
                  rw [hvz]; omega
                · exact h1X
                · exact h1Y
            | cons b rest' =>
                obtain ⟨s1, c1, hb, hc1, h10, h1X, h1Y, h1t, h1d, h1r, h1f⟩ :=
                  distStep2_ev (main := main) hXY hXt hXd hYt hYd htd hX0 hY0 ht0 hd0
                    (a := a) (b := b) (rest := rest') (ax := ax) (ay := ay) (A := A)
                    (J1 := J1) (J2 := J2) (g := g) (S := S) h0 hX hY
                have hr : g rH = Glyph.cons := by
                  rw [hreg]; exact distAux_headD_ofList_cons a (b :: rest') A
                have hlen' : rest'.length ≤ n := by
                  simp only [List.length_cons] at hlen; omega
                obtain ⟨s2, c2, hloop2, hc2, h20, h2X, h2Y, h2t, h2d, h2r, h2f⟩ :=
                  ih rest' hlen' ([a] :: ax) ([b] :: ay) s1.reg s1.stk A J1 J2 h10 h1X h1Y h1r
                refine ⟨s2, c1 + c2 + 1, ?_, ?_, h20, ?_, ?_, ?_, ?_, h2r, ?_⟩
                · exact Ev.loopT hr hb hloop2
                · have h1 : c1 ≤ 20 * (vsz a + vsz b) + 50 := hc1
                  have h2 : c2 ≤ 30 * (vsz (ofList rest') + 1) + 1 := hc2
                  rw [distAux_vsz_ofList_cons a (b :: rest'), distAux_vsz_ofList_cons b rest']
                  omega
                · exact h2X
                · exact h2Y
                · rw [h2t, h1t]
                · rw [h2d, h1d]
                · intro k hk0 hkX hkY hkt hkd
                  rw [h2f k hk0 hkX hkY hkt hkd, h1f k hk0 hkX hkY hkt hkd]
  exact key rest0.length rest0 (le_refl _)

/-- `distribute X Y t d` walks the `cons`-chain `ofList xs` on stack 0, moving its elements alternately
(one to `X`, the next to `Y`) and terminating each with a `gMark`, so that at the end `X` holds
`runEncB (altSplit xs).1` and `Y` holds `runEncB (altSplit xs).2` above their existing contents.
(NOTE: the definition of `distBody` in SortDefs.lean now pushes the `gMark` *before* the element, so
that the marker ends up below it, matching `runEnc r = encs r ++ [gMark]`.) -/
theorem distribute_ev {main : Cmd} {X Y t d : Stk}
    (hXY : X ≠ Y) (hXt : X ≠ t) (hXd : X ≠ d) (hYt : Y ≠ t) (hYd : Y ≠ d) (htd : t ≠ d)
    (hX0 : X ≠ 0) (hY0 : Y ≠ 0) (ht0 : t ≠ 0) (hd0 : d ≠ 0)
    {g : Reg → Glyph} {S : Stk → List Glyph} {xs : List Val} {A J1 J2 : List Glyph}
    (h0 : S 0 = (ofList xs).enc ++ A)
    (hX : S X = runEncB ([] : List (List Val)) ++ J1)
    (hY : S Y = runEncB ([] : List (List Val)) ++ J2) :
    ∃ s' n, Ev main (distribute X Y t d) ⟨g, S⟩ s' n ∧ n ≤ 60 * (vsz (ofList xs) + 1) ∧
      s'.stk 0 = A ∧
      s'.stk X = runEncB (altSplit xs).1 ++ J1 ∧
      s'.stk Y = runEncB (altSplit xs).2 ++ J2 ∧
      (∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → s'.stk k = S k) := by
  have hX' : S X = runEnc ([] : List (List Val)) ++ gBnd :: J1 := by
    rw [hX]; rfl
  have hY' : S Y = runEnc ([] : List (List Val)) ++ gBnd :: J2 := by
    rw [hY]; rfl
  have hpeek : Ev main (.peek 0 rH) ⟨g, S⟩
      ⟨Function.update g rH (((ofList xs).enc ++ A).headD Glyph.eos), S⟩ 1 := by
    have h := ev_peek' main (0 : Stk) rH g S
    rw [h0] at h
    exact h
  obtain ⟨s1, n1, hloop, hn1, h10, h1X, h1Y, h1t, h1d, h1r, h1f⟩ :=
    distAux_loop (main := main) hXY hXt hXd hYt hYd htd hX0 hY0 ht0 hd0
      xs [] [] (Function.update g rH (((ofList xs).enc ++ A).headD Glyph.eos)) S A J1 J2
      h0 hX' hY' rfl
  have hpop : Ev main (.pop 0 rI) s1
      ⟨Function.update s1.reg rI Glyph.nil, Function.update s1.stk 0 A⟩ 1 := by
    have h := ev_pop' main (0 : Stk) rI s1.reg s1.stk
    rw [h10] at h
    rw [List.headD_cons] at h
    exact h
  have hloop_pop : Ev main (.seq (.loop rH Glyph.cons (distBody X Y t d)) (.pop 0 rI))
      ⟨Function.update g rH (((ofList xs).enc ++ A).headD Glyph.eos), S⟩
      ⟨Function.update s1.reg rI Glyph.nil, Function.update s1.stk 0 A⟩ (n1 + 1) :=
    Ev.seq' hloop hpop (le_refl (n1 + 1))
  have hmain : Ev main (distribute X Y t d) ⟨g, S⟩
      ⟨Function.update s1.reg rI Glyph.nil, Function.update s1.stk 0 A⟩
      (1 + (n1 + 1)) := by
    unfold distribute
    exact Ev.seq' hpeek hloop_pop (le_refl (1 + (n1 + 1)))
  refine ⟨⟨Function.update s1.reg rI Glyph.nil, Function.update s1.stk 0 A⟩,
    1 + (n1 + 1), hmain, ?_, ?_, ?_, ?_, ?_⟩
  · exact distAux_cost_le n1 (vsz (ofList xs)) hn1
  · show Function.update s1.stk 0 A 0 = A
    rw [Function.update_self]
  · show Function.update s1.stk 0 A X = runEncB (altSplit xs).1 ++ J1
    rw [Function.update_of_ne hX0, h1X, distAux_runEncB_eq]
    rfl
  · show Function.update s1.stk 0 A Y = runEncB (altSplit xs).2 ++ J2
    rw [Function.update_of_ne hY0, h1Y, distAux_runEncB_eq]
    rfl
  · intro k hk0 hkX hkY
    show Function.update s1.stk 0 A k = S k
    rw [Function.update_of_ne hk0]
    by_cases hkt : k = t
    · subst hkt; rw [h1t]
    · by_cases hkd : k = d
      · subst hkd; rw [h1d]
      · rw [h1f k hk0 hkX hkY hkt hkd]

end Work.Layout
