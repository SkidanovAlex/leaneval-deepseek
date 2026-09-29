import Mathlib
import Submission.Work.Layout.AA.ProgAux
import Submission.Work.Layout.AA.Defs
import Submission.Work.Layout.AA.moveTo_ev
import Submission.Work.Layout.AA.copyIntB1_loop
import Submission.Work.Layout.AA.decInt_ev

/-!
# `decInt` (no hypothesis on the content below the marker)

`Work.Layout.decInt a t rr rf rk rs rt` decrements the natural-number counter on top of stack `a`,
using `t` as scratch (with its boundary marker preserved).  This file proves the spec needed by the
`applyAlong` development: the only assumption about the scratch stack `t` is that its top is the
boundary marker `Glyph.mk 7`; *nothing* is assumed about the glyphs below it (the corresponding
`hD : gMark ∉ DB` hypothesis of `Work.Layout.AA.decInt_ev` is unused in that proof, since the block
moved back by `moveTo` is computed explicitly and is marker-free).

This is the statement of `Work.Layout.AA.decInt_ev2` from `ProgSpecs.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Layout.AA

open HvdH

theorem decInt_ev2 (main : HvdH.Cmd) (a t : HvdH.Stk) (rr rf rk rs rt : HvdH.Reg)
    (hat : a ≠ t) (h1 : rr ≠ rf) (h2 : rr ≠ rk) (h3 : rr ≠ rs) (h4 : rr ≠ rt) (h5 : rf ≠ rk)
    (h6 : rf ≠ rs) (h7 : rf ≠ rt) (h8 : rk ≠ rs) (h9 : rk ≠ rt) (h10 : rs ≠ rt)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (k : ℕ)
    (A DB : List HvdH.Glyph)
    (ha : X a = (HvdH.Val.int ((k + 1 : ℕ) : ℤ)).enc ++ A)
    (ht : X t = Work.Layout.gMark :: DB) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.decInt a t rr rf rk rs rt) ⟨g, X⟩ s' n ∧
      n ≤ 40 * (HvdH.isz (k + 1) + 1) ∧
      s'.stk a = (HvdH.Val.int (k : ℤ)).enc ++ A ∧ s'.stk t = Work.Layout.gMark :: DB ∧
      (∀ j, j ≠ a → j ≠ t → s'.stk j = X j) := by
  -- 1. the bits of `k+1`
  obtain ⟨tz, rest, hL, hrest, hsub⟩ := enc_decomp (k + 1) (by omega)
  have hk1 : (k + 1) - 1 = k := by omega
  have hT : List.replicate tz true ++ (if rest = [] then [] else false :: rest) =
      Computability.encodeNat k := by rw [← hsub, hk1]
  -- 2. length bookkeeping
  have hSz : tz + rest.length + 1 = (k + 1).size := by
    have hlen : (Computability.encodeNat (k + 1)).length = tz + 1 + rest.length := by
      rw [hL]
      simp only [List.length_append, List.length_replicate, List.length_cons]
      omega
    rw [Work.IntLib.encodeNat_length] at hlen
    omega
  have hisz : HvdH.isz ((k + 1 : ℕ) : ℤ) = (k + 1).size + 2 := by
    rw [HvdH.isz, Int.natAbs_natCast]
  -- 3. the encoding of `k+1` begins with the sign `pos`
  have ha' : X a = HvdH.Glyph.pos :: ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
      ++ HvdH.Glyph.iend :: A) := by
    rw [ha]
    exact enc_int_ofNat_append (k+1) A
  -- 4. the leading `pop a rs` (reads the sign) and the first `set rf cons`
  have hpop : Ev main (.pop a rs) ⟨g, X⟩
      ⟨Function.update g rs HvdH.Glyph.pos,
        Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
          ++ HvdH.Glyph.iend :: A)⟩ 1 := by
    have h := ev_pop' main a rs g X
    rw [ha', List.headD_cons, List.tail_cons] at h
    exact h
  have hset1 : Ev main (.set rf HvdH.Glyph.cons)
      ⟨Function.update g rs HvdH.Glyph.pos,
        Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
          ++ HvdH.Glyph.iend :: A)⟩
      ⟨Function.update (Function.update g rs HvdH.Glyph.pos) rf HvdH.Glyph.cons,
        Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
          ++ HvdH.Glyph.iend :: A)⟩ 1 :=
    ev_set' main rf HvdH.Glyph.cons _ _
  -- 5. phase 1
  obtain ⟨s2, n2, hloop1, hn2, hr2, ha2, ht2, hf2⟩ :=
    decB1_loopEv main a t rr rf rk hat tz rest
      (Function.update (Function.update g rs HvdH.Glyph.pos) rf HvdH.Glyph.cons)
      (Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
        ++ HvdH.Glyph.iend :: A))
      A (HvdH.Glyph.mk 7 :: DB)
      (by simp)
      (by rw [Function.update_self, hL])
      (by rw [Function.update_of_ne (Ne.symm hat)]; exact ht)
  have hset2 : Ev main (.set rf HvdH.Glyph.cons) s2
      ⟨Function.update s2.reg rf HvdH.Glyph.cons, s2.stk⟩ 1 :=
    ev_set' main rf HvdH.Glyph.cons s2.reg s2.stk
  -- 6. phase 2 (`decB2` is `copyIntB1`)
  have hdecB2 : Work.Layout.decB2 a t rr rf = Work.Layout.copyIntB1 a t rr rf := rfl
  obtain ⟨s4, hrun4, ha4, ht4, hf4, hr4⟩ :=
    copyIntB1_loop main hat rr rf (rest.map HvdH.Glyph.bit) A
      (Function.update s2.reg rf HvdH.Glyph.cons) s2.stk
      (by
        intro hmem
        obtain ⟨b, _, hb⟩ := List.mem_map.mp hmem
        cases b <;> exact absurd hb (by decide))
      (by simp)
      (by simpa using ha2)
  have hloop2ev : Ev main (.loop rf HvdH.Glyph.cons (Work.Layout.decB2 a t rr rf))
      ⟨Function.update s2.reg rf HvdH.Glyph.cons, s2.stk⟩ s4 (5 * (rest.length + 1) + 1) := by
    have h := loopRuns.eval hrun4 (by rw [hr4]; decide)
    rw [← hdecB2] at h
    simpa [List.length_map] using h
  -- 7. the gadget
  obtain ⟨s5, n5, hgadget, hn5, ht5, hf5⟩ :=
    decIte_gadget main t rr rt h4 tz rest s4.reg s4.stk (HvdH.Glyph.mk 7 :: DB) hrest (by
      rw [ht4, ht2, ← List.map_reverse]
      simp only [List.cons_append, List.append_assoc])
  obtain ⟨n5', hev5blk, hn5'⟩ := hgadget
  obtain ⟨sa, m1, m2, hev6, hev789, hm12⟩ := Eval.seq_inv hev5blk
  obtain ⟨sb, m3, m4, hev7, hev89, hm34⟩ := Eval.seq_inv hev789
  obtain ⟨sc, m5, m6, hev8, hev9, hm56⟩ := Eval.seq_inv hev89
  -- 8. `moveTo`
  set D : List HvdH.Glyph := HvdH.Glyph.iend ::
    (List.replicate tz true ++ (if rest = [] then [] else false :: rest)).reverse.map HvdH.Glyph.bit
    with hDdef
  have hDmem : HvdH.Glyph.mk 7 ∉ D := by
    rw [hDdef]
    intro hmem
    rcases List.mem_cons.mp hmem with hmem' | hmem'
    · exact absurd hmem' (by decide)
    · obtain ⟨b, _, hb⟩ := List.mem_map.mp hmem'
      cases b <;> exact absurd hb (by decide)
  have hDlen : D.length ≤ (k + 1).size + 1 := by
    rw [hDdef]
    have hTlen : (List.replicate tz true
        ++ (if rest = [] then [] else false :: rest)).length ≤ tz + rest.length + 1 := by
      by_cases hre : rest = []
      · subst hre
        simp
      · rw [if_neg hre]
        simp only [List.length_append, List.length_replicate, List.length_cons]
        omega
    simp only [List.length_cons, List.length_map, List.length_reverse]
    omega
  obtain ⟨s6, n6, hmove, hn6, ht6, ha6, hf6⟩ :=
    moveTo_ev main t a rr rf h1 (Ne.symm hat) s5.reg s5.stk D DB hDmem
      (by rw [hDdef]; exact ht5)
  -- 9. the register `rs` survives the body
  have hmid : Ev main (seqs [.set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB1 a t rr rf rk),
      .set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB2 a t rr rf),
      .pop t rt, .peek t rr,
      .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip,
      .push t rt,
      moveTo t a rr rf])
      ⟨Function.update g rs HvdH.Glyph.pos,
        Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
          ++ HvdH.Glyph.iend :: A)⟩ s6
      (40 * (HvdH.isz ((k+1:ℕ):ℤ) + 1)) := by
    have hprog : seqs [.set rf HvdH.Glyph.cons,
        .loop rf HvdH.Glyph.cons (decB1 a t rr rf rk),
        .set rf HvdH.Glyph.cons,
        .loop rf HvdH.Glyph.cons (decB2 a t rr rf),
        .pop t rt, .peek t rr,
        .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip,
        .push t rt,
        moveTo t a rr rf]
        = .seq (.set rf HvdH.Glyph.cons)
            (.seq (.loop rf HvdH.Glyph.cons (decB1 a t rr rf rk))
              (.seq (.set rf HvdH.Glyph.cons)
                (.seq (.loop rf HvdH.Glyph.cons (decB2 a t rr rf))
                  (.seq (.pop t rt)
                    (.seq (.peek t rr)
                      (.seq (.ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip)
                        (.seq (.push t rt) (moveTo t a rr rf)))))))) := rfl
    have hnat : Ev main (seqs [.set rf HvdH.Glyph.cons,
        .loop rf HvdH.Glyph.cons (decB1 a t rr rf rk),
        .set rf HvdH.Glyph.cons,
        .loop rf HvdH.Glyph.cons (decB2 a t rr rf),
        .pop t rt, .peek t rr,
        .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip,
        .push t rt,
        moveTo t a rr rf])
        ⟨Function.update g rs HvdH.Glyph.pos,
          Function.update X a ((Computability.encodeNat (k+1)).map HvdH.Glyph.bit
            ++ HvdH.Glyph.iend :: A)⟩ s6
        (1 + ((6*(tz+1)+1) + (1 + ((5*(rest.length+1)+1)
          + (m1 + (m3 + (m5 + (m6 + (6*D.length+8))))))))) := by
      rw [hprog]
      exact Ev.seq hset1 (Ev.seq (hloop1.mono hn2) (Ev.seq hset2 (Ev.seq hloop2ev
        (Ev.seq ⟨m1, hev6, le_rfl⟩ (Ev.seq ⟨m3, hev7, le_rfl⟩
          (Ev.seq ⟨m5, hev8, le_rfl⟩ (Ev.seq ⟨m6, hev9, le_rfl⟩
            (hmove.mono hn6))))))))
    exact hnat.mono (by omega)
  have hrs_notin : rs ∉ cmdRegs (seqs [.set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB1 a t rr rf rk),
      .set rf HvdH.Glyph.cons,
      .loop rf HvdH.Glyph.cons (decB2 a t rr rf),
      .pop t rt, .peek t rr,
      .ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip,
      .push t rt,
      moveTo t a rr rf]) := by
    rw [cmdRegs_body]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h3.symm, h6.symm, h8.symm, h10⟩
  have hrs6 : s6.reg rs = HvdH.Glyph.pos := by
    obtain ⟨nm, hevalm, _⟩ := hmid
    have hfr := eval_reg_frame hevalm hrs_notin
    simpa using hfr
  -- 10. the final `push a rs`
  have hpush : Ev main (.push a rs) s6
      ⟨s6.reg, Function.update s6.stk a (s6.reg rs :: s6.stk a)⟩ 1 :=
    ev_push' main a rs s6.reg s6.stk
  -- 11. the whole program
  have hwhole : Ev main (Work.Layout.decInt a t rr rf rk rs rt) ⟨g, X⟩
      ⟨s6.reg, Function.update s6.stk a (s6.reg rs :: s6.stk a)⟩
      (40 * (HvdH.isz ((k+1:ℕ):ℤ) + 1)) := by
    have hprog : Work.Layout.decInt a t rr rf rk rs rt
        = .seq (.pop a rs)
            (.seq (.set rf HvdH.Glyph.cons)
              (.seq (.loop rf HvdH.Glyph.cons (decB1 a t rr rf rk))
                (.seq (.set rf HvdH.Glyph.cons)
                  (.seq (.loop rf HvdH.Glyph.cons (decB2 a t rr rf))
                    (.seq (.pop t rt)
                      (.seq (.peek t rr)
                        (.seq (.ite rr (HvdH.Glyph.bit false) (seqs [.pop t rr]) .skip)
                          (.seq (.push t rt)
                            (.seq (moveTo t a rr rf) (.push a rs)))))))))) := rfl
    have hnat : Ev main (Work.Layout.decInt a t rr rf rk rs rt) ⟨g, X⟩
        ⟨s6.reg, Function.update s6.stk a (s6.reg rs :: s6.stk a)⟩
        (1 + (1 + ((6*(tz+1)+1) + (1 + ((5*(rest.length+1)+1)
          + (m1 + (m3 + (m5 + (m6 + ((6*D.length+8) + 1)))))))))) := by
      rw [hprog]
      exact Ev.seq hpop (Ev.seq hset1 (Ev.seq (hloop1.mono hn2) (Ev.seq hset2
        (Ev.seq hloop2ev (Ev.seq ⟨m1, hev6, le_rfl⟩ (Ev.seq ⟨m3, hev7, le_rfl⟩
          (Ev.seq ⟨m5, hev8, le_rfl⟩ (Ev.seq ⟨m6, hev9, le_rfl⟩
            (Ev.seq (hmove.mono hn6) hpush)))))))))
    exact hnat.mono (by omega)
  -- 12. conclusions
  have hDrev : D.reverse = (List.replicate tz true ++
      (if rest = [] then [] else false :: rest)).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] := by
    rw [hDdef, List.reverse_cons, ← List.map_reverse, List.reverse_reverse]
  have hs5a : s5.stk a = A := by rw [hf5 a hat, ha4]
  have hs6a : s6.stk a = D.reverse ++ A := by rw [ha6, hs5a]
  refine ⟨⟨s6.reg, Function.update s6.stk a (s6.reg rs :: s6.stk a)⟩,
    40 * (HvdH.isz ((k+1:ℕ):ℤ) + 1), hwhole, le_rfl, ?_, ?_, ?_⟩
  · rw [stk_mk, Function.update_self, hrs6, hs6a, hDrev, hT]
    simp [HvdH.Val.enc, List.cons_append, List.singleton_append, List.append_assoc]
  · rw [stk_mk, Function.update_of_ne (Ne.symm hat)]
    exact ht6
  · intro j hja hjt
    rw [stk_mk, Function.update_of_ne hja, hf6 j hjt hja, hf5 j hjt, hf4 j hja hjt,
      hf2 j hja hjt]
    exact Function.update_of_ne hja _ _

end Work.Layout.AA
