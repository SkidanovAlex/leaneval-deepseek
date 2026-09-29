import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paApplyDCost
import Submission.Work.Resample.paWords
import Submission.Work.Resample.paProofs1
import Submission.Work.Resample.axisIter_disc
import Submission.Work.Resample.mulNatWord
import Submission.Work.Main.word.conjDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-- **Second half of one axis step of the `Ã` program.**  As `Work.Resample.paApplyD`, but with the
hypothesis `Kb * p < N` (which the assembly can supply directly) instead of `Kb ≤ Kc` (which it
cannot, `Kc` being this lemma's own existential constant).  In `paApplyD`'s proof the hypothesis
`Kb ≤ Kc` is used only to derive `Kb * p < N`, so the `paApplyD` proof script goes through after
replacing that derivation by the new hypothesis.  (Alternatively re-prove the statement directly
from `PAMid … j Pj`: run `LayoutLib.applyAlong` with `rest := Pj`, `A := (ts.take j).prod`,
`m := ss.getD j 0`, `n := ts.getD j 0`, `B := (ss.drop (j+1)).prod`, then park the new array,
`WordP.clearRgn`, unpark, and multiply `A_j` by `t_j` with `Work.Resample.mulNatWord`.) -/
theorem paApplyE (KL : HvdH.KernelLib) (LL : HvdH.LayoutLib) (Kb : ℕ) (prep q : HvdH.Cmd) :
    ∃ (app : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ)
        (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
        (zs0 : List (ℤ × ℤ)) (Pj : List HvdH.Val),
      HvdH.ResParams p α ss ts → Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N → Kb * p < N →
      j < HvdH.D →
      Work.Resample.SliceSpecAtA Kb p α (ss.getD j 0) (ts.getD j 0) prep q (Φ j) Pj →
      Work.Resample.WordP main app
        (Work.Resample.PAMid Kb p α ss ts Φ zs0 j Pj)
        (fun vs rest a out b => Work.Resample.PAInv p α ss ts Φ zs0 (j + 1) out rest b)
        (fun _ _ _ => Kc * Work.Resample.PABr Kb Cm p α ss ts j) := by
  obtain ⟨comb, Kal, hAL⟩ := LL.applyAlong
  obtain ⟨parkP, Kp, hPark⟩ := paW2 1 (by decide)
  obtain ⟨unparkP, Ku, hUnpark⟩ := paW1 1 (by decide)
  obtain ⟨mv7P, Km7, hmv7⟩ := paW1 7 (by decide)
  obtain ⟨mv6P, Km6, hmv6⟩ := paW1 6 (by decide)
  obtain ⟨st6P, Km2, hstore6⟩ := paW2 6 (by decide)
  obtain ⟨mulP, Kmul, hmul⟩ := mulNatWord
  obtain ⟨Kc, hCost⟩ := paApplyD_cost Kal Kmul Kb Kp Ku Km7 Km6 Km2
  refine ⟨Cmd.seq (comb q) (Cmd.seq parkP (Cmd.seq
      (Cmd.seq (Cmd.set 15 Work.IntLib.Shift.gGo)
        (Cmd.loop 15 Work.IntLib.Shift.gGo (Work.IntLib.Shift.clearBody 0 paMark 14 15)))
      (Cmd.seq unparkP (Cmd.seq mv7P (Cmd.seq mv6P (Cmd.seq mulP st6P)))))), Kc, ?_⟩
  intro main N Cm p α ss ts j Φ zs0 Pj hRes hMon hMul hKN hKbpN hjD hSlice
  intro vs rest a hPre s R0 Bg h0 hk
  obtain ⟨arr, hPAVec, hvs, hPjsum, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpRest⟩ := hPre
  obtain ⟨harr, hlen0, hdisc0, hsz0⟩ := hPAVec
  obtain ⟨-, hQ, hΦdisc, -⟩ := hSlice
  -- ## basic facts
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hRes' : ResParams p α ss ts := ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩
  have hjss : j < ss.length := by rw [hsslen]; exact hjD
  have hjts : j < ts.length := by rw [htslen]; exact hjD
  obtain ⟨-, ht2, hs2, hB1, hAsBts⟩ := pbRA_dimFacts p α ss ts j hRes' hjD
  have hss_ge : ∀ i, i < ss.length → 2 ≤ ss.getD i 0 := fun i hi =>
    (hdim i (by rw [← hsslen]; exact hi)).1
  have hge : ∀ (l : List ℕ), (∀ i, i < l.length → 2 ≤ l.getD i 0) → ∀ x ∈ l, 1 ≤ x := by
    intro l hl x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have h2 := hl i hi
    rw [List.getD_eq_getElem l 0 hi, hix] at h2
    exact le_trans (by norm_num : 1 ≤ 2) h2
  have hBs1 : 1 ≤ (ss.drop (j + 1)).prod :=
    pbRnd_one_le_prod (fun x hx => hge ss hss_ge x (List.mem_of_mem_drop hx))
  have hA1 : 1 ≤ (ts.take j).prod :=
    pbRnd_one_le_prod (fun x hx =>
      pbRnd_one_le_ts p α ss ts hRes' x ((List.take_sublist j ts).subset hx))
  have htj1 : 1 ≤ ts.getD j 0 := le_trans (by norm_num : 1 ≤ 2) ht2
  -- `hKbpN : Kb * p < N` is now a hypothesis of the statement
  have hlenAx : (axisIter ss ts Φ j zs0).length =
      (ts.take j).prod * (ss.getD j 0) * (ss.drop (j + 1)).prod := by
    have h1 : (ss.drop j).prod = (ss.getD j 0) * (ss.drop (j + 1)).prod :=
      pbRnd_prod_drop_eq_prod ss hjss
    rw [hlen0, h1]; ring
  have hlen_es : (List.map HvdH.cfxVal (axisIter ss ts Φ j zs0)).length =
      (ts.take j).prod * (ss.getD j 0) * (ss.drop (j + 1)).prod := by
    rw [List.length_map, hlenAx]
  have hszEs : ∀ x ∈ List.map HvdH.cfxVal (axisIter ss ts Φ j zs0), vsz x ≤ 2 * p + 8 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact Work.Main.word.vsz_cfxVal_le (hdisc0 z hz)
  have hPin : ∀ σ < (ts.take j).prod * (ss.drop (j + 1)).prod,
      PAs p (ss.getD j 0)
        ((HvdH.slices (ts.take j).prod (ss.getD j 0) (ss.drop (j + 1)).prod
          (List.map HvdH.cfxVal (axisIter ss ts Φ j zs0))).getD σ []) := by
    intro σ hσ
    unfold PAs
    obtain ⟨h1, h2, h3⟩ := pa_slice_spec (p := p) hlenAx hdisc0 hσ
    exact ⟨_, h1, h2, h3⟩
  have hvs' : vs = Val.int (ts.take j).prod :: Val.int (ss.getD j 0) :: Val.int (ts.getD j 0) ::
      Val.int (ss.drop (j + 1)).prod ::
      ofList (List.map HvdH.cfxVal (axisIter ss ts Φ j zs0)) :: Pj := by
    rw [hvs, harr]; rfl
  have h0' : s.stk 0 = encs (Val.int (ts.take j).prod :: Val.int (ss.getD j 0) ::
      Val.int (ts.getD j 0) :: Val.int (ss.drop (j + 1)).prod ::
      ofList (List.map HvdH.cfxVal (axisIter ss ts Φ j zs0)) :: Pj) ++
      paMark :: (encs rest ++ R0) := by rw [h0, hvs']
  -- ## the slice word on every slice
  have hq : ∀ sl : List Val, sl.length = ss.getD j 0 → PAs p (ss.getD j 0) sl →
      HvdH.WordR main q (fun vsW => vsW = ofList sl :: Pj)
        (fun _ out => ∃ ol, out = ofList ol :: Pj ∧ ol.length = ts.getD j 0 ∧
          PAt p (ss.getD j 0) (ts.getD j 0) (Φ j) sl ol ∧ ∀ y ∈ ol, vsz y ≤ 2 * p + 8)
        (fun _ => Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) *
          (Cm (Kb * p) + p + 1)) := by
    intro sl hsl hPsl
    obtain ⟨u, hsl_eq, hu_len, hu_disc⟩ := hPsl
    intro vsW hvsW sW RW h0W
    obtain ⟨out, sW', n, hPost, hev, hc, h0'', hk''⟩ :=
      hQ main N Cm hMon hMul hKbpN (ofList (u.map HvdH.cfxVal) :: Pj ++ [])
        ⟨u, [], rfl, hu_len, hu_disc⟩ sW RW (by rw [h0W, hvsW, hsl_eq]; simp)
    obtain ⟨u', rest', w, hvsPost, hout, hw_len, hw_disc, hw_get⟩ := hPost
    have hrest : rest' = [] := by
      have h2 := hvsPost
      rw [List.cons_append, List.cons_append] at h2
      injection h2 with _ h2'
      exact List.append_cancel_left h2'.symm
    have hu' : u' = u := by
      have h2 := hvsPost
      rw [List.cons_append, List.cons_append] at h2
      injection h2 with h2'' _
      exact pa_map_cfxVal_inj (pa_ofList_inj h2''.symm)
    refine ⟨out, sW', n, ⟨w.map HvdH.cfxVal, ?_, ?_, ⟨u, w, hsl_eq, rfl, hw_len,
      fun k => by rw [hw_get k, hu']⟩, ?_⟩, hev, hc, h0'', hk''⟩
    · rw [hout, hrest]; simp only [HvdH.cvecVal, List.append_nil]
    · simp [List.length_map, hw_len]
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact Work.Main.word.vsz_cfxVal_le (hw_disc z hz)
  -- ## phase 1: `comb q`
  obtain ⟨out4, s4, n4, hP4, hev4, hc4, h04, hk4⟩ :=
    hAL main q Pj (ss.getD j 0) (ts.getD j 0) (PAs p (ss.getD j 0))
      (PAt p (ss.getD j 0) (ts.getD j 0) (Φ j))
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))
      (2 * p + 8) (by intro sl hsl hPsl; exact hq sl hsl hPsl)
      (ts.take j).prod (ss.drop (j + 1)).prod
      (List.map HvdH.cfxVal (axisIter ss ts Φ j zs0)) hlen_es hszEs hPin
      (Val.int (ts.take j).prod :: Val.int (ss.getD j 0) :: Val.int (ts.getD j 0) ::
        Val.int (ss.drop (j + 1)).prod ::
        ofList (List.map HvdH.cfxVal (axisIter ss ts Φ j zs0)) :: Pj)
      rfl s (paMark :: (encs rest ++ R0)) h0'
  obtain ⟨outs, hout4, houts_len, houts_facts⟩ := hP4
  have hk4' : ∀ k : Stk, k ≠ 0 → s4.stk k = encs (a k) ++ Bg k := by
    intro k hk0; rw [hk4 k hk0]; exact hk k hk0
  -- ## the new array
  set newarr : Val := ofList (HvdH.unslices (ts.take j).prod (ts.getD j 0)
    (ss.drop (j + 1)).prod outs) with hnewarr
  have hnew4 : out4 = newarr :: Pj := by rw [hout4, hnewarr]
  have he : ∀ σ < (ts.take j).prod * (ss.drop (j + 1)).prod, ∃ w : List (ℤ × ℤ),
      outs.getD σ [] = w.map HvdH.cfxVal ∧ w.length = ts.getD j 0 ∧
      ∀ k : Fin (ts.getD j 0), w.getD (k : ℕ) (0, 0) = (Φ j) (fun jj : Fin (ss.getD j 0) =>
        ((HvdH.slices (ts.take j).prod (ss.getD j 0) (ss.drop (j + 1)).prod
          (axisIter ss ts Φ j zs0)).getD σ []).getD (jj : ℕ) (0, 0)) k := by
    intro σ hσ
    obtain ⟨-, hAt⟩ := houts_facts σ hσ
    obtain ⟨u, w, hsl_eq, hol_eq, hw_len, hw_get⟩ := hAt
    have hu : u = (HvdH.slices (ts.take j).prod (ss.getD j 0) (ss.drop (j + 1)).prod
        (axisIter ss ts Φ j zs0)).getD σ [] := by
      refine pa_map_cfxVal_inj ?_
      rw [← hsl_eq]
      exact paGlueA (ts.take j).prod (ss.getD j 0) (ss.drop (j + 1)).prod
        (axisIter ss ts Φ j zs0) hlenAx hσ
    refine ⟨w, hol_eq, hw_len, fun k => ?_⟩
    rw [hw_get k, hu]
  have huns : HvdH.unslices (ts.take j).prod (ts.getD j 0) (ss.drop (j + 1)).prod outs =
      (axisList (ts.take j).prod (ss.getD j 0) (ts.getD j 0) (ss.drop (j + 1)).prod
        (Φ j) (axisIter ss ts Φ j zs0)).map HvdH.cfxVal :=
    paGlueD (ts.take j).prod (ss.getD j 0) (ts.getD j 0) (ss.drop (j + 1)).prod
      (lt_of_lt_of_le (by norm_num : 0 < 2) hs2) (lt_of_lt_of_le (by norm_num : 0 < 2) ht2) hBs1
      (Φ j) (axisIter ss ts Φ j zs0) hlenAx outs houts_len he
  have hnew : newarr = cvecVal (axisIter ss ts Φ (j + 1) zs0) := by
    rw [hnewarr, huns, ← pa_axisIter_succ ss ts Φ j zs0]
    rfl
  have hlenAx2 : (axisIter ss ts Φ (j + 1) zs0).length =
      (ts.take (j + 1)).prod * (ss.drop (j + 1)).prod := by
    rw [pa_axisIter_succ ss ts Φ j zs0, axisList_length_axisIter_length, pbRnd_prod_take_succ ts hjts]
  have hdiscAx2 : ∀ z ∈ axisIter ss ts Φ (j + 1) zs0, inDisc p z := by
    rw [pa_axisIter_succ ss ts Φ j zs0]
    exact paGlueE p (ts.take j).prod (ss.getD j 0) (ts.getD j 0) (ss.drop (j + 1)).prod
      (Φ j) (axisIter ss ts Φ j zs0) hdisc0 hΦdisc
  have hszNew : vsz newarr ≤ ts.prod * (2 * p + 8) + ts.prod + 1 := by
    rw [hnew]
    exact pa_vsz_axis_le hRes' (Nat.succ_le_of_lt hjD) hlenAx2 hdiscAx2
  -- ## phase 2: park the new array on stack 1
  obtain ⟨out5, a5, s5, n5, ⟨hout5, e5⟩, hev5, hc5, h05, hk5⟩ :=
    hPark main newarr Pj [] out4 a ⟨hnew4, hp1⟩ s4 (paMark :: (encs rest ++ R0)) Bg h04 hk4'
  -- ## phase 3: clear the region above the marker
  obtain ⟨out6, b6, s6, n6, ⟨hout6, eb6⟩, hev6, hc6, h06, hk6⟩ :=
    WordP.clearRgn main 14 15 Pj rest a5 trivial s5 R0 Bg (by rw [h05, hout5]) hk5
  have hk6' : ∀ k : Stk, k ≠ 0 → s6.stk k = encs (a5 k) ++ Bg k := by
    intro k hk0; rw [hk6 k hk0, eb6]
  -- ## phase 4: unpark the new array
  obtain ⟨out7, a7, s7, n7, ⟨hout7, e7⟩, hev7, hc7, h07, hk7⟩ :=
    hUnpark main newarr [] [] a5 ⟨rfl, by rw [e5, Function.update_self]⟩ s6
      (paMark :: (encs rest ++ R0)) Bg (by rw [h06, hout6]) hk6'
  -- ## phase 5: stack 7 → stack 0
  obtain ⟨out8, a8, s8, n8, ⟨hout8, e8⟩, hev8, hc8, h08, hk8⟩ :=
    hmv7 main (Val.int ((ts.getD j 0 : ℕ) : ℤ)) out7 out7 a7
      ⟨rfl, by rw [e7, Function.update_of_ne (by decide : (7 : Stk) ≠ 1), e5,
        Function.update_of_ne (by decide : (7 : Stk) ≠ 1), hp7]⟩
      s7 (paMark :: (encs rest ++ R0)) Bg h07 hk7
  -- ## phase 6: stack 6 → stack 0
  obtain ⟨out9, a9, s9, n9, ⟨hout9, e9⟩, hev9, hc9, h09, hk9⟩ :=
    hmv6 main (Val.int (((ts.take j).prod : ℕ) : ℤ)) out8 out8 a8
      ⟨rfl, by rw [e8, Function.update_of_ne (by decide : (6 : Stk) ≠ 7), e7,
        Function.update_of_ne (by decide : (6 : Stk) ≠ 1), e5,
        Function.update_of_ne (by decide : (6 : Stk) ≠ 1), hp6]⟩
      s8 (paMark :: (encs rest ++ R0)) Bg h08 hk8
  -- ## phase 7: multiply the two running values
  obtain ⟨out10, s10, n10, hP10, hev10, hc10, h010, hk10⟩ :=
    hmul main ((ts.take j).prod) (ts.getD j 0) hA1 htj1 (newarr :: []) out9
      (by rw [hout9, hout8, hout7]) s9 (paMark :: (encs rest ++ R0)) h09
  have hk10' : ∀ k : Stk, k ≠ 0 → s10.stk k = encs (a9 k) ++ Bg k := by
    intro k hk0; rw [hk10 k hk0]; exact hk9 k hk0
  -- ## phase 8: store the product on stack 6
  obtain ⟨out11, a11, s11, n11, ⟨hout11, e11⟩, hev11, hc11, h011, hk11⟩ :=
    hstore6 main (Val.int ((((ts.take j).prod) * (ts.getD j 0) : ℕ) : ℤ)) (newarr :: []) []
      out10 a9 ⟨hP10, by rw [e9, Function.update_self]⟩
      s10 (paMark :: (encs rest ++ R0)) Bg h010 hk10'
  -- ## the final invariant
  have hnw : vsz newarr + 1 ≤ ts.prod * (2 * p + 8) + ts.prod + 2 :=
    Nat.add_le_add_right hszNew 1
  have hnewlast : (ts.take (j + 1)).prod = (ts.take j).prod * ts.getD j 0 :=
    pbRnd_prod_take_succ ts hjts
  have hA11 : a11 1 = [] := by
    rw [e11, Function.update_of_ne (by decide : (1 : Stk) ≠ 6), e9,
      Function.update_of_ne (by decide : (1 : Stk) ≠ 6), e8,
      Function.update_of_ne (by decide : (1 : Stk) ≠ 7), e7, Function.update_self]
  have hA11gen : ∀ k : Stk, k ≠ 1 → k ≠ 6 → k ≠ 7 → a11 k = a k := by
    intro k h1 h6 h7
    rw [e11, Function.update_of_ne h6, e9, Function.update_of_ne h6, e8,
      Function.update_of_ne h7, e7, Function.update_of_ne h1, e5, Function.update_of_ne h1]
  refine ⟨[newarr], a11, s11, n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + n11)))))), ?_, ?_, ?_,
    ?_, ?_⟩
  · -- the invariant `PAInv … (j+1)`
    refine ⟨newarr, ⟨hnew, hlenAx2, hdiscAx2, hszNew⟩, rfl, hA11, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA11gen 2 (by decide) (by decide) (by decide), hp2]
    · rw [hA11gen 3 (by decide) (by decide) (by decide), hp3]
    · rw [hA11gen 4 (by decide) (by decide) (by decide), hp4]
    · rw [hA11gen 5 (by decide) (by decide) (by decide), hp5]
    · rw [e11, Function.update_self, hnewlast]
    · intro k hk0 hkF
      rcases eq_or_ne k 1 with hk1e | hk1n
      · rw [hk1e]; exact hA11
      rcases eq_or_ne k 7 with hk7e | hk7n
      · rw [hk7e, e11, Function.update_of_ne (by decide : (7 : Stk) ≠ 6), e9,
          Function.update_of_ne (by decide : (7 : Stk) ≠ 6), e8, Function.update_self]
      have hk6n : k ≠ 6 := by
        intro h
        exact hkF (by rw [h]; decide)
      have hk7v : (k : ℕ) ≠ 7 := pa_val_ne_seven k hk7n
      have hmem : (k : ℕ) ∉ ({2, 3, 4, 5, 6, 7} : Finset ℕ) := by
        intro hmem
        have h56 : (k : ℕ) ∈ ({2, 3, 4, 5, 6} : Finset ℕ) ∨ (k : ℕ) = 7 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
          tauto
        rcases h56 with h | h
        · exact hkF h
        · exact hk7v h
      rw [hA11gen k hk1n hk6n hk7n, hpRest k hk0 hmem]
  · -- the run
    refine Eval.seq hev4 (Eval.seq hev5 (Eval.seq hev6 (Eval.seq hev7
      (Eval.seq hev8 (Eval.seq hev9 (Eval.seq hev10 hev11))))))
  · -- the cost bound
    have hbound : n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + n11)))))) ≤
        paAppCost Kal Kmul Kb Kp Ku Km7 Km6 Km2 Cm p α ss ts j Pj newarr := by
      unfold paAppCost
      dsimp only at hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11
      exact Nat.add_le_add hc4 (Nat.add_le_add hc5 (Nat.add_le_add hc6 (Nat.add_le_add hc7
        (Nat.add_le_add hc8 (Nat.add_le_add hc9 (Nat.add_le_add hc10 hc11))))))
    exact le_trans hbound (hCost Cm p α ss ts j Pj newarr hRes' hjD hnw hPjsum)
  · -- the marker prefix
    rw [h011, hout11]
  · -- the other stacks
    exact hk11


end Work.Resample
