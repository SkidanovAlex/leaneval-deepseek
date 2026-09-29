import Mathlib
import Submission.Work.Layout.Take.Basic
import Submission.Work.Layout.Take.cmpBody_go
import Submission.Work.Layout.Take.cmpBody_stop
import Submission.Work.Layout.Take.tzB_sum_le

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.Layout.Take

open HvdH
open Work.Layout

/-- Budget for one *working* iteration of `cmpBody` on the binary counter `k`: the body itself
costs at most `20 * (tzB k.bits + 2) + 10` (`Remark`: `20 * (tzB k.bits + 2)` for `decProg` plus
`8` primitive steps), plus one step for the loop test. -/
def cmpIt (k : ℕ) : ℕ := 20 * (tzB k.bits + 2) + 12

/-- The comparison loop of `cmpProg`: starting from a state whose binary counter on `sBit` is
`k` (`bitsG_x k.bits` above the frame) and whose unary counter `sD` holds `len` units, the loop
`loop rG gCont_x cmpBody` performs `min k len` *working* iterations (each one consuming a unit of
`sD`, decrementing the counter and pushing the unit on `sDp`) followed by one *stopping* iteration
(which only sets `rG := eos`), so `min k len + 1` iterations in total.  The cost is bounded by
`∑_{i < min k len} cmpIt (k - i) + 10`, and the resulting state has counter `k - min k len`,
`len - min k len` units left on `sD` and `min k len` units on `sDp` above what was there. -/
theorem cmpLoop (main : HvdH.Cmd) (hdec : DecStep main) :
    ∀ (m k len : ℕ), min k len = m → ∀ (R Drest : List Glyph) (g : Reg → Glyph)
      (X : Stk → List Glyph),
      X sBit = bitsG_x k.bits ++ gMark :: R →
      X sD = List.replicate len gU ++ gMark :: Drest →
      g rG = gCont_x →
      ∃ s', loopRuns main rG gCont_x cmpBody (m + 1) ⟨g, X⟩ s'
          ((∑ i ∈ Finset.range m, cmpIt (k - i)) + 10) ∧
        s'.stk sBit = bitsG_x ((k - m).bits) ++ gMark :: R ∧
        s'.stk sD = List.replicate (len - m) gU ++ gMark :: Drest ∧
        s'.stk sDp = List.replicate m gU ++ X sDp ∧
        s'.reg rG = Glyph.eos ∧
        s'.stk sTmp = X sTmp ∧
        (∀ j, j ≠ sBit → j ≠ sD → j ≠ sDp → j ≠ sTmp → s'.stk j = X j) := by
  intro m
  induction m with
  | zero =>
      intro k len hmin R Drest g X hbit hD hg
      have hstop : k = 0 ∨ len = 0 := by
        rcases le_total k len with h | h
        · exact Or.inl (by rw [Nat.min_eq_left h] at hmin; exact hmin)
        · exact Or.inr (by rw [Nat.min_eq_right h] at hmin; exact hmin)
      obtain ⟨s', n', hev, hn', hreg, hall⟩ :=
        cmpBody_stop main k len hstop R Drest g X hbit hD
      refine ⟨s', loopRuns.mono le_rfl (loopRuns.one hg (hev.mono hn'))
          (by simp only [Finset.range_zero, Finset.sum_empty, Nat.zero_add]; omega),
        ?_, ?_, ?_, hreg, ?_, ?_⟩
      · rw [hall sBit, Nat.sub_zero]; exact hbit
      · rw [hall sD, Nat.sub_zero]; exact hD
      · rw [hall sDp]; simp
      · exact hall sTmp
      · intro j _ _ _ _; exact hall j
  | succ m ih =>
      intro k len hmin R Drest g X hbit hD hg
      have hk : 0 < k := by
        have h1 : min k len ≤ k := Nat.min_le_left k len
        omega
      have hl : 0 < len := by
        have h1 : min k len ≤ len := Nat.min_le_right k len
        omega
      have hmin' : min (k - 1) (len - 1) = m := by
        have h1 : min (k - 1) (len - 1) + 1 = min k len := by
          rcases le_total k len with h | h
          · rw [Nat.min_eq_left h, Nat.min_eq_left (by omega : k - 1 ≤ len - 1)]
            omega
          · rw [Nat.min_eq_right h, Nat.min_eq_right (by omega : len - 1 ≤ k - 1)]
            omega
        omega
      obtain ⟨s1, n1, hev1, hn1, hbit1, hD1, hDp1, hreg1, htmp1, hfr1⟩ :=
        cmpBody_go main hdec k len hk hl R Drest g X hbit hD
      obtain ⟨s2, hrun2, hbit2, hD2, hDp2, hreg2, htmp2, hfr2⟩ :=
        ih (k - 1) (len - 1) hmin' R Drest s1.reg s1.stk hbit1 hD1 hreg1
      have hrun1 : loopRuns main rG gCont_x cmpBody 1 ⟨g, X⟩ s1 (n1 + 1) := loopRuns.one hg hev1
      have hcat : loopRuns main rG gCont_x cmpBody (1 + (m + 1)) ⟨g, X⟩ s2
          ((n1 + 1) + ((∑ i ∈ Finset.range m, cmpIt ((k - 1) - i)) + 10)) :=
        loopRuns.concat (m + 1) hrun1 hrun2
      have hsum_shift : (∑ i ∈ Finset.range m, cmpIt (k - (i + 1)))
          = (∑ i ∈ Finset.range m, cmpIt ((k - 1) - i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hik : i + 1 ≤ k := by
          have h1 : min k len ≤ k := Nat.min_le_left k len
          have := Finset.mem_range.mp hi
          omega
        rw [show k - (i + 1) = (k - 1) - i by omega]
      have hsum_succ : (∑ i ∈ Finset.range (m + 1), cmpIt (k - i))
          = cmpIt k + (∑ i ∈ Finset.range m, cmpIt ((k - 1) - i)) := by
        rw [Finset.sum_range_succ', hsum_shift, Nat.sub_zero]
        exact Nat.add_comm _ _
      have hcost : (n1 + 1) + ((∑ i ∈ Finset.range m, cmpIt ((k - 1) - i)) + 10)
          ≤ (∑ i ∈ Finset.range (m + 1), cmpIt (k - i)) + 10 := by
        rw [hsum_succ]
        have h1 : cmpIt k = 20 * (tzB k.bits + 2) + 12 := rfl
        omega
      refine ⟨s2, loopRuns.mono (by omega) (loopRuns.cast (by omega) hcat) hcost,
        ?_, ?_, ?_, hreg2, ?_, ?_⟩
      · rw [hbit2, show (k - 1) - m = k - (m + 1) by omega]
      · rw [hD2, show (len - 1) - m = len - (m + 1) by omega]
      · rw [hDp2, hDp1, List.replicate_succ']
        simp [List.append_assoc]
      · rw [htmp2, htmp1]
      · intro j hj1 hj2 hj3 hj4
        rw [hfr2 j hj1 hj2 hj3 hj4, hfr1 j hj1 hj2 hj3 hj4]

/-- `cmpProg` (`Submission/Work/Layout/Take/Defs.lean`) consumes units of the unary counter `sD`
(decrementing the binary counter on `sBit` once per unit, via `decProg`, whose specification is the
hypothesis `hdec : Work.Layout.DecStep main`) until either `sBit` is empty (the counter is `0`) or
`sD` is exhausted.  It stops after `min k len` decrements, moving exactly those units to `sDp`; the
frame markers are never consumed (the loop tests with `peek`).  Here `X sBit = bitsG_x k.bits ++
gMark :: R` holds the bits of `k` least significant first above its marker, and `X sD` holds `len`
unary units above its marker. -/
theorem cmp_ev (main : HvdH.Cmd) (hdec : Work.Layout.DecStep main) (k len : ℕ)
    (R Drest : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (hbit : X Work.Layout.sBit = Work.Layout.bitsG_x k.bits ++ Work.Layout.gMark :: R)
    (hD : X Work.Layout.sD = List.replicate len Work.Layout.gU ++ Work.Layout.gMark :: Drest) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.cmpProg ⟨g, X⟩ s' n ∧
      n ≤ 200 * (len + k.size + 1) ∧
      s'.stk Work.Layout.sBit = Work.Layout.bitsG_x ((k - min k len).bits) ++ Work.Layout.gMark :: R ∧
      s'.stk Work.Layout.sD = List.replicate (len - min k len) Work.Layout.gU ++ Work.Layout.gMark :: Drest ∧
      s'.stk Work.Layout.sDp = List.replicate (min k len) Work.Layout.gU ++ X Work.Layout.sDp ∧
      (∀ j, j ≠ Work.Layout.sBit → j ≠ Work.Layout.sD → j ≠ Work.Layout.sDp → s'.stk j = X j) := by
  obtain ⟨s1, hrun, hbit1, hD1, hDp1, hreg1, htmp1, hfr1⟩ :=
    cmpLoop main hdec (min k len) k len rfl R Drest (Function.update g rG gCont_x) X hbit hD
      (by simp)
  have hset : Ev main (.set rG gCont_x) ⟨g, X⟩ ⟨Function.update g rG gCont_x, X⟩ 1 :=
    ev_set' main rG gCont_x g X
  have hc : s1.reg rG ≠ gCont_x := by
    rw [hreg1]; exact fun h => gCont_ne_eos h.symm
  have hloop : Ev main (.loop rG gCont_x cmpBody) ⟨Function.update g rG gCont_x, X⟩ s1
      ((∑ i ∈ Finset.range (min k len), cmpIt (k - i)) + 10 + 1) :=
    loopRuns.eval hrun hc
  have hmain : Ev main cmpProg ⟨g, X⟩ s1
      (1 + ((∑ i ∈ Finset.range (min k len), cmpIt (k - i)) + 10 + 1)) := by
    unfold cmpProg
    simp only [seqs]
    exact Ev.seq' hset hloop le_rfl
  refine ⟨s1, _, hmain, ?_, hbit1, hD1, hDp1, ?_⟩
  · have hmle : min k len ≤ len := Nat.min_le_right k len
    have hkle : min k len ≤ k := Nat.min_le_left k len
    have hsum := tzB_sum_le (min k len) k hkle
    have hsz : (k - min k len).size ≤ k.size := Nat.size_le_size (Nat.sub_le k (min k len))
    have hsplit : (∑ i ∈ Finset.range (min k len), cmpIt (k - i))
        = 20 * (∑ i ∈ Finset.range (min k len), (tzB ((k - i).bits) + 2))
          + (min k len) * 12 := by
      simp only [cmpIt, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, smul_eq_mul, Nat.mul_comm]
    have hinner : (∑ i ∈ Finset.range (min k len), (tzB ((k - i).bits) + 2))
        ≤ (min k len + (k - min k len).size) + 2 * (min k len) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
      have h2 : (min k len) * 2 = 2 * (min k len) := Nat.mul_comm _ _
      omega
    omega
  · intro j hj1 hj2 hj3
    by_cases h4 : j = sTmp
    · rw [h4]; exact htmp1
    · exact hfr1 j hj1 hj2 hj3 h4

end Work.Layout.Take
