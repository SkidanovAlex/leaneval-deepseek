import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paWords
import Submission.Work.Resample.paProofs1
import Submission.Work.Resample.pbW6f
import Submission.Work.Resample.paBasic
import Submission.Work.Compiler.stack_len_le
import Submission.Work.Resample.pbRndDefs
import Submission.Work.Resample.pbRAdim
import Submission.Work.Resample.paTabSz
import Submission.Work.Resample.paPABrFacts
import Submission.Work.Resample.paProdWordCost

/-!
# Preamble of one axis step of the `Ã` program (`Work.Resample.paStageE`)

As `Submission/Work/Resample/paStageD.lean`, but with the hypothesis `Kb * p < N` (which the assembly
can supply directly) in place of `Kb ≤ Kc` (which it cannot, `Kc` being this lemma's own existential
constant).  In `paStageD`'s proof the hypothesis `Kb ≤ Kc` is used only to derive `Kb * p < N`, so the
proof below is `paStageD`'s with that single derivation replaced by the new hypothesis.

The helper declarations are named `paE…` so that they do not clash with the `paStageD` ones.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-- `SliceSpecAtA 0 …` is contradictory: the cost bound `0` of the preparation word is smaller
than the smallest possible `Eval` cost. -/
theorem paEKb0False {Kb : ℕ} (hKb0 : Kb = 0) {p α s t : ℕ} {prep q : Cmd}
    {Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)} {Pj : List Val}
    (h : SliceSpecAtA Kb p α s t prep q Φ Pj)
    (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ) (hmon : Monotone Cm) (hmb : MulBelow main N Cm)
    (hN : Kb * p < N) : False := by
  obtain ⟨hprep, -, -, -⟩ := h
  obtain ⟨out, s', n, -, hev, hc, -⟩ :=
    hprep main N Cm hmon hmb hN [Val.int p, Val.int α, Val.int s, Val.int t] ⟨[], rfl⟩
      ⟨fun _ => Glyph.eos, fun k => if k = 0 then encs [Val.int p, Val.int α, Val.int s, Val.int t]
        else []⟩ [] (by simp)
  have hpos : 1 ≤ n := paEvalPos hev
  rw [hKb0] at hc
  simp at hc
  omega

/-! ## The cost of the preamble -/

/-- The cost constant of the preamble: the sum of the per-phase constants, plus `Kb`. -/
def paEStageKc (K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f
    Kb : ℕ) : ℕ :=
  K1 + (3 * K5a + (K7 + (3 * K5b + (K11 + (Kpv + (7 * K6 * (D + 1) + (Kn10 + (Kc4a + (Kc4b +
    (Kc4c + (Kc4d + (1 + (Ku1 + (Kb10 + (Kc4e + (Kb11 + (Kc4f + Kb)))))))))))))))))

/-- The aggregate cost bound of the eighteen phases of the preamble, in their order of execution. -/
def paEStageCost (K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f
    Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) (arr : Val) : ℕ :=
  K1 * (vsz arr + 1) + (K5a * (vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j +
    1)))) + vsz (Val.int (ts.getD j 0 : ℤ)) + 1) + (K7 * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) +
    (K5b * (vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) + vsz
    (Val.int (ss.getD j 0 : ℤ)) + 1) + (K11 * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) + (Kpv *
    (vsz (Val.int 1) + 1) + (K6 * ((ss.drop (j + 1)).length + 1) * ((((ss.drop (j + 1)).map (fun
    x : ℕ => isz (x : ℤ))).sum) + ((ss.drop (j + 1)).prod).size + 2) * (((ss.drop (j +
    1)).prod).size + 2) + (Kn10 * (vsz (Val.int ((ss.drop (j + 1)).prod)) + 1) + (Kc4a * (vsz
    (Val.int (ts.getD j 0 : ℤ)) + 1) + (Kc4b * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) + (Kc4c *
    (vsz (Val.int α) + 1) + (Kc4d * (vsz (Val.int p) + 1) + (1 * (Kb * (ts.getD j 0 + 1) * (p +
    1) ^ Kb) + (Ku1 * (vsz arr + 1) + (Kb10 * (vsz (Val.int ((ss.drop (j + 1)).prod)) + 1) +
    (Kc4e * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) + (Kb11 * (vsz (Val.int (ss.getD j 0 : ℤ)) +
    1) + (Kc4f * (vsz (Val.int ((ts.take j).prod)) + 1))))))))))))))))))

/-- The cost bound of the preamble. -/
theorem paEStageCostBd (K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11
    Kc4f Kb : ℕ) :
    ∀ (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) (arr : Val),
      ResParams p α ss ts → j < D →
      vsz arr ≤ ts.prod * (2 * p + 8) + ts.prod + 1 →
      paEStageCost K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f Kb
        Cm p α ss ts j arr ≤
        paEStageKc K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f Kb *
          PABr Kb Cm p α ss ts j := by
  intro Cm p α ss ts j arr hRes hjD harr
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hResC : ResParams p α ss ts := ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩
  have hD1 : 1 ≤ D := pbRndD_pos
  obtain ⟨b_arr, b_s, b_t, b_A, b_B, b_ssl, b_tsl, b_drop⟩ := paPABrFacts (Kb := Kb) (Cm := Cm)
    (p := p) (α := α) (ss := ss) (ts := ts) (j := j) hResC hjD
  have b_Dp : (D + 1) * (p + 2) ≤ PABr Kb Cm p α ss ts j := by unfold PABr; omega
  have b_isz1 : 4 ≤ PABr Kb Cm p α ss ts j := by unfold PABr; omega
  have vsc : vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) = vsz (Val.int (ts.getD j 0 : ℤ)) + vsz (intList (ts.drop (j + 1))) + 1 :=
    Work.ConvR.vsz_cons _ _
  have vsint : vsz (Val.int (ts.getD j 0 : ℤ)) = isz ((ts.getD j 0 : ℕ) : ℤ) := Work.ConvR.vsz_int _
  have vscs : vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) = vsz (Val.int (ss.getD j 0 : ℤ)) + vsz (intList (ss.drop (j + 1))) + 1 :=
    Work.ConvR.vsz_cons _ _
  have vsints : vsz (Val.int (ss.getD j 0 : ℤ)) = isz ((ss.getD j 0 : ℕ) : ℤ) := Work.ConvR.vsz_int _
  -- ## phase 1 / 14: park / unpark the array
  have hc1 : K1 * (vsz arr + 1) ≤ K1 * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left K1 ?_
    omega
  -- ## phase 2: peel `t_j` off stack 3
  have hc2 : K5a * (vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) + vsz (Val.int (ts.getD j 0 : ℤ)) + 1) ≤ 3 * K5a * PABr Kb Cm p α ss ts j := by
    have h3 : vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) + vsz (Val.int (ts.getD j 0 : ℤ)) + 1 ≤ 3 * PABr Kb Cm p α ss ts j := by
      rw [vsc, vsint]
      omega
    calc K5a * (vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) + vsz (Val.int (ts.getD j 0 : ℤ)) + 1) ≤ K5a * (3 * PABr Kb Cm p α ss ts j) := Nat.mul_le_mul_left K5a h3
      _ = 3 * K5a * PABr Kb Cm p α ss ts j := by ring
  -- ## phase 3: stash `t_j` on stack 7
  have hc3 : K7 * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) ≤ K7 * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left K7 ?_
    rw [vsint]
    omega
  -- ## phase 4: peel `s_j` off stack 2
  have hc4 : K5b * (vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) + vsz (Val.int (ss.getD j 0 : ℤ)) + 1) ≤ 3 * K5b * PABr Kb Cm p α ss ts j := by
    have h3 : vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) + vsz (Val.int (ss.getD j 0 : ℤ)) + 1 ≤ 3 * PABr Kb Cm p α ss ts j := by
      rw [vscs, vsints]
      omega
    calc K5b * (vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) + vsz (Val.int (ss.getD j 0 : ℤ)) + 1) ≤ K5b * (3 * PABr Kb Cm p α ss ts j) := Nat.mul_le_mul_left K5b h3
      _ = 3 * K5b * PABr Kb Cm p α ss ts j := by ring
  -- ## phase 5: stash `s_j` on stack 11
  have hc5 : K11 * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) ≤ K11 * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left K11 ?_
    rw [vsints]
    omega
  -- ## phase 6: push `int 1`
  have hc6 : Kpv * (vsz (Val.int 1) + 1) ≤ Kpv * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kpv ?_
    have h1 : isz (1 : ℤ) ≤ 3 := by
      have h2 : (1 : ℤ).natAbs = 1 := by simp
      have h3 : Nat.size ((1 : ℤ).natAbs) ≤ 1 := by rw [h2]; exact paSizeLeSelf 1
      simp only [isz]; omega
    rw [Work.ConvR.vsz_int]
    omega
  -- ## phase 7: multiply `ss.drop (j+1)` into the accumulator
  have hlen_ss : (ss.drop (j + 1)).length ≤ D := by rw [List.length_drop, hsslen]; omega
  have hlt_ss : ∀ x ∈ ss.drop (j + 1), x < 2 ^ p := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    rw [← hix, ← List.getD_eq_getElem (ss.drop (j + 1)) 0 hi]
    rw [pa_getD_drop ss (j + 1) i (by simpa using hi)]
    have hi2 : i < (ss.drop (j + 1)).length := hi
    rw [List.length_drop, hsslen] at hi2
    exact lt_trans (hdim (i + (j + 1)) (by omega)).2.1 (hdim (i + (j + 1)) (by omega)).2.2.1
  have hts_one : ∀ x ∈ ts, 1 ≤ x := pbRnd_one_le_ts p α ss ts hResC
  have hA1 : 1 ≤ (ts.take j).prod :=
    pbRnd_one_le_prod (fun x hx => hts_one x ((List.take_sublist j ts).subset hx))
  have hBhyp : (ss.drop (j + 1)).prod ≤
      (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) := by
    have h1 : 1 ≤ (ts.take j).prod * (ss.getD j 0 + ts.getD j 0 + 1) := by
      have h2 : 1 ≤ ss.getD j 0 + ts.getD j 0 + 1 := by omega
      calc 1 = 1 * 1 := (mul_one 1).symm
        _ ≤ (ts.take j).prod * (ss.getD j 0 + ts.getD j 0 + 1) := Nat.mul_le_mul hA1 h2
    calc (ss.drop (j + 1)).prod = 1 * (ss.drop (j + 1)).prod := (one_mul _).symm
      _ ≤ ((ts.take j).prod * (ss.getD j 0 + ts.getD j 0 + 1)) * (ss.drop (j + 1)).prod :=
          Nat.mul_le_mul_right _ h1
      _ = (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) := by ring
  have hc7 : K6 * ((ss.drop (j + 1)).length + 1) * ((((ss.drop (j + 1)).map (fun x : ℕ => isz (x : ℤ))).sum) + ((ss.drop (j + 1)).prod).size + 2) * (((ss.drop (j + 1)).prod).size + 2) ≤ 7 * K6 * (D + 1) * PABr Kb Cm p α ss ts j :=
    paProdWordCost hResC hjD (ss.drop (j + 1)) ((ss.drop (j + 1)).prod) hlen_ss hlt_ss hBhyp
  -- ## phase 8: stash `B_j` on stack 10
  have hc8 : Kn10 * (vsz (Val.int ((ss.drop (j + 1)).prod)) + 1) ≤ Kn10 * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kn10 ?_
    rw [Work.ConvR.vsz_int]
    omega
  -- ## phase 9: copy `t_j` onto the value stack
  have hc9 : Kc4a * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) ≤ Kc4a * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4a ?_
    rw [vsint]
    omega
  -- ## phase 10: copy `s_j` onto the value stack
  have hc10 : Kc4b * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) ≤ Kc4b * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4b ?_
    rw [vsints]
    omega
  -- ## phase 11: copy `α` onto the value stack
  have hα3 : α + 3 ≤ (D + 1) * (p + 2) := by
    have h4 : α + 2 ≤ p := by
      have h5 : α + 2 ≤ α * α := by
        calc α + 2 ≤ 2 * α := by omega
          _ = α * 2 := by ring
          _ ≤ α * α := Nat.mul_le_mul_left α hα2
      have h6 : α * α < p := by simpa [pow_two] using hαp
      omega
    calc α + 3 ≤ 2 * (p + 2) := by omega
      _ ≤ (D + 1) * (p + 2) := Nat.mul_le_mul_right _ (by omega)
  have hc11 : Kc4c * (vsz (Val.int α) + 1) ≤ Kc4c * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4c ?_
    have h1 : isz ((α : ℕ) : ℤ) = α.size + 2 := by simp [isz, Int.natAbs_natCast]
    rw [Work.ConvR.vsz_int, h1]
    have h2 : α.size ≤ α := paSizeLeSelf α
    omega
  -- ## phase 12: copy `p` onto the value stack
  have hp3 : p + 3 ≤ (D + 1) * (p + 2) := by
    calc p + 3 ≤ 2 * (p + 2) := by omega
      _ ≤ (D + 1) * (p + 2) := Nat.mul_le_mul_right _ (by omega)
  have hc12 : Kc4d * (vsz (Val.int p) + 1) ≤ Kc4d * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4d ?_
    have h1 : isz ((p : ℕ) : ℤ) = p.size + 2 := by simp [isz, Int.natAbs_natCast]
    rw [Work.ConvR.vsz_int, h1]
    have h2 : p.size ≤ p := paSizeLeSelf p
    omega
  -- ## phase 13: `prep`
  have hc13 : 1 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) ≤ 1 * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left 1 ?_
    unfold PABr; omega
  -- ## phase 14: unpark the array
  have hc14 : Ku1 * (vsz arr + 1) ≤ Ku1 * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Ku1 ?_
    omega
  -- ## phase 15: move `B_j` from stack 10 to the value stack
  have hc15 : Kb10 * (vsz (Val.int ((ss.drop (j + 1)).prod)) + 1) ≤ Kb10 * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kb10 ?_
    rw [Work.ConvR.vsz_int]
    omega
  -- ## phase 16: copy `t_j` onto the value stack
  have hc16 : Kc4e * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) ≤ Kc4e * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4e ?_
    rw [vsint]
    omega
  -- ## phase 17: move `s_j` from stack 11 to the value stack
  have hc17 : Kb11 * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) ≤ Kb11 * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kb11 ?_
    rw [vsints]
    omega
  -- ## phase 18: copy `A_j` onto the value stack
  have hc18 : Kc4f * (vsz (Val.int ((ts.take j).prod)) + 1) ≤ Kc4f * PABr Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4f ?_
    rw [Work.ConvR.vsz_int]
    omega
  -- ## assembly
  have key : paEStageCost K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11
      Kc4f Kb Cm p α ss ts j arr ≤ (K1 + (3 * K5a + (K7 + (3 * K5b + (K11 + (Kpv + (7 * K6 * (D + 1) + (Kn10 + (Kc4a + (Kc4b + (Kc4c + (Kc4d + (1 + (Ku1 + (Kb10 + (Kc4e + (Kb11 + (Kc4f)))))))))))))))))) * PABr Kb Cm p α ss ts j := by
    unfold paEStageCost
    have hchain : K1 * (vsz arr + 1) + (K5a * (vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) + vsz (Val.int (ts.getD j 0 : ℤ)) + 1) + (K7 * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) + (K5b * (vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) + vsz (Val.int (ss.getD j 0 : ℤ)) + 1) + (K11 * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) + (Kpv * (vsz (Val.int 1) + 1) + (K6 * ((ss.drop (j + 1)).length + 1) * ((((ss.drop (j + 1)).map (fun x : ℕ => isz (x : ℤ))).sum) + ((ss.drop (j + 1)).prod).size + 2) * (((ss.drop (j + 1)).prod).size + 2) + (Kn10 * (vsz (Val.int ((ss.drop (j + 1)).prod)) + 1) + (Kc4a * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) + (Kc4b * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) + (Kc4c * (vsz (Val.int α) + 1) + (Kc4d * (vsz (Val.int p) + 1) + (1 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) + (Ku1 * (vsz arr + 1) + (Kb10 * (vsz (Val.int ((ss.drop (j + 1)).prod)) + 1) + (Kc4e * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) + (Kb11 * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) + (Kc4f * (vsz (Val.int ((ts.take j).prod)) + 1)))))))))))))))))) ≤ K1 * PABr Kb Cm p α ss ts j + (3 * K5a * PABr Kb Cm p α ss ts j + (K7 * PABr Kb Cm p α ss ts j + (3 * K5b * PABr Kb Cm p α ss ts j + (K11 * PABr Kb Cm p α ss ts j + (Kpv * PABr Kb Cm p α ss ts j + (7 * K6 * (D + 1) * PABr Kb Cm p α ss ts j + (Kn10 * PABr Kb Cm p α ss ts j + (Kc4a * PABr Kb Cm p α ss ts j + (Kc4b * PABr Kb Cm p α ss ts j + (Kc4c * PABr Kb Cm p α ss ts j + (Kc4d * PABr Kb Cm p α ss ts j + (1 * PABr Kb Cm p α ss ts j + (Ku1 * PABr Kb Cm p α ss ts j + (Kb10 * PABr Kb Cm p α ss ts j + (Kc4e * PABr Kb Cm p α ss ts j + (Kb11 * PABr Kb Cm p α ss ts j + (Kc4f * PABr Kb Cm p α ss ts j))))))))))))))))) :=
      Nat.add_le_add hc1 (Nat.add_le_add hc2 (Nat.add_le_add hc3 (Nat.add_le_add hc4
        (Nat.add_le_add hc5 (Nat.add_le_add hc6 (Nat.add_le_add hc7 (Nat.add_le_add hc8
        (Nat.add_le_add hc9 (Nat.add_le_add hc10 (Nat.add_le_add hc11 (Nat.add_le_add hc12
        (Nat.add_le_add hc13 (Nat.add_le_add hc14 (Nat.add_le_add hc15 (Nat.add_le_add hc16
        (Nat.add_le_add hc17 (hc18)))))))))))))))))
    have heq : K1 * PABr Kb Cm p α ss ts j + (3 * K5a * PABr Kb Cm p α ss ts j + (K7 * PABr Kb Cm p α ss ts j + (3 * K5b * PABr Kb Cm p α ss ts j + (K11 * PABr Kb Cm p α ss ts j + (Kpv * PABr Kb Cm p α ss ts j + (7 * K6 * (D + 1) * PABr Kb Cm p α ss ts j + (Kn10 * PABr Kb Cm p α ss ts j + (Kc4a * PABr Kb Cm p α ss ts j + (Kc4b * PABr Kb Cm p α ss ts j + (Kc4c * PABr Kb Cm p α ss ts j + (Kc4d * PABr Kb Cm p α ss ts j + (1 * PABr Kb Cm p α ss ts j + (Ku1 * PABr Kb Cm p α ss ts j + (Kb10 * PABr Kb Cm p α ss ts j + (Kc4e * PABr Kb Cm p α ss ts j + (Kb11 * PABr Kb Cm p α ss ts j + (Kc4f * PABr Kb Cm p α ss ts j))))))))))))))))) = (K1 + (3 * K5a + (K7 + (3 * K5b + (K11 + (Kpv + (7 * K6 * (D + 1) + (Kn10 + (Kc4a + (Kc4b + (Kc4c + (Kc4d + (1 + (Ku1 + (Kb10 + (Kc4e + (Kb11 + (Kc4f)))))))))))))))))) * PABr Kb Cm p α ss ts j := by ring
    exact le_trans hchain (le_of_eq heq)
  refine le_trans key (Nat.mul_le_mul_right (PABr Kb Cm p α ss ts j) ?_)
  unfold paEStageKc
  omega


/-- **Preamble of one axis step of the `Ã` program.**  As `Work.Resample.paStageD`, but with the
hypothesis `Kb * p < N` (which the assembly can supply directly) instead of `Kb ≤ Kc` (which it
cannot, `Kc` being this lemma's own existential constant).  In `paStageD`'s proof, the hypothesis
`Kb ≤ Kc` is used only to derive `Kb * p < N`, so the `paStageD` proof script goes through after
replacing that derivation by the new hypothesis (or by re-proving the statement directly: from the
invariant `PAInv … j`, park the array on stack 1, peel `t_j` off stack 3 and `s_j` off stack 2, keep
a copy of `t_j` on stack 7, compute `B_j = (ss.drop (j+1)).prod` on stack 2 with
`Work.Resample.pbW6` into an `int 1` accumulator (stash on stack 10), push the four `prep` arguments
`p, α, s_j, t_j` (in this order, `p` on top) with `paW4`, run `prep`, unpark the array on top of the
table `Pj`, and push the four `LayoutLib.applyAlong` arguments `A_j, s_j, t_j, B_j` (in this order,
`A_j` on top)). -/
theorem paStageE (Kb : ℕ) (prep q : HvdH.Cmd) :
    ∃ (stage : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ)
        (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
        (zs0 : List (ℤ × ℤ)) (Pj : List HvdH.Val),
      HvdH.ResParams p α ss ts → Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N → Kb * p < N →
      j < HvdH.D →
      Work.Resample.SliceSpecAtA Kb p α (ss.getD j 0) (ts.getD j 0) prep q (Φ j) Pj →
      Work.Resample.WordP main stage
        (fun vs rest a => Work.Resample.PAInv p α ss ts Φ zs0 j vs rest a)
        (fun vs rest a out b => Work.Resample.PAMid Kb p α ss ts Φ zs0 j Pj out rest b)
        (fun _ _ _ => Kc * Work.Resample.PABr Kb Cm p α ss ts j) := by

  obtain ⟨park1, K1, hPark1⟩ := paW2 1 (by decide)
  obtain ⟨peel3, K5a, hPeel3⟩ := paW5 3 (by decide)
  obtain ⟨mv7, K7, hmv7⟩ := paW2 7 (by decide)
  obtain ⟨peel2, K5b, hPeel2⟩ := paW5 2 (by decide)
  obtain ⟨mv11, K11, hmv11⟩ := paW2 11 (by decide)
  obtain ⟨push1, Kpv, hPush1⟩ := Work.Kernel.kernelLib_pushVal
  obtain ⟨prod6, K6, hProd6⟩ := pbW6f
  obtain ⟨mv10, Kn10, hmv10⟩ := paW2 10 (by decide)
  obtain ⟨cp7, Kc4a, hCp7⟩ := paW4 7 (by decide)
  obtain ⟨cp11, Kc4b, hCp11⟩ := paW4 11 (by decide)
  obtain ⟨cp4, Kc4c, hCp4⟩ := paW4 4 (by decide)
  obtain ⟨cp5, Kc4d, hCp5⟩ := paW4 5 (by decide)
  obtain ⟨unpark1, Ku1, hUnpark1⟩ := paW1 1 (by decide)
  obtain ⟨mvB10, Kb10, hmvB10⟩ := paW1 10 (by decide)
  obtain ⟨cp7b, Kc4e, hCp7b⟩ := paW4 7 (by decide)
  obtain ⟨mv11b, Kb11, hmv11b⟩ := paW1 11 (by decide)
  obtain ⟨cp6, Kc4f, hCp6⟩ := paW4 6 (by decide)
  have hCost := paEStageCostBd K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10
    Kc4e Kb11 Kc4f Kb
  refine ⟨Cmd.seq park1 (Cmd.seq peel3 (Cmd.seq mv7 (Cmd.seq peel2 (Cmd.seq mv11 (Cmd.seq (push1 (Val.int
  1)) (Cmd.seq prod6 (Cmd.seq mv10 (Cmd.seq cp7 (Cmd.seq cp11 (Cmd.seq cp4 (Cmd.seq cp5 (Cmd.seq
  prep (Cmd.seq unpark1 (Cmd.seq mvB10 (Cmd.seq cp7b (Cmd.seq mv11b (cp6))))))))))))))))),
    paEStageKc K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f Kb, ?_⟩
  intro main N Cm p α ss ts j Φ zs0 Pj hRes hMon hMul hKN hKbN hjD hSlice
  intro vs rest a hPre s R0 Bg h0 hk
  obtain ⟨arr, hPAVec, hvs, hp1, hp2, hp3, hp4, hp5, hp6, hpRest⟩ := hPre
  have hp7 : a 7 = [] := hpRest 7 (by decide) (by decide)
  obtain ⟨harr, hlen0, hdisc0, hsz0⟩ := hPAVec
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hRes' : ResParams p α ss ts := ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩
  have hjts : j < ts.length := by rw [htslen]; exact hjD
  have hjss : j < ss.length := by rw [hsslen]; exact hjD
  have hKbpN : Kb * p < N := hKbN
  have hKb1 : 1 ≤ Kb := by
    rcases Nat.eq_zero_or_pos Kb with h0' | h0'
    · exact (paEKb0False h0' hSlice main N Cm hMon hMul hKbpN).elim
    · exact h0'
  have hstj : ss.getD j 0 < ts.getD j 0 := (hdim j hjD).2.1
  have hs2 : 2 ≤ ss.getD j 0 := (hdim j hjD).1
  have h3split : intList (ts.drop j) =
      Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1))) :=
    pa_intList_drop_cons hjts
  have h2split : intList (ss.drop j) =
      Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1))) :=
    pa_intList_drop_cons hjss
  have hss_ge : ∀ x ∈ ss.drop (j + 1), 2 ≤ x := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    rw [← hix, ← List.getD_eq_getElem (ss.drop (j + 1)) 0 hi]
    rw [pa_getD_drop ss (j + 1) i (by simpa using hi)]
    have hi2 : i < (ss.drop (j + 1)).length := hi
    rw [List.length_drop, hsslen] at hi2
    exact (hdim (i + (j + 1)) (by omega)).1
  -- ## phase 1: park the array on stack 1
  obtain ⟨vs1, a1, s1, n1, ⟨hv1, e1⟩, hev1, hc1, h01, hk1⟩ :=
    hPark1 main arr [] (a 1) vs a ⟨by simp [hvs], rfl⟩ s (paMark :: (encs rest ++ R0)) Bg h0 hk
  -- ## phase 2: peel `t_j` off stack 3
  have h2a : a1 3 = Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1))) :: [] := by
    rw [e1, Function.update_of_ne (by decide : (3 : Stk) ≠ 1), hp3, h3split]
  obtain ⟨vs2, a2, s2, n2, ⟨hv2, e2⟩, hev2, hc2, h02, hk2⟩ :=
    hPeel3 main (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1))) [] [] vs1 a1 ⟨hv1, h2a⟩ s1 (paMark :: (encs rest ++ R0)) Bg h01 hk1
  -- ## phase 3: stash `t_j` on stack 7
  have h3a : a2 7 = [] := by
    rw [e2, Function.update_of_ne (by decide : (7 : Stk) ≠ 3), e1, Function.update_of_ne (by
      decide : (7 : Stk) ≠ 1), hp7]
  obtain ⟨vs3, a3, s3, n3, ⟨hv3, e3⟩, hev3, hc3, h03, hk3⟩ :=
    hmv7 main (Val.int (ts.getD j 0 : ℤ)) [] [] vs2 a2 ⟨by rw [hv2, hv1], h3a⟩ s2 (paMark :: (encs rest ++ R0)) Bg h02 hk2
  -- ## phase 4: peel `s_j` off stack 2
  have h4a : a3 2 = Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1))) :: [] := by
    rw [e3, Function.update_of_ne (by decide : (2 : Stk) ≠ 7), e2, Function.update_of_ne (by
      decide : (2 : Stk) ≠ 3), e1, Function.update_of_ne (by decide : (2 : Stk) ≠ 1), hp2,
      h2split]
  obtain ⟨vs4, a4, s4, n4, ⟨hv4, e4⟩, hev4, hc4, h04, hk4⟩ :=
    hPeel2 main (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1))) [] [] vs3 a3 ⟨hv3, h4a⟩ s3 (paMark :: (encs rest ++ R0)) Bg h03 hk3
  -- ## phase 5: stash `s_j` on stack 11
  have h5a : a4 11 = [] := by
    rw [e4, Function.update_of_ne (by decide : (11 : Stk) ≠ 2), e3, Function.update_of_ne (by
      decide : (11 : Stk) ≠ 7), e2, Function.update_of_ne (by decide : (11 : Stk) ≠ 3), e1,
      Function.update_of_ne (by decide : (11 : Stk) ≠ 1), hpRest 11 (by decide) (by decide)]
  obtain ⟨vs5, a5, s5, n5, ⟨hv5, e5⟩, hev5, hc5, h05, hk5⟩ :=
    hmv11 main (Val.int (ss.getD j 0 : ℤ)) [] [] vs4 a4 ⟨by rw [hv4, hv3], h5a⟩ s4 (paMark :: (encs rest ++ R0)) Bg h04 hk4
  -- ## phase 6: push `int 1`
  obtain ⟨vs6, s6, n6, hpost6, hev6, hc6, h06, hk6⟩ :=
    hPush1 main (Val.int 1) vs5 trivial s5 (paMark :: (encs rest ++ R0)) h05
  have hv6 : vs6 = Val.int 1 :: [] := by rw [hpost6, hv5]
  have hk6' : ∀ k : Stk, k ≠ 0 → s6.stk k = encs (a5 k) ++ Bg k := by
    intro k hk0; rw [hk6 k hk0]; exact hk5 k hk0
  -- ## phase 7: multiply `ss.drop (j+1)` into the accumulator
  have h7a : a5 2 = intList (ss.drop (j + 1)) :: [] := by
    rw [e5, Function.update_of_ne (by decide : (2 : Stk) ≠ 11), e4, Function.update_self]
  obtain ⟨vs7, a6, s7, n7, ⟨hv7, e6⟩, hev7, hc7, h07, hk7⟩ :=
    hProd6 main (ss.drop (j + 1)) [] [] hss_ge vs6 a5 ⟨hv6, h7a⟩ s6 (paMark :: (encs rest ++ R0)) Bg h06 hk6'
  -- ## phase 8: stash `B_j` on stack 10
  have h8a : a6 10 = [] := by
    rw [e6, e5, Function.update_of_ne (by decide : (10 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (10 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (10 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (10 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (10 : Stk) ≠ 1), hpRest 10 (by decide) (by decide)]
  obtain ⟨vs8, a7, s8, n8, ⟨hv8, e7⟩, hev8, hc8, h08, hk8⟩ :=
    hmv10 main (Val.int ((ss.drop (j + 1)).prod)) [] [] vs7 a6 ⟨hv7, h8a⟩ s7 (paMark :: (encs rest ++ R0)) Bg h07 hk7
  -- ## phase 9: copy `t_j` onto the value stack
  have h9a : a7 7 = [Val.int (ts.getD j 0 : ℤ)] := by
    rw [e7, Function.update_of_ne (by decide : (7 : Stk) ≠ 10), e6, e5, Function.update_of_ne
      (by decide : (7 : Stk) ≠ 11), e4, Function.update_of_ne (by decide : (7 : Stk) ≠ 2), e3,
      Function.update_self]
  obtain ⟨vs9, a8, s9, n9, ⟨hv9, e8⟩, hev9, hc9, h09, hk9⟩ :=
    hCp7 main (Val.int (ts.getD j 0 : ℤ)) vs8 vs8 a7 ⟨rfl, h9a⟩ s8 (paMark :: (encs rest ++ R0)) Bg h08 hk8
  -- ## phase 10: copy `s_j` onto the value stack
  have h10a : a8 11 = [Val.int (ss.getD j 0 : ℤ)] := by
    rw [e8, e7, Function.update_of_ne (by decide : (11 : Stk) ≠ 10), e6, e5,
      Function.update_self]
  obtain ⟨vs10, a9, s10, n10, ⟨hv10, e9⟩, hev10, hc10, h010, hk10⟩ :=
    hCp11 main (Val.int (ss.getD j 0 : ℤ)) vs9 vs9 a8 ⟨rfl, h10a⟩ s9 (paMark :: (encs rest ++ R0)) Bg h09 hk9
  -- ## phase 11: copy `α` onto the value stack
  have h11a : a9 4 = [Val.int α] := by
    rw [e9, e8, e7, Function.update_of_ne (by decide : (4 : Stk) ≠ 10), e6, e5,
      Function.update_of_ne (by decide : (4 : Stk) ≠ 11), e4, Function.update_of_ne (by decide :
      (4 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (4 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (4 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (4 : Stk) ≠ 1), hp4]
  obtain ⟨vs11, a10, s11, n11, ⟨hv11, e10⟩, hev11, hc11, h011, hk11⟩ :=
    hCp4 main (Val.int α) vs10 vs10 a9 ⟨rfl, h11a⟩ s10 (paMark :: (encs rest ++ R0)) Bg h010 hk10
  -- ## phase 12: copy `p` onto the value stack
  have h12a : a10 5 = [Val.int p] := by
    rw [e10, e9, e8, e7, Function.update_of_ne (by decide : (5 : Stk) ≠ 10), e6, e5,
      Function.update_of_ne (by decide : (5 : Stk) ≠ 11), e4, Function.update_of_ne (by decide :
      (5 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (5 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (5 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (5 : Stk) ≠ 1), hp5]
  obtain ⟨vs12, a11, s12, n12, ⟨hv12, e11⟩, hev12, hc12, h012, hk12⟩ :=
    hCp5 main (Val.int p) vs11 vs11 a10 ⟨rfl, h12a⟩ s11 (paMark :: (encs rest ++ R0)) Bg h011 hk11
  -- ## phase 13: `prep`
  have hv12' : vs12 = Val.int p :: Val.int α :: Val.int (ss.getD j 0) ::
      Val.int (ts.getD j 0) :: [] := by
    rw [hv12, hv11, hv10, hv9, hv8]
  obtain ⟨out13, s13, n13, hpost13, hev13, hc13, h013, hk13⟩ :=
    (hSlice.1 main N Cm hMon hMul hKbpN) vs12 ⟨[], by rw [hv12']⟩ s12
      (paMark :: (encs rest ++ R0)) h012
  obtain ⟨rest13, hvs13, hout13⟩ := hpost13
  have hrest13 : rest13 = [] := by
    have hlen : vs12.length = (Val.int p :: Val.int α :: Val.int (ss.getD j 0) ::
        Val.int (ts.getD j 0) :: rest13).length := congrArg List.length hvs13
    rw [hv12'] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    have h0 : rest13.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero h0
  have hout13' : out13 = Pj := by rw [hout13, hrest13, List.append_nil]
  have hk13' : ∀ k : Stk, k ≠ 0 → s13.stk k = encs (a11 k) ++ Bg k := by
    intro k hk0; rw [hk13 k hk0]; exact hk12 k hk0
  -- ## phase 14: unpark the array on top of the table
  have h14a : a11 1 = [arr] := by
    rw [e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (1 : Stk) ≠ 10), e6, e5,
      Function.update_of_ne (by decide : (1 : Stk) ≠ 11), e4, Function.update_of_ne (by decide :
      (1 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (1 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (1 : Stk) ≠ 3), e1, Function.update_self, hp1]
  obtain ⟨vs14, a12, s14, n14, ⟨hv14, e12⟩, hev14, hc14, h014, hk14⟩ :=
    hUnpark1 main arr Pj out13 a11 ⟨hout13', h14a⟩ s13 (paMark :: (encs rest ++ R0)) Bg h013 hk13'
  -- ## phase 15: move `B_j` from stack 10 to the value stack
  have h15a : a12 10 = [Val.int ((ss.drop (j + 1)).prod)] := by
    rw [e12, Function.update_of_ne (by decide : (10 : Stk) ≠ 1), e11, e10, e9, e8, e7,
      Function.update_self]
  obtain ⟨vs15, a13, s15, n15, ⟨hv15, e13⟩, hev15, hc15, h015, hk15⟩ :=
    hmvB10 main (Val.int ((ss.drop (j + 1)).prod)) vs14 vs14 a12 ⟨rfl, h15a⟩ s14 (paMark :: (encs rest ++ R0)) Bg h014 hk14
  -- ## phase 16: copy `t_j` onto the value stack
  have h16a : a13 7 = [Val.int (ts.getD j 0 : ℤ)] := by
    rw [e13, Function.update_of_ne (by decide : (7 : Stk) ≠ 10), e12, Function.update_of_ne (by
      decide : (7 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (7 :
      Stk) ≠ 10), e6, e5, Function.update_of_ne (by decide : (7 : Stk) ≠ 11), e4,
      Function.update_of_ne (by decide : (7 : Stk) ≠ 2), e3, Function.update_self]
  obtain ⟨vs16, a14, s16, n16, ⟨hv16, e14⟩, hev16, hc16, h016, hk16⟩ :=
    hCp7b main (Val.int (ts.getD j 0 : ℤ)) vs15 vs15 a13 ⟨rfl, h16a⟩ s15 (paMark :: (encs rest ++ R0)) Bg h015 hk15
  -- ## phase 17: move `s_j` from stack 11 to the value stack
  have h17a : a14 11 = [Val.int (ss.getD j 0 : ℤ)] := by
    rw [e14, e13, Function.update_of_ne (by decide : (11 : Stk) ≠ 10), e12,
      Function.update_of_ne (by decide : (11 : Stk) ≠ 1), e11, e10, e9, e8, e7,
      Function.update_of_ne (by decide : (11 : Stk) ≠ 10), e6, e5, Function.update_self]
  obtain ⟨vs17, a15, s17, n17, ⟨hv17, e15⟩, hev17, hc17, h017, hk17⟩ :=
    hmv11b main (Val.int (ss.getD j 0 : ℤ)) vs16 vs16 a14 ⟨rfl, h17a⟩ s16 (paMark :: (encs rest ++ R0)) Bg h016 hk16
  -- ## phase 18: copy `A_j` onto the value stack
  have h18a : a15 6 = [Val.int ((ts.take j).prod)] := by
    rw [e15, Function.update_of_ne (by decide : (6 : Stk) ≠ 11), e14, e13, Function.update_of_ne
      (by decide : (6 : Stk) ≠ 10), e12, Function.update_of_ne (by decide : (6 : Stk) ≠ 1), e11,
      e10, e9, e8, e7, Function.update_of_ne (by decide : (6 : Stk) ≠ 10), e6, e5,
      Function.update_of_ne (by decide : (6 : Stk) ≠ 11), e4, Function.update_of_ne (by decide :
      (6 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (6 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (6 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (6 : Stk) ≠ 1), hp6]
  obtain ⟨vs18, a16, s18, n18, ⟨hv18, e16⟩, hev18, hc18, h018, hk18⟩ :=
    hCp6 main (Val.int ((ts.take j).prod)) vs17 vs17 a15 ⟨rfl, h18a⟩ s17 (paMark :: (encs rest ++ R0)) Bg h017 hk17
  -- ## the final value list
  have hvs18' : vs18 = Val.int ((ts.take j).prod) :: Val.int (ss.getD j 0 : ℤ) ::
      Val.int (ts.getD j 0 : ℤ) :: Val.int ((ss.drop (j + 1)).prod) :: arr :: Pj := by
    rw [hv18, hv17, hv16, hv15, hv14, hout13']
  -- ## the table size bound
  have hPjsum : (Pj.map vsz).sum ≤ 8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) :=
    paTabSz hSlice.1 main N Cm hMon hMul hKbpN hKb1 hp100 hα2 hαp hs2 hstj
  -- ## the components of the final stack description
  have ha1F : a16 1 = [] := by
    rw [e16, e15, Function.update_of_ne (by decide : (1 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (1 : Stk) ≠ 10), e12, Function.update_self]
  have ha2F : a16 2 = [intList (ss.drop (j + 1))] := by
    rw [e16, e15, Function.update_of_ne (by decide : (2 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (2 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (2 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (2 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (2 : Stk) ≠ 11), e4, Function.update_self]
  have ha3F : a16 3 = [intList (ts.drop (j + 1))] := by
    rw [e16, e15, Function.update_of_ne (by decide : (3 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (3 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (3 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (3 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (3 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (3 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (3 : Stk) ≠ 7), e2,
      Function.update_self]
  have ha4F : a16 4 = [Val.int α] := by
    rw [e16, e15, Function.update_of_ne (by decide : (4 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (4 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (4 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (4 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (4 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (4 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (4 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (4 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (4 : Stk) ≠ 1), hp4]
  have ha5F : a16 5 = [Val.int p] := by
    rw [e16, e15, Function.update_of_ne (by decide : (5 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (5 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (5 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (5 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (5 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (5 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (5 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (5 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (5 : Stk) ≠ 1), hp5]
  have ha6F : a16 6 = [Val.int ((ts.take j).prod)] := by
    rw [e16, e15, Function.update_of_ne (by decide : (6 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (6 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (6 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (6 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (6 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (6 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (6 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (6 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (6 : Stk) ≠ 1), hp6]
  have ha7F : a16 7 = [Val.int (ts.getD j 0 : ℤ)] := by
    rw [e16, e15, Function.update_of_ne (by decide : (7 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (7 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (7 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (7 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (7 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (7 : Stk) ≠ 2), e3, Function.update_self]
  have haRestF : ∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({2, 3, 4, 5, 6, 7} : Finset ℕ) →
      a16 k = [] := by
    intro k hk0 hkF
    have hkF6 : (k : ℕ) ∉ ({2, 3, 4, 5, 6} : Finset ℕ) := by
      intro h
      exact hkF (by simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
    have hk2 : k ≠ 2 := by intro h; exact hkF (by rw [h]; decide)
    have hk3 : k ≠ 3 := by intro h; exact hkF (by rw [h]; decide)
    have hk7 : k ≠ 7 := by intro h; exact hkF (by rw [h]; decide)
    by_cases hk1 : k = 1
    · rw [hk1]; exact ha1F
    by_cases hk10 : k = 10
    · rw [hk10, e16, e15, Function.update_of_ne (by decide : (10 : Stk) ≠ 11), e14, e13,
        Function.update_self]
    by_cases hk11 : k = 11
    · rw [hk11, e16, e15, Function.update_self]
    rw [e16, e15, Function.update_of_ne hk11, e14, e13, Function.update_of_ne hk10, e12,
      Function.update_of_ne hk1, e11, e10, e9, e8, e7, Function.update_of_ne hk10, e6, e5,
      Function.update_of_ne hk11, e4, Function.update_of_ne hk2, e3, Function.update_of_ne hk7,
      e2, Function.update_of_ne hk3, e1, Function.update_of_ne hk1, hpRest k hk0 hkF6]
  -- ## assembly
  refine ⟨vs18, a16, s18, n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + (n12 + (n13 + (n14 + (n15 +
  (n16 + (n17 + (n18))))))))))))))))), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨arr, ⟨harr, hlen0, hdisc0, hsz0⟩, hvs18', hPjsum, ha1F, ha2F, ha3F, ha4F, ha5F, ha6F, ha7F, haRestF⟩
  · exact Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4 (Eval.seq hev5 (Eval.seq hev6
  (Eval.seq hev7 (Eval.seq hev8 (Eval.seq hev9 (Eval.seq hev10 (Eval.seq hev11 (Eval.seq hev12
  (Eval.seq hev13 (Eval.seq hev14 (Eval.seq hev15 (Eval.seq hev16 (Eval.seq hev17
  hev18))))))))))))))))
  · have hc13' : n13 ≤ 1 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) := by simpa using hc13
    have hbound : n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + (n12 + (n13 + (n14 + (n15 +
  (n16 + (n17 + (n18))))))))))))))))) ≤
        paEStageCost K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f Kb
          Cm p α ss ts j arr := by
      unfold paEStageCost
      exact       Nat.add_le_add hc1 (Nat.add_le_add hc2 (Nat.add_le_add hc3 (Nat.add_le_add hc4
        (Nat.add_le_add hc5 (Nat.add_le_add hc6 (Nat.add_le_add hc7 (Nat.add_le_add hc8
        (Nat.add_le_add hc9 (Nat.add_le_add hc10 (Nat.add_le_add hc11 (Nat.add_le_add hc12
        (Nat.add_le_add hc13' (Nat.add_le_add hc14 (Nat.add_le_add hc15 (Nat.add_le_add hc16
        (Nat.add_le_add hc17 hc18))))))))))))))))
    exact le_trans hbound (hCost Cm p α ss ts j arr hRes' hjD hsz0)
  · exact h018
  · exact hk18


end Work.Resample
