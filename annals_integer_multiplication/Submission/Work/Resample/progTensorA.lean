import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.specs
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paProofs1
import Submission.Work.Resample.paSetupE
import Submission.Work.Resample.paStageE
import Submission.Work.Resample.paApplyE
import Submission.Work.Resample.paFinalD
import Submission.Work.Resample.paCostD
import Submission.Work.Resample.paFinApproxD

/-!
# The tensoring program `Ã` of paper Theorem 4.1 (the `A` half)

This file assembles the program `progA` of the statement
`Work.Resample.progTensorA` from the six pieces proved in the sibling modules:

* `Work.Resample.paSetupE` — the prologue (moving the control values to stacks 2–5, parking the
  array, pushing the marker `paMark`, putting `int 1` on stack 6 and bringing the array back);
* `Work.Resample.paStageE` — the preamble of one axis step (peel the dimension data, build the
  table `Pj` with `prep`, push the four `applyAlong` arguments);
* `Work.Resample.paApplyE` — the body of one axis step (`LayoutLib.applyAlong` with `comb q`, cleaning
  the junk above the marker, updating the running outer product with `Work.Resample.mulNatWord`);
* `Work.Resample.paIter` (`Submission.Work.Resample.paProofs1`) — the `HvdH.D`-fold iteration;
* `Work.Resample.paFinalD` — the epilogue (draining the auxiliary stacks, removing the marker);
* `Work.Resample.paCostD` — the cost arithmetic (the three budgets fit into `HvdH.resCost`);
* `Work.Resample.paFinApproxD` — the analytic end (the error `< HvdH.D * p^2`).

The assembly itself is a `WordR`-level computation: run `setup`, then the `D`-fold iteration, then
`fin`, tracking the intermediate value stacks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-- Per-axis extraction of the `SliceSpecAtA` data from the uniform `SliceSpecA` specification. -/
theorem paSliceSpec (Kb : ℕ) (prep q : Cmd)
    (hAt : ∀ (p α s t : ℕ), 2 ≤ s → s < t → Nat.Coprime s t → t < 2 ^ p → 2 ≤ α → 100 ≤ p →
      α ^ 2 < p → (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1 →
      ∃ (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)) (P : List Val),
        SliceSpecAtA Kb p α s t prep q Φ P)
    (p α : ℕ) (ss ts : List ℕ) (hRP : HvdH.ResParams p α ss ts) (j : ℕ) (hj : j < HvdH.D) :
    ∃ (Φ : (Fin (ss.getD j 0) → ℤ × ℤ) → (Fin (ts.getD j 0) → ℤ × ℤ)) (Pj : List Val),
      SliceSpecAtA Kb p α (ss.getD j 0) (ts.getD j 0) prep q Φ Pj := by
  have h := hRP.2.2.2.2.2 j hj
  exact hAt p α (ss.getD j 0) (ts.getD j 0) h.1 h.2.1 h.2.2.2.1 h.2.2.1 hRP.2.2.2.1 hRP.2.2.1
    hRP.2.2.2.2.1 h.2.2.2.2

/-- The statement `Work.Resample.progTensorA` (paper Theorem 4.1, `A` half). -/
theorem progTensorA (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib)
    (RM : HvdH.ResMath1DProp) (hA : Work.Resample.SliceSpecA KL IL LL FL RM) :
    ∃ (progA : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ),
      HvdH.ResParams p α ss ts → Monotone Cm → HvdH.MulBelow main N Cm → K * p < N →
      HvdH.WordR main progA
        (fun vs => ∃ (zs : List (ℤ × ℤ)) (rest : List HvdH.Val),
          vs = .int p :: .int α :: HvdH.intList ss :: HvdH.intList ts :: HvdH.cvecVal zs :: rest ∧
          HvdH.InDiscVec p ss.prod zs)
        (fun vs out => ∃ (zs : List (ℤ × ℤ)) (rest : List HvdH.Val) (ws : List (ℤ × ℤ)),
          vs = .int p :: .int α :: HvdH.intList ss :: HvdH.intList ts :: HvdH.cvecVal zs :: rest ∧
          out = HvdH.cvecVal ws :: rest ∧
          HvdH.Approx p ws (Work.Resample.resAop ss ts α (HvdH.fxVec p ss.prod zs))
            (HvdH.D * p ^ 2 : ℕ))
        (fun _ => HvdH.resCost K Cm p α ts) := by
  obtain ⟨prep, q, Kb, hAt⟩ := hA
  obtain ⟨setup, Kc1, hsetup⟩ := paSetupE
  obtain ⟨stage, Kc2, hstage⟩ := paStageE Kb prep q
  obtain ⟨app, Kc3, happ⟩ := paApplyE KL LL Kb prep q
  obtain ⟨iter, Kc5, hiter⟩ := paIter Kb (Kc2 + Kc3) (Cmd.seq stage app)
  obtain ⟨fin, Kc4, hfin⟩ := paFinalD
  obtain ⟨K, hK1, hK', hK4, hKb, hcost⟩ := paCostD Kb Kc1 (max Kc5 (Kc2 + Kc3)) Kc4
  have hK5 : Kc5 ≤ K := le_trans (le_max_left _ _) hK'
  have hK23 : Kc2 + Kc3 ≤ K := le_trans (le_max_right _ _) hK'
  have hK2 : Kc2 ≤ K := by omega
  have hK3 : Kc3 ≤ K := by omega
  refine ⟨Work.Layout.seqs [setup, iter, fin], K, ?_⟩
  intro main N Cm p α ss ts hRP hmon hmb hKp
  intro vs0 hPre s R h0
  obtain ⟨zs0, rest, hvs0, hin⟩ := hPre
  -- the chosen slice maps
  let Phi : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ) := fun i =>
    if hi : i < HvdH.D then Classical.choose (paSliceSpec Kb prep q hAt p α ss ts hRP i hi)
    else fun _ _ => (0, 0)
  have hPhi : ∀ j < HvdH.D, ∃ Pj, SliceSpecAtA Kb p α (ss.getD j 0) (ts.getD j 0) prep q
      (Phi j) Pj := by
    intro j hj
    have h := paSliceSpec Kb prep q hAt p α ss ts hRP j hj
    have hval : Phi j = Classical.choose h := by
      show (if hi : j < HvdH.D then Classical.choose
        (paSliceSpec Kb prep q hAt p α ss ts hRP j hi) else fun _ _ => (0,0)) = _
      rw [dif_pos hj]
    rw [hval]
    exact ⟨Classical.choose (Classical.choose_spec h),
      Classical.choose_spec (Classical.choose_spec h)⟩
  have hPhiAt : ∀ j < HvdH.D, ∃ (s t : ℕ) (prep' q' : HvdH.Cmd) (Kb' : ℕ) (Pj : List HvdH.Val),
      s = ss.getD j 0 ∧ t = ts.getD j 0 ∧
      SliceSpecAtA Kb' p α (ss.getD j 0) (ts.getD j 0) prep' q' (Phi j) Pj := by
    intro j hj
    obtain ⟨Pj, hPj⟩ := hPhi j hj
    exact ⟨ss.getD j 0, ts.getD j 0, prep, q, Kb, Pj, rfl, rfl, hPj⟩
  -- the cost hypotheses
  have hNK1 : Kc1 * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hK1) hKp
  have hNK5 : Kc5 * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hK5) hKp
  have hNK4 : Kc4 * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hK4) hKp
  have hNKb : Kb * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hKb) hKp
  have hNK2 : Kc2 * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hK2) hKp
  have hNK3 : Kc3 * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hK3) hKp
  -- the single axis step
  have hround : ∀ j < HvdH.D, WordP main (Cmd.seq stage app)
      (fun vs rest a => PAInv p α ss ts Phi zs0 j vs rest a)
      (fun vs rest a out b => PAInv p α ss ts Phi zs0 (j + 1) out rest b)
      (fun _ _ _ => (Kc2 + Kc3) * PABr Kb Cm p α ss ts j) := by
    intro j hj
    obtain ⟨Pj, hPj⟩ := hPhi j hj
    refine WordP.conseq (Pre' := fun vs rest a => PAInv p α ss ts Phi zs0 j vs rest a)
      (Post' := fun vs rest a out b => PAInv p α ss ts Phi zs0 (j + 1) out rest b)
      (C' := fun _ _ _ => (Kc2 + Kc3) * PABr Kb Cm p α ss ts j)
      (WordP.seq (B := fun _ _ _ => Kc3 * PABr Kb Cm p α ss ts j)
        (hstage main N Cm p α ss ts j Phi zs0 Pj hRP hmon hmb hNK2 hNKb hj hPj)
        (happ main N Cm p α ss ts j Phi zs0 Pj hRP hmon hmb hNK3 hNKb hj hPj)
        (fun vs rest a mid a' hmid => hmid)
        (fun vs rest a mid a' _ => le_rfl)) ?_ ?_ ?_
    · intro vs rest a hh
      exact hh
    · intro vs rest a out b _ hpost
      obtain ⟨mid, a', _, hpost2⟩ := hpost
      exact hpost2
    · intro vs rest a _
      exact le_of_eq (by rw [Nat.add_mul])
  -- the prologue
  obtain ⟨out1, rout1, b1, s1, n1, hp1, hev1, hc1, h01, hk1⟩ :=
    (hsetup main p α ss ts Phi zs0 rest hRP hin.1 hin.2) vs0 (fun _ : HvdH.Stk => ([] : List HvdH.Val))
      ⟨hvs0, fun k _ => rfl⟩ s R (fun k => s.stk k) h0 (fun k _ => rfl)
  obtain ⟨hrout1, hPA1⟩ := hp1
  -- the D-fold iteration
  obtain ⟨out2, b2, s2, n2, hPA2, hev2, hc2, h02, hk2⟩ :=
    (hiter main N Cm p α ss ts Phi zs0 hRP hmon hmb hNK5 hround) out1 rout1 b1 hPA1
      s1 R (fun k => s.stk k) h01 hk1
  -- the epilogue
  obtain ⟨out3, b3, s3, n3, hp3, hev3, hc3, h03, hk3⟩ :=
    (hfin main p α ss ts Phi zs0 hRP) out2 rout1 b2 hPA2 s2 R (fun k => s.stk k) h02 hk2
  obtain ⟨hout3, hb3⟩ := hp3
  refine ⟨HvdH.cvecVal (axisIter ss ts Phi HvdH.D zs0) :: rest, s3, n1 + (n2 + n3), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨zs0, rest, axisIter ss ts Phi HvdH.D zs0, hvs0, rfl,
      paFinApproxD p α ss ts Phi zs0 hRP hPhiAt RM hin⟩
  · show Eval main (Cmd.seq setup (Cmd.seq iter fin)) s s3 (n1 + (n2 + n3))
    exact Eval.seq hev1 (Eval.seq hev2 hev3)
  · have hc := hcost Cm p α ss ts hRP hmon
    have hmax : Kc5 * PAIterBrF Kb Cm p α ss ts
        ≤ (max Kc5 (Kc2 + Kc3)) * PAIterBrF Kb Cm p α ss ts :=
      Nat.mul_le_mul_right _ (le_max_left _ _)
    calc n1 + (n2 + n3)
        ≤ Kc1 * PASetupBr p ss ts + (Kc5 * PAIterBrF Kb Cm p α ss ts
            + Kc4 * PAFinalBr p ss ts) := Nat.add_le_add hc1 (Nat.add_le_add hc2 hc3)
      _ ≤ Kc1 * PASetupBr p ss ts + ((max Kc5 (Kc2 + Kc3)) * PAIterBrF Kb Cm p α ss ts
            + Kc4 * PAFinalBr p ss ts) := Nat.add_le_add_left (Nat.add_le_add_right hmax _) _
      _ = (Kc1 * PASetupBr p ss ts + (max Kc5 (Kc2 + Kc3)) * PAIterBrF Kb Cm p α ss ts)
            + Kc4 * PAFinalBr p ss ts := by rw [Nat.add_assoc]
      _ ≤ resCost K Cm p α ts := hc
  · simp only [h03, hout3, hrout1, Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.nil_append,
      List.append_nil, List.append_assoc]
  · intro k hk0
    rw [hk3 k hk0, hb3 k hk0, Work.Kernel.encs_nil, List.nil_append]

end Work.Resample
