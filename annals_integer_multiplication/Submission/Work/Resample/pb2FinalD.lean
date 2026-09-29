import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2Defs
import Submission.Work.Resample.paKillD
import Submission.Work.Resample.paTapD
import Submission.Work.Resample.paFinalSizes

/-! Guidance from the project lead (the requester):

LEAD (endgame: Resample's B half is the LAST open piece of the whole problem — speed matters). This statement is the
MIRROR of the already PROVED `Work.Resample.paFinalD` (Submission/Work/Resample/). Start by COPYING that file's proof and
adapting it; do not design anything new. Mirror dictionary (definitions in Submission/Work/Resample/pb2Defs.lean):
PAVec/PAInv/PAMid/PABr/PAIterBrF ↦ PB2Vec/PB2Inv/PB2Mid/PB2Br/PB2IterBrF; the array flows from shape ts (input,
ts.prod entries) to shape ss (output); list iteration is `axisIter ts ss Φ` with Φ j : (Fin t_j → ℤ×ℤ) → (Fin s_j → ℤ×ℤ);
applyAlong arguments per axis j are A = (ss.take j).prod, m = t_j, n = s_j, B = (ts.drop (j+1)).prod; stack 2 holds the
remaining INPUT dims (ts.drop j), stack 3 the remaining OUTPUT dims (ss.drop j), stack 6 (ss.take j).prod, stack 7 s_j;
SliceSpecAtA Kb p α s t prep q Φ P ↦ SliceSpecAt prep q Kb p α s t Φ P (argument order differs; its q cost has the extra
Kb(t+1)(p+1)² term, already in PB2Br); resAop/rA ↦ resBop/rB. Size bounds keep ts.prod (sᵢ < tᵢ, so every intermediate
array has ≤ ts.prod entries: (ss.take j).prod ≤ (ts.take j).prod). NEVER import pbSetupF, pbRoundF, pbIterGo*, pbIterF*
(obsolete route; pbSetupF needs 17 GB). Split into children only where the A-side proof was split.

The implementation below follows that advice literally: the epilogue is assembled from the *proved*
`Ã`-side pieces, with no new mathematical content.
* The drain of the five auxiliary stacks 2–6 is `Work.Resample.paKillD` **instantiated with the two
  dimension lists swapped**, `hkill main p α ts ss`.  At the end of the loop `PB2Inv … D` puts
  `[intList (ts.drop D)]` on stack 2, `[intList (ss.drop D)]` on stack 3 and `[int ((ss.take D).prod)]`
  on stack 6 — which is *exactly* the (value-generic) precondition of `paKillD` after the swap
  `ss ↦ ts`, `ts ↦ ss`, with the matching cost `vsz (intList (ts.drop D)) + … + vsz (int ((ss.take D).prod)) + 6`.
* The tap (park the array, remove the marker, bring the array back) is `Work.Resample.paTapD`, whose
  statement is independent of which array is parked and of which dimension list produced it.
* The arithmetic is the mirror of `paFinalSizes`: the array bound is the first conjunct of
  `paFinalSizes` verbatim, and the drained-value bound differs from `paFinalSizes`'s second conjunct
  `… + vsz (int ((ts.take D).prod)) + 6` only in its last summand, which is
  `vsz (int ((ss.take D).prod)) = isz ↑(ss.prod)` against `isz ↑(ts.prod)`; `Work.MainP.ss_prod_le_ts_prod`
  and the monotonicity of `isz` close the gap (`Work.Resample.pa_isz_le_isz_of_le`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-- Consequence rule for `WordPe` (mirror of `WordP.conseq`); named `pb2WordPe_conseq` to avoid
clashing with the sibling modules of the area. -/
theorem pb2WordPe_conseq {main p : Cmd}
    {Pre : List Val → List Val → (Stk → List Val) → Prop}
    {Post : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C : List Val → List Val → (Stk → List Val) → ℕ}
    {Pre' : List Val → List Val → (Stk → List Val) → Prop}
    {Post' : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C' : List Val → List Val → (Stk → List Val) → ℕ}
    (h : WordPe main p Pre Post C) (h1 : ∀ vs rest a, Pre' vs rest a → Pre vs rest a)
    (h2 : ∀ vs rest a out b, Pre' vs rest a → Post vs rest a out b → Post' vs rest a out b)
    (h3 : ∀ vs rest a, Pre' vs rest a → C vs rest a ≤ C' vs rest a) :
    WordPe main p Pre' Post' C' := by
  intro vs rest a hPre s R0 Bg h0 hk
  obtain ⟨out, b, s', n, hPost, hev, hc, h0', hk'⟩ :=
    h vs rest a (h1 vs rest a hPre) s R0 Bg h0 hk
  exact ⟨out, b, s', n, h2 vs rest a out b hPre hPost, hev, le_trans hc (h3 vs rest a hPre),
    h0', hk'⟩

/-- Mirror of paFinalD for the B half: epilogue draining the auxiliary stacks. -/
theorem pb2FinalD :
    ∃ (fin : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (p α : ℕ) (ss ts : List ℕ)
        (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
        (zs0 : List (ℤ × ℤ)),
      HvdH.ResParams p α ss ts →
      Work.Resample.WordPe main fin
        (Work.Resample.PB2Inv p α ss ts Φ zs0 HvdH.D)
        (fun vs rest a out b =>
          out = [HvdH.cvecVal (Work.Resample.axisIter ts ss Φ HvdH.D zs0)] ∧
          (∀ k : HvdH.Stk, k ≠ 0 → b k = []))
        (fun _ _ _ => Kc * Work.Resample.PAFinalBr p ss ts) := by
  obtain ⟨kill, Kf, hkill⟩ := paKillD
  obtain ⟨tap, Kt, htap⟩ := paTapD
  refine ⟨HvdH.Cmd.seq kill tap, 8 * Kf + Kt, ?_⟩
  intro main p α ss ts Φ zs0 hres
  obtain ⟨hsize1, hsize2⟩ :=
    paFinalSizes p α ss ts hres.2.2.2.2.1 hres.1 hres.2.1
  have hssD : ss.drop HvdH.D = [] := List.drop_eq_nil_of_le (le_of_eq hres.1)
  have htsD : ts.drop HvdH.D = [] := List.drop_eq_nil_of_le (le_of_eq hres.2.1)
  have htakeS : ss.take HvdH.D = ss := List.take_of_length_le (le_of_eq hres.1)
  have htakeT : ts.take HvdH.D = ts := List.take_of_length_le (le_of_eq hres.2.1)
  -- `α ≤ p`, hence `isz α ≤ isz p` (`paFinalSizes`'s argument)
  have hαp' : α ≤ p := by
    have hlt : α ^ 2 < p := hres.2.2.2.2.1
    rcases Nat.eq_zero_or_pos α with h | h
    · subst h; omega
    · have h2 := Nat.le_self_pow (n := 2) (by decide) α
      omega
  have hPP : ss.prod ≤ ts.prod := Work.MainP.ss_prod_le_ts_prod hres
  -- the total encoded size of the six drained values, bounded by the epilogue budget
  have hsum : HvdH.vsz (HvdH.intList (ts.drop HvdH.D)) +
        HvdH.vsz (HvdH.intList (ss.drop HvdH.D)) +
        HvdH.vsz (HvdH.Val.int (α : ℤ)) + HvdH.vsz (HvdH.Val.int (p : ℤ)) +
        HvdH.vsz (HvdH.Val.int (((ss.take HvdH.D).prod : ℕ) : ℤ)) + 6 ≤
      8 * Work.Resample.PAFinalBr p ss ts := by
    simp only [htakeS, htakeT, hssD, htsD, pa_vsz_intList_nil, Work.ConvR.vsz_int] at hsize2 ⊢
    have h1 : HvdH.isz (α : ℤ) ≤ HvdH.isz (p : ℤ) := pa_isz_le_isz_of_le hαp'
    have h2 : HvdH.isz ((ss.prod : ℕ) : ℤ) ≤ HvdH.isz ((ts.prod : ℕ) : ℤ) :=
      pa_isz_le_isz_of_le hPP
    omega
  -- ### the five drains: `paKillD` with the two dimension lists swapped
  have hpart1 : WordP main kill (PB2Inv p α ss ts Φ zs0 HvdH.D)
      (fun vs rest a out b => ∃ arr, PB2Vec p ss ts Φ zs0 HvdH.D arr ∧ out = [arr] ∧
        (∀ k : Stk, k ≠ 0 → b k = []))
      (fun _ _ _ => 8 * Kf * PAFinalBr p ss ts) := by
    refine WordP.conseq (WordP.ofWordM (hkill main p α ts ss)) ?_ ?_ ?_
    · rintro vs rest a ⟨arr, hvec, hvs, h1, h2, h3, h4, h5, h6, hrest⟩
      exact ⟨h2, h3, h4, h5, h6, hrest⟩
    · rintro vs rest a out b ⟨arr, hvec, hvs, h1, h2, h3, h4, h5, h6, hrest⟩ ⟨hout, hb⟩
      exact ⟨arr, hvec, by rw [hout, hvs], hb⟩
    · intro vs rest a _
      have h := Nat.mul_le_mul_left Kf hsum
      exact le_trans h (le_of_eq (by ring))
  -- ### park, clear the marker, unpark
  have hpart2 : WordPe main tap
      (fun vs rest a => ∃ arr, PB2Vec p ss ts Φ zs0 HvdH.D arr ∧ vs = [arr] ∧
        (∀ k : Stk, k ≠ 0 → a k = []))
      (fun vs rest a out b => out = [cvecVal (axisIter ts ss Φ HvdH.D zs0)] ∧
        (∀ k : Stk, k ≠ 0 → b k = []))
      (fun _ _ _ => Kt * PAFinalBr p ss ts) := by
    refine pb2WordPe_conseq (htap main) ?_ ?_ ?_
    · intro vs rest a hpre
      obtain ⟨arr, hvec, hvs, ha⟩ := hpre
      exact ⟨arr, hvs, ha⟩
    · intro vs rest a out b hpre hpost
      obtain ⟨arr, hvec, hvs, ha⟩ := hpre
      obtain ⟨arr', hvs', hout, hb⟩ := hpost
      have harr : arr' = arr := by simpa using hvs'.symm.trans hvs
      exact ⟨by rw [hout, harr, hvec.1], hb⟩
    · intro vs rest a hpre
      obtain ⟨arr, hvec, hvs, ha⟩ := hpre
      have h : vs.headD Val.nil = arr := by rw [hvs]; rfl
      rw [h]
      refine Nat.mul_le_mul_left _ (le_trans ?_ hsize1)
      have := hvec.2.2.2
      omega
  -- ### the epilogue
  refine pb2WordPe_conseq
    (WordP.seq_e (B := fun _ _ _ => Kt * PAFinalBr p ss ts) hpart1 hpart2 ?_ ?_) ?_ ?_ ?_
  · intro vs rest a mid a' hpost
    exact hpost
  · intro vs rest a mid a' hpost
    exact le_rfl
  · intro vs rest a hpre
    exact hpre
  · intro vs rest a out b hpre hpost
    obtain ⟨mid, a', -, h⟩ := hpost
    exact h
  · intro vs rest a hpre
    exact le_of_eq (by ring)

end Work.Resample
