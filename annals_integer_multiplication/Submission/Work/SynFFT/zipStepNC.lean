import Mathlib
import Submission.Work.SynFFT.zipKit

namespace Work.SynFFT

open HvdH
open Work.Layout

/-- One iteration of the `zipCat` loop when the first group is exhausted and the second nonempty:
the body pushes the empty row (`nil`, i.e. `ofList []`) on the value stack, then moves the head row
`r2` of stack `2` *on top* of it, so the merge is called with the pair `(r2, [])` (the exhausted
group contributes like `zipCat [] (r2 :: t2)`).  See `Work.SynFFT.zipStepCC` for the available
sub-lemmas (`Work.SynFFT.zMer_ev`, `Work.Layout.mvVal_ev_full`, `Work.Layout.pushConst_ev`,
`Work.Layout.ev_peek'`, `Work.Layout.ev_pop'`, `Work.Layout.Ev.seq'`, `Work.Layout.Ev.iteT`,
`Work.Layout.Ev.iteF`); the cost is `Work.SynFFT.zStepCost KA [] (r2 :: t2)
= (KA + 100) * (vsz (ofList r2) + 1)` (`zBump_nil`, `zBump_cons`). -/
theorem zipStepNC {main zApp : HvdH.Cmd} {KA : ℕ}
    (hApp : ∀ (xs ys rest' : List HvdH.Val), HvdH.WordR main zApp
      (fun vs => vs = HvdH.ofList xs :: HvdH.ofList ys :: rest')
      (fun _ out => out = HvdH.ofList (xs ++ ys) :: rest')
      (fun _ => KA * (HvdH.vsz (HvdH.ofList xs) + 1)))
    {rest : List HvdH.Val} {R : List HvdH.Glyph} {r2 : List HvdH.Val}
    {t2 : List (List HvdH.Val)} {Racc : List (List HvdH.Val)} {Z1 Z2 Z3 : List HvdH.Glyph}
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph}
    (h0 : X 0 = HvdH.encs rest ++ R)
    (h1 : X 1 = (HvdH.ofList ([] : List HvdH.Val)).enc ++ Z1)
    (h2 : X 2 = HvdH.Glyph.cons :: ((HvdH.ofList r2).enc ++
      ((HvdH.ofList (t2.map HvdH.ofList)).enc ++ Z2)))
    (h3 : X 3 = (HvdH.ofList (Racc.map HvdH.ofList)).enc ++ Z3) :
    ∃ s' n, Work.Layout.Ev main (Work.SynFFT.zBody zApp) ⟨g, X⟩ s' n ∧
      n ≤ Work.SynFFT.zStepCost KA [] (r2 :: t2) ∧
      s'.stk 0 = X 0 ∧
      s'.stk 1 = X 1 ∧
      s'.stk 2 = (HvdH.ofList (t2.map HvdH.ofList)).enc ++ Z2 ∧
      s'.stk 3 = (HvdH.ofList ((HvdH.ofList (([] : List HvdH.Val) ++ r2)) ::
        Racc.map HvdH.ofList)).enc ++ Z3 ∧
      s'.reg Work.SynFFT.zF = HvdH.Glyph.cons ∧
      s'.stk 4 = X 4 ∧ s'.stk 5 = X 5 ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 → s'.stk k = X k) := by
  -- The first group is exhausted: stack `1` carries the `nil` cell of `ofList []`.
  have h1' : X 1 = HvdH.Glyph.nil :: Z1 := h1
  -- ## Step 1: `peek 1 zP` reads `nil`, which is `≠ cons`, so the loop body takes its *second*
  -- branch.
  set g₁ : HvdH.Reg → HvdH.Glyph := Function.update g zP HvdH.Glyph.nil with hg₁
  have hpeek1 : Work.Layout.Ev main (.peek 1 zP) ⟨g, X⟩ ⟨g₁, X⟩ 1 := by
    have h := Work.Layout.ev_peek' main 1 zP g X
    rw [h1'] at h
    simpa [hg₁] using h
  have hg₁ne : g₁ zP ≠ HvdH.Glyph.cons := by
    simp only [hg₁, Function.update_self]
    exact gnil_ne_cons
  -- ## Step 2: `peek 2 zP` reads `cons` (the second group still has rows).
  set g₂ : HvdH.Reg → HvdH.Glyph := Function.update g₁ zP HvdH.Glyph.cons with hg₂
  have hpeek2 : Work.Layout.Ev main (.peek 2 zP) ⟨g₁, X⟩ ⟨g₂, X⟩ 1 := by
    have h := Work.Layout.ev_peek' main 2 zP g₁ X
    rw [h2] at h
    simpa [hg₂] using h
  have hg₂val : g₂ zP = HvdH.Glyph.cons := by
    simp only [hg₂, Function.update_self]
  -- ## Step 3: `pushConst 0 Glyph.nil` — push the empty row `ofList []` on the value stack.
  obtain ⟨s₃, n₃, hEv₃, hn₃, h3s0, h3fr, _, _⟩ :=
    Work.Layout.pushConst_ev (main := main) (k := 0) (cst := HvdH.Glyph.nil) (g := g₂) (X := X)
  -- ## Step 4: `pop 2 rA` strips the `cons` cell of the second group, exposing the row `r2`.
  have h3s2 : s₃.stk 2 = X 2 := h3fr 2 (by decide)
  have hhead2 : (s₃.stk 2).headD HvdH.Glyph.eos = HvdH.Glyph.cons := by
    rw [h3s2, h2]; rfl
  have htail2 : (s₃.stk 2).tail =
      (HvdH.ofList r2).enc ++ ((HvdH.ofList (t2.map HvdH.ofList)).enc ++ Z2) := by
    rw [h3s2, h2]; rfl
  set X₄ : HvdH.Stk → List HvdH.Glyph := Function.update s₃.stk 2
    ((HvdH.ofList r2).enc ++ ((HvdH.ofList (t2.map HvdH.ofList)).enc ++ Z2)) with hX₄
  set g₄ : HvdH.Reg → HvdH.Glyph := Function.update s₃.reg rA HvdH.Glyph.cons with hg₄
  have hpopv : Work.Layout.Ev main (.pop 2 rA) s₃ ⟨g₄, X₄⟩ 1 := by
    have h := Work.Layout.ev_pop' main 2 rA s₃.reg s₃.stk
    rw [hhead2, htail2] at h
    simpa [hg₄, hX₄] using h
  -- ## Step 5: `mvVal 2 0 4 5` moves the row `r2` on top of the pushed empty row.
  have hX₄0 : X₄ 0 = HvdH.Glyph.nil :: X 0 := by
    simp only [hX₄, Function.update_of_ne (by decide : (0 : HvdH.Stk) ≠ 2)]
    exact h3s0
  have hX₄2 : X₄ 2 = (HvdH.ofList r2).enc ++
      ((HvdH.ofList (t2.map HvdH.ofList)).enc ++ Z2) := by
    simp only [hX₄, Function.update_self]
  obtain ⟨s₅, n₅, hEv₅, hn₅, h5a, h5b, h5c, h5d, h5fr⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 2) (b := 0) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := g₄) (X := X₄) hX₄2 hX₄0
  -- ## Step 6: the merge gadget, with the pair `(r2, [])` on the value stack.
  have hz0 : s₅.stk 0 =
      HvdH.encs (HvdH.ofList r2 :: HvdH.ofList ([] : List HvdH.Val) :: rest) ++ R := by
    rw [h5b]
    change (HvdH.ofList r2).enc ++ ([HvdH.Glyph.nil] ++ X 0) =
      HvdH.encs (HvdH.ofList r2 :: HvdH.ofList ([] : List HvdH.Val) :: rest) ++ R
    rw [h0, Work.Kernel.encs_cons, Work.Kernel.encs_cons,
      show (HvdH.ofList ([] : List HvdH.Val)).enc = [HvdH.Glyph.nil] from rfl]
    simp only [List.append_assoc]
  have hs33 : s₃.stk 3 = X 3 := h3fr 3 (by decide)
  have hX₄3 : X₄ 3 = s₃.stk 3 := by
    simp only [hX₄, Function.update_of_ne (by decide : (3 : HvdH.Stk) ≠ 2)]
  have hz3 : s₅.stk 3 = (HvdH.ofList (Racc.map HvdH.ofList)).enc ++ Z3 := by
    rw [h5fr 3 (by decide) (by decide) (by decide) (by decide), hX₄3, hs33, h3]
  obtain ⟨s₆, n₆, hEv₆, hn₆, h6a, h6b, h6c, h6d, h6e, h6fr⟩ :=
    Work.SynFFT.zMer_ev (main := main) (zApp := zApp) (KA := KA) (f := zF) hApp
      (rest := rest) (R := R) (r₁ := r2) (r₂ := ([] : List HvdH.Val))
      (Racc := Racc) (Z3 := Z3) (g := s₅.reg) (X := s₅.stk) hz0 hz3
  -- ## Assembly of the four commands of the branch
  have hbranch : Work.Layout.Ev main (Work.Layout.seqs [pushConst 0 HvdH.Glyph.nil, .pop 2 rA,
      Work.Layout.mvVal 2 0 4 5, zMer zApp zF]) ⟨g₂, X⟩ s₆ (n₃ + (1 + (n₅ + n₆))) :=
    Ev.seqs_cons hEv₃ (Ev.seqs_cons hpopv (Ev.seqs_cons hEv₅ hEv₆))
  have hite2 : Work.Layout.Ev main (.ite zP HvdH.Glyph.cons
      (Work.Layout.seqs [pushConst 0 HvdH.Glyph.nil, .pop 2 rA, Work.Layout.mvVal 2 0 4 5,
        zMer zApp zF])
      (.set zF HvdH.Glyph.eos)) ⟨g₂, X⟩ s₆ (n₃ + (1 + (n₅ + n₆)) + 1) :=
    Ev.iteT hg₂val hbranch
  have hseq2 : Work.Layout.Ev main (Work.Layout.seqs [.peek 2 zP, .ite zP HvdH.Glyph.cons
      (Work.Layout.seqs [pushConst 0 HvdH.Glyph.nil, .pop 2 rA, Work.Layout.mvVal 2 0 4 5,
        zMer zApp zF])
      (.set zF HvdH.Glyph.eos)]) ⟨g₁, X⟩ s₆ (1 + (n₃ + (1 + (n₅ + n₆)) + 1)) :=
    Ev.seqs_cons hpeek2 hite2
  have hite1 : Work.Layout.Ev main (.ite zP HvdH.Glyph.cons
      (Work.Layout.seqs [.pop 1 rA, .peek 2 zP, .ite zP HvdH.Glyph.cons
        (Work.Layout.seqs [.pop 2 rA, Work.Layout.mvVal 2 0 4 5, Work.Layout.mvVal 1 0 4 5,
          zMer zApp zF])
        (Work.Layout.seqs [pushConst 0 HvdH.Glyph.nil, Work.Layout.mvVal 1 0 4 5,
          zMer zApp zF])])
      (Work.Layout.seqs [.peek 2 zP, .ite zP HvdH.Glyph.cons
        (Work.Layout.seqs [pushConst 0 HvdH.Glyph.nil, .pop 2 rA, Work.Layout.mvVal 2 0 4 5,
          zMer zApp zF])
        (.set zF HvdH.Glyph.eos)])) ⟨g₁, X⟩ s₆ ((1 + (n₃ + (1 + (n₅ + n₆)) + 1)) + 1) :=
    Ev.iteF hg₁ne hseq2
  have hbody : Work.Layout.Ev main (Work.SynFFT.zBody zApp) ⟨g, X⟩ s₆
      (1 + ((1 + (n₃ + (1 + (n₅ + n₆)) + 1)) + 1)) := by
    unfold Work.SynFFT.zBody
    exact Ev.seqs_cons hpeek1 hite1
  -- ## The invariant in the final state
  have hstk0 : s₆.stk 0 = X 0 := by rw [h6a, h0]
  have hstk2 : s₆.stk 2 = (HvdH.ofList (t2.map HvdH.ofList)).enc ++ Z2 := by
    rw [h6fr 2 (by decide) (by decide) (by decide) (by decide), h5a]
  have hstk3 : s₆.stk 3 = (HvdH.ofList ((HvdH.ofList (([] : List HvdH.Val) ++ r2)) ::
      Racc.map HvdH.ofList)).enc ++ Z3 := by
    rw [h6b]
    simp
  have hstk1 : s₆.stk 1 = X 1 := by
    simp only [h6fr 1 (by decide) (by decide) (by decide) (by decide),
      h5fr 1 (by decide) (by decide) (by decide) (by decide),
      hX₄, Function.update_of_ne (by decide : (1 : HvdH.Stk) ≠ 2),
      h3fr 1 (by decide : (1 : HvdH.Stk) ≠ 0)]
  have hstk4 : s₆.stk 4 = X 4 := by
    simp only [h6d, h5c, hX₄, Function.update_of_ne (by decide : (4 : HvdH.Stk) ≠ 2),
      h3fr 4 (by decide : (4 : HvdH.Stk) ≠ 0)]
  have hstk5 : s₆.stk 5 = X 5 := by
    simp only [h6e, h5d, hX₄, Function.update_of_ne (by decide : (5 : HvdH.Stk) ≠ 2),
      h3fr 5 (by decide : (5 : HvdH.Stk) ≠ 0)]
  have hframe : ∀ k : HvdH.Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 →
      s₆.stk k = X k := by
    intro k hk0 hk1 hk2 hk3 hk4 hk5
    simp only [h6fr k hk0 hk3 hk4 hk5, h5fr k hk2 hk0 hk4 hk5, hX₄,
      Function.update_of_ne hk2, h3fr k hk0]
  refine ⟨s₆, 1 + ((1 + (n₃ + (1 + (n₅ + n₆)) + 1)) + 1), hbody, ?_, hstk0, hstk1,
    hstk2, hstk3, h6c, hstk4, hstk5, hframe⟩
  -- ## Cost
  have hstep : Work.SynFFT.zStepCost KA [] (r2 :: t2) =
      (KA + 100) * (HvdH.vsz (HvdH.ofList r2) + 1) := by
    simp [Work.SynFFT.zStepCost, Work.SynFFT.zBump_nil, Work.SynFFT.zBump_cons]
  rw [hstep, Nat.add_mul]
  have hv : HvdH.vsz (HvdH.ofList ([] : List HvdH.Val)) = 1 := rfl
  rw [hv] at hn₆
  omega

end Work.SynFFT
