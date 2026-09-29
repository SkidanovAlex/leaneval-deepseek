import Mathlib
import Submission.Work.IntLib.Shift.Defs

namespace Work.IntLib.Shift

/-- `cleanup` unfolded into the seven successive `clearAll` calls. -/
theorem cleanup_unfold :
    cleanup = .seq (clearAll sSg rZ rJ)
      (.seq (clearAll sM rZ rJ)
        (.seq (clearAll sK rZ rJ)
          (.seq (clearAll sP rZ rJ)
            (.seq (clearAll sA rZ rJ)
              (.seq (clearAll sT rZ rJ) (clearAll sT2 rZ rJ)))))) := rfl


theorem cleanup_ev (main : HvdH.Cmd) (Sg M Kb Pl A T T2 : List HvdH.Glyph)
    (JSg JM JK JP JA JT JT2 : List HvdH.Glyph) (s : HvdH.State)
    (hSg : ∀ h ∈ Sg, h ≠ Work.IntLib.Shift.gmk Work.IntLib.Shift.sSg)
    (hM : ∀ h ∈ M, h ≠ Work.IntLib.Shift.gmk Work.IntLib.Shift.sM)
    (hKb : ∀ h ∈ Kb, h ≠ Work.IntLib.Shift.gmk Work.IntLib.Shift.sK)
    (hP : ∀ h ∈ Pl, h ≠ Work.IntLib.Shift.gmk Work.IntLib.Shift.sP)
    (hA : ∀ h ∈ A, h ≠ Work.IntLib.Shift.gmk Work.IntLib.Shift.sA)
    (hT : ∀ h ∈ T, h ≠ Work.IntLib.Shift.gmk Work.IntLib.Shift.sT)
    (hT2 : ∀ h ∈ T2, h ≠ Work.IntLib.Shift.gmk Work.IntLib.Shift.sT2)
    (eSg : s.stk Work.IntLib.Shift.sSg = Sg ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sSg :: JSg)
    (eM : s.stk Work.IntLib.Shift.sM = M ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: JM)
    (eKb : s.stk Work.IntLib.Shift.sK = Kb ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sK :: JK)
    (eP : s.stk Work.IntLib.Shift.sP = Pl ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sP :: JP)
    (eA : s.stk Work.IntLib.Shift.sA = A ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sA :: JA)
    (eT : s.stk Work.IntLib.Shift.sT = T ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sT :: JT)
    (eT2 : s.stk Work.IntLib.Shift.sT2 = T2 ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sT2 :: JT2) :
    ∃ (s' : HvdH.State) (n : ℕ), HvdH.Eval main Work.IntLib.Shift.cleanup s s' n ∧
      n ≤ 5 * (Sg.length + M.length + Kb.length + Pl.length + A.length + T.length + T2.length + 7) + 40 ∧
      s'.stk Work.IntLib.Shift.sSg = JSg ∧ s'.stk Work.IntLib.Shift.sM = JM ∧
      s'.stk Work.IntLib.Shift.sK = JK ∧ s'.stk Work.IntLib.Shift.sP = JP ∧
      s'.stk Work.IntLib.Shift.sA = JA ∧ s'.stk Work.IntLib.Shift.sT = JT ∧
      s'.stk Work.IntLib.Shift.sT2 = JT2 ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.Shift.sSg → j ≠ Work.IntLib.Shift.sM →
        j ≠ Work.IntLib.Shift.sK → j ≠ Work.IntLib.Shift.sP → j ≠ Work.IntLib.Shift.sA →
        j ≠ Work.IntLib.Shift.sT → j ≠ Work.IntLib.Shift.sT2 → s'.stk j = s.stk j) := by
  -- step 1: clear stack `sSg`
  obtain ⟨s1, m1, he1, hm1, hs1, ho1⟩ :=
    clearAll_ev (main := main) sSg rZ rJ Sg JSg s.reg s.stk hSg eSg
  have heM : s1.stk sM = M ++ gmk sM :: JM := by
    rw [ho1 sM (by decide)]; exact eM
  -- step 2: clear stack `sM`
  obtain ⟨s2, m2, he2, hm2, hs2, ho2⟩ :=
    clearAll_ev (main := main) sM rZ rJ M JM s1.reg s1.stk hM heM
  have u2 : ∀ j, j ≠ sSg → j ≠ sM → s2.stk j = s.stk j := by
    intro j h1 h2; rw [ho2 j h2, ho1 j h1]
  have heKb : s2.stk sK = Kb ++ gmk sK :: JK := by
    rw [u2 sK (by decide) (by decide)]; exact eKb
  -- step 3: clear stack `sK`
  obtain ⟨s3, m3, he3, hm3, hs3, ho3⟩ :=
    clearAll_ev (main := main) sK rZ rJ Kb JK s2.reg s2.stk hKb heKb
  have u3 : ∀ j, j ≠ sSg → j ≠ sM → j ≠ sK → s3.stk j = s.stk j := by
    intro j h1 h2 h3; rw [ho3 j h3, u2 j h1 h2]
  have hePl : s3.stk sP = Pl ++ gmk sP :: JP := by
    rw [u3 sP (by decide) (by decide) (by decide)]; exact eP
  -- step 4: clear stack `sP`
  obtain ⟨s4, m4, he4, hm4, hs4, ho4⟩ :=
    clearAll_ev (main := main) sP rZ rJ Pl JP s3.reg s3.stk hP hePl
  have u4 : ∀ j, j ≠ sSg → j ≠ sM → j ≠ sK → j ≠ sP → s4.stk j = s.stk j := by
    intro j h1 h2 h3 h4; rw [ho4 j h4, u3 j h1 h2 h3]
  have heA : s4.stk sA = A ++ gmk sA :: JA := by
    rw [u4 sA (by decide) (by decide) (by decide) (by decide)]; exact eA
  -- step 5: clear stack `sA`
  obtain ⟨s5, m5, he5, hm5, hs5, ho5⟩ :=
    clearAll_ev (main := main) sA rZ rJ A JA s4.reg s4.stk hA heA
  have u5 : ∀ j, j ≠ sSg → j ≠ sM → j ≠ sK → j ≠ sP → j ≠ sA → s5.stk j = s.stk j := by
    intro j h1 h2 h3 h4 h5; rw [ho5 j h5, u4 j h1 h2 h3 h4]
  have heT : s5.stk sT = T ++ gmk sT :: JT := by
    rw [u5 sT (by decide) (by decide) (by decide) (by decide) (by decide)]; exact eT
  -- step 6: clear stack `sT`
  obtain ⟨s6, m6, he6, hm6, hs6, ho6⟩ :=
    clearAll_ev (main := main) sT rZ rJ T JT s5.reg s5.stk hT heT
  have u6 : ∀ j, j ≠ sSg → j ≠ sM → j ≠ sK → j ≠ sP → j ≠ sA → j ≠ sT →
      s6.stk j = s.stk j := by
    intro j h1 h2 h3 h4 h5 h6; rw [ho6 j h6, u5 j h1 h2 h3 h4 h5]
  have heT2 : s6.stk sT2 = T2 ++ gmk sT2 :: JT2 := by
    rw [u6 sT2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact eT2
  -- step 7: clear stack `sT2`
  obtain ⟨s7, m7, he7, hm7, hs7, ho7⟩ :=
    clearAll_ev (main := main) sT2 rZ rJ T2 JT2 s6.reg s6.stk hT2 heT2
  -- later steps do not touch the earlier stacks: transport the results to `s7`
  have r1 : ∀ j, j ≠ sM → j ≠ sK → j ≠ sP → j ≠ sA → j ≠ sT → j ≠ sT2 →
      s7.stk j = s1.stk j := by
    intro j h2 h3 h4 h5 h6 h7
    rw [ho7 j h7, ho6 j h6, ho5 j h5, ho4 j h4, ho3 j h3, ho2 j h2]
  have r2 : ∀ j, j ≠ sK → j ≠ sP → j ≠ sA → j ≠ sT → j ≠ sT2 → s7.stk j = s2.stk j := by
    intro j h3 h4 h5 h6 h7; rw [ho7 j h7, ho6 j h6, ho5 j h5, ho4 j h4, ho3 j h3]
  have r3 : ∀ j, j ≠ sP → j ≠ sA → j ≠ sT → j ≠ sT2 → s7.stk j = s3.stk j := by
    intro j h4 h5 h6 h7; rw [ho7 j h7, ho6 j h6, ho5 j h5, ho4 j h4]
  have r4 : ∀ j, j ≠ sA → j ≠ sT → j ≠ sT2 → s7.stk j = s4.stk j := by
    intro j h5 h6 h7; rw [ho7 j h7, ho6 j h6, ho5 j h5]
  have r5 : ∀ j, j ≠ sT → j ≠ sT2 → s7.stk j = s5.stk j := by
    intro j h6 h7; rw [ho7 j h7, ho6 j h6]
  have r6 : ∀ j, j ≠ sT2 → s7.stk j = s6.stk j := ho7
  have gSg : s7.stk sSg = JSg := by
    rw [r1 sSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)];
      exact hs1
  have gM : s7.stk sM = JM := by
    rw [r2 sM (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs2
  have gK : s7.stk sK = JK := by
    rw [r3 sK (by decide) (by decide) (by decide) (by decide)]; exact hs3
  have gP : s7.stk sP = JP := by
    rw [r4 sP (by decide) (by decide) (by decide)]; exact hs4
  have gA : s7.stk sA = JA := by
    rw [r5 sA (by decide) (by decide)]; exact hs5
  have gT : s7.stk sT = JT := by
    rw [r6 sT (by decide)]; exact hs6
  have gT2 : s7.stk sT2 = JT2 := hs7
  have u7 : ∀ j, j ≠ sSg → j ≠ sM → j ≠ sK → j ≠ sP → j ≠ sA → j ≠ sT → j ≠ sT2 →
      s7.stk j = s.stk j := by
    intro j h1 h2 h3 h4 h5 h6 h7; rw [ho7 j h7, u6 j h1 h2 h3 h4 h5 h6]
  refine ⟨s7, m1 + (m2 + (m3 + (m4 + (m5 + (m6 + m7))))), ?_, ?_, gSg, gM, gK, gP, gA, gT, gT2,
    u7⟩
  · rw [cleanup_unfold]
    exact HvdH.Eval.seq he1 (HvdH.Eval.seq he2 (HvdH.Eval.seq he3 (HvdH.Eval.seq he4
      (HvdH.Eval.seq he5 (HvdH.Eval.seq he6 he7)))))
  · omega

end Work.IntLib.Shift
