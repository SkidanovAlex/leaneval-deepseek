import Mathlib
import Submission.Work.Kernel.Raw

namespace Work.Kernel

/-- `import Submission.Work.Kernel.Raw`, work in `namespace Work.Kernel`.  The program pops the single glyph `Glyph.cons`.  Helpers in this file must be named with the prefix `unconsV_`. -/
theorem unconsV : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ main : HvdH.Cmd, HvdH.WordR main prog
    (fun vs => ∃ a b rest, vs = HvdH.Val.cons a b :: rest)
    (fun vs out => ∃ a b rest, vs = HvdH.Val.cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K) := by
  refine ⟨HvdH.Cmd.pop 0 0, 1, ?_⟩
  intro main vs hvs s R hR
  obtain ⟨a, b, rest, rfl⟩ := hvs
  refine ⟨a :: b :: rest, HvdH.State.tPop s 0 0, 1, ⟨a, b, rest, rfl, rfl⟩,
    eval_pop main 0 0 s, le_rfl, ?_, ?_⟩
  · have h1 : (HvdH.State.tPop s 0 0).stk 0 = (s.stk 0).tail := by
      simp [HvdH.State.tPop]
    rw [h1, hR]
    simp [HvdH.Val.enc, encs_cons, List.append_assoc]
  · intro k hk
    simp [HvdH.State.tPop, HvdH.State.updStk, HvdH.State.updReg, hk]

end Work.Kernel
