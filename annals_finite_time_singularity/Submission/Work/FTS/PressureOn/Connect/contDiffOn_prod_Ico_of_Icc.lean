import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem contDiffOn_prod_Ico_of_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {T : ℝ} {g : E × ℝ → F}
    (h : ∀ S ∈ Set.Ioo 0 T, ContDiffOn ℝ n g (Set.univ ×ˢ Set.Icc 0 S)) :
    ContDiffOn ℝ n g (Set.univ ×ˢ Set.Ico 0 T) := by
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨y, t⟩ ⟨-, ht⟩
  obtain ⟨ht0, htT⟩ := ht
  -- pick an intermediate cutoff `S` with `t < S < T`
  obtain ⟨S, htS, hST⟩ : ∃ S : ℝ, t < S ∧ S < T := ⟨(t + T) / 2, by linarith, by linarith⟩
  have hS0 : 0 < S := lt_of_le_of_lt ht0 htS
  refine ⟨Set.univ ×ˢ Set.Ioo (-1) S, isOpen_univ.prod isOpen_Ioo, ⟨trivial, ?_⟩, ?_⟩
  · exact ⟨by linarith, htS⟩
  · refine (h S ⟨hS0, hST⟩).mono ?_
    rintro ⟨a, b⟩ ⟨⟨-, hb⟩, ⟨-, hb'⟩⟩
    exact ⟨trivial, ⟨hb.1, le_of_lt hb'.2⟩⟩

end Work.FTS.PressureOn.Connect
