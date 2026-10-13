import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.Wilkies.CG.C4a.Spec

namespace Work.WilE7.Dim

theorem basic_holds_basicSA {q r : ℕ} (c : WilkiesDesign.E.EAChain q r)
    (B : WilkiesDesign.E.Basic q r) :
    {y : Fin q → ℝ | B.holds c y} =
      WilkiesDesign.CG.C4a.BasicSA
        (fun y : Fin q → ℝ =>
          ∑ i : Fin B.eqs.length, (WilkiesDesign.E.eaEval c (B.eqs.get i) y) ^ 2)
        (fun (j : Fin B.pos.length) (y : Fin q → ℝ) =>
          WilkiesDesign.E.eaEval c (B.pos.get j) y) := by
  ext y
  simp only [Set.mem_ofPred_eq, WilkiesDesign.E.Basic.holds, WilkiesDesign.CG.C4a.BasicSA]
  constructor
  · rintro ⟨he, hp⟩
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun i _ => sq_nonneg _)]
      intro i _
      rw [he (B.eqs.get i) (List.get_mem _ _)]
      norm_num
    · intro j
      exact hp (B.pos.get j) (List.get_mem _ _)
  · rintro ⟨he, hp⟩
    refine ⟨?_, ?_⟩
    · intro f hf
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hf
      have h0 : (WilkiesDesign.E.eaEval c (B.eqs.get i) y) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (fun i _ => sq_nonneg _)).mp he i (Finset.mem_univ i)
      rw [← hi]
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h0
    · intro g hg
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
      rw [← hi]
      exact hp i

end Work.WilE7.Dim
