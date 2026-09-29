import Submission.Work.IntLib.SqrtGcd.GcdProg
import Submission.Work.IntLib.SqrtGcd.gcdSetupEval
import Submission.Work.IntLib.SqrtGcd.gcdFinishEvalGen

/-!
# The gcd word

`Work.IntLib.SG.gcdWord` : `int a :: int b :: rest ↦ int (Int.gcd a b) :: rest` at cost
`K · (isz a + isz b)²`, obtained by composing the setup (`gcdSetupEval`) with the run + emit +
cleanup (`gcdFinishEvalGen`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

theorem gcdWord :
    ∃ (p : Cmd) (K : ℕ), ∀ main, BinOp main p (fun _ _ => True)
      (fun a b => (Int.gcd a b : ℤ)) (fun a b => K * (isz a + isz b) ^ 2) := by
  refine ⟨gcdProg, 1000000, ?_⟩
  intro main vs hpre s R hR
  obtain ⟨a, b, rest, rfl, -⟩ := hpre
  have hR' : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ (encs rest ++ R) := by
    rw [hR, Work.Kernel.encs_cons, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  obtain ⟨s1, m1, hev1, hm1, h01, hU1, hV1, hG1, hP1, hQ1, hR1, hS1, hfr1⟩ :=
    Work.IntLib.SqrtGcd.gcdSetupEval main a b (encs rest ++ R) s hR'
  obtain ⟨s2, m2, hev2, hm2, h02, hU2, hV2, hG2, hP2, hQ2, hR2, hS2, hfr2⟩ :=
    Work.IntLib.SqrtGcd.gcdFinishEvalGen main a b (encs rest ++ R)
      (s.stk sU) (s.stk sV) (s.stk sG) (s.stk sP) (s.stk sQ) (s.stk sR) (s.stk sS)
      s1 h01 hU1 hV1 hG1 hP1 hQ1 hR1 hS1
  refine ⟨.int (Int.gcd a b) :: rest, s2, m1 + m2, ⟨a, b, rest, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq hev1 hev2
  · have hx1 : 1 ≤ isz a + isz b := by
      have h2 : 2 ≤ isz a := by rw [isz_eq]; omega
      omega
    have hsq : (isz a + isz b + 1) * (isz a + isz b + 1)
        ≤ 4 * ((isz a + isz b) * (isz a + isz b)) := by nlinarith
    have hgoal : m1 + m2 ≤ 1000000 * (isz a + isz b) * (isz a + isz b) := by
      nlinarith [hm1, hm2, hsq]
    calc m1 + m2 ≤ 1000000 * (isz a + isz b) * (isz a + isz b) := hgoal
      _ = 1000000 * (isz a + isz b) ^ 2 := by ring
  · rw [h02, Work.Kernel.encs_cons, List.append_assoc]
  · intro k hk
    by_cases h1 : k = sU
    · rw [h1, hU2]
    by_cases h2 : k = sV
    · rw [h2, hV2]
    by_cases h3 : k = sG
    · rw [h3, hG2]
    by_cases h4 : k = sP
    · rw [h4, hP2]
    by_cases h5 : k = sQ
    · rw [h5, hQ2]
    by_cases h6 : k = sR
    · rw [h6, hR2]
    by_cases h7 : k = sS
    · rw [h7, hS2]
    · exact (hfr2 k hk h1 h2 h3 h4 h5 h6 h7).trans (hfr1 k hk h1 h2 h3 h4 h5 h6 h7)

end SG
end Work.IntLib
