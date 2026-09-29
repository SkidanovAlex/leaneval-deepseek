import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.specs
import Submission.Work.Resample.resAopNorm
import Submission.Work.Resample.resBopNorm
import Submission.Work.Resample.resampleIdentity
import Submission.Work.Resample.progTensorA
import Submission.Work.Resample.progTensorB

/-!
# Assembly of `HvdH.ResampleProp` (paper Theorem 4.1)

`resampleCore` assembles the area's Theorem 4.1 from the pieces:
`resAop`/`resBop` with `resAopNorm`/`resBopNorm` (M1), `resampleIdentity` (M2), and the two
tensoring programs `progTensorA`/`progTensorB` obtained from the uniform one-dimensional slice
words (`SliceSpecA`/`SliceSpecB`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- `resCost` is monotone in the cost constant (with `Cm` monotone). -/
theorem resCost_mono {Cm : ℕ → ℕ} (hC : Monotone Cm) {K K' : ℕ} (h : K ≤ K')
    (p α : ℕ) (ts : List ℕ) : resCost K Cm p α ts ≤ resCost K' Cm p α ts := by
  unfold resCost
  have h1 : Cm (K * p) ≤ Cm (K' * p) := hC (Nat.mul_le_mul_right p h)
  have h2 : K * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K * p) + p) ≤
      K' * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K' * p) + p) := by
    gcongr
  have h3 : K * ts.prod * p ^ 2 ≤ K' * ts.prod * p ^ 2 := by gcongr
  have h4 : K * ts.sum * (p + 1) ^ K ≤ K' * ts.sum * (p + 1) ^ K' := by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul h le_rfl
    · exact Nat.pow_le_pow_right (by omega) h
  exact add_le_add (add_le_add h2 h3) h4

/-- Paper Theorem 4.1, assembled from the two tensoring programs and the linear-algebraic facts. -/
theorem resampleCore (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib)
    (_DFT : HvdH.DFTMathProp) (RM : HvdH.ResMath1DProp)
    (hA : SliceSpecA KL IL LL FL RM) (hB : SliceSpecB KL IL LL FL RM) : HvdH.ResampleProp := by
  obtain ⟨progA, KA, hPA⟩ := progTensorA KL IL LL FL RM hA
  obtain ⟨progB, KB, hPB⟩ := progTensorB KL IL LL FL RM hB
  refine ⟨progA, progB, max KA KB, ?_⟩
  intro p α ss ts hpar
  refine ⟨resAop ss ts α, resBop ss ts α, resAopNorm p α ss ts hpar RM,
    resBopNorm p α ss ts hpar RM, resampleIdentity p α ss ts hpar RM, ?_⟩
  intro main N Cm hmon hmb hN
  exact ⟨KL.conseq main progA _ _ _ _ _ _
      (hPA main N Cm p α ss ts hpar hmon hmb
        (lt_of_le_of_lt (Nat.mul_le_mul_right p (le_max_left _ _)) hN))
      (fun _ h => h) (fun _ _ _ h => h)
      (fun _ _ => resCost_mono hmon (le_max_left _ _) p α ts),
    KL.conseq main progB _ _ _ _ _ _
      (hPB main N Cm p α ss ts hpar hmon hmb
        (lt_of_le_of_lt (Nat.mul_le_mul_right p (le_max_right _ _)) hN))
      (fun _ h => h) (fun _ _ _ h => h)
      (fun _ _ => resCost_mono hmon (le_max_right _ _) p α ts)⟩

end Work.Resample
