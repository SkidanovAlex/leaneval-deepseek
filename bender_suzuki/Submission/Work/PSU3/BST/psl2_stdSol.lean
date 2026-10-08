import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.PSU3.BenderST
import Submission.Work.PSU3.BenderST.psl2_standard_clause

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.BST

theorem psl2_stdSol (n : ℕ) (hn : 2 ≤ n) :
    ∃ s₀ r₀ : LeanEval.GroupTheory.Defs.PSL2Model n,
      s₀ ∈ (Submission.PSL2.pSL2BenderPair n hn).U ∧ orderOf s₀ = 2 ∧
      r₀ ∈ (Submission.PSL2.pSL2BenderPair n hn).U ∧
      (Submission.PSL2.pSL2BenderPair n hn).w * s₀ * (Submission.PSL2.pSL2BenderPair n hn).w
        = r₀⁻¹ * (Submission.PSL2.pSL2BenderPair n hn).w * r₀ ∧
      orderOf (s₀ * (Submission.PSL2.pSL2BenderPair n hn).w) = 3 := by
  classical
  -- The witness: the image `u₀` of the unipotent matrix `!![1,1;0,1]` in `PSL(2,2ⁿ)`,
  -- which lies in `U = range (unipotentPSLHom K)`.
  let u₀ : LeanEval.GroupTheory.Defs.PSL2Model n :=
    Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)
      (Multiplicative.ofAdd (1 : GaloisField 2 n))
  have hu₀ord : orderOf u₀ = 2 := Work.PSU3.BenderST.psl2_orderOf_unipotent_one n
  have hu₀U : u₀ ∈ (Submission.PSL2.pSL2BenderPair n hn).U :=
    MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (1 : GaloisField 2 n), rfl⟩
  have hu₀inv : u₀⁻¹ = u₀ := by
    apply inv_eq_of_mul_eq_one_right
    have h := pow_orderOf_eq_one u₀
    rw [hu₀ord] at h
    simpa [pow_two] using h
  -- `(u₀, u₀)` is a solution of the structure identity `w s w = r⁻¹ w r`
  have hconj : (Submission.PSL2.pSL2BenderPair n hn).w * u₀ *
        (Submission.PSL2.pSL2BenderPair n hn).w
      = u₀⁻¹ * (Submission.PSL2.pSL2BenderPair n hn).w * u₀ := by
    rw [hu₀inv]
    exact Work.PSU3.BenderST.psl2_weyl_conj_unipotent_one n
  exact ⟨u₀, u₀, hu₀U, hu₀ord, hu₀U, hconj,
    Work.PSU3.BenderST.psl2_orderOf_unipotent_one_mul_weyl n⟩

end Work.PSU3.BST
