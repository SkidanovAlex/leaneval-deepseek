import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.exists_nat_cfInner_resFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- The multiplicity of an irreducible character of `G` in the induction of an irreducible
-- character of `H` is a natural number: for `θ ∈ Irr H` and `χ ∈ Irr G`,
-- `⟨Ind_H^G θ, χ⟩_G = |G|⁻¹ ∑_g indFun H θ g * conj (χ g)` is a natural number.
-- Proof: Frobenius reciprocity (`Work.Induction.frobenius_reciprocity`) gives
-- `⟨Ind_H^G θ, χ⟩_G = ⟨θ, Res_H^G χ⟩_H = conj ⟨Res_H^G χ, θ⟩_H` (using `χ ∈ Irr G` is a class
-- function), and `⟨Res_H^G χ, θ⟩_H ∈ ℕ` by `Work.Induction.exists_nat_cfInner_resFun`.
theorem exists_nat_cfInner_indFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    {θ : H → ℂ} (hθ : θ ∈ Work.CharCore.Irr H) {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G) :
    ∃ n : ℕ, Work.CharCore.cfInner (Work.Induction.indFun H θ) χ = n := by
  obtain ⟨n, hn⟩ := Work.Induction.exists_nat_cfInner_resFun hχ hθ
  refine ⟨n, ?_⟩
  rw [Work.Induction.frobenius_reciprocity H θ χ
        (Work.CharCore.isClassFun_of_mem_Irr hχ),
      Work.CharCore.cfInner_conj_symm, hn]
  simp

end Work.Induction
