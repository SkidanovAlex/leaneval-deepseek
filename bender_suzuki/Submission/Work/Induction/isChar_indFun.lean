import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.Basic
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.exists_nat_cfInner_resFun
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.CharCore.isChar_iff_exists_nat_coeffs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- **Induction of an irreducible character is a character.**  `indFun H θ` is a class function
-- (`Work.Induction.isClassFun_indFun`), so `Work.CharCore.classFun_eq_sum_irr` expands it as
-- `∑_{χ ∈ Irr G} ⟨indFun H θ, χ⟩ • χ`; Frobenius reciprocity
-- (`Work.Induction.frobenius_reciprocity`, applicable because `χ ∈ Irr G` is a class function)
-- gives `⟨indFun H θ, χ⟩ = ⟨θ, Res_H^G χ⟩_H = conj ⟨Res_H^G χ, θ⟩_H`, and
-- `⟨Res_H^G χ, θ⟩_H ∈ ℕ` by `Work.Induction.exists_nat_cfInner_resFun`.  Hence all the
-- coefficients are natural numbers and `Work.CharCore.isChar_iff_exists_nat_coeffs` concludes.
theorem isChar_indFun_irr {G : Type*} [Group G] [Fintype G] {H : Subgroup G} {θ : H → ℂ}
    (hθ : θ ∈ Work.CharCore.Irr H) :
    Work.CharCore.IsChar (Work.Induction.indFun H θ) := by
  classical
  -- For each `χ ∈ Irr G`, the multiplicity of `χ` in `indFun H θ` is a natural number.
  choose n hn using fun χ : ↥(Work.CharCore.Irr G) =>
    exists_nat_cfInner_resFun (χ := (χ : G → ℂ)) χ.2 (θ := θ) hθ
  have hkey : ∀ χ : ↥(Work.CharCore.Irr G),
      Work.CharCore.cfInner (indFun H θ) (χ : G → ℂ) = (n χ : ℂ) := by
    intro χ
    have hχc : Work.CharCore.IsClassFun (χ : G → ℂ) :=
      Work.CharCore.isClassFun_of_mem_Irr χ.2
    rw [frobenius_reciprocity H θ (χ : G → ℂ) hχc]
    rw [Work.CharCore.cfInner_conj_symm, hn χ]
    simp
  rw [Work.CharCore.isChar_iff_exists_nat_coeffs]
  refine ⟨n, ?_⟩
  rw [Work.CharCore.classFun_eq_sum_irr (isClassFun_indFun H θ)]
  rw [Finset.sum_subtype (CharCore.Irr G) (fun x => Iff.rfl)
        (fun χ => Work.CharCore.cfInner (indFun H θ) χ • χ)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [hkey χ]

-- **Induction of a character is a character** (`Work.CharCore.IsChar φ` is
-- `φ ∈ AddSubmonoid.closure (Irr H)`).  Proof: `hφ` gives `φ = ∑_{θ ∈ Irr H} n θ • θ`
-- (`Work.CharCore.isChar_iff_exists_nat_coeffs`); by linearity of `indFun`
-- (`Work.Induction.indFun_sum` and `Work.Induction.indFun_smul`, in
-- `Submission/Work/Induction/Basic.lean`) it suffices to show `IsChar (indFun H θ)` for
-- `θ ∈ Irr H`, which is `Work.Induction.isChar_indFun_irr` above.
theorem isChar_indFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G} {φ : H → ℂ}
    (hφ : Work.CharCore.IsChar φ) : Work.CharCore.IsChar (Work.Induction.indFun H φ) := by
  classical
  obtain ⟨c, hc⟩ := Work.CharCore.isChar_iff_exists_nat_coeffs.mp hφ
  rw [hc, indFun_sum]
  refine Work.CharCore.IsChar.sum (fun θ _ => ?_)
  rw [indFun_smul]
  simpa only [Nat.cast_smul_eq_nsmul] using
    Work.CharCore.IsChar.nsmul (isChar_indFun_irr θ.2) (c θ)

end Work.Induction
