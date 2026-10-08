import Mathlib
import Submission.Work.Induction.Defs
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

-- **Restriction of a character is a character** (`Work.CharCore.IsChar φ` is
-- `φ ∈ AddSubmonoid.closure (Irr G)`, i.e. a non-negative integral combination of irreducible
-- characters).  Proof: `hφ` gives `φ = ∑_{χ ∈ Irr G} n χ • χ`
-- (`Work.CharCore.isChar_iff_exists_nat_coeffs`); `resFun` is additive, so it suffices to show
-- `IsChar (resFun H χ)` for `χ ∈ Irr G`; expanding `resFun H χ` in the orthonormal basis
-- `Irr H` (`Work.CharCore.classFun_eq_sum_irr`, using `Work.Induction.isClassFun_resFun`), its
-- coefficients are `⟨Res_H^G χ, θ⟩_H`, natural numbers by
-- `Work.Induction.exists_nat_cfInner_resFun`; then `Work.CharCore.isChar_iff_exists_nat_coeffs`
-- concludes.
theorem isChar_resFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G} {φ : G → ℂ}
    (hφ : Work.CharCore.IsChar φ) : Work.CharCore.IsChar (Work.Induction.resFun H φ) := by
  classical
  -- It suffices to prove the claim for `χ ∈ Irr G`.
  have hχchar : ∀ χ : G → ℂ, χ ∈ Work.CharCore.Irr G →
      Work.CharCore.IsChar (resFun H χ) := by
    intro χ hχ
    -- `Res_H^G χ` is a class function.
    have hcf : IsClassFun (resFun H χ) :=
      isClassFun_resFun (Work.CharCore.isClassFun_of_mem_Irr hχ)
    -- Expand it in the orthonormal basis `Irr H`.
    have hexp := Work.CharCore.classFun_eq_sum_irr (G := H) hcf
    refine (Work.CharCore.isChar_iff_exists_nat_coeffs (G := H)).mpr ?_
    -- Its coefficients `⟨Res_H^G χ, θ⟩_H` are natural numbers.
    let m : ↥(Work.CharCore.Irr H) → ℕ := fun θ =>
      Classical.choose (Work.Induction.exists_nat_cfInner_resFun (G := G) hχ θ.2)
    have hm : ∀ θ : ↥(Work.CharCore.Irr H),
        Work.CharCore.cfInner (resFun H χ) (θ : H → ℂ) = (m θ : ℂ) := fun θ =>
      Classical.choose_spec (Work.Induction.exists_nat_cfInner_resFun (G := G) hχ θ.2)
    refine ⟨m, ?_⟩
    rw [hexp, Finset.sum_subtype (Work.CharCore.Irr H) (fun x => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro θ _
    rw [hm θ]
  -- The set of `ψ` whose restriction is a character is an additive submonoid of `G → ℂ`
  -- containing `Irr G`, hence contains the closure of `Irr G`.
  let T : AddSubmonoid (G → ℂ) :=
    { carrier := {ψ | Work.CharCore.IsChar (resFun H ψ)}
      zero_mem' := Work.CharCore.IsChar.zero (G := H)
      add_mem' := by
        intro f g hf hg
        change Work.CharCore.IsChar (resFun H (f + g))
        rw [resFun_add]
        exact Work.CharCore.IsChar.add hf hg }
  have hle : AddSubmonoid.closure ((Work.CharCore.Irr G : Finset (G → ℂ)) : Set (G → ℂ)) ≤ T := by
    rw [AddSubmonoid.closure_le]
    intro χ hχ
    exact hχchar χ hχ
  exact hle hφ

end Work.Induction
