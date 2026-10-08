import Mathlib
import Submission.Work.Clifford.classFun_eq_zero_of_orthogonal
import Submission.Work.Clifford.CFun
import Submission.Work.CharCore.mem_Irr_iff_fdrep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.exists_irr_constituent_resFun`

Every irreducible complex character `χ` of a finite group `G` has an irreducible constituent on
any subgroup `H ≤ G`: there is `ψ ∈ Irr H` with `⟪Res_H^G χ, ψ⟫ ≠ 0`.

The argument avoids the decomposition theory of `Res_H^G χ` altogether.  The restriction
`Res_H^G χ` is a class function on `H`, and it is non-zero because `χ 1 = χ(1) ≠ 0`.  If *no*
irreducible character of `H` were a constituent of it, then it would be a class function
orthogonal to every element of `Irr H`, hence zero by
`Work.Clifford.classFun_eq_zero_of_orthogonal` — a contradiction.

The only input beyond the orthogonality criterion is that the degree `χ 1` of an irreducible
character is non-zero, for which we use the `Work.CharCore` development
(`Work.CharCore.irrDeg_spec`, `Work.CharCore.irrDeg_ne_zero`) after identifying
`Work.Clifford.Irr` with the `Work.CharCore` character set through
`Work.CharCore.mem_Irr_iff_fdrep`.
-/

noncomputable section

open Classical

namespace Work.Clifford

/-- The restriction of a class function on `G` to a subgroup `H ≤ G` is a class function on `H`. -/
theorem isClassFun_resFun {G : Type*} [Group G] {H : Subgroup G} {f : G → ℂ}
    (hf : IsClassFun f) : IsClassFun (resFun H f) := by
  intro a b
  simpa using hf a b

theorem exists_irr_constituent_resFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype H]
    {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) :
    ∃ ψ : H → ℂ, ψ ∈ Work.Clifford.Irr H ∧
      Work.Clifford.IsConstituentOf ψ (Work.Clifford.resFun H χ) := by
  by_contra hcon
  push Not at hcon
  -- `Res_H^G χ` is a class function on `H`.
  have hclass : IsClassFun (resFun H χ) :=
    isClassFun_resFun (IsClassFun.of_mem_Irr hχ)
  -- If it had no irreducible constituent, it would be orthogonal to all of `Irr H`, hence zero.
  have horth : ∀ ψ : H → ℂ, ψ ∈ Irr H → cfInner (resFun H χ) ψ = 0 := by
    intro ψ hψ
    by_contra hne
    exact hcon ψ hψ hne
  have hzero : resFun H χ = 0 := classFun_eq_zero_of_orthogonal hclass horth
  -- But it is non-zero, its value at `1` being the degree `χ 1 ≠ 0`.
  obtain ⟨V, hV, hχeq⟩ := hχ
  have hC : χ ∈ Work.CharCore.Irr G :=
    (Work.CharCore.mem_Irr_iff_fdrep χ).mpr ⟨V, hV, hχeq⟩
  have hchi1 : χ 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hC]
    exact Work.CharCore.irrDeg_ne_zero hC
  have h1 : resFun H χ 1 ≠ 0 := by
    simpa using hchi1
  rw [hzero] at h1
  exact h1 rfl

end Work.Clifford
