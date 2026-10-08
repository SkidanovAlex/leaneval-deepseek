import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.CFun
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.Induction.Defs
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.ZassenhausPSL2.Feit.excl_aux
import Submission.Work.ZassenhausPSL2.Feit.excl_degree_support
import Submission.Work.ZassenhausPSL2.Feit.indFun_excl_apply

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.Feit.cfInner_indFun_excl_ne` (Feit's leaf F4)

In a split rank-one Zassenhaus configuration `H = Q ⋊ D` (`D = twoPoint H t = H ⊓ Hᵗ`,
`Q ⊴ H`), for two **distinct** irreducible characters `χ ≠ χ'`, both non-trivial on `Q`
(i.e. both in `𝒮 = excludingKernel H Q`), the induced characters have inner product `|D|`:

`⟨Ind_H^G χ, Ind_H^G χ'⟩_G = |D|`.

Indeed, by Frobenius reciprocity the inner product is `⟨χ, Res_H^G (Ind_H^G χ')⟩_H`, and by
Feit's leaf F3 (`indFun_excl_apply`) one has `Res_H^G (Ind_H^G χ') = χ' + ρ_H`, the regular
character of `H` (here written `F`, the function which is `|H|` at `1` and `0` elsewhere).
Orthonormality of the irreducible characters gives `⟨χ, χ'⟩ = 0` for `χ ≠ χ'`, while
`⟨χ, ρ_H⟩ = χ 1 = |D|` because every member of `𝒮` has degree `|D|` (Feit's leaf F2a,
`excl_degree_support`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Classical

namespace Work.ZassenhausPSL2.Feit

theorem cfInner_indFun_excl_ne {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) {χ χ' : H → ℂ}
    (hχ : χ ∈ Submission.Blueprint.excludingKernel H Q)
    (hχ' : χ' ∈ Submission.Blueprint.excludingKernel H Q) (hne : χ ≠ χ') :
    Work.CharCore.cfInner (Work.Induction.indFun H χ) (Work.Induction.indFun H χ') =
      (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
  classical
  -- F2a: the degree of `χ` is `|D|`.
  obtain ⟨hχ1, -⟩ := excl_degree_support h hz h2 hab hχ
  -- `χ` and `χ'` are irreducible characters of `H`.
  have hχIrr : χ ∈ Work.CharCore.Irr H := (mem_excludingKernel_iff.mp hχ).1
  have hχ'Irr : χ' ∈ Work.CharCore.Irr H := (mem_excludingKernel_iff.mp hχ').1
  -- Frobenius reciprocity: `⟨Ind χ, Ind χ'⟩_G = ⟨χ, Res (Ind χ')⟩_H`.
  rw [Work.Induction.frobenius_reciprocity H χ (Work.Induction.indFun H χ')
    (Work.Induction.isClassFun_indFun H χ')]
  -- The `H`-function `F` which is `|H|` at the identity and `0` elsewhere.
  let F : ↥H → ℂ := fun x => if x = 1 then (Nat.card ↥H : ℂ) else 0
  -- F3 (`indFun_excl_apply`): `Res_H^G (Ind_H^G χ') = χ' + F`.
  have hres : Work.Induction.resFun H (Work.Induction.indFun H χ') = χ' + F := by
    funext x
    rw [Work.Induction.resFun_apply, Pi.add_apply,
      Work.ZassenhausPSL2.Feit.indFun_excl_apply h hz h2 hab hχ' x]
  rw [hres, Work.CharCore.cfInner_add_right,
    Work.CharCore.irr_orthonormal χ χ' hχIrr hχ'Irr, ite_eq_right hne]
  -- `⟨χ, F⟩ = χ 1 = |D|`, because `F` is supported at `1`.
  have hFv : Work.CharCore.cfInner χ F = χ 1 := by
    rw [Work.CharCore.cfInner_apply]
    have hsum : (∑ x : ↥H, χ x * starRingEnd ℂ (F x))
        = χ 1 * starRingEnd ℂ ((Nat.card ↥H : ℂ)) := by
      rw [Finset.sum_eq_single 1]
      · dsimp only [F]; simp
      · intro b _ hb; dsimp only [F]; simp [hb]
      · intro hh; exact absurd (Finset.mem_univ 1) hh
    rw [hsum, map_natCast]
    have hcard : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Nat.card_eq_fintype_card (α := ↥H), mul_comm (χ 1) (Fintype.card ↥H : ℂ),
      ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  rw [hFv, hχ1, zero_add]

end Work.ZassenhausPSL2.Feit
