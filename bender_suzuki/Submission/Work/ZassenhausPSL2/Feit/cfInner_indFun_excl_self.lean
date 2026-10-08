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

namespace Work.ZassenhausPSL2.Feit

open Classical

theorem cfInner_indFun_excl_self {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) {χ : H → ℂ}
    (hχ : χ ∈ Submission.Blueprint.excludingKernel H Q) :
    Work.CharCore.cfInner (Work.Induction.indFun H χ) (Work.Induction.indFun H χ) =
      1 + (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
  classical
  -- F2a: the degree of `χ` is `|D|`.
  obtain ⟨hχ1, -⟩ := excl_degree_support h hz h2 hab hχ
  -- `χ` is an irreducible character of `H`.
  have hχIrr : χ ∈ Work.CharCore.Irr H := (mem_excludingKernel_iff.mp hχ).1
  -- Frobenius reciprocity: `⟨Ind χ, Ind χ⟩_G = ⟨χ, Res (Ind χ)⟩_H`.
  rw [Work.Induction.frobenius_reciprocity H χ (Work.Induction.indFun H χ)
    (Work.Induction.isClassFun_indFun H χ)]
  -- The `H`-function `F` which is `|H|` at the identity and `0` elsewhere.
  let F : ↥H → ℂ := fun x => if x = 1 then (Nat.card ↥H : ℂ) else 0
  -- F3 (`indFun_excl_apply`): `Res_H^G (Ind_H^G χ) = χ + F`.
  have hres : Work.Induction.resFun H (Work.Induction.indFun H χ) = χ + F := by
    funext x
    rw [Work.Induction.resFun_apply, Pi.add_apply,
      Work.ZassenhausPSL2.Feit.indFun_excl_apply h hz h2 hab hχ x]
  rw [hres, Work.CharCore.cfInner_add_right,
    Work.CharCore.irr_orthonormal χ χ hχIrr hχIrr, ite_eq_left rfl]
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
  rw [hFv, hχ1]

end Work.ZassenhausPSL2.Feit
