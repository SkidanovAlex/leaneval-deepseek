import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.step9_global_sums
import Submission.Work.Induction.All
import Submission.Work.ZassenhausTwoGroup.zetaStar_norm
import Submission.Work.ZassenhausTwoGroup.card_H_eq
import Submission.Work.ZassenhausTwoGroup.card_quotient_eq
import Submission.Work.ZassenhausTwoGroup.indFun_Q_apply_mem_Q
import Submission.Work.ZassenhausTwoGroup.etaStar_data

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit (20'), `⟨Ind_Q^G ζ₁, Ind_Q^G 1_Q⟩_G = |D|`

In the split rank-one set-up `IsSplitRankOne H Q t` (`H = Q ⋊ D` with `D = twoPoint H t =
H ⊓ Hᵗ`, `Q ⊴ H`, `Q ⊓ D = ⊥`) the induced trivial character `Ξ₀ = Ind_Q^G 1_Q` of `G` has

* value `|D|` at every `q ∈ Q ∖ 1` (`indFun_Q_apply_mem_Q` for the trivial linear character,
  i.e. `Q` has exactly `|D|` `H`-conjugates of `q`, namely the `d q d⁻¹`, `d ∈ D`), and
* value `[G : Q] = (|Q| + 1)·|D|` at `1` (`indFun_apply_one`, `Q_index_eq_of_isSplitRankOne`).

Since `⟨Ind_Q^G ζ₁, Ξ₀⟩_G = ⟨ζ₁, Res_Q^G Ξ₀⟩_Q` (Frobenius reciprocity) and a non-trivial
irreducible character of `Q` sums to `0` over `Q`, this gives

`⟨Ind_Q^G ζ₁, Ξ₀⟩_G = |Q|⁻¹ · ([G:Q] - |D|) = |Q|⁻¹ · |Q| · |D| = |D|`.

Only the split rank-one structure is used: the Zassenhaus hypothesis `hZ` is not needed.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- `[G : Q] = (|Q| + 1) · |D|` where `D = twoPoint H t`: `H = Q ⋊ D` has index `|Q| + 1` in
`G` by the rank-one Bruhat decomposition `G = H ⊔ HtH`. -/
theorem Q_index_eq_of_isSplitRankOne {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Q.index = (Nat.card ↥Q + 1) * Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have heq : Nat.card ↥Q * Q.index
      = Nat.card ↥Q * ((Nat.card ↥Q + 1) * Nat.card ↥(Submission.Blueprint.twoPoint H t)) := by
    rw [Subgroup.card_mul_index Q, ← Subgroup.card_mul_index H, card_H_eq h,
      Subgroup.index_eq_card H, card_quotient_eq h]
    ring
  exact Nat.eq_of_mul_eq_mul_left hQpos heq

theorem chiXi_Xi0_inner {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1) :
    Work.CharCore.cfInner (Work.Induction.indFun Q ζ₁)
      (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)))
        = (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
  classical
  -- The irreducibility of `ζ₁` enters only through the orthogonality relation
  -- `∑_{q ∈ Q} ζ₁ q = 0`.  The character-theory library states its results at the canonical
  -- `Fintype ↥Q` instance (`Q.instFintypeSubtypeMemOfDecidablePred`), so transport `hζ` there
  -- once and for all, and install that instance for the rest of the proof.
  have hζ' : ζ₁ ∈ @Work.CharCore.Irr ↥Q _ Q.instFintypeSubtypeMemOfDecidablePred :=
    (mem_Irr_of_fintype_iff _ _).mp hζ
  letI : Fintype ↥Q := Q.instFintypeSubtypeMemOfDecidablePred
  -- the value of `Ind_Q^G 1_Q` at `1`
  have hval_one : Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)) (1 : G) = (Q.index : ℂ) := by
    rw [Work.Induction.indFun_apply_one, mul_one]
  -- the value of `Ind_Q^G 1_Q` at `1 ≠ q ∈ Q`: the number `|D|` of `H`-conjugates of `q`
  have hval_ne : ∀ q : ↥Q, q ≠ 1 →
      Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)) (q : G)
        = (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
    intro q hq
    have hmain := indFun_Q_apply_mem_Q (H := H) (Q := Q) (t := t) h (1 : ↥Q →* ℂˣ) hq
    have hfun : (fun x : ↥Q => ((1 : ↥Q →* ℂˣ) x : ℂ)) = (fun _ : ↥Q => (1 : ℂ)) := by
      funext x; simp
    rw [hfun] at hmain
    rw [hmain]
    simp only [MonoidHom.one_apply, Units.val_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card]
  -- orthogonality: a non-principal irreducible character of `Q` sums to `0`
  have hsumall : (∑ q : ↥Q, ζ₁ q) = 0 :=
    Work.CharCore.sum_apply_eq_zero_of_mem_Irr_of_ne_one hζ' hζ1
  have herase0 : (∑ q ∈ Finset.univ.erase (1 : ↥Q), ζ₁ q) = -1 := by
    have h' := Finset.sum_erase_add (Finset.univ : Finset ↥Q) ζ₁ (Finset.mem_univ (1 : ↥Q))
    rw [hsumall, hlin] at h'
    exact add_eq_zero_iff_eq_neg.mp h'
  -- the value of `Res_Q^G (Ind_Q^G 1_Q)` at `1`
  have hone : ζ₁ 1 * starRingEnd ℂ (Work.Induction.resFun Q
      (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ))) 1) = (Q.index : ℂ) := by
    show ζ₁ 1 * starRingEnd ℂ
      (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)) (1 : G)) = (Q.index : ℂ)
    rw [hval_one, hlin, one_mul, map_natCast]
  -- its values off `1`
  have hcong : ∀ q ∈ Finset.univ.erase (1 : ↥Q), ζ₁ q *
      starRingEnd ℂ (Work.Induction.resFun Q (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ))) q)
        = ζ₁ q * (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
    intro q hq
    rw [Finset.mem_erase] at hq
    show ζ₁ q * starRingEnd ℂ
        (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)) (q : G))
      = ζ₁ q * (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ)
    rw [hval_ne q hq.1, map_natCast]
  have herase : (∑ q ∈ Finset.univ.erase (1 : ↥Q), ζ₁ q *
      starRingEnd ℂ (Work.Induction.resFun Q (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ))) q))
      = - (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
    rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, herase0]
    ring
  -- the full sum `∑_q ζ₁ q · conj (Ξ₀ q)`
  have hsum : (∑ q : ↥Q, ζ₁ q *
      starRingEnd ℂ (Work.Induction.resFun Q (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ))) q))
      = (Q.index : ℂ) - (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset ↥Q) _
      (Finset.mem_univ (1 : ↥Q))]
    rw [herase, hone]
    ring
  -- Frobenius reciprocity turns the `G`-inner product into the `Q`-inner product
  have hfr := Work.Induction.frobenius_reciprocity Q ζ₁
      (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)))
      (Work.Induction.isClassFun_indFun Q (fun _ : ↥Q => (1 : ℂ)))
  rw [hfr, Work.CharCore.cfInner_apply, hsum]
  -- the remaining arithmetic
  have hQc : (Nat.card ↥Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hfc : (Fintype.card ↥Q : ℂ) = (Nat.card ↥Q : ℂ) := by
    rw [← Nat.card_eq_fintype_card]
  rw [hfc, Q_index_eq_of_isSplitRankOne h]
  push_cast
  rw [show ((Nat.card ↥Q : ℂ) + 1) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ)
        - (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ)
      = (Nat.card ↥Q : ℂ) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) by ring]
  rw [← mul_assoc, inv_mul_cancel₀ hQc, one_mul]

end Work.ZassenhausTwoGroup
