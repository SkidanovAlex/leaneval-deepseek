import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.ZassenhausTwoGroup.zetaStar_norm
import Submission.Work.ZassenhausTwoGroup.chiXi_indFun_sum_eq
import Submission.Work.CharCore.step9_global_sums

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

/-!
# `Work.ZassenhausTwoGroup.chiXi_not_const`

In the split rank-one set-up `IsSplitRankOne H Q t` of a Zassenhaus group (`IsZassenhaus H`),
with `D = twoPoint H t = H ⊓ Hᵗ`, the induced function `Ind_Q^G ζ₁` of a non-trivial **linear**
character `ζ₁` of the Frobenius kernel `Q` is **not constant** on `Q ∖ {1}`, as soon as
`|D| ≠ |Q| - 1` (Feit's proviso `q ≠ m - 1`).

This is the statement used in `chiXi_exceptionals`: Feit's Corollary 2.4 says that
`Ind_Q^G ζ₁ - χ₁` (the difference of the induced character of a non-trivial linear `ζ₁` and the
exceptional character attached to it) is constant on `Q ∖ 1`; the present lemma shows that
`Ind_Q^G ζ₁` itself is not constant there, i.e. that `χ₁` is genuinely exceptional.

## The argument

Write `m = |Q|`, `q = |D|`, and suppose `f = Ind_Q^G ζ₁` is constant, `f(y) = γ`, on
`Q ∖ {1}`.  Two computations — both consequences of the fixed-point-freeness of `D` on `Q`
(`fpf_on_Q`) — contradict `q ≠ m - 1`:

* **(sum)** `∑_{y ∈ Q} f(y) = m·q` (`chiXi_indFun_sum_eq`): the value at `1` is
  `Q.index = (m+1)q` (`indFun_apply_one`, `card_H_eq`, `card_quotient_eq`) and the values on
  `Q ∖ {1}` sum to `-q` (the inner sum `∑_{d ∈ D} ζ₁ (d y d⁻¹)` is the orbit sum, and the total
  over an orbit-sum is `0`).  With constancy this gives `(m - 1)·γ = -q`.
* **(norm)** `∑_{y ∈ Q} ζ₁(y)·conj(f(y)) = m(q+1)` (the unnormalised form of
  `‖Ind_Q^G ζ₁‖² = q + 1`, `zetaStar_norm`).  Since `ζ₁` is non-trivial,
  `∑_{y ∈ Q ∖ {1}} ζ₁(y) = -1`, so `conj γ = (m+1)q - m(q+1) = q - m`, i.e. `γ = q - m`
  (`γ` is real).

Substituting the second relation into the first: `(m-1)(q-m) = -q`, i.e. `m(q - m + 1) = 0`,
so `q = m - 1`, contradicting the hypothesis.

The hypothesis `|D| ≠ |Q| - 1` is not redundant: in the *excluded* case (`q = m - 1`, e.g. the
Borel `Q ⋊ D` of `PSL(2, q)` with `D` acting transitively on `Q ∖ 1`, or `V₄ ⋊ C₃ ⊂ A₅`)
the induced function *is* constant on `Q ∖ {1}`.
-/

open Classical

/-- The index of `Q` in `G`: `|G : Q| = (|Q| + 1)·|D|`, from `|G : H| = |Q| + 1`
(`card_quotient_eq`) and `|H| = |Q|·|D|` (`card_H_eq`). -/
private theorem chiXi_Q_index {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Q.index = (Nat.card ↥Q + 1) * Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have heq : Nat.card ↥Q * Q.index
      = Nat.card ↥Q *
          ((Nat.card ↥Q + 1) * Nat.card ↥(Submission.Blueprint.twoPoint H t)) := by
    rw [Subgroup.card_mul_index Q, ← Subgroup.card_mul_index H, card_H_eq h,
      Subgroup.index_eq_card H, card_quotient_eq h]
    ring
  exact Nat.eq_of_mul_eq_mul_left hQpos heq

/-- `Q ≠ ⊥` in the rank-one set-up: otherwise `|H| = |Q|·|D| = |D|` would be both even
(`Even (Nat.card H)`, strong embedding) and odd (`Odd (Nat.card (twoPoint H t))`). -/
private theorem chiXi_exists_ne_one {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) : ∃ y : ↥Q, y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : Q = ⊥ := by
    ext x
    constructor
    · intro hx
      simpa using congrArg Subtype.val (hcon ⟨x, hx⟩)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact Q.one_mem
  have hone : Nat.card ↥Q = 1 := by
    rw [hbot]
    exact Subgroup.card_bot
  have hHeq : Nat.card ↥H = Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    have hc := card_H_eq h
    rw [hone, one_mul] at hc
    exact hc
  have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    odd_card_twoPoint h.stronglyEmbedded h.not_mem
  have hev : Even (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := by
    rw [← hHeq]
    exact even_card_of_stronglyEmbedded h.stronglyEmbedded
  exact Nat.not_even_iff_odd.mpr hodd hev

/-- **The unnormalised norm identity** `∑_{y ∈ Q} ζ₁(y)·conj(Ind_Q^G ζ₁(y)) = |Q|·(|D| + 1)`.

This is Frobenius reciprocity applied to Feit's display (20), `‖Ind_Q^G ζ₁‖² = |D| + 1`
(`zetaStar_norm`): `cfInner (Ind ζ₁) (Ind ζ₁) = cfInner ζ₁ (Res_Q (Ind ζ₁))` and `cfInner` on
`↥Q` is `|Q|⁻¹` times the sum appearing here. -/
private theorem chiXi_sum_norm_priv {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1) :
    ∑ y : ↥Q, ζ₁ y * starRingEnd ℂ (Work.Induction.indFun Q ζ₁ (y : G))
      = (Nat.card ↥Q : ℂ) * ((Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) + 1) := by
  classical
  have hfr := Work.Induction.frobenius_reciprocity Q ζ₁ (Work.Induction.indFun Q ζ₁)
    (Work.Induction.isClassFun_indFun Q ζ₁)
  have hzt := zetaStar_norm h hZ hζ hζ1 hlin
  have h1 : Work.CharCore.cfInner ζ₁ (Work.Induction.resFun Q (Work.Induction.indFun Q ζ₁))
      = (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) + 1 := by
    rw [← hfr]
    exact hzt
  rw [Work.CharCore.cfInner_apply] at h1
  simp only [Work.Induction.resFun_apply] at h1
  rw [← Nat.card_eq_fintype_card (α := ↥Q)] at h1
  have hcard : (Nat.card ↥Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Nat.card_pos (α := ↥Q)).ne'
  have h2 := congrArg (fun z : ℂ => (Nat.card ↥Q : ℂ) * z) h1
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul] at h2
  exact h2

theorem chiXi_not_const {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hne : Nat.card (Submission.Blueprint.twoPoint H t) ≠ Nat.card ↥Q - 1)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1) :
    ∃ y y' : ↥Q, y ≠ 1 ∧ y' ≠ 1 ∧
      Work.Induction.indFun Q ζ₁ (y : G) ≠ Work.Induction.indFun Q ζ₁ (y' : G) := by
  classical
  -- The statement's own `Fintype ↥Q` instance, recorded before it is shadowed below.
  let instQ : Fintype ↥Q := inferInstance
  -- Fix the `Fintype ↥Q` instance to the canonical one
  -- (`Subgroup.instFintypeSubtypeMemOfDecidablePred`), the instance with which
  -- `Work.Induction.frobenius_reciprocity` is stated; this makes the `cfInner` on `↥Q`
  -- occurring in that lemma and in the goal syntactically identical.
  letI : Fintype ↥Q := Q.instFintypeSubtypeMemOfDecidablePred
  -- `hζ` is a statement about membership in `Irr ↥Q`, which does not depend on the `Fintype`
  -- instance: transfer it to the canonical one through the `FDRep`-characterisation.
  have hζ' : ζ₁ ∈ Work.CharCore.Irr ↥Q :=
    (Work.CharCore.mem_Irr_iff_fdrep (G := ↥Q) ζ₁).mpr
      ((@Work.CharCore.mem_Irr_iff_fdrep ↥Q _ instQ ζ₁).mp hζ)
  by_contra hcon
  -- constancy of `Ind_Q^G ζ₁` on `Q ∖ 1`
  have hconst : ∀ y y' : ↥Q, y ≠ 1 → y' ≠ 1 →
      Work.Induction.indFun Q ζ₁ (y : G) = Work.Induction.indFun Q ζ₁ (y' : G) := by
    intro y y' hy hy'
    by_contra hne'
    exact hcon ⟨y, y', hy, hy', hne'⟩
  obtain ⟨y₀, hy₀⟩ := chiXi_exists_ne_one (G := G) (H := H) (Q := Q) (t := t) h
  set γ : ℂ := Work.Induction.indFun Q ζ₁ (y₀ : G) with hγdef
  have hconstγ : ∀ y : ↥Q, y ≠ 1 → Work.Induction.indFun Q ζ₁ (y : G) = γ :=
    fun y hy => (hconst y y₀ hy hy₀).trans hγdef.symm
  -- `ζ₁` is a linear character, so its sum over `Q` vanishes (it is non-trivial)
  have hsumζ : (∑ y : ↥Q, ζ₁ y) = 0 := by
    refine Work.CharCore.sum_apply_eq_zero_of_mem_Irr_of_ne_one hζ' ?_
    intro hh
    exact hζ1 (by rw [hh]; rfl)
  -- value at `1`
  have hval1 : Work.Induction.indFun Q ζ₁ (1 : G) = (Q.index : ℂ) := by
    rw [Work.Induction.indFun_apply_one, hlin, mul_one]
  -- the two identities (Feit (20) and the orbit-sum identity)
  have hP1 : (∑ y : ↥Q, ζ₁ y * starRingEnd ℂ (Work.Induction.indFun Q ζ₁ (y : G)))
      = (Nat.card ↥Q : ℂ) * ((Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) + 1) :=
    chiXi_sum_norm_priv h hZ hζ' hζ1 hlin
  have hP2 : (∑ y : ↥Q, Work.Induction.indFun Q ζ₁ (y : G))
      = (Nat.card ↥Q : ℂ) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) :=
    chiXi_indFun_sum_eq h hζ' hζ1 hlin
  -- `Q.index = (m+1)q`
  have hidx : (Q.index : ℂ)
      = ((Nat.card ↥Q : ℂ) + 1) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) := by
    rw [chiXi_Q_index h]; push_cast; ring
  have hcardF : (Fintype.card ↥Q : ℂ) = (Nat.card ↥Q : ℂ) := by
    rw [Nat.card_eq_fintype_card]
  -- (i) `(m - 1) * γ = -q`, in the form `m * γ - γ = -q`
  have hsplit : (∑ y : ↥Q, Work.Induction.indFun Q ζ₁ (y : G))
      = Work.Induction.indFun Q ζ₁ (1 : G)
        + ∑ y ∈ Finset.univ.erase (1 : ↥Q), Work.Induction.indFun Q ζ₁ (y : G) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : ↥Q)), add_comm]
    simp only [Subgroup.coe_one]
  have herase_const : (∑ y ∈ Finset.univ.erase (1 : ↥Q), Work.Induction.indFun Q ζ₁ (y : G))
      = (Fintype.card ↥Q : ℂ) * γ - γ := by
    have h1 : (∑ y ∈ Finset.univ.erase (1 : ↥Q), Work.Induction.indFun Q ζ₁ (y : G))
        = ∑ _y ∈ Finset.univ.erase (1 : ↥Q), γ := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      exact hconstγ y (Finset.mem_erase.mp hy).1
    rw [h1, Finset.sum_erase_eq_sub (Finset.mem_univ (1 : ↥Q)), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hI : (Nat.card ↥Q : ℂ) * γ - γ
      = -(Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) := by
    have key : (Nat.card ↥Q : ℂ) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ)
        = ((Nat.card ↥Q : ℂ) + 1) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ)
          + ((Nat.card ↥Q : ℂ) * γ - γ) := by
      rw [← hP2, hsplit, hval1, herase_const, hcardF, hidx]
    have h2 : (Nat.card ↥Q : ℂ) * γ - γ
        = (Nat.card ↥Q : ℂ) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ)
          - ((Nat.card ↥Q : ℂ) + 1) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) := by
      rw [key]; ring
    rw [h2]; ring
  -- (ii) `γ = q - m`
  have hsplit2 : (∑ y : ↥Q, ζ₁ y * starRingEnd ℂ (Work.Induction.indFun Q ζ₁ (y : G)))
      = ζ₁ 1 * starRingEnd ℂ (Work.Induction.indFun Q ζ₁ (1 : G))
        + ∑ y ∈ Finset.univ.erase (1 : ↥Q),
            ζ₁ y * starRingEnd ℂ (Work.Induction.indFun Q ζ₁ (y : G)) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : ↥Q)), add_comm]
    simp only [Subgroup.coe_one]
  have hsumζ' : (∑ y ∈ Finset.univ.erase (1 : ↥Q), ζ₁ y) = -1 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : ↥Q)), hsumζ, hlin]
    ring
  have h1term : ζ₁ 1 * starRingEnd ℂ (Work.Induction.indFun Q ζ₁ (1 : G)) = (Q.index : ℂ) := by
    rw [hval1, hlin, one_mul, map_natCast]
  have herase2 : (∑ y ∈ Finset.univ.erase (1 : ↥Q),
        ζ₁ y * starRingEnd ℂ (Work.Induction.indFun Q ζ₁ (y : G)))
      = -starRingEnd ℂ γ := by
    have h1 : (∑ y ∈ Finset.univ.erase (1 : ↥Q),
          ζ₁ y * starRingEnd ℂ (Work.Induction.indFun Q ζ₁ (y : G)))
        = ∑ y ∈ Finset.univ.erase (1 : ↥Q), ζ₁ y * starRingEnd ℂ γ := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [hconstγ y (Finset.mem_erase.mp hy).1]
    rw [h1, ← Finset.sum_mul, hsumζ']
    ring
  have hstarγ : starRingEnd ℂ γ
      = (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) - (Nat.card ↥Q : ℂ) := by
    have key : (Nat.card ↥Q : ℂ) * ((Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) + 1)
        = (Q.index : ℂ) - starRingEnd ℂ γ := by
      rw [← hP1, hsplit2, h1term, herase2]
      ring
    rw [hidx] at key
    linear_combination key
  have hII : γ = (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) - (Nat.card ↥Q : ℂ) := by
    have h := congrArg (starRingEnd ℂ) hstarγ
    simpa using h
  -- the arithmetic: substituting (ii) into (i) gives `q = m - 1`
  have hm0 : (Nat.card ↥Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Nat.card_pos (α := ↥Q)).ne'
  have hfinal : (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ)
      = (Nat.card ↥Q : ℂ) - 1 := by
    have hI' : (Nat.card ↥Q : ℂ) * γ - γ
        = -(Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) := hI
    rw [hII] at hI'
    have key : (Nat.card ↥Q : ℂ) * ((Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ)
        - (Nat.card ↥Q : ℂ) + 1) = 0 := by
      linear_combination hI'
    have key' := (mul_eq_zero.mp key).resolve_left hm0
    linear_combination key'
  refine hne ?_
  refine Nat.cast_injective (R := ℂ) ?_
  rw [hfinal, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos (α := ↥Q)).ne'),
    Nat.cast_one]

end Work.ZassenhausTwoGroup
