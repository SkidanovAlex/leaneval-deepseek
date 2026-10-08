import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.isTI_Q_induction
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ZassenhausTwoGroup.conj_mem_Q_iff
import Submission.Work.ZassenhausTwoGroup.card_H_eq
import Submission.Work.ZassenhausTwoGroup.card_quotient_eq
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q
import Submission.Work.ZassenhausTwoGroup.zetaStar_aux
import Submission.Work.ZassenhausTwoGroup.indFun_Q_apply_mem_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit's display (20): `‖Ind_Q^G ζ‖² = |D| + 1`

This file proves `Work.ZassenhausTwoGroup.zetaStar_norm`, the norm computation `(20)` of
W. Feit, *On a class of doubly transitive permutation groups*, Illinois J. Math. 4 (1960),
for the split rank-one set-up `IsSplitRankOne H Q t` of a Zassenhaus group
(`IsZassenhaus H`), with `D = twoPoint H t = H ⊓ Hᵗ`.

For a non-trivial **linear** character `ζ` of the Frobenius kernel `Q` (`Q ⊴ H = Q ⋊ D` with `D`
acting fixed point freely on `Q`), the induced character `Ind_Q^G ζ` has

`‖Ind_Q^G ζ‖² = |D| + 1`.

The proof is Feit's: by Frobenius reciprocity `‖Ind_Q^G ζ‖² = ⟨ζ, Res_Q^G Ind_Q^G ζ⟩_Q`; the value
of `Ind_Q^G ζ` at `q ∈ Q ∖ 1` is `∑_{d ∈ D} ζ (d q d⁻¹)` (the module `indFun_Q_apply_mem_Q`, the
`Q`-conjugation being invisible because `ζ` is a homomorphism into the abelian group `ℂˣ`), while
`Ind_Q^G ζ (1) = |G : Q| = (|Q|+1)|D|`; the orthogonality relation `∑_{q∈Q} ζ (q d q⁻¹ d⁻¹) = 0`
for `1 ≠ d ∈ D` (`zs_sum_comm_conj_zero`, from fixed-point-freeness) then evaluates the inner
product to `(1/|Q|) (|G:Q| + |Q| - |D|) = |D| + 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G]

/-! ## Two elementary auxiliaries -/

section Aux

open Classical

/-- **Orthogonality `∑_{q ∈ Q} φ (q d q⁻¹ d⁻¹) = 0`.**  For a non-trivial linear character `φ`
of `Q` and `1 ≠ d ∈ D = twoPoint H t`, the "commutator" map `q ↦ q d q⁻¹ d⁻¹` is a bijection of
`Q` (fixed-point-freeness of `d` on `Q`, `fpf_on_Q`), so the sum is the sum of `φ` over all of
`Q`, which vanishes because `φ` is non-trivial. -/
private theorem zs_sum_comm_conj_zero {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (φ : ↥Q →* ℂˣ) (hφ : (fun x : ↥Q => (φ x : ℂ)) ≠ 1)
    {d : ↥(twoPoint H t)} (hd : d ≠ 1) :
    ∑ q : ↥Q, (φ (q * (conjQD h d q)⁻¹) : ℂ) = 0 := by
  classical
  have hdG : (d : G) ≠ 1 := fun hh => hd (Subtype.ext hh)
  have hfpf : IsFpfOn (twoPoint H t) Q := fpf_on_Q h hz
  -- the `G`-value of the "commutator" element
  have hcoe : ∀ q : ↥Q, ((q * (conjQD h d q)⁻¹ : ↥Q) : G)
      = (q : G) * (d : G) * (q : G)⁻¹ * (d : G)⁻¹ := by
    intro q
    rw [Subgroup.coe_mul, Subgroup.coe_inv, conjQD_coe]
    group
  -- the map is injective (fixed-point-freeness)
  have hinj : Function.Injective (fun q : ↥Q => q * (conjQD h d q)⁻¹) := by
    intro q₁ q₂ heq
    have hG : (q₁ : G) * (d : G) * (q₁ : G)⁻¹ * (d : G)⁻¹
        = (q₂ : G) * (d : G) * (q₂ : G)⁻¹ * (d : G)⁻¹ := by
      have hc := congrArg (fun z : ↥Q => (z : G)) heq
      rw [hcoe q₁, hcoe q₂] at hc
      exact hc
    have hA : (q₁ : G) * (d : G) * (q₁ : G)⁻¹ = (q₂ : G) * (d : G) * (q₂ : G)⁻¹ :=
      mul_right_cancel hG
    -- `d` commutes with `c = q₂⁻¹ * q₁`
    have h3 : (d : G) * ((q₂ : G)⁻¹ * (q₁ : G)) = ((q₂ : G)⁻¹ * (q₁ : G)) * (d : G) := by
      have key : (q₂ : G) * ((d : G) * ((q₂ : G)⁻¹ * (q₁ : G)))
          = (q₂ : G) * (((q₂ : G)⁻¹ * (q₁ : G)) * (d : G)) := by
        calc (q₂ : G) * ((d : G) * ((q₂ : G)⁻¹ * (q₁ : G)))
            = ((q₂ : G) * (d : G) * (q₂ : G)⁻¹) * (q₁ : G) := by group
          _ = ((q₁ : G) * (d : G) * (q₁ : G)⁻¹) * (q₁ : G) := by rw [← hA]
          _ = (q₁ : G) * (d : G) := by group
          _ = (q₂ : G) * (((q₂ : G)⁻¹ * (q₁ : G)) * (d : G)) := by group
      exact mul_left_cancel key
    have hcd : (d : G) * (((q₂⁻¹ : ↥Q) * q₁ : ↥Q) : G) * (d : G)⁻¹
        = (((q₂⁻¹ : ↥Q) * q₁ : ↥Q) : G) := by
      rw [show (((q₂⁻¹ : ↥Q) * q₁ : ↥Q) : G) = (q₂ : G)⁻¹ * (q₁ : G) by simp, h3]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have hc1 : ((q₂⁻¹ * q₁ : ↥Q) : G) = 1 :=
      hfpf (d : G) d.2 hdG ((q₂⁻¹ * q₁ : ↥Q) : G) (q₂⁻¹ * q₁ : ↥Q).2 hcd
    have hone : q₂⁻¹ * q₁ = (1 : ↥Q) := Subtype.ext hc1
    have : q₁ = q₂ := by
      have hh := congrArg (fun z : ↥Q => q₂ * z) hone
      simpa using hh
    exact this
  have hbij : Function.Bijective (fun q : ↥Q => q * (conjQD h d q)⁻¹) :=
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  -- a non-trivial linear character sums to `0` over a finite group
  have hsum0 : (∑ q : ↥Q, (φ q : ℂ)) = 0 := by
    have hex : ∃ a : ↥Q, (φ a : ℂ) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hφ (funext (fun x => hcon x))
    obtain ⟨a, ha⟩ := hex
    have h1 : (∑ q : ↥Q, (φ (a * q) : ℂ)) = ∑ q : ↥Q, (φ q : ℂ) :=
      Equiv.sum_comp (Equiv.mulLeft a) (fun q : ↥Q => (φ q : ℂ))
    have h2 : (∑ q : ↥Q, (φ (a * q) : ℂ)) = (φ a : ℂ) * ∑ q : ↥Q, (φ q : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [map_mul, Units.val_mul]
    have h3 : (φ a : ℂ) * (∑ q : ↥Q, (φ q : ℂ)) = ∑ q : ↥Q, (φ q : ℂ) := by
      rw [← h2, h1]
    have h4 : ((φ a : ℂ) - 1) * (∑ q : ↥Q, (φ q : ℂ)) = 0 := by
      rw [sub_mul, one_mul, h3, sub_self]
    have h5 : (φ a : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr ha
    exact (mul_eq_zero.mp h4).resolve_left h5
  calc ∑ q : ↥Q, (φ (q * (conjQD h d q)⁻¹) : ℂ)
      = ∑ q : ↥Q, (φ q : ℂ) := by
        have hh := Equiv.sum_comp
          (Equiv.ofBijective (fun q : ↥Q => q * (conjQD h d q)⁻¹) hbij)
          (fun q : ↥Q => (φ q : ℂ))
        simpa only [Equiv.ofBijective_apply] using hh
    _ = 0 := hsum0

/-- The index of `Q` in `G` is `(|Q| + 1) · |D|` (`= |Ω| · |D|`): `H = Q ⋊ D` has index `|Q|+1`
(`card_quotient_eq`) and order `|Q|·|D|` (`card_H_eq`). -/
private theorem zs_Q_index_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) :
    Q.index = (Nat.card ↥Q + 1) * Nat.card ↥(twoPoint H t) := by
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have heq : Nat.card ↥Q * Q.index
      = Nat.card ↥Q * ((Nat.card ↥Q + 1) * Nat.card ↥(twoPoint H t)) := by
    rw [Subgroup.card_mul_index Q, ← Subgroup.card_mul_index H, card_H_eq h,
      Subgroup.index_eq_card H, card_quotient_eq h]
    ring
  exact Nat.eq_of_mul_eq_mul_left hQpos heq

end Aux

/-! ## The main theorem -/

theorem zetaStar_norm {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    {ζ : ↥Q → ℂ} (hζ : ζ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ ≠ 1) (hlin : ζ 1 = 1) :
    Work.CharCore.cfInner (Work.Induction.indFun Q ζ) (Work.Induction.indFun Q ζ)
      = (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) + 1 := by
  classical
  -- `ζ` is a linear character
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥Q →* ℂˣ, ∀ x : ↥Q, ζ x = (φ x : ℂ) := by
    refine (Work.CharCore.linear_char_iff_deg_one hζ).mp ?_
    have hspec := Work.CharCore.irrDeg_spec hζ
    have h1 : (Work.CharCore.irrDeg ζ : ℂ) = 1 := by rw [← hspec, hlin]
    exact_mod_cast h1
  have hζφ : ζ = fun x : ↥Q => (φ x : ℂ) := funext (fun x => hφ x)
  have hφne : (fun x : ↥Q => (φ x : ℂ)) ≠ 1 := by rw [← hζφ]; exact hζ1
  -- From here on use the classical `Fintype ↥Q` instance, the one baked into
  -- `Work.Induction.frobenius_reciprocity`.
  letI : Fintype ↥Q := Q.instFintypeSubtypeMemOfDecidablePred
  -- a version of `ζ` recognised as an irreducible character at that instance
  obtain ⟨χ, hχIrr, hχeq⟩ := Work.CharCore.exists_irr_of_monoidHom φ
  -- Frobenius reciprocity
  rw [Work.Induction.frobenius_reciprocity Q ζ (Work.Induction.indFun Q ζ)
    (Work.Induction.isClassFun_indFun Q ζ)]
  simp only [Work.CharCore.cfInner_apply]
  -- the value of the induced function at `q ∈ Q ∖ 1`
  have hK : ∀ q : ↥Q, q ≠ 1 →
      ζ q * starRingEnd ℂ (Work.Induction.resFun Q (Work.Induction.indFun Q ζ) q)
        = ∑ d : ↥(twoPoint H t), ζ (q * (conjQD h d q)⁻¹) := by
    intro q hq
    have hval : Work.Induction.resFun Q (Work.Induction.indFun Q ζ) q
        = ∑ d : ↥(twoPoint H t), (φ (conjQD h d q) : ℂ) := by
      have h0 : Work.Induction.indFun Q ζ
          = Work.Induction.indFun Q (fun x : ↥Q => (φ x : ℂ)) := by rw [hζφ]
      rw [Work.Induction.resFun_apply, h0]
      exact indFun_Q_apply_mem_Q h φ hq
    have hstar : starRingEnd ℂ (∑ d : ↥(twoPoint H t), (φ (conjQD h d q) : ℂ))
        = ∑ d : ↥(twoPoint H t), ζ ((conjQD h d q)⁻¹) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [← hχeq (conjQD h d q), Work.CharCore.star_Irr χ hχIrr (conjQD h d q),
        hχeq ((conjQD h d q)⁻¹), ← hφ ((conjQD h d q)⁻¹)]
    have hmult : ∀ d : ↥(twoPoint H t),
        ζ q * ζ ((conjQD h d q)⁻¹) = ζ (q * (conjQD h d q)⁻¹) := by
      intro d
      rw [hφ q, hφ (q * (conjQD h d q)⁻¹), hφ ((conjQD h d q)⁻¹), map_mul, Units.val_mul]
    rw [hval, hstar, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => hmult d)
  -- the value at `1`
  have h1term : ζ (1 : ↥Q) * starRingEnd ℂ (Work.Induction.resFun Q (Work.Induction.indFun Q ζ) 1)
      = (Q.index : ℂ) := by
    rw [Work.Induction.resFun_apply, Subgroup.coe_one, Work.Induction.indFun_apply_one,
      hlin, mul_one, one_mul]
    exact map_natCast (starRingEnd ℂ) Q.index
  -- the sum over `Q ∖ 1`, in the form `∑_d ∑_{q ≠ 1}`
  have herase : (∑ q ∈ Finset.univ.erase (1 : ↥Q),
        ζ q * starRingEnd ℂ (Work.Induction.resFun Q (Work.Induction.indFun Q ζ) q))
      = (Nat.card ↥Q : ℂ) - (Nat.card ↥(twoPoint H t) : ℂ) := by
    have h1 : (∑ q ∈ Finset.univ.erase (1 : ↥Q),
          ζ q * starRingEnd ℂ (Work.Induction.resFun Q (Work.Induction.indFun Q ζ) q))
        = ∑ q ∈ Finset.univ.erase (1 : ↥Q),
            ∑ d : ↥(twoPoint H t), ζ (q * (conjQD h d q)⁻¹) := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      rw [Finset.mem_erase] at hq
      exact hK q hq.1
    rw [h1, Finset.sum_comm]
    have hd1 : (∑ q ∈ Finset.univ.erase (1 : ↥Q),
          ζ (q * (conjQD h (1 : ↥(twoPoint H t)) q)⁻¹)) = (Nat.card ↥Q : ℂ) - 1 := by
      have hterm : ∀ q : ↥Q, ζ (q * (conjQD h (1 : ↥(twoPoint H t)) q)⁻¹) = 1 := by
        intro q
        have hcq : conjQD h (1 : ↥(twoPoint H t)) q = q := by
          apply Subtype.ext
          rw [conjQD_coe]
          simp
        rw [hcq, mul_inv_cancel, hlin]
      rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥Q)), Finset.card_univ, nsmul_eq_mul,
        mul_one, Nat.card_eq_fintype_card,
        Nat.cast_pred (Fintype.card_pos_iff.mpr ⟨1⟩)]
    have hdd : ∀ d : ↥(twoPoint H t), d ≠ 1 →
        (∑ q ∈ Finset.univ.erase (1 : ↥Q), ζ (q * (conjQD h d q)⁻¹)) = -1 := by
      intro d hd
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : ↥Q))]
      have hzero : (∑ q : ↥Q, ζ (q * (conjQD h d q)⁻¹)) = 0 := by
        rw [show (∑ q : ↥Q, ζ (q * (conjQD h d q)⁻¹))
              = ∑ q : ↥Q, (φ (q * (conjQD h d q)⁻¹) : ℂ) from
            Finset.sum_congr rfl (fun q _ => hφ (q * (conjQD h d q)⁻¹))]
        exact zs_sum_comm_conj_zero h hz φ hφne hd
      have h1d : ζ ((1 : ↥Q) * (conjQD h d (1 : ↥Q))⁻¹) = 1 := by
        have hcq : conjQD h d (1 : ↥Q) = 1 := by
          apply Subtype.ext
          rw [conjQD_coe]
          simp
        rw [hcq, inv_one, mul_one, hlin]
      rw [hzero, h1d]
      ring
    have hrest : (∑ d ∈ Finset.univ.erase (1 : ↥(twoPoint H t)),
          ∑ q ∈ Finset.univ.erase (1 : ↥Q), ζ (q * (conjQD h d q)⁻¹))
        = 1 - (Nat.card ↥(twoPoint H t) : ℂ) := by
      have hcong : ∀ d ∈ Finset.univ.erase (1 : ↥(twoPoint H t)),
          (∑ q ∈ Finset.univ.erase (1 : ↥Q), ζ (q * (conjQD h d q)⁻¹)) = -1 := by
        intro d hd
        rw [Finset.mem_erase] at hd
        exact hdd d hd.1
      rw [Finset.sum_congr rfl hcong,
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥(twoPoint H t))),
        Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card,
        Nat.cast_pred (Fintype.card_pos_iff.mpr ⟨1⟩)]
      ring
    rw [← Finset.sum_erase_add _ (fun d : ↥(twoPoint H t) =>
          ∑ q ∈ Finset.univ.erase (1 : ↥Q), ζ (q * (conjQD h d q)⁻¹))
        (Finset.mem_univ (1 : ↥(twoPoint H t)))]
    rw [hd1, hrest]
    ring
  rw [← Finset.sum_erase_add _ (fun q : ↥Q =>
        ζ q * starRingEnd ℂ (Work.Induction.resFun Q (Work.Induction.indFun Q ζ) q))
      (Finset.mem_univ (1 : ↥Q))]
  rw [h1term, herase]
  -- final arithmetic
  have hidx : (Q.index : ℂ)
      = ((Nat.card ↥Q : ℂ) + 1) * (Nat.card ↥(Submission.Blueprint.twoPoint H t) : ℂ) := by
    rw [zs_Q_index_eq h]
    push_cast
    ring
  have hcard : (Nat.card ↥Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Nat.card_ne_zero).mpr ⟨⟨1⟩, inferInstance⟩
  rw [show (Fintype.card ↥Q : ℂ) = (Nat.card ↥Q : ℂ) by rw [Nat.card_eq_fintype_card], hidx]
  field_simp
  ring

end Work.ZassenhausTwoGroup
