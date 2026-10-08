import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.ThmG.Defs
import Submission.Work.ThmG.nilpotent_of_K_ne_one
import Submission.Work.ThmG.nilpotent_two_odd_split
import Submission.Work.ThmG.oddPart_le_normalizer
import Submission.Work.ThmG.twoPart_eq_map_sylow_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Export.coprimeDQProp` — `Q` is a Hall subgroup of `H`

Peterfalvi I, Ch. I (used in Ch. VI §1, p. 257, and as hypothesis (3) of Appendix XII): in the
split rank-one situation `H = Q ⋊ D`, `D = H ∩ H^t`, the order of the normal complement `Q`
is coprime to `|D|`; equivalently `Q` (and `D`) is a **Hall subgroup** of `H`.

This module proves `Work.ThmG.CoprimeDQProp` from the inputs available in this workspace:
nilpotency of `Q` (`Work.ThmG.nilpotent_of_K_ne_one`, from `KNeOneProp`, `ChIIFourProp` and
Thompson's theorem) together with `Work.ThmG.FpfOddPartProp` (Ch. V §2 Lemma 2 c: `D` acts
fixed-point-freely on `Q₁ = O_{2'}(Q)`).  The proof is the elementary count:

* `|D|` is odd (`IsStronglyEmbedded`), so `|D|` is coprime to `O_2(Q)`;
* `D` acts fixed-point-freely on the odd part `Q₁ = O_{2'}(Q)`, so the orbit count (Burnside)
  gives `|D| ∣ |Q₁| - 1`, whence `(|D|, |Q₁|) = 1`;
* `Q = O_2(Q) · O_{2'}(Q)` with coprime factors because `Q` is nilpotent.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.DoubleTransitivity

open Submission.Blueprint

/-- **`Q` is a Hall subgroup of `H`** (`(|D|, |Q|) = 1`), Peterfalvi I Ch. I.
This is `Work.ThmG.CoprimeDQProp`. -/
theorem coprimeDQProp (hTh : ThompsonFrobeniusProp) (hC4 : ChIIFourProp)
    (hK : Work.ThmG.KNeOneProp) (hFpf : Work.ThmG.FpfOddPartProp) :
    Work.ThmG.CoprimeDQProp := by
  intro G instG instFin H Q t hRank
  have hRankK : Work.ThmG.RankOneHyp G H Q t := hRank
  obtain ⟨hSit, hSimple, hSplit, hNZ, hB3⟩ := hRank
  classical
  haveI h2p : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) :=
    hSplit.stronglyEmbedded.2.2 t hSplit.not_mem
  have hQnil : Group.IsNilpotent Q :=
    Work.ThmG.nilpotent_of_K_ne_one hSit hC4 hTh hSplit (hK G H Q t hRankK)
  obtain ⟨hsup, hinf, hcomm, hcop2, hoddQ, hnil2, hcard, hne⟩ :=
    Work.ThmG.nilpotent_two_odd_split Q hQnil
  -- ## Step 1: `|D| ∣ |Q₁| - 1`, where `Q₁ = O_{2'}(Q)`
  have hDQ1 : twoPoint H t ≤
      Subgroup.normalizer ((Work.ThmG.oddPart Q : Subgroup G) : Set G) :=
    le_trans inf_le_left (Work.ThmG.oddPart_le_normalizer hSplit.normal)
  have hsmul : ∀ (d : ↥(twoPoint H t)) (x : ↥(Work.ThmG.oddPart Q)),
      (d : G) * (x : G) * (d : G)⁻¹ ∈ Work.ThmG.oddPart Q := fun d x =>
    (Subgroup.mem_normalizer_iff.mp (hDQ1 d.2) (x : G)).mp x.2
  letI : MulAction ↥(twoPoint H t) ↥(Work.ThmG.oddPart Q) :=
    { smul := fun d x => ⟨(d : G) * (x : G) * (d : G)⁻¹, hsmul d x⟩
      one_smul := fun x => by
        apply Subtype.ext
        show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
        simp
      mul_smul := fun d e x => by
        apply Subtype.ext
        show ((d : G) * (e : G)) * (x : G) * ((d : G) * (e : G))⁻¹
          = (d : G) * ((e : G) * (x : G) * (e : G)⁻¹) * (d : G)⁻¹
        group }
  -- `Fintype.card` of the fixed points
  have hfix1 : Fintype.card (MulAction.fixedBy ↥(Work.ThmG.oddPart Q)
      (1 : ↥(twoPoint H t))) = Nat.card ↥(Work.ThmG.oddPart Q) := by
    have he : (MulAction.fixedBy ↥(Work.ThmG.oddPart Q) (1 : ↥(twoPoint H t)))
        ≃ ↥(Work.ThmG.oddPart Q) :=
      (Equiv.subtypeEquivRight (fun x => by rw [MulAction.mem_fixedBy]; simp)).trans
        (Equiv.Set.univ _)
    calc Fintype.card (MulAction.fixedBy ↥(Work.ThmG.oddPart Q) (1 : ↥(twoPoint H t)))
        = Fintype.card ↥(Work.ThmG.oddPart Q) := Fintype.card_congr he
      _ = Nat.card ↥(Work.ThmG.oddPart Q) := Nat.card_eq_fintype_card.symm
  have hfixne : ∀ d : ↥(twoPoint H t), d ≠ 1 →
      Fintype.card (MulAction.fixedBy ↥(Work.ThmG.oddPart Q) d) = 1 := by
    intro d hd
    have key : ∀ x : ↥(Work.ThmG.oddPart Q),
        (d : G) * (x : G) * (d : G)⁻¹ = (x : G) → x = 1 := by
      intro x hx
      exact Subtype.ext (hFpf G H Q t hRankK (d : G) d.2
        (fun h1 => hd (Subtype.ext h1)) (x : G) x.2 hx)
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, fun y => ?_⟩
    · apply Subtype.ext
      change (d : G) * (1 : G) * (d : G)⁻¹ = (1 : G)
      simp
    · exact Subtype.ext (key y.1 (congrArg Subtype.val y.2))
  have hsum : (∑ d : ↥(twoPoint H t),
        Fintype.card (MulAction.fixedBy ↥(Work.ThmG.oddPart Q) d))
      = Nat.card ↥(Work.ThmG.oddPart Q) + (Nat.card ↥(twoPoint H t) - 1) := by
    have h2 : (∑ d ∈ Finset.univ.erase (1 : ↥(twoPoint H t)),
        Fintype.card (MulAction.fixedBy ↥(Work.ThmG.oddPart Q) d))
        = Nat.card ↥(twoPoint H t) - 1 := by
      trans (∑ d ∈ Finset.univ.erase (1 : ↥(twoPoint H t)), (1 : ℕ))
      · exact Finset.sum_congr rfl (fun d hd => hfixne d (Finset.mem_erase.mp hd).1)
      · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
          ← Nat.card_eq_fintype_card]
        simp
    rw [← Finset.add_sum_erase Finset.univ
      (fun d : ↥(twoPoint H t) => Fintype.card (MulAction.fixedBy ↥(Work.ThmG.oddPart Q) d))
      (Finset.mem_univ 1), hfix1, h2]
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    ↥(twoPoint H t) ↥(Work.ThmG.oddPart Q)
  have hmain : Nat.card ↥(Work.ThmG.oddPart Q) + (Nat.card ↥(twoPoint H t) - 1)
      = Fintype.card (Quotient (MulAction.orbitRel ↥(twoPoint H t) ↥(Work.ThmG.oddPart Q)))
        * Nat.card ↥(twoPoint H t) := by
    rw [← hsum, hB, Nat.card_eq_fintype_card]
  have hDpos : 1 ≤ Nat.card ↥(twoPoint H t) := by
    haveI : Nonempty ↥(twoPoint H t) := ⟨⟨1, (twoPoint H t).one_mem⟩⟩
    exact Nat.card_pos
  have hQ1pos : 1 ≤ Nat.card ↥(Work.ThmG.oddPart Q) := by
    haveI : Nonempty ↥(Work.ThmG.oddPart Q) := ⟨⟨1, Work.ThmG.one_mem_oddPart Q⟩⟩
    exact Nat.card_pos
  have h1 : Nat.card ↥(Work.ThmG.oddPart Q) - 1
      = Fintype.card (Quotient (MulAction.orbitRel ↥(twoPoint H t) ↥(Work.ThmG.oddPart Q)))
          * Nat.card ↥(twoPoint H t) - Nat.card ↥(twoPoint H t) := by omega
  have hdivQ1 : Nat.card ↥(twoPoint H t) ∣ Nat.card ↥(Work.ThmG.oddPart Q) - 1 := by
    rw [h1]
    refine ⟨Fintype.card (Quotient (MulAction.orbitRel ↥(twoPoint H t)
      ↥(Work.ThmG.oddPart Q))) - 1, ?_⟩
    rw [Nat.mul_comm (Nat.card ↥(twoPoint H t))
      (Fintype.card (Quotient (MulAction.orbitRel ↥(twoPoint H t)
        ↥(Work.ThmG.oddPart Q))) - 1), Nat.sub_mul, one_mul]
  have hcopQ1 : Nat.Coprime (Nat.card ↥(twoPoint H t)) (Nat.card ↥(Work.ThmG.oddPart Q)) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hg : Nat.gcd (Nat.card ↥(twoPoint H t)) (Nat.card ↥(Work.ThmG.oddPart Q))
        ∣ Nat.card ↥(Work.ThmG.oddPart Q) - (Nat.card ↥(Work.ThmG.oddPart Q) - 1) :=
      Nat.dvd_sub (Nat.gcd_dvd_right _ _) ((Nat.gcd_dvd_left _ _).trans hdivQ1)
    rw [show Nat.card ↥(Work.ThmG.oddPart Q) - (Nat.card ↥(Work.ThmG.oddPart Q) - 1) = 1
        from by omega] at hg
    exact Nat.dvd_one.mp hg
  -- ## Step 2: `|D|` is coprime to the `2`-part `O_2(Q)`
  have hcopQ2 : Nat.Coprime (Nat.card ↥(twoPoint H t)) (Nat.card ↥(Work.ThmG.twoPart Q)) := by
    obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := Q)
    have hP := Work.ThmG.twoPart_eq_map_sylow_two Q hQnil P
    have hcardP : Nat.card ↥(Work.ThmG.twoPart Q) = Nat.card ↥(P : Subgroup Q) := by
      rw [hP]
      exact Subgroup.card_map_of_injective Q.subtype_injective
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(P : Subgroup Q))).mp P.isPGroup'
    rw [hcardP, hn]
    exact (Nat.coprime_two_right.mpr hDodd).pow_right n
  -- ## Conclusion
  rw [← hcard]
  exact hcopQ2.mul_right hcopQ1

end Work.DoubleTransitivity
