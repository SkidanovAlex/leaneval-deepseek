import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA._cf_na
import Submission.Work.PSU3.StageA.caseC_W_semireg
import Submission.Work.PSU3.StageA.caseC_module_data
import Submission.Work.PSU3.StageA.caseC_zeta_action
import Submission.Work.PSU3.StageA.caseC_frame_core

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem coarseFrame_exists {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hst : t * s * t = s * t * s)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) {ζ : G}
    (hζ : ζ ∈ Work.ThmF.W H t) (hζ1 : ζ ≠ 1) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card (Work.ThmF.Q0sub H) = 2 ^ n ∧
      ∃ fr : Work.PSU3.CoarseFrame H Q t n, fr.zc 1 = s ∧ (fr.ζ : G) = ζ := by
  -- In case c) (`|Q| = q³`) the group `Q` is non-abelian (Peterfalvi II, Ch. VI §1).
  have hnab := caseC_not_abelian_cf hS hC4 hHig hcard
  -- `Q₀ = ⟨Inv H⟩ = {x ∈ Q | x² = 1}` and `|Q₀| = 2ⁿ`, `n ≥ 2`.
  have hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 := by
    intro x
    constructor
    · intro hx
      exact Subtype.ext (caseC_mem_Q0sub_iff hS hC4 (x : G) hx)
    · intro hx
      have hxG : (x : G) * (x : G) = 1 := by
        have h := congrArg Subtype.val hx
        simpa [Subgroup.coe_mul] using h
      by_cases h1 : (x : G) = 1
      · rw [h1]
        exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H)
      · have ho : orderOf (x : G) = 2 :=
          orderOf_eq_prime (by rw [pow_two]; exact hxG) h1
        exact Work.ThmF.Q0_le_Q0sub H
          (Work.ThmF.involutions_subset_Q0 H ⟨hS.split.le x.2, ho⟩)
  obtain ⟨n, hn2, hcardn⟩ : ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (caseC_Q0sub_isPGroup hS)
    have hcard0 := caseC_card_Q0sub_eq hS hC4
    have hinv2 : 2 ≤ (involutions (H : Set G)).ncard :=
      Work.ThmF.Bender.cardInvGeTwo hS.split.stronglyEmbedded hS.situation.1.1
    refine ⟨n, ?_, hn⟩
    have h3 : 3 ≤ 2 ^ n := by rw [← hn, hcard0]; omega
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num at h3
    · exact h
  -- `W` acts semiregularly on `Q ∖ Q₀` (Peterfalvi II, Ch. V §2 Lemma 2 c)).
  have hW := caseC_W_semireg hS hC4 hHig hcard
  -- The conjugation action of `ζ` on `Q/Q₀` is fixed-point-free and `ord ζ ∣ q + 1`.
  obtain ⟨hζd, hζf⟩ := caseC_zeta_action hS hC4 hHig hcard hnab hZ hW hζ hζ1
  -- The field `F_q` with `Q₀ ≅ (F_q,+)` and `Q/Q₀ ≅ F_q²` (`K` acting by scalars).
  obtain ⟨D⟩ := caseC_module_data hS hC4 hHig hcard hnab hZ hW hζ hζ1
  -- The coarse frame itself: the quadratic extension `E = F_{q²}`, `bar`, `κ`, `zc`, `nm`.
  obtain ⟨fr, hzc, hzeta⟩ :=
    caseC_frame_core hS hC4 D hn2 hcardn hZ hW hs hs2 hst hζ hζ1 hζd hζf
  exact ⟨n, hn2, hcardn, fr, hzc, hzeta⟩

end Work.PSU3.StageA
