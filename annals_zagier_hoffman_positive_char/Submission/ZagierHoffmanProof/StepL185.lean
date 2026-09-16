import Submission.ZagierHoffmanProof.StepL184
import Submission.ZagierHoffmanProof.StepL148

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L185: ★★ `maink_case2_qqq_amb` — the all-`q` CASE-2 leaf at an AMBIENT level

The first of the three ambient chain ports (PLAN SESSION 272/273): the `maink_case2_qqq` leaf
(StepL148) runs at its own level `k` but its OUTPUTS are required to be `Λ`-admissible and the
recursion hypothesis receives the AMBIENT `ambNu Λ` descent — supplied by StepL175's
`maink_case2_qqq_amb_step` (the qqq members strictly drop at `k`, and their depth is `> k`, so
`ambNu Λ` strictly decreases at every ambient `Λ ≥ k`).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem maink_case2_qqq_amb (w : ℕ) (k : ℕ) (s : Fin k → ℕ+) (hw : weight k s = w)
    (hk1 : 1 ≤ k) (hk2 : 2 ≤ k)
    (hallq : ∀ i : Fin k, (s i : ℕ) = Nat.card F)
    (Λ : ℕ) (hΛ : k ≤ Λ)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      ambNu Λ (Nat.card F) w m < ambNu Λ (Nat.card F) w s →
        ¬ kAdmissible (Nat.card F) m Λ → AdmExpT F w Λ m) :
    AdmExpT F w Λ s := by
  classical
  let D := toData F (r1Rel F)
  let E := RelData.BCqIter F (k - 1) D
  let u : D.ιA := PUnit.unit
  let uE : E.ιA := RelData.iterIdx F (k - 1) D u
  have hdep1 : (toData F (r1Rel F)).depA PUnit.unit = 1 := rfl
  have hEqdep : E.depA uE = k := by
    dsimp [uE, u, E, D]
    rw [RelData.BCqIter_depA_at F (k - 1) (toData F (r1Rel F)) PUnit.unit, hdep1]
    omega
  -- (1) the ζ-identity with the collapsed a-side
  have haz : ζ_A F (E.cA uE) = ζ_A F s := by
    dsimp [uE, u, E, D]
    exact BCqIter_r1_cA_zeta F (k - 1) k (by rw [hdep1]; omega) s hallq
  have hz0 : (∑ i : E.ιA, (((E.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cA i))) +
      (∑ p : E.ιB, (((E.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cB p))) = 0 := by
    have hz := BCqIter_zeta_zero F (k - 1) (r1Rel F)
    rw [toBinaryRel_zeta_eq F E (BCqIter_valid F (k - 1) (r1Rel F))] at hz
    simpa [E, D] using hz
  have ha : (∑ i : E.ιA, (((E.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cA i)))
      = ζ_A F s := by
    rw [← RelData.sum_iterIdx F (k - 1) D
      (fun i => (((E.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cA i)))]
    have hcollapse : (∑ i : D.ιA, (((E.aA (RelData.iterIdx F (k - 1) D i) : RatFunc F) :
            RatFunc.CompletionAtInfty F) * ζ_A F (E.cA (RelData.iterIdx F (k - 1) D i))))
        = (((E.aA uE : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cA uE)) := by
      haveI : Subsingleton D.ιA := ⟨fun a b => by cases a; cases b; rfl⟩
      have h := Fintype.sum_subsingleton (f := fun i : D.ιA =>
        (((E.aA (RelData.iterIdx F (k - 1) D i) : RatFunc F) :
            RatFunc.CompletionAtInfty F) * ζ_A F (E.cA (RelData.iterIdx F (k - 1) D i)))) u
      simpa [uE] using h
    rw [hcollapse]
    have ha1 : (E.aA uE : RatFunc F) = 1 := by
      dsimp [uE, u]
      rw [RelData.BCqIter_aA_at F (k - 1) D PUnit.unit]
      rfl
    rw [ha1, haz]
    simp [completion_coe_one]
  have hrel : ζ_A F s +
      (∑ p : E.ιB, (((E.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cB p))) = 0 := by
    rw [← ha]
    simpa using hz0
  -- (2) the member facts
  have hbasW : ∀ j : D.ιB, weight (D.depB j) (D.cB j) = Nat.card F := by
    intro j
    change weight 2 (pair oneExp (qMinusExp F)) = Nat.card F
    rw [weight_pair]
    change 1 + (Nat.card F - 1) = Nat.card F
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  have hwt : ∀ p : E.ιB, weight (E.depB p) (E.cB p) = w := by
    intro p
    have hO := RelData.BCqIterO_cB_weight F (k - 1) D (Nat.card F) hbasW
    have hchain : RelData.BCqIterO F (k - 1) D = E := RelData.BCqIterO_eq_BCqIter F (k - 1) D
    have hwT := RelData.cB_weight_eq_of_eq F hchain p
    rw [← hwT, hO (hchain.symm ▸ p)]
    have hkq : w = k * Nat.card F := by
      rw [← hw, weight, Finset.sum_congr rfl (fun i _ => hallq i)]
      simp
    have hqm : (k - 1) * Nat.card F + Nat.card F = k * Nat.card F := by
      have hk : k = (k - 1) + 1 := by omega
      conv_rhs => rw [hk]
      rw [Nat.succ_mul]
    rw [hkq]
    exact hqm
  have hg : ∀ j : D.ιB, ∀ m : ℕ,
      psum (D.cB j) m ≤ (if m = 0 then 0 else if m ≤ 1 then m else Nat.card F) := by
    intro j m
    cases j
    change psum (pair oneExp (qMinusExp F)) m ≤
      (if m = 0 then 0 else if m ≤ 1 then m else Nat.card F)
    rcases m with _ | _ | m
    · rw [psum_zero, if_pos rfl]
    · rw [if_neg (by omega : ¬ ((1 : ℕ) = 0)), if_pos (by omega : (1 : ℕ) ≤ 1)]
      rw [show (1 : ℕ) = 0 + 1 by omega,
        psum_succ (pair oneExp (qMinusExp F)) 0, psum_zero, pad0_pair_zero]
      change (1 : ℕ) ≤ 1
      omega
    · rw [if_neg (by omega : ¬ (m + 2 = 0)), if_neg (by omega : ¬ (m + 2 ≤ 1))]
      rw [psum_ge_depth (pair oneExp (qMinusExp F)) (by omega : 2 ≤ m + 2), weight_pair]
      change 1 + (Nat.card F - 1) ≤ Nat.card F
      have h2 : 2 ≤ Nat.card F := card_ge_two F
      omega
  have hdrop : ∀ p : E.ιB, psum (E.cB p) k < psum s k := by
    intro p
    have hchain : RelData.BCqIterO F (k - 1) D = E := RelData.BCqIterO_eq_BCqIter F (k - 1) D
    have hps := RelData.psum_cB_eq_of_eq F hchain p k
    have hO := RelData.BCqIterO_cB_psum_le F (k - 1) D
      (fun m => (if m = 0 then 0 else if m ≤ 1 then m else Nat.card F)) hg
      (hchain.symm ▸ p) k (by omega)
    rw [hps] at hO
    have hidx : k - (k - 1) = 1 := by omega
    rw [hidx] at hO
    have hgone : (if (1 : ℕ) = 0 then 0 else if (1 : ℕ) ≤ 1 then 1 else Nat.card F) = 1 := by
      rw [if_neg (by omega : ¬ ((1 : ℕ) = 0)), if_pos (by omega : (1 : ℕ) ≤ 1)]
    rw [hgone] at hO
    have hpsk : psum s k = k * Nat.card F := by
      change (∑ j ∈ Finset.range k, pad0 s j) = k * Nat.card F
      rw [Finset.sum_congr rfl (fun j hj => ?_)]
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
      · rw [pad0_of_lt s (Finset.mem_range.mp hj)]
        exact hallq _
    rw [hpsk]
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    have hksub : (k - 1) * Nat.card F + 1 < k * Nat.card F := by
      have hk : k = (k - 1) + 1 := by omega
      have hks : k * Nat.card F = (k - 1) * Nat.card F + Nat.card F := by
        conv_lhs => rw [hk]
        rw [Nat.succ_mul]
      rw [hks]
      omega
    omega
  -- (3) the fold and the dispatch
  let mdep (p : E.ιB) : ℕ := E.depB p
  let mhdep (p : E.ιB) : 0 < mdep p := E.hdepB p
  let mc (p : E.ιB) : Fin (mdep p) → ℕ+ := E.cB p
  let ma (p : E.ιB) : RatFunc F := -(E.aB p)
  have hid : ζ_A F s = ∑ p : E.ιB,
      (((ma p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc p)) := by
    have h' : ζ_A F s = -(∑ p : E.ιB,
        (((E.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cB p))) :=
      eq_neg_of_add_eq_zero_left hrel
    rw [h', ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [ma, mc]
    exact (neg_coe_mul_zeta F (E.aB p) (E.cB p)).symm
  have horder : ∀ p : E.ιB, ∀ ℓ : ℕ, Λ ≤ ℓ → psum (mc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    have hkℓ : k ≤ ℓ := le_trans hΛ hℓ
    rw [psum_ge_depth s hkℓ]
    calc
      psum (mc p) ℓ ≤ weight (mdep p) (mc p) := psum_le_weight (mc p) ℓ
      _ = w := by
            dsimp [mdep, mc]
            exact hwt p
      _ = weight k s := hw.symm
  have e : ∀ p : E.ιB, AdmExpT F w Λ (mc p) := by
    intro p
    have hwv : weight (mdep p) (mc p) = w := by
      dsimp [mdep, mc]
      exact hwt p
    by_cases hkadm : kAdmissible (Nat.card F) (mc p) Λ
    · exact admExpT_self F w Λ (mhdep p) (mc p) hwv hkadm
    · refine rec (mdep p) (mc p) hwv ?_ hkadm
      dsimp only [mdep, mc]
      exact maink_case2_qqq_amb_step F w k s hw hk1 hallq p Λ hΛ
  exact admExpT_combine F w Λ s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
