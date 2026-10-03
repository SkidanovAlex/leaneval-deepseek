import Mathlib
import Submission.Work.Peluse.LadderP.augJensen
import Submission.Work.Peluse.LadderP.stepConstants
import Submission.Work.Peluse.LadderP.stepPLem
import Submission.Work.Peluse.LadderP.augPowStateLeBoxAvgSum
import Submission.Work.Peluse.LadderP.badMassLe
import Submission.Work.Peluse.LadderP.logLeM1MulEta
import Submission.Work.Peluse.LadderP.coreLeU
import Submission.Work.Peluse.LadderP.stepBadCount
import Submission.Work.Peluse.LadderP.massLower
import Submission.Work.Peluse.LadderP.finalConstLe
import Submission.Work.Peluse.LadderP.smallLeOfCore
import Submission.Work.Peluse.LadderP.nondegLeOfCore

/-! Guidance from the project lead (the requester):

LEAD (curric-46): node of Submission/Work/Peluse/LADDER_STEP_LEAD.md (Claude design, 2026-10-03), section 5.4 (P4, Lemma 5.6 with the carried long slots; 600–1000 lines). Note: step j uses Lemma 5.1 at level 2^j, not j+1 (the Lemma51Defs docstring is wrong), which gives the proof sketch with explicit constants. Definitions are in the LEAD-FROZEN Submission/Work/Peluse/Holds/LadderP.lean (namespace Work.Peluse.LadderP; do not edit it). Background: the constant-loss ladder (ladderStepQ, CaseSU*, Peluse54SThm, ...) is FALSE (LADDER_STEP_LEAD §1), so do not reuse those statements; their helper lemmas may be reused only if they are true as stated.

## Infrastructure now on disk (all sorry-free and building), see `NOTES_P4_ASSEMBLY.md`

* `stepPCore`  — `padL`/`padR`, `headPart`, `dotZ_padL`/`dotZ_padR`, `enumAll`, `augEnum` (+ injective / nonzero)
* `stepPPeel`  — `ABlk0`/`ABlk`/`BBlk`/`longBlk`, the concatenation identities (`ladderSlots_aug_eq`,
  `ladderSlots_j_eq`), the block swap `boxNormPow_append_swap`, and the two peel identities
  `peel_succ_inner` / `peel_concl_inner` (the exact content of the peel)
* `stepPState` — the four states, the two state identities, the shifts `stepShift`/`stepShift3`/
  `stepShiftE` with the exceptional set `stepBad`
* `stepPSupp`  — `SuppSmall`, its preservation by `iterDelta`, `boxNormPow ≤ 1`, `boxNormPow ≤ boxNorm`
* `stepPAve`   — the states after the peel, summed over `(h,h')` and the shift tuples `km`
* `enumIndep`, `augJensen`, `patJensen`, `bslotSum`, `stepConstants` — proved children
* `stepPBridge`, `stepShift3Bound`, `stepPLem` — the bridges and the pointwise Lemma 5.1 input
* `stateBSumBound`, `augPowStateLeBoxAvgSum`, `badMassLe`, `logLeM1MulEta`, `coreLeU` — the assembly bricks
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-! ## Auxiliary arithmetic facts for the assembly -/

/-- `e ≤ 2^K * (1 + 2 e) * e` for every `K`, `e` (the middle factor is at least `1`). -/
private lemma le_smul_expand (K e : ℕ) : e ≤ 2 ^ K * (1 + 2 * e) * e := by
  have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have h2 : 1 ≤ 1 + 2 * e := by omega
  calc e = 1 * 1 * e := by ring
    _ ≤ 2 ^ K * (1 + 2 * e) * e := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (le_refl e)

theorem ladderStepP_of_lemma51P (h : ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.lemma51P t) :
    ∀ j : ℕ, Work.Peluse.LadderP.ladderStepP j := by
  intro j n
  -- the three windows of Lemma 5.1 at level `2^j` (with `B₀ = j+1`)
  obtain ⟨s', hs'1, e₅₁, he₅₁, C₅₁, hC₅₁pos, hC₅₁le1, h51raw⟩ :=
    h (2^j) (Nat.one_le_two_pow) (j+1)
  -- the counting constant and the numeric constants of the step
  obtain ⟨C_s, hC_s_pos, hC_s⟩ := stepBadCount j
  obtain ⟨e, C, cη, he1, hCpos, hCle1, hcηpos, hcηle1, he_ge1, he_ge2, he_ge3,
    hC_le1, hcη_le_C, hC_log, h2Cs, hC_le2⟩ :=
    stepConstants j n s' e₅₁ hs'1 he₅₁ hC₅₁pos hC₅₁le1 hC_s_pos
  refine ⟨s', hs'1, e, he1, C, hCpos, hCle1, ?_⟩
  intro c M₁ L D N f u hc hL2 hLM hN hML hD1 hsup hbd hu0 hu1 hsmall hnondeg hstate
  have hM₁ : 1 ≤ M₁ := le_trans (by omega : 1 ≤ L) hLM
  have hL1 : 1 ≤ L := le_trans (by omega : 1 ≤ 2) hL2
  have hu0' : 0 ≤ u := le_of_lt hu0
  have hfin : FinSuppZ f := ⟨N, hsup⟩
  have hs0 : Fin M₁ := ⟨0, by omega⟩
  -- the three constants of the step
  set γ : ℝ := u ^ (2 ^ (2 ^ (j+1) - 1 + n)) / 4 with hγdef
  set η : ℝ := cη * γ ^ (2 * e₅₁) with hηdef
  set ε : ℝ := C₅₁ * γ ^ e₅₁ with hεdef
  have hγ0 : 0 < γ := by
    rw [hγdef]; exact div_pos (pow_pos hu0 _) (by norm_num)
  have hγnn : 0 ≤ γ := le_of_lt hγ0
  have hγ1 : γ ≤ 1 := by
    rw [hγdef]
    have hnum : u ^ (2 ^ (2 ^ (j+1) - 1 + n)) ≤ 1 := pow_le_one₀ hu0' hu1
    linarith
  have hη0 : 0 < η := by
    rw [hηdef]; exact mul_pos hcηpos (pow_pos hγ0 _)
  have hη1 : η ≤ 1 := by
    rw [hηdef]
    have hpow : γ ^ (2 * e₅₁) ≤ 1 := pow_le_one₀ hγnn hγ1
    have hnn : 0 ≤ γ ^ (2 * e₅₁) := pow_nonneg hγnn _
    nlinarith [hcηle1, hpow, hnn, hcηpos]
  have hηle : η ≤ C₅₁ * γ ^ e₅₁ := by
    rw [hηdef]
    have h1 : γ ^ (2 * e₅₁) ≤ γ ^ e₅₁ :=
      pow_le_pow_of_le_one hγnn hγ1 (by omega : e₅₁ ≤ 2 * e₅₁)
    calc cη * γ ^ (2 * e₅₁) ≤ C₅₁ * γ ^ (2 * e₅₁) :=
          mul_le_mul_of_nonneg_right hcη_le_C (pow_nonneg hγnn _)
      _ ≤ C₅₁ * γ ^ e₅₁ := mul_le_mul_of_nonneg_left h1 (le_of_lt hC₅₁pos)
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hε0' : 0 < ε := by rw [hεdef]; exact mul_pos hC₅₁pos (pow_pos hγ0 _)
  have hεle : ε ≤ C₅₁ * γ ^ e₅₁ := le_of_eq hεdef
  -- (1) the state, raised to the `2^T`-th power
  have hstep1 : u ^ (2 ^ (2 ^ (j+1) - 1 + n)) ≤ augPowState j n M₁ c L D N f := by
    have hstate' : u ≤ augNormState j n M₁ c L D N f := by
      rw [boxLadderNorm_succ_eq_augNormState j n M₁ c L D N f] at hstate
      exact hstate
    exact le_trans (pow_le_pow_left₀ hu0' hstate' (2 ^ (2 ^ (j+1) - 1 + n)))
      (augJensen j n M₁ hM₁ c L D N f hbd hsup)
  -- (2) the peel and the averaging over the averaged parameter
  have havg : u ^ (2 ^ (2 ^ (j+1) - 1 + n)) ≤
      ((M₁ : ℝ))⁻¹ ^ (2*j+1) *
        ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
          ∑ km : KmT j n M₁ c L D h₁ h₁',
            Gwt j n M₁ c L D h₁ h₁' *
              LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) h₁ h₁' h'_s) N
                (Gof j n M₁ c L D h₁ h₁' km f) :=
    le_trans hstep1 (augPowStateLeBoxAvgSum j n M₁ hM₁ c L D N f hfin hbd hsup)
  -- (3) the smallness of `C u^e`
  have hCue : C * u ^ e ≤ 1 := by
    have h1 : u ^ e ≤ 1 := pow_le_one₀ hu0' hu1
    have h2 : 0 ≤ u ^ e := pow_nonneg hu0' e
    nlinarith [hCle1, h1, hCpos, h2]
  have hDle : (D : ℝ) ≤ (M₁ : ℝ) * (L : ℝ) := by
    calc (D : ℝ) ≤ C * u ^ e * ((M₁ : ℝ) * (L : ℝ)) := hsmall
      _ ≤ 1 * ((M₁ : ℝ) * (L : ℝ)) :=
          mul_le_mul_of_nonneg_right hCue (by positivity)
      _ = (M₁ : ℝ) * (L : ℝ) := by ring
  -- (4) the bad mass
  have hlog : Real.log ((j : ℝ) + 2) ≤ (M₁ : ℝ) * η :=
    logLeM1MulEta j n M₁ hM₁ L D hCpos hcηpos he₅₁ hγdef hηdef hu0 hu1 hL2 hLM he_ge2
      hDle hnondeg hC_log
  have hconst : C_s * (2 * (M₁ : ℝ) * η) ≤ ε * γ * (M₁ : ℝ) := by
    rw [hηdef, hεdef]
    have hg2 : γ ^ (2 * e₅₁) ≤ γ ^ e₅₁ * γ := by
      rw [show 2 * e₅₁ = e₅₁ + e₅₁ from by ring, pow_add]
      have h := pow_le_pow_of_le_one hγnn hγ1 (show 1 ≤ e₅₁ by omega)
      simpa using mul_le_mul_of_nonneg_left h (pow_nonneg hγnn e₅₁)
    have hg2nn : 0 ≤ γ ^ (2 * e₅₁) := pow_nonneg hγnn _
    have hM1nn : (0 : ℝ) ≤ M₁ := by positivity
    have hA : C_s * (2 * (M₁ : ℝ) * (cη * γ ^ (2 * e₅₁)))
        = (2 * C_s * cη) * (M₁ * γ ^ (2 * e₅₁)) := by ring
    rw [hA]
    calc (2 * C_s * cη) * (M₁ * γ ^ (2 * e₅₁))
        ≤ C₅₁ * (M₁ * γ ^ (2 * e₅₁)) :=
          mul_le_mul_of_nonneg_right h2Cs (mul_nonneg hM1nn hg2nn)
      _ ≤ C₅₁ * (M₁ * (γ ^ e₅₁ * γ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg2 hM1nn) (le_of_lt hC₅₁pos)
      _ = C₅₁ * γ ^ e₅₁ * γ * (M₁ : ℝ) := by ring
  have hbad : ((M₁ : ℝ))⁻¹ ^ (2*j+1) *
      ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        (if ε * (M₁ : ℝ)
            < ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs0) (Fin.snoc h₁' h'_s)).card : ℝ)
          then (1 : ℝ) else 0) ≤ γ :=
    badMassLe j M₁ hM₁ hγ0 hγ1 hη0 hη1 hε0' hs0 hC_s_pos
      (hC_s M₁ hM₁ η hη0 hη1 (enumAll j)) hlog hconst
  -- (5) the pointwise Lemma 5.1 input
  have hcore : C * u ^ e ≤ C₅₁ * cη ^ e₅₁ * γ ^ ((1 + 2 * e₅₁) * e₅₁) :=
    coreLeU j n he₅₁ hCpos hC₅₁pos hcηpos hγdef hu0 hu1 he_ge1 hC_le1
  have hDsmall : (D : ℝ) ≤ C₅₁ * (γ * η) ^ e₅₁ * ((M₁ : ℝ) * (L : ℝ)) :=
    smallLeOfCore j n M₁ L D hC₅₁pos he₅₁ hu1 hηdef hcore hsmall
  have he_le : e₅₁ ≤ e := le_trans (le_smul_expand (2^(j+1) - 1 + n) e₅₁) he_ge1
  have hnondeg51 : ((M₁ : ℝ) * (L : ℝ)) ^ e₅₁ ≤ C₅₁ * (γ * η * (D : ℝ)) ^ e₅₁ * (L : ℝ) :=
    nondegLeOfCore j n M₁ L D hM₁ hC₅₁pos he₅₁ he_le hL1 hηdef hcore hDle hnondeg
  have lem : ∀ (h₁ : Fin j → Fin M₁) (h₁' : Fin j → Fin M₁) (h'_s : Fin M₁)
      (km : KmT j n M₁ c L D h₁ h₁'),
      γ ≤ LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) h₁ h₁' h'_s) N
            (Gof j n M₁ c L D h₁ h₁' km f) →
      ¬ (ε * (M₁ : ℝ)
          < ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs0) (Fin.snoc h₁' h'_s)).card : ℝ)) →
      (C₅₁ * γ ^ e₅₁) ^ (2^s') ≤ Gpow j n s' M₁ c L D N h₁ h₁' km f :=
    lemma51Step j n M₁ hM₁ c L D N f hC₅₁pos hC₅₁le1 hs'1 he₅₁ h51raw hc hL2 hLM hN hML
      hD1 hfin hbd hsup hγ0 hγ1 hη0 hηle hε0 hεle hDsmall hnondeg51 hs0
  -- (6) the reassembly
  have hmass : 2 * γ * (C₅₁ * γ ^ e₅₁) ^ (2^s') ≤ patPowState j (n+s') M₁ c L D N f :=
    massLower j n M₁ hM₁ c L D N f hfin hbd hsup hs0 hs'1 he₅₁ hC₅₁pos hC₅₁le1
      hγdef hu0 hu1 hεdef havg hbad lem
  -- (7) the constants
  have hfinal : 2 * γ * (C₅₁ * γ ^ e₅₁) ^ (2^s') ≤
      boxLadderNorm j (n+s') M₁ c (Holds.omegaOf j) L D N f := by
    rw [boxLadderNorm_eq_patNormState j (n+s') M₁ c L D N f]
    exact le_trans hmass (patJensen j (n+s') M₁ hM₁ c L D N f hbd hsup)
  have hconst2 : C * u ^ e ≤ 2 * γ * (C₅₁ * γ ^ e₅₁) ^ (2^s') :=
    finalConstLe j n s' e₅₁ hCpos hC₅₁pos he₅₁ hγdef hu0 hu1 he_ge3 hC_le2
  exact le_trans hconst2 hfinal

end

end Work.Peluse.LadderP
