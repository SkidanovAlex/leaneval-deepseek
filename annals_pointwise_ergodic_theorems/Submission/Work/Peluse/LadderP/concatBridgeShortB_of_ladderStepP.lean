import Mathlib
import Submission.Work.Peluse.Holds.LadderP
import Submission.Work.Peluse.concatBridgeShortA
import Submission.Work.Peluse.LadderP.smallnessPOne
import Submission.Work.Peluse.LadderP.smallnessPTwo

/-! Guidance from the project lead (the requester):

LEAD (curric-46): node of Submission/Work/Peluse/LADDER_STEP_LEAD.md (Claude design, 2026-10-03), section 5.2 (P5, iterate the steps; adapt the proved concatBridgeShortA_of_ladderStepQ bookkeeping; 300–500 lines), which gives the proof sketch with explicit constants. Definitions are in the LEAD-FROZEN Submission/Work/Peluse/Holds/LadderP.lean (namespace Work.Peluse.LadderP; do not edit it). Background: the constant-loss ladder (ladderStepQ, CaseSU*, Peluse54SThm, ...) is FALSE (LADDER_STEP_LEAD §1), so do not reuse those statements; their helper lemmas may be reused only if they are true as stated.  Split it into children in parallel where natural. Never write the words "theorem concatBridgeShortB_of_ladderStepP" in comments/docstrings.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

/-! ## The running constants of the power-loss ladder

This is the bookkeeping of `LADDER_STEP_LEAD` §5.2: the `s`-fold iteration of the one-step interface
`ladderStepP` along `Holds.boxLadder`.  Unlike the constant-factor ladder of
`concatBridgeShortA_of_ladderStepQ`, the step now adds `sp j n` long slots and loses a *power*
`C·u^e` of the running value, and both the number of added slots and the loss exponent depend on the
number `n` of slots already carried.  The running data are therefore defined by recursion on the
step index. -/

/-- The number of long slots accumulated after `k` steps of the power-loss ladder (`s` steps in all):
step `k` sits at level `j = s-1-k` and adds `sp j n` slots, `n` being the number already
accumulated. -/
def naccP (s : ℕ) (sp : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (k + 1) => naccP s sp k + sp (s - 1 - k) (naccP s sp k)

lemma naccP_zero (s : ℕ) (sp : ℕ → ℕ → ℕ) : naccP s sp 0 = 0 := rfl

lemma naccP_succ (s k : ℕ) (sp : ℕ → ℕ → ℕ) :
    naccP s sp (k + 1) = naccP s sp k + sp (s - 1 - k) (naccP s sp k) := rfl

lemma naccP_mono (s : ℕ) (sp : ℕ → ℕ → ℕ) {k l : ℕ} (hkl : k ≤ l) :
    naccP s sp k ≤ naccP s sp l := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih =>
      rw [naccP_succ]
      exact le_trans ih (Nat.le_add_right _ _)

lemma naccP_ge_self (s : ℕ) (sp : ℕ → ℕ → ℕ) (hsp : ∀ j n, 1 ≤ sp j n) :
    ∀ k, k ≤ naccP s sp k := by
  intro k
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      rw [naccP_succ]
      have h := hsp (s - 1 - k) (naccP s sp k)
      omega

/-- The running exponent after `k` steps of the power-loss ladder. -/
def kexpP (s : ℕ) (sp : ℕ → ℕ → ℕ) (ep : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | (k + 1) => kexpP s sp ep k * ep (s - 1 - k) (naccP s sp k)

lemma kexpP_zero (s : ℕ) (sp ep : ℕ → ℕ → ℕ) : kexpP s sp ep 0 = 1 := rfl

lemma kexpP_succ (s k : ℕ) (sp ep : ℕ → ℕ → ℕ) :
    kexpP s sp ep (k + 1) = kexpP s sp ep k * ep (s - 1 - k) (naccP s sp k) := rfl

lemma kexpP_ge_one (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (hep : ∀ j n, 1 ≤ ep j n) :
    ∀ k, 1 ≤ kexpP s sp ep k := by
  intro k
  induction k with
  | zero => rw [kexpP_zero]
  | succ k ih => rw [kexpP_succ]; exact one_le_mul ih (hep _ _)

lemma kexpP_mono (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (hep : ∀ j n, 1 ≤ ep j n) {k l : ℕ}
    (hkl : k ≤ l) : kexpP s sp ep k ≤ kexpP s sp ep l := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih =>
      rw [kexpP_succ]
      calc kexpP s sp ep k ≤ kexpP s sp ep l := ih
        _ = kexpP s sp ep l * 1 := (mul_one _).symm
        _ ≤ kexpP s sp ep l * ep (s - 1 - l) (naccP s sp l) :=
            Nat.mul_le_mul (le_refl _) (hep _ _)

/-- Every step exponent of the ladder is at most the total exponent `kexpP s sp ep s`. -/
lemma ep_le_kexpP (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (hep : ∀ j n, 1 ≤ ep j n) {k : ℕ} (hk : k < s) :
    ep (s - 1 - k) (naccP s sp k) ≤ kexpP s sp ep s := by
  have h1 : ep (s - 1 - k) (naccP s sp k) ≤ kexpP s sp ep (k + 1) := by
    rw [kexpP_succ]
    calc ep (s - 1 - k) (naccP s sp k) = 1 * ep (s - 1 - k) (naccP s sp k) := (one_mul _).symm
      _ ≤ kexpP s sp ep k * ep (s - 1 - k) (naccP s sp k) :=
          Nat.mul_le_mul (kexpP_ge_one s sp ep hep k) (le_refl _)
  exact le_trans h1 (kexpP_mono s sp ep hep (by omega))

/-- The running constant after `k` steps of the power-loss ladder (base `min 1 C₁`). -/
def cstP (s : ℕ) (sp : ℕ → ℕ → ℕ) (ep : ℕ → ℕ → ℕ) (cp : ℕ → ℕ → ℝ) (C₁ : ℝ) : ℕ → ℝ
  | 0 => min 1 C₁
  | (k + 1) =>
      cp (s - 1 - k) (naccP s sp k) * (cstP s sp ep cp C₁ k) ^ (ep (s - 1 - k) (naccP s sp k))

lemma cstP_zero (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (cp : ℕ → ℕ → ℝ) (C₁ : ℝ) :
    cstP s sp ep cp C₁ 0 = min 1 C₁ := rfl

lemma cstP_succ (s k : ℕ) (sp ep : ℕ → ℕ → ℕ) (cp : ℕ → ℕ → ℝ) (C₁ : ℝ) :
    cstP s sp ep cp C₁ (k + 1) =
      cp (s - 1 - k) (naccP s sp k) * (cstP s sp ep cp C₁ k) ^ (ep (s - 1 - k) (naccP s sp k)) :=
  rfl

lemma cstP_pos (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (cp : ℕ → ℕ → ℝ) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hcp : ∀ j n, 0 < cp j n) : ∀ k, 0 < cstP s sp ep cp C₁ k := by
  intro k
  induction k with
  | zero => rw [cstP_zero]; exact lt_min one_pos hC₁
  | succ k ih => rw [cstP_succ]; exact mul_pos (hcp _ _) (pow_pos ih _)

lemma cstP_le_one (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (cp : ℕ → ℕ → ℝ) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hcp0 : ∀ j n, 0 < cp j n) (hcp1 : ∀ j n, cp j n ≤ 1) :
    ∀ k, cstP s sp ep cp C₁ k ≤ 1 := by
  intro k
  induction k with
  | zero => rw [cstP_zero]; exact min_le_left _ _
  | succ k ih =>
      rw [cstP_succ]
      have h0 : 0 ≤ cstP s sp ep cp C₁ k := (cstP_pos s sp ep cp hC₁ hcp0 k).le
      calc cp (s - 1 - k) (naccP s sp k)
            * (cstP s sp ep cp C₁ k) ^ (ep (s - 1 - k) (naccP s sp k))
          ≤ 1 * 1 := mul_le_mul (hcp1 _ _) (pow_le_one₀ h0 ih) (pow_nonneg h0 _) (by norm_num)
        _ = 1 := mul_one 1

/-- The running constant is nonincreasing in the number of steps taken. -/
lemma cstP_anti (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (cp : ℕ → ℕ → ℝ) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hcp0 : ∀ j n, 0 < cp j n) (hcp1 : ∀ j n, cp j n ≤ 1) (hep : ∀ j n, 1 ≤ ep j n) :
    ∀ k, cstP s sp ep cp C₁ (k + 1) ≤ cstP s sp ep cp C₁ k := by
  intro k
  have h0 : 0 ≤ cstP s sp ep cp C₁ k := (cstP_pos s sp ep cp hC₁ hcp0 k).le
  have h1 : cstP s sp ep cp C₁ k ≤ 1 := cstP_le_one s sp ep cp hC₁ hcp0 hcp1 k
  rw [cstP_succ]
  calc cp (s - 1 - k) (naccP s sp k) * (cstP s sp ep cp C₁ k) ^ (ep (s - 1 - k) (naccP s sp k))
      ≤ 1 * (cstP s sp ep cp C₁ k) ^ (ep (s - 1 - k) (naccP s sp k)) :=
        mul_le_mul_of_nonneg_right (hcp1 _ _) (pow_nonneg h0 _)
    _ = (cstP s sp ep cp C₁ k) ^ (ep (s - 1 - k) (naccP s sp k)) := one_mul _
    _ ≤ cstP s sp ep cp C₁ k := by
        simpa using pow_le_pow_of_le_one h0 h1 (hep _ _)

lemma cstP_mono (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (cp : ℕ → ℕ → ℝ) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hcp0 : ∀ j n, 0 < cp j n) (hcp1 : ∀ j n, cp j n ≤ 1) (hep : ∀ j n, 1 ≤ ep j n) {k l : ℕ}
    (hkl : k ≤ l) : cstP s sp ep cp C₁ l ≤ cstP s sp ep cp C₁ k := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact le_trans (cstP_anti s sp ep cp hC₁ hcp0 hcp1 hep l) ih

/-- The step constant `cp` dominates the final running constant `cstP … s`. -/
lemma cstP_le_cp (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (cp : ℕ → ℕ → ℝ) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hcp0 : ∀ j n, 0 < cp j n) (hcp1 : ∀ j n, cp j n ≤ 1) (hep : ∀ j n, 1 ≤ ep j n)
    {k : ℕ} (hk : k < s) : cstP s sp ep cp C₁ s ≤ cp (s - 1 - k) (naccP s sp k) := by
  have h1 : cstP s sp ep cp C₁ (k + 1) ≤ cp (s - 1 - k) (naccP s sp k) := by
    rw [cstP_succ]
    have h0 : 0 ≤ cstP s sp ep cp C₁ k := (cstP_pos s sp ep cp hC₁ hcp0 k).le
    have h2 : (cstP s sp ep cp C₁ k) ^ (ep (s - 1 - k) (naccP s sp k)) ≤ 1 :=
      pow_le_one₀ h0 (cstP_le_one s sp ep cp hC₁ hcp0 hcp1 k)
    calc cp (s - 1 - k) (naccP s sp k) * (cstP s sp ep cp C₁ k) ^ (ep (s - 1 - k) (naccP s sp k))
        ≤ cp (s - 1 - k) (naccP s sp k) * 1 :=
          mul_le_mul_of_nonneg_left h2 (hcp0 _ _).le
      _ = cp (s - 1 - k) (naccP s sp k) := mul_one _
  exact le_trans (cstP_mono s sp ep cp hC₁ hcp0 hcp1 hep (by omega)) h1

/-- The two factors of the running value at step `k + 1` are the step constant times the `e_k`-th
power of the running value at step `k`. -/
lemma cstP_mul_pow_succ (s : ℕ) (sp ep : ℕ → ℕ → ℕ) (cp : ℕ → ℕ → ℝ) (C₁ : ℝ) (K₁ : ℕ)
    (γ : ℝ) (k : ℕ) :
    cstP s sp ep cp C₁ (k + 1) * γ ^ (K₁ * kexpP s sp ep (k + 1))
      = cp (s - 1 - k) (naccP s sp k)
          * (cstP s sp ep cp C₁ k * γ ^ (K₁ * kexpP s sp ep k))
              ^ (ep (s - 1 - k) (naccP s sp k)) := by
  have hpow : γ ^ (K₁ * (kexpP s sp ep k * ep (s - 1 - k) (naccP s sp k)))
      = (γ ^ (K₁ * kexpP s sp ep k)) ^ (ep (s - 1 - k) (naccP s sp k)) := by
    rw [← Nat.mul_assoc, pow_mul]
  rw [cstP_succ, kexpP_succ, hpow, mul_pow]
  ring

theorem concatBridgeShortB_of_ladderStepP (h : ∀ j : ℕ, Work.Peluse.LadderP.ladderStepP j) :
    Work.Peluse.LadderP.ConcatBridgeShortB := by
  classical
  intro s hs C₁ hC₁ K₁ hK₁
  choose sp hsp ep hep cp hcp0 hcp1 hstep using h
  set E : ℕ := kexpP s sp ep s with hEdef
  have hE1 : 1 ≤ E := by rw [hEdef]; exact kexpP_ge_one s sp ep hep s
  set c₀ : ℝ := cstP s sp ep cp C₁ s with hc₀def
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; exact cstP_pos s sp ep cp hC₁ hcp0 s
  have hc₀le1 : c₀ ≤ 1 := by rw [hc₀def]; exact cstP_le_one s sp ep cp hC₁ hcp0 hcp1 s
  set A : ℝ := max 4 ((2 : ℝ) ^ (E + 1) / c₀ ^ (E + 1)) with hAdef
  have hA4 : (4 : ℝ) ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hApos : (0 : ℝ) < A := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hAkey : (2 : ℝ) ^ (E + 1) / c₀ ^ (E + 1) ≤ A := by
    rw [hAdef]; exact le_max_right _ _
  refine ⟨max (naccP s sp s) 2, le_max_right _ _, c₀ / 2, by positivity, A, hA1,
      K₁ * E * E + E + 1, by omega, ?_⟩
  intro c hc K hK N M₁ M₂ γ γ' f hM2 hM21 hN hNM hsup hbd hγ0 hγ1 hγ'0 hAγ' hAM₂ hbox
  obtain ⟨ωOf, hinjω, hnzω, hboxineq⟩ := hbox
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hM₂1 : (1 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM2
  have hM₂M₁ : (M₂ : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM21
  have hM₁pos : 1 ≤ M₁ := le_trans hM2 hM21
  have hM₁posR : (0 : ℝ) ≤ (M₁ : ℝ) := by positivity
  have hK1 : 1 ≤ K := by omega
  -- `γ' ≤ 1`
  have hγ'1 : γ' ≤ 1 := by
    have h1 : γ' ≤ γ ^ K / A := (le_div_iff₀ hApos).mpr (by linarith [hAγ'])
    have h2 : γ ^ K / A ≤ 1 := by
      rw [div_le_one hApos]
      exact le_trans (pow_le_one₀ hγ0.le hγ1) hA1
    linarith
  have hγγ'0 : 0 < γ * γ' := mul_pos hγ0 hγ'0
  have hγγ'1 : γ * γ' ≤ 1 := by nlinarith [hγ0.le, hγ'0.le, hγ1, hγ'1]
  -- the two consequences of the frozen non-degeneracy hypothesis
  have hkey : A * γ' ≤ γ' * (M₂ : ℝ) * (γ * γ') ^ K := by
    have h := mul_le_mul_of_nonneg_right hAM₂ hγ'0.le
    calc A * γ' ≤ (M₂ : ℝ) * (γ * γ') ^ K * γ' := h
      _ = γ' * (M₂ : ℝ) * (γ * γ') ^ K := by ring
  have hpowγ' : (γ * γ') ^ K ≤ γ' := by
    have h1 : (γ * γ') ^ K ≤ (γ') ^ K := by
      rw [mul_pow]
      calc γ ^ K * γ' ^ K ≤ 1 * γ' ^ K :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hγ0.le hγ1) (by positivity)
        _ = γ' ^ K := one_mul _
    have h2 : (γ') ^ K ≤ (γ') ^ 1 := pow_le_pow_of_le_one hγ'0.le hγ'1 hK1
    simpa using le_trans h1 h2
  have hγ'M₂4 : 4 ≤ γ' * (M₂ : ℝ) := by
    have h1 : A * γ' ≤ γ' * (M₂ : ℝ) * γ' :=
      le_trans hkey (mul_le_mul_of_nonneg_left hpowγ' (by positivity))
    have h2 : A ≤ γ' * (M₂ : ℝ) := (mul_le_mul_iff_of_pos_right hγ'0).mp h1
    linarith
  have hγ'M₁4 : 4 ≤ γ' * (M₁ : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hM₂M₁ hγ'0.le
    linarith
  -- the two windows
  set Lwin : ℕ := (⌊γ' * (M₂ : ℝ)⌋).toNat with hLwindef
  set Dwin : ℕ := (⌊γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat with hDwindef
  have hfloorpos : (0 : ℤ) ≤ ⌊γ' * (M₂ : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
  have hDfloorpos : (0 : ℤ) ≤ ⌊γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  have hLcast : ((Lwin : ℕ) : ℝ) = ((⌊γ' * (M₂ : ℝ)⌋ : ℤ) : ℝ) := by
    rw [hLwindef]
    exact_mod_cast (Int.toNat_of_nonneg hfloorpos)
  have hDcast : ((Dwin : ℕ) : ℝ) = ((⌊γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ : ℤ) : ℝ) := by
    rw [hDwindef]
    exact_mod_cast (Int.toNat_of_nonneg hDfloorpos)
  have hLin : (Lwin : ℝ) ≤ γ' * (M₂ : ℝ) := by rw [hLcast]; exact Int.floor_le _
  have hLlo : γ' * (M₂ : ℝ) - 1 ≤ (Lwin : ℝ) := by
    have h := Int.lt_floor_add_one (γ' * (M₂ : ℝ))
    rw [← hLcast] at h
    linarith
  have hDin : (Dwin : ℝ) ≤ γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ) := by
    rw [hDcast]; exact Int.floor_le _
  have hDlo : γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ) - 1 ≤ (Dwin : ℝ) := by
    have h := Int.lt_floor_add_one (γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ))
    rw [← hDcast] at h
    linarith
  have hL2 : 2 ≤ Lwin := by
    have h : (2 : ℝ) ≤ (Lwin : ℝ) := by linarith
    exact_mod_cast h
  have hL1 : 1 ≤ Lwin := by omega
  have hLleM₁ : Lwin ≤ M₁ := by
    have h2 : γ' * (M₂ : ℝ) ≤ (M₂ : ℝ) := by nlinarith [hγ'1, hM₂1]
    have h3 : (Lwin : ℝ) ≤ (M₁ : ℝ) := le_trans hLin (le_trans h2 hM₂M₁)
    exact_mod_cast h3
  have hγ'M₂le : γ' * (M₂ : ℝ) ≤ 2 * (Lwin : ℝ) := by linarith [hLlo, hL1]
  have hM₁L : (M₁ : ℝ) * (Lwin : ℝ) ≤ (N : ℝ) / (c : ℝ) := by
    have h2 : γ' * (M₂ : ℝ) ≤ (M₂ : ℝ) := by nlinarith [hγ'1, hM₂1]
    have h3 : (Lwin : ℝ) ≤ (M₂ : ℝ) := le_trans hLin h2
    calc (M₁ : ℝ) * (Lwin : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (N : ℝ) / (c : ℝ) := hNM
  have hDle : (Dwin : ℝ) ≤ 2 * γ' * (M₁ : ℝ) * (Lwin : ℝ) := by
    have h2 : γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ) = (γ' * (M₁ : ℝ)) * (γ' * (M₂ : ℝ)) := by ring
    calc (Dwin : ℝ) ≤ γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ) := hDin
      _ = (γ' * (M₁ : ℝ)) * (γ' * (M₂ : ℝ)) := h2
      _ ≤ (γ' * (M₁ : ℝ)) * (2 * (Lwin : ℝ)) :=
          mul_le_mul_of_nonneg_left hγ'M₂le (by positivity)
      _ = 2 * γ' * (M₁ : ℝ) * (Lwin : ℝ) := by ring
  have hDge : γ' * (M₁ : ℝ) * (Lwin : ℝ) / 2 ≤ (Dwin : ℝ) := by
    have h2 : γ' * (M₁ : ℝ) * (Lwin : ℝ) ≤ γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ) := by
      nlinarith [hLin, hγ'0.le, hM₁posR]
    have h3 : (2 : ℝ) ≤ γ' * (M₁ : ℝ) * (Lwin : ℝ) := by nlinarith [hγ'M₁4, hL2]
    linarith [hDlo, h2, h3]
  have hD1 : 1 ≤ Dwin := by
    have h3 : (2 : ℝ) ≤ γ' * (M₁ : ℝ) * (Lwin : ℝ) := by nlinarith [hγ'M₁4, hL2]
    have h : (1 : ℝ) ≤ (Dwin : ℝ) := by linarith [hDge, h3]
    exact_mod_cast h
  -- the `s`-fold iteration along the ladder
  have hmain : ∀ k : ℕ, k ≤ s →
      cstP s sp ep cp C₁ k * γ ^ (K₁ * kexpP s sp ep k)
        ≤ boxLadderNorm (s - k) (naccP s sp k) M₁ c (Holds.omegaOf (s - k)) Lwin Dwin N f := by
    intro k
    induction k with
    | zero =>
        intro _
        simp only [cstP_zero, kexpP_zero, Nat.mul_one, naccP_zero, Nat.sub_zero]
        calc min 1 C₁ * γ ^ K₁ ≤ C₁ * γ ^ K₁ :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hγ0.le K₁)
          _ ≤ Concat.boxAvg s M₁ c ωOf Lwin N f := hboxineq
          _ = Concat.boxAvg s M₁ c (Holds.omegaOf s) Lwin N f :=
              boxAvg_omegaOf_indep hinjω hnzω
          _ = Holds.boxLadder s 0 M₁ c (Holds.omegaOf s) Lwin Dwin N f :=
              (boxLadder_top' s M₁ c (Holds.omegaOf s) Lwin Dwin N f).symm
          _ ≤ boxLadderNorm s 0 M₁ c (Holds.omegaOf s) Lwin Dwin N f :=
              LadderB.boxLadder_le_norm s 0 M₁ c (Holds.omegaOf s) Lwin Dwin N hbd hsup
    | succ k ih =>
        intro hk
        have hks : k ≤ s := by omega
        have hklt : k < s := by omega
        have hj1 : s - 1 - k + 1 = s - k := by omega
        have hih := ih hks
        rw [← hj1] at hih
        set ek : ℕ := ep (s - 1 - k) (naccP s sp k) with hek
        set ck : ℝ := cp (s - 1 - k) (naccP s sp k) with hck
        set xk : ℝ := cstP s sp ep cp C₁ k * γ ^ (K₁ * kexpP s sp ep k) with hxk
        have hekE : ek ≤ E := by rw [hek, hEdef]; exact ep_le_kexpP s sp ep hep hklt
        have hkE : kexpP s sp ep k ≤ E := by rw [hEdef]; exact kexpP_mono s sp ep hep hks
        have hck0 : 0 < ck := by rw [hck]; exact hcp0 _ _
        have hck_lb : c₀ ≤ ck := by
          rw [hck, hc₀def]
          exact cstP_le_cp s sp ep cp hC₁ hcp0 hcp1 hep hklt
        have hxkpos : 0 < xk := by
          rw [hxk]
          exact mul_pos (cstP_pos s sp ep cp hC₁ hcp0 k) (pow_pos hγ0 _)
        have hxkle1 : xk ≤ 1 := by
          rw [hxk]
          calc cstP s sp ep cp C₁ k * γ ^ (K₁ * kexpP s sp ep k)
              ≤ 1 * 1 := mul_le_mul (cstP_le_one s sp ep cp hC₁ hcp0 hcp1 k)
                  (pow_le_one₀ hγ0.le hγ1) (pow_nonneg hγ0.le _) (by norm_num)
            _ = 1 := mul_one 1
        have hxk_lb : c₀ * γ ^ (K₁ * E) ≤ xk := by
          rw [hxk]
          have h1 : c₀ ≤ cstP s sp ep cp C₁ k := by
            rw [hc₀def]; exact cstP_mono s sp ep cp hC₁ hcp0 hcp1 hep hks
          have h2 : γ ^ (K₁ * E) ≤ γ ^ (K₁ * kexpP s sp ep k) :=
            pow_le_pow_of_le_one hγ0.le hγ1 (Nat.mul_le_mul_left K₁ hkE)
          exact mul_le_mul h1 h2 (pow_nonneg hγ0.le _) (le_trans hc₀pos.le h1)
        have hkEk : (K₁ * E) * ek ≤ K := by
          have h1 : (K₁ * E) * ek ≤ (K₁ * E) * E := Nat.mul_le_mul_left _ hekE
          have h2 : (K₁ * E) * E ≤ K₁ * E * E + E + 1 := by omega
          exact le_trans h1 (le_trans h2 hK)
        have hek1 : ek + 1 ≤ K := by
          have h1 : ek + 1 ≤ E + 1 := by omega
          have h2 : E + 1 ≤ K₁ * E * E + E + 1 := by omega
          exact le_trans h1 (le_trans h2 hK)
        have hldata : (Dwin : ℝ) ≤ ck * xk ^ ek * ((M₁ : ℝ) * (Lwin : ℝ)) := by
          have hge : 2 * γ' ≤ ck * xk ^ ek :=
            le_trans (smallnessPOne hγ0 hγ1 hγ'0 hApos hAγ' hc₀pos hc₀le1 hAkey hkEk hekE
                hxk_lb)
              (mul_le_mul_of_nonneg_right hck_lb (by positivity))
          calc (Dwin : ℝ) ≤ 2 * γ' * (M₁ : ℝ) * (Lwin : ℝ) := hDle
            _ = (2 * γ') * ((M₁ : ℝ) * (Lwin : ℝ)) := by ring
            _ ≤ (ck * xk ^ ek) * ((M₁ : ℝ) * (Lwin : ℝ)) :=
                mul_le_mul_of_nonneg_right hge (by positivity)
            _ = ck * xk ^ ek * ((M₁ : ℝ) * (Lwin : ℝ)) := by ring
        have hkdata : ((M₁ : ℝ) * (Lwin : ℝ)) ^ ek ≤ ck * (xk * (Dwin : ℝ)) ^ ek * (Lwin : ℝ) := by
          have hL : A * γ' / 2 ≤ (Lwin : ℝ) * (γ * γ') ^ K := by
            have h1 : γ' * (M₂ : ℝ) / 2 ≤ (Lwin : ℝ) := by linarith [hγ'M₂le]
            calc A * γ' / 2 = (A * γ') / 2 := by ring
              _ ≤ ((γ' * (M₂ : ℝ)) * (γ * γ') ^ K) / 2 := by linarith [hkey]
              _ = (γ' * (M₂ : ℝ) / 2) * (γ * γ') ^ K := by ring
              _ ≤ (Lwin : ℝ) * (γ * γ') ^ K :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
          have hA' : 1 ≤ A * (c₀ / 2) ^ (E + 1) := by
            have h3 : A * (c₀ / 2) ^ (E + 1) = A * c₀ ^ (E + 1) / 2 ^ (E + 1) := by
              rw [div_pow, mul_div_assoc]
            rw [h3, le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (E + 1)), one_mul]
            calc (2 : ℝ) ^ (E + 1)
                = (2 : ℝ) ^ (E + 1) / c₀ ^ (E + 1) * c₀ ^ (E + 1) :=
                  (div_mul_cancel₀ _ (pow_ne_zero _ (ne_of_gt hc₀pos))).symm
              _ ≤ A * c₀ ^ (E + 1) := mul_le_mul_of_nonneg_right hAkey (by positivity)
          have hcore : 1 ≤ c₀ * (xk * γ' / 2) ^ ek * (Lwin : ℝ) :=
            smallnessPTwo hγ0 hγ1 hγ'0 hγ'1 hxkpos hxk_lb hc₀pos hc₀le1 hA' hkEk hek1 hekE hL
          have hZ0 : 0 ≤ ((M₁ : ℝ) * (Lwin : ℝ)) ^ ek := by positivity
          have hmerge : ((M₁ : ℝ) * (Lwin : ℝ)) ^ ek * (xk * γ' / 2) ^ ek
              = (((M₁ : ℝ) * (Lwin : ℝ)) * (xk * γ' / 2)) ^ ek := (mul_pow _ _ _).symm
          have harg : ((M₁ : ℝ) * (Lwin : ℝ)) * (xk * γ' / 2) ≤ xk * (Dwin : ℝ) := by
            nlinarith [hDge, hxkpos]
          calc ((M₁ : ℝ) * (Lwin : ℝ)) ^ ek
              = ((M₁ : ℝ) * (Lwin : ℝ)) ^ ek * 1 := (mul_one _).symm
            _ ≤ ((M₁ : ℝ) * (Lwin : ℝ)) ^ ek
                  * (c₀ * (xk * γ' / 2) ^ ek * (Lwin : ℝ)) :=
                mul_le_mul_of_nonneg_left hcore hZ0
            _ = c₀ * (((M₁ : ℝ) * (Lwin : ℝ)) ^ ek * (xk * γ' / 2) ^ ek) * (Lwin : ℝ) := by ring
            _ = c₀ * (((M₁ : ℝ) * (Lwin : ℝ)) * (xk * γ' / 2)) ^ ek * (Lwin : ℝ) := by
                rw [hmerge]
            _ ≤ c₀ * (xk * (Dwin : ℝ)) ^ ek * (Lwin : ℝ) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left
                    (pow_le_pow_left₀ (by positivity) harg ek) hc₀pos.le)
                  (by positivity)
            _ ≤ ck * (xk * (Dwin : ℝ)) ^ ek * (Lwin : ℝ) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hck_lb (by positivity)) (by positivity)
        have hstepk := hstep (s - 1 - k) (naccP s sp k) c M₁ Lwin Dwin N f xk
          hc hL2 hLleM₁ hN hM₁L hD1 hsup hbd hxkpos hxkle1 hldata hkdata hih
        rw [show s - (k + 1) = s - 1 - k by omega, naccP_succ s k sp,
          cstP_mul_pow_succ s sp ep cp C₁ K₁ γ k]
        exact hstepk
  -- the bottom of the ladder and the level raise
  have hnacc1 : 1 ≤ naccP s sp s := le_trans hs (naccP_ge_self s sp hsp s)
  have hbot := hmain s le_rfl
  rw [Nat.sub_self, boxLadderNorm_zero] at hbot
  have hbot' : c₀ * γ ^ (K₁ * E) ≤ uNorm (naccP s sp s) (arithIcc c Dwin) (symIcc N) f := by
    have hthis : cstP s sp ep cp C₁ s * γ ^ (K₁ * kexpP s sp ep s) = c₀ * γ ^ (K₁ * E) := by
      rw [hc₀def, hEdef]
    rwa [hthis] at hbot
  have hKgeE : K₁ * E ≤ K := by
    have h1 : K₁ * E ≤ (K₁ * E) * E := by
      have h := Nat.mul_le_mul_left (K₁ * E) hE1
      simpa using h
    have h2 : (K₁ * E) * E ≤ K :=
      le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) hK)
    exact le_trans h1 h2
  have hγγ'K : (γ * γ') ^ K ≤ γ ^ (K₁ * E) := by
    have h1 : γ ^ K ≤ γ ^ (K₁ * E) := pow_le_pow_of_le_one hγ0.le hγ1 hKgeE
    have h2 : γ' ^ K ≤ 1 := pow_le_one₀ hγ'0.le hγ'1
    calc (γ * γ') ^ K = γ ^ K * γ' ^ K := mul_pow _ _ _
      _ ≤ γ ^ (K₁ * E) * 1 := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = γ ^ (K₁ * E) := mul_one _
  have hQne : (arithIcc c Dwin).Nonempty := by
    refine ⟨c * 1, ?_⟩
    rw [arithIcc]
    refine Finset.mem_image.mpr ⟨1, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨le_refl 1, hD1⟩
    · ring
  have hQbd : ∀ x ∈ arithIcc c Dwin, |x| ≤ (N : ℤ) := by
    intro x hx
    rw [arithIcc] at hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hn2 : n ≤ Dwin := (Finset.mem_Icc.mp hn).2
    have hDleM : Dwin ≤ M₁ * M₂ := by
      have h1 : (Dwin : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by
        refine le_trans hDin ?_
        have h2 : γ' * γ' ≤ 1 := by nlinarith [hγ'0.le, hγ'1]
        calc γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ) = (γ' * γ') * ((M₁ : ℝ) * (M₂ : ℝ)) := by ring
          _ ≤ 1 * ((M₁ : ℝ) * (M₂ : ℝ)) := mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = (M₁ : ℝ) * (M₂ : ℝ) := one_mul _
      exact_mod_cast h1
    have hcM : (c : ℤ) * ((M₁ : ℤ) * (M₂ : ℤ)) ≤ (N : ℤ) := by
      have h2 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
      have h3 : (c : ℝ) * ((M₁ : ℝ) * (M₂ : ℝ)) = (M₁ : ℝ) * (M₂ : ℝ) * (c : ℝ) := by ring
      have h5 : (M₁ : ℝ) * (M₂ : ℝ) * (c : ℝ) ≤ (N : ℝ) := (le_div_iff₀ h2).mp hNM
      have h6 : (c : ℝ) * ((M₁ : ℝ) * (M₂ : ℝ)) ≤ (N : ℝ) := by rw [h3]; exact h5
      exact_mod_cast h6
    have hxnn : (0 : ℤ) ≤ c * (n : ℤ) := mul_nonneg hc.le (by positivity)
    rw [abs_of_nonneg hxnn]
    calc c * (n : ℤ) ≤ c * (Dwin : ℤ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hn2) hc.le
      _ ≤ c * ((M₁ : ℤ) * (M₂ : ℤ)) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hDleM) hc.le
      _ ≤ (N : ℤ) := hcM
  have hraise := uNorm_le_uNorm_max_two (naccP s sp s) hnacc1 (by omega) hQne hQbd hsup hbd
  have hraise2 : (1 / 2 : ℝ) * uNorm (naccP s sp s) (arithIcc c Dwin) (symIcc N) f
      ≤ uNorm (max (naccP s sp s) 2) (arithIcc c Dwin) (symIcc N) f := by
    have h2 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 / 4 : ℝ) ≤ 1)
      simpa using h
    have h3 : (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 1 := by linarith
    have h4 : 0 ≤ uNorm (max (naccP s sp s) 2) (arithIcc c Dwin) (symIcc N) f :=
      Concat.uNorm_nonneg _ _ _ _
    calc (1 / 2 : ℝ) * uNorm (naccP s sp s) (arithIcc c Dwin) (symIcc N) f
        ≤ (1 / 2 : ℝ) * ((2 : ℝ) ^ (1 / 4 : ℝ)
            * uNorm (max (naccP s sp s) 2) (arithIcc c Dwin) (symIcc N) f) :=
          mul_le_mul_of_nonneg_left hraise (by norm_num)
      _ = ((1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 4 : ℝ))
            * uNorm (max (naccP s sp s) 2) (arithIcc c Dwin) (symIcc N) f := by ring
      _ ≤ 1 * uNorm (max (naccP s sp s) 2) (arithIcc c Dwin) (symIcc N) f :=
          mul_le_mul_of_nonneg_right h3 h4
      _ = uNorm (max (naccP s sp s) 2) (arithIcc c Dwin) (symIcc N) f := one_mul _
  calc c₀ / 2 * (γ * γ') ^ K ≤ c₀ / 2 * γ ^ (K₁ * E) :=
        mul_le_mul_of_nonneg_left hγγ'K (by positivity)
    _ = (1 / 2 : ℝ) * (c₀ * γ ^ (K₁ * E)) := by ring
    _ ≤ (1 / 2 : ℝ) * uNorm (naccP s sp s) (arithIcc c Dwin) (symIcc N) f :=
        mul_le_mul_of_nonneg_left hbot' (by norm_num)
    _ ≤ uNorm (max (naccP s sp s) 2) (arithIcc c Dwin) (symIcc N) f := hraise2

end

end Work.Peluse.LadderP
