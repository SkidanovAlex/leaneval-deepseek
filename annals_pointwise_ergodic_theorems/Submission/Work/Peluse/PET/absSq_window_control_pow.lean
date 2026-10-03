/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.WindowControl.boxNormPow_one_window
import Submission.Work.Peluse.WindowControl.sqrtGamma_le_windowSum

/-!
# Window control with the exponent `2 ^ (m-1)` made explicit

`Work.Peluse.WindowControl.absSq_window_control` produces *some* `K ≥ 1` such that the
`m`-linear average being of size `≥ √γ` forces the level-one box norm of `|F_m|^{2^{m-1}}`
to be at least `(γ/1000)^K`.  In fact its proof computes with `K = 2^{m-1}`; this file
records that statement with the exponent made explicit (the `∃ K` wrapper removed).

The proof is a verbatim copy of the proof of `absSq_window_control` (the private helper
lemmas `card_symIcc`, `card_window`, `card_bound`, `final_assembly` are reproduced here).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Work.Peluse.PET

private lemma card_symIcc (N : ℕ) : (Work.Peluse.symIcc N).card = 2 * N + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : ((N : ℤ) + 1 - (-(N : ℤ))) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

private lemma card_window (N : ℕ) : (Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))).card = 4 * N + 1 := by
  rw [Int.card_Icc]
  have h : (2 * (N : ℤ) + 1 - (-(2 * (N : ℤ)))) = ((4 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

private lemma card_bound (N p : ℕ) (hN : 0 < N) (hp : 1 ≤ p) :
    (2 * (N : ℝ) + 1) * (4 * (N : ℝ) + 1) ^ (2 * p - 1) ≤ 1000 ^ p * (N : ℝ) ^ (2 * p) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNnn : (0 : ℝ) ≤ N := by linarith
  have h1 : (2 * (N : ℝ) + 1) ≤ 3 * N := by nlinarith
  have h2 : (4 * (N : ℝ) + 1) ≤ 5 * N := by nlinarith
  have hbase : (3 : ℝ) * 5 ^ (2 * p - 1) ≤ 1000 ^ p := by
    have h25 : (5 : ℝ) ^ (2 * p) ≤ 1000 ^ p := by
      have hsq : (5 : ℝ) ^ (2 * p) = ((5 : ℝ) ^ 2) ^ p := by rw [pow_mul]
      rw [hsq]
      norm_num
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) p
    refine le_trans ?_ h25
    have h5nn : (0 : ℝ) ≤ 5 ^ (2 * p - 1) := by positivity
    have hle : (3 : ℝ) * 5 ^ (2 * p - 1) ≤ 5 * 5 ^ (2 * p - 1) := by nlinarith [h5nn]
    rwa [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * p)] at hle
  calc (2 * (N : ℝ) + 1) * (4 * (N : ℝ) + 1) ^ (2 * p - 1)
      ≤ (3 * N) * (5 * N) ^ (2 * p - 1) := by gcongr
    _ = 3 * 5 ^ (2 * p - 1) * N ^ (2 * p) := by
        rw [mul_pow]
        have hNpow : (N : ℝ) ^ (2 * p - 1) * N = (N : ℝ) ^ (2 * p) := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * p)]
        rw [← hNpow]
        ring
    _ ≤ 1000 ^ p * N ^ (2 * p) := by
        have : (0 : ℝ) ≤ N ^ (2 * p) := by positivity
        nlinarith [hbase, this]


private lemma final_assembly {p N : ℕ} (hp1 : 1 ≤ p) (hN : 0 < N) {γ Sp Qp Kp Rn T1 T2 : ℝ}
    (hγ : 0 < γ) (hSp : 0 < Sp) (hQp : 0 < Qp) (hKp : 0 < Kp)
    (hcard : Sp * Kp ^ (2 * p - 1) ≤ 1000 ^ p * (N : ℝ) ^ (2 * p))
    (hRK : Real.sqrt γ * (N : ℝ) * Qp ≤ Rn)
    (hpm : Rn ^ (2 * p) ≤ Kp ^ (2 * p - 1) * T1)
    (hT : T1 ≤ Qp ^ (2 * p - 2) * T2) :
    (γ / 1000) ^ p ≤ Sp⁻¹ * Qp⁻¹ ^ 2 * T2 := by
  have hCpos : 0 < Kp ^ (2 * p - 1) * Qp ^ (2 * p - 2) := by positivity
  have step1 : (γ / 1000) ^ p * (Sp * Kp ^ (2 * p - 1)) ≤ γ ^ p * (N : ℝ) ^ (2 * p) := by
    rw [div_pow]
    calc (γ ^ p / 1000 ^ p) * (Sp * Kp ^ (2 * p - 1))
        ≤ (γ ^ p / 1000 ^ p) * (1000 ^ p * (N : ℝ) ^ (2 * p)) := by
          apply mul_le_mul_of_nonneg_left hcard; positivity
      _ = γ ^ p * (N : ℝ) ^ (2 * p) := by field_simp
  have hs : (Real.sqrt γ * (N : ℝ) * Qp) ^ (2 * p) = γ ^ p * (N : ℝ) ^ (2 * p) * Qp ^ (2 * p) := by
    rw [mul_pow, mul_pow, pow_mul (Real.sqrt γ) 2 p, Real.sq_sqrt hγ.le]
  have step2 : γ ^ p * (N : ℝ) ^ (2 * p) * Qp ^ (2 * p) ≤ Kp ^ (2 * p - 1) * Qp ^ (2 * p - 2) * T2 := by
    rw [← hs]
    calc (Real.sqrt γ * (N : ℝ) * Qp) ^ (2 * p) ≤ Rn ^ (2 * p) :=
          pow_le_pow_left₀ (by positivity) hRK (2 * p)
      _ ≤ Kp ^ (2 * p - 1) * T1 := hpm
      _ ≤ Kp ^ (2 * p - 1) * (Qp ^ (2 * p - 2) * T2) := by
          apply mul_le_mul_of_nonneg_left hT; positivity
      _ = Kp ^ (2 * p - 1) * Qp ^ (2 * p - 2) * T2 := by ring
  have hQp2 : Qp ^ (2 * p) = Qp ^ 2 * Qp ^ (2 * p - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have step3 : (γ / 1000) ^ p * (Sp * Qp ^ 2) * (Kp ^ (2 * p - 1) * Qp ^ (2 * p - 2))
      ≤ T2 * (Kp ^ (2 * p - 1) * Qp ^ (2 * p - 2)) := by
    calc (γ / 1000) ^ p * (Sp * Qp ^ 2) * (Kp ^ (2 * p - 1) * Qp ^ (2 * p - 2))
        = (γ / 1000) ^ p * (Sp * Kp ^ (2 * p - 1)) * Qp ^ (2 * p) := by rw [hQp2]; ring
      _ ≤ (γ ^ p * (N : ℝ) ^ (2 * p)) * Qp ^ (2 * p) := by
          apply mul_le_mul_of_nonneg_right step1; positivity
      _ = γ ^ p * (N : ℝ) ^ (2 * p) * Qp ^ (2 * p) := by ring
      _ ≤ Kp ^ (2 * p - 1) * Qp ^ (2 * p - 2) * T2 := step2
      _ = T2 * (Kp ^ (2 * p - 1) * Qp ^ (2 * p - 2)) := by ring
  have step4 : (γ / 1000) ^ p * (Sp * Qp ^ 2) ≤ T2 := le_of_mul_le_mul_right step3 hCpos
  have hfinal : Sp⁻¹ * Qp⁻¹ ^ 2 * T2 = T2 / (Sp * Qp ^ 2) := by
    rw [div_eq_mul_inv, mul_inv, inv_pow]
    ring
  rw [hfinal, le_div_iff₀ (by positivity : 0 < Sp * Qp ^ 2)]
  exact step4

/-- The output `K` of `Work.Peluse.WindowControl.absSq_window_control` can be taken to be exactly
`2 ^ (m - 1)`: the proof there already computes with `p := 2 ^ (m - 1)` and derives
`(γ/1000)^p ≤ boxNormPow 1 (arithIcc (c m) M) (symIcc N) (fun x => ‖F m x‖^p)`; only the final
`∃ K` wrapper is in the way. So this is that same statement with the exponent made explicit.
`absSq_window_control.lean` (same file, `submission/Work/Peluse/WindowControl/`) is sorry-free;
copying its proof body and instantiating `K` with `2 ^ (m - 1)` proves this.  The file should live
in namespace `Work.Peluse.PET` (module `Submission.Work.Peluse.PET.absSq_window_control_pow`). -/
theorem absSq_window_control_pow {m : ℕ} (hm : 0 < m) :
    ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ γ / (1000 * (m + 1)) → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ / 1000) ^ (2 ^ (m - 1)) ≤ Work.Peluse.boxNormPow 1
        (fun _ : Fin 1 => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) M)
        (Work.Peluse.symIcc N)
        (fun x => ((‖F ⟨m, Nat.lt_succ_self m⟩ x‖ ^ (2 ^ (m - 1)) : ℝ) : ℂ)) := by
  intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hFbdd hFsupp hcy hγ'γ hfloor havg
  set p : ℕ := 2 ^ (m - 1) with hp_def
  set cm : ℤ := c ⟨m, Nat.lt_succ_self m⟩ with hcm_def
  set Fm : ℤ → ℂ := F ⟨m, Nat.lt_succ_self m⟩ with hFm_def
  set Q : Finset ℤ := Work.Peluse.arithIcc cm M with hQ_def
  set S : Finset ℤ := Work.Peluse.symIcc N with hS_def
  set K : Finset ℤ := Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) with hK_def
  have hp1 : 1 ≤ p := by rw [hp_def]; exact Nat.one_le_two_pow
  have hppos : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hp1
  have h2p1 : 1 ≤ 2 * p := by omega
  have hgf : (fun x : ℤ => (‖Fm x‖ : ℂ) ^ p) = (fun x : ℤ => ((‖Fm x‖ ^ p : ℝ) : ℂ)) := by
    funext x
    exact (Complex.ofReal_pow (‖Fm x‖) p).symm
  have hmain : Real.sqrt γ * (N : ℝ) * (Q.card : ℝ) ≤ ∑ x ∈ S, ∑ a ∈ Q, ‖Fm (x + a)‖ := by
    have h := Work.Peluse.WindowControl.sqrtGamma_le_windowSum hm hc0 hN hM F hγ hFbdd hFsupp hcy havg
    simpa [hQ_def, hS_def, hFm_def, hcm_def] using h
  have hbd : ∀ a ∈ Q, |a| ≤ (N : ℤ) := by
    intro a ha
    rw [hQ_def, Work.Peluse.arithIcc] at ha
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp ha
    rw [← hya, hcm_def]
    exact hcy y hy ⟨m, Nat.lt_succ_self m⟩
  have hgsupp : Work.Peluse.SupportIn (fun x : ℤ => ((‖Fm x‖ ^ p : ℝ) : ℂ)) N := by
    intro x hx
    have h0 : Fm x = 0 := by
      rw [hFm_def]
      exact hFsupp ⟨m, Nat.lt_succ_self m⟩ x hx
    show ((‖Fm x‖ ^ p : ℝ) : ℂ) = 0
    rw [h0, norm_zero, zero_pow hppos.ne', Complex.ofReal_zero]
  have hKsum : (∑ x ∈ K, ‖∑ a ∈ Q, ((‖Fm (x + a)‖ ^ p : ℝ) : ℂ)‖ ^ 2)
      = ∑ x ∈ K, (∑ a ∈ Q, ‖Fm (x + a)‖ ^ p) ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hinner : (∑ a ∈ Q, ((‖Fm (x + a)‖ ^ p : ℝ) : ℂ))
        = (((∑ a ∈ Q, ‖Fm (x + a)‖ ^ p : ℝ)) : ℂ) :=
      (Complex.ofReal_sum Q (fun a => ‖Fm (x + a)‖ ^ p)).symm
    rw [hinner]
    rw [Complex.norm_of_nonneg (Finset.sum_nonneg fun a _ => pow_nonneg (norm_nonneg _) p)]
  have hbox : Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q) S
        (fun x : ℤ => ((‖Fm x‖ ^ p : ℝ) : ℂ))
      = (S.card : ℝ)⁻¹ * ((Q.card : ℝ))⁻¹ ^ 2
        * ∑ x ∈ K, (∑ a ∈ Q, ‖Fm (x + a)‖ ^ p) ^ 2 := by
    have h := Work.Peluse.WindowControl.boxNormPow_one_window (N := N) Q S (fun x : ℤ => ((‖Fm x‖ ^ p : ℝ) : ℂ)) hbd hgsupp
    rw [h, hKsum, hK_def]
  have hper : ∀ x ∈ K, (∑ a ∈ Q, ‖Fm (x + a)‖) ^ (2 * p)
      ≤ (Q.card : ℝ) ^ (2 * p - 2) * (∑ a ∈ Q, ‖Fm (x + a)‖ ^ p) ^ 2 := by
    intro x _
    have hsum_nn : (0 : ℝ) ≤ ∑ a ∈ Q, ‖Fm (x + a)‖ :=
      Finset.sum_nonneg fun a _ => norm_nonneg _
    have hpow := pow_sum_le_card_mul_sum_pow (s := Q) (f := fun a => ‖Fm (x + a)‖)
      (fun a _ => norm_nonneg _) (p - 1)
    rw [Nat.sub_add_cancel hp1] at hpow
    have h2 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (∑ a ∈ Q, ‖Fm (x + a)‖) ^ p) hpow 2
    have hL : ((∑ a ∈ Q, ‖Fm (x + a)‖) ^ p) ^ 2 = (∑ a ∈ Q, ‖Fm (x + a)‖) ^ (2 * p) := by
      rw [← pow_mul (∑ a ∈ Q, ‖Fm (x + a)‖) p 2, Nat.mul_comm p 2]
    have hR : ((Q.card : ℝ) ^ (p - 1) * (∑ a ∈ Q, ‖Fm (x + a)‖ ^ p)) ^ 2
        = (Q.card : ℝ) ^ (2 * p - 2) * (∑ a ∈ Q, ‖Fm (x + a)‖ ^ p) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      have he : (Q.card : ℝ) ^ ((p - 1) * 2) = (Q.card : ℝ) ^ (2 * p - 2) := by
        congr 1
        omega
      rw [he]
    rw [hL, hR] at h2
    exact h2
  have hT1T2 : (∑ x ∈ K, (∑ a ∈ Q, ‖Fm (x + a)‖) ^ (2 * p))
      ≤ (Q.card : ℝ) ^ (2 * p - 2) * ∑ x ∈ K, (∑ a ∈ Q, ‖Fm (x + a)‖ ^ p) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hper
  have hpmK : (∑ x ∈ K, ∑ a ∈ Q, ‖Fm (x + a)‖) ^ (2 * p)
      ≤ (K.card : ℝ) ^ (2 * p - 1) * ∑ x ∈ K, (∑ a ∈ Q, ‖Fm (x + a)‖) ^ (2 * p) := by
    have h := pow_sum_le_card_mul_sum_pow (s := K) (f := fun x => ∑ a ∈ Q, ‖Fm (x + a)‖)
      (fun x _ => Finset.sum_nonneg fun a _ => norm_nonneg _) (2 * p - 1)
    rwa [Nat.sub_add_cancel h2p1] at h
  have hRK0 : Real.sqrt γ * (N : ℝ) * (Q.card : ℝ) ≤ ∑ x ∈ K, ∑ a ∈ Q, ‖Fm (x + a)‖ := by
    refine le_trans hmain ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      have hx' : -(N : ℤ) ≤ x ∧ x ≤ (N : ℤ) := by
        rw [hS_def, Work.Peluse.symIcc, Finset.mem_Icc] at hx
        exact hx
      rw [hK_def, Finset.mem_Icc]
      omega
    · intro x _ _
      exact Finset.sum_nonneg fun a _ => norm_nonneg _
  obtain ⟨Sp, hSp_def⟩ : ∃ Sp : ℝ, Sp = (S.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨Qp, hQp_def⟩ : ∃ Qp : ℝ, Qp = (Q.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨Kp, hKp_def⟩ : ∃ Kp : ℝ, Kp = (K.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨Rn, hRn_def⟩ : ∃ Rn : ℝ, Rn = ∑ x ∈ K, ∑ a ∈ Q, ‖Fm (x + a)‖ := ⟨_, rfl⟩
  obtain ⟨T1, hT1_def⟩ : ∃ T1 : ℝ, T1 = ∑ x ∈ K, (∑ a ∈ Q, ‖Fm (x + a)‖) ^ (2 * p) := ⟨_, rfl⟩
  obtain ⟨T2, hT2_def⟩ : ∃ T2 : ℝ, T2 = ∑ x ∈ K, (∑ a ∈ Q, ‖Fm (x + a)‖ ^ p) ^ 2 := ⟨_, rfl⟩
  have hSp_pos : 0 < Sp := by
    rw [hSp_def]
    exact_mod_cast Finset.card_pos.mpr ⟨0, by
      rw [hS_def, Work.Peluse.symIcc, Finset.mem_Icc]; omega⟩
  have hQp_pos : 0 < Qp := by
    rw [hQp_def]
    exact_mod_cast Finset.card_pos.mpr ⟨cm * 1, by
      rw [hQ_def, Work.Peluse.arithIcc]
      exact Finset.mem_image.mpr ⟨1, by rw [Finset.mem_Icc]; omega, by ring⟩⟩
  have hKp_pos : 0 < Kp := by
    rw [hKp_def]
    exact_mod_cast Finset.card_pos.mpr ⟨0, by
      rw [hK_def, Finset.mem_Icc]; omega⟩
  have hcard : Sp * Kp ^ (2 * p - 1) ≤ 1000 ^ p * (N : ℝ) ^ (2 * p) := by
    have hS' : Sp = 2 * (N : ℝ) + 1 := by
      rw [hSp_def, hS_def, card_symIcc]; push_cast; ring
    have hK' : Kp = 4 * (N : ℝ) + 1 := by
      rw [hKp_def, hK_def, card_window]; push_cast; ring
    rw [hS', hK']
    exact card_bound N p hN hp1
  have hRK' : Real.sqrt γ * (N : ℝ) * Qp ≤ Rn := by
    rw [hRn_def, hQp_def]; exact hRK0
  have hpmK' : Rn ^ (2 * p) ≤ Kp ^ (2 * p - 1) * T1 := by
    rw [hRn_def, hKp_def, hT1_def]; exact hpmK
  have hT1T2' : T1 ≤ Qp ^ (2 * p - 2) * T2 := by
    rw [hT1_def, hQp_def, hT2_def]; exact hT1T2
  have hAns := final_assembly hp1 hN hγ hSp_pos hQp_pos hKp_pos hcard hRK' hpmK' hT1T2'
  rw [hbox, ← hSp_def, ← hQp_def, ← hT2_def]
  exact hAns

end Work.Peluse.PET
