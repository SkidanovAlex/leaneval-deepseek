/-
# Peluse's Lemma 4.10 in the paper's gauge (the `pelGauge` target)

Target: `Work.Peluse.PET.boxNormPow_control_linear_v2_pelGauge`.

The proof is an assembly of three régimes (see `pelGauge_main` below):

* régime (A) `γ' ≤ γ^Kp/Cp`: Peluse's Lemma 4.10 in the paper's gauge, applied directly
  (`PetLinear.linear_boxnorm_control_paper`, the PET induction of the `PetLinear` chapter);
* régime (B) `γ' > γ^Kp/Cp` and `2 Cp ≤ γ^Kp M`: the same paper's gauge applied at the *fine* scale
  `⌊γ^Kp M/Cp⌋`, followed by the transfer-up `TransferUp.boxNormPow_transfer_up`;
* régime (C) `γ' > γ^Kp/Cp` and `γ^Kp M < 2 Cp`: the diagonal route
  `PET.boxNormPow_control_linear_v2_diag` (with `PET.diagHyp_of_gapHyp`).

The degenerate case (some `c i = c_m`) and the case `m = 1` are handled by
`Track.boxNormPow_control_linear_v2_of_degenerate_direction` and
`PET.boxNormPow_control_linear_v2_one`.
-/
import Mathlib
import Submission.Work.Peluse.PET.boxNormPow_control_linear_v2_one
import Submission.Work.Peluse.PET.boxNormPow_control_linear_v2_diag
import Submission.Work.Peluse.PET.diagHyp_of_gapHyp
import Submission.Work.Peluse.PET.paperGaugeBound
import Submission.Work.Peluse.TransferUp.boxNormPow_transfer_up

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.PET

noncomputable section

/-! ## The direction family of the target -/

/-- The direction family `(c_m - c_i)[H]`, `i : Fin m`. -/
private abbrev pelDirFam {m : ℕ} (c : Fin (m + 1) → ℤ) (H : ℕ) : Fin m → Finset ℤ :=
  fun i => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc) H

/-! ## Elementary arithmetic -/

/-- For every real `A` there is `q` with `A ≤ 1000^q`. -/
private lemma exists_pow1000_ge (A : ℝ) : ∃ q : ℕ, A ≤ (1000 : ℝ) ^ q := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (max A 0) (show (1 : ℝ) < 1000 by norm_num)
  exact ⟨q, le_trans (le_max_left _ _) hq.le⟩

/-- **Régime (A) arithmetic.**  `(γ/1000)^K ≤ (γ/C)^Kp` if `Kp ≤ K` and `C^Kp ≤ 1000^K`. -/
private lemma regimeA_pow_aux {C γ : ℝ} {Kp K : ℕ} (hC : 0 < C) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hK : Kp ≤ K) (h1000 : C ^ Kp ≤ (1000 : ℝ) ^ K) :
    (γ / 1000) ^ K ≤ (γ / C) ^ Kp := by
  have h1 : (0 : ℝ) < (1000 : ℝ) ^ K := pow_pos (by norm_num) _
  have h2 : (0 : ℝ) < C ^ Kp := pow_pos hC _
  rw [div_pow, div_pow, div_le_div_iff₀ h1 h2]
  have h3 : γ ^ K ≤ γ ^ Kp := pow_le_pow_of_le_one hγ.le hγ1 hK
  have h4 : γ ^ K * C ^ Kp ≤ γ ^ Kp * C ^ Kp := mul_le_mul_of_nonneg_right h3 h2.le
  have h5 : γ ^ Kp * C ^ Kp ≤ γ ^ Kp * (1000 : ℝ) ^ K :=
    mul_le_mul_of_nonneg_left h1000 (pow_nonneg hγ.le _)
  linarith

/-- **Régime (B) arithmetic.**  Trading the scale ratio against the power of `(γ/1000)⁻¹`. -/
private lemma regimeB_pow_aux {m : ℕ} {Cp cT γ : ℝ} {eT Kp K : ℕ}
    (hCp : 0 < Cp) (hcT : 0 < cT) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hK : Kp + (Kp - 2 ^ m) * eT ≤ K)
    (hconst : 2 ^ eT * Cp ^ (eT + Kp) ≤ cT * (1000 : ℝ) ^ (2 ^ m * eT) * (1000 : ℝ) ^ K) :
    (γ / 1000) ^ K
      ≤ cT * (γ ^ (Kp - 2 ^ m) * (1000 : ℝ) ^ (2 ^ m) / (2 * Cp)) ^ eT
          * (γ / Cp) ^ Kp := by
  have hexp : (Kp - 2 ^ m) * eT + Kp ≤ K := by omega
  have hkey : cT * (γ ^ (Kp - 2 ^ m) * (1000 : ℝ) ^ (2 ^ m) / (2 * Cp)) ^ eT
        * (γ / Cp) ^ Kp
      = γ ^ ((Kp - 2 ^ m) * eT + Kp) * (cT * (1000 : ℝ) ^ (2 ^ m * eT))
          / (2 ^ eT * Cp ^ (eT + Kp)) := by
    ring_nf
    simp only [one_div]
  rw [hkey, div_pow]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hγpow : γ ^ K ≤ γ ^ ((Kp - 2 ^ m) * eT + Kp) :=
    pow_le_pow_of_le_one hγ.le hγ1 hexp
  calc γ ^ K * (2 ^ eT * Cp ^ (eT + Kp))
      ≤ γ ^ K * (cT * (1000 : ℝ) ^ (2 ^ m * eT) * (1000 : ℝ) ^ K) :=
        mul_le_mul_of_nonneg_left hconst (pow_nonneg hγ.le _)
    _ ≤ γ ^ ((Kp - 2 ^ m) * eT + Kp)
          * (cT * (1000 : ℝ) ^ (2 ^ m * eT) * (1000 : ℝ) ^ K) :=
        mul_le_mul_of_nonneg_right hγpow (by positivity)
    _ = γ ^ ((Kp - 2 ^ m) * eT + Kp) * (cT * (1000 : ℝ) ^ (2 ^ m * eT))
          * (1000 : ℝ) ^ K := by ring

/-- **Régime (B) scale ratio.** -/
private lemma ratio_bound_aux {m Kp : ℕ} {γ γ' Cp : ℝ} {M H H'' : ℕ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ' : 0 < γ') (hCp : 0 < Cp)
    (hgaug : γ' ≤ (γ / 1000) ^ (2 ^ m))
    (hbig : 2 ≤ γ ^ Kp * (M : ℝ) / Cp)
    (hH1 : 1 ≤ H) (hH''1 : 1 ≤ H'')
    (hH''lb : γ ^ Kp / Cp * (M : ℝ) - 1 ≤ (H'' : ℝ))
    (hHub : (H : ℝ) ≤ γ' * (M : ℝ)) :
    γ ^ (Kp - 2 ^ m) * (1000 : ℝ) ^ (2 ^ m) / (2 * Cp) ≤ (H'' : ℝ) / (H : ℝ) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have h0 : γ ^ Kp * (M : ℝ) / Cp ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hγ.le _) hcon)
        hCp.le
    linarith
  have hγKp : (0 : ℝ) < γ ^ Kp := pow_pos hγ _
  have ht : 2 ≤ γ ^ Kp / Cp * (M : ℝ) := by rw [div_mul_eq_mul_div]; exact hbig
  have hH''ge : γ ^ Kp / Cp * (M : ℝ) / 2 ≤ (H'' : ℝ) := by linarith
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
  have h1 : γ ^ Kp / Cp * (M : ℝ) / 2 / (γ' * (M : ℝ)) ≤ (H'' : ℝ) / (H : ℝ) :=
    div_le_div₀ (by positivity) hH''ge hHpos hHub
  have h2 : γ ^ Kp / Cp * (M : ℝ) / 2 / (γ' * (M : ℝ)) = γ ^ Kp / (2 * Cp * γ') := by
    field_simp
  rw [h2] at h1
  -- the truncated power and the gauge bound on `1/γ'`
  have htrunc : γ ^ (Kp - 2 ^ m) ≤ γ ^ Kp / γ ^ (2 ^ m) := by
    rcases le_total (2 ^ m) Kp with h | h
    · rw [pow_sub₀ γ hγ.ne' h, div_eq_mul_inv]
    · rw [Nat.sub_eq_zero_of_le h, pow_zero, one_le_div (pow_pos hγ _)]
      exact pow_le_pow_of_le_one hγ.le hγ1 h
  have hinv : (1000 : ℝ) ^ (2 ^ m) / γ ^ (2 ^ m) ≤ 1 / γ' := by
    rw [div_le_div_iff₀ (by positivity) hγ']
    have hg : γ' * (1000 : ℝ) ^ (2 ^ m) ≤ γ ^ (2 ^ m) := by
      have := hgaug
      rw [div_pow] at this
      calc γ' * (1000 : ℝ) ^ (2 ^ m) ≤ (γ ^ (2 ^ m) / (1000 : ℝ) ^ (2 ^ m)) * (1000 : ℝ) ^ (2 ^ m) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = γ ^ (2 ^ m) := by field_simp
    linarith
  have hnum : γ ^ (Kp - 2 ^ m) * (1000 : ℝ) ^ (2 ^ m) ≤ γ ^ Kp / γ' := by
    calc γ ^ (Kp - 2 ^ m) * (1000 : ℝ) ^ (2 ^ m)
        ≤ (γ ^ Kp / γ ^ (2 ^ m)) * (1000 : ℝ) ^ (2 ^ m) :=
          mul_le_mul_of_nonneg_right htrunc (by positivity)
      _ = γ ^ Kp * ((1000 : ℝ) ^ (2 ^ m) / γ ^ (2 ^ m)) := by ring
      _ ≤ γ ^ Kp * (1 / γ') := mul_le_mul_of_nonneg_left hinv hγKp.le
      _ = γ ^ Kp / γ' := by ring
  have hstepB : γ ^ (Kp - 2 ^ m) * (1000 : ℝ) ^ (2 ^ m) / (2 * Cp) ≤ γ ^ Kp / (2 * Cp * γ') := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h := hnum
    rw [le_div_iff₀ hγ'] at h
    nlinarith [h, hCp, hγ']
  linarith [h1, hstepB]

/-! ## The two ingredients of the assembly -/

/-- Peluse's Lemma 4.10 in the paper's gauge (`PetLinear.linear_boxnorm_control_paper`),
phrased with the direction family of the target. -/
private def PelPaper (m : ℕ) : Prop :=
  ∃ Kp : ℕ, ∃ Cp : ℝ, 1 ≤ Kp ∧ 0 < Cp ∧
    ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ γ ^ Kp / Cp → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ / Cp) ^ Kp ≤ Work.Peluse.boxNormPow m (pelDirFam c (⌊γ' * (M : ℝ)⌋).toNat)
        (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩)

/-- The transfer-up of the box norm (`TransferUp.boxNormPow_transfer_up`). -/
private def PelTransferUp (m : ℕ) : Prop :=
  ∃ cT : ℝ, ∃ eT : ℕ, 0 < cT ∧
    ∀ (N : ℕ) (F : ℤ → ℂ), (∀ x : ℤ, ‖F x‖ ≤ 1) → Work.Peluse.SupportIn F N →
      ∀ (d : Fin m → ℤ), (∀ i, d i ≠ 0) → ∀ (H' H : ℕ), 1 ≤ H' → H' ≤ H →
        (∀ i, |d i| * (H : ℤ) ≤ 2 * (N : ℤ)) →
        cT * ((H' : ℝ) / (H : ℝ)) ^ eT *
            Work.Peluse.boxNormPow m (fun i : Fin m => Work.Peluse.arithIcc (d i) H')
              (Work.Peluse.symIcc N) F
          ≤ Work.Peluse.boxNormPow m (fun i : Fin m => Work.Peluse.arithIcc (d i) H)
              (Work.Peluse.symIcc N) F


/-- The `pelGauge` hypothesis implies the linear (`v2`) gauge hypothesis. -/
private lemma v2_gauge_aux {m : ℕ} {γ γ' : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (h : γ' ≤ (γ / 1000) ^ (2 ^ m)) : γ' ≤ γ / (1000 * ((m + 1 : ℕ) : ℝ)) := by
  refine le_trans h ?_
  have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hm : m ≤ 2 ^ m - 1 := by
    have h' := Nat.lt_two_pow_self (n := m)
    omega
  have h1000m : ((m : ℝ) + 1) ≤ (1000 : ℝ) ^ m := by
    have h1 : m + 1 ≤ 1000 ^ m := by
      have h2 : m + 1 ≤ 2 ^ m := by
        have h' := Nat.lt_two_pow_self (n := m)
        omega
      have h3 : 2 ^ m ≤ 1000 ^ m := Nat.pow_le_pow_left (by norm_num) m
      omega
    have h4 : ((m + 1 : ℕ) : ℝ) ≤ ((1000 ^ m : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h4 ⊢
    linarith
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : γ ^ (2 ^ m) = γ * γ ^ (2 ^ m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel h2m]
  have e2 : (1000 : ℝ) ^ (2 ^ m) = 1000 * (1000 : ℝ) ^ (2 ^ m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel h2m]
  rw [e1, e2]
  push_cast
  have hγle : γ ^ (2 ^ m - 1) ≤ 1 := pow_le_one₀ hγ.le hγ1
  have hmle : ((m : ℝ) + 1) ≤ (1000 : ℝ) ^ (2 ^ m - 1) := by
    calc ((m : ℝ) + 1) ≤ (1000 : ℝ) ^ m := h1000m
      _ ≤ (1000 : ℝ) ^ (2 ^ m - 1) := pow_le_pow_right₀ (by norm_num) hm
  have hkey : γ ^ (2 ^ m - 1) * ((m : ℝ) + 1) ≤ (1000 : ℝ) ^ (2 ^ m - 1) := by
    have h1 : γ ^ (2 ^ m - 1) * ((m : ℝ) + 1) ≤ 1 * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hγle (by positivity)
    linarith [h1, hmle]
  have hgoal2 : γ * 1000 * (γ ^ (2 ^ m - 1) * ((m : ℝ) + 1))
      ≤ γ * 1000 * (1000 : ℝ) ^ (2 ^ m - 1) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  linarith [hgoal2]

/-- **The assembly.**  The `pelGauge` target for `2 ≤ m`, conditional on Peluse's Lemma 4.10 in
the paper's gauge and on the transfer-up of the box norm. -/
private theorem pelGauge_main {m : ℕ} (hm : 2 ≤ m) (hpaper : PelPaper m)
    (htransfer : PelTransferUp m) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 →
      ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ},
      0 < γ → 0 < γ' → γ ≤ 1 → (∀ i x, ‖F i x‖ ≤ 1) →
      (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ (γ / 1000) ^ (2 ^ m) → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ / 1000) ^ K ≤ Work.Peluse.boxNormPow m (pelDirFam c (⌊γ' * (M : ℝ)⌋).toNat)
        (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩) := by
  classical
  obtain ⟨Kp, Cp, hKp1, hCp, hpaperBody⟩ := hpaper
  obtain ⟨cT, eT, hcT, htransferBody⟩ := htransfer
  obtain ⟨Kdeg, hKdeg1, hdegBody⟩ :=
    Work.Peluse.Track.boxNormPow_control_linear_v2_of_degenerate_direction (m := m) (by omega)
  obtain ⟨q1, hq1⟩ : ∃ q : ℕ, Cp ^ Kp ≤ (1000 : ℝ) ^ q := exists_pow1000_ge _
  obtain ⟨q2, hq2⟩ : ∃ q : ℕ,
      2 ^ eT * Cp ^ (eT + Kp) / (cT * (1000 : ℝ) ^ (2 ^ m * eT)) ≤ (1000 : ℝ) ^ q :=
    exists_pow1000_ge _
  obtain ⟨q3, hq3⟩ : ∃ q : ℕ,
      4 * (2 * Cp) ^ m / (1000 * ((m : ℝ) + 1)) ^ m ≤ (1000 : ℝ) ^ q := exists_pow1000_ge _
  set P : ℕ := 2 ^ (m - 1) with hPdef
  set P2 : ℕ := 2 ^ m with hP2def
  have hPle : P ≤ P2 := by
    rw [hPdef, hP2def]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  set K : ℕ := q1 + q2 + q3 + Kdeg + 1 + P2 + (Kp + Kp * eT) + (m * Kp + q3 + P2) + P with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    linarith [Nat.zero_le q1, Nat.zero_le q2, Nat.zero_le q3, Nat.zero_le Kdeg,
      Nat.zero_le P2, Nat.zero_le (Kp + Kp * eT), Nat.zero_le (m * Kp + q3 + P2),
      Nat.zero_le P]
  have hq1K : q1 ≤ K := by
    rw [hKdef]
    linarith [Nat.zero_le q2, Nat.zero_le q3, Nat.zero_le Kdeg,
      Nat.zero_le P2, Nat.zero_le (Kp + Kp * eT), Nat.zero_le (m * Kp + q3 + P2),
      Nat.zero_le P]
  have hq2K : q2 ≤ K := by
    rw [hKdef]
    linarith [Nat.zero_le q1, Nat.zero_le q3, Nat.zero_le Kdeg,
      Nat.zero_le P2, Nat.zero_le (Kp + Kp * eT), Nat.zero_le (m * Kp + q3 + P2),
      Nat.zero_le P]
  have hq3K : q3 ≤ K := by
    rw [hKdef]
    linarith [Nat.zero_le q1, Nat.zero_le q2, Nat.zero_le Kdeg,
      Nat.zero_le P2, Nat.zero_le (Kp + Kp * eT), Nat.zero_le (m * Kp + q3 + P2),
      Nat.zero_le P]
  have hKdegK : Kdeg ≤ K := by
    rw [hKdef]
    linarith [Nat.zero_le q1, Nat.zero_le q2, Nat.zero_le q3,
      Nat.zero_le P2, Nat.zero_le (Kp + Kp * eT), Nat.zero_le (m * Kp + q3 + P2),
      Nat.zero_le P]
  have hKpK : Kp ≤ K := by
    rw [hKdef]
    linarith [Nat.zero_le q1, Nat.zero_le q2, Nat.zero_le q3, Nat.zero_le Kdeg,
      Nat.zero_le P2, Nat.zero_le (Kp * eT), Nat.zero_le (m * Kp + q3 + P2),
      Nat.zero_le P]
  have hKexp : Kp + (Kp - 2 ^ m) * eT ≤ K := by
    have h1 : (Kp - 2 ^ m) * eT ≤ Kp * eT := Nat.mul_le_mul_right eT (Nat.sub_le Kp (2 ^ m))
    rw [hKdef]
    linarith [h1, Nat.zero_le q1, Nat.zero_le q2, Nat.zero_le q3, Nat.zero_le Kdeg,
      Nat.zero_le P2, Nat.zero_le (m * Kp + q3 + P2), Nat.zero_le P]
  have hKl : 2 ^ (m - 1) + m * (Kp - 1) ≤ K := by
    have h2 : m * (Kp - 1) ≤ m * Kp := Nat.mul_le_mul_left m (Nat.sub_le Kp 1)
    rw [← hPdef, hKdef]
    linarith [hPle, h2, Nat.zero_le q1, Nat.zero_le q2, Nat.zero_le q3,
      Nat.zero_le Kdeg, Nat.zero_le (Kp + Kp * eT), Nat.zero_le q3, Nat.zero_le P2,
      Nat.zero_le P]
  have hq3le : q3 ≤ K - 2 ^ (m - 1) := by
    rw [← hPdef]
    apply Nat.le_sub_of_add_le
    rw [hKdef]
    linarith [hPle, Nat.zero_le q1, Nat.zero_le q2, Nat.zero_le q3,
      Nat.zero_le Kdeg, Nat.zero_le (Kp + Kp * eT), Nat.zero_le (m * Kp),
      Nat.zero_le P2, Nat.zero_le P]
  have hK2 : 2 ^ (m - 1) ≤ K := by
    rw [← hPdef, hKdef]
    linarith [Nat.zero_le q1, Nat.zero_le q2, Nat.zero_le q3, Nat.zero_le Kdeg,
      Nat.zero_le P2, Nat.zero_le (Kp + Kp * eT), Nat.zero_le (m * Kp + q3 + P2)]
  have h1000K : (1000 : ℝ) ^ q1 ≤ (1000 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hq1K
  have h1000K2 : (1000 : ℝ) ^ q2 ≤ (1000 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hq2K
  have hC1000 : Cp ^ Kp ≤ (1000 : ℝ) ^ K := le_trans hq1 h1000K
  have hconst : 2 ^ eT * Cp ^ (eT + Kp) ≤ cT * (1000 : ℝ) ^ (2 ^ m * eT) * (1000 : ℝ) ^ K := by
    have hden : (0 : ℝ) < cT * (1000 : ℝ) ^ (2 ^ m * eT) := by positivity
    have h2 := le_trans hq2 h1000K2
    rw [div_le_iff₀ hden] at h2
    calc 2 ^ eT * Cp ^ (eT + Kp)
        ≤ cT * (1000 : ℝ) ^ (2 ^ m * eT) * (1000 : ℝ) ^ K := by linarith [h2]
      _ = cT * (1000 : ℝ) ^ (2 ^ m * eT) * (1000 : ℝ) ^ K := rfl
  have hKc : 4 * (2 * Cp) ^ m / (1000 * ((m : ℝ) + 1)) ^ m ≤ (1000 : ℝ) ^ (K - 2 ^ (m - 1)) :=
    le_trans hq3 (pow_le_pow_right₀ (by norm_num) hq3le)
  refine ⟨K, hK1, ?_⟩
  intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hgauge hHge hLam
  set H : ℕ := ⌊γ' * (M : ℝ)⌋.toNat with hHdef
  have hH1 : 1 ≤ H := hHge
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hHle : (H : ℝ) ≤ γ' * (M : ℝ) := by
    rw [hHdef, Int.floor_toNat]
    exact Nat.floor_le (le_of_lt (mul_pos hγ' hMpos))
  have hγ'1 : γ' ≤ 1 := by
    refine le_trans hgauge ?_
    exact pow_le_one₀ (by positivity) (by linarith)
  have hHM : H ≤ M := by
    have h2 : (H : ℝ) ≤ (M : ℝ) := by
      calc (H : ℝ) ≤ γ' * (M : ℝ) := hHle
        _ ≤ 1 * (M : ℝ) := mul_le_mul_of_nonneg_right hγ'1 hMpos.le
        _ = (M : ℝ) := one_mul _
    exact_mod_cast h2
  have hv2 : γ' ≤ γ / (1000 * ((m + 1 : ℕ) : ℝ)) := v2_gauge_aux hγ hγ1 hgauge
  have hv2' : γ' ≤ γ / (1000 * ((m : ℝ) + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hv2
  have hdirbd : ∀ i : Fin m, |c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc| * (H : ℤ) ≤ 2 * (N : ℤ) := by
    intro i
    have hHmem : H ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hH1, hHM⟩
    have h1 : |c ⟨m, Nat.lt_succ_self m⟩ * (H : ℤ)| ≤ (N : ℤ) := hcy H hHmem _
    have h2 : |c i.castSucc * (H : ℤ)| ≤ (N : ℤ) := hcy H hHmem _
    have hHnn : (0 : ℤ) ≤ (H : ℤ) := by positivity
    have h3 : |c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc| * (H : ℤ)
        = |(c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc) * (H : ℤ)| := by
      rw [abs_mul, abs_of_nonneg hHnn]
    rw [h3, sub_mul]
    calc |c ⟨m, Nat.lt_succ_self m⟩ * (H : ℤ) - c i.castSucc * (H : ℤ)|
        ≤ |c ⟨m, Nat.lt_succ_self m⟩ * (H : ℤ)| + |c i.castSucc * (H : ℤ)| := abs_sub _ _
      _ ≤ (N : ℤ) + (N : ℤ) := add_le_add h1 h2
      _ = 2 * (N : ℤ) := by ring
  by_cases hdeg : ∃ i₀ : Fin m, c i₀.castSucc = c ⟨m, Nat.lt_succ_self m⟩
  · have hres := hdegBody c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy hv2' hHge hLam hdeg
    exact le_trans (pow_le_pow_of_le_one (by positivity) (by linarith) hKdegK) hres
  · have hdirne : ∀ i : Fin m, c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc ≠ 0 := by
      intro i hi
      apply hdeg
      refine ⟨i, ?_⟩
      have h2 : c ⟨m, Nat.lt_succ_self m⟩ = c i.castSucc := by omega
      exact h2.symm
    by_cases hA : γ' ≤ γ ^ Kp / Cp
    · refine le_trans (regimeA_pow_aux hCp hγ hγ1 hKpK hC1000) ?_
      exact hpaperBody c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy hA hHge hLam
    · have hAgt : γ ^ Kp / Cp < γ' := lt_of_not_ge hA
      by_cases hB : 2 * Cp ≤ γ ^ Kp * (M : ℝ)
      · set γ'' : ℝ := γ ^ Kp / Cp with hγ''def
        set H'' : ℕ := ⌊γ'' * (M : ℝ)⌋.toNat with hH''def
        have hγ''pos : 0 < γ'' := by rw [hγ''def]; positivity
        have hH''1 : 1 ≤ H'' := by
          rw [hH''def, Int.le_toNat (Int.floor_nonneg.mpr (by positivity)), Int.le_floor]
          push_cast
          have ht : γ'' * (M : ℝ) = γ ^ Kp * (M : ℝ) / Cp := by rw [hγ''def]; ring
          rw [ht, le_div_iff₀ hCp]
          linarith
        have hH''le : H'' ≤ H := by
          rw [hH''def, hHdef]
          apply Int.toNat_le_toNat
          apply Int.floor_le_floor
          exact mul_le_mul_of_nonneg_right hAgt.le hMpos.le
        have hbig : 2 ≤ γ ^ Kp * (M : ℝ) / Cp := by
          rw [le_div_iff₀ hCp]; linarith
        have hH''lb : γ'' * (M : ℝ) - 1 ≤ (H'' : ℝ) := by
          have hcast : ((H'' : ℕ) : ℝ) = ((⌊γ'' * (M : ℝ)⌋ : ℤ) : ℝ) := by
            rw [hH''def]
            exact_mod_cast (Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity)))
          have hlt : γ'' * (M : ℝ) - 1 < ((⌊γ'' * (M : ℝ)⌋ : ℤ) : ℝ) := by
            have h := Int.lt_floor_add_one (γ'' * (M : ℝ))
            linarith
          rw [hcast]
          linarith
        have hratio := ratio_bound_aux hγ hγ1 hγ' hCp hgauge hbig hH1 hH''1 hH''lb hHle
        have hfine := hpaperBody c hc0 hN hM F hγ hγ''pos hγ1 hF hFs hcy (le_refl _) hH''1 hLam
        have hTU := htransferBody N (F ⟨m, Nat.lt_succ_self m⟩) (hF _) (hFs _)
          (fun i => c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc) hdirne
          H'' H hH''1 hH''le hdirbd
        refine le_trans (regimeB_pow_aux hCp hcT hγ hγ1 hKexp hconst) ?_
        calc cT * (γ ^ (Kp - 2 ^ m) * (1000 : ℝ) ^ (2 ^ m) / (2 * Cp)) ^ eT * (γ / Cp) ^ Kp
            ≤ cT * ((H'' : ℝ) / (H : ℝ)) ^ eT * (γ / Cp) ^ Kp := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              refine mul_le_mul_of_nonneg_left ?_ hcT.le
              exact pow_le_pow_left₀ (by positivity) hratio eT
          _ ≤ cT * ((H'' : ℝ) / (H : ℝ)) ^ eT *
                Work.Peluse.boxNormPow m (pelDirFam c H'') (Work.Peluse.symIcc N)
                  (F ⟨m, Nat.lt_succ_self m⟩) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact hfine
          _ ≤ Work.Peluse.boxNormPow m (pelDirFam c H) (Work.Peluse.symIcc N)
                (F ⟨m, Nat.lt_succ_self m⟩) := hTU
      · have hC2 : γ ^ Kp * (M : ℝ) < 2 * Cp := lt_of_not_ge hB
        have hdiag : (γ * (M : ℝ) / (1000 * ((m : ℝ) + 1))) ^ m
            ≤ (1 / 4) * (1000 / γ) ^ (K - 2 ^ (m - 1)) :=
          diagHyp_of_gapHyp hm hKp1 hCp hγ hγ1 hMpos hC2 hKl hKc
        have hdiagbox := boxNormPow_control_linear_v2_diag (m := m) hm (K - 2 ^ (m - 1))
          c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy hv2' hHge hLam hdiag
        have hpow : 2 ^ (m - 1) + (K - 2 ^ (m - 1)) = K := Nat.add_sub_cancel' hK2
        rw [hpow] at hdiagbox
        exact hdiagbox

/-- **Peluse's Lemma 4.10 in the paper's gauge, `pelGauge` form** (the frozen target).

* `m = 1`: `PET.boxNormPow_control_linear_v2_one`;
* `m ≥ 2`: the three-régime assembly `pelGauge_main`, whose two ingredients are Peluse's Lemma 4.10
  in the paper's gauge (`PelPaper`, available in the workspace as
  `PetLinear.linear_boxnorm_control_paper`) and the transfer-up of the box norm (`PelTransferUp`,
  available as `TransferUp.boxNormPow_transfer_up`). -/
theorem boxNormPow_control_linear_v2_pelGauge {m : ℕ} (hm : 0 < m) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ (γ / 1000) ^ (2 ^ m) → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ / 1000) ^ K ≤ Work.Peluse.boxNormPow m
        (fun i : Fin m => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc)
          (⌊γ' * (M : ℝ)⌋).toNat) (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩) := by
  by_cases hm1 : m = 1
  · subst hm1
    obtain ⟨K1, hK11, hone⟩ := boxNormPow_control_linear_v2_one
    refine ⟨K1, hK11, ?_⟩
    intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hgauge hHge hLam
    refine hone c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy ?_ hHge hLam
    have h2 : (γ / 1000) ^ (2 ^ (1 : ℕ)) ≤ γ / (1000 * (1 + 1)) := by
      norm_num
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hγ.le, hγ1]
    exact le_trans hgauge h2
  · have hm2 : 2 ≤ m := by omega
    refine pelGauge_main hm2 ?_ ?_
    · -- Peluse's Lemma 4.10 in the paper's gauge (this is `PetLinear.linear_boxnorm_control_paper`
      -- in the shape of the direction family `pelDirFam` of the target).
      obtain ⟨Kp, Cp, hKp1, hCp, hbody⟩ := paperGaugeBound (m := m) (by omega)
      refine ⟨Kp, Cp, hKp1, hCp, ?_⟩
      intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hg hH hLam
      simpa only [pelDirFam] using
        hbody c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy hg hH hLam
    · -- The transfer-up of the box norm.
      obtain ⟨cT, hcT, eT, hTU⟩ :=
        Work.Peluse.TransferUp.boxNormPow_transfer_up (k := m) hm2
      exact ⟨cT, eT, hcT, hTU⟩

end

end Work.Peluse.PET
