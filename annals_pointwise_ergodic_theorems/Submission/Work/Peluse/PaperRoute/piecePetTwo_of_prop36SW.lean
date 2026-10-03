import Mathlib
import Submission.Work.Peluse.Holds.Corrected
import Submission.Work.Peluse.UControl.bandStructureAprime
import Submission.Work.Peluse.PaperRoute.PiecePetTwo

/-!
# `PiecePetTwo P` from the corrected Proposition 3.6 `Prop36SW`

This is the **level-`≥ 2`** form of `Work.Peluse.piecePet_of_prop36SW`: the *same* consumer argument
against the corrected §5 chapter `Work.Peluse.C46.Prop36SW P`, with the conclusion recorded as
`Work.Peluse.UControl.PiecePetTwo P` instead of `Work.Peluse.UControl.PiecePet P`.

The change is possible because `Prop36SW` already delivers its level as `∃ s, 2 ≤ s` (`Corrected.lean`
line "`def Prop36SW`"), so nothing in the proof has to be re-derived: `PiecePetTwo` is `PiecePet`'s
body with the level bound `1 ≤ s₀` replaced by `2 ≤ s₀`.  The reason the stronger form is the one
the route needs is in `PaperRoute/PiecePetTwo.lean`: the paper-route consumer
`Work.Peluse.PaperRoute.ucontrolPaper_of_piecePet` needs a level `s ≥ 2` (the level is shared between
the `U`-control and the degree-lowering chapter `PeluseULowering`, which is `∀ s, 2 ≤ s → …`), and the
Gowers norms *decrease* in the level, so the level-`1` record is strictly weaker and cannot be raised
(`uNormPow_level_raise_win 1 2` runs the other way and loses a power of the norm).

So this file closes the last link of the route
`AreaA2 ← … ← PiecePetTwo ← Prop36SW ← PeluseLadderA ← PeluseConcatFixed ←
ExpansionPETShortA ∧ ConcatBridgeShortA`: with it, the single chapter hypothesis of
`Work.Peluse.PaperRoute.area_a2_of_piecePet` is produced by

  `fun P hd => Work.Peluse.PaperRoute.piecePetTwo_of_prop36SW P hd (prop36SW P)`

(`prop36SW` being the §5 lane's O2 output).

The proof is the file `Submission/Work/Peluse/piecePet_of_prop36SW.lean` verbatim below the
`Prop36SW` extraction; only the goal's level bound differs (and `by omega` discharges it from the
`2 ≤ s` extracted from `Prop36SW`).  The file is *not* an edit of that file: it is a copy, so the
§5 lane keeps its own `piecePet_of_prop36SW : … → PiecePet P` untouched.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators
open Polynomial

namespace Work.Peluse.PaperRoute

noncomputable section

open Work.Peluse.UControl

theorem piecePetTwo_of_prop36SW (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (h : Work.Peluse.C46.Prop36SW P) : Work.Peluse.UControl.PiecePetTwo P := by
  obtain ⟨D, K₃₄, hK₃₄, h34'⟩ := prop34Holds P
  obtain ⟨s, hs2, h36'⟩ := h D
  refine ⟨s, by omega, ?_⟩
  intro A' hA'
  have hA'pos : (0 : ℝ) < A' := lt_of_lt_of_le one_pos hA'
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : ℝ, A₀ = 1 + 2 * A' := ⟨_, rfl⟩
  have hA₀1 : 1 ≤ A₀ := by rw [hA₀def]; linarith
  obtain ⟨A₃₄, hA₃₄, h34''⟩ := h34' A₀ hA₀1
  obtain ⟨A₃₆, hA₃₆, K₃₆, hK₃₆, h36''⟩ := h36' A₀ hA₀1
  have hA₃₄pos : (0 : ℝ) < A₃₄ := lt_of_lt_of_le one_pos hA₃₄
  have hA₃₆pos : (0 : ℝ) < A₃₆ := lt_of_lt_of_le one_pos hA₃₆
  obtain ⟨Csh, hCshpos, hCsh⟩ := uNormPow_shrink_ambient hs2
  obtain ⟨Dη, hDηdef⟩ : ∃ Dη : ℝ, Dη = ((A' + 2) * A₃₄) ^ K₃₄ := ⟨_, rfl⟩
  have hDηpos : 0 < Dη := by rw [hDηdef]; positivity
  obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = Dη ^ K₃₆ * A₃₆ := ⟨_, rfl⟩
  have hM₀pos : 0 < M₀ := by rw [hM₀def]; positivity
  obtain ⟨Cp, hCpdef⟩ : ∃ Cp : ℝ, Cp = 1 + 2 * M₀ + (2 * M₀) ^ P.natDegree +
      A₃₆ ^ (K₃₆ + 1) * Dη ^ (K₃₆ * (K₃₆ + 1)) + M₀ / Csh +
      2 * (Dη ^ (K₃₆ * (P.natDegree + 1)) * A₃₆ ^ (P.natDegree + 1)) := ⟨_, rfl⟩
  have hCpterm1 : (0 : ℝ) ≤ (2 * M₀) ^ P.natDegree := by positivity
  have hCpterm2 : (0 : ℝ) ≤ A₃₆ ^ (K₃₆ + 1) * Dη ^ (K₃₆ * (K₃₆ + 1)) := by positivity
  have hCpterm3 : (0 : ℝ) ≤ M₀ / Csh := by positivity
  have hCpterm4 : (0 : ℝ) ≤
      2 * (Dη ^ (K₃₆ * (P.natDegree + 1)) * A₃₆ ^ (P.natDegree + 1)) := by positivity
  have hCp1 : 1 ≤ Cp := by rw [hCpdef]; linarith
  have hCp_2M₀ : 2 * M₀ ≤ Cp := by rw [hCpdef]; linarith
  have hCp_2M₀pow : (2 * M₀) ^ P.natDegree ≤ Cp := by rw [hCpdef]; linarith
  have hCp_prov : A₃₆ ^ (K₃₆ + 1) * Dη ^ (K₃₆ * (K₃₆ + 1)) ≤ Cp := by rw [hCpdef]; linarith
  have hCp_Csh : M₀ / Csh ≤ Cp := by rw [hCpdef]; linarith
  have hCp_X : 2 * (Dη ^ (K₃₆ * (P.natDegree + 1)) * A₃₆ ^ (P.natDegree + 1)) ≤ Cp := by
    rw [hCpdef]; linarith
  refine ⟨Cp, hCp1, 1 + 2 * K₃₄ * K₃₆ * (P.natDegree + K₃₆ + 2), by omega, ?_⟩
  intro C hC1 K hK N N₁ g₀ g₁ g₂ γ δ' hHyp hgauge hdir
  have hHyp' := hHyp
  obtain ⟨hdH, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1', hK1, hsmall, hnd,
    hS0, hS1, hS2, hb0, hb1, hb2, hΛ⟩ := hHyp'
  have hd1 : 1 ≤ P.natDegree := by omega
  -- ## consequences of `Kp ≤ K`
  have hK_big : 2 * K₃₄ * K₃₆ * (P.natDegree + K₃₆ + 2) ≤ K := by omega
  have hKnew_le : 2 * K₃₄ * K₃₆ * (P.natDegree + 1) ≤ K := by
    have h1 : 2 * K₃₄ * K₃₆ * (P.natDegree + 1) ≤ 2 * K₃₄ * K₃₆ * (P.natDegree + K₃₆ + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    exact le_trans h1 hK_big
  have hγK_le_new : γ ^ K ≤ γ ^ (2 * K₃₄ * K₃₆ * (P.natDegree + 1)) :=
    pow_le_pow_of_le_one hγ0.le hγ1 hKnew_le
  have hK_a : 2 * K₃₄ * K₃₆ ≤ K := by
    have h1 : 2 * K₃₄ * K₃₆ * 1 ≤ 2 * K₃₄ * K₃₆ * (P.natDegree + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h5 : 2 * K₃₄ * K₃₆ * 1 = 2 * K₃₄ * K₃₆ := Nat.mul_one _
    rw [h5] at h1
    exact le_trans h1 hKnew_le
  have hK_d : 2 * K₃₄ * K₃₆ * P.natDegree ≤ K := by
    have h1 : 2 * K₃₄ * K₃₆ * P.natDegree ≤ 2 * K₃₄ * K₃₆ * (P.natDegree + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    exact le_trans h1 hKnew_le
  have hK_e : 2 * K₃₄ * K₃₆ * (K₃₆ + 1) ≤ K := by
    have h1 : 2 * K₃₄ * K₃₆ * (K₃₆ + 1) ≤ 2 * K₃₄ * K₃₆ * (P.natDegree + K₃₆ + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    exact le_trans h1 hK_big
  -- ## the enlarged ambient
  obtain ⟨Np, hNpdef⟩ : ∃ Np : ℕ, Np = ambMu P.natDegree N N₁ * N₁ := ⟨_, rfl⟩
  have hambMupos : (0 : ℝ) < (ambMu P.natDegree N N₁ : ℕ) :=
    Nat.cast_pos.mpr (ambMu_pos (d := P.natDegree) hN hN₁)
  have hNp1 : 1 ≤ Np := by
    rw [hNpdef]
    exact Nat.mul_pos (ambMu_pos (d := P.natDegree) hN hN₁) (by omega)
  have hN₁_le_Np : N₁ ≤ Np := by
    rw [hNpdef]
    calc N₁ = 1 * N₁ := (one_mul _).symm
      _ ≤ ambMu P.natDegree N N₁ * N₁ :=
          Nat.mul_le_mul_right _ (ambMu_pos (d := P.natDegree) hN hN₁)
  have hNp_ge_pow : (N : ℝ) ^ P.natDegree ≤ (Np : ℝ) := by
    rw [hNpdef, Nat.cast_mul]
    exact le_ambMu_mul (d := P.natDegree) hN₁
  have hNp_lt : (Np : ℝ) < A₀ * (N : ℝ) ^ P.natDegree := by
    rw [hNpdef, Nat.cast_mul, hA₀def]
    have h := ambMu_mul_lt (d := P.natDegree) (N := N) (N₁ := N₁) hN₁
    have h2 : (2 : ℝ) * (N₁ : ℝ) ≤ (2 * A') * (N : ℝ) ^ P.natDegree := by
      calc (2 : ℝ) * (N₁ : ℝ) ≤ 2 * (A' * (N : ℝ) ^ P.natDegree) := by linarith [hsc1]
        _ = (2 * A') * (N : ℝ) ^ P.natDegree := by ring
    linarith
  have hNp_scale : N₁ + N ^ (P.natDegree - 1) ≤ Np := by
    rw [hNpdef]
    exact ambMu_hscale (d := P.natDegree) hd1 hN hN₁
  -- ## the strength `γ₃₄ = γ/ambMu`
  obtain ⟨γ₃₄, hγ₃₄def⟩ : ∃ γ₃₄ : ℝ, γ₃₄ = γ / (ambMu P.natDegree N N₁) := ⟨_, rfl⟩
  have hγ₃₄pos : 0 < γ₃₄ := by rw [hγ₃₄def]; positivity
  have hγ₃₄le1 : γ₃₄ ≤ 1 := by
    rw [hγ₃₄def, div_le_iff₀ hambMupos]
    calc γ ≤ 1 := hγ1
      _ ≤ (ambMu P.natDegree N N₁ : ℝ) := by exact_mod_cast (ambMu_pos (d := P.natDegree) hN hN₁)
      _ = 1 * (ambMu P.natDegree N N₁ : ℝ) := (one_mul _).symm
  have hambMu_le : (ambMu P.natDegree N N₁ : ℝ) ≤ A' / γ + 2 := by
    have h := ambMu_le_of_scale (d := P.natDegree) (N := N) (N₁ := N₁) hN₁ hγ0 hA' hsc2
    simp only [ambMu] at h ⊢
    push_cast
    linarith
  have hγ₃₄_ge : γ ^ 2 / (A' + 2) ≤ γ₃₄ := by
    rw [hγ₃₄def, div_le_div_iff₀ (by positivity : (0 : ℝ) < A' + 2) hambMupos]
    calc γ ^ 2 * (ambMu P.natDegree N N₁ : ℝ) ≤ γ ^ 2 * (A' / γ + 2) :=
          mul_le_mul_of_nonneg_left hambMu_le (by positivity)
      _ = γ * (A' + 2 * γ) := by field_simp; try ring
      _ ≤ γ * (A' + 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hγ0.le
          linarith
  -- ## the family strength `η` and the consumer's window `δ''`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = (γ₃₄ / A₃₄) ^ K₃₄ := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hη_le1 : η ≤ 1 := by
    rw [hηdef]
    refine pow_le_one₀ (by positivity) ?_
    rw [div_le_one hA₃₄pos]
    exact le_trans hγ₃₄le1 hA₃₄
  have hbase : γ ^ 2 / ((A' + 2) * A₃₄) ≤ γ₃₄ / A₃₄ := by
    have h : γ ^ 2 / (A' + 2) / A₃₄ ≤ γ₃₄ / A₃₄ :=
      div_le_div_of_nonneg_right hγ₃₄_ge hA₃₄pos.le
    rwa [div_div] at h
  have hη_ge : γ ^ (2 * K₃₄) / Dη ≤ η := by
    rw [hηdef, hDηdef]
    calc γ ^ (2 * K₃₄) / (((A' + 2) * A₃₄) ^ K₃₄)
        = (γ ^ 2 / ((A' + 2) * A₃₄)) ^ K₃₄ := by rw [div_pow, ← pow_mul]
      _ ≤ (γ₃₄ / A₃₄) ^ K₃₄ := pow_le_pow_left₀ (by positivity) hbase K₃₄
  have hη_pow_ge : γ ^ (2 * K₃₄ * K₃₆) / Dη ^ K₃₆ ≤ η ^ K₃₆ := by
    calc γ ^ (2 * K₃₄ * K₃₆) / Dη ^ K₃₆ = (γ ^ (2 * K₃₄) / Dη) ^ K₃₆ := by
          rw [div_pow, ← pow_mul]
      _ ≤ η ^ K₃₆ := pow_le_pow_left₀ (by positivity) hη_ge K₃₆
  obtain ⟨δ'', hδ''def⟩ : ∃ δ'' : ℝ, δ'' = η ^ K₃₆ / A₃₆ := ⟨_, rfl⟩
  have hδ''pos : 0 < δ'' := by rw [hδ''def]; positivity
  have hA₃₆δ'' : A₃₆ * δ'' = η ^ K₃₆ := by rw [hδ''def]; field_simp
  have hA₃₄δ'' : A₃₄ * δ'' ≤ γ₃₄ ^ K₃₄ := by
    have hm1 : 1 ≤ K₃₄ * K₃₆ := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hηeq : η ^ K₃₆ = γ₃₄ ^ (K₃₄ * K₃₆) / A₃₄ ^ (K₃₄ * K₃₆) := by
      rw [hηdef, ← pow_mul, div_pow]
    have h1 : A₃₄ / A₃₄ ^ (K₃₄ * K₃₆) ≤ 1 := by
      rw [div_le_one (by positivity)]
      simpa using pow_le_pow_right₀ hA₃₄ hm1
    have h2 : γ₃₄ ^ (K₃₄ * K₃₆) ≤ γ₃₄ ^ K₃₄ :=
      pow_le_pow_of_le_one hγ₃₄pos.le hγ₃₄le1 (Nat.le_mul_of_pos_right K₃₄ (by omega))
    have h3 : (0 : ℝ) ≤ γ₃₄ ^ (K₃₄ * K₃₆) := by positivity
    rw [hδ''def, hηeq]
    rw [← mul_div_assoc]
    have hrew : A₃₄ * (γ₃₄ ^ (K₃₄ * K₃₆) / A₃₄ ^ (K₃₄ * K₃₆)) / A₃₆
        = γ₃₄ ^ (K₃₄ * K₃₆) * (A₃₄ / A₃₄ ^ (K₃₄ * K₃₆)) / A₃₆ := by ring
    rw [hrew]
    calc γ₃₄ ^ (K₃₄ * K₃₆) * (A₃₄ / A₃₄ ^ (K₃₄ * K₃₆)) / A₃₆
        ≤ γ₃₄ ^ (K₃₄ * K₃₆) * 1 / A₃₆ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) (by positivity)
      _ = γ₃₄ ^ (K₃₄ * K₃₆) / A₃₆ := by rw [mul_one]
      _ ≤ γ₃₄ ^ (K₃₄ * K₃₆) := by
          rw [div_le_iff₀ hA₃₆pos]
          nlinarith [h3, hA₃₆]
      _ ≤ γ₃₄ ^ K₃₄ := h2
  have hδ''_ge : γ ^ (2 * K₃₄ * K₃₆) / M₀ ≤ δ'' := by
    have h2 : γ ^ (2 * K₃₄ * K₃₆) * A₃₆ ≤ η ^ K₃₆ * (Dη ^ K₃₆ * A₃₆) := by
      have h3 : (γ ^ (2 * K₃₄ * K₃₆) / Dη ^ K₃₆) * A₃₆ ≤ η ^ K₃₆ * A₃₆ :=
        mul_le_mul_of_nonneg_right hη_pow_ge (by positivity)
      rw [div_mul_eq_mul_div] at h3
      have h4 : γ ^ (2 * K₃₄ * K₃₆) * A₃₆ ≤ η ^ K₃₆ * A₃₆ * Dη ^ K₃₆ :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < Dη ^ K₃₆)).mp h3
      linarith [h4]
    rw [hδ''def, hM₀def]
    rw [div_le_div_iff₀ (by positivity) hA₃₆pos]
    linarith [h2]
  -- ## the numerical facts derived from `Hyp`
  have hL1 : 1 ≤ dirLen P δ' N := Hyp.one_le_dirLen hHyp
  have hL1R : (1 : ℝ) ≤ (dirLen P δ' N : ℝ) := by exact_mod_cast hL1
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1'
  have hgauge' : A' * Cp ≤ γ ^ K * (A' * (N : ℝ) ^ P.natDegree) := by
    have h1 : A' * Cp ≤ γ ^ K * (N₁ : ℝ) := by
      calc A' * Cp ≤ C := hgauge
        _ ≤ C * (dirLen P δ' N : ℝ) := le_mul_of_one_le_right (le_of_lt hCpos) hL1R
        _ ≤ γ ^ K * (N₁ : ℝ) := hsmall
    have h2 : γ ^ K * (N₁ : ℝ) ≤ γ ^ K * (A' * (N : ℝ) ^ P.natDegree) :=
      mul_le_mul_of_nonneg_left hsc1 (by positivity)
    linarith [le_trans h1 h2]
  have hCp_le_γKNpow : Cp ≤ γ ^ K * (N : ℝ) ^ P.natDegree := by
    have h4 : A' * Cp ≤ A' * (γ ^ K * (N : ℝ) ^ P.natDegree) := by
      have := hgauge'
      linarith [this]
    exact le_of_mul_le_mul_left h4 hA'pos
  have hCp_inv_le : Cp * γ⁻¹ ^ K ≤ (N : ℝ) ^ P.natDegree := by
    calc Cp * γ⁻¹ ^ K ≤ (γ ^ K * (N : ℝ) ^ P.natDegree) * γ⁻¹ ^ K :=
          mul_le_mul_of_nonneg_right hCp_le_γKNpow (by positivity)
      _ = (N : ℝ) ^ P.natDegree := by
          rw [inv_pow, mul_comm (γ ^ K) ((N : ℝ) ^ P.natDegree), mul_assoc,
            mul_inv_cancel₀ (pow_ne_zero K (ne_of_gt hγ0)), mul_one]
  have hγK_le : γ ^ K ≤ γ ^ (2 * K₃₄ * K₃₆) := pow_le_pow_of_le_one hγ0.le hγ1 hK_a
  -- ## the window transfer: `δ' ≤ δ''^(deg P + 1)`
  have hM₀_pow : M₀ ^ (P.natDegree + 1) =
      Dη ^ (K₃₆ * (P.natDegree + 1)) * A₃₆ ^ (P.natDegree + 1) := by
    rw [hM₀def, mul_pow, ← pow_mul]
  have hpowdiv : η ^ K₃₆ * δ'' ^ P.natDegree / A₃₆ = δ'' ^ (P.natDegree + 1) := by
    rw [pow_succ, ← hA₃₆δ'']
    field_simp
  have hδ''_ge_d1 : γ ^ (2 * K₃₄ * K₃₆ * (P.natDegree + 1)) /
      (Dη ^ (K₃₆ * (P.natDegree + 1)) * A₃₆ ^ (P.natDegree + 1)) ≤
      δ'' ^ (P.natDegree + 1) := by
    have h1 : (γ ^ (2 * K₃₄ * K₃₆) / M₀) ^ (P.natDegree + 1) =
        γ ^ (2 * K₃₄ * K₃₆ * (P.natDegree + 1)) /
          (Dη ^ (K₃₆ * (P.natDegree + 1)) * A₃₆ ^ (P.natDegree + 1)) := by
      rw [div_pow, hM₀_pow, ← pow_mul]
    rw [← h1]
    exact pow_le_pow_left₀ (by positivity) hδ''_ge _
  have hδ'_le : δ' ≤ 2 * γ ^ K / Cp := delta_le_of_window_p hHyp hA' hgauge hCp1
  have hstep : 2 * γ ^ K / Cp ≤
      γ ^ (2 * K₃₄ * K₃₆ * (P.natDegree + 1)) /
        (Dη ^ (K₃₆ * (P.natDegree + 1)) * A₃₆ ^ (P.natDegree + 1)) := by
    have hp1 : (2 * (Dη ^ (K₃₆ * (P.natDegree + 1)) * A₃₆ ^ (P.natDegree + 1))) * γ ^ K
        ≤ Cp * γ ^ K := mul_le_mul_of_nonneg_right hCp_X (pow_nonneg hγ0.le K)
    have hp2 : γ ^ K * Cp ≤ γ ^ (2 * K₃₄ * K₃₆ * (P.natDegree + 1)) * Cp :=
      mul_le_mul_of_nonneg_right hγK_le_new (le_of_lt (by positivity : (0 : ℝ) < Cp))
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < Cp)
      (by positivity : (0 : ℝ) < Dη ^ (K₃₆ * (P.natDegree + 1)) * A₃₆ ^ (P.natDegree + 1))]
    linarith [hp1, hp2]
  have hδ'_le_d : δ' ≤ δ'' ^ (P.natDegree + 1) := by
    linarith [hδ'_le, hstep, hδ''_ge_d1]
  have hL_ge : δ' * (N : ℝ) ^ P.natDegree ≤
      max (1 : ℝ) (η ^ K₃₆ * δ'' ^ P.natDegree * (N : ℝ) ^ P.natDegree / A₃₆) := by
    have h1 : δ' * (N : ℝ) ^ P.natDegree ≤
        η ^ K₃₆ * δ'' ^ P.natDegree * (N : ℝ) ^ P.natDegree / A₃₆ := by
      have h2 : η ^ K₃₆ * δ'' ^ P.natDegree * (N : ℝ) ^ P.natDegree / A₃₆
          = δ'' ^ (P.natDegree + 1) * (N : ℝ) ^ P.natDegree := by
        rw [← hpowdiv]
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right hδ'_le_d (by positivity)
    exact le_trans h1 (le_max_right _ _)
  have hγinvpow_d : 1 ≤ γ⁻¹ ^ K * γ ^ (2 * K₃₄ * K₃₆ * P.natDegree) := by
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity : (0 : ℝ) < γ ^ K), one_mul]
    exact pow_le_pow_of_le_one hγ0.le hγ1 hK_d
  have h2d : (2 : ℝ) ^ P.natDegree ≤ (N : ℝ) ^ P.natDegree * δ'' ^ P.natDegree := by
    have hCp_d : (2 : ℝ) ^ P.natDegree * M₀ ^ P.natDegree ≤ Cp := by
      rw [← mul_pow]; exact hCp_2M₀pow
    have h5 : (2 : ℝ) ^ P.natDegree ≤ Cp / M₀ ^ P.natDegree := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hδpow : γ ^ (2 * K₃₄ * K₃₆ * P.natDegree) / M₀ ^ P.natDegree ≤ δ'' ^ P.natDegree := by
      rw [pow_mul, ← div_pow]
      exact pow_le_pow_left₀ (by positivity) hδ''_ge P.natDegree
    have h6 : Cp / M₀ ^ P.natDegree
        ≤ Cp * γ⁻¹ ^ K * (γ ^ (2 * K₃₄ * K₃₆ * P.natDegree) / M₀ ^ P.natDegree) := by
      calc Cp / M₀ ^ P.natDegree
          = (Cp / M₀ ^ P.natDegree) * 1 := (mul_one _).symm
        _ ≤ (Cp / M₀ ^ P.natDegree) * (γ⁻¹ ^ K * γ ^ (2 * K₃₄ * K₃₆ * P.natDegree)) :=
            mul_le_mul_of_nonneg_left hγinvpow_d (by positivity)
        _ = Cp * γ⁻¹ ^ K * (γ ^ (2 * K₃₄ * K₃₆ * P.natDegree) / M₀ ^ P.natDegree) := by ring
    have h7 : Cp * γ⁻¹ ^ K * (γ ^ (2 * K₃₄ * K₃₆ * P.natDegree) / M₀ ^ P.natDegree)
        ≤ (N : ℝ) ^ P.natDegree * δ'' ^ P.natDegree := by
      have h8 := mul_le_mul_of_nonneg_right hCp_inv_le (by positivity :
        (0 : ℝ) ≤ γ ^ (2 * K₃₄ * K₃₆ * P.natDegree) / M₀ ^ P.natDegree)
      calc Cp * γ⁻¹ ^ K * (γ ^ (2 * K₃₄ * K₃₆ * P.natDegree) / M₀ ^ P.natDegree)
          = (Cp * γ⁻¹ ^ K) * (γ ^ (2 * K₃₄ * K₃₆ * P.natDegree) / M₀ ^ P.natDegree) := by ring
        _ ≤ (N : ℝ) ^ P.natDegree * (γ ^ (2 * K₃₄ * K₃₆ * P.natDegree) / M₀ ^ P.natDegree) := h8
        _ ≤ (N : ℝ) ^ P.natDegree * δ'' ^ P.natDegree :=
            mul_le_mul_of_nonneg_left hδpow (by positivity)
    linarith [h5, h6, h7]
  have hNδ''_ge : 2 ≤ (N : ℝ) * δ'' := by
    have h9 : (N : ℝ) ^ P.natDegree * δ'' ^ P.natDegree = ((N : ℝ) * δ'') ^ P.natDegree := by
      rw [mul_pow]
    have hpow := le_trans h2d (le_of_eq h9)
    exact le_of_pow_le_pow_left₀ (by omega : P.natDegree ≠ 0) (by positivity) hpow
  have h2floor : 2 ≤ (⌊δ'' * (N : ℝ)⌋).toNat := by
    have h2z : (2 : ℤ) ≤ ⌊δ'' * (N : ℝ)⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith [hNδ''_ge]
    have h : ((2 : ℕ) : ℤ) ≤ ⌊δ'' * (N : ℝ)⌋ := by exact_mod_cast h2z
    have := Int.toNat_le_toNat h
    simpa using this
  have hproviso : A₃₆ * (η * δ'') ^ (-(K₃₆ : ℤ)) ≤ (Np : ℝ) := by
    rw [zpow_neg, zpow_natCast]
    rw [mul_inv_le_iff₀ (by positivity)]
    have hηδ'' : γ ^ (2 * K₃₄ * (K₃₆ + 1)) / (Dη * M₀) ≤ η * δ'' := by
      have h := mul_le_mul hη_ge hδ''_ge (by positivity) (by positivity)
      calc γ ^ (2 * K₃₄ * (K₃₆ + 1)) / (Dη * M₀)
          = γ ^ (2 * K₃₄) / Dη * (γ ^ (2 * K₃₄ * K₃₆) / M₀) := by
            rw [div_mul_div_comm, ← pow_add]
            congr 2
            ring
        _ ≤ η * δ'' := h
    have h3 : (γ ^ (2 * K₃₄ * (K₃₆ + 1)) / (Dη * M₀)) ^ K₃₆ ≤ (η * δ'') ^ K₃₆ :=
      pow_le_pow_left₀ (by positivity) hηδ'' K₃₆
    have h4 : γ ^ (2 * K₃₄ * K₃₆ * (K₃₆ + 1)) / (Dη * M₀) ^ K₃₆
        ≤ (γ ^ (2 * K₃₄ * (K₃₆ + 1)) / (Dη * M₀)) ^ K₃₆ := by
      rw [div_pow]
      rw [show γ ^ (2 * K₃₄ * K₃₆ * (K₃₆ + 1)) = (γ ^ (2 * K₃₄ * (K₃₆ + 1))) ^ K₃₆ from by
        rw [← pow_mul]; ring_nf]
    have h7 : 1 ≤ γ⁻¹ ^ K * γ ^ (2 * K₃₄ * K₃₆ * (K₃₆ + 1)) := by
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity : (0 : ℝ) < γ ^ K), one_mul]
      exact pow_le_pow_of_le_one hγ0.le hγ1 hK_e
    have h8 : (Dη * M₀) ^ K₃₆ = A₃₆ ^ K₃₆ * Dη ^ (K₃₆ * (K₃₆ + 1)) := by
      rw [hM₀def, mul_pow, mul_pow, ← pow_mul]
      ring_nf
    have h11 : A₃₆ ≤ Cp / (Dη * M₀) ^ K₃₆ := by
      rw [h8, le_div_iff₀ (by positivity)]
      have h12 : A₃₆ * (A₃₆ ^ K₃₆ * Dη ^ (K₃₆ * (K₃₆ + 1)))
          = A₃₆ ^ (K₃₆ + 1) * Dη ^ (K₃₆ * (K₃₆ + 1)) := by
        rw [pow_succ]; ring
      rw [h12]
      exact hCp_prov
    have h13 : A₃₆ ≤ (Cp / (Dη * M₀) ^ K₃₆) * (γ⁻¹ ^ K * γ ^ (2 * K₃₄ * K₃₆ * (K₃₆ + 1))) := by
      calc A₃₆ ≤ (Cp / (Dη * M₀) ^ K₃₆) * 1 := by rw [mul_one]; exact h11
        _ ≤ _ := mul_le_mul_of_nonneg_left h7 (by positivity)
    calc A₃₆
        ≤ (Cp / (Dη * M₀) ^ K₃₆) * (γ⁻¹ ^ K * γ ^ (2 * K₃₄ * K₃₆ * (K₃₆ + 1))) := h13
      _ = Cp * γ⁻¹ ^ K * (γ ^ (2 * K₃₄ * K₃₆ * (K₃₆ + 1)) / (Dη * M₀) ^ K₃₆) := by ring
      _ ≤ Cp * γ⁻¹ ^ K * ((γ ^ (2 * K₃₄ * (K₃₆ + 1)) / (Dη * M₀)) ^ K₃₆) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ Cp * γ⁻¹ ^ K * (η * δ'') ^ K₃₆ := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (Cp * γ⁻¹ ^ K) * (η * δ'') ^ K₃₆ := by ring
      _ ≤ (N : ℝ) ^ P.natDegree * (η * δ'') ^ K₃₆ :=
          mul_le_mul_of_nonneg_right hCp_inv_le (by positivity)
      _ ≤ (Np : ℝ) * (η * δ'') ^ K₃₆ := by
          have hmul := mul_le_mul_of_nonneg_right hNp_ge_pow (by positivity :
            (0 : ℝ) ≤ (η * δ'') ^ K₃₆)
          linarith [hmul]
  -- ## the two chapters
  have hFbound : ∀ (i : Fin (P.natDegree + 1)) (x : ℤ),
      ‖embF P.natDegree Np g₀ g₁ g₂ i x‖ ≤ 1 := embF_bound hb0 hb1 hb2
  have hFsupp : ∀ i : Fin (P.natDegree + 1), SupportIn (embF P.natDegree Np g₀ g₁ g₂ i) Np :=
    embF_supportIn hN₁_le_Np hS0 hS1 hS2
  have hscale34 : γ₃₄ * (N : ℝ) ^ P.natDegree ≤ A₀ * (Np : ℝ) := by
    have h1 : γ₃₄ * (N : ℝ) ^ P.natDegree ≤ γ₃₄ * (Np : ℝ) :=
      mul_le_mul_of_nonneg_left hNp_ge_pow hγ₃₄pos.le
    have h2 : γ₃₄ * (Np : ℝ) ≤ (Np : ℝ) := by
      nlinarith [hγ₃₄le1, Nat.cast_nonneg (α := ℝ) Np]
    have h3 : (Np : ℝ) ≤ A₀ * (Np : ℝ) := by
      nlinarith [hA₀1, Nat.cast_nonneg (α := ℝ) Np]
    linarith
  have hLambdaMD : γ₃₄ ≤ ‖LambdaMD Np N P (embF P.natDegree Np g₀ g₁ g₂)‖ := by
    rw [hNpdef, embLambdaMD hd hN hN₁ g₀ g₁ g₂ hS0, hγ₃₄def, div_eq_mul_inv, norm_mul,
      norm_inv, Complex.norm_natCast]
    have h2 : γ * ((ambMu P.natDegree N N₁ : ℕ) : ℝ)⁻¹
        ≤ ‖LambdaZ N₁ N P g₀ g₁ g₂‖ * ((ambMu P.natDegree N N₁ : ℕ) : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hΛ (by positivity)
    linarith [h2]
  have h34out : η ≤ D.famAvg P.natDegree (⌊δ'' * (N : ℝ)⌋).toNat P.leadingCoeff Np g₂ := by
    have h := h34'' Np N (embF P.natDegree Np g₀ g₁ g₂) γ₃₄ δ'' hd hNp1 hN
      (le_of_lt hNp_lt) hscale34 hγ₃₄pos hγ₃₄le1 hδ''pos hA₃₄δ'' h2floor hFbound hFsupp hLambdaMD
    rw [embF_last hd] at h
    rwa [← hηdef] at h
  have h36out : η ^ K₃₆ ≤ A₃₆ * uNormPow s
      (arithIcc (dirCoeff P)
        (⌊max (1 : ℝ) (η ^ K₃₆ * δ'' ^ P.natDegree * (N : ℝ) ^ P.natDegree / A₃₆)⌋).toNat)
      (symIcc Np) g₂ := by
    have h := h36'' Np N g₂ η δ'' hd hNp1 hN (le_of_lt hNp_lt)
      (by nlinarith [hNp_ge_pow, Nat.cast_nonneg (α := ℝ) Np, hA₀1])
      hηpos hη_le1 hδ''pos (le_of_eq hA₃₆δ'') h2floor hb2 (hS2.mono hN₁_le_Np) hproviso h34out
    simpa only [dirCoeff] using h
  -- ## the transfer back to the data's direction count and ambient
  have hdirne : dirCoeff P ≠ 0 := by
    rw [dirCoeff]
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast Nat.factorial_ne_zero P.natDegree
    · rw [Polynomial.leadingCoeff_ne_zero]
      intro h0
      rw [h0] at hd
      simp at hd
  have hL_le_Llong : dirLen P δ' N ≤
      (⌊max (1 : ℝ) (η ^ K₃₆ * δ'' ^ P.natDegree * (N : ℝ) ^ P.natDegree / A₃₆)⌋).toNat := by
    rw [dirLen]
    exact Int.toNat_le_toNat (Int.floor_mono hL_ge)
  have hshrink := hCsh (dirCoeff P) (dirLen P δ' N)
    ((⌊max (1 : ℝ) (η ^ K₃₆ * δ'' ^ P.natDegree * (N : ℝ) ^ P.natDegree / A₃₆)⌋).toNat)
    N₁ Np g₂ hdirne hL1 hL_le_Llong hN₁_le_Np hS2 hb2
  have hUlong : η ^ K₃₆ / A₃₆ ≤ uNormPow s
      (arithIcc (dirCoeff P)
        (⌊max (1 : ℝ) (η ^ K₃₆ * δ'' ^ P.natDegree * (N : ℝ) ^ P.natDegree / A₃₆)⌋).toNat)
      (symIcc Np) g₂ := by
    rw [div_le_iff₀ hA₃₆pos]; linarith [h36out]
  have hUlower : Csh * η ^ K₃₆ / A₃₆ ≤ uNormPow s
      (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂ := by
    have h1 : Csh * (η ^ K₃₆ / A₃₆) ≤ Csh * uNormPow s
        (arithIcc (dirCoeff P)
          (⌊max (1 : ℝ) (η ^ K₃₆ * δ'' ^ P.natDegree * (N : ℝ) ^ P.natDegree / A₃₆)⌋).toNat)
        (symIcc Np) g₂ :=
      mul_le_mul_of_nonneg_left hUlong hCshpos.le
    have h2 : Csh * η ^ K₃₆ / A₃₆ = Csh * (η ^ K₃₆ / A₃₆) := by ring
    rw [h2]
    linarith [h1, hshrink]
  -- ## the final arithmetic
  rw [Concl]
  have hηK : γ ^ K * A₃₆ / M₀ ≤ η ^ K₃₆ := by
    rw [hM₀def]
    have h1 : γ ^ K * A₃₆ / (Dη ^ K₃₆ * A₃₆) = γ ^ K / Dη ^ K₃₆ := by field_simp
    rw [h1]
    exact le_trans (div_le_div_of_nonneg_right hγK_le (by positivity)) hη_pow_ge
  have hfinal : γ ^ K ≤ Cp * A' ^ K * γ⁻¹ ^ K * (Csh * η ^ K₃₆ / A₃₆) := by
    have h2 : γ ^ K ≤ M₀ * η ^ K₃₆ / A₃₆ := by
      have h3 : γ ^ K * A₃₆ ≤ η ^ K₃₆ * M₀ := by
        have h4 := (div_le_iff₀ hM₀pos).mp hηK
        linarith [h4]
      rw [le_div_iff₀ hA₃₆pos]
      linarith [h3]
    have h3 : M₀ ≤ Cp * Csh := by
      have h4 := (div_le_iff₀ hCshpos).mp hCp_Csh
      linarith [h4]
    have h4 : M₀ * η ^ K₃₆ / A₃₆ ≤ (Cp * Csh) * η ^ K₃₆ / A₃₆ := by
      have h5 : M₀ * η ^ K₃₆ ≤ (Cp * Csh) * η ^ K₃₆ :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      exact div_le_div_of_nonneg_right h5 hA₃₆pos.le
    have h5 : (Cp * Csh) * η ^ K₃₆ / A₃₆ ≤ Cp * A' ^ K * γ⁻¹ ^ K * (Csh * η ^ K₃₆ / A₃₆) := by
      have hA'K1 : 1 ≤ A' ^ K := one_le_pow₀ hA'
      have hγi1 : 1 ≤ γ⁻¹ ^ K := one_le_pow₀ (one_le_inv₀ hγ0 |>.mpr hγ1)
      have h6 : 1 ≤ A' ^ K * γ⁻¹ ^ K := by
        have h1 : (1 : ℝ) * 1 ≤ A' ^ K * γ⁻¹ ^ K :=
          mul_le_mul hA'K1 hγi1 (by norm_num) (by positivity)
        simpa using h1
      have h7 : Cp * Csh * η ^ K₃₆ / A₃₆ = Cp * (Csh * η ^ K₃₆ / A₃₆) := by ring
      rw [h7]
      calc Cp * (Csh * η ^ K₃₆ / A₃₆)
          = Cp * (Csh * η ^ K₃₆ / A₃₆) * 1 := (mul_one _).symm
        _ ≤ Cp * (Csh * η ^ K₃₆ / A₃₆) * (A' ^ K * γ⁻¹ ^ K) :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
        _ = Cp * A' ^ K * γ⁻¹ ^ K * (Csh * η ^ K₃₆ / A₃₆) := by ring
    linarith [h2, h4, h5]
  have hfin : Cp * A' ^ K * γ⁻¹ ^ K * (Csh * η ^ K₃₆ / A₃₆)
      ≤ Cp * A' ^ K * γ⁻¹ ^ K * uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N))
          (symIcc N₁) g₂ :=
    mul_le_mul_of_nonneg_left hUlower (by positivity)
  linarith [hfinal, hfin]

end


end Work.Peluse.PaperRoute
