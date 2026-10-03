import Mathlib
import Submission.Work.Peluse.PaperRoute.Defs
import Submission.Work.Peluse.PaperRoute.PiecePetTwo
import Submission.Work.Peluse.NodeAux

/-!
# `PeluseUControlPaper` from the paper-route chapter `PiecePetTwo`

`Work.Peluse.UControl.PiecePetTwo P` (`PaperRoute/PiecePetTwo.lean`) is the paper's chain
(Peluse's Propositions 3.4 + 3.6 for `(x, x+y, x+P(y))`) at a *fixed* level `s₀ ≥ 2`, with the
data hypotheses packaged as `Work.Peluse.UControl.Hyp`, the PET gauge `A'·C_p ≤ C` and the
direction fit `κ·L ≤ N₁`.  This module wires it to the paper-faithful node of the frozen target,
`Work.Peluse.PeluseUControlPaper P` (Corollary 3.8 + Theorem 3.7 at the crux's *single* shift
length `D = ⌊δ^K N^d / C⌋`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.PaperRoute

noncomputable section

open Work.Peluse

/-! ## Elementary arithmetic helpers -/

/-- `γ = δ²N₀²/((2MA+1)MA)` is positive, is `≤ δ`, and is bounded below by `δ⁵/(3A'²θ²)`
whenever `MA ≤ θ·Nᵈ` and `Nᵈ ≤ A' δ⁻¹ N₀`. -/
lemma gamma_bounds {δ θ A' : ℝ} {d N N₀ MA : ℕ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N)
    (hN₀ : 1 ≤ N₀) (hMA : 1 ≤ MA) (hN₀MA : (N₀ : ℝ) ≤ (MA : ℝ))
    (hA' : 1 ≤ A') (hθ : 0 < θ)
    (hMAub : (MA : ℝ) ≤ θ * (N : ℝ) ^ d)
    (hsc2 : (N : ℝ) ^ d ≤ A' * δ⁻¹ * (N₀ : ℝ)) :
    0 < δ ^ 2 * (N₀ : ℝ) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ)) ∧
    δ ^ 2 * (N₀ : ℝ) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ)) ≤ δ ∧
    δ ^ 5 / (3 * A' ^ 2 * θ ^ 2)
      ≤ δ ^ 2 * (N₀ : ℝ) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ)) := by
  have hMA1 : (1 : ℝ) ≤ (MA : ℝ) := by exact_mod_cast hMA
  have hMApos : (0 : ℝ) < (MA : ℝ) := by linarith
  have hN₀1 : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
  have hN₀pos : (0 : ℝ) < (N₀ : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hA'pos : 0 < A' := by linarith
  have hden : (0 : ℝ) < (2 * (MA : ℝ) + 1) * (MA : ℝ) := by positivity
  have hdenle : (2 * (MA : ℝ) + 1) * (MA : ℝ) ≤ 3 * (MA : ℝ) ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · -- `γ ≤ δ`
    have hN₀sq : (N₀ : ℝ) ^ 2 ≤ (MA : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hN₀MA 2
    have h1 : δ ^ 2 * (N₀ : ℝ) ^ 2 ≤ δ ^ 2 * (MA : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hN₀sq (by positivity)
    have h2 : δ ^ 2 * (MA : ℝ) ^ 2 ≤ ((2 * (MA : ℝ) + 1) * (MA : ℝ)) * δ ^ 2 := by
      have hMA2 : (MA : ℝ) ^ 2 ≤ (2 * (MA : ℝ) + 1) * (MA : ℝ) := by nlinarith
      calc δ ^ 2 * (MA : ℝ) ^ 2 = (MA : ℝ) ^ 2 * δ ^ 2 := by ring
        _ ≤ ((2 * (MA : ℝ) + 1) * (MA : ℝ)) * δ ^ 2 :=
            mul_le_mul_of_nonneg_right hMA2 (by positivity)
    have h3 : δ ^ 2 * (N₀ : ℝ) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ)) ≤ δ ^ 2 := by
      rw [div_le_iff₀ hden]
      linarith [h1, h2]
    have h4 : δ ^ 2 ≤ δ := by nlinarith [hδ0, hδ1]
    linarith
  · -- `δ⁵/(3A'²θ²) ≤ γ`
    have hδN₀ : δ * (N : ℝ) ^ d / A' ≤ (N₀ : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hsc2 (le_of_lt (div_pos hδ0 hA'pos))
      have h2 : (δ / A') * (A' * δ⁻¹ * (N₀ : ℝ)) = (N₀ : ℝ) := by field_simp
      have h3 : (δ / A') * (N : ℝ) ^ d = δ * (N : ℝ) ^ d / A' := by ring
      linarith [h, h2, h3]
    have hstep1 : δ ^ 2 * (δ * (N : ℝ) ^ d / A') ^ 2 ≤ δ ^ 2 * (N₀ : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hδN₀ 2) (by positivity)
    have hstepA : δ ^ 2 * (δ * (N : ℝ) ^ d / A') ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ))
        ≤ δ ^ 2 * (N₀ : ℝ) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ)) :=
      div_le_div_of_nonneg_right hstep1 (le_of_lt hden)
    have hstepB : δ ^ 2 * (δ * (N : ℝ) ^ d / A') ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ))
        = δ ^ 4 / (3 * A' ^ 2 * θ ^ 2)
          * (3 * θ ^ 2 * ((N : ℝ) ^ d) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ))) := by
      field_simp
    have hNdpow : (0 : ℝ) < ((N : ℝ) ^ d) ^ 2 := by positivity
    have hMA2le : (2 * (MA : ℝ) + 1) * (MA : ℝ) ≤ 3 * θ ^ 2 * ((N : ℝ) ^ d) ^ 2 := by
      have h1 : (MA : ℝ) ^ 2 ≤ (θ * (N : ℝ) ^ d) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hMApos) hMAub 2
      have h2 : (θ * (N : ℝ) ^ d) ^ 2 = θ ^ 2 * ((N : ℝ) ^ d) ^ 2 := by rw [mul_pow]
      nlinarith [hdenle, h1, h2]
    have hstepC : 1 ≤ 3 * θ ^ 2 * ((N : ℝ) ^ d) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ)) := by
      rw [le_div_iff₀ hden]
      linarith [hMA2le]
    have hstepD : δ ^ 5 / (3 * A' ^ 2 * θ ^ 2) ≤ δ ^ 4 / (3 * A' ^ 2 * θ ^ 2) := by
      have h34 : δ ^ 5 ≤ δ ^ 4 := by
        have : δ ^ 5 = δ ^ 4 * δ := by ring
        rw [this]
        nlinarith [pow_nonneg (le_of_lt hδ0) 4, hδ1, hδ0]
      exact div_le_div_of_nonneg_right h34 (by positivity)
    have hstepE : δ ^ 4 / (3 * A' ^ 2 * θ ^ 2) * 1
        ≤ δ ^ 4 / (3 * A' ^ 2 * θ ^ 2)
          * (3 * θ ^ 2 * ((N : ℝ) ^ d) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ))) :=
      mul_le_mul_of_nonneg_left hstepC (by positivity)
    calc δ ^ 5 / (3 * A' ^ 2 * θ ^ 2)
        ≤ δ ^ 4 / (3 * A' ^ 2 * θ ^ 2) := hstepD
      _ = δ ^ 4 / (3 * A' ^ 2 * θ ^ 2) * 1 := by ring
      _ ≤ δ ^ 4 / (3 * A' ^ 2 * θ ^ 2)
            * (3 * θ ^ 2 * ((N : ℝ) ^ d) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ))) := hstepE
      _ = δ ^ 2 * (δ * (N : ℝ) ^ d / A') ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ)) := by
            rw [← hstepB]
      _ ≤ δ ^ 2 * (N₀ : ℝ) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ)) := hstepA

/-- The floor of a real number `≥ 2` is at least its half. -/
lemma half_le_floor_toNat {Γ : ℝ} (hΓ : 2 ≤ Γ) : Γ / 2 ≤ ((⌊Γ⌋ : ℤ) : ℝ) := by
  have h3 : Γ - 1 ≤ ((⌊Γ⌋ : ℤ) : ℝ) := by
    have := Int.lt_floor_add_one Γ
    linarith
  linarith

/-- `N ≥ C·(δ⁻¹)^{K₂}` with `1 ≤ d` and `K ≤ d·K₂` forces the crux window
`⌊δ^K Nᵈ/C⌋ ≥ 1` (so that the crux's shift length is never `0`). -/
lemma crux_window_ge_one {δ : ℝ} {d K K₂ C N : ℕ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hd : 1 ≤ d) (hN : 1 ≤ N) (hC : 1 ≤ C)
    (hnd : (C : ℝ) * (δ⁻¹) ^ K₂ ≤ (N : ℝ)) (hKK₂ : K ≤ d * K₂) :
    1 ≤ (⌊δ ^ K * (N : ℝ) ^ d / (C : ℝ)⌋).toNat := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hC1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hCpos : (0 : ℝ) < (C : ℝ) := by linarith
  have hNd : (C : ℝ) ^ d * (δ⁻¹) ^ (K₂ * d) ≤ (N : ℝ) ^ d := by
    have h := pow_le_pow_left₀ (by positivity) hnd d
    rw [mul_pow, ← pow_mul] at h
    exact h
  have hKK₂' : K ≤ K₂ * d := by rwa [Nat.mul_comm d K₂] at hKK₂
  have hone : 1 ≤ δ ^ K * (δ⁻¹) ^ (K₂ * d) := by
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa using pow_le_pow_of_le_one (le_of_lt hδ0) hδ1 hKK₂'
  have heq : δ ^ K * ((C : ℝ) ^ d * (δ⁻¹) ^ (K₂ * d)) / (C : ℝ)
      = (C : ℝ) ^ (d - 1) * (δ ^ K * (δ⁻¹) ^ (K₂ * d)) := by
    have hCd : (C : ℝ) ^ d = (C : ℝ) ^ (d - 1) * (C : ℝ) := by
      conv_lhs => rw [show d = (d - 1) + 1 by omega]
      rw [pow_add, pow_one]
    rw [hCd]
    field_simp
  have hmain : 1 ≤ δ ^ K * (N : ℝ) ^ d / (C : ℝ) := by
    have hstep : δ ^ K * ((C : ℝ) ^ d * (δ⁻¹) ^ (K₂ * d)) / (C : ℝ)
        ≤ δ ^ K * (N : ℝ) ^ d / (C : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNd (by positivity)) (le_of_lt hCpos)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (C : ℝ) ^ (d - 1) * (δ ^ K * (δ⁻¹) ^ (K₂ * d)) :=
            mul_le_mul (one_le_pow₀ hC1) hone (by norm_num) (by positivity)
      _ = δ ^ K * ((C : ℝ) ^ d * (δ⁻¹) ^ (K₂ * d)) / (C : ℝ) := heq.symm
      _ ≤ δ ^ K * (N : ℝ) ^ d / (C : ℝ) := hstep
  have h1 : (1 : ℤ) ≤ ⌊δ ^ K * (N : ℝ) ^ d / (C : ℝ)⌋ :=
    Int.le_floor.mpr (by push_cast; exact hmain)
  have h2 : ((1 : ℤ).toNat : ℕ) ≤ (⌊δ ^ K * (N : ℝ) ^ d / (C : ℝ)⌋).toNat :=
    Int.toNat_le_toNat h1
  simpa using h2

/-! ## Three arithmetic lemmas for the wiring

These are stated with *abstract* real variables so that the local definitions of the main proof
(which the elaborator unfolds under `rw`) never appear inside them. -/

/-- **The chapter's window is non-degenerate**: with `δ' = γ^{K_p}κ₁/C_p`, the target's
non-degeneracy `C ≤ (δ^{5K_p}N)^{O(1)}` forces `2 ≤ δ'N`. -/
lemma two_le_delta'_mul_N {γ δ' Γ₀ C_ch N Pw Cc : ℝ} {Kp : ℕ} {κ₁ : ℝ}
    (hδ' : δ' = γ ^ Kp * κ₁ / C_ch)
    (hγp : Pw / Γ₀ ^ Kp ≤ γ ^ Kp)
    (hPN : Cc ≤ Pw * N)
    (hκ₁C : 2 * Γ₀ ^ Kp * C_ch ≤ κ₁ * Cc)
    (hCc : 0 < C_ch) (hκ₁ : 0 < κ₁) (hΓ₀ : 0 < Γ₀) (hN : 0 < N) (hγ : 0 < γ) :
    2 ≤ δ' * N := by
  have h1 : (2 : ℝ) ≤ Cc * κ₁ / (Γ₀ ^ Kp * C_ch) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hκ₁C]
  have h3 : (2 : ℝ) ≤ (Pw * N) * κ₁ / (Γ₀ ^ Kp * C_ch) := by
    calc (2 : ℝ) ≤ Cc * κ₁ / (Γ₀ ^ Kp * C_ch) := h1
      _ ≤ (Pw * N) * κ₁ / (Γ₀ ^ Kp * C_ch) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hPN (le_of_lt hκ₁)
  have h4 : (Pw * N) * κ₁ / (Γ₀ ^ Kp * C_ch) = (Pw / Γ₀ ^ Kp) * κ₁ * N / C_ch := by ring
  have h5 : (Pw / Γ₀ ^ Kp) * κ₁ * N / C_ch ≤ γ ^ Kp * κ₁ * N / C_ch := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hCc)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγp (le_of_lt hκ₁)) (le_of_lt hN)
  have h6 : γ ^ Kp * κ₁ * N / C_ch = δ' * N := by rw [hδ']; ring
  linarith [h3, h4.le, h4.ge, h5, h6.le, h6.ge]

/-- **The chapter's non-degeneracy** `C_p ≤ (γδ')^{K_p}(δ'N)²`, from the target's
non-degeneracy `C ≤ δ^{-K₂}N` and the polynomial gain `γ ≥ δ⁵/Γ₀`. -/
lemma C_ch_le_gamma_delta {γ δ' Γ₀ C_ch N δ : ℝ} {Kp K₂ : ℕ} {κ₁ Cc : ℝ}
    (hδ' : δ' = γ ^ Kp * κ₁ / C_ch)
    (hγ : 0 < γ)
    (hγΓ₀ : δ ^ 5 / Γ₀ ≤ γ)
    (hN2 : Cc ^ 2 * (δ⁻¹) ^ (2 * K₂) ≤ N ^ 2)
    (hδK : (1 : ℝ) ≤ δ ^ (5 * (Kp * (Kp + 3))) * (δ⁻¹) ^ (2 * K₂))
    (hCc2 : C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) ≤ κ₁ ^ (Kp + 2) * Cc ^ 2)
    (hCc : 0 < C_ch) (hΓ₀ : 0 < Γ₀) (hκ₁ : 0 ≤ κ₁) (hδ0 : 0 < δ) :
    C_ch ≤ (γ * δ') ^ Kp * (δ' * N) ^ 2 := by
  have hEeq : (γ * δ') ^ Kp * (δ' * N) ^ 2
      = γ ^ (Kp * (Kp + 3)) * κ₁ ^ (Kp + 2) * N ^ 2 / C_ch ^ (Kp + 2) := by
    have h1 : (γ * δ') ^ Kp * (δ' * N) ^ 2 = γ ^ Kp * (δ') ^ (Kp + 2) * N ^ 2 := by ring_nf
    rw [h1, hδ', div_pow, mul_pow,
      show (γ ^ Kp) ^ (Kp + 2) = γ ^ (Kp * (Kp + 2)) by rw [pow_mul]]
    rw [show γ ^ Kp * (γ ^ (Kp * (Kp + 2)) * κ₁ ^ (Kp + 2) / C_ch ^ (Kp + 2)) * N ^ 2
        = γ ^ (Kp * (Kp + 3)) * κ₁ ^ (Kp + 2) * N ^ 2 / C_ch ^ (Kp + 2) by
      rw [show Kp * (Kp + 3) = Kp + Kp * (Kp + 2) by ring, pow_add]
      ring]
  rw [hEeq, le_div_iff₀ (by positivity)]
  have h1 : δ ^ (5 * (Kp * (Kp + 3))) / Γ₀ ^ (Kp * (Kp + 3)) ≤ γ ^ (Kp * (Kp + 3)) := by
    have h := pow_le_pow_left₀ (by positivity) hγΓ₀ (Kp * (Kp + 3))
    have h2 : (δ ^ 5 / Γ₀) ^ (Kp * (Kp + 3))
        = δ ^ (5 * (Kp * (Kp + 3))) / Γ₀ ^ (Kp * (Kp + 3)) := by rw [div_pow, ← pow_mul]
    rwa [h2] at h
  have hA : δ ^ (5 * (Kp * (Kp + 3))) ≤ γ ^ (Kp * (Kp + 3)) * Γ₀ ^ (Kp * (Kp + 3)) :=
    (div_le_iff₀ (by positivity)).mp h1
  have hB : Cc ^ 2 ≤ δ ^ (5 * (Kp * (Kp + 3))) * N ^ 2 := by
    have hb1 : Cc ^ 2 ≤ δ ^ (5 * (Kp * (Kp + 3))) * (Cc ^ 2 * (δ⁻¹) ^ (2 * K₂)) := by
      have h := mul_le_mul_of_nonneg_right hδK (pow_nonneg (le_of_lt hδ0) 2)
      nlinarith [h]
    have hb2 : δ ^ (5 * (Kp * (Kp + 3))) * (Cc ^ 2 * (δ⁻¹) ^ (2 * K₂))
        ≤ δ ^ (5 * (Kp * (Kp + 3))) * N ^ 2 :=
      mul_le_mul_of_nonneg_left hN2 (by positivity)
    linarith [hb1, hb2]
  have hstep2 : κ₁ ^ (Kp + 2) * Cc ^ 2
      ≤ κ₁ ^ (Kp + 2) * (δ ^ (5 * (Kp * (Kp + 3))) * N ^ 2) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hstep3 : κ₁ ^ (Kp + 2) * (δ ^ (5 * (Kp * (Kp + 3))) * N ^ 2)
      ≤ κ₁ ^ (Kp + 2) * ((γ ^ (Kp * (Kp + 3)) * Γ₀ ^ (Kp * (Kp + 3))) * N ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA (by positivity)) (by positivity)
  have hstep4 : κ₁ ^ (Kp + 2) * ((γ ^ (Kp * (Kp + 3)) * Γ₀ ^ (Kp * (Kp + 3))) * N ^ 2)
      = γ ^ (Kp * (Kp + 3)) * κ₁ ^ (Kp + 2) * N ^ 2 * Γ₀ ^ (Kp * (Kp + 3)) := by ring
  have hG : C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3))
      ≤ γ ^ (Kp * (Kp + 3)) * κ₁ ^ (Kp + 2) * N ^ 2 * Γ₀ ^ (Kp * (Kp + 3)) :=
    le_trans hCc2 (le_trans hstep2 (le_trans hstep3 (le_of_eq hstep4)))
  calc C_ch * C_ch ^ (Kp + 2) = C_ch ^ (Kp + 3) := by rw [← pow_succ']
    _ ≤ γ ^ (Kp * (Kp + 3)) * κ₁ ^ (Kp + 2) * N ^ 2 :=
        le_of_mul_le_mul_right hG (by positivity)

/-- **The bridge's length condition** `D ≤ (deg P)!·L`: the chapter's window is long compared
with the crux's. -/
lemma D_le_fac_mul_L {δ δ' γ Γ₀ C_ch N : ℝ} {Kp : ℕ} {κ₁ Cc : ℝ} {d : ℕ} {D L : ℕ}
    (hδ' : δ' = γ ^ Kp * κ₁ / C_ch)
    (hD : (D : ℝ) ≤ δ ^ (5 * Kp) * N / Cc)
    (hL : δ' * N / 2 ≤ (L : ℝ))
    (hγp : δ ^ (5 * Kp) / Γ₀ ^ Kp ≤ γ ^ Kp)
    (hCg3 : 2 * Γ₀ ^ Kp * C_ch ≤ (d.factorial : ℝ) * κ₁ * Cc)
    (hCc : 0 < C_ch) (hΓ₀ : 0 < Γ₀) (hκ₁ : 0 < κ₁) (hCc0 : 0 < Cc)
    (hN : 0 ≤ N) (hγ : 0 < γ) :
    D ≤ d.factorial * L := by
  have hγpΓ₀ : δ ^ (5 * Kp) ≤ γ ^ Kp * Γ₀ ^ Kp := (div_le_iff₀ (by positivity)).mp hγp
  have hfac : δ ^ (5 * Kp) * (2 * C_ch) ≤ (d.factorial : ℝ) * γ ^ Kp * κ₁ * Cc := by
    calc δ ^ (5 * Kp) * (2 * C_ch) ≤ (γ ^ Kp * Γ₀ ^ Kp) * (2 * C_ch) :=
          mul_le_mul_of_nonneg_right hγpΓ₀ (by positivity)
      _ = γ ^ Kp * (2 * Γ₀ ^ Kp * C_ch) := by ring
      _ ≤ γ ^ Kp * ((d.factorial : ℝ) * κ₁ * Cc) :=
          mul_le_mul_of_nonneg_left hCg3 (pow_nonneg (le_of_lt hγ) Kp)
      _ = (d.factorial : ℝ) * γ ^ Kp * κ₁ * Cc := by ring
  have hstep : δ ^ (5 * Kp) * N / Cc ≤ (d.factorial : ℝ) * (δ' * N / 2) := by
    have h1 : δ ^ (5 * Kp) * N / Cc
        = (δ ^ (5 * Kp) * (2 * C_ch)) * N / (2 * C_ch * Cc) := by
      field_simp
    have h2 : (δ ^ (5 * Kp) * (2 * C_ch)) * N / (2 * C_ch * Cc)
        ≤ ((d.factorial : ℝ) * γ ^ Kp * κ₁ * Cc) * N / (2 * C_ch * Cc) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hfac hN
    have h3 : ((d.factorial : ℝ) * γ ^ Kp * κ₁ * Cc) * N / (2 * C_ch * Cc)
        = (d.factorial : ℝ) * (δ' * N / 2) := by
      rw [hδ']; field_simp
    linarith [h1.le, h1.ge, h2, h3.le, h3.ge]
  have h4 : (D : ℝ) ≤ (d.factorial : ℝ) * (L : ℝ) := by
    calc (D : ℝ) ≤ δ ^ (5 * Kp) * N / Cc := hD
      _ ≤ (d.factorial : ℝ) * (δ' * N / 2) := hstep
      _ ≤ (d.factorial : ℝ) * (L : ℝ) := mul_le_mul_of_nonneg_left hL (by positivity)
  exact_mod_cast h4

/-! ## The wiring

We now prove the target from the chapter.  The proof follows the structure of
`Work.Peluse.ucontrol_of_concat_of_chapterWith`, with the chapter `PiecePetTwo` in place of
`Theorem37ChapterWith`; the extra content is the construction of the chapter's shift parameter
`δ'` (and of its derivative `L = dirLen P δ' N`) from the target's data. -/

theorem ucontrolPaper_of_piecePet (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (h : Work.Peluse.UControl.PiecePetTwo P) : Work.Peluse.PeluseUControlPaper P := by
  classical
  obtain ⟨s₀, hs₀2, hbody₁⟩ := h
  refine ⟨s₀, hs₀2, fun A' hA' => ?_⟩
  -- the direction-coefficient bridge (multiplicity `(deg P)!`)
  have hfac2 : 2 ≤ P.natDegree.factorial := by
    have h1 := Nat.factorial_le hd
    have h2 : Nat.factorial 2 = 2 := by decide
    omega
  obtain ⟨kap, hkap_pos, hkap_spec⟩ :=
    uNormPow_direction_bridge (s := s₀) hs₀2 P.natDegree.factorial hfac2
  -- the coefficients of `P`
  set CP : ℕ := ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).natAbs with hCPdef
  set κ₁ : ℕ := P.leadingCoeff.natAbs with hκ₁def
  have hκ₁1 : 1 ≤ κ₁ := by rw [hκ₁def]; exact one_le_leadingCoeff_natAbs hd
  have hκ₁pos : (0 : ℝ) < (κ₁ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hκ₁1)
  set A'' : ℝ := A' + (CP : ℝ) with hA''def
  have hA''ge : A' ≤ A'' := by rw [hA''def]; linarith
  have hA''1 : 1 ≤ A'' := le_trans hA' hA''ge
  have hA''pos : 0 < A'' := lt_of_lt_of_le one_pos hA''1
  set θ : ℝ := A' + (CP : ℝ) with hθdef
  have hθeq : θ = A'' := by rw [hθdef, hA''def]
  have hθ1 : 1 ≤ θ := hθeq ▸ hA''1
  have hθpos : 0 < θ := lt_of_lt_of_le one_pos hθ1
  set Γ₀ : ℝ := 3 * A' ^ 2 * θ ^ 2 with hΓ₀def
  have hΓ₀pos : 0 < Γ₀ := by rw [hΓ₀def]; positivity
  -- the chapter at the enlarged imbalance `A''`
  obtain ⟨Cp, hCp1, Kp, hKp1, hbody₂⟩ := hbody₁ A'' hA''1
  -- the chapter's smallness constant
  set C_ch : ℝ :=
    max 1 (max (A'' * Cp) (max θ (max ((P.natDegree.factorial : ℝ) * (κ₁ : ℝ)) 2)))
    with hC_chdef
  have hC_ch1 : 1 ≤ C_ch := by rw [hC_chdef]; exact le_max_left _ _
  have hC_chpos : 0 < C_ch := lt_of_lt_of_le one_pos hC_ch1
  have hC_ch_A''Cp : A'' * Cp ≤ C_ch := by
    rw [hC_chdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_ch_θ : θ ≤ C_ch := by
    rw [hC_chdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hC_ch_fac : (P.natDegree.factorial : ℝ) * (κ₁ : ℝ) ≤ C_ch := by
    rw [hC_chdef]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  -- the exponents of the target
  set K : ℕ := 5 * Kp with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; omega
  have hK4 : 4 * Kp ≤ K := by rw [hKdef]; omega
  set K₂ : ℕ := 5 * Kp + 3 * Kp * (Kp + 3) + 4 with hK₂def
  have hK₂1 : 1 ≤ K₂ := by rw [hK₂def]; omega
  have hK₂ge5 : 5 * Kp ≤ K₂ := by rw [hK₂def]; omega
  have hK₂ge2 : 5 * Kp * (Kp + 3) ≤ 2 * K₂ := by rw [hK₂def]; nlinarith [hKp1]
  have hK₂ge_d : K ≤ P.natDegree * K₂ := by rw [hKdef]; nlinarith [hK₂ge5, hd]
  -- the target's constant
  set C : ℕ := max 2 (max (Nat.ceil (2 * Γ₀ ^ Kp * C_ch / (κ₁ : ℝ)))
      (max (Nat.ceil (C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) * 2 ^ (Kp + 2) * A' ^ (Kp + 2)))
        (max (Nat.ceil (2 * C_ch * Γ₀ ^ Kp / ((P.natDegree.factorial : ℝ) * (κ₁ : ℝ))))
          (Nat.ceil (C_ch * A'' ^ (5 * Kp) * 3 ^ (2 * Kp) / kap))))) with hCdef
  have hC2 : 2 ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC1 : 1 ≤ C := by omega
  have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC1)
  have hCeil1 : (Nat.ceil (2 * Γ₀ ^ Kp * C_ch / (κ₁ : ℝ)) : ℝ) ≤ (C : ℝ) := by
    rw [hCdef]; simp only [Nat.cast_max, le_max_iff]
    exact Or.inr (Or.inl le_rfl)
  have hCeil2 : (Nat.ceil (C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) * 2 ^ (Kp + 2)
      * A' ^ (Kp + 2)) : ℝ) ≤ (C : ℝ) := by
    rw [hCdef]; simp only [Nat.cast_max, le_max_iff]
    exact Or.inr (Or.inr (Or.inl le_rfl))
  have hCeil3 : (Nat.ceil (2 * C_ch * Γ₀ ^ Kp
      / ((P.natDegree.factorial : ℝ) * (κ₁ : ℝ))) : ℝ) ≤ (C : ℝ) := by
    rw [hCdef]; simp only [Nat.cast_max, le_max_iff]
    exact Or.inr (Or.inr (Or.inr (Or.inl le_rfl)))
  have hCeil4 : (Nat.ceil (C_ch * A'' ^ (5 * Kp) * 3 ^ (2 * Kp) / kap) : ℝ) ≤ (C : ℝ) := by
    rw [hCdef]; simp only [Nat.cast_max, le_max_iff]
    exact Or.inr (Or.inr (Or.inr (Or.inr le_rfl)))
  have hCg1 : 2 * Γ₀ ^ Kp * C_ch / (κ₁ : ℝ) ≤ (C : ℝ) := le_trans (Nat.le_ceil _) hCeil1
  have hCg2 : C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) * 2 ^ (Kp + 2) * A' ^ (Kp + 2)
      ≤ (C : ℝ) := le_trans (Nat.le_ceil _) hCeil2
  have hCg3 : 2 * C_ch * Γ₀ ^ Kp / ((P.natDegree.factorial : ℝ) * (κ₁ : ℝ)) ≤ (C : ℝ) :=
    le_trans (Nat.le_ceil _) hCeil3
  have hCg4 : C_ch * A'' ^ (5 * Kp) * 3 ^ (2 * Kp) / kap ≤ (C : ℝ) :=
    le_trans (Nat.le_ceil _) hCeil4
  refine ⟨C, K, K₂, hC1, hK1, hK₂1, ?_⟩
  intro N N₀ f₀ f₁ f₂ δ hd' hN hN₀ hsc1 hsc2 hδ0 hδ1 hnd hsup0 hsup1 hsup2 hb0 hb1 hb2 hΛ
  -- basic facts about the data
  set MA : ℕ := dSup P N₀ N with hMAdef
  have hMA1 : 1 ≤ MA := le_trans hN₀ (le_dSup P N₀ N)
  have hN₀MA : (N₀ : ℝ) ≤ (MA : ℝ) := by exact_mod_cast le_dSup P N₀ N
  have hMA1' : (1 : ℝ) ≤ (MA : ℝ) := by exact_mod_cast hMA1
  have hMApos : (0 : ℝ) < (MA : ℝ) := lt_of_lt_of_le one_pos hMA1'
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN₀1 : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
  have hN₀pos : (0 : ℝ) < (N₀ : ℝ) := by linarith
  have hA'pos : (0 : ℝ) < A' := lt_of_lt_of_le one_pos hA'
  set F : ℤ → ℂ := dualFn N P f₀ f₁ with hFdef
  have hsupF : SupportIn F MA := by
    rw [hFdef, hMAdef]; exact dualFn_supportIn_dSup P f₀ f₁ hsup0
  have hbF : ∀ x : ℤ, ‖F x‖ ≤ 1 := by
    rw [hFdef]; exact norm_dualFn_le_one (by omega) P f₀ f₁ hb0 hb1
  have hsupF' : SupportIn (fun x : ℤ => star (F x)) MA := fun x hx => by
    simp [hsupF x hx]
  have hbF' : ∀ x : ℤ, ‖(fun x : ℤ => star (F x)) x‖ ≤ 1 := fun x => by
    rw [norm_star]; exact hbF x
  have hsup0' : SupportIn f₀ MA := hsup0.mono (le_dSup P N₀ N)
  have hsup1' : SupportIn f₁ MA := hsup1.mono (le_dSup P N₀ N)
  -- Peluse's Corollary 3.8 (Cauchy–Schwarz against the dual function)
  have hcs := Pairing.cs_dualFn_step (N₀ := N₀) (N := N) (by omega : 0 < N₀) (by omega : 0 < N)
    P f₀ f₁ f₂ hsup0 hsup1 hb2 (le_of_lt hδ0) hΛ
  rw [← hMAdef] at hcs
  rw [← hFdef] at hcs
  -- the correlation strength of the dual pair
  set γ : ℝ := δ ^ 2 * (N₀ : ℝ) ^ 2 / ((2 * (MA : ℝ) + 1) * (MA : ℝ)) with hγdef
  have hscal : LambdaZ MA N P f₀ f₁ (fun x : ℤ => star (F x))
      = ((N₀ : ℂ) * ((MA : ℂ))⁻¹) * LambdaZ N₀ N P f₀ f₁ (fun x : ℤ => star (F x)) :=
    LambdaZ_scale P N₀ MA N (by simp [Nat.cast_eq_zero]; omega) f₀ f₁ _
  have hγΛ : γ ≤ ‖LambdaZ MA N P f₀ f₁ (fun x : ℤ => star (F x))‖ := by
    have h1 : γ = ((N₀ : ℝ) / (MA : ℝ)) * (δ ^ 2 * (N₀ : ℝ) / (2 * (MA : ℝ) + 1)) := by
      rw [hγdef]; field_simp
    have h2 : (0 : ℝ) ≤ (N₀ : ℝ) / (MA : ℝ) := by positivity
    have h3 := mul_le_mul_of_nonneg_left hcs h2
    have h4 : ‖(N₀ : ℂ) * ((MA : ℂ))⁻¹‖ = (N₀ : ℝ) / (MA : ℝ) := by
      rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast, div_eq_mul_inv]
    rw [hscal, norm_mul, h4]
    exact le_trans (le_of_eq h1) h3
  -- bounds on `MA`
  have hMAub : (MA : ℝ) ≤ θ * (N : ℝ) ^ P.natDegree := by
    have hp : ((polySup P N : ℕ) : ℝ) ≤ (CP : ℝ) * (N : ℝ) ^ P.natDegree := by
      have h' := polySup_le_sum_coeff_mul_pow P hN
      rw [hCPdef]
      exact_mod_cast h'
    have hMAeq : (MA : ℝ) = (N₀ : ℝ) + ((polySup P N : ℕ) : ℝ) := by
      rw [hMAdef, dSup]; push_cast; ring
    rw [hMAeq, hθdef]
    linarith [hsc1, hp]
  have hκ₁le : (κ₁ : ℝ) * (N : ℝ) ^ P.natDegree ≤ (MA : ℝ) := by
    have h' := lc_natAbs_mul_pow_le_polySup P N
    rw [hκ₁def]
    have h2 : P.leadingCoeff.natAbs * N ^ P.natDegree ≤ MA :=
      le_trans h' (Nat.le_add_left _ _)
    exact_mod_cast h2
  -- the `γ`-sandwich
  have hγb := gamma_bounds (d := P.natDegree) hδ0 hδ1 hN hN₀ hMA1 hN₀MA hA' hθpos hMAub hsc2
  have hγpos : 0 < γ := hγb.1
  have hγleδ : γ ≤ δ := hγb.2.1
  have hγle1 : γ ≤ 1 := le_trans hγleδ hδ1
  have hγΓ₀ : δ ^ 5 / Γ₀ ≤ γ := by
    have h' := hγb.2.2
    rwa [← hΓ₀def] at h'
  -- the shift parameter of the chapter, and the length it produces
  set δ' : ℝ := γ ^ Kp * (κ₁ : ℝ) / C_ch with hδ'def
  set L : ℕ := UControl.dirLen P δ' N with hLdef
  have hLsym : UControl.dirLen P δ' N = L := hLdef.symm
  have hLfloor : (L : ℝ) = ((⌊δ' * (N : ℝ) ^ P.natDegree⌋ : ℤ) : ℝ) := by
    rw [hLdef, UControl.dirLen]
    have h' := Int.toNat_of_nonneg
      (Int.floor_nonneg.mpr (show (0 : ℝ) ≤ δ' * (N : ℝ) ^ P.natDegree by positivity))
    exact_mod_cast h'
  have hLle : (L : ℝ) ≤ δ' * (N : ℝ) ^ P.natDegree := by
    rw [hLfloor]; exact Int.floor_le _
  -- the arithmetic inputs coming from the target's scale relation
  have hδinv : (1 : ℝ) ≤ δ ^ (5 * Kp) * (δ⁻¹) ^ K₂ := by
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa using pow_le_pow_of_le_one (le_of_lt hδ0) hδ1 hK₂ge5
  have hCN : (C : ℝ) ≤ δ ^ (5 * Kp) * (N : ℝ) := by
    have h1 : δ ^ (5 * Kp) * ((C : ℝ) * (δ⁻¹) ^ K₂) ≤ δ ^ (5 * Kp) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hnd (by positivity)
    have h2 : (C : ℝ) * 1 ≤ (C : ℝ) * (δ ^ (5 * Kp) * (δ⁻¹) ^ K₂) :=
      mul_le_mul_of_nonneg_left hδinv (by positivity)
    have h3 : δ ^ (5 * Kp) * ((C : ℝ) * (δ⁻¹) ^ K₂)
        = (C : ℝ) * (δ ^ (5 * Kp) * (δ⁻¹) ^ K₂) := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hκ₁C : 2 * Γ₀ ^ Kp * C_ch ≤ (κ₁ : ℝ) * (C : ℝ) := by
    have h := hCg1
    rw [div_le_iff₀ hκ₁pos] at h
    linarith [h]
  have hγp : δ ^ (5 * Kp) / Γ₀ ^ Kp ≤ γ ^ Kp := by
    have h := pow_le_pow_left₀ (by positivity) hγΓ₀ Kp
    have h2 : (δ ^ 5 / Γ₀) ^ Kp = δ ^ (5 * Kp) / Γ₀ ^ Kp := by rw [div_pow, ← pow_mul]
    rwa [h2] at h
  have hfac1 : (1 : ℝ) ≤ (P.natDegree.factorial : ℝ) := by
    have h2 : 1 ≤ P.natDegree.factorial := by
      have h5 := Nat.factorial_le hd
      have h6 : Nat.factorial 2 = 2 := by decide
      omega
    exact_mod_cast h2
  -- the shift parameter is in `(0,1]`
  have hδ'pos : 0 < δ' := by rw [hδ'def]; positivity
  have hδ'le1 : δ' ≤ 1 := by
    rw [hδ'def, div_le_one hC_chpos]
    have h1 : γ ^ Kp ≤ 1 := pow_le_one₀ (le_of_lt hγpos) hγle1
    have h2 : (κ₁ : ℝ) ≤ (P.natDegree.factorial : ℝ) * (κ₁ : ℝ) := by
      nlinarith [hfac1, hκ₁pos]
    nlinarith [h1, h2, hC_ch_fac, hκ₁pos]
  -- the chapter's window is non-degenerate: `2 ≤ δ'N`
  have hδ'N2 : 2 ≤ δ' * (N : ℝ) :=
    two_le_delta'_mul_N hδ'def hγp hCN hκ₁C hC_chpos hκ₁pos hΓ₀pos hNpos hγpos
  have hδ'N : 1 ≤ δ' * (N : ℝ) := by linarith [hδ'N2]
  have hδ'Nfloor : 1 ≤ (⌊δ' * (N : ℝ)⌋).toNat := by
    have h1 : (1 : ℤ) ≤ ⌊δ' * (N : ℝ)⌋ :=
      Int.le_floor.mpr (by push_cast; exact hδ'N)
    have h2 := Int.toNat_le_toNat h1
    simpa using h2
  -- the length `L` is `≥ 1` and `≥ δ'N^d/2`
  have hx2 : 2 ≤ δ' * (N : ℝ) ^ P.natDegree := by
    have hNd : (N : ℝ) ^ P.natDegree = (N : ℝ) ^ (P.natDegree - 1) * (N : ℝ) := by
      rw [← pow_succ]; congr 1; omega
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ δ' * (N : ℝ) * (N : ℝ) ^ (P.natDegree - 1) :=
          mul_le_mul hδ'N2 (one_le_pow₀ hN1) (by norm_num) (by positivity)
      _ = δ' * (N : ℝ) ^ P.natDegree := by rw [hNd]; ring
  have hL1 : 1 ≤ L := by
    rw [hLdef, UControl.dirLen]
    have h1 : (1 : ℤ) ≤ ⌊δ' * (N : ℝ) ^ P.natDegree⌋ :=
      Int.le_floor.mpr (by push_cast; exact le_trans (by norm_num) hx2)
    have h2 := Int.toNat_le_toNat h1
    simpa using h2
  have hLlow : δ' * (N : ℝ) ^ P.natDegree / 2 ≤ (L : ℝ) := by
    rw [hLfloor]
    have := Int.lt_floor_add_one (δ' * (N : ℝ) ^ P.natDegree)
    linarith
  -- the target's shift length
  set D : ℕ := (⌊δ ^ K * (N : ℝ) ^ P.natDegree / (C : ℝ)⌋).toNat with hDdef
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    exact crux_window_ge_one hδ0 hδ1 (by omega) hN hC1 hnd hK₂ge_d
  have hDle : (D : ℝ) ≤ δ ^ K * (N : ℝ) ^ P.natDegree / (C : ℝ) := by
    have hx0 : (0 : ℝ) ≤ δ ^ K * (N : ℝ) ^ P.natDegree / (C : ℝ) := by positivity
    have h1 : (D : ℝ) = ((⌊δ ^ K * (N : ℝ) ^ P.natDegree / (C : ℝ)⌋ : ℤ) : ℝ) := by
      rw [hDdef]
      have h' := Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx0)
      exact_mod_cast h'
    rw [h1]; exact Int.floor_le _
  -- the chapter's smallness gauge
  have hC_ch_L : C_ch * (L : ℝ) ≤ γ ^ Kp * (MA : ℝ) := by
    calc C_ch * (L : ℝ) ≤ C_ch * (δ' * (N : ℝ) ^ P.natDegree) :=
          mul_le_mul_of_nonneg_left hLle (le_of_lt hC_chpos)
      _ = γ ^ Kp * ((κ₁ : ℝ) * (N : ℝ) ^ P.natDegree) := by
            rw [hδ'def]; field_simp
      _ ≤ γ ^ Kp * (MA : ℝ) := mul_le_mul_of_nonneg_left hκ₁le (by positivity)
  -- the chapter's non-degeneracy `C_ch ≤ (γ δ')^{Kp} (δ' N)^2`
  have hC_ch_le : C_ch ≤ (γ * δ') ^ Kp * (δ' * (N : ℝ)) ^ 2 := by
    have hN2 : (C : ℝ) ^ 2 * (δ⁻¹) ^ (2 * K₂) ≤ (N : ℝ) ^ 2 := by
      have h1 : ((C : ℝ) * (δ⁻¹) ^ K₂) ^ 2 ≤ (N : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hnd 2
      have h2 : ((C : ℝ) * (δ⁻¹) ^ K₂) ^ 2 = (C : ℝ) ^ 2 * (δ⁻¹) ^ (2 * K₂) := by
        rw [mul_pow, ← pow_mul, show K₂ * 2 = 2 * K₂ by ring]
      rwa [h2] at h1
    have hδK : (1 : ℝ) ≤ δ ^ (5 * (Kp * (Kp + 3))) * (δ⁻¹) ^ (2 * K₂) := by
      have h3 : 5 * (Kp * (Kp + 3)) ≤ 2 * K₂ := by nlinarith [hK₂ge2, hKp1]
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      simpa using pow_le_pow_of_le_one (le_of_lt hδ0) hδ1 h3
    have hCc2 : C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) ≤ (κ₁ : ℝ) ^ (Kp + 2) * (C : ℝ) ^ 2 := by
      have hZ0 : (0 : ℝ) ≤ C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) := by positivity
      have hX : (1 : ℝ) ≤ 2 ^ (Kp + 2) * A' ^ (Kp + 2) := by
        have h1 : (1 : ℝ) ≤ 2 ^ (Kp + 2) := one_le_pow₀ (by norm_num)
        have h2 : (1 : ℝ) ≤ A' ^ (Kp + 2) := one_le_pow₀ hA'
        nlinarith [h1, h2]
      have hCsq : (C : ℝ) ≤ (C : ℝ) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
        nlinarith
      have hZm : C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3))
          ≤ C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) * (2 ^ (Kp + 2) * A' ^ (Kp + 2)) := by
        nth_rewrite 1 [← mul_one (C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)))]
        exact mul_le_mul_of_nonneg_left hX hZ0
      have hassoc : C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) * (2 ^ (Kp + 2) * A' ^ (Kp + 2))
          = C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) * 2 ^ (Kp + 2) * A' ^ (Kp + 2) := by ring
      rw [hassoc] at hZm
      have h1 : C_ch ^ (Kp + 3) * Γ₀ ^ (Kp * (Kp + 3)) ≤ (C : ℝ) ^ 2 := by
        linarith [hCg2, hCsq, hZm]
      have h4 : (1 : ℝ) ≤ (κ₁ : ℝ) ^ (Kp + 2) := one_le_pow₀ (by exact_mod_cast hκ₁1)
      nlinarith [h1, h4, hZ0, pow_nonneg (by positivity : (0 : ℝ) ≤ (κ₁ : ℝ)) (Kp + 2)]
    exact C_ch_le_gamma_delta hδ'def hγpos hγΓ₀ hN2 hδK hCc2 hC_chpos hΓ₀pos
      (le_of_lt hκ₁pos) hδ0
  -- the chapter's window is long enough for the direction bridge
  have hDL : D ≤ P.natDegree.factorial * L := by
    have hD' : (D : ℝ) ≤ δ ^ (5 * Kp) * (N : ℝ) ^ P.natDegree / (C : ℝ) := by
      calc (D : ℝ) ≤ δ ^ K * (N : ℝ) ^ P.natDegree / (C : ℝ) := hDle
        _ = δ ^ (5 * Kp) * (N : ℝ) ^ P.natDegree / (C : ℝ) := by rw [hKdef]
    have hCg3' : 2 * Γ₀ ^ Kp * C_ch ≤ (P.natDegree.factorial : ℝ) * (κ₁ : ℝ) * (C : ℝ) := by
      have h := hCg3
      rw [div_le_iff₀ (by positivity)] at h
      linarith only [h]
    exact D_le_fac_mul_L hδ'def hD' hLlow hγp hCg3' hC_chpos hΓ₀pos hκ₁pos hCpos
      (le_of_lt (pow_pos hNpos P.natDegree)) hγpos
  -- the chapter's hypotheses
  have hsc2'' : (N : ℝ) ^ P.natDegree ≤ A'' * γ⁻¹ * (MA : ℝ) := by
    have h1 : δ⁻¹ ≤ γ⁻¹ := (inv_le_inv₀ hδ0 hγpos).mpr hγleδ
    have h2 : A' * δ⁻¹ ≤ A'' * γ⁻¹ :=
      mul_le_mul hA''ge h1 (by positivity) (le_of_lt hA''pos)
    have h3 : A' * δ⁻¹ * (N₀ : ℝ) ≤ A'' * γ⁻¹ * (MA : ℝ) :=
      mul_le_mul h2 hN₀MA (le_of_lt hN₀pos) (by positivity)
    linarith [hsc2, h3]
  have hMAub' : (MA : ℝ) ≤ A'' * (N : ℝ) ^ P.natDegree := by
    rw [hθeq] at hMAub; exact hMAub
  have hLleMA : (L : ℝ) ≤ (MA : ℝ) / C_ch := by
    have h1 : γ ^ Kp * (MA : ℝ) / C_ch ≤ (MA : ℝ) / C_ch := by
      rw [div_le_div_iff₀ hC_chpos hC_chpos]
      have h2 : γ ^ Kp * (MA : ℝ) ≤ 1 * (MA : ℝ) :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ (le_of_lt hγpos) hγle1 (n := Kp)) (le_of_lt hMApos)
      simpa using mul_le_mul_of_nonneg_right h2 (le_of_lt hC_chpos)
    have h2 : C_ch * (L : ℝ) ≤ C_ch * ((MA : ℝ) / C_ch) := by
      calc C_ch * (L : ℝ) ≤ γ ^ Kp * (MA : ℝ) := hC_ch_L
        _ = C_ch * (γ ^ Kp * (MA : ℝ) / C_ch) := by field_simp
        _ ≤ C_ch * ((MA : ℝ) / C_ch) := mul_le_mul_of_nonneg_left h1 (le_of_lt hC_chpos)
    exact le_of_mul_le_mul_left h2 hC_chpos
  have hfacL : (P.natDegree.factorial : ℝ) * (κ₁ : ℝ) * (L : ℝ) ≤ (MA : ℝ) := by
    have h2 : (P.natDegree.factorial : ℝ) * (κ₁ : ℝ) * (L : ℝ)
        ≤ C_ch * ((MA : ℝ) / C_ch) := by
      have h3 := mul_le_mul_of_nonneg_right hC_ch_fac (show (0 : ℝ) ≤ (L : ℝ) by positivity)
      calc (P.natDegree.factorial : ℝ) * (κ₁ : ℝ) * (L : ℝ) ≤ C_ch * (L : ℝ) := by linarith [h3]
        _ ≤ C_ch * ((MA : ℝ) / C_ch) := mul_le_mul_of_nonneg_left hLleMA (le_of_lt hC_chpos)
    calc (P.natDegree.factorial : ℝ) * (κ₁ : ℝ) * (L : ℝ) ≤ C_ch * ((MA : ℝ) / C_ch) := h2
      _ = (MA : ℝ) := by field_simp
  have hdirfit : (UControl.dirCoeff P) * (L : ℤ) ≤ (MA : ℤ) := by
    rw [UControl.dirCoeff]
    by_cases hlc : P.leadingCoeff < 0
    · have h2 : (0 : ℤ) < (P.natDegree.factorial : ℤ) := by
        have h3 : 1 ≤ P.natDegree.factorial := by
          have h4 := Nat.factorial_le hd
          have h5 : Nat.factorial 2 = 2 := by decide
          omega
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h3)
      have h3 : (0 : ℤ) ≤ (L : ℤ) := by exact_mod_cast (Nat.zero_le L)
      have h1 : (P.natDegree.factorial : ℤ) * P.leadingCoeff * (L : ℤ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos h2.le (le_of_lt hlc)) h3
      have h4 : (0 : ℤ) ≤ (MA : ℤ) := by exact_mod_cast (Nat.zero_le MA)
      linarith
    · have hlcpos : 0 < P.leadingCoeff := by omega
      have hκ₁eq : (κ₁ : ℤ) = P.leadingCoeff := by
        rw [hκ₁def]
        exact Int.natAbs_of_nonneg (le_of_lt hlcpos)
      rw [← hκ₁eq]
      exact_mod_cast hfacL
  -- the chapter's hypotheses
  have hsc2'' : (N : ℝ) ^ P.natDegree ≤ A'' * γ⁻¹ * (MA : ℝ) := by
    have h1 : δ⁻¹ ≤ γ⁻¹ := (inv_le_inv₀ hδ0 hγpos).mpr hγleδ
    have h2 : A' * δ⁻¹ ≤ A'' * γ⁻¹ :=
      mul_le_mul hA''ge h1 (by positivity) (le_of_lt hA''pos)
    have h3 : A' * δ⁻¹ * (N₀ : ℝ) ≤ A'' * γ⁻¹ * (MA : ℝ) :=
      mul_le_mul h2 hN₀MA (le_of_lt hN₀pos) (by positivity)
    linarith [hsc2, h3]
  have hMAub' : (MA : ℝ) ≤ A'' * (N : ℝ) ^ P.natDegree := by
    rw [hθeq] at hMAub; exact hMAub
  have hHyp : UControl.Hyp P A'' C_ch Kp N MA f₀ f₁ (fun x : ℤ => star (F x)) γ δ' := by
    refine ⟨hd, hN, hMA1, hγpos, hγle1, hδ'pos, hδ'le1, hδ'Nfloor, hMAub', hsc2'',
      hC_ch1, hKp1, ?_, ?_, hsup0', hsup1', hsupF', hb0, hb1, hbF', hγΛ⟩
    · rw [hLsym]; exact hC_ch_L
    · exact hC_ch_le
  -- Peluse's Propositions 3.4 + 3.6 at the chosen parameters
  have hchap := hbody₂ C_ch hC_ch1 Kp le_rfl N MA f₀ f₁ (fun x : ℤ => star (F x)) γ δ'
    hHyp hC_ch_A''Cp hdirfit
  have hCp_le_C_ch : Cp ≤ C_ch := by
    have h1 : Cp ≤ A'' * Cp := by nlinarith only [hCp1, hA''1]
    linarith only [hC_ch_A''Cp, h1]
  have hC_concl : γ ^ (2 * Kp) ≤ Cp * A'' ^ Kp
      * uNormPow s₀ (arithIcc (UControl.dirCoeff P) L) (symIcc MA) F := by
    rw [UControl.Concl] at hchap
    rw [hLsym, uNormPow_star] at hchap
    have hγp_pos : 0 < γ ^ Kp := pow_pos hγpos Kp
    have h1 : γ ^ Kp * γ ^ Kp ≤ γ ^ Kp * (Cp * A'' ^ Kp * γ⁻¹ ^ Kp
        * uNormPow s₀ (arithIcc (UControl.dirCoeff P) L) (symIcc MA) F) :=
      mul_le_mul_of_nonneg_left hchap (le_of_lt hγp_pos)
    have h2 : γ ^ Kp * (Cp * A'' ^ Kp * γ⁻¹ ^ Kp
        * uNormPow s₀ (arithIcc (UControl.dirCoeff P) L) (symIcc MA) F)
        = Cp * A'' ^ Kp * uNormPow s₀ (arithIcc (UControl.dirCoeff P) L) (symIcc MA) F := by
      rw [inv_pow]
      field_simp
    have h3 : γ ^ Kp * γ ^ Kp = γ ^ (2 * Kp) := by rw [← pow_add]; ring_nf
    rw [h3, h2] at h1
    exact h1
  -- the direction-coefficient bridge
  have hbridge := hkap_spec P.leadingCoeff (leadingCoeff_ne_zero_of_two_le_natDegree hd)
    L D MA F hL1 hD1 hDL hbF hsupF
  have hbridge' : kap * uNormPow s₀ (arithIcc (UControl.dirCoeff P) L) (symIcc MA) F
      ≤ uNormPow s₀ (arithIcc P.leadingCoeff D) (symIcc MA) F := by
    rw [UControl.dirCoeff]
    exact hbridge
  have hC_concl' : γ ^ (2 * Kp) ≤ C_ch * A'' ^ Kp
      * uNormPow s₀ (arithIcc (UControl.dirCoeff P) L) (symIcc MA) F :=
    le_trans hC_concl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCp_le_C_ch (pow_nonneg (le_of_lt hA''pos) Kp))
      (by rw [uNormPow, boxNormPow]; exact norm_nonneg _))
  have hU : kap * γ ^ (2 * Kp) / (C_ch * A'' ^ Kp)
      ≤ uNormPow s₀ (arithIcc P.leadingCoeff D) (symIcc MA) F := by
    have h2 : γ ^ (2 * Kp) / (C_ch * A'' ^ Kp)
        ≤ uNormPow s₀ (arithIcc (UControl.dirCoeff P) L) (symIcc MA) F := by
      rw [div_le_iff₀ (by positivity)]
      linarith [hC_concl']
    have h1 : kap * γ ^ (2 * Kp) / (C_ch * A'' ^ Kp)
        ≤ kap * uNormPow s₀ (arithIcc (UControl.dirCoeff P) L) (symIcc MA) F := by
      calc kap * γ ^ (2 * Kp) / (C_ch * A'' ^ Kp)
          = kap * (γ ^ (2 * Kp) / (C_ch * A'' ^ Kp)) := by ring
        _ ≤ kap * uNormPow s₀ (arithIcc (UControl.dirCoeff P) L) (symIcc MA) F :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt hkap_pos)
    linarith [h1, hbridge']
  -- the final exponent matching (the proved `arith_final`)
  have hfin := UControl.arith_final (d := P.natDegree) (K := K) (K₀ := Kp) (δ := δ)
    (κ := kap) (C₀ := C_ch) (C := (C : ℝ)) (A' := A') (A'' := A'') (N := N) (N₀ := N₀) (MA := MA)
    hδ0 hδ1 hN hN₀ hMA1 hA' hA''1 hsc2 hMAub' hKp1 hK4 hC_chpos hkap_pos hCpos hCg4
  rw [← hγdef] at hfin
  have hmain : δ ^ (2 * K) ≤ (C : ℝ) * A' ^ K
      * uNormPow s₀ (arithIcc P.leadingCoeff D) (symIcc MA) F := by
    have h1 : δ ^ (2 * K) ≤ uNormPow s₀ (arithIcc P.leadingCoeff D) (symIcc MA) F
        * ((C : ℝ) * A' ^ K) := by
      have h2 : δ ^ (2 * K) / ((C : ℝ) * A' ^ K)
          ≤ uNormPow s₀ (arithIcc P.leadingCoeff D) (symIcc MA) F := le_trans hfin hU
      rwa [div_le_iff₀ (by positivity)] at h2
    linarith [h1]
  have hpow : δ ^ K = δ ^ (2 * K) * (δ⁻¹) ^ K := by
    rw [inv_pow, show (2 : ℕ) * K = K + K by ring, pow_add, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero K (ne_of_gt hδ0)), mul_one]
  rw [hpow]
  have hgoal : (C : ℝ) * A' ^ K * (δ⁻¹) ^ K
        * uNormPow s₀ (arithIcc P.leadingCoeff D) (symIcc MA) F
      = ((C : ℝ) * A' ^ K * uNormPow s₀ (arithIcc P.leadingCoeff D) (symIcc MA) F)
        * (δ⁻¹) ^ K := by ring
  rw [hgoal]
  exact mul_le_mul_of_nonneg_right hmain (by positivity)

end

end Work.Peluse.PaperRoute
