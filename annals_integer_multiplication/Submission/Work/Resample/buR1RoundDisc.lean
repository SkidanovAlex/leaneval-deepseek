import Mathlib
import Submission.Work.Resample.buQWstepKit

/-!
# `Work.Resample.buR1RoundDisc`

Disc bounds for one Neumann round of the `B̃` word (paper Lemma 4.11 and its use in the
Neumann summation): the fold of the column table over the input vector, divided by `2^p`,
stays in a disc of radius `B/2 + 34 * egM p α + 4`, and the signed accumulation into the
running Neumann sum stays in the disc of radius `B2 + B/2 + 34 * egM p α + 5`.

The numerics: a fold entry is bounded by `buRowS * B`, where the row sum is at most
`2^p/2 + 8 * egM p α` (hypothesis `hrow`), and the truncated division by `2^p` costs less
than `√2` per coordinate pair.  Note `buRoundL` is definitionally the object
`buTdivV p (buPFold Wt s m v (2*m))` of the statement (`buRoundL_eq_pfold`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## the numeric core -/

/-- `(B:ℝ)/2 - 1 ≤ ⌊B/2⌋`. -/
theorem buRD_half_cast (B : ℕ) : (B : ℝ) / 2 - 1 ≤ ((B / 2 : ℕ) : ℝ) := by
  have h1 : B < 2 * (B / 2) + 2 := by
    have := Nat.div_add_mod B 2
    have h2 : B % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  have h2 : (B : ℝ) < 2 * (((B / 2 : ℕ) : ℝ) + 1) := by exact_mod_cast h1
  linarith

/-- The arithmetic core of the disc bound of one round: a fold entry of norm at most
`S * B` with row sum `S ≤ 2^p/2 + 8m` and input radius `B ≤ 2^(p+2)`, truncated at `2^p`,
lands in the disc of radius `⌊B/2⌋ + 34m + 4`. -/
theorem buRD_num {p m B : ℕ} {S : ℝ}
    (hS : S ≤ (2 : ℝ) ^ p / 2 + 8 * (m : ℝ)) (hB : B ≤ 2 ^ (p + 2)) :
    S * (B : ℝ) / (2 : ℝ) ^ p + Real.sqrt 2 ≤ (((B / 2 + 34 * m + 4 : ℕ)) : ℝ) := by
  have hBnn : (0 : ℝ) ≤ (B : ℝ) := by positivity
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hB2 : (B : ℝ) / (2 : ℝ) ^ p ≤ 4 := by
    have h2 : (B : ℝ) ≤ (2 : ℝ) ^ (p + 2) := by
      have h3 : ((2 : ℕ) ^ (p + 2) : ℝ) = (2 : ℝ) ^ (p + 2) := by push_cast; ring
      calc (B : ℝ) ≤ ((2 : ℕ) ^ (p + 2) : ℝ) := by exact_mod_cast hB
        _ = (2 : ℝ) ^ (p + 2) := h3
    have h4 : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
    calc (B : ℝ) / (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (p + 2) / (2 : ℝ) ^ p :=
          div_le_div_of_nonneg_right h2 (le_of_lt h4)
      _ = 4 := by
          rw [show (2 : ℝ) ^ (p + 2) = (2 : ℝ) ^ p * 4 by rw [pow_add]; norm_num]
          field_simp
  have hrow2 : S * (B : ℝ) / (2 : ℝ) ^ p ≤ (B : ℝ) / 2 + 32 * (m : ℝ) := by
    have h5 : S * (B : ℝ) / (2 : ℝ) ^ p
        ≤ ((2 : ℝ) ^ p / 2 + 8 * (m : ℝ)) * (B : ℝ) / (2 : ℝ) ^ p :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hS hBnn) (by positivity)
    have h6 : ((2 : ℝ) ^ p / 2 + 8 * (m : ℝ)) * (B : ℝ) / (2 : ℝ) ^ p
        = (B : ℝ) / 2 + 8 * (m : ℝ) * ((B : ℝ) / (2 : ℝ) ^ p) := by
      field_simp
      try ring
    have h7 : 8 * (m : ℝ) * ((B : ℝ) / (2 : ℝ) ^ p) ≤ 32 * (m : ℝ) := by
      have h8 : 8 * (m : ℝ) * ((B : ℝ) / (2 : ℝ) ^ p) ≤ 8 * (m : ℝ) * 4 :=
        mul_le_mul_of_nonneg_left hB2 (by positivity)
      linarith
    calc S * (B : ℝ) / (2 : ℝ) ^ p
        ≤ ((2 : ℝ) ^ p / 2 + 8 * (m : ℝ)) * (B : ℝ) / (2 : ℝ) ^ p := h5
      _ = (B : ℝ) / 2 + 8 * (m : ℝ) * ((B : ℝ) / (2 : ℝ) ^ p) := h6
      _ ≤ (B : ℝ) / 2 + 32 * (m : ℝ) := by linarith
  have h8 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h9 := buRD_half_cast B
  have h10 : (((B / 2 + 34 * m + 4 : ℕ)) : ℝ) = ((B / 2 : ℕ) : ℝ) + 34 * (m : ℝ) + 4 := by
    push_cast; ring
  rw [h10]
  linarith

/-! ## the list-level disc bound of one round -/

/-- The round vector has length `s`. -/
theorem buRD_len (Wt : ℤ → ℤ → ℤ) (p s m : ℕ) {v : List (ℤ × ℤ)} (hv : v.length = s) :
    (buTdivV p (buPFold Wt s m v (2 * m))).length = s := by
  rw [buTdivV_length, buPFold_length Wt s m v hv (2 * m) (by rw [buColsN_length])]

/-- Every entry of the round vector lies in the disc of radius `⌊B/2⌋ + 34m + 4`. -/
theorem buRD_gz (Wt : ℤ → ℤ → ℤ) (p s m B : ℕ) {v : List (ℤ × ℤ)}
    (hv : v.length = s) (hBv : ∀ z ∈ v, ‖gz z‖ ≤ (B : ℝ))
    (hrow : ∀ ℓ : ℤ, buRowS Wt m ℓ (2 * m) ≤ (2 : ℝ) ^ p / 2 + 8 * (m : ℝ))
    (hB : B ≤ 2 ^ (p + 2)) :
    ∀ ℓ < s, ‖gz ((buRoundL Wt p s m v).getD ℓ (0, 0))‖ ≤ (((B / 2 + 34 * m + 4 : ℕ)) : ℝ) := by
  intro ℓ hℓ
  have h1 := buRoundL_gz_le Wt p s m B v hv hBv ℓ hℓ
  exact le_trans h1 (buRD_num (p := p) (m := m) (B := B)
    (S := buRowS Wt m (ℓ : ℤ) (2 * m)) (hrow ℓ) hB)

/-- The round vector lies in the disc of radius `⌊B/2⌋ + 34m + 4`. -/
theorem buRD_buInV (Wt : ℤ → ℤ → ℤ) (p s m B : ℕ) {v : List (ℤ × ℤ)}
    (hv : v.length = s) (hBv : ∀ z ∈ v, ‖gz z‖ ≤ (B : ℝ))
    (hrow : ∀ ℓ : ℤ, buRowS Wt m ℓ (2 * m) ≤ (2 : ℝ) ^ p / 2 + 8 * (m : ℝ))
    (hB : B ≤ 2 ^ (p + 2)) :
    buInV (B / 2 + 34 * m + 4) (buRoundL Wt p s m v) := by
  rw [buInV_iff]
  intro z hz
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_iff_getElem.mp hz
  have hlen : (buRoundL Wt p s m v).length = s := by
    rw [buRoundL_eq_pfold]
    exact buRD_len Wt p s m hv
  have hl : ℓ < s := by omega
  rw [← List.getD_eq_getElem _ _ hℓ]
  exact buRD_gz Wt p s m B hv hBv hrow hB ℓ hl

/-! ## the target -/

theorem buR1RoundDisc
    (p α s t : ℕ) (hs : 2 ≤ s) (hp : 100 ≤ p) (B B2 : ℕ)
    (hB : B ≤ 2 ^ (p + 2)) (hB2 : B2 ≤ 2 ^ (p + 2))
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
    (v acc : List (ℤ × ℤ)) (hv : v.length = s) (ha : acc.length = s)
    (hbv : buInV B v) (hbacc : buInV B2 acc) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))).length = s ∧
    buInV (B / 2 + 34 * egM p α + 4)
      (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))) ∧
    (buAddV acc (buSMulV σ (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))))).length
      = s ∧
    buInV (B2 + B / 2 + 34 * egM p α + 5)
      (buAddV acc (buSMulV σ (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))))) := by
  have hlen : (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))).length = s :=
    buRD_len (buWt p α s t) p s (egM p α) hv
  have hdisc : buInV (B / 2 + 34 * egM p α + 4)
      (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))) := by
    rw [← buRoundL_eq_pfold (buWt p α s t) p s (egM p α) v]
    exact buRD_buInV (buWt p α s t) p s (egM p α) B hv
      (fun z hz => (buInV_iff B v).mp hbv z hz)
      (fun ℓ => by rw [buRowS_full]; exact hrow ℓ) hB
  have hlen2 : (buAddV acc (buSMulV σ
      (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))))).length = s := by
    rw [buAddV_length, ha, buSMulV, List.length_map, hlen, Nat.min_self]
  have hdisc2 : buInV (B2 + B / 2 + 34 * egM p α + 5)
      (buAddV acc (buSMulV σ
        (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))))) := by
    have h1 : buInV (B / 2 + 34 * egM p α + 4)
        (buSMulV σ (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α)))) :=
      buInV_buSMulV hσ hdisc
    have h2 : buInV (B2 + (B / 2 + 34 * egM p α + 4))
        (buAddV acc (buSMulV σ
          (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))))) :=
      buInV_buAddV hbacc h1
    exact buQT_buInV_mono (by omega) h2
  exact ⟨hlen, hdisc, hlen2, hdisc2⟩

end Work.Resample
