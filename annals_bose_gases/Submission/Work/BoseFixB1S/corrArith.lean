import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.RegimeAux
import Submission.Work.BoseFixB1S.CorrAux.crossTermBound
import Submission.Work.BoseFixB1S.CorrAux.prodTermBound
import Submission.Work.BoseFixB1S.fsXpLogSmall
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.corrArith`

The elementary arithmetic domination behind the per-box correlation estimate.

At FS's parameter choice the box side and the small-box side are the monomials

  `ℓ = sideAt μ A = A · (μA³)^{-163/323}`,  `d = (paramsAt μ A).d = (μA³)^{6/323}`,

so with `t = μA³` and `L = 1 + (ℓd)⁻¹ + |log d| = 1 + A⁻¹t^{157/323} + (6/323)|log t|`

  `C₀ ℓ⁻² C₁ L³ (ℓd)⁻³ ≤ 8 C₀C₁ A⁻⁵ t^{797/323} (1+|log t|)³`,
  `2 √(C₀ℓ⁻²) √(C₁ L³ (ℓd)⁻³ (2π)³ Cχ) ≤ 2 √(8C₀C₁Cχ(2π)³) A^{-5/2} t^{797/646} (1+|log t|)^{3/2}`,

while the right-hand side is `bValue/(4ℓ²) = (1/64) A⁻² t^{326/323}`.  Each of the
two bounds is a factor `(1/128)` of `ℓ⁻²` times a factor which is at most `1` once
`t^{471/323}(1+|log t|)³` — respectively `t^{145/646}(1+|log t|)^{3/2}` — is
small, and that is exactly what `fsXpLogSmall` provides (a positive power of `t`
beats every power of `log`).

The two displayed estimates are proved in the sibling modules
`Submission.Work.BoseFixB1S.CorrAux.prodTermBound` and
`...crossTermBound`; this file chooses `ε₀` (a minimum of the two logarithmic
thresholds, of `1`, and of `A^{323/157}`, which makes `(ℓd)⁻¹ ≤ 1`) and adds the
two halves.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixB1S

open Work.BoseBox

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **Smallness of `K · (μa³)^{c/323} · (1+|log t|)^M`**: a positive power of `t`
beats every power of `|log t|`, uniformly in the prefactor `K`.  This is
`fsXpLogSmall` with the constant `K⁻¹`, multiplied through by `K`. -/
lemma fsXp_mul_log_le_one {K c M : ℝ} (hK : 0 < K) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      K * fsXp t c * (1 + |Real.log t|) ^ M ≤ 1 := by
  obtain ⟨ε, hε, h⟩ := fsXpLogSmall (c := c) (M := M) (K := K⁻¹) (inv_pos.mpr hK) hc hM
  refine ⟨ε, hε, fun t ht htle => ?_⟩
  have h1 := h t ht htle
  have h2 : K * (fsXp t c * (1 + |Real.log t|) ^ M) ≤ K * K⁻¹ :=
    mul_le_mul_of_nonneg_left h1 hK.le
  rw [mul_inv_cancel₀ hK.ne'] at h2
  calc K * fsXp t c * (1 + |Real.log t|) ^ M
      = K * (fsXp t c * (1 + |Real.log t|) ^ M) := by ring
    _ ≤ 1 := h2

theorem corrArith {C₀ C₁ Cχ A : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (hχ : 0 ≤ Cχ) (hA : 0 < A) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * A ^ 3 ≤ ε₀ →
      (let ℓ : ℝ := Work.BoseBox.sideAt μ A
       let d : ℝ := (Work.BoseBox.paramsAt μ A).d
       let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
       ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
          + 2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
        ≤ Work.BoseBox.bValue / (4 * ℓ ^ 2)) := by
  -- the two large constants of the logarithmic thresholds; the `+1` makes them
  -- strictly positive even when `C₀C₁` (resp. `C₀C₁Cχ`) vanishes
  set KA : ℝ := (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) + 1) * A ^ (-(3 : ℝ)) with hKAdef
  set KB : ℝ := (128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) + 1)
      * A ^ (-(1 / 2 : ℝ)) with hKBdef
  have hKApos : 0 < KA := by
    rw [hKAdef]
    have hA3 : 0 < A ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hA _
    have hC : 0 ≤ C₀ * C₁ := mul_nonneg h₀ h₁
    have hp : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have hX : 0 ≤ 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) := by nlinarith [hp, hC]
    exact mul_pos (by linarith) hA3
  have hKBpos : 0 < KB := by
    rw [hKBdef]
    have hA3 : 0 < A ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hA _
    have hp : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have hs : 0 ≤ Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) := Real.sqrt_nonneg _
    have hX : 0 ≤ 128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) := by
      nlinarith [hp, hs]
    exact mul_pos (by linarith) hA3
  obtain ⟨δA, hδApos, hδA⟩ :=
    fsXp_mul_log_le_one (K := KA) (c := 471) (M := ((3 : ℕ) : ℝ)) hKApos (by norm_num) (by norm_num)
  obtain ⟨δB, hδBpos, hδB⟩ :=
    fsXp_mul_log_le_one (K := KB) (c := 145 / 2) (M := 3 / 2) hKBpos (by norm_num) (by norm_num)
  refine ⟨min 1 (min (A ^ (323 / 157 : ℝ)) (min δA δB)), ?_, ?_⟩
  · exact lt_min one_pos (lt_min (Real.rpow_pos_of_pos hA _) (lt_min hδApos hδBpos))
  · intro μ hμ hμle
    set t : ℝ := μ * A ^ 3 with ht_def
    have ht : 0 < t := by rw [ht_def]; positivity
    have htm : t ≤ min (A ^ (323 / 157 : ℝ)) (min δA δB) := hμle.trans (min_le_right _ _)
    have htA : t ≤ A ^ (323 / 157 : ℝ) := htm.trans (min_le_left _ _)
    have htδA : t ≤ δA := (htm.trans (min_le_right _ _)).trans (min_le_left _ _)
    have htδB : t ≤ δB := (htm.trans (min_le_right _ _)).trans (min_le_right _ _)
    -- `(ℓd)⁻¹ = A⁻¹t^{157/323} ≤ 1` for `t ≤ A^{323/157}`
    have hu : A⁻¹ * fsXp t 157 ≤ 1 := by
      have h1 : fsXp t 157 ≤ A := by
        have h2 := Real.rpow_le_rpow ht.le htA (by norm_num : (0 : ℝ) ≤ (157 : ℝ) / 323)
        have h3 : (A ^ (323 / 157 : ℝ)) ^ ((157 : ℝ) / 323) = A := by
          rw [← Real.rpow_mul hA.le]; norm_num
        rw [h3] at h2
        simpa [fsXp] using h2
      calc A⁻¹ * fsXp t 157 ≤ A⁻¹ * A := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1 := by rw [inv_mul_cancel₀ hA.ne']
    -- the closed forms of the parameters
    let ℓ : ℝ := Work.BoseBox.sideAt μ A
    let d : ℝ := (Work.BoseBox.paramsAt μ A).d
    let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
    have hℓ : ℓ = A * fsXp t (-163) := by
      show Work.BoseBox.sideAt μ A = A * fsXp t (-163)
      rw [ht_def]
      exact Work.BoseFixB1.sideAt_eq_fsXp hA hμ
    have hd : d = fsXp t 6 := by
      show (Work.BoseBox.paramsAt μ A).d = fsXp t 6
      rw [ht_def]
      exact Work.BoseFixB1.d_eq_fsXp μ A
    have hℓpos : 0 < ℓ := by rw [hℓ]; exact mul_pos hA (fsXp_pos ht)
    -- the two estimates of the summands
    have hX : C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
        ≤ 8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3 := by
      have h := Work.BoseFixB1S.CorrAux.prodTermBound (C₀ := C₀) (C₁ := C₁) (A := A) (t := t)
        h₀ h₁ hA ht hu
      dsimp only at h
      simp only [← hℓ, ← hd] at h
      exact h
    have hY : 2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
        Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
        ≤ 2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
            fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ) := by
      have h := Work.BoseFixB1S.CorrAux.crossTermBound (C₀ := C₀) (C₁ := C₁) (Cχ := Cχ) (A := A) (t := t)
        h₀ h₁ hχ hA ht hu
      dsimp only at h
      simp only [← hℓ, ← hd] at h
      exact h
    -- `ℓ⁻² = A⁻² fsXp t 326`
    have hℓinv : (ℓ⁻¹) ^ 2 = A ^ (-(2 : ℝ)) * fsXp t 326 := by
      have h1 : ℓ⁻¹ = A⁻¹ * fsXp t 163 := by
        rw [hℓ, mul_inv, fsXp_inv ht, neg_neg]
      rw [h1, mul_pow]
      congr 1
      · rw [inv_pow, ← Real.rpow_natCast A 2, ← Real.rpow_neg hA.le]
        simp only [Nat.cast_ofNat]
      · rw [fsXp_pow ht.le]; norm_num
    -- the two logarithmic thresholds
    have hKA : 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ)) *
        fsXp t 471 * (1 + |Real.log t|) ^ 3 ≤ 1 := by
      have h := hδA t ht htδA
      rw [hKAdef] at h
      rw [Real.rpow_natCast] at h
      have hA3 : 0 ≤ A ^ (-(3 : ℝ)) := Real.rpow_nonneg hA.le _
      have hle : 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ))
          ≤ (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) + 1) * A ^ (-(3 : ℝ)) := by
        rw [add_mul, one_mul]
        linarith
      calc 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ)) *
              fsXp t 471 * (1 + |Real.log t|) ^ 3
          = (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ))) *
              (fsXp t 471 * (1 + |Real.log t|) ^ 3) := by ring
        _ ≤ ((128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) + 1) * A ^ (-(3 : ℝ))) *
              (fsXp t 471 * (1 + |Real.log t|) ^ 3) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg (fsXp_nonneg ht.le) (by positivity))
        _ = ((128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) + 1) * A ^ (-(3 : ℝ))) *
              fsXp t 471 * (1 + |Real.log t|) ^ 3 := by ring
        _ ≤ 1 := h
    have hKB : 128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
        A ^ (-(1 / 2 : ℝ)) * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ) ≤ 1 := by
      have h := hδB t ht htδB
      rw [hKBdef] at h
      have hA3 : 0 ≤ A ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hA.le _
      have hle : 128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
            A ^ (-(1 / 2 : ℝ))
          ≤ (128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) + 1) *
            A ^ (-(1 / 2 : ℝ)) := by
        rw [add_mul, one_mul]
        linarith
      calc 128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
              A ^ (-(1 / 2 : ℝ)) * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)
          = (128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
              A ^ (-(1 / 2 : ℝ))) * (fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) := by ring
        _ ≤ ((128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) + 1) *
              A ^ (-(1 / 2 : ℝ))) * (fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg (fsXp_nonneg ht.le) (by positivity))
        _ = ((128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) + 1) *
              A ^ (-(1 / 2 : ℝ))) * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ) := by ring
        _ ≤ 1 := h
    -- the two identities factoring out `(ℓ⁻¹)²`
    have hXid : ((2 * Real.pi) ^ 3)⁻¹ *
          (8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3)
        = (1 / 128) * (ℓ⁻¹) ^ 2 *
          (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ)) *
            fsXp t 471 * (1 + |Real.log t|) ^ 3) := by
      rw [show (-(5 : ℝ)) = (-(2 : ℝ)) + (-(3 : ℝ)) by norm_num, Real.rpow_add hA]
      rw [show (797 : ℝ) = 326 + 471 by norm_num, ← fsXp_mul ht]
      rw [hℓinv]
      ring
    have hYid : ((2 * Real.pi) ^ 3)⁻¹ *
          (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
            fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ))
        = (1 / 128) * (ℓ⁻¹) ^ 2 *
          (128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
            A ^ (-(1 / 2 : ℝ)) * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) := by
      rw [show (-(5 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-(2 : ℝ)) by norm_num, Real.rpow_add hA]
      rw [show (797 / 2 : ℝ) = 145 / 2 + 326 by norm_num, ← fsXp_mul ht]
      rw [hℓinv]
      ring
    -- each half is at most `(1/128) ℓ⁻²`
    have hXA : ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹)
        ≤ (1 / 128) * (ℓ⁻¹) ^ 2 := by
      calc ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹)
          ≤ ((2 * Real.pi) ^ 3)⁻¹ *
              (8 * (C₀ * C₁) * A ^ (-(5 : ℝ)) * fsXp t 797 * (1 + |Real.log t|) ^ 3) :=
              mul_le_mul_of_nonneg_left hX (by positivity)
        _ = (1 / 128) * (ℓ⁻¹) ^ 2 *
              (128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (C₀ * C₁)) * A ^ (-(3 : ℝ)) *
                fsXp t 471 * (1 + |Real.log t|) ^ 3) := hXid
        _ ≤ (1 / 128) * (ℓ⁻¹) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hKA (mul_nonneg (by norm_num) (sq_nonneg _))
        _ = (1 / 128) * (ℓ⁻¹) ^ 2 := by ring
    have hYA : ((2 * Real.pi) ^ 3)⁻¹ *
          (2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
        ≤ (1 / 128) * (ℓ⁻¹) ^ 2 := by
      calc ((2 * Real.pi) ^ 3)⁻¹ *
            (2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
              Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
          ≤ ((2 * Real.pi) ^ 3)⁻¹ *
              (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
                fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hY (by positivity)
        _ = (1 / 128) * (ℓ⁻¹) ^ 2 *
              (128 * (((2 * Real.pi) ^ 3)⁻¹) * (2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)) *
                A ^ (-(1 / 2 : ℝ)) * fsXp t (145 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) := hYid
        _ ≤ (1 / 128) * (ℓ⁻¹) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hKB (mul_nonneg (by norm_num) (sq_nonneg _))
        _ = (1 / 128) * (ℓ⁻¹) ^ 2 := by ring
    have hb : Work.BoseBox.bValue / (4 * ℓ ^ 2) = (1 / 64) * (ℓ⁻¹) ^ 2 := by
      rw [Work.BoseBox.bValue, inv_pow]
      field_simp
      ring
    show ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
          + 2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
        ≤ Work.BoseBox.bValue / (4 * ℓ ^ 2)
    rw [hb]
    have hsplit : ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
          + 2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ))
        = ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * (ℓ⁻¹) ^ 2 * C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹)
          + ((2 * Real.pi) ^ 3)⁻¹ * (2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)) := by ring
    rw [hsplit]
    linarith [hXA, hYA]

end Work.BoseFixB1S
