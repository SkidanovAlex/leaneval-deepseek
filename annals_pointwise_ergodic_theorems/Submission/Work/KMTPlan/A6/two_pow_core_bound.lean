import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.KMTPlan.A6

open Work.Analysis.EndVar

/-! ## Elementary prerequisites

These are the (purely real/arithmetic) facts the uniform core bound rests on.  The main one is
`two_pow_absorb_arith`: the doubly exponential `2^{2^{2ρu}}` is more than enough to absorb the
polynomial linear part and the exponential factor `2·Qc·2^{ρu}`. -/

/-- `x - 1 ≤ ⌊x⌋` (as a natural), for `x ≥ 1`. -/
lemma floor_toNat_ge_sub_one {x : ℝ} (hx : 1 ≤ x) : x - 1 ≤ ((⌊x⌋).toNat : ℝ) := by
  have h2 : ((⌊x⌋).toNat : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg (by
    have : (1:ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; exact hx)
    omega)
  have h3 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have h4 : ((⌊x⌋).toNat : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast h2
  linarith

/-- `(n+1)^2 ≤ 2^n` for `n ≥ 6`. -/
lemma nat_sq_succ_le_two_pow : ∀ n : ℕ, 6 ≤ n → (n+1)^2 ≤ 2^n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m _ ih =>
    have h1 : (m+2)^2 ≤ 2 * (m+1)^2 := by nlinarith
    calc (m+1+1)^2 = (m+2)^2 := by ring
      _ ≤ 2 * (m+1)^2 := h1
      _ ≤ 2 * 2^m := by linarith
      _ = 2^(m+1) := by ring

/-- `β^2 ≤ 2^β` for real `β ≥ 6`. -/
lemma rpow_sq_le_two_rpow {β : ℝ} (hβ : 6 ≤ β) : β^2 ≤ (2:ℝ)^β := by
  have hβ0 : 0 ≤ β := by linarith
  have hn6 : 6 ≤ ⌊β⌋₊ := Nat.le_floor (by exact_mod_cast hβ)
  have hβle : β ≤ ((⌊β⌋₊ : ℕ) : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one β)
  have hsq : β^2 ≤ (((⌊β⌋₊ : ℕ) : ℝ) + 1)^2 := by nlinarith
  have hnat : (⌊β⌋₊ + 1)^2 ≤ 2^(⌊β⌋₊) := nat_sq_succ_le_two_pow ⌊β⌋₊ hn6
  have hnatR : (((⌊β⌋₊ : ℕ) : ℝ) + 1)^2 ≤ ((2:ℕ)^(⌊β⌋₊) : ℝ) := by
    exact_mod_cast hnat
  have hle2 : ((⌊β⌋₊ : ℕ) : ℝ) ≤ β := Nat.floor_le hβ0
  calc β^2 ≤ (((⌊β⌋₊ : ℕ) : ℝ) + 1)^2 := hsq
    _ ≤ ((2:ℕ)^(⌊β⌋₊) : ℝ) := hnatR
    _ = (2:ℝ)^(((⌊β⌋₊ : ℕ) : ℝ)) := by rw [Real.rpow_natCast]; simp
    _ ≤ (2:ℝ)^β := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle2

/-- `2·Qc ≤ 2^{β/2}` as soon as `β ≥ 8·Qc + 8` (and `Qc > 0`). -/
lemma two_Qc_le_two_rpow_half {β Qc : ℝ} (hQc : 0 < Qc) (h : 8*Qc + 8 ≤ β) :
    2*Qc ≤ (2:ℝ)^(β/2) := by
  have h2Qc : 0 < 2*Qc := by linarith
  rw [Real.le_rpow_iff_log_le h2Qc (by norm_num : (0:ℝ) < 2)]
  have hβ0 : 0 ≤ β := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (2:ℝ)/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rcases le_or_gt (2*Qc) 1 with h1 | h1
  · have hlog : Real.log (2*Qc) ≤ 0 := Real.log_nonpos h2Qc.le h1
    have : 0 ≤ β/2 * Real.log 2 := mul_nonneg (by linarith) hlog2pos.le
    linarith
  · have hlog : Real.log (2*Qc) ≤ 2*Qc - 1 := Real.log_le_sub_one_of_pos h2Qc
    have hβ3 : 2*Qc - 1 ≤ β/3 := by linarith
    have hstep : β/3 ≤ β/2 * Real.log 2 := by
      have h1 : β/2 * (2/3) ≤ β/2 * Real.log 2 :=
        mul_le_mul_of_nonneg_left hlog2.le (by linarith)
      have h2 : β/2 * (2/3) = β/3 := by ring
      linarith
    linarith

/-- **The crude absorbing bound behind the uniform core bound.**  For `ρ > 0` and `Qc > 0` there
is `B ≥ 0` with `u + 2·Qc·2^{ρu} ≤ 2^{2^{2ρu} − 1} + B` for every `u : ℕ`.

The proof takes `A := max 6 (max (8·Qc + 8) (2ρ)⁻¹)` and
`B := max 1 (A/(2ρ) + 2·Qc·2^{A/2})`, and splits on `β := 2ρu < A`:

* if `β < A` then `u < A/(2ρ)` and `2^{ρu} < 2^{A/2}`, so the left-hand side is `< B ≤` the
  right-hand side plus `B`;
* if `β ≥ A` then `u = β/(2ρ) ≤ β·β = β²` (as `(2ρ)⁻¹ ≤ β`), while `β² ≤ 2^β`
  (`rpow_sq_le_two_rpow`) and `2·Qc ≤ 2^{β/2}` (`two_Qc_le_two_rpow_half`), so
  `u + 2Qc·2^{β/2} ≤ β² + 2^β ≤ 2^{β+1} ≤ 2^{2^β − 1}`
  (the last step because `β + 2 ≤ 2^β` for `β ≥ 6`). -/
theorem two_pow_absorb_arith (ρ Qc : ℝ) (hρ : 0 < ρ) (hQc : 0 < Qc) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℕ,
      (u : ℝ) + 2 * Qc * (2 : ℝ) ^ (ρ * (u : ℝ))
        ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (2 * (ρ * (u : ℝ))) - 1) + B := by
  set A : ℝ := max 6 (max (8*Qc + 8) ((2*ρ)⁻¹)) with hA
  have hA6 : 6 ≤ A := le_max_left _ _
  have hAinv : (2*ρ)⁻¹ ≤ A :=
    le_trans (le_max_right (8*Qc + 8) ((2*ρ)⁻¹)) (le_max_right 6 _)
  have hAQc : 8*Qc + 8 ≤ A :=
    le_trans (le_max_left (8*Qc + 8) ((2*ρ)⁻¹)) (le_max_right 6 _)
  have hρ0 : 0 < 2*ρ := by linarith
  refine ⟨max 1 (A/(2*ρ) + 2*Qc*(2:ℝ)^(A/2)), ?_, ?_⟩
  · exact le_trans zero_le_one (le_max_left (1:ℝ) _)
  intro u
  set β : ℝ := 2*(ρ*(u:ℝ)) with hβdef
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hu_eq : (u:ℝ) = β/(2*ρ) := by
    rw [eq_div_iff (ne_of_gt hρ0), hβdef]; ring
  rcases lt_or_ge β A with hlt | hge
  · have hu : (u:ℝ) < A/(2*ρ) := by
      rw [hu_eq]; exact div_lt_div_of_pos_right hlt hρ0
    have hexp : ρ*(u:ℝ) < A/2 := by
      rw [hβdef] at hlt; linarith
    have hpow : (2:ℝ)^(ρ*(u:ℝ)) ≤ (2:ℝ)^(A/2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp.le
    have h1 : (u:ℝ) + 2*Qc*(2:ℝ)^(ρ*(u:ℝ)) ≤ A/(2*ρ) + 2*Qc*(2:ℝ)^(A/2) := by
      have := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ 2*Qc)
      linarith
    have h2 : 0 ≤ (2:ℝ)^((2:ℝ)^β - 1) :=
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) ((2:ℝ)^β - 1)).le
    have h3 : A/(2*ρ) + 2*Qc*(2:ℝ)^(A/2)
        ≤ max 1 (A/(2*ρ) + 2*Qc*(2:ℝ)^(A/2)) := le_max_right _ _
    linarith
  · have hβA6 : 6 ≤ β := le_trans hA6 hge
    have hβinv : (2*ρ)⁻¹ ≤ β := le_trans hAinv hge
    have hβQc : 8*Qc + 8 ≤ β := le_trans hAQc hge
    have hu_le : (u:ℝ) ≤ β^2 := by
      rw [hu_eq, div_eq_mul_inv]
      calc β * (2*ρ)⁻¹ ≤ β * β := mul_le_mul_of_nonneg_left hβinv hβ0
        _ = β^2 := by ring
    have hsq : β^2 ≤ (2:ℝ)^β := rpow_sq_le_two_rpow hβA6
    have hQc2 : 2*Qc ≤ (2:ℝ)^(β/2) := two_Qc_le_two_rpow_half hQc hβQc
    have hexp : ρ*(u:ℝ) = β/2 := by rw [hβdef]; ring
    have hprod : 2*Qc*(2:ℝ)^(ρ*(u:ℝ)) ≤ (2:ℝ)^β := by
      rw [hexp]
      calc 2*Qc*(2:ℝ)^(β/2) ≤ (2:ℝ)^(β/2) * (2:ℝ)^(β/2) :=
            mul_le_mul_of_nonneg_right hQc2
              (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (β/2)).le
        _ = (2:ℝ)^(β/2 + β/2) := (Real.rpow_add (by norm_num) _ _).symm
        _ = (2:ℝ)^β := by congr 1; ring
    have hfinal : (u:ℝ) + 2*Qc*(2:ℝ)^(ρ*(u:ℝ)) ≤ (2:ℝ)^((2:ℝ)^β - 1) := by
      have hsum : (u:ℝ) + 2*Qc*(2:ℝ)^(ρ*(u:ℝ)) ≤ (2:ℝ)^(β+1) := by
        have h1 : (2:ℝ)^(β+1) = (2:ℝ)^β + (2:ℝ)^β := by
          rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]; ring
        rw [h1]; linarith
      have h2 : β + 1 ≤ (2:ℝ)^β - 1 := by
        have h3 : β + 2 ≤ (2:ℝ)^β := by nlinarith
        linarith
      exact le_trans hsum (Real.rpow_le_rpow_of_exponent_le (by norm_num) h2)
    have hB0 : 0 ≤ max 1 (A/(2*ρ) + 2*Qc*(2:ℝ)^(A/2)) :=
      le_trans zero_le_one (le_max_left (1:ℝ) _)
    linarith

/-- **The uniform bound on the composite exponent of the crude route.**  On the core (main regime
`k₁ + 2·uScale ρ (max k₁ k₂) ≤ Log N`, and `u` bounding `l₁, l₂, k₁, k₂` from above), the exponent

  `k₁ − Log N + 2·Qc·2^{ρl₁}`

is bounded by a constant depending only on `ρ` and `Qc` (in fact by `Qc²/2 + 2`): writing
`s = 2^{ρu} ≥ 1` and `t = 2^{ρl₁} ≤ s`, the hypothesis gives `Log N ≥ k₁ + 2⌊2^{2ρu}⌋ ≥ k₁ + 2s² − 2`,
so the exponent is `≤ 2Qc·t − 2s² + 2 ≤ 2Qc·s − 2s² + 2 ≤ Qc²/2 + 2`.  This is what makes the
composite constant of `mdlVanishingCase` uniform in `(l₁,l₂,k₁,k₂)`. -/
theorem two_pow_core_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (Qc : ℝ) (hQc : 0 < Qc) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N k₁ k₂ l₁ u : ℕ),
      l₁ ≤ u → k₁ ≤ u → k₂ ≤ u →
      Work.KMTAreas.A7.splitCut ρ u < N →
      k₁ + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) ≤ (Work.Analysis.EndVar.logN N).toNat →
      (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)
          + 2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) ≤ C := by
  obtain ⟨B, hB0, hB⟩ := two_pow_absorb_arith ρ Qc hρ hQc
  refine ⟨(2:ℝ) ^ (B + 1), Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _, ?_⟩
  intro N k₁ k₂ l₁ u hl₁ hk₁ hk₂ hsplit hmain
  set L : ℕ := Nat.log 2 (max N 2) with hLdef
  have hlogNR : (Work.Analysis.EndVar.logN N : ℝ) = (L : ℝ) := by
    have h1 : Work.Analysis.EndVar.logN N = (L : ℤ) := by
      simp only [Work.Analysis.EndVar.logN, hLdef]
    rw [h1]; simp
  have hsplit_le : Work.KMTAreas.A7.splitCut ρ u ≤ max N 2 :=
    le_trans (le_of_lt hsplit) (le_max_left _ _)
  have hn_le : 2 ^ (Work.Analysis.EndVar.scaleCount 1 ρ u) ≤ L := by
    rw [hLdef]
    have hcut_eq : Work.KMTAreas.A7.splitCut ρ u
        = 2 ^ (2 ^ Work.Analysis.EndVar.scaleCount 1 ρ u) := rfl
    rw [hcut_eq] at hsplit_le
    exact Nat.le_log_of_pow_le (by norm_num) hsplit_le
  have hnR : ((2:ℕ)^(Work.Analysis.EndVar.scaleCount 1 ρ u) : ℝ) ≤ (L:ℝ) := by
    exact_mod_cast hn_le
  have hnR' : (2:ℝ)^((Work.Analysis.EndVar.scaleCount 1 ρ u : ℕ) : ℝ) ≤ (L:ℝ) := by
    have : (2:ℝ)^((Work.Analysis.EndVar.scaleCount 1 ρ u : ℕ) : ℝ)
        = ((2:ℕ)^(Work.Analysis.EndVar.scaleCount 1 ρ u) : ℝ) := by
      rw [Real.rpow_natCast, Nat.cast_ofNat]
    rw [this]; exact hnR
  have hx1 : (1:ℝ) ≤ (2:ℝ)^(2*(ρ*(u:ℝ))) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hfloor : (2:ℝ)^(2*(ρ*(u:ℝ))) - 1 ≤ (Work.Analysis.EndVar.scaleCount 1 ρ u : ℝ) := by
    unfold Work.Analysis.EndVar.scaleCount
    simp only [Nat.cast_one, one_mul]
    rw [show (2:ℝ)^(2 * ρ * (u:ℝ)) = (2:ℝ)^(2*(ρ*(u:ℝ))) by congr 1; ring]
    exact floor_toNat_ge_sub_one hx1
  have hLbig : (2:ℝ)^((2:ℝ)^(2*(ρ*(u:ℝ))) - 1) ≤ (L:ℝ) :=
    calc (2:ℝ)^((2:ℝ)^(2*(ρ*(u:ℝ))) - 1)
        ≤ (2:ℝ)^((Work.Analysis.EndVar.scaleCount 1 ρ u : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
      _ ≤ (L:ℝ) := hnR'
  have hk1u : (k₁:ℝ) ≤ (u:ℝ) := by exact_mod_cast hk₁
  have hl1u : (2:ℝ)^(ρ*(l₁:ℝ)) ≤ (2:ℝ)^(ρ*(u:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (l₁:ℝ) ≤ (u:ℝ) := by exact_mod_cast hl₁
    nlinarith [hρ.le]
  have hE : (k₁:ℝ) - (Work.Analysis.EndVar.logN N : ℝ) + 2*Qc*(2:ℝ)^(ρ*(l₁:ℝ))
      ≤ (u:ℝ) + 2*Qc*(2:ℝ)^(ρ*(u:ℝ)) - (2:ℝ)^((2:ℝ)^(2*(ρ*(u:ℝ))) - 1) := by
    rw [hlogNR]
    have := mul_le_mul_of_nonneg_left hl1u (by positivity : (0:ℝ) ≤ 2*Qc)
    linarith
  have hB' := hB u
  have hEB : (k₁:ℝ) - (Work.Analysis.EndVar.logN N : ℝ) + 2*Qc*(2:ℝ)^(ρ*(l₁:ℝ)) ≤ B := by
    linarith
  calc (2:ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)
          + 2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
      ≤ (2:ℝ)^B := Real.rpow_le_rpow_of_exponent_le (by norm_num) hEB
    _ ≤ (2:ℝ)^(B+1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end Work.KMTPlan.A6
