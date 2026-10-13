import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SlotT2.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elementary helpers for the `A · D_z f` flat row

The canonical-weight algebra (`Work.FTS.TransportS.SlotT2.canonW q = w² sin(2θ)^{-q}`), weighted
AM–GM, the per-term three-factor bound, and the `(0,0)`-splitting of a double `range`-sum.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem rowDz_sin2_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The defining equation of the canonical weight. -/
theorem rowDz_canonW_eq (q z θ : ℝ) :
    canonW q z θ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := rfl

/-- Multiplying a canonical weight by a power of `sin(2θ)` shifts the exponent. -/
theorem rowDz_canonW_mul_sigma {q t z θ : ℝ} (hσ : 0 < Real.sin (2 * θ)) :
    canonW q z θ * (Real.sin (2 * θ)) ^ t = canonW (q - t) z θ := by
  rw [rowDz_canonW_eq, rowDz_canonW_eq, mul_assoc, ← Real.rpow_add hσ]
  ring_nf

/-- The canonical weight determines its exponent. -/
theorem rowDz_canonW_eq_of {ρ : ℝ → ℝ → ℝ} {q q₀ : ℝ} (hρ : ρ = canonW q)
    (hρ' : ρ = canonW q₀) : q = q₀ := by
  have h1 : canonW q 1 (Real.pi / 8) = canonW q₀ 1 (Real.pi / 8) := by rw [← hρ, hρ']
  rw [rowDz_canonW_eq, rowDz_canonW_eq] at h1
  have hw : (Work.Spaces.w 1) ^ 2 = 16 := by rw [Work.Spaces.w]; norm_num
  have hs : Real.sin (2 * (Real.pi / 8)) = Real.sin (Real.pi / 4) := by ring_nf
  rw [hw, hs] at h1
  have hspos : 0 < Real.sin (Real.pi / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hslt : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 / 2), h2]
  have h2 : Real.sin (Real.pi / 4) ^ (-q) = Real.sin (Real.pi / 4) ^ (-q₀) := by
    nlinarith [h1]
  have hlog := congrArg Real.log h2
  rw [Real.log_rpow hspos, Real.log_rpow hspos] at hlog
  have hne : Real.log (Real.sin (Real.pi / 4)) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hspos (ne_of_lt hslt)
  have h3 : (q₀ - q) * Real.log (Real.sin (Real.pi / 4)) = 0 := by linarith [hlog]
  have h4 : q₀ - q = 0 := (mul_eq_zero.mp h3).resolve_right hne
  linarith [h4]

/-- Weighted AM–GM. -/
theorem rowDz_canonW_abs_mul_le {e z θ : ℝ} (hσ : 0 ≤ Real.sin (2 * θ)) (Y Z : ℝ) :
    canonW e z θ * |Y| * |Z| ≤ canonW e z θ * Y ^ 2 + canonW e z θ * Z ^ 2 := by
  have hc : 0 ≤ canonW e z θ := by
    rw [rowDz_canonW_eq]; exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσ _)
  set s := Real.sqrt (canonW e z θ) with hs
  have hs2 : s ^ 2 = canonW e z θ := Real.sq_sqrt hc
  have h : 2 * (s * |Y|) * (s * |Z|) ≤ (s * |Y|) ^ 2 + (s * |Z|) ^ 2 := by
    nlinarith [sq_nonneg (s * |Y| - s * |Z|)]
  have e1 : 2 * (s * |Y|) * (s * |Z|) = 2 * (canonW e z θ * |Y| * |Z|) := by
    rw [← hs2]; ring
  have e2 : (s * |Y|) ^ 2 + (s * |Z|) ^ 2 = canonW e z θ * Y ^ 2 + canonW e z θ * Z ^ 2 := by
    rw [← hs2, mul_pow, mul_pow, sq_abs, sq_abs]
  have hnn : 0 ≤ canonW e z θ * Y ^ 2 + canonW e z θ * Z ^ 2 :=
    add_nonneg (mul_nonneg hc (sq_nonneg _)) (mul_nonneg hc (sq_nonneg _))
  linarith [h, e1, e2, hnn]

/-- **The per-term three-factor bound**: a coefficient slot whose weighted absolute value is at
most `M·canonW e`, paired against two datum slots whose `canonW e`-weighted squares are dominated
by `A₁` and `A₂`. -/
theorem rowDz_term_le {α q e M : ℝ} {X Y Z A₁ A₂ : ℝ → ℝ → ℝ} (hM : 0 ≤ M)
    (hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |X z θ| ≤ M * canonW e z θ)
    (hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW e z θ * (Y z θ) ^ 2 ≤ A₁ z θ)
    (hZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW e z θ * (Z z θ) ^ 2 ≤ A₂ z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |X z θ| * |Y z θ| * |Z z θ| ≤ M * (A₁ z θ + A₂ z θ) := by
  intro z θ hz hθ hθ2
  have hσ : 0 ≤ Real.sin (2 * θ) := le_of_lt (rowDz_sin2_pos ⟨hθ, hθ2⟩)
  have h1 : canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
      ≤ M * (canonW e z θ * |Y z θ| * |Z z θ|) := by
    have h2 : canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
        = (canonW q z θ * |X z θ|) * (|Y z θ| * |Z z θ|) := by ring
    have h3 : M * (canonW e z θ * |Y z θ| * |Z z θ|)
        = (M * canonW e z θ) * (|Y z θ| * |Z z θ|) := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_right (hX z θ hz hθ hθ2)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
      ≤ M * (canonW e z θ * |Y z θ| * |Z z θ|) := h1
    _ ≤ M * (canonW e z θ * (Y z θ) ^ 2 + canonW e z θ * (Z z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left (rowDz_canonW_abs_mul_le hσ _ _) hM
    _ ≤ M * (A₁ z θ + A₂ z θ) :=
        mul_le_mul_of_nonneg_left (add_le_add (hY z θ hz hθ hθ2) (hZ z θ hz hθ hθ2)) hM

/-- Splitting off the `(0,0)`-summand of a double `range`-sum. -/
theorem rowDz_dsum_split (a b : ℕ) (C : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j)
      = C 0 0 + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0 else C i j) := by
  have hL : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j)
      = (∑ j ∈ Finset.range (b + 1), C 0 j)
        + ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range (b + 1), C (i + 1) j := by
    rw [Finset.sum_range_succ']; ring
  have hL0 : (∑ j ∈ Finset.range (b + 1), C 0 j)
      = C 0 0 + ∑ j ∈ Finset.range b, C 0 (j + 1) := by
    rw [Finset.sum_range_succ']; ring
  have hD : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ) else C i j))
      = (∑ j ∈ Finset.range (b + 1), (if (0 : ℕ) = 0 ∧ j = 0 then (0 : ℝ) else C 0 j))
        + ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range (b + 1),
            (if (i + 1) = 0 ∧ j = 0 then (0 : ℝ) else C (i + 1) j) := by
    rw [Finset.sum_range_succ']; ring
  have hD0 : (∑ j ∈ Finset.range (b + 1), (if (0 : ℕ) = 0 ∧ j = 0 then (0 : ℝ) else C 0 j))
      = ∑ j ∈ Finset.range b, C 0 (j + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have hDtail : (∑ i ∈ Finset.range a, ∑ j ∈ Finset.range (b + 1),
        (if (i + 1) = 0 ∧ j = 0 then (0 : ℝ) else C (i + 1) j))
      = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range (b + 1), C (i + 1) j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    exact Nat.succ_ne_zero i h
  rw [hL, hL0, hD, hD0, hDtail]
  ring

/-- `|A| ≤ K` from the `𝒲^{6,∞}`-bound. -/
theorem rowDz_A_le {α K : ℝ} {A : ℝ → ℝ → ℝ} (hAwl : Work.Spaces.WlInfMem α 6 A)
    (hAK : Work.Spaces.WlInf α 6 A ≤ K) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K := by
  intro z θ hz hθ hθ2
  have h := Work.Spaces.pz_sup_bound α 6 A hAwl 0 (by norm_num) z θ (le_of_lt hz)
    ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have h2 : Work.Spaces.WlInf α 6 A / (z + 1) ^ 0 ≤ K := by
    rw [pow_zero, div_one]; exact hAK
  exact le_trans h h2

/-- `|D_z A| ≤ K` from the `𝒲^{6,∞}`-bound. -/
theorem rowDz_DzA_le {α K : ℝ} {A : ℝ → ℝ → ℝ} (hAwl : Work.Spaces.WlInfMem α 6 A)
    (hAK : Work.Spaces.WlInf α 6 A ≤ K) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dz A z θ| ≤ K := by
  intro z θ hz hθ hθ2
  have h := Work.Spaces.pz_sup_bound α 6 A hAwl 1 (by norm_num) z θ (le_of_lt hz)
    ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have h2 : |Work.Spaces.pzIter 1 A z θ| ≤ K / (z + 1) := by
    refine le_trans h ?_
    rw [pow_one]
    exact div_le_div_of_nonneg_right hAK hz1.le
  rw [Work.Spaces.Dz, abs_mul, abs_of_pos hz]
  calc z * |Work.Spaces.pzIter 1 A z θ| ≤ z * (K / (z + 1)) :=
        mul_le_mul_of_nonneg_left h2 hz.le
    _ ≤ K := by
        rw [mul_div_assoc', div_le_iff₀ hz1]
        have hK0 : 0 ≤ K := le_trans (Work.Spaces.WlInf_nonneg α 6 A hAwl) hAK
        nlinarith [hK0]

/-- The constant `2·1000K` is dominated by `4000(1+C1f)(1+K+Kf)`. -/
theorem rowDz_const1 {C1f K Kf : ℝ} (hC1f : 0 < C1f) (hK : 0 ≤ K) (hKf : 0 ≤ Kf) :
    2 * (1000 * K) ≤ 4000 * (1 + C1f) * (1 + K + Kf) := by
  have h1 : (1 : ℝ) ≤ 1 + C1f := by linarith
  have h2 : (1 + K) ≤ 1 + K + Kf := by linarith
  have h3 : (0 : ℝ) ≤ 1 + K := by linarith
  have h4 : (1 : ℝ) * (1 + K) ≤ (1 + C1f) * (1 + K + Kf) :=
    mul_le_mul h1 h2 h3 (by linarith)
  calc 2 * (1000 * K) = 2000 * K := by ring
    _ ≤ 4000 * (1 + K) := by nlinarith
    _ = 4000 * (1 * (1 + K)) := by ring
    _ ≤ 4000 * ((1 + C1f) * (1 + K + Kf)) := mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 4000 * (1 + C1f) * (1 + K + Kf) := by ring

/-- The constant `2·C1f·Kf` is dominated by `4000(1+C1f)(1+K+Kf)`. -/
theorem rowDz_const2 {C1f K Kf : ℝ} (hC1f : 0 < C1f) (hK : 0 ≤ K) (hKf : 0 ≤ Kf) :
    2 * (C1f * Kf) ≤ 4000 * (1 + C1f) * (1 + K + Kf) := by
  have h1 : C1f * Kf ≤ (1 + C1f) * (1 + Kf) := by nlinarith [hC1f.le, hKf]
  have h2 : (1 + C1f) * (1 + Kf) ≤ (1 + C1f) * (1 + K + Kf) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : 2 * ((1 + C1f) * (1 + K + Kf)) ≤ 4000 * ((1 + C1f) * (1 + K + Kf)) := by
    have h4 : (0 : ℝ) ≤ (1 + C1f) * (1 + K + Kf) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h4]
  calc 2 * (C1f * Kf) ≤ 2 * ((1 + C1f) * (1 + Kf)) := by linarith
    _ ≤ 2 * ((1 + C1f) * (1 + K + Kf)) := by linarith
    _ ≤ 4000 * ((1 + C1f) * (1 + K + Kf)) := h3
    _ = 4000 * (1 + C1f) * (1 + K + Kf) := by ring

/-- The constant `2·2000K` is dominated by `4000(1+C1f)(1+K+Kf)`. -/
theorem rowDz_const3 {C1f K Kf : ℝ} (hC1f : 0 < C1f) (hK : 0 ≤ K) (hKf : 0 ≤ Kf) :
    2 * (2000 * K) ≤ 4000 * (1 + C1f) * (1 + K + Kf) := by
  have h1 : K ≤ (1 + C1f) * (1 + K + Kf) := by
    have h2 : (1 : ℝ) ≤ 1 + C1f := by linarith
    have h3 : (1 + K) ≤ 1 + K + Kf := by linarith
    calc K ≤ 1 + K := by linarith
      _ = 1 * (1 + K) := by ring
      _ ≤ (1 + C1f) * (1 + K + Kf) := mul_le_mul h2 h3 (by linarith) (by linarith)
  calc 2 * (2000 * K) = 4000 * K := by ring
    _ ≤ 4000 * ((1 + C1f) * (1 + K + Kf)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 4000 * (1 + C1f) * (1 + K + Kf) := by ring

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
