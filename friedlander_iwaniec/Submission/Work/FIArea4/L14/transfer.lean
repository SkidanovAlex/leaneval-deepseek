import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Assembly
import Submission.Commons.Data.Nat.card_divisors_le_const_mul_rpow
import Submission.Work.FIArea4.L14.sum_inv_oddPart_le
import Submission.Work.FIArea4.L14.sum_pairs_le_divisors
import Submission.Work.FIArea4.L14.abel_sum_rpow

namespace Work.FIArea4.L14

open Work.FIPlan

open scoped BigOperators

noncomputable section

/-- Weighted transfer lemma: if the partial sums `F(Q) = Σ_{q ≤ Q, q odd, q ≠ □}` of a
nonnegative function `f` satisfy `F(Q) ≤ Q M` for all `Q ≤ D²`, then the double sum
`Σ_{b₁,b₂ ≤ D, b₁' b₂' ≠ □} (b₁b₂)^{-1} f(b₁' b₂')` is `≪_δ D^{2δ} M` for every `δ > 0`.
(Proof: the weight of a given `q = b₁'b₂'` is at most `C (log D)² d(q)/q ≤ C_δ q^{-1+δ}`, and
Abel summation against the decreasing weight `q^{-1+δ}` produces `D^{2δ}`; the `(log D)²` is
absorbed into `D^{2δ}`.) -/
theorem transfer (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ) (M : ℝ) (f : ℕ → ℝ), 1 ≤ D → 0 ≤ M →
      (∀ q, 0 ≤ f q) →
      (∀ Q, Q ≤ D * D →
        (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q), f q) ≤ (Q : ℝ) * M) →
      (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
          (((b1 * b2 : ℕ) : ℝ)⁻¹) * f (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2))
        ≤ C * (D : ℝ) ^ (2 * δ) * M := by
  set β : ℝ := δ / 2 with hβdef
  have hβ : 0 < β := by rw [hβdef]; linarith
  obtain ⟨Cd, hCdpos, hCd⟩ := Commons.Data.Nat.card_divisors_le_const_mul_rpow β hβ
  obtain ⟨Ca, hCapos, hCa⟩ := abel_sum_rpow β hβ
  refine ⟨4 * Cd * Ca, by positivity, ?_⟩
  intro D M f hD hM hf hPsum
  set E : Finset ℕ := (Finset.Icc 1 D).filter Odd with hE
  set Φ : ℕ → ℝ := fun q => if Odd q ∧ Nat.sqrt q ^ 2 ≠ q then f q else 0 with hΦ
  have hΦnn : ∀ q, 0 ≤ Φ q := by
    intro q
    simp only [hΦ]
    by_cases h : Odd q ∧ Nat.sqrt q ^ 2 ≠ q
    · rw [if_pos h]; exact hf q
    · rw [if_neg h]
  -- Step 1: replace `f` by `Φ`, absorbing the filter into the summand.
  have hstep1 : (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (oddPart b1 * oddPart b2) ^ 2 ≠ oddPart b1 * oddPart b2),
          (((b1 * b2 : ℕ) : ℝ)⁻¹) * f (oddPart b1 * oddPart b2))
      = (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ Finset.Icc 1 D, (((b1 * b2 : ℕ) : ℝ)⁻¹) * Φ (oddPart b1 * oddPart b2)) := by
    apply Finset.sum_congr rfl
    intro b1 hb1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b2 hb2
    have hb1' : 1 ≤ b1 := (Finset.mem_Icc.mp hb1).1
    have hb2' : 1 ≤ b2 := (Finset.mem_Icc.mp hb2).1
    have hodd1 : Odd (oddPart b1) := Work.FIArea4.oddPart_odd (by omega)
    have hodd2 : Odd (oddPart b2) := Work.FIArea4.oddPart_odd (by omega)
    have hodd : Odd (oddPart b1 * oddPart b2) := hodd1.mul hodd2
    simp only [hΦ]
    have hmul : ((b1 * b2 : ℕ) : ℝ)⁻¹
        * (if Odd (oddPart b1 * oddPart b2) ∧ Nat.sqrt (oddPart b1 * oddPart b2) ^ 2
              ≠ oddPart b1 * oddPart b2 then f (oddPart b1 * oddPart b2) else 0)
        = if Nat.sqrt (oddPart b1 * oddPart b2) ^ 2 ≠ oddPart b1 * oddPart b2
          then ((b1 * b2 : ℕ) : ℝ)⁻¹ * f (oddPart b1 * oddPart b2) else 0 := by
      by_cases hc : Nat.sqrt (oddPart b1 * oddPart b2) ^ 2 ≠ oddPart b1 * oddPart b2
      · rw [if_pos hc, if_pos ⟨hodd, hc⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.2), mul_zero]
    rw [hmul]
  -- Step 2: remove the powers of two from the weights, at the cost of a factor `4`.
  have hstep2 : (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ Finset.Icc 1 D, (((b1 * b2 : ℕ) : ℝ)⁻¹) * Φ (oddPart b1 * oddPart b2))
      ≤ 4 * (∑ e1 ∈ E, ∑ e2 ∈ E, (((e1 * e2 : ℕ)) : ℝ)⁻¹ * Φ (e1 * e2)) := by
    have hinner : ∀ b1 ∈ Finset.Icc 1 D,
        (∑ b2 ∈ Finset.Icc 1 D, (((b1 * b2 : ℕ) : ℝ)⁻¹) * Φ (oddPart b1 * oddPart b2))
          ≤ 2 * (∑ e2 ∈ E, ((e2 : ℝ))⁻¹ * (((b1 : ℝ))⁻¹ * Φ (oddPart b1 * e2))) := by
      intro b1 hb1
      have hb1' : 1 ≤ b1 := (Finset.mem_Icc.mp hb1).1
      have h := sum_inv_oddPart_le D (fun x => ((b1 : ℝ))⁻¹ * Φ (oddPart b1 * x))
        (fun x => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg b1)) (hΦnn _))
      refine le_trans ?_ h
      apply Finset.sum_le_sum
      intro b2 hb2
      apply le_of_eq
      rw [Nat.cast_mul, mul_inv]
      ring
    have hG : ∀ y, 0 ≤ ∑ e2 ∈ E, ((e2 : ℝ))⁻¹ * Φ (y * e2) := by
      intro y
      apply Finset.sum_nonneg
      intro e2 _
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg e2)) (hΦnn _)
    have hout := sum_inv_oddPart_le D (fun y => ∑ e2 ∈ E, ((e2 : ℝ))⁻¹ * Φ (y * e2)) hG
    have hXY : (∑ b1 ∈ Finset.Icc 1 D,
          2 * (∑ e2 ∈ E, ((e2 : ℝ))⁻¹ * (((b1 : ℝ))⁻¹ * Φ (oddPart b1 * e2))))
        = 2 * (∑ b1 ∈ Finset.Icc 1 D,
            ((b1 : ℝ))⁻¹ * (∑ e2 ∈ E, ((e2 : ℝ))⁻¹ * Φ (oddPart b1 * e2))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b1 hb1
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e2 he2
      ring
    have hYZ : (∑ e1 ∈ E, ((e1 : ℝ))⁻¹ * (∑ e2 ∈ E, ((e2 : ℝ))⁻¹ * Φ (e1 * e2)))
        = (∑ e1 ∈ E, ∑ e2 ∈ E, (((e1 * e2 : ℕ)) : ℝ)⁻¹ * Φ (e1 * e2)) := by
      apply Finset.sum_congr rfl
      intro e1 he1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e2 he2
      rw [Nat.cast_mul, mul_inv]
      ring
    calc (∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ Finset.Icc 1 D, (((b1 * b2 : ℕ) : ℝ)⁻¹) * Φ (oddPart b1 * oddPart b2))
        ≤ ∑ b1 ∈ Finset.Icc 1 D,
            2 * (∑ e2 ∈ E, ((e2 : ℝ))⁻¹ * (((b1 : ℝ))⁻¹ * Φ (oddPart b1 * e2))) :=
          Finset.sum_le_sum hinner
      _ = 2 * (∑ b1 ∈ Finset.Icc 1 D,
            ((b1 : ℝ))⁻¹ * (∑ e2 ∈ E, ((e2 : ℝ))⁻¹ * Φ (oddPart b1 * e2))) := hXY
      _ ≤ 2 * (2 * (∑ e1 ∈ E, ((e1 : ℝ))⁻¹ * (∑ e2 ∈ E, ((e2 : ℝ))⁻¹ * Φ (e1 * e2)))) := by
          have h2 := mul_le_mul_of_nonneg_left hout (by norm_num : (0 : ℝ) ≤ 2)
          linarith [h2]
      _ = 4 * (∑ e1 ∈ E, ∑ e2 ∈ E, (((e1 * e2 : ℕ)) : ℝ)⁻¹ * Φ (e1 * e2)) := by
          rw [hYZ]; ring
  -- Step 3: group the pairs by their product; the multiplicity is at most `d(q)`.
  have hstep3 : 4 * (∑ e1 ∈ E, ∑ e2 ∈ E, (((e1 * e2 : ℕ)) : ℝ)⁻¹ * Φ (e1 * e2))
      ≤ 4 * (∑ q ∈ Finset.Icc 1 (D * D), ((q.divisors.card : ℕ) : ℝ) * Φ q / (q : ℝ)) := by
    have hp := sum_pairs_le_divisors D Φ hΦnn
    rw [hE]
    linarith [hp]
  -- Step 4: the divisor bound `d(q) ≤ Cd * q^β`.
  have hstep4 : (∑ q ∈ Finset.Icc 1 (D * D), ((q.divisors.card : ℕ) : ℝ) * Φ q / (q : ℝ))
      ≤ Cd * (∑ q ∈ Finset.Icc 1 (D * D), Φ q * (q : ℝ) ^ (β - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    have hqd : ((q.divisors.card : ℕ) : ℝ) ≤ Cd * (q : ℝ) ^ β := hCd q
    have h1 : ((q.divisors.card : ℕ) : ℝ) * Φ q / (q : ℝ)
        ≤ (Cd * (q : ℝ) ^ β) * Φ q / (q : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqd (hΦnn q)) (le_of_lt hqpos)
    have h2 : (Cd * (q : ℝ) ^ β) * Φ q / (q : ℝ) = Cd * (Φ q * (q : ℝ) ^ (β - 1)) := by
      have hrw : (q : ℝ) ^ β / (q : ℝ) = (q : ℝ) ^ (β - 1) := (Real.rpow_sub_one hqne β).symm
      calc (Cd * (q : ℝ) ^ β) * Φ q / (q : ℝ)
          = Cd * Φ q * ((q : ℝ) ^ β / (q : ℝ)) := by ring
        _ = Cd * Φ q * (q : ℝ) ^ (β - 1) := by rw [hrw]
        _ = Cd * (Φ q * (q : ℝ) ^ (β - 1)) := by ring
    linarith [h1, h2.le, h2.ge]
  -- Step 5: Abel summation against `q^(β-1)`.
  have hstep5 : (∑ q ∈ Finset.Icc 1 (D * D), Φ q * (q : ℝ) ^ (β - 1))
      ≤ Ca * ((D * D : ℕ) : ℝ) ^ β * M := by
    have hpart : ∀ Q, Q ≤ D * D → ∑ q ∈ Finset.Icc 1 Q, Φ q ≤ (Q : ℝ) * M := by
      intro Q hQ
      have h := hPsum Q hQ
      have heq : (∑ q ∈ Finset.Icc 1 Q, Φ q)
          = ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q), f q := by
        rw [Finset.sum_filter]
      rw [heq]
      exact h
    exact hCa Φ M (D * D) hM hΦnn hpart
  -- Assembly.
  calc (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (oddPart b1 * oddPart b2) ^ 2 ≠ oddPart b1 * oddPart b2),
          (((b1 * b2 : ℕ) : ℝ)⁻¹) * f (oddPart b1 * oddPart b2))
      = (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ Finset.Icc 1 D, (((b1 * b2 : ℕ) : ℝ)⁻¹) * Φ (oddPart b1 * oddPart b2)) := hstep1
    _ ≤ 4 * (∑ e1 ∈ E, ∑ e2 ∈ E, (((e1 * e2 : ℕ)) : ℝ)⁻¹ * Φ (e1 * e2)) := hstep2
    _ ≤ 4 * (∑ q ∈ Finset.Icc 1 (D * D), ((q.divisors.card : ℕ) : ℝ) * Φ q / (q : ℝ)) := hstep3
    _ ≤ 4 * (Cd * (∑ q ∈ Finset.Icc 1 (D * D), Φ q * (q : ℝ) ^ (β - 1))) := by
        linarith [hstep4]
    _ ≤ 4 * (Cd * (Ca * ((D * D : ℕ) : ℝ) ^ β * M)) := by
        have h1 := mul_le_mul_of_nonneg_left hstep5 (by positivity : (0 : ℝ) ≤ 4 * Cd)
        linarith [h1]
    _ ≤ (4 * Cd * Ca) * (D : ℝ) ^ (2 * δ) * M := by
        have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
        have hND : ((D * D : ℕ) : ℝ) ^ β = (D : ℝ) ^ δ := by
          have hDnn : (0 : ℝ) ≤ (D : ℝ) := by positivity
          have hbase : ((D * D : ℕ) : ℝ) = (D : ℝ) ^ (2 : ℝ) := by
            rw [Nat.cast_mul, Real.rpow_two]; ring
          rw [hbase, ← Real.rpow_mul hDnn (2 : ℝ) β]
          rw [show (2 : ℝ) * β = δ by rw [hβdef]; ring]
        have hle : (D : ℝ) ^ δ ≤ (D : ℝ) ^ (2 * δ) :=
          Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
        have hA : 0 ≤ 4 * Cd * Ca := by positivity
        calc 4 * (Cd * (Ca * ((D * D : ℕ) : ℝ) ^ β * M))
            = (4 * Cd * Ca) * ((D * D : ℕ) : ℝ) ^ β * M := by ring
          _ = (4 * Cd * Ca) * (D : ℝ) ^ δ * M := by rw [hND]
          _ ≤ (4 * Cd * Ca) * (D : ℝ) ^ (2 * δ) * M :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hA) hM

end

end Work.FIArea4.L14
