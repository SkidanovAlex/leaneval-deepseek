/-
# The small-`N` branch of Proposition `lip-2`, with the constants of `LipOutputGenTwoTail`

This is `Work.KMTAreas.A4Z.LipOutputGenTwoTail P ρ A C K C0 K2` for a constant `C` chosen from
the data `A ≥ 1`, `K ≥ 1`, `C0 ≥ 1`, `K2 ≥ 1`, `A ^ (K2 - 1) ≤ C0 ^ 2`, in the regime
`N ^ d ≤ C δ^{-K}`.  The construction is the same as in `Submission.Work.KMTAreas.A4Z.smallTail`
(the second dual function `Ã_N^{**}(f,h)` truncated to the window `[-A N^d, A N^d]`), but the
generality in `(K, C0, K2)` requires

* `δ^K ≤ δ` (used for the correlation clause, `K ≥ 1`, `δ ≤ 1`), and
* the hypothesis `A ^ (K2-1) ≤ C0 ^ 2` (used for the `ℓ²` tail clause: the truncation is
  supported in `[-A N^d, A N^d]`, so its `ℓ²` tail at radius `R N^d` is bounded by
  `2 A N^d + 1`, and this is dominated by `C0^2 R^{-K2} (C A δ^{-K})^2 N^d` precisely because
  `C0^2 ≥ A^{K2-1}`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.smallTail

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4Z

/-- The elementary tail estimate behind the `ℓ²` clause: for `1 ≤ A`, `1 ≤ K2`,
`A ^ (K2 - 1) ≤ C0 ^ 2`, `2 ≤ C`, `0 < δ ≤ 1`, `1 ≤ K`, `1 ≤ R ≤ A` and `Nd > 0`,
`3 * A * Nd ≤ C0^2 * R^{-K2} * (C * A * δ^{-K})^2 * Nd`. -/
theorem l2Tail_rhs_aux {A C0 K2 C δ R Nd K : ℝ} (hA : 1 ≤ A) (hK2 : 1 ≤ K2)
    (hAK : A ^ (K2 - 1) ≤ C0 ^ 2) (hC : 2 ≤ C) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 1 ≤ K) (hR1 : 1 ≤ R) (hRA : R ≤ A) (hNd : 0 < Nd) :
    3 * A * Nd ≤ C0 ^ 2 * R ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2 * Nd := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hδK1 : 1 ≤ δ⁻¹ ^ K := Real.one_le_rpow (one_le_inv₀ hδ0 |>.mpr hδ1) (by linarith)
  have hS2 : 1 ≤ (δ⁻¹ ^ K) ^ 2 := one_le_pow₀ hδK1
  have hC2 : 4 ≤ C ^ 2 := by nlinarith
  have hCS : 4 ≤ C ^ 2 * (δ⁻¹ ^ K) ^ 2 := by
    calc (4 : ℝ) = 4 * 1 := by ring
      _ ≤ C ^ 2 * (δ⁻¹ ^ K) ^ 2 := mul_le_mul hC2 hS2 (by norm_num) (by positivity)
  have hsq : (C * A * δ⁻¹ ^ K) ^ 2 = C ^ 2 * A ^ 2 * (δ⁻¹ ^ K) ^ 2 := by ring
  have h4A : 4 * A ^ 2 ≤ (C * A * δ⁻¹ ^ K) ^ 2 := by
    rw [hsq]
    calc 4 * A ^ 2 = (4 : ℝ) * A ^ 2 := by ring
      _ ≤ (C ^ 2 * (δ⁻¹ ^ K) ^ 2) * A ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg A)
      _ = C ^ 2 * A ^ 2 * (δ⁻¹ ^ K) ^ 2 := by ring
  have hcore : 1 ≤ C0 ^ 2 * R ^ (-(K2)) * A := by
    have hAA : A ^ (K2 - 1) * A ^ (1 - K2) = 1 := by
      rw [← Real.rpow_add hA0, show K2 - 1 + (1 - K2) = 0 by ring, Real.rpow_zero]
    have hC0A : 1 ≤ C0 ^ 2 * A ^ (1 - K2) := by
      have h := mul_le_mul_of_nonneg_right hAK (le_of_lt (Real.rpow_pos_of_pos hA0 (1 - K2)))
      rwa [hAA] at h
    have hRneg : A ^ (-(K2)) ≤ R ^ (-(K2)) :=
      Real.rpow_le_rpow_of_nonpos hR0 hRA (by linarith)
    have hAneg : A ^ (-(K2)) * A = A ^ (1 - K2) := by
      rw [show (1 : ℝ) - K2 = -K2 + 1 by ring, Real.rpow_add hA0, Real.rpow_one]
    calc (1 : ℝ) ≤ C0 ^ 2 * A ^ (1 - K2) := hC0A
      _ = C0 ^ 2 * (A ^ (-(K2)) * A) := by rw [hAneg]
      _ ≤ C0 ^ 2 * (R ^ (-(K2)) * A) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C0)
          exact mul_le_mul_of_nonneg_right hRneg (le_of_lt hA0)
      _ = C0 ^ 2 * R ^ (-(K2)) * A := by ring
  have hRneg_nonneg : 0 ≤ C0 ^ 2 * R ^ (-(K2)) :=
    mul_nonneg (sq_nonneg C0) (le_of_lt (Real.rpow_pos_of_pos hR0 (-(K2))))
  have hstep : 4 * A * Nd ≤ C0 ^ 2 * R ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2 * Nd := by
    calc 4 * A * Nd = 1 * (4 * A * Nd) := by ring
      _ ≤ (C0 ^ 2 * R ^ (-(K2)) * A) * (4 * A * Nd) :=
          mul_le_mul_of_nonneg_right hcore (by positivity)
      _ = C0 ^ 2 * R ^ (-(K2)) * (4 * A ^ 2) * Nd := by ring
      _ ≤ C0 ^ 2 * R ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2 * Nd :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4A hRneg_nonneg) (le_of_lt hNd)
  nlinarith [hstep, hA0, hNd]

/-- **The small-`N` branch of Proposition `lip-2` with the general constants.** -/
theorem smallTailK (P : Polynomial ℤ) : ∀ A : ℝ, 1 ≤ A → ∀ (K C0 K2 : ℝ), 1 ≤ K → 1 ≤ C0 → 1 ≤ K2 → A ^ (K2 - 1) ≤ C0 ^ 2 → ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 → A * (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree → Work.Analysis.InverseTheory.SupportIn f N₀ → Work.Analysis.InverseTheory.SupportIn g N₀ → Work.Analysis.InverseTheory.SupportIn h N₀ → (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) → δ * (N : ℝ) ^ P.natDegree ≤ ‖Work.Analysis.InverseTheory.bilinPair (Work.Analysis.InverseTheory.AhalfZ N P f g) h‖ → (N : ℝ) ^ P.natDegree ≤ C * δ⁻¹ ^ K → ∃ (G : ℤ → ℂ) (l : ℕ) (k : ℤ), (∀ x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K) ∧ Summable (fun x : ℤ => ‖G x‖) ∧ (∑' x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧ Work.Analysis.InverseTheory.FourierSupportIn G (Work.Analysis.InverseTheory.majorArc ρ l k) ∧ (2 : ℝ) ^ l ≤ C * A * δ⁻¹ ^ K ∧ (2 : ℝ) ^ k ≤ C * A * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree ∧ δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖Work.Analysis.InverseTheory.bilinPair g G‖ ∧ (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ else 0) ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧ (∀ R : ℝ, 1 ≤ R → ∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0) ≤ C0 ^ 2 * R ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2 * (N : ℝ) ^ P.natDegree) := by
  intro A hA K C0 K2 hK hC0 hK2 hAK
  refine ⟨4, by norm_num, ?_⟩
  intro ρ hρ0 hρ1 N N₀ δ f g h hN hδ0 hδ1 hN0lo hN0hi hfs hgs hhs hfb hgb hhb hcorr hsmall
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hδinvpos : (0 : ℝ) < δ⁻¹ := lt_of_lt_of_le zero_lt_one hδinv1
  have hδK1 : (1 : ℝ) ≤ δ⁻¹ ^ K := Real.one_le_rpow hδinv1 (by linarith)
  have hsmall' : (N : ℝ) ^ P.natDegree ≤ 4 * δ⁻¹ ^ K := hsmall
  have hAδK : (1 : ℝ) ≤ A * δ⁻¹ ^ K := by
    have h := mul_le_mul hA hδK1 (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hA0)
    simpa using h
  have h1goal : (1 : ℝ) ≤ 4 * A * δ⁻¹ ^ K := by
    have h4 : (4 : ℝ) * (A * δ⁻¹ ^ K) = 4 * A * δ⁻¹ ^ K := by ring
    linarith [hAδK, h4]
  -- the truncation window
  set R : ℕ := ⌊A * (N : ℝ) ^ P.natDegree⌋₊ with hRdef
  have hRle : (R : ℝ) ≤ A * (N : ℝ) ^ P.natDegree := Nat.floor_le (by positivity)
  have hN0R : N₀ ≤ R := Nat.le_floor hN0hi
  have hAN1 : (1 : ℝ) ≤ A * (N : ℝ) ^ P.natDegree :=
    one_le_mul_of_one_le_of_one_le hA hNd1
  have hN0ge1 : 1 ≤ N₀ := by
    have h2 : (1 : ℝ) / 2 ≤ (N₀ : ℝ) := by linarith [hAN1, hN0lo]
    have h3 : (0 : ℝ) < (N₀ : ℝ) := by linarith
    have h4 : 0 < N₀ := by exact_mod_cast h3
    omega
  have hR1 : 1 ≤ R := le_trans hN0ge1 hN0R
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  -- the candidate: the second dual function truncated to the window
  set G : ℤ → ℂ := fun x => if x.natAbs ≤ R then AhalfTranspose₂ N P f h x else 0 with hGdef
  have hGvan : ∀ x : ℤ, R < x.natAbs → G x = 0 := by
    intro x hx
    simp only [hGdef]
    rw [if_neg (not_le.mpr hx)]
  have hG1 : ∀ x : ℤ, ‖G x‖ ≤ 1 := by
    intro x
    simp only [hGdef]
    by_cases hx : x.natAbs ≤ R
    · rw [if_pos hx]; exact norm_AhalfTranspose₂_le_one hN P hfb hhb x
    · rw [if_neg hx]; simp
  refine ⟨G, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the sup bound
    intro x
    exact le_trans (hG1 x) h1goal
  · -- (2) summability
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(R : ℤ)) (R : ℤ)) fun x hx => ?_
    have hx' : R < x.natAbs := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h <;> omega
    rw [hGvan x hx', norm_zero]
  · -- (3) the `ℓ¹` bound
    have h3 : (∑' x : ℤ, ‖G x‖) ≤ 2 * (R : ℝ) + 1 := by
      have hsupp : SupportIn G R := hGvan
      have h := ellOne_le_of_supportIn G R hsupp (C := 1) (fun x => hG1 x)
      simpa [ellOne] using h
    have h4a : 2 * (R : ℝ) + 1 ≤ 3 * (A * (N : ℝ) ^ P.natDegree) := by linarith [hRle, hAN1]
    have h4b : 3 * (A * (N : ℝ) ^ P.natDegree) ≤ 4 * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by
      have h3δ : (3 : ℝ) ≤ 4 * δ⁻¹ ^ K := by linarith [hδK1]
      have hANpos : (0 : ℝ) < A * (N : ℝ) ^ P.natDegree := mul_pos hA0 hNdpos
      calc 3 * (A * (N : ℝ) ^ P.natDegree)
          ≤ (4 * δ⁻¹ ^ K) * (A * (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_right h3δ (le_of_lt hANpos)
        _ = 4 * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by ring
    linarith [h3, h4a, h4b]
  · -- (4) Fourier support: the major arcs at `(0,0)` are everything
    rw [Work.KMTAreas.A4.lipMajorArcZeroZero hρ0 hρ1]
    exact fun ξ hξ => absurd (Set.mem_univ ξ) hξ
  · -- (5) the linear scale
    rw [pow_zero]
    exact h1goal
  · -- (6) the continuous scale
    have h6 : (1 : ℝ) ≤ 4 * A * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree := by
      rw [le_div_iff₀ hNdpos, one_mul]
      have hm : (1 : ℝ) * δ⁻¹ ^ K ≤ A * δ⁻¹ ^ K :=
        mul_le_mul_of_nonneg_right hA (le_of_lt (Real.rpow_pos_of_pos hδinvpos K))
      rw [one_mul] at hm
      have h4 : 4 * δ⁻¹ ^ K ≤ 4 * A * δ⁻¹ ^ K := by
        have h5 : (4 : ℝ) * (δ⁻¹ ^ K) ≤ 4 * (A * δ⁻¹ ^ K) :=
          mul_le_mul_of_nonneg_left hm (by norm_num)
        have hEq : 4 * (A * δ⁻¹ ^ K) = 4 * A * δ⁻¹ ^ K := by ring
        linarith [h5, hEq]
      exact le_trans hsmall' h4
    rw [zpow_zero]
    exact h6
  · -- (7) the correlation
    have hGg : bilinPair g G = bilinPair (AhalfTranspose₂ N P f h) g := by
      rw [bilinPair, bilinPair]
      refine tsum_congr fun x => ?_
      by_cases hx : x.natAbs ≤ R
      · have hGx : G x = AhalfTranspose₂ N P f h x := by
          simp only [hGdef]; rw [if_pos hx]
        rw [hGx]; ring
      · have hGx : G x = 0 := by simp only [hGdef]; rw [if_neg hx]
        have hxN : N₀ < x.natAbs := lt_of_le_of_lt hN0R (lt_of_not_ge hx)
        rw [hGx, mul_zero, hgs x hxN, mul_zero]
    have htr : bilinPair (AhalfTranspose₂ N P f h) g = bilinPair (AhalfZ N P f g) h :=
      (bilinPair_AhalfZ_eq_transpose₂ (FinSupp.of_supportIn hfs) (FinSupp.of_supportIn hgs)
        (FinSupp.of_supportIn hhs) N P).symm
    have hδKleδ : δ ^ K ≤ δ := by
      have h := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hK
      rwa [Real.rpow_one] at h
    calc δ ^ K * (N : ℝ) ^ P.natDegree ≤ δ * (N : ℝ) ^ P.natDegree :=
          mul_le_mul_of_nonneg_right hδKleδ hNdpos.le
      _ ≤ ‖bilinPair (AhalfZ N P f g) h‖ := hcorr
      _ = ‖bilinPair g G‖ := by rw [hGg, htr]
  · -- (8) the `ℓ¹`-fringe clause: the truncation vanishes outside the window
    have hzero : (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ else 0))
        = ∑' _x : ℤ, (0 : ℝ) := by
      refine tsum_congr fun x => ?_
      by_cases hx : A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
      · have hxR : R < x.natAbs := by
          have h1 : A * (N : ℝ) ^ P.natDegree < (x.natAbs : ℝ) := by
            rwa [abs_cast_eq_natAbs] at hx
          exact_mod_cast lt_of_le_of_lt hRle h1
        rw [if_pos hx, hGvan x hxR, norm_zero]
      · rw [if_neg hx]
    rw [hzero, tsum_zero]
    exact div_nonneg (mul_nonneg (Real.rpow_pos_of_pos hδ0 K).le hNdpos.le) (by norm_num)
  · -- (9) the `ℓ²`-tail clause, from the support bound
    intro R' hR'
    have hR'pos : (0 : ℝ) < R' := lt_of_lt_of_le zero_lt_one hR'
    by_cases hbig : A ≤ R'
    · -- nothing survives the truncation
      have hzero : (∑' x : ℤ, (if R' * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0))
          = ∑' _x : ℤ, (0 : ℝ) := by
        refine tsum_congr fun x => ?_
        by_cases hx : R' * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
        · have hxR : R < x.natAbs := by
            by_contra hcon
            have h1 : |(x : ℝ)| ≤ (R : ℝ) := by
              rw [abs_cast_eq_natAbs]; exact_mod_cast not_lt.mp hcon
            have h3 : A * (N : ℝ) ^ P.natDegree ≤ R' * (N : ℝ) ^ P.natDegree :=
              mul_le_mul_of_nonneg_right hbig hNdpos.le
            linarith [h1, hRle, h3, hx]
          rw [if_pos hx, hGvan x hxR]; simp
        · rw [if_neg hx]
      rw [hzero, tsum_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C0)
        (le_of_lt (Real.rpow_pos_of_pos hR'pos (-(K2))))) (sq_nonneg _)) hNdpos.le
    · -- the support bound suffices
      have hR'ltA : R' < A := lt_of_not_ge hbig
      have htail := l2tail_of_support hGvan hG1 (R' * (N : ℝ) ^ P.natDegree)
      have h3AN : (∑' x : ℤ, (if R' * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0))
          ≤ 3 * (A * (N : ℝ) ^ P.natDegree) := by
        have h7 : 2 * (R : ℝ) + 1 ≤ 3 * (R : ℝ) := by linarith [hR1']
        have h8 : 3 * (R : ℝ) ≤ 3 * (A * (N : ℝ) ^ P.natDegree) := by linarith [hRle]
        linarith [htail, h7, h8]
      have hnum : 3 * (A * (N : ℝ) ^ P.natDegree)
          ≤ C0 ^ 2 * R' ^ (-(K2)) * (4 * A * δ⁻¹ ^ K) ^ 2 * (N : ℝ) ^ P.natDegree := by
        have h := l2Tail_rhs_aux hA hK2 hAK (by norm_num : (2 : ℝ) ≤ 4) hδ0 hδ1 hK hR'
          hR'ltA.le hNdpos
        linarith [h]
      linarith [h3AN, hnum]

end Work.KMTAreas.A4Z
