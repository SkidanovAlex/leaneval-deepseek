/-
# The small-`N` branch of `Work.KMTAreas.A4Z.lipTwoGenTail`, in the parametric form

`Work.KMTAreas.A4Z.SmallTailBranch P` is the small-`N` branch of Proposition `lip-2` with the tail
clauses in the *parametric* form used by the gluing `Work.KMTAreas.A4Z.glue`: the exponents `K` and
the tail constants `C₀, K₂` are prescribed by the caller (subject to `1 ≤ K`, `1 ≤ C₀`, `1 ≤ K₂`
and `A ^ (K₂ - 1) ≤ C₀ ^ 2`), and only a *threshold* `Cmin` for the main constant `C` has to be
produced — every `C ≥ Cmin` then works.

The construction is that of `Submission.Work.KMTAreas.A4Z.smallTailK` (`C = 4` there) and of
`Submission.Work.KMTAreas.A4Z.smallTail`: the candidate is the second dual function
`Ã_N^{**}(f,h)` of §5 of the paper, truncated to the window `[-⌊A N^d⌋, ⌊A N^d⌋]`.  Its Fourier
transform is supported in the vacuous major arcs `majorArc ρ 0 0 = Set.univ`, its pairing with `g`
is `⟨Ã_N(f,g), h⟩` by the transposition identity, and the truncation makes the `ℓ¹`-fringe clause
hold with equality (mass `0`).

Since `smallTailK` is stated as `∃ C, 0 < C ∧ …` (an existential witness, which does not reduce),
and since the constant `C` of the target is a *parameter* of the branch, we redo the (short)
verification with `C` explicit.  Every use of `C` is monotone in it, so `Cmin = 4` works: the case
hypothesis `N ^ d ≤ C δ ^ {-K}` is used only for the clause `2 ^ k ≤ C A δ^{-K}/N^d` with `k = 0`
(i.e. `N ^ d ≤ C A δ^{-K}`); the `ℓ²`-tail uses the hypothesis `A ^ (K₂-1) ≤ C₀ ^ 2` exactly as in
`smallTailK`; and the remaining clauses use only `C ≥ 4`, `A ≥ 1`, `δ ≤ 1`, `K ≥ 1`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.glue
import Submission.Work.KMTAreas.A4Z.smallTailK

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4Z

/-- **The small-`N` branch of Proposition `lip-2` with the tail clauses, in the parametric form
`Work.KMTAreas.A4Z.SmallTailBranch` requested by the gluing.** -/
theorem smallTailBranch (P : Polynomial ℤ) : Work.KMTAreas.A4Z.SmallTailBranch P := by
  intro A hA K C0 K2 hK hC0 hK2 hAK
  refine ⟨4, by norm_num, ?_⟩
  intro C hC4 ρ hρ0 hρ1 N N₀ δ f g h hN hδ0 hδ1 hN0lo hN0hi hfs hgs hhs hfb hgb hhb hcorr
    hsmall
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC4
  have hC3 : (3 : ℝ) ≤ C := by linarith
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hδinvpos : (0 : ℝ) < δ⁻¹ := lt_of_lt_of_le zero_lt_one hδinv1
  have hδK1 : (1 : ℝ) ≤ δ⁻¹ ^ K := Real.one_le_rpow hδinv1 (by linarith)
  have hδK0 : (0 : ℝ) ≤ δ⁻¹ ^ K := le_trans zero_le_one hδK1
  have hAδK : (1 : ℝ) ≤ A * δ⁻¹ ^ K := by
    have h := mul_le_mul hA hδK1 (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hA0)
    simpa using h
  -- the target constant in clause (1)
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have h1goal : (1 : ℝ) ≤ C * A * δ⁻¹ ^ K := by
    have hCA : (1 : ℝ) ≤ C * A := one_le_mul_of_one_le_of_one_le hC1 hA
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (C * A) * δ⁻¹ ^ K := mul_le_mul hCA hδK1 (by norm_num) (by positivity)
      _ = C * A * δ⁻¹ ^ K := by ring
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
    exact (hG1 x).trans h1goal
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
    have h4b : 3 * (A * (N : ℝ) ^ P.natDegree)
        ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by
      have h3δ : (3 : ℝ) ≤ C * δ⁻¹ ^ K :=
        hC3.trans (le_mul_of_one_le_right hCpos.le hδK1)
      have hANpos : (0 : ℝ) < A * (N : ℝ) ^ P.natDegree := mul_pos hA0 hNdpos
      calc 3 * (A * (N : ℝ) ^ P.natDegree)
          ≤ (C * δ⁻¹ ^ K) * (A * (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_right h3δ (le_of_lt hANpos)
        _ = C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by ring
    linarith [h3, h4a, h4b]
  · -- (4) Fourier support: the major arcs at `(0,0)` are everything
    rw [Work.KMTAreas.A4.lipMajorArcZeroZero hρ0 hρ1]
    exact fun ξ hξ => absurd (Set.mem_univ ξ) hξ
  · -- (5) the linear scale
    rw [pow_zero]
    exact h1goal
  · -- (6) the continuous scale: this is where the small-`N` case hypothesis is used
    have h6 : (1 : ℝ) ≤ C * A * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree := by
      rw [le_div_iff₀ hNdpos, one_mul]
      calc (N : ℝ) ^ P.natDegree ≤ C * δ⁻¹ ^ K := hsmall
        _ ≤ C * A * δ⁻¹ ^ K := by
            have hCA : C ≤ C * A := le_mul_of_one_le_right hCpos.le hA
            calc C * δ⁻¹ ^ K ≤ (C * A) * δ⁻¹ ^ K :=
                  mul_le_mul_of_nonneg_right hCA hδK0
              _ = C * A * δ⁻¹ ^ K := by ring
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
    have htarget : (0 : ℝ) ≤ C0 ^ 2 * R' ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2
        * (N : ℝ) ^ P.natDegree :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C0)
        (Real.rpow_nonneg hR'pos.le _)) (sq_nonneg _)) hNdpos.le
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
      exact htarget
    · -- the support bound suffices
      have hR'ltA : R' < A := lt_of_not_ge hbig
      have htail := l2tail_of_support hGvan hG1 (R' * (N : ℝ) ^ P.natDegree)
      have h3AN : (∑' x : ℤ, (if R' * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0))
          ≤ 3 * (A * (N : ℝ) ^ P.natDegree) := by
        have h7 : 2 * (R : ℝ) + 1 ≤ 3 * (R : ℝ) := by linarith [hR1']
        have h8 : 3 * (R : ℝ) ≤ 3 * (A * (N : ℝ) ^ P.natDegree) := by linarith [hRle]
        linarith [htail, h7, h8]
      have hnum : 3 * (A * (N : ℝ) ^ P.natDegree)
          ≤ C0 ^ 2 * R' ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2 * (N : ℝ) ^ P.natDegree := by
        have h2C : (2 : ℝ) ≤ C := by linarith
        simpa only [mul_assoc] using
          l2Tail_rhs_aux hA hK2 hAK h2C hδ0 hδ1 hK hR' hR'ltA.le hNdpos
      linarith [h3AN, hnum]

end Work.KMTAreas.A4Z
