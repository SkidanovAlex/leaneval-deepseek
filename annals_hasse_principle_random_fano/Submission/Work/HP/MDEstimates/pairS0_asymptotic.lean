import Mathlib
import Submission.Work.HP.MDEstimates.primCount_asymp
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Lat.card_Mon
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.veronese_key
import Submission.Work.HP.MDEstimates.pairS0_arith
import Submission.Work.HP.MDEstimates.mu_sum_aux
import Submission.Work.HP.MDEstimates.ball_count_R0
import Submission.Work.HP.MDEstimates.veronese_linIndep
import Submission.Work.HP.MDEstimates.gam_structure
import Submission.Work.HP.MDEstimates.detL_Gam_upper

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MvPolynomial Finset

namespace Work.HP.MDEstimates

open Work.HP

/-- `pairS0 d n A p` is the number of primitive points of `Γ_{p.1,p.2}` of norm at most `A`. -/
lemma pairS0_eq_primNcard (d n : ℕ) (A : ℝ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :
    pairS0 d n A p
      = (({a : Mon d n → ℤ | a ∈ Gam d n p.1 p.2 ∧ IsPrim a ∧ eNorm a ≤ A}.ncard : ℝ)) := by
  have hset : {a ∈ primSet d n A (fun _ => True) |
        formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0}
      = {a : Mon d n → ℤ | a ∈ Gam d n p.1 p.2 ∧ IsPrim a ∧ eNorm a ≤ A} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_sep_iff, primSet, true_and, MDBasic.mem_Gam_iff]
    tauto
  unfold pairS0
  rw [hset]

/-- `8 ι_{d,n}` is the volume of the unit ball divided by the `ζ`-series, i.e. `V_R/ζ(R)`. -/
lemma mainTerm_eq (d n : ℕ) :
    8 * iotaDN d n
      = ballVol (NN d n - 2) / (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (NN d n - 2)) := by
  by_cases hZ : (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (NN d n - 2)) = 0
  · unfold iotaDN
    rw [hZ, mul_zero, div_zero]
    ring
  · unfold iotaDN
    field_simp

/-- The main theorem: the per-pair asymptotic count of the primitive coefficient vectors vanishing
at two points of height at most `B`, with the relative error `O(μ/A)` of Le Boudec's Lemma 3. -/
theorem pairS0_asymptotic (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      ∀ p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ), p ∈ Omega d n B → muXY n p.1 p.2 ≤ A →
        |pairS0 d n A p - 8 * iotaDN d n * A ^ (NN d n - 2) / detL (Gam d n p.1 p.2)|
          ≤ K * (A ^ (NN d n - 2) / detL (Gam d n p.1 p.2)) * (muXY n p.1 p.2 / A) := by
  classical
  obtain ⟨Kc, hKcpos, hKc⟩ := primCount_asymp (Mon d n)
  have hN6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have hδpos : 0 < (NN d n : ℝ) - 4 - 2 * (d : ℝ) / ((n : ℝ) + 1 - d) := by
    have h := arith_gap d n hd hdn h22
    linarith
  obtain ⟨Bl, hBlpos, hBl⟩ := log_pow_le_rpow (NN d n - 4) 1
    ((NN d n : ℝ) - 4 - 2 * (d : ℝ) / ((n : ℝ) + 1 - d)) (by norm_num) hδpos
  refine ⟨2 * Kc * (1 + (NN d n : ℝ)), max Bl 3, by positivity, by positivity, ?_⟩
  intro A B hB hAB hAB2 p hp hmu
  have hB3 : (3 : ℝ) ≤ B := le_trans (le_max_right _ _) hB
  have hBlB : Bl ≤ B := le_trans (le_max_left _ _) hB
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB3
  have hlogBpos : 0 < Real.log B := Real.log_pos (by linarith)
  have hA1 : 1 ≤ A := by
    have h2 : 1 ≤ B / Real.log B := by
      rw [le_div_iff₀ hlogBpos]
      linarith [Real.log_le_sub_one_of_pos hBpos]
    linarith
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  obtain ⟨hpx, hpy, hne, hne'⟩ := hp
  obtain ⟨hxprim, hxe⟩ := hpx
  obtain ⟨hyprim, hye⟩ := hpy
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hden : ((n : ℝ) + 1 - d) ≠ 0 := by
    have : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    intro h; linarith
  have hli : LinearIndependent ℤ ![p.1, p.2] := linIndep_of_ne_pm hxprim hyprim hne hne'
  have hν : LinearIndependent ℤ ![veronese d n p.1, veronese d n p.2] :=
    veronese_linIndep d n hd p.1 p.2 hxprim hyprim hne hne'
  obtain ⟨hrank, hprimLat, hdetpos⟩ := gam_structure d n p.1 p.2 hν
  have hlam : lam (Gam d n p.1 p.2) (rk (Gam d n p.1 p.2)) ≤ muXY n p.1 p.2 := by
    rw [hrank]
    exact (veronese_key d n hd hn2 p.1 p.2 hxprim hyprim hli).1
  have hrk3 : 3 ≤ rk (Gam d n p.1 p.2) := by rw [hrank]; omega
  have hkey := hKc (Gam d n p.1 p.2) A (muXY n p.1 p.2) hrk3 hA1 hprimLat hdetpos hlam hmu
  rw [pairS0_eq_primNcard]
  rw [mainTerm_eq d n]
  rw [hrank] at hkey
  refine le_trans hkey ?_
  -- `μ ≥ 1` and `log μ ≤ μ`
  have hμ0 : 0 ≤ muXY n p.1 p.2 := by
    unfold muXY
    refine mul_nonneg (by positivity) ?_
    refine le_trans ?_ (le_max_left _ _)
    refine div_nonneg (Real.sInf_nonneg ?_) (Real.sInf_nonneg ?_)
    · rintro D ⟨L, -, -, rfl⟩; exact detL_nonneg L
    · rintro D ⟨L, -, -, rfl⟩; exact detL_nonneg L
  have hμ1 : 1 ≤ muXY n p.1 p.2 := by
    have h1 : 1 ≤ lam (Gam d n p.1 p.2) (rk (Gam d n p.1 p.2)) := by
      rw [hrank]
      exact one_le_lam _ (by omega) (by rw [hrank])
    linarith
  have hlogμ : Real.log (muXY n p.1 p.2) ≤ muXY n p.1 p.2 := Real.log_le_self hμ0
  -- ### the determinant is at most `N · B^{2d/(n+1-d)}`
  have hdet : detL (Gam d n p.1 p.2)
      ≤ (NN d n : ℝ) * B ^ (2 * (d : ℝ) / ((n : ℝ) + 1 - d)) := by
    have h := detL_Gam_upper d n hd hn2 p.1 p.2 hxprim hyprim hli
    have hexp : ∀ z : ℝ, (0 : ℝ) ≤ z → z ^ d ≤ (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d → z ^ d ≤ B ^ ((d : ℝ) / ((n : ℝ) + 1 - d)) := by
      intro z hz hz2
      have h3 : (B ^ (1 / ((n : ℝ) + 1 - d))) ^ d = B ^ ((d : ℝ) / ((n : ℝ) + 1 - d)) := by
        rw [← Real.rpow_natCast (B ^ (1 / ((n : ℝ) + 1 - d))) d,
          ← Real.rpow_mul (le_of_lt hBpos)]
        congr 1
        field_simp
      linarith [hz2, h3.le, h3.ge]
    have h1 : (eNorm p.1) ^ d ≤ B ^ ((d : ℝ) / ((n : ℝ) + 1 - d)) :=
      hexp _ (Real.sqrt_nonneg _) (pow_le_pow_left₀ (Real.sqrt_nonneg _) hxe d)
    have h2 : (eNorm p.2) ^ d ≤ B ^ ((d : ℝ) / ((n : ℝ) + 1 - d)) :=
      hexp _ (Real.sqrt_nonneg _) (pow_le_pow_left₀ (Real.sqrt_nonneg _) hye d)
    have hprod : (eNorm p.1 * eNorm p.2) ^ d ≤ B ^ (2 * (d : ℝ) / ((n : ℝ) + 1 - d)) := by
      calc (eNorm p.1 * eNorm p.2) ^ d = (eNorm p.1) ^ d * (eNorm p.2) ^ d := mul_pow _ _ _
        _ ≤ B ^ ((d : ℝ) / ((n : ℝ) + 1 - d)) * B ^ ((d : ℝ) / ((n : ℝ) + 1 - d)) :=
            mul_le_mul h1 h2 (pow_nonneg (Real.sqrt_nonneg _) d)
              (Real.rpow_nonneg (le_of_lt hBpos) _)
        _ = B ^ (2 * (d : ℝ) / ((n : ℝ) + 1 - d)) := by
            rw [← Real.rpow_add hBpos]
            congr 1
            ring
    calc detL (Gam d n p.1 p.2) ≤ (NN d n : ℝ) * (eNorm p.1 * eNorm p.2) ^ d := h
      _ ≤ (NN d n : ℝ) * B ^ (2 * (d : ℝ) / ((n : ℝ) + 1 - d)) :=
          mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
  -- ### `det ≤ N A^{N-4}`
  have hlogB : (Real.log B) ^ (NN d n - 4)
      ≤ 1 * B ^ ((NN d n : ℝ) - 4 - 2 * (d : ℝ) / ((n : ℝ) + 1 - d)) := hBl B hBlB
  have hdetA : detL (Gam d n p.1 p.2) ≤ (NN d n : ℝ) * A ^ (NN d n - 4) := by
    have hNB : (NN d n : ℝ) * B ^ (2 * (d : ℝ) / ((n : ℝ) + 1 - d))
        ≤ (NN d n : ℝ) * (B / Real.log B) ^ (NN d n - 4) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [div_pow, le_div_iff₀ (pow_pos hlogBpos _)]
      calc B ^ (2 * (d : ℝ) / ((n : ℝ) + 1 - d)) * (Real.log B) ^ (NN d n - 4)
          ≤ B ^ (2 * (d : ℝ) / ((n : ℝ) + 1 - d))
              * (1 * B ^ ((NN d n : ℝ) - 4 - 2 * (d : ℝ) / ((n : ℝ) + 1 - d))) :=
            mul_le_mul_of_nonneg_left hlogB (Real.rpow_nonneg (le_of_lt hBpos) _)
        _ = B ^ ((NN d n : ℝ) - 4) := by
            rw [one_mul, ← Real.rpow_add hBpos]
            congr 1
            ring
        _ = B ^ (NN d n - 4) := by
            have h4 : 4 ≤ NN d n := by omega
            rw [show (NN d n : ℝ) - 4 = ((NN d n - 4 : ℕ) : ℝ) by
              rw [Nat.cast_sub h4]; norm_num, Real.rpow_natCast]
    calc detL (Gam d n p.1 p.2)
        ≤ (NN d n : ℝ) * B ^ (2 * (d : ℝ) / ((n : ℝ) + 1 - d)) := hdet
      _ ≤ (NN d n : ℝ) * (B / Real.log B) ^ (NN d n - 4) := hNB
      _ ≤ (NN d n : ℝ) * A ^ (NN d n - 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact pow_le_pow_left₀ (by positivity) hAB _
  -- ### absorbing the `A log μ` term
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hDne : detL (Gam d n p.1 p.2) ≠ 0 := ne_of_gt hdetpos
  have hpow : A ^ (NN d n - 2) = A ^ (NN d n - 4) * A ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hlogterm : Kc * A * (1 + Real.log (muXY n p.1 p.2))
      ≤ 2 * Kc * (NN d n : ℝ)
          * ((A ^ (NN d n - 2) / detL (Gam d n p.1 p.2)) * (muXY n p.1 p.2 / A)) := by
    have h2 : (1 : ℝ) ≤ (NN d n : ℝ) * A ^ (NN d n - 4) / detL (Gam d n p.1 p.2) := by
      rw [le_div_iff₀ hdetpos]
      linarith [hdetA]
    have h3 : A * (1 + Real.log (muXY n p.1 p.2)) ≤ 2 * (A * muXY n p.1 p.2) := by
      nlinarith [hlogμ, hApos.le, hμ0, hμ1]
    have h4 : A * muXY n p.1 p.2
        ≤ A * muXY n p.1 p.2 * ((NN d n : ℝ) * A ^ (NN d n - 4) / detL (Gam d n p.1 p.2)) := by
      nlinarith [h2, mul_nonneg hApos.le hμ0]
    have h5 : A * muXY n p.1 p.2 * ((NN d n : ℝ) * A ^ (NN d n - 4) / detL (Gam d n p.1 p.2))
        = (NN d n : ℝ) * ((A ^ (NN d n - 2) / detL (Gam d n p.1 p.2)) * (muXY n p.1 p.2 / A)) := by
      rw [hpow]
      field_simp
    calc Kc * A * (1 + Real.log (muXY n p.1 p.2))
        = Kc * (A * (1 + Real.log (muXY n p.1 p.2))) := by ring
      _ ≤ Kc * (2 * (A * muXY n p.1 p.2)) := mul_le_mul_of_nonneg_left h3 (le_of_lt hKcpos)
      _ ≤ Kc * (2 * (A * muXY n p.1 p.2
            * ((NN d n : ℝ) * A ^ (NN d n - 4) / detL (Gam d n p.1 p.2)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hKcpos)
          linarith [h4]
      _ = 2 * Kc * (NN d n : ℝ)
          * ((A ^ (NN d n - 2) / detL (Gam d n p.1 p.2)) * (muXY n p.1 p.2 / A)) := by
          rw [h5]; ring
  -- ### final assembly
  calc Kc * (A ^ (NN d n - 2) / detL (Gam d n p.1 p.2) * (muXY n p.1 p.2 / A))
        + Kc * A * (1 + Real.log (muXY n p.1 p.2))
      ≤ Kc * (A ^ (NN d n - 2) / detL (Gam d n p.1 p.2) * (muXY n p.1 p.2 / A))
        + 2 * Kc * (NN d n : ℝ)
          * (A ^ (NN d n - 2) / detL (Gam d n p.1 p.2) * (muXY n p.1 p.2 / A)) := by
          linarith [hlogterm]
    _ = Kc * (1 + 2 * (NN d n : ℝ))
          * (A ^ (NN d n - 2) / detL (Gam d n p.1 p.2) * (muXY n p.1 p.2 / A)) := by ring
    _ ≤ 2 * Kc * (1 + (NN d n : ℝ))
          * (A ^ (NN d n - 2) / detL (Gam d n p.1 p.2) * (muXY n p.1 p.2 / A)) := by
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · nlinarith [hKcpos, (Nat.cast_nonneg (NN d n) : (0:ℝ) ≤ (NN d n : ℝ))]
          · positivity
    _ = 2 * Kc * (1 + (NN d n : ℝ)) * (A ^ (NN d n - 2) / detL (Gam d n p.1 p.2))
          * (muXY n p.1 p.2 / A) := by ring

end Work.HP.MDEstimates
