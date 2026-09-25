import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.Maximal.mstTail_geom_tsum
import Submission.Work.Maximal.mstKappa_tail_exp_decay

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option maxHeartbeats 2000000

noncomputable section

open Work.BourgainPlan.Maximal

/-! ## Elementary `rpow` algebra used by the tail summation -/

/-- `(p * q * s) ^ z = p ^ z * q ^ z * s ^ z` for nonnegative `p, q, s`. -/
private lemma rpow_mul_three {p q s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s) (z : ℝ) :
    (p * q * s) ^ z = p ^ z * q ^ z * s ^ z := by
  have h1 : (p * q * s) ^ z = p ^ z * (q ^ z * s ^ z) := by
    rw [mul_assoc, Real.mul_rpow hp (mul_nonneg hq hs), Real.mul_rpow hq hs]
  rw [h1]; ring

/-- `(x ^ a) ^ b = x ^ (a * b)` for `x ≥ 0`. -/
private lemma rpow_rpow {x : ℝ} (hx : 0 ≤ x) (a b : ℝ) : (x ^ a) ^ b = x ^ (a * b) :=
  (Real.rpow_mul hx a b).symm

/-- `(x ^ a) * (x ^ b) = x ^ (a + b)` for `x > 0`. -/
private lemma rpow_rpow_mul {x : ℝ} (hx : 0 < x) (a b : ℝ) : (x ^ a) * (x ^ b) = x ^ (a + b) :=
  (Real.rpow_add hx a b).symm

theorem mstNuS_sub_mstWideModel_tail_arith (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (l : ℕ) (hl : 1 ≤ l)
    {Atriv C₁ Cc D : ℝ} (hApos : 0 < Atriv) (hC₁ : 0 < C₁) (hCc : 0 < Cc) (hD : 0 < D)
    {δ : ℝ} (hδ : 0 < δ)
    (hcard : ∀ s : ℕ, ((Work.Maximal.mstAnnulus l s).card : ℝ)
      ≤ Cc * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
    {q r θ : ℝ} (hq : 1 < q) (hqr : q < r) (hr : r < 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      Summable (fun j : ℕ =>
        (Atriv * ((s : ℝ) + 1) ^ (-(δ * l))
            * ((Work.Maximal.mstAnnulus l s).card : ℝ)) ^ (1 - θ)
          * (C₁ * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
              * (2 : ℝ) ^ (-((((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ) + (j : ℝ))
                  / (2 * (P.natDegree : ℝ))))) ^ θ)
      ∧ (∑' j : ℕ,
        (Atriv * ((s : ℝ) + 1) ^ (-(δ * l))
            * ((Work.Maximal.mstAnnulus l s).card : ℝ)) ^ (1 - θ)
          * (C₁ * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
              * (2 : ℝ) ^ (-((((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ) + (j : ℝ))
                  / (2 * (P.natDegree : ℝ))))) ^ θ) ≤ 1 := by
  have hdeg : 0 < P.natDegree := by omega
  have hd1 : 1 ≤ P.natDegree := by omega
  have hdR : (0 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast hdeg
  have hθ2 : (0 : ℝ) < 1 - θ := by linarith
  -- the geometric ratio `ρ = 2^{-θ/(2d)}` and the threshold constant `MM`
  set ρ : ℝ := (2 : ℝ) ^ (-(θ / (2 * (P.natDegree : ℝ)))) with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ < 1 := by
    have h1 : (2 : ℝ) ^ (-(θ / (2 * (P.natDegree : ℝ)))) < 1 := by
      rw [Real.rpow_lt_one_iff_of_pos (show (0 : ℝ) < 2 by norm_num)]
      exact Or.inl ⟨by norm_num, by
        have : 0 < θ / (2 * (P.natDegree : ℝ)) := by positivity
        linarith⟩
    rwa [hρdef]
  have h1ρ : 0 < 1 - ρ := by linarith
  set MM : ℝ := (Atriv * Cc) ^ (1 - θ) * (C₁ * D) ^ θ * (1 - ρ)⁻¹ with hMMdef
  have hMMpos : 0 < MM := by
    rw [hMMdef]
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)) (inv_pos.mpr h1ρ)
  obtain ⟨S, hS⟩ := mstKappa_tail_exp_decay P hd hδ l hl hθ0 hθ1 hMMpos
  refine ⟨S, fun s hs => ?_⟩
  set xx : ℝ := (s : ℝ) + 1 with hxxdef
  have hxx1 : 1 ≤ xx := by
    rw [hxxdef]
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  have hxx0 : 0 < xx := lt_of_lt_of_le zero_lt_one hxx1
  have hxxc0 : 0 ≤ xx := le_of_lt hxx0
  set uu : ℝ := xx ^ (1 / 10 : ℝ) with huudef
  have hcard' : ((mstAnnulus l s).card : ℝ) ≤ Cc * Real.exp uu := by
    rw [huudef, hxxdef]; exact hcard s
  set aa : ℝ := (Atriv * xx ^ (-(δ * l)) * ((mstAnnulus l s).card : ℝ)) ^ (1 - θ) with haadef
  set bb : ℝ := C₁ * (D * xx ^ (-(δ * l))) with hbbdef
  have haa0 : 0 ≤ aa := by
    rw [haadef]
    exact Real.rpow_nonneg (mul_nonneg (mul_nonneg hApos.le (Real.rpow_nonneg hxxc0 _))
      (Nat.cast_nonneg _)) _
  have hbb0 : 0 ≤ bb := by rw [hbbdef]; positivity
  obtain ⟨hsumm, htsum⟩ := mstTail_geom_tsum θ hθ0 hθ1 P.natDegree hd1
    (2 ^ Work.BourgainPlan.Maximal.mstKappa P s) aa bb haa0 hbb0
  constructor
  · exact hsumm
  · rw [htsum, ← hρdef]
    -- the two factor bounds
    have hA : aa ≤ (Atriv * Cc) ^ (1 - θ) * (xx ^ (-(δ * l))) ^ (1 - θ)
        * Real.exp ((1 - θ) * uu) := by
      rw [haadef]
      have hbase : Atriv * xx ^ (-(δ * l)) * ((mstAnnulus l s).card : ℝ)
          ≤ Atriv * xx ^ (-(δ * l)) * (Cc * Real.exp uu) :=
        mul_le_mul_of_nonneg_left hcard'
          (mul_nonneg hApos.le (Real.rpow_nonneg hxxc0 _))
      have hstep := Real.rpow_le_rpow
        (mul_nonneg (mul_nonneg hApos.le (Real.rpow_nonneg hxxc0 _)) (Nat.cast_nonneg _))
        hbase hθ2.le
      refine le_trans hstep (le_of_eq ?_)
      rw [show Atriv * xx ^ (-(δ * l)) * (Cc * Real.exp uu)
          = (Atriv * Cc) * xx ^ (-(δ * l)) * Real.exp uu by ring]
      rw [rpow_mul_three (mul_nonneg hApos.le hCc.le) (Real.rpow_nonneg hxxc0 _)
        (Real.exp_pos uu).le]
      congr 1
      rw [← Real.exp_mul]
      congr 1
      ring
    have hB : bb ^ θ = (C₁ * D) ^ θ * (xx ^ (-(δ * l))) ^ θ := by
      rw [hbbdef, show C₁ * (D * xx ^ (-(δ * l))) = (C₁ * D) * xx ^ (-(δ * l)) by ring,
        Real.mul_rpow (mul_nonneg hC₁.le hD.le) (Real.rpow_nonneg hxxc0 _)]
    -- assemble the product bound
    have hkey : aa * bb ^ θ ≤ ((Atriv * Cc) ^ (1 - θ) * (xx ^ (-(δ * l))) ^ (1 - θ)
        * Real.exp ((1 - θ) * uu)) * ((C₁ * D) ^ θ * (xx ^ (-(δ * l))) ^ θ) :=
      mul_le_mul hA (le_of_eq hB) (Real.rpow_nonneg hbb0 θ)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg (mul_nonneg hApos.le hCc.le) _)
          (Real.rpow_nonneg (Real.rpow_nonneg hxxc0 _) _)) (Real.exp_pos _).le)
    have hE2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(θ * ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
        / (2 * (P.natDegree : ℝ)))) := Real.rpow_nonneg (by norm_num) _
    have hkey2 : aa * bb ^ θ
          * (2 : ℝ) ^ (-(θ * ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
              / (2 * (P.natDegree : ℝ)))) * (1 - ρ)⁻¹
        ≤ (((Atriv * Cc) ^ (1 - θ) * (xx ^ (-(δ * l))) ^ (1 - θ) * Real.exp ((1 - θ) * uu))
            * ((C₁ * D) ^ θ * (xx ^ (-(δ * l))) ^ θ))
          * (2 : ℝ) ^ (-(θ * ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
              / (2 * (P.natDegree : ℝ)))) * (1 - ρ)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hE2nn)
        (le_of_lt (inv_pos.mpr h1ρ))
    have hprod : (((Atriv * Cc) ^ (1 - θ) * (xx ^ (-(δ * l))) ^ (1 - θ) * Real.exp ((1 - θ) * uu))
            * ((C₁ * D) ^ θ * (xx ^ (-(δ * l))) ^ θ))
          * (2 : ℝ) ^ (-(θ * ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
              / (2 * (P.natDegree : ℝ)))) * (1 - ρ)⁻¹
        = MM * xx ^ (-(δ * l)) * Real.exp ((1 - θ) * uu)
          * (2 : ℝ) ^ (-(θ * ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
              / (2 * (P.natDegree : ℝ)))) := by
      have hxpow : (xx ^ (-(δ * l))) ^ (1 - θ) * (xx ^ (-(δ * l))) ^ θ = xx ^ (-(δ * l)) := by
        rw [rpow_rpow hxxc0, rpow_rpow hxxc0, rpow_rpow_mul hxx0]
        congr 1
        ring
      have hre : ((Atriv * Cc) ^ (1 - θ) * (xx ^ (-(δ * l))) ^ (1 - θ) * Real.exp ((1 - θ) * uu))
            * ((C₁ * D) ^ θ * (xx ^ (-(δ * l))) ^ θ)
          = ((Atriv * Cc) ^ (1 - θ) * (C₁ * D) ^ θ)
            * ((xx ^ (-(δ * l))) ^ (1 - θ) * (xx ^ (-(δ * l))) ^ θ)
            * Real.exp ((1 - θ) * uu) := by ring
      rw [hre, hxpow, hMMdef]
      ring
    refine le_trans (le_trans hkey2 (le_of_eq hprod)) ?_
    simpa only [hxxdef, huudef] using hS s hs

end

end Work.Maximal
