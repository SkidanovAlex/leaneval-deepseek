
import Mathlib
import Submission.Work.FIArea3.PairDefs6
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.pairSumContent
import Submission.Work.FIArea3.polarBox_tau_avg
import Submission.Work.FIArea3.secondMomentCore
import Submission.Work.FIArea3.pairBracketPrim2
import Submission.Work.FIArea2.absDelta_lt_four_pi
import Submission.Work.FIArea3.polarBox_content_tau_sq_avg

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

lemma absDelta_gPrim_le (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta (gPrim z1) z2 ≤ Work.FIPlan.absDelta z1 z2 := by
  rcases eq_or_ne (gContent z1) 0 with h0 | h0
  · rw [gContent, Nat.gcd_eq_zero_iff] at h0
    have hz : z1 = 0 := Zsqrtd.ext (Int.natAbs_eq_zero.mp h0.1) (Int.natAbs_eq_zero.mp h0.2)
    subst hz
    simp [gPrim, Work.FIPlan.absDelta, Work.FIPlan.Delta]
  · have hpos : 0 < gContent z1 := Nat.pos_of_ne_zero h0
    calc Work.FIPlan.absDelta (gPrim z1) z2
        ≤ gContent z1 * Work.FIPlan.absDelta (gPrim z1) z2 :=
          Nat.le_mul_of_pos_left _ hpos
      _ = Work.FIPlan.absDelta z1 z2 := (absDelta_gContent_mul_gPrim z1 z2).symm

lemma absDelta_gPrim_lt_four_pi {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    (Work.FIPlan.absDelta (gPrim z1) z2 : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := by
  have hle := absDelta_gPrim_le z1 z2
  have hlt := Work.FIArea2.absDelta_lt_four_pi (Pa := Pa) (φ := φ) h1 h2
  have hcast : ((Work.FIPlan.absDelta (gPrim z1) z2 : ℕ) : ℝ)
      ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hle
  linarith

/-- `(1 + L)^4 ≤ 16 L^{2^20-1}` for `L ≥ 1`. -/
lemma logpow_four_le (L : ℝ) (hL : 1 ≤ L) :
    (1 + L) ^ (4 : ℕ) ≤ 16 * L ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
  have h1 : (1 + L) ^ (2 : ℕ) ≤ (2 * L) ^ (2 : ℕ) := by
    apply pow_le_pow_left₀ (by linarith) _ 2
    linarith
  have h2 : (1 + L) ^ (4 : ℕ) = ((1 + L) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
  have h3 : ((2 * L) ^ (2 : ℕ)) ^ (2 : ℕ) = 16 * L ^ (4 : ℕ) := by ring
  have h4 : L ^ (4 : ℕ) ≤ L ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) :=
    pow_le_pow_right₀ hL (by norm_num)
  rw [h2]
  calc ((1 + L) ^ (2 : ℕ)) ^ (2 : ℕ) ≤ ((2 * L) ^ (2 : ℕ)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by positivity) h1 2
    _ = 16 * L ^ (4 : ℕ) := h3
    _ ≤ 16 * L ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by linarith [h4]

/-- `√(c u² L^{2^18}) = √c u L^{2^17}` for `c, u, L ≥ 0`. -/
lemma sqrt_sq_log (c u L : ℝ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hL : 0 ≤ L) :
    Real.sqrt (c * u ^ 2 * L ^ ((2 : ℕ) ^ (18 : ℕ)))
      = Real.sqrt c * u * L ^ ((2 : ℕ) ^ (17 : ℕ)) := by
  have hLp : 0 ≤ L ^ ((2 : ℕ) ^ (17 : ℕ)) := by positivity
  have harg : c * u ^ 2 * L ^ ((2 : ℕ) ^ (18 : ℕ))
      = (Real.sqrt c * u * L ^ ((2 : ℕ) ^ (17 : ℕ))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hc,
      show (L ^ ((2 : ℕ) ^ (17 : ℕ)) : ℝ) ^ 2 = L ^ ((2 : ℕ) ^ (18 : ℕ)) from by
        rw [← pow_mul]
        norm_num]
  rw [harg, Real.sqrt_sq (by positivity)]

theorem pairSumSharp6 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
      (ind : GaussianInt → GaussianInt → ℝ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (∀ z : GaussianInt, ind z z = 0) →
      (∀ z1 z2 : GaussianInt, 0 ≤ ind z1 z2) →
      (∀ z1 z2 : GaussianInt, ind z1 z2 ≤ 1) →
      Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ind z1 z2 * (‖β z1‖ * ‖β z2‖
              * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))))
        ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
  obtain ⟨Ca, hCapos, havg⟩ := polarBox_tau_avg
  obtain ⟨Cm, hCmpos, hsec⟩ := secondMomentCore
  obtain ⟨Cb, hCbpos, hbrk⟩ := pairBracketPrim2
  obtain ⟨Cc, hCcpos, hcon⟩ := polarBox_content_tau_sq_avg
  refine ⟨144 * Ca ^ 2 + Cb * Real.sqrt (Cm * Cc), by positivity, ?_⟩
  intro Pa φ β ind hβ hdiag hnn hle1 hu
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with huD
  set B : Finset GaussianInt := polarBoxFinset Pa φ with hB
  have hu0 : 0 ≤ u := by rw [huD]; exact mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  have hu1 : 1 ≤ u := by
    rw [huD]; exact le_trans (Real.one_le_rpow Pa.hN1 (by norm_num)) hu
  have hlog1 : 1 ≤ Real.log Pa.N := one_le_log_N_of_sharp hu
  have hlog0 : 0 ≤ Real.log Pa.N := le_trans zero_le_one hlog1
  have hBsub : B ⊆ Work.FITop.boxN Pa := polarBoxFinset_subset Pa φ
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  -- u^2 = theta^2 * N
  have hu2 : u ^ 2 = Pa.θ ^ 2 * Pa.N := by rw [huD, mul_pow, Real.sq_sqrt (by linarith)]
  have hu4 : u ^ (4 : ℕ) = Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ) := by
    rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hu2]; ring
  have hθ4le : Pa.θ ^ (4:ℕ) * Pa.N ^ (2:ℕ) ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3:ℕ) * Pa.N ^ (2:ℕ) := by
    have h1 : Pa.θ ^ (4:ℕ) = Pa.θ ^ (3:ℕ) * Pa.θ := by ring
    have h2 : Pa.θ ≤ Pa.τ⁻¹ + Pa.θ := by
      have : 0 ≤ Pa.τ⁻¹ := by
        have hx1 : (1:ℝ) < (Pa.x:ℝ) := by
          have h2' : 1 < Pa.x := lt_of_lt_of_le (by norm_num) Pa.hx
          exact_mod_cast h2'
        have hlogx : 0 < Real.log (Pa.x:ℝ) := Real.log_pos hx1
        have hτpos : 0 < Pa.τ := lt_of_lt_of_le (Real.rpow_pos_of_pos hlogx _) Pa.hτ1
        exact inv_nonneg.mpr hτpos.le
      linarith
    calc Pa.θ ^ (4:ℕ) * Pa.N ^ (2:ℕ) = Pa.θ ^ (3:ℕ) * Pa.N ^ (2:ℕ) * Pa.θ := by rw [h1]; ring
      _ ≤ Pa.θ ^ (3:ℕ) * Pa.N ^ (2:ℕ) * (Pa.τ⁻¹ + Pa.θ) := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3:ℕ) * Pa.N ^ (2:ℕ) := by ring
  -- (1) reduce the double sum over `boxN` to the double sum over `B`
  have hβ0 : ∀ z ∈ Work.FITop.boxN Pa, z ∉ B → β z = 0 := by
    intro z hz hzB
    by_contra h
    exact hzB (by
      rw [hB, mem_polarBoxFinset]
      exact ⟨hz, (hβ.2 z h).1⟩)
  have key1 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        ind z1 z2 * (‖β z1‖ * ‖β z2‖
            * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))))
      = ∑ z1 ∈ B, ∑ z2 ∈ B,
        ind z1 z2 * (‖β z1‖ * ‖β z2‖
            * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))) := by
    have e1 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        ind z1 z2 * (‖β z1‖ * ‖β z2‖
            * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))))
        = ∑ z1 ∈ B, ∑ z2 ∈ Work.FITop.boxN Pa,
          ind z1 z2 * (‖β z1‖ * ‖β z2‖
              * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))) := by
      refine (Finset.sum_subset hBsub ?_).symm
      intro z hz hzB
      rw [hβ0 z hz hzB]; simp
    rw [e1]
    refine Finset.sum_congr rfl fun z1 hz1 => ?_
    refine (Finset.sum_subset hBsub ?_).symm
    intro z hz hzB
    rw [hβ0 z hz hzB]; simp
  rw [key1]
  -- (2) pointwise bound and the split
  have hpt : ∀ z1 ∈ B, ∀ z2 ∈ B,
      ind z1 z2 * (‖β z1‖ * ‖β z2‖ * (1 + pairDel z1 z2))
        ≤ pairTau z1 * pairTau z2 * (1 + pairDel z1 z2) := by
    intro z1 _ z2 _
    have h1 : ‖β z1‖ ≤ pairTau z1 := hβ.1 z1
    have h2 : ‖β z2‖ ≤ pairTau z2 := hβ.1 z2
    have h3 : (0 : ℝ) ≤ 1 + pairDel z1 z2 := one_add_pairDel_nonneg z1 z2
    have h5 : ‖β z1‖ * ‖β z2‖ ≤ pairTau z1 * pairTau z2 :=
      mul_le_mul h1 h2 (norm_nonneg _) (pairTau_nonneg z1)
    have h6 : ‖β z1‖ * ‖β z2‖ * (1 + pairDel z1 z2)
        ≤ pairTau z1 * pairTau z2 * (1 + pairDel z1 z2) :=
      mul_le_mul_of_nonneg_right h5 h3
    have hS0 : 0 ≤ ‖β z1‖ * ‖β z2‖ * (1 + pairDel z1 z2) :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h3
    calc ind z1 z2 * (‖β z1‖ * ‖β z2‖ * (1 + pairDel z1 z2))
        ≤ 1 * (‖β z1‖ * ‖β z2‖ * (1 + pairDel z1 z2)) :=
          mul_le_mul_of_nonneg_right (hle1 z1 z2) hS0
      _ = ‖β z1‖ * ‖β z2‖ * (1 + pairDel z1 z2) := one_mul _
      _ ≤ pairTau z1 * pairTau z2 * (1 + pairDel z1 z2) := h6
  have hstep : (∑ z1 ∈ B, ∑ z2 ∈ B,
        ind z1 z2 * (‖β z1‖ * ‖β z2‖
            * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))))
      ≤ ∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * (1 + pairDel z1 z2) :=
    Finset.sum_le_sum fun z1 hz1 => Finset.sum_le_sum fun z2 hz2 => hpt z1 hz1 z2 hz2
  refine hstep.trans ?_
  -- (3) split the sum
  set A : ℝ := ∑ z ∈ B, pairTau z with hA
  set L : ℝ := Real.log Pa.N with hLdef
  have hL1 : 1 ≤ L := hlog1
  have hL0 : 0 ≤ L := hlog0
  have hsplit : (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * (1 + pairDel z1 z2))
      = A ^ 2 + ∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * pairDel z1 z2 := by
    have h1 : ∀ z1 ∈ B, ∀ z2 ∈ B,
        pairTau z1 * pairTau z2 * (1 + pairDel z1 z2)
          = pairTau z1 * pairTau z2 + pairTau z1 * pairTau z2 * pairDel z1 z2 := by
      intro z1 _ z2 _; ring
    have h2 : (∑ z1 ∈ B, ∑ z2 ∈ B,
          (pairTau z1 * pairTau z2 + pairTau z1 * pairTau z2 * pairDel z1 z2))
        = (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2)
          + ∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * pairDel z1 z2 := by
      simp only [Finset.sum_add_distrib]
    have h3 : (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2) = A ^ 2 := by
      rw [hA, pow_two, Finset.sum_mul_sum]
    calc (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * (1 + pairDel z1 z2))
        = ∑ z1 ∈ B, ∑ z2 ∈ B,
            (pairTau z1 * pairTau z2 + pairTau z1 * pairTau z2 * pairDel z1 z2) :=
          Finset.sum_congr rfl fun z1 hz1 => Finset.sum_congr rfl fun z2 hz2 => h1 z1 hz1 z2 hz2
      _ = (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2)
            + ∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * pairDel z1 z2 := h2
      _ = A ^ 2 + ∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * pairDel z1 z2 := by rw [h3]
  rw [hsplit]
  -- (4) the `1`-part
  have hA1 : A ≤ Ca * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)
      * (1 + Real.log Pa.N) ^ (2 : ℕ) := by
    rw [hA, hB]; exact havg Pa φ hu
  have hS1 : A ^ 2 ≤ 144 * Ca ^ 2 * u ^ (4 : ℕ) * L ^ (((2:ℕ)^(20:ℕ)) - 1) := by
    have hTle : Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1 ≤ 3 * u ^ 2 := by
      have h1 : Pa.θ * Real.sqrt Pa.N ≤ u ^ 2 := by rw [hu2]; nlinarith [hu1]
      have h2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith [hu1]
      rw [hu2]; linarith
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun z _ => pairTau_nonneg z
    have hstep1 : A ≤ Ca * (3 * u ^ 2) * (1 + L) ^ (2 : ℕ) := by
      have h1 : Ca * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * (1 + L) ^ (2 : ℕ)
          ≤ Ca * (3 * u ^ 2) * (1 + L) ^ (2 : ℕ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hTle hCapos.le
      have hA1' : A ≤ Ca * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * (1 + L) ^ (2 : ℕ) := by
        rw [hLdef]; exact hA1
      linarith [hA1', h1]
    have hstep2 : (Ca * (3 * u ^ 2) * (1 + L) ^ (2 : ℕ)) ^ (2 : ℕ)
        = 9 * Ca ^ 2 * u ^ (4 : ℕ) * ((1 + L) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    have hstep3 : ((1 + L) ^ (2 : ℕ)) ^ (2 : ℕ) = (1 + L) ^ (4 : ℕ) := by ring
    have hCa0 : 0 ≤ Ca := hCapos.le
    calc A ^ 2 ≤ (Ca * (3 * u ^ 2) * (1 + L) ^ (2 : ℕ)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hA0 hstep1 2
      _ = 9 * Ca ^ 2 * u ^ (4 : ℕ) * (1 + L) ^ (4 : ℕ) := by rw [hstep2, hstep3]
      _ ≤ 9 * Ca ^ 2 * u ^ (4 : ℕ) * (16 * L ^ (((2:ℕ)^(20:ℕ)) - 1)) := by
          refine mul_le_mul_of_nonneg_left (logpow_four_le L hL1) (by positivity)
      _ = 144 * Ca ^ 2 * u ^ (4 : ℕ) * L ^ (((2:ℕ)^(20:ℕ)) - 1) := by ring
  -- (5) the `τ Δ`-part
  have hS2 : (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * pairDel z1 z2)
      ≤ Cb * Real.sqrt (Cm * Cc) * u ^ (4 : ℕ) * L ^ (((2:ℕ)^(20:ℕ)) - 1) := by
    have hbracket : ∀ z1 ∈ B,
        (∑ z2 ∈ B, pairTau z2 * pairDel z1 z2)
          ≤ Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ)) * ((gContent z1).divisors.card : ℝ) := by
      intro z1 hz1
      rw [hB] at hz1
      have hin : Work.FITop3.InPolarBox Pa φ z1 := (mem_polarBoxFinset.mp hz1).2
      have hz1ne : z1 ≠ 0 := by
        intro h
        rw [h] at hin
        have hz : (Work.FIPlan.gnorm (0 : GaussianInt) : ℝ) = 0 := by
          simp [Work.FIPlan.gnorm]
        linarith [hin.2.1, hN1, hz]
      have hbr := hbrk Pa φ (gPrim z1) hu (coprime_gPrimNe hz1ne) (fun z hz =>
        absDelta_gPrim_lt_four_pi hin (mem_polarBoxFinset.mp hz).2)
      have h1 : (∑ z2 ∈ B, pairTau z2 * pairDel z1 z2)
          ≤ ∑ z2 ∈ B,
              pairTau z2 * (((gContent z1).divisors.card : ℝ) * pairDel (gPrim z1) z2) := by
        refine Finset.sum_le_sum fun z2 _ => ?_
        have h2 : pairDel z1 z2 ≤ ((gContent z1).divisors.card : ℝ) * pairDel (gPrim z1) z2 :=
          tau_absDelta_le_mul z1 z2
        have h3 : 0 ≤ pairTau z2 := pairTau_nonneg z2
        nlinarith [h2, h3]
      have h4 : (∑ z2 ∈ B,
            pairTau z2 * (((gContent z1).divisors.card : ℝ) * pairDel (gPrim z1) z2))
          = ((gContent z1).divisors.card : ℝ)
              * ∑ z2 ∈ B, pairTau z2 * pairDel (gPrim z1) z2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z2 _ => by ring
      rw [h4] at h1
      have h5 : (∑ z2 ∈ B, pairTau z2 * pairDel (gPrim z1) z2)
          ≤ Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ)) := by
        rw [hB, hLdef, huD]
        exact hbr
      have h6 : 0 ≤ ((gContent z1).divisors.card : ℝ) := by positivity
      have h7 : ((gContent z1).divisors.card : ℝ)
            * (∑ z2 ∈ B, pairTau z2 * pairDel (gPrim z1) z2)
          ≤ ((gContent z1).divisors.card : ℝ) * (Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ))) :=
        mul_le_mul_of_nonneg_left h5 h6
      calc (∑ z2 ∈ B, pairTau z2 * pairDel z1 z2)
          ≤ ((gContent z1).divisors.card : ℝ)
              * ∑ z2 ∈ B, pairTau z2 * pairDel (gPrim z1) z2 := h1
        _ ≤ ((gContent z1).divisors.card : ℝ) * (Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ))) := h7
        _ = Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ)) * ((gContent z1).divisors.card : ℝ) := by ring
    have hmix : (∑ z1 ∈ B, pairTau z1 * ((gContent z1).divisors.card : ℝ))
        ≤ Real.sqrt (Cm * Cc) * u ^ 2 * L ^ ((2:ℕ)^(18:ℕ)) := by
      have hCS := Real.sum_mul_le_sqrt_mul_sqrt B (fun z => pairTau z)
        (fun z => ((gContent z).divisors.card : ℝ))
      have hs1 : (∑ z ∈ B, pairTau z ^ 2) ≤ Cm * u ^ 2 * L ^ ((2:ℕ)^(18:ℕ)) := by
        rw [hB, hLdef, huD]; exact hsec Pa φ hu
      have hs2 : (∑ z ∈ B, (((gContent z).divisors.card : ℝ)) ^ 2)
          ≤ Cc * u ^ 2 * L ^ ((2:ℕ)^(18:ℕ)) := by
        rw [hB, hLdef, huD]; exact hcon Pa φ hu
      have hr1 : Real.sqrt (∑ z ∈ B, pairTau z ^ 2)
          ≤ Real.sqrt Cm * u * L ^ ((2:ℕ)^(17:ℕ)) := by
        have := Real.sqrt_le_sqrt hs1
        rwa [sqrt_sq_log Cm u L hCmpos.le hu0 hL0] at this
      have hr2 : Real.sqrt (∑ z ∈ B, (((gContent z).divisors.card : ℝ)) ^ 2)
          ≤ Real.sqrt Cc * u * L ^ ((2:ℕ)^(17:ℕ)) := by
        have := Real.sqrt_le_sqrt hs2
        rwa [sqrt_sq_log Cc u L hCcpos.le hu0 hL0] at this
      have hcomb : (Real.sqrt Cm * u * L ^ ((2:ℕ)^(17:ℕ)))
            * (Real.sqrt Cc * u * L ^ ((2:ℕ)^(17:ℕ)))
          = Real.sqrt (Cm * Cc) * u ^ 2 * L ^ ((2:ℕ)^(18:ℕ)) := by
        rw [Real.sqrt_mul hCmpos.le]
        rw [show (Real.sqrt Cm * u * L ^ ((2:ℕ)^(17:ℕ)))
              * (Real.sqrt Cc * u * L ^ ((2:ℕ)^(17:ℕ)))
            = (Real.sqrt Cm * Real.sqrt Cc) * (u * u)
                * (L ^ ((2:ℕ)^(17:ℕ)) * L ^ ((2:ℕ)^(17:ℕ))) by ring]
        rw [← pow_two u, ← pow_add, show ((2:ℕ)^(17:ℕ)) + ((2:ℕ)^(17:ℕ)) = ((2:ℕ)^(18:ℕ)) from by norm_num]
      calc (∑ z1 ∈ B, pairTau z1 * ((gContent z1).divisors.card : ℝ))
          ≤ Real.sqrt (∑ z ∈ B, pairTau z ^ 2)
              * Real.sqrt (∑ z ∈ B, (((gContent z).divisors.card : ℝ)) ^ 2) := hCS
        _ ≤ (Real.sqrt Cm * u * L ^ ((2:ℕ)^(17:ℕ)))
              * (Real.sqrt Cc * u * L ^ ((2:ℕ)^(17:ℕ))) :=
            mul_le_mul hr1 hr2 (Real.sqrt_nonneg _) (by positivity)
        _ = Real.sqrt (Cm * Cc) * u ^ 2 * L ^ ((2:ℕ)^(18:ℕ)) := hcomb
    have hfinal : (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * pairDel z1 z2)
        ≤ (∑ z1 ∈ B, pairTau z1 * ((gContent z1).divisors.card : ℝ))
            * (Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ))) := by
      calc (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * pairDel z1 z2)
          = ∑ z1 ∈ B, pairTau z1 * ∑ z2 ∈ B, pairTau z2 * pairDel z1 z2 := by
            refine Finset.sum_congr rfl fun z1 _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z2 _ => by ring
        _ ≤ ∑ z1 ∈ B, pairTau z1
              * (Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ)) * ((gContent z1).divisors.card : ℝ)) := by
            refine Finset.sum_le_sum fun z1 hz1 => ?_
            exact mul_le_mul_of_nonneg_left (hbracket z1 hz1) (pairTau_nonneg z1)
        _ = (∑ z1 ∈ B, pairTau z1 * ((gContent z1).divisors.card : ℝ))
              * (Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ))) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun z1 _ => by ring
    have hLp0 : 0 ≤ L ^ ((2:ℕ)^(19:ℕ)) := by positivity
    have hb0 : 0 ≤ Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ)) := by positivity
    calc (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * pairDel z1 z2)
        ≤ (∑ z1 ∈ B, pairTau z1 * ((gContent z1).divisors.card : ℝ))
            * (Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ))) := hfinal
      _ ≤ (Real.sqrt (Cm * Cc) * u ^ 2 * L ^ ((2:ℕ)^(18:ℕ)))
            * (Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ))) :=
          mul_le_mul_of_nonneg_right hmix hb0
      _ ≤ Cb * Real.sqrt (Cm * Cc) * u ^ (4 : ℕ) * L ^ (((2:ℕ)^(20:ℕ)) - 1) := by
          have hexp : ((2:ℕ)^(18:ℕ)) + ((2:ℕ)^(19:ℕ)) ≤ ((2:ℕ)^(20:ℕ)) - 1 := by norm_num
          have hp : L ^ (((2:ℕ)^(18:ℕ)) + ((2:ℕ)^(19:ℕ))) ≤ L ^ (((2:ℕ)^(20:ℕ)) - 1) :=
            pow_le_pow_right₀ hL1 hexp
          have heq : (Real.sqrt (Cm * Cc) * u ^ 2 * L ^ ((2:ℕ)^(18:ℕ)))
                * (Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ)))
              = Cb * Real.sqrt (Cm * Cc) * u ^ (4 : ℕ)
                  * L ^ (((2:ℕ)^(18:ℕ)) + ((2:ℕ)^(19:ℕ))) := by
            rw [show (Real.sqrt (Cm * Cc) * u ^ 2 * L ^ ((2:ℕ)^(18:ℕ)))
                  * (Cb * u ^ 2 * L ^ ((2:ℕ)^(19:ℕ)))
                = Cb * Real.sqrt (Cm * Cc) * (u ^ 2 * u ^ 2)
                    * (L ^ ((2:ℕ)^(18:ℕ)) * L ^ ((2:ℕ)^(19:ℕ))) by ring,
              ← pow_add, ← pow_add]
          rw [heq]
          exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hsum : A ^ 2 + (∑ z1 ∈ B, ∑ z2 ∈ B, pairTau z1 * pairTau z2 * pairDel z1 z2)
      ≤ (144 * Ca ^ 2 + Cb * Real.sqrt (Cm * Cc)) * u ^ (4 : ℕ)
          * (Real.log Pa.N) ^ (((2:ℕ)^(20:ℕ)) - 1) := by
    linarith [hS1, hS2]
  refine hsum.trans ?_
  have hfin : u ^ (4 : ℕ) * (Real.log Pa.N) ^ (((2:ℕ)^(20:ℕ)) - 1)
      ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (((2:ℕ)^(20:ℕ)) - 1) := by
    have hL0 : 0 ≤ (Real.log Pa.N) ^ (((2:ℕ)^(20:ℕ)) - 1) := by positivity
    rw [hu4]
    exact mul_le_mul_of_nonneg_right hθ4le hL0
  have hK0 : 0 ≤ 144 * Ca ^ 2 + Cb * Real.sqrt (Cm * Cc) := by positivity
  calc (144 * Ca ^ 2 + Cb * Real.sqrt (Cm * Cc)) * u ^ (4 : ℕ)
        * (Real.log Pa.N) ^ (((2:ℕ)^(20:ℕ)) - 1)
      = (144 * Ca ^ 2 + Cb * Real.sqrt (Cm * Cc))
          * (u ^ (4 : ℕ) * (Real.log Pa.N) ^ (((2:ℕ)^(20:ℕ)) - 1)) := by ring
    _ ≤ (144 * Ca ^ 2 + Cb * Real.sqrt (Cm * Cc))
          * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
              * (Real.log Pa.N) ^ (((2:ℕ)^(20:ℕ)) - 1)) :=
        mul_le_mul_of_nonneg_left hfin hK0
    _ = (144 * Ca ^ 2 + Cb * Real.sqrt (Cm * Cc)) * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ)
          * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ (((2:ℕ)^(20:ℕ)) - 1) := by ring

end
end Work.FIArea3
