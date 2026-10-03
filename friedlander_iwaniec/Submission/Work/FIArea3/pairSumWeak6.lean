import Mathlib
import Submission.Work.FIArea3.PairDefs6
import Submission.Work.FIArea3.pairSumCrude6
import Submission.Work.FIArea3.pairSumSharp6
import Submission.Work.FIArea3.polarBoxCardLeOne

set_option autoImplicit false

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- On the `β`-support of an `IsBoxCoeff` coefficient, `(z,z)=1` is impossible: `(z,z)=1` forces
`z ∣ 1`, hence `|z|² = 1`, but the support has `|z|² > N ≥ 1`.  So the diagonal never contributes
to the pair sum. -/
lemma not_gaussCoprime_self_of_isBoxCoeff {Pa : Work.FITop.Params} {φ : ℝ}
    {β : GaussianInt → ℂ} (hβ : Work.FITop3.IsBoxCoeff Pa φ β) {z : GaussianInt}
    (hz : β z ≠ 0) : ¬ Work.FIPlan.GaussCoprime z z := by
  intro hcop
  obtain ⟨x, y, hxy⟩ := hcop
  have hdvd : z ∣ (1 : GaussianInt) := ⟨x + y, by rw [← hxy]; ring⟩
  obtain ⟨v, hv⟩ := hdvd
  have hgm : Work.FIPlan.gnorm (z * v) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm v := by
    simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]
  have h1 : Work.FIPlan.gnorm ((1 : GaussianInt)) = 1 := by
    simp only [Work.FIPlan.gnorm, Zsqrtd.norm_one, Int.natAbs_one]
  have hgn : Work.FIPlan.gnorm z * Work.FIPlan.gnorm v = 1 := by
    have h2 := hgm
    rw [← hv, h1] at h2
    exact h2.symm
  have hz1 : Work.FIPlan.gnorm z = 1 := Nat.eq_one_of_mul_eq_one_right hgn
  have hbox := (hβ.2 z hz).1
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hgt : (1 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith [hbox.2.1]
  rw [hz1] at hgt
  norm_num at hgt

theorem pairSumWeak6 : Work.FIArea3.PairSumWeak6 := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := pairSumCrude6
  obtain ⟨C₂, hC₂pos, hC₂⟩ := pairSumSharp6
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁pos (le_max_left _ _), ?_⟩
  intro Pa φ β hβ
  set ind : GaussianInt → GaussianInt → ℝ :=
    fun z1 z2 => if Work.FIPlan.GaussCoprime z1 z2 ∧ z1 ≠ z2 then (1 : ℝ) else 0 with hind
  have hself : ∀ z, ind z z = 0 := by
    intro z; rw [hind]; exact if_neg (fun h => h.2 rfl)
  have hnn : ∀ z1 z2, 0 ≤ ind z1 z2 := by
    intro z1 z2; simp only [hind]; split_ifs <;> norm_num
  have hle1 : ∀ z1 z2, ind z1 z2 ≤ 1 := by
    intro z1 z2; simp only [hind]; split_ifs <;> norm_num
  have hstep : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          ‖β z1‖ * ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
        else 0))
      ≤ (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ind z1 z2 * (‖β z1‖ * ‖β z2‖ *
            (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))) := by
    refine Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => ?_))
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hc]
      by_cases he : z1 = z2
      · subst he
        have hb : β z1 = 0 := by
          by_contra hb'
          exact not_gaussCoprime_self_of_isBoxCoeff hβ hb' hc
        simp [hb]
      · have h1 : ind z1 z2 = 1 := by
          rw [hind]; exact if_pos ⟨hc, he⟩
        rw [h1, one_mul]
    · rw [if_neg hc]
      have h0 : ind z1 z2 = 0 := by
        rw [hind]; exact if_neg (fun h => hc h.1)
      rw [h0, zero_mul]
  have hK : (0 : ℝ) ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
      * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
    have hlogx : (0 : ℝ) < Real.log (Pa.x : ℝ) :=
      Real.log_pos (by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) Pa.hx))
    have hτpos : (0 : ℝ) < Pa.τ :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hlogx _) Pa.hτ1
    have h4 : (0 : ℝ) ≤ Pa.τ⁻¹ + Pa.θ := by
      have h := inv_pos.mpr hτpos
      linarith [le_of_lt h, le_of_lt Pa.hθ0]
    have h1 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
    have h2 : (0 : ℝ) ≤ Pa.N ^ (2 : ℕ) := sq_nonneg _
    have h3 : (0 : ℝ) ≤ Pa.θ ^ (3 : ℕ) := pow_nonneg (le_of_lt Pa.hθ0) _
    positivity
  have hCbound : ∀ C : ℝ, C ≤ max C₁ C₂ →
      C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
        * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)
      ≤ max C₁ C₂ * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
        * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
    intro C hC
    calc C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)
        = C * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)) := by ring
      _ ≤ max C₁ C₂ * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)) :=
          mul_le_mul_of_nonneg_right hC hK
      _ = max C₁ C₂ * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by ring
  by_cases hu : Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8)
  · by_cases h10 : Pa.θ * Real.sqrt Pa.N < 1 / 10
    · have hcard := polarBoxCardLeOne Pa φ h10
      have hzero : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ind z1 z2 * (‖β z1‖ * ‖β z2‖ *
            (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))) = 0 := by
        set S := (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0) with hS
        have hSsub : S ⊆ polarBoxFinset Pa φ := by
          intro z hz
          rw [hS, Finset.mem_filter] at hz
          rw [mem_polarBoxFinset]
          exact ⟨hz.1, (hβ.2 z hz.2).1⟩
        have hScard : S.card ≤ 1 := le_trans (Finset.card_le_card hSsub) hcard
        have hinner : ∀ z1 : GaussianInt,
            (∑ z2 ∈ Work.FITop.boxN Pa,
                ind z1 z2 * (‖β z1‖ * ‖β z2‖ *
                  (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))))
              = ∑ z2 ∈ S,
                ind z1 z2 * (‖β z1‖ * ‖β z2‖ *
                  (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))) := by
          intro z1
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro z2 hz2 hnot
          have hb : β z2 = 0 := by
            by_contra hcon
            exact hnot (Finset.mem_filter.mpr ⟨hz2, hcon⟩)
          simp [hb]
        have houter : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ S,
              ind z1 z2 * (‖β z1‖ * ‖β z2‖ *
                (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))))
            = ∑ z1 ∈ S, ∑ z2 ∈ S,
              ind z1 z2 * (‖β z1‖ * ‖β z2‖ *
                (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))) := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro z1 hz1 hnot
          have hb : β z1 = 0 := by
            by_contra hcon
            exact hnot (Finset.mem_filter.mpr ⟨hz1, hcon⟩)
          rw [Finset.sum_eq_zero]
          intro z2 _
          simp [hb]
        rw [Finset.sum_congr rfl (fun z1 _ => hinner z1), houter]
        rcases Finset.eq_empty_or_nonempty S with hS0 | ⟨z0, hz0⟩
        · rw [hS0]; simp
        · have hSeq : S = {z0} := by
            rw [Finset.eq_singleton_iff_unique_mem]
            exact ⟨hz0, fun b hb => Finset.card_le_one.mp hScard b hb z0 hz0⟩
          rw [hSeq]
          have : ind z0 z0 = 0 := hself z0
          simp [this]
      rw [hzero] at hstep
      have hCn : (0 : ℝ) ≤ max C₁ C₂ := le_of_lt (lt_of_lt_of_le hC₁pos (le_max_left _ _))
      have h4 : (0 : ℝ) ≤ Pa.τ⁻¹ + Pa.θ := by
        have hlogx : (0 : ℝ) < Real.log (Pa.x : ℝ) :=
          Real.log_pos (by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) Pa.hx))
        have hτpos : (0 : ℝ) < Pa.τ :=
          lt_of_lt_of_le (Real.rpow_pos_of_pos hlogx _) Pa.hτ1
        have h := inv_pos.mpr hτpos
        linarith [le_of_lt h, le_of_lt Pa.hθ0]
      have h1 : (0 : ℝ) ≤ (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) :=
        pow_nonneg (Real.log_nonneg Pa.hN1) _
      have h2 : (0 : ℝ) ≤ Pa.N ^ (2 : ℕ) := sq_nonneg _
      have h3 : (0 : ℝ) ≤ Pa.θ ^ (3 : ℕ) := pow_nonneg (le_of_lt Pa.hθ0) _
      exact hstep.trans (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCn h4) h3) h2) h1)
    · refine (hstep.trans (hC₁ Pa φ β ind hβ hself hnn hle1 (not_lt.mp h10) hu)).trans ?_
      exact hCbound C₁ (le_max_left _ _)
  · refine (hstep.trans (hC₂ Pa φ β ind hβ hself hnn hle1 (le_of_lt (not_le.mp hu)))).trans ?_
    exact hCbound C₂ (le_max_right _ _)

end

end Work.FIArea3
