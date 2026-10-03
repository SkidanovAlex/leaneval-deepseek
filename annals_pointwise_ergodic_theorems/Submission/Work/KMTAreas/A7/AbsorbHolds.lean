/-
# Absorption of the arithmetic factors of the `l₂ = 0` mass bound (KMT §6, Area A7)

Target: `Work.KMTAreas.A7.AbsorbHolds (P : ℤ[X]) : Work.KMTAreas.A7.AbsorbStatement P`
(`Submission/Work/KMTAreas/A7/LoMixedRMassDefs.lean` / `LoMixedRMass.lean`).

`AbsorbStatement P` is the bookkeeping step that turns the per-fibre mass bound of §6
(`FibreMassStatement`) into the `l₂ = 0` mass bound `LoMixedRMassStatement`: for a single scale
`l₁` and an exact-height denominator `q ∈ P_{≤l₁}` it absorbs the arithmetic factors

  `#(ℚ/ℤ)_{≤l₁} · q² · (1 + Sval(P,k₁,k₂)²) · 2^{k₁+dk₂}`   (`d = P.natDegree`)

into the model weight `modelWeight A ρ l₁ 0 k₁ k₂ = (1+L)^A · 2^{A·2^{ρL}}`, `L = max l₁ k₁ k₂`.

Two ingredients are needed, and both are supplied by the library:

* the *cardinality* bound `iw_height_card_le`: `#(ℚ/ℤ)_{≤l} ≤ C₂(ρ)·2^{2^{ρl}}`;
* the *sharp element* bound `iwP_element_le_sharp` of Appendix A:
  `q ≤ 2^{C(ρ)·(1 + l·2^{ρl/2} + l)}` for `q ∈ P_{≤l}`.

The key point is that the crude element bound `q ≤ 2^{C(ρ)2^{ρl}}` (of `iwP_element_le`) is
*not* enough: it would force `A ≥ C(ρ)`, which cannot be uniform in `ρ` (as `ρ → 0` the constant
of the elementary bound blows up like `1/ρ`).  With the sharp bound the total exponent of `2` on
the left is at most

  `2^{ρL} + 2C(ρ)(1 + L·2^{ρL/2} + L) + (3d+3)L + 4 + log₂ C₂(ρ)`,

and `2^{ρL}` dominates each of the remaining terms, so a *fixed* `A` (we take `A = 2`) works for
all `ρ ≤ 1`, with the constant `C(ρ)` supplied by
`Work.KMTAreas.A7.exp_dominates_poly_half`.  The elementary real-variable inequality
`a(1 + L·2^{ρL/2} + L) + bL + c ≤ 2^{ρL} + K` is delegated to that module, and
`Work.KMTAreas.A7.sval_term_bound` handles `(1 + Sval²)·2^{k₁+dk₂}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedRMass

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- `lmaxR l₁ l₂ k₁ k₂` is the maximum of the four parameters, as a real number. -/
lemma lmaxR_eq_top (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂ = ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  simp only [Int.cast_max, Int.cast_natCast, Nat.cast_max]

/-- The value of `lmaxR` at `l₂ = 0`: the maximum of `l₁`, `k₁`, `k₂`. -/
lemma lmaxR_zero_l2 (l₁ k₁ k₂ : ℕ) :
    lmaxR l₁ 0 k₁ k₂ = ((max (max l₁ k₁) k₂ : ℕ) : ℝ) := by
  rw [lmaxR_eq_top, Nat.cast_inj]
  omega

/-- **Absorption of the arithmetic factors of the `l₂ = 0` mass bound.** -/
theorem AbsorbHolds (P : Polynomial ℤ) : Work.KMTAreas.A7.AbsorbStatement P := by
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨C₂₀, hC₂₀pos, hC₂₀⟩ := Work.Analysis.IonescuWainger.iw_height_card_le hρ
  obtain ⟨Cq, hCqpos, hCq⟩ := Work.KMTPlan.A6.iwP_element_le_sharp ρ hρ hρ1
  set C₂ : ℝ := max 1 C₂₀ with hC₂def
  have hC₂1 : (1:ℝ) ≤ C₂ := le_max_left _ _
  have hC₂pos : (0:ℝ) < C₂ := lt_of_lt_of_le one_pos hC₂1
  have hC₂ : ∀ l : ℕ, ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)
      ≤ C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l:ℝ))) := fun l =>
    (hC₂₀ l).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hCqnn : (0:ℝ) ≤ Cq := hCqpos.le
  obtain ⟨K, hK0, hK⟩ := exp_dominates_poly_half ρ hρ hρ1 (2*Cq) (3*((P.natDegree:ℝ)+1)) 4
      (by positivity) (by positivity) (by norm_num)
  refine ⟨C₂ * (2:ℝ)^K, by positivity, ?_⟩
  intro l₁ q k₁ k₂ hq
  set Ln : ℕ := max (max l₁ k₁) k₂ with hLndef
  have hl₁ : l₁ ≤ Ln := by rw [hLndef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hk₁ : k₁ ≤ Ln := by rw [hLndef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hk₂ : k₂ ≤ Ln := by rw [hLndef]; exact le_max_right _ _
  set X : ℝ := Cq * (1 + (l₁:ℝ) * (2:ℝ)^(ρ*(l₁:ℝ)/2) + (l₁:ℝ)) with hXdef
  have hcard : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
      ≤ C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ))) := hC₂ l₁
  have hqR : (q:ℝ) ≤ (2:ℝ)^X := by rw [hXdef]; exact hCq l₁ q hq
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast Work.Analysis.IonescuWainger.pos_of_mem_iwP hq
  have hq2 : (q:ℝ)^2 ≤ (2:ℝ)^(2*X) := by
    have h := pow_le_pow_left₀ hqpos.le hqR 2
    rwa [show ((2:ℝ)^X)^2 = (2:ℝ)^(2*X) from by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring] at h
  have hsv : (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)
      ≤ (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := sval_term_bound P Ln k₁ k₂ hk₁ hk₂
  have hstep1 : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * (q:ℝ)^2
        * (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)
      ≤ (C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)))) * (2:ℝ)^(2*X)
        * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := by
    rw [show ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * (q:ℝ)^2
          * (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)
        = (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * (q:ℝ)^2)
          * ((1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)) from by ring]
    refine mul_le_mul (mul_le_mul hcard hq2 (by positivity) (by positivity)) hsv
      (by positivity) (by positivity)
  have hp1 : (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ))) * (2:ℝ)^(2*X)
      = (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X) :=
    (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
  have hp2 : (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X) * (2:ℝ)^(((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ))
      = (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ)) :=
    (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
  have hnat : (2:ℝ)^(3*(P.natDegree+1)*Ln + 4)
      = (2:ℝ)^(((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ)) :=
    (Real.rpow_natCast (2:ℝ) _).symm
  have hEeq : (C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)))) * (2:ℝ)^(2*X)
        * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4)
      = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ)) := by
    calc (C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)))) * (2:ℝ)^(2*X) * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4)
        = C₂ * ((2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ))) * (2:ℝ)^(2*X)) * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := by
          ring
      _ = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X) * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := by rw [hp1]
      _ = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X)
            * (2:ℝ)^(((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ)) := by rw [hnat]
      _ = C₂ * ((2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X)
            * (2:ℝ)^(((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ))) := by ring
      _ = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ)) := by
          rw [hp2]
  have hcast : (((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ))
      = 3*((P.natDegree:ℝ)+1)*(Ln:ℝ) + 4 := by push_cast; ring
  have hexp : (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ))
      ≤ (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ)) + K) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    have h1 : (2:ℝ)^(ρ*(l₁:ℝ)) ≤ (2:ℝ)^(ρ*(Ln:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have h : (l₁:ℝ) ≤ (Ln:ℝ) := by exact_mod_cast hl₁
        nlinarith [hρ])
    have h2 : 2*X ≤ 2*Cq*(1 + (Ln:ℝ)*(2:ℝ)^(ρ*(Ln:ℝ)/2) + (Ln:ℝ)) := by
      rw [hXdef]
      have hl₁R : (l₁:ℝ) ≤ (Ln:ℝ) := by exact_mod_cast hl₁
      have hy : (2:ℝ)^(ρ*(l₁:ℝ)/2) ≤ (2:ℝ)^(ρ*(Ln:ℝ)/2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ])
      have hprod : (l₁:ℝ) * (2:ℝ)^(ρ*(l₁:ℝ)/2) ≤ (Ln:ℝ) * (2:ℝ)^(ρ*(Ln:ℝ)/2) :=
        mul_le_mul hl₁R hy (by positivity) (by positivity)
      have h1' : 1 + (l₁:ℝ) * (2:ℝ)^(ρ*(l₁:ℝ)/2) + (l₁:ℝ)
          ≤ 1 + (Ln:ℝ) * (2:ℝ)^(ρ*(Ln:ℝ)/2) + (Ln:ℝ) := by linarith
      nlinarith [h1', hCqnn]
    have h3 := hK Ln
    rw [hcast]
    linarith [h1, h2, h3]
  have hfinal : (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ)) + K)
      = (2:ℝ)^K * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ))) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    ring
  have hmodel : Work.KMTAreas.A7.modelWeight 2 ρ l₁ 0 k₁ k₂
      = ((1+(Ln:ℝ))^(2:ℝ)) * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ))) := by
    simp only [Work.KMTAreas.A7.modelWeight, lmaxR_zero_l2, ← hLndef]
  have h1sq : (1:ℝ) ≤ (1+(Ln:ℝ))^(2:ℝ) :=
    Real.one_le_rpow (by linarith : (1:ℝ) ≤ 1 + (Ln:ℝ)) (by norm_num)
  calc ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * (q:ℝ)^2
        * (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)
      ≤ (C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)))) * (2:ℝ)^(2*X)
        * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := hstep1
    _ = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ)) := hEeq
    _ ≤ C₂ * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ)) + K) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = C₂ * (2:ℝ)^K * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ))) := by rw [hfinal]; ring
    _ ≤ C₂ * (2:ℝ)^K * (((1+(Ln:ℝ))^(2:ℝ)) * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_mul_of_one_le_left (by positivity) h1sq
    _ = (C₂ * (2:ℝ)^K) * Work.KMTAreas.A7.modelWeight 2 ρ l₁ 0 k₁ k₂ := by
        rw [hmodel]


end

end Work.KMTAreas.A7
