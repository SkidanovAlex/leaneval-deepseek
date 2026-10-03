/-
# The fibre mass bound: the integration by parts, the summation and the assembly

This module assembles the fibre mass bound of §6 from
* the Leibniz expansion and the pointwise weighted bound (`FibreMassAux`),
* the sharp two-radii `L¹`-bound for the derivatives of the symbol (`fibreMass_hbd`),
* the `ℓ¹`-summation over the frequency lattice (`Work.KMTAreas.A7.hiCrudeTsum`),
* the comparison of the two constants (`fibreMass_const_compare`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FibreMassHbd

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

theorem fibreInt_eq_kf (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ : Work.Analysis.IonescuWainger.Circle) (p₁ p₂ : ℤ) :
    fibreInt P N k₁ k₂ α₁ p₁ p₂
      = kf (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
          * weylAvg P N α₁ 0 a b) p₁ p₂ := by
  obtain ⟨hsm, hc⟩ := contDiff_hasCompactSupport_fibreSymbol P N k₁ k₂ α₁ 0
  have hint : Integrable (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2
      * weylAvg P N α₁ 0 z.1 z.2) :=
    integrable_dp (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
      * weylAvg P N α₁ 0 a b) 0 0 (hsm.of_le (by norm_num)) hc
  rw [kf_eq_kfX (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
    * weylAvg P N α₁ 0 a b) p₁ p₂ hint]
  simp only [kfX, fibreInt]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only [ee_neg_add]
  ring

/-! ## §7  The integration-by-parts identity -/

theorem kf_dp_symbol (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    ∀ (i₁ i₂ : ℕ), i₁ ≤ 2 → i₂ ≤ 2 → ∀ (q₁ q₂ : ℤ),
      kf (Work.KMTPlan.A6.dp i₁ i₂ (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
          * weylAvg P N α₁ α₂ a b)) q₁ q₂
        = (2 * (Real.pi : ℂ) * Complex.I * (q₁ : ℂ)) ^ i₁
          * (2 * (Real.pi : ℂ) * Complex.I * (q₂ : ℂ)) ^ i₂
          * kf (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
              * weylAvg P N α₁ α₂ a b) q₁ q₂ := by
  obtain ⟨hsm, hc⟩ := contDiff_hasCompactSupport_fibreSymbol P N k₁ k₂ α₁ α₂
  intro i₁ i₂ hi₁ hi₂ q₁ q₂
  have hsm00 : ContDiff ℝ (↑(0 : ℕ) + ↑(0 : ℕ)) (fun p : ℝ × ℝ => varphiN N k₁ p.1
      * varphitildeN P.natDegree N k₂ p.2 * weylAvg P N α₁ α₂ p.1 p.2) :=
    hsm.of_le (by norm_num)
  have hsm0j : ContDiff ℝ (↑i₂) (fun p : ℝ × ℝ => varphiN N k₁ p.1
      * varphitildeN P.natDegree N k₂ p.2 * weylAvg P N α₁ α₂ p.1 p.2) :=
    hsm.of_le (by exact_mod_cast (by omega : i₂ ≤ 4))
  have hsmj : ContDiff ℝ (↑(i₁ + i₂)) (fun p : ℝ × ℝ => varphiN N k₁ p.1
      * varphitildeN P.natDegree N k₂ p.2 * weylAvg P N α₁ α₂ p.1 p.2) :=
    hsm.of_le (by exact_mod_cast (by omega : i₁ + i₂ ≤ 4))
  exact kf_dp (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
      * weylAvg P N α₁ α₂ a b) i₁ i₂ q₁ q₂
    (integrable_dp (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
      * weylAvg P N α₁ α₂ a b) 0 0 hsm00 hc)
    (integrable_dp (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
      * weylAvg P N α₁ α₂ a b) 0 i₂ (hsm.of_le (by exact_mod_cast (by omega : 0 + i₂ ≤ 4))) hc)
    (integrable_dp (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
      * weylAvg P N α₁ α₂ a b) i₁ i₂ hsmj hc)
    (fun x => Work.KMTPlan.A6.cdp_fiber₂ (fun a b => varphiN N k₁ a
      * varphitildeN P.natDegree N k₂ b * weylAvg P N α₁ α₂ a b) i₂ hsm0j x)
    (fun x => compSupp_fiber_snd (fun z : ℝ × ℝ => varphiN N k₁ z.1
      * varphitildeN P.natDegree N k₂ z.2 * weylAvg P N α₁ α₂ z.1 z.2) hc x)
    (fun y => Work.KMTPlan.A6.cdp_fiber₁ (fun a b => Work.KMTPlan.A6.dp2 i₂
      (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
        * weylAvg P N α₁ α₂ a b) a b) i₁
      (Work.KMTPlan.A6.cdp_contDiff_dp2_iter (fun a b => varphiN N k₁ a
        * varphitildeN P.natDegree N k₂ b * weylAvg P N α₁ α₂ a b) i₁ i₂ hsmj) y)
    (fun y => compSupp_iteratedDeriv_fiber (fun z : ℝ × ℝ => varphiN N k₁ z.1
      * varphitildeN P.natDegree N k₂ z.2 * weylAvg P N α₁ α₂ z.1 z.2) hc i₂ y)

/-! ## §8  The pointwise bound for the Fourier coefficients -/

theorem kf_pointwise_bound (P : Polynomial ℤ) (N q k₁ k₂ : ℕ)
    (α₁ : Work.Analysis.IonescuWainger.Circle) (hN : 1 ≤ N) (hq : 0 < q)
    (hs : q • α₁ = 0) (hne : α₁ ≠ 0) (p₁ p₂ : ℤ) :
    ‖kf (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
        * weylAvg P N α₁ 0 a b) p₁ p₂‖
      ≤ fibHbdC P N q k₁ k₂
        * (Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p₁
            * Work.KMTPlan.A6.wt (fibR₂ P N k₂) p₂) := by
  have hmZ : mZ P q α₁ 0 = 0 := fibre_mZ_zero P hq hs hne
  exact Work.KMTAreas.A7.kf_le
    (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b * weylAvg P N α₁ 0 a b)
    (fibHbdC P N q k₁ k₂) ((N : ℝ)⁻¹) (fibR₂ P N k₂)
    (kf_dp_symbol P N k₁ k₂ α₁ 0)
    (fun i₁ i₂ hi₁ hi₂ =>
      fibreMass_hbd P N q k₁ k₂ α₁ 0 hmZ hN hq hs (by simp) i₁ i₂ hi₁ hi₂)
    p₁ p₂

/-! ## §9  The mass bound for the Fourier coefficients -/

theorem fibreMass_bound (P : Polynomial ℤ) (N q k₁ k₂ : ℕ)
    (α₁ : Work.Analysis.IonescuWainger.Circle) (hN : 1 ≤ N) (hq : 0 < q)
    (hs : q • α₁ = 0) (hne : α₁ ≠ 0) :
    Summable (fun p : ℤ × ℤ => ‖fibreInt P N k₁ k₂ α₁ p.1 p.2‖)
      ∧ (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α₁ p.1 p.2‖)
        ≤ fibConst P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hr₁ : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
  have hr₁1 : (N : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hNpos]
    exact hN1
  have hr₂ : (0 : ℝ) < fibR₂ P N k₂ := fibR₂_pos P hN
  have hr₂1 : fibR₂ P N k₂ ≤ 1 := fibR₂_le_one P hN
  have hpw : ∀ p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α₁ p.1 p.2‖
      ≤ fibHbdC P N q k₁ k₂ * (Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p.1
          * Work.KMTPlan.A6.wt (fibR₂ P N k₂) p.2) := by
    intro p
    rw [fibreInt_eq_kf]
    exact kf_pointwise_bound P N q k₁ k₂ α₁ hN hq hs hne p.1 p.2
  constructor
  · refine Summable.of_nonneg_of_le
      (f := fun p : ℤ × ℤ => fibHbdC P N q k₁ k₂
        * (Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p.1
            * Work.KMTPlan.A6.wt (fibR₂ P N k₂) p.2))
      (fun p => norm_nonneg _) (fun p => ?_) ?_
    · exact (hpw p).trans (le_of_eq (by ring))
    · obtain ⟨hs1, -⟩ := Work.KMTPlan.A6.wt_tsum_le ((N : ℝ)⁻¹) hr₁ hr₁1
      obtain ⟨hs2, -⟩ := Work.KMTPlan.A6.wt_tsum_le (fibR₂ P N k₂) hr₂ hr₂1
      have hmul := hs1.mul_of_nonneg hs2
        (fun p => Work.KMTPlan.A6.wt_nonneg hr₁.le p)
        (fun p => Work.KMTPlan.A6.wt_nonneg hr₂.le p)
      exact hmul.mul_left _
  · have htsum := Work.KMTAreas.A7.hiCrudeTsum
      (fun p : ℤ × ℤ => fibreInt P N k₁ k₂ α₁ p.1 p.2) (fibHbdC P N q k₁ k₂)
      ((N : ℝ)⁻¹) (fibR₂ P N k₂)
      (fibHbdC_pos P N q k₁ k₂ hq hN).le hr₁ hr₁1 hr₂ hr₂1
      (fun p => (hpw p).trans (le_of_eq (by ring)))
    exact htsum.trans (fibreMass_const_compare P N q k₁ k₂ hN hq)

end

end Work.KMTAreas.A7
