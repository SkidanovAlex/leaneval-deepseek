import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.Defs
import Submission.Work.WilE3.Taylor.CaseII.GenDeficit
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-- The degree bound for the squared gradient `sqGrad c Φ = ∑ₗ (∂ₗΦ)²`. -/
lemma sphAux_totalDegree_sqGrad_le (c : EAChain k r) (Φ : EAPoly k r) :
    (sqGrad c Φ).totalDegree ≤ 2 * (Φ.totalDegree + 1) := by
  rw [sqGrad]
  refine MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ)
    (f := fun l : Fin k => (eaD c l Φ) ^ 2) ?_
  intro l _
  have h := Work.WilE5.totalDegree_eaD_le c l Φ
  have h2 := MvPolynomial.totalDegree_pow (eaD c l Φ) 2
  omega

/-- The degree bound for the perturbed partial `∂ᵢG + vᵢG`, `G = sqGrad c Φ`. -/
lemma sphAux_totalDegree_pertGrad_le (c : EAChain k r) (Φ : EAPoly k r) (v : Fin k → ℝ)
    (i : Fin k) :
    (eaD c i (sqGrad c Φ) + MvPolynomial.C (v i) * sqGrad c Φ).totalDegree
      ≤ 2 * (Φ.totalDegree + 1) + 1 := by
  have hsq := sphAux_totalDegree_sqGrad_le c Φ
  have h1 := Work.WilE5.totalDegree_eaD_le c i (sqGrad c Φ)
  have hC : (MvPolynomial.C (v i) * sqGrad c Φ : EAPoly k r).totalDegree
      ≤ 2 * (Φ.totalDegree + 1) := by
    refine le_trans (MvPolynomial.totalDegree_mul (MvPolynomial.C (v i)) (sqGrad c Φ)) ?_
    rw [MvPolynomial.totalDegree_C]
    omega
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_) <;> omega

/-- The degree bound for the sphere `sphereP y δ2 = ∑ (xᵢ - yᵢ)² - δ2` (at most `2`). -/
lemma sphAux_totalDegree_sphereP_le (y : Fin k → ℝ) (δ2 : ℝ) :
    (sphereP (k := k) (r := r) y δ2).totalDegree ≤ 2 := by
  rw [sphereP, sub_eq_add_neg]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ)
      (f := fun i : Fin k => (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y i)) ^ 2) ?_) le_rfl
    intro i _
    have h2 := MvPolynomial.totalDegree_pow
      (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y i) : EAPoly k r) 2
    have h1 : (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y i) : EAPoly k r).totalDegree ≤ 1 := by
      rw [sub_eq_add_neg]
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
      · rw [MvPolynomial.totalDegree_X]
      · rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C]; omega
    omega
  · rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C]; omega

/-- The degree bound for the radial minor `pertMinor3`. -/
lemma sphAux_totalDegree_pertMinor3_le (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ)
    (i₀ j₀ l : Fin k) :
    (pertMinor3 c Φ v y i₀ j₀ l).totalDegree ≤ 3 * Φ.totalDegree + 5 := by
  have hU : ∀ m : Fin k,
      (eaD c m (sqGrad c Φ) + MvPolynomial.C (v m) * sqGrad c Φ).totalDegree
        ≤ 2 * (Φ.totalDegree + 1) + 1 := fun m => sphAux_totalDegree_pertGrad_le c Φ v m
  have hW : ∀ m : Fin k, (eaD c m Φ).totalDegree ≤ Φ.totalDegree + 1 :=
    fun m => Work.WilE5.totalDegree_eaD_le c m Φ
  have hT : ∀ m : Fin k,
      (MvPolynomial.X (Sum.inl m) - MvPolynomial.C (y m) : EAPoly k r).totalDegree ≤ 1 := by
    intro m
    rw [sub_eq_add_neg]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · rw [MvPolynomial.totalDegree_X]
    · rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C]; omega
  have hP : ∀ b' cc d e : Fin k,
      ((eaD c b' Φ) * (MvPolynomial.X (Sum.inl cc) - MvPolynomial.C (y cc))
        - (eaD c d Φ) * (MvPolynomial.X (Sum.inl e) - MvPolynomial.C (y e))).totalDegree
        ≤ Φ.totalDegree + 2 := by
    intro b' cc d e
    refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 := hW b'; have h2 := hT cc; omega
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 := hW d; have h2 := hT e; omega
  have hM : ∀ a b' cc d e : Fin k,
      ((eaD c a (sqGrad c Φ) + MvPolynomial.C (v a) * sqGrad c Φ)
        * ((eaD c b' Φ) * (MvPolynomial.X (Sum.inl cc) - MvPolynomial.C (y cc))
          - (eaD c d Φ) * (MvPolynomial.X (Sum.inl e) - MvPolynomial.C (y e)))).totalDegree
        ≤ 3 * Φ.totalDegree + 5 := by
    intro a b' cc d e
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h1 := hU a
    have h2 := hP b' cc d e
    omega
  simp only [pertMinor3]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
    · exact hM i₀ j₀ l l j₀
    · exact hM j₀ i₀ l l i₀
  · exact hM l i₀ j₀ j₀ i₀

theorem atomDeg_sphSys_le {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Φ : WilkiesDesign.E.EAPoly k r) (v y : Fin k → ℝ) (δ2 : ℝ)
    (i₀ j₀ i : Fin k) :
    WilkiesDesign.E.atomDeg (Work.WilE3.Taylor.CaseII.sphSys c Φ v y δ2 i₀ j₀ i) ≤ 3 * WilkiesDesign.E.atomDeg Φ + 3 := by
  have hsp := sphAux_totalDegree_sphereP_le (k := k) (r := r) y δ2
  have hm := sphAux_totalDegree_pertMinor3_le c Φ v y i₀ j₀ i
  rw [sphSys]
  split_ifs
  · simp only [atomDeg]; omega
  · simp only [atomDeg]; omega
  · simp only [atomDeg]; omega

end Work.WilE3.Taylor.CaseII
