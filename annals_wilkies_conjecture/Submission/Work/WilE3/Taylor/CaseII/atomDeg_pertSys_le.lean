import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.Defs
import Submission.Work.WilE3.Taylor.CaseII.GenDeficit
import Submission.Work.WilE5.Basic

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **the degree side-condition for `pertSys`**
  (node T2d of `cbc/wilkies_e3_caseII.md`): every row of `pertSys` has
  `atomDeg ≤ 3 · atomDeg Φ + 3`, the degree range the PROVED
  `Work.WilE3.Taylor.CaseII.Gen.squareCount_goodLevel` (node T2) accepts.

  The computation is the same as `Work.WilE3.Taylor.atomDeg_polarSys_le`: `atomDeg Q = Q.totalDegree + 1`
  and `Work.WilE5.totalDegree_eaD_le` (`eaD` does not raise the total degree by more than one), so
  `totalDegree (sqGrad c Φ) ≤ 2 (totalDegree Φ + 1)`, the perturbing coefficients `C (v i)` have
  total degree `0`, and the minor `∂_{i₀}Φ · (∂ᵢG + vᵢG) − ∂ᵢΦ · (∂_{i₀}G + v_{i₀}G)` multiplies
  factors of `totalDegree ≤ totalDegree Φ + 1` and `≤ 2 (totalDegree Φ + 1) + 1`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-- The degree bound for `sqGrad`: `totalDegree (∑ₗ (∂ₗΦ)²) ≤ 2 (totalDegree Φ + 1)`. -/
private lemma totalDegree_sqGrad_le (c : EAChain k r) (Φ : EAPoly k r) :
    (sqGrad c Φ).totalDegree ≤ 2 * (Φ.totalDegree + 1) := by
  rw [sqGrad]
  refine MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ)
    (f := fun l : Fin k => (eaD c l Φ) ^ 2) ?_
  intro l _
  have h := Work.WilE5.totalDegree_eaD_le c l Φ
  have h2 := MvPolynomial.totalDegree_pow (eaD c l Φ) 2
  omega

/-- The degree bound for the perturbed partial `∂ᵢG + vᵢG`, `G = sqGrad c Φ`. -/
private lemma totalDegree_pertGrad_le (c : EAChain k r) (Φ : EAPoly k r) (v : Fin k → ℝ)
    (i : Fin k) :
    (eaD c i (sqGrad c Φ) + MvPolynomial.C (v i) * sqGrad c Φ).totalDegree
      ≤ 2 * (Φ.totalDegree + 1) + 1 := by
  have hsq := totalDegree_sqGrad_le c Φ
  have h1 := Work.WilE5.totalDegree_eaD_le c i (sqGrad c Φ)
  have hC : (MvPolynomial.C (v i) * sqGrad c Φ : EAPoly k r).totalDegree
      ≤ 2 * (Φ.totalDegree + 1) := by
    refine le_trans (MvPolynomial.totalDegree_mul (MvPolynomial.C (v i)) (sqGrad c Φ)) ?_
    rw [MvPolynomial.totalDegree_C]
    omega
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_) <;> omega

/-- The degree bound for the minor part of `pertSys`. -/
private lemma totalDegree_pertMinor_le (c : EAChain k r) (Φ : EAPoly k r) (v : Fin k → ℝ)
    (i₀ i : Fin k) :
    (pertMinor c Φ v i₀ i).totalDegree ≤ 3 * Φ.totalDegree + 4 := by
  have hU : ∀ l : Fin k, (eaD c l (sqGrad c Φ) + MvPolynomial.C (v l) * sqGrad c Φ).totalDegree
      ≤ 2 * (Φ.totalDegree + 1) + 1 := fun l => totalDegree_pertGrad_le c Φ v l
  have hW : ∀ l : Fin k, (eaD c l Φ).totalDegree ≤ Φ.totalDegree + 1 :=
    fun l => Work.WilE5.totalDegree_eaD_le c l Φ
  have h1 : (eaD c i₀ Φ * (eaD c i (sqGrad c Φ) + MvPolynomial.C (v i) * sqGrad c Φ)).totalDegree
      ≤ 3 * Φ.totalDegree + 4 := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h1 := hU i
    have h2 := hW i₀
    omega
  have h2 : (eaD c i Φ * (eaD c i₀ (sqGrad c Φ) + MvPolynomial.C (v i₀) * sqGrad c Φ)).totalDegree
      ≤ 3 * Φ.totalDegree + 4 := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h1 := hU i₀
    have h2 := hW i
    omega
  rw [pertMinor, sub_eq_add_neg]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le h1 ?_)
  rw [MvPolynomial.totalDegree_neg]
  exact h2

/-- **(T2d, interior)** every row of `pertSys` has atom degree `≤ 3 · atomDeg Φ + 3`. -/
theorem atomDeg_pertSys_le {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Φ : WilkiesDesign.E.EAPoly k r) (v : Fin k → ℝ) (i₀ i : Fin k) :
    WilkiesDesign.E.atomDeg (Work.WilE3.Taylor.CaseII.pertSys c Φ v i₀ i) ≤ 3 * WilkiesDesign.E.atomDeg Φ + 3 := by
  have hΦ : Φ.totalDegree ≤ 3 * Φ.totalDegree + 3 := by omega
  have hm := totalDegree_pertMinor_le c Φ v i₀ i
  by_cases h : i = i₀
  · simp only [pertSys, h, ite_true, atomDeg]
    omega
  · simp only [pertSys, h, ite_false, atomDeg]
    omega

end Work.WilE3.Taylor.CaseII
