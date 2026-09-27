import Mathlib
import Submission.Work.Mostow.gapA.screwDefs
import Submission.Work.Mostow.gapA.screwNorm

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

/-- The Minkowski pairing `⟨x, N x⟩` of the screw motion: only the two `span{A,B}`-components
contribute `ρ + ρ⁻¹`, all mixed terms vanish because `N` is orthogonal and `A`, `B` are the
λ-eigenvectors. -/
theorem screwDisp {a b : Submission.Mostow.E 3} (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (N : (Fin 3 ⊕ Fin 1 → ℝ) →ₗ[ℝ] (Fin 3 ⊕ Fin 1 → ℝ))
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (hNA : N (Work.Mostow.gapA.nullA a) = ρ • Work.Mostow.gapA.nullA a) (hNB : N (Work.Mostow.gapA.nullB b) = ρ⁻¹ • Work.Mostow.gapA.nullB b)
    (hform : ∀ x y : Fin 3 ⊕ Fin 1 → ℝ, Work.Mostow.mink (N x) (N y) = Work.Mostow.mink x y)
    (hmem : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ Work.Mostow.gapA.Nsub a b → N x ∈ Work.Mostow.gapA.Nsub a b)
    (x : Fin 3 ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x (N x) = Work.Mostow.gapA.alC a b x * Work.Mostow.gapA.beC a b x * Work.Mostow.gapA.smB a b * (ρ + ρ⁻¹)
      + Work.Mostow.mink (Work.Mostow.gapA.prjN a b x) (N (Work.Mostow.gapA.prjN a b x)) := by
  have hAA : Work.Mostow.mink (nullA a) (nullA a) = 0 := mink_nvec_self ha
  have hBB : Work.Mostow.mink (nullB b) (nullB b) = 0 := mink_nvec_self hb
  have hAB : Work.Mostow.mink (nullA a) (nullB b) = smB a b := rfl
  have hBA : Work.Mostow.mink (nullB b) (nullA a) = smB a b :=
    (Work.Mostow.minkSeg_comm (nullA a) (nullB b)).symm
  have hvN : prjN a b x ∈ Nsub a b := (screwNorm ha hb hab).2.2.2.1 x
  have hvA : Work.Mostow.mink (prjN a b x) (nullA a) = 0 := (mem_Nsub.mp hvN).1
  have hvB : Work.Mostow.mink (prjN a b x) (nullB b) = 0 := (mem_Nsub.mp hvN).2
  have hAv : Work.Mostow.mink (nullA a) (prjN a b x) = 0 := by
    rw [Work.Mostow.minkSeg_comm]; exact hvA
  have hBv : Work.Mostow.mink (nullB b) (prjN a b x) = 0 := by
    rw [Work.Mostow.minkSeg_comm]; exact hvB
  have hAnv : Work.Mostow.mink (nullA a) (N (prjN a b x)) = 0 := by
    have h := hform (nullA a) (prjN a b x)
    rw [hNA] at h
    rw [sn_mink_smul_left] at h
    rw [hAv] at h
    exact (mul_eq_zero.mp h).resolve_left hρ
  have hBnv : Work.Mostow.mink (nullB b) (N (prjN a b x)) = 0 := by
    have h := hform (nullB b) (prjN a b x)
    rw [hNB] at h
    rw [sn_mink_smul_left] at h
    rw [hBv] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hρ)
  have hNp : N (alC a b x • nullA a + beC a b x • nullB b + prjN a b x)
      = (alC a b x * ρ) • nullA a + (beC a b x * ρ⁻¹) • nullB b + N (prjN a b x) := by
    simp only [LinearMap.map_add, LinearMap.map_smul, hNA, hNB, smul_smul]
  have key : Work.Mostow.mink (alC a b x • nullA a + beC a b x • nullB b + prjN a b x)
      (N (alC a b x • nullA a + beC a b x • nullB b + prjN a b x))
      = alC a b x * beC a b x * smB a b * (ρ + ρ⁻¹)
        + Work.Mostow.mink (prjN a b x) (N (prjN a b x)) := by
    rw [hNp]
    simp only [Work.Mostow.minkSeg_add_left, Work.Mostow.minkSeg_add_right,
      sn_mink_smul_left, sn_mink_smul_right,
      hAA, hBB, hAB, hBA, hvA, hvB, hAnv, hBnv]
    ring
  rw [eq_decomp a b x] at key
  exact key

end

end Work.Mostow.gapA
