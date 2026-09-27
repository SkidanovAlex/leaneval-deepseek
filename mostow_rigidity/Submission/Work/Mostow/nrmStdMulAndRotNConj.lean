import Mathlib
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.normConjIsom

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- `nrmStd k m` is multiplicative on the setwise stabiliser of the standard stratum.  Same argument
as `rhd_resStd_mul`: every element of the stabiliser is `blk` of its restriction and its normal part
(`rhd_stab_form`), and `blk` is multiplicative and injective on the pair (`blk_hom`). -/
lemma rhd_nrmStd_mul (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    {g h : PO (k + m) 1} (hg : g ∈ SetStabStd k m) (hh : h ∈ SetStabStd k m) :
    nrmStd k m (g * h) = nrmStd k m g * nrmStd k m h := by
  have hgh : g * h ∈ SetStabStd k m := rhd_mul_mem_stab k m hA hg hh
  have e1 := rhd_stab_form k m hAk hIk hA hI hgh
  have e2 : g * h = blk k m (resStd k m g * resStd k m h) (nrmStd k m g * nrmStd k m h) := by
    conv_lhs => rw [rhd_stab_form k m hAk hIk hA hI hg,
                    rhd_stab_form k m hAk hIk hA hI hh]
    rw [← (blk_hom k m hAk hIk hA hI).1]
  exact ((blk_hom k m hAk hIk hA hI).2.2 _ _ _ _ (e1.symm.trans e2)).2

/-- `nrmStd k m 1 = 1`. -/
lemma rhd_nrmStd_one (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) :
    nrmStd k m (1 : PO (k + m) 1) = 1 := by
  have h1 : (1 : PO (k + m) 1) ∈ SetStabStd k m := rhd_one_mem_stab k m hA
  have e1 := rhd_stab_form k m hAk hIk hA hI h1
  have e2 : blk k m (resStd k m 1) (nrmStd k m 1) = blk k m 1 1 := by
    rw [← e1, (blk_hom k m hAk hIk hA hI).2.1]
  exact ((blk_hom k m hAk hIk hA hI).2.2 _ _ _ _ e2).2

/-- The inverse rule for `nrmStd` on the setwise stabiliser. -/
lemma rhd_nrmStd_inv (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    {g : PO (k + m) 1} (hg : g ∈ SetStabStd k m) :
    nrmStd k m g⁻¹ = (nrmStd k m g)⁻¹ := by
  have h2 := rhd_nrmStd_mul k m hAk hIk hA hI (rhd_inv_mem_stab k m hA hg) hg
  rw [inv_mul_cancel g, rhd_nrmStd_one k m hAk hIk hA hI] at h2
  exact eq_inv_of_mul_eq_one_left h2.symm

/-- `rotN` is invariant under conjugation by a linear isometry: conjugation by `R` acts on
`opOf S - 1` as an isometry of operator norms (`normConjIsom`). -/
lemma rhd_rotN_conj {m : ℕ} (R S : E m ≃ₗᵢ[ℝ] E m) :
    rotN (R * S * R⁻¹) = rotN S := by
  have h1 : (R * S * R⁻¹).toLinearIsometry.toContinuousLinearMap - 1 =
      (R : E m →L[ℝ] E m) * ((S : E m →L[ℝ] E m) - 1) * ((R.symm : E m →L[ℝ] E m)) := by
    ext x
    simp
  have hR : rotN (R * S * R⁻¹) =
      ‖(R : E m →L[ℝ] E m) * ((S : E m →L[ℝ] E m) - 1) * ((R.symm : E m →L[ℝ] E m))‖ := by
    rw [show rotN (R * S * R⁻¹) =
      ‖(R * S * R⁻¹).toLinearIsometry.toContinuousLinearMap - 1‖ from rfl, h1]
  rw [hR, normConjIsom R ((S : E m →L[ℝ] E m) - 1)]
  rfl

/-- `nrmStd k m` is multiplicative on the setwise stabiliser of the standard stratum, its inverse
rule holds there, and `rotN` is invariant under conjugation by a linear isometry. -/
theorem nrmStdMulAndRotNConj (k m : ℕ)
    (hAk : Submission.Mostow.POActionProp k) (hIk : Submission.Mostow.HypIsometryProp k)
    (hA : Submission.Mostow.POActionProp (k + m)) (hI : Submission.Mostow.HypIsometryProp (k + m)) :
    (∀ g h : LeanEval.Geometry.MostowRigidity.PO (k + m) 1,
      g ∈ Submission.Mostow.SetStabStd k m → h ∈ Submission.Mostow.SetStabStd k m →
      Submission.Mostow.nrmStd k m (g * h) = Submission.Mostow.nrmStd k m g * Submission.Mostow.nrmStd k m h) ∧
    Submission.Mostow.nrmStd k m (1 : LeanEval.Geometry.MostowRigidity.PO (k + m) 1) = 1 ∧
    (∀ g : LeanEval.Geometry.MostowRigidity.PO (k + m) 1,
      g ∈ Submission.Mostow.SetStabStd k m → g⁻¹ ∈ Submission.Mostow.SetStabStd k m) ∧
    (∀ g : LeanEval.Geometry.MostowRigidity.PO (k + m) 1,
      g ∈ Submission.Mostow.SetStabStd k m →
      Submission.Mostow.nrmStd k m g⁻¹ = (Submission.Mostow.nrmStd k m g)⁻¹) ∧
    (∀ R S : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m,
      Submission.Mostow.rotN (R * S * R⁻¹) = Submission.Mostow.rotN S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g h hg hh
    exact rhd_nrmStd_mul k m hAk hIk hA hI hg hh
  · exact rhd_nrmStd_one k m hAk hIk hA hI
  · intro g hg
    exact rhd_inv_mem_stab k m hA hg
  · intro g hg
    exact rhd_nrmStd_inv k m hAk hIk hA hI hg
  · intro R S
    exact rhd_rotN_conj R S

end Work.Mostow
