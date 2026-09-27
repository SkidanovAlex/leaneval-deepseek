import Mathlib
import Submission.Mostow.SubHypDefs
import Submission.Work.Mostow.blk_smul_fermi

/-! Guidance from the project lead (the requester):

# Block decomposition of the stratum stabiliser (lead's design; F5/F6 of NOTES_LEAD_strata_KM.md)
# blk k m h R is choice-defined; its meaning is Work.Mostow.blk_smul_fermi (PROVED):
#   blk k m h R • fermi k m v w = fermi k m (h • v) (R w).
# blk_hom: compare actions on Fermi points (fermi is a bijection: fermi_inv, PROVED) and use faithfulness
#   (POActionProp clause "(∀ u, g • u = u) → g = 1") in dimension k+m for the product law and blk 1 1 = 1; injectivity:
#   equal actions ⇒ h • v = h' • v ∀ v (faithfulness in dimension k) and R w = R' w ∀ w (normal vectors, w ↦ fermi v w
#   injective). Group law on E m ≃ₗᵢ[ℝ] E m: (R * R') x = R (R' x).
# Never use `λ` as a variable name.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem blk_hom (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) :
    (∀ (h h' : PO k 1) (R R' : E m ≃ₗᵢ[ℝ] E m), blk k m (h * h') (R * R') = blk k m h R * blk k m h' R') ∧
    blk k m 1 1 = 1 ∧
    ∀ (h h' : PO k 1) (R R' : E m ≃ₗᵢ[ℝ] E m), blk k m h R = blk k m h' R' → h = h' ∧ R = R' := by
  have hA0 : POActionProp (k + m) := hA
  have hAk0 : POActionProp k := hAk
  obtain ⟨-, -, -, hOneA, hMulA, hFaithA, -⟩ := hA0
  obtain ⟨-, -, -, hOneK, hMulK, hFaithK, -⟩ := hAk0
  have hFermiInv : ∀ u : E (k + m), fermi k m (fermiInv k m u).1 (fermiInv k m u).2 = u :=
    (fermi_inv k m).2.1
  have hfermiInv1 : ∀ (v : E k) (w : E m), fermiInv k m (fermi k m v w) = (v, w) :=
    (fermi_inv k m).1
  -- two elements of `PO (k+m) 1` agreeing everywhere are equal (faithfulness)
  have key : ∀ g g' : PO (k + m) 1, (∀ u : E (k + m), g • u = g' • u) → g = g' := by
    intro g g' hgg
    have h1 : g⁻¹ * g' = 1 := hFaithA (g⁻¹ * g') (fun u => by
      rw [hMulA g⁻¹ g' u, ← hgg u, ← hMulA g⁻¹ g u, inv_mul_cancel, hOneA u])
    exact inv_mul_eq_one.mp h1
  refine ⟨?_, ?_, ?_⟩
  · intro h h' R R'
    apply key
    intro u
    obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi k m v w := ⟨_, _, (hFermiInv u).symm⟩
    rw [blk_smul_fermi k m hAk hIk hA hI (h * h') (R * R') v w,
        hMulA (blk k m h R) (blk k m h' R') (fermi k m v w),
        blk_smul_fermi k m hAk hIk hA hI h' R' v w,
        blk_smul_fermi k m hAk hIk hA hI h R (h' • v) (R' w)]
    rw [hMulK h h' v]
    rfl
  · apply key
    intro u
    obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi k m v w := ⟨_, _, (hFermiInv u).symm⟩
    rw [blk_smul_fermi k m hAk hIk hA hI 1 1 v w, hOneK v, hOneA (fermi k m v w)]
    rfl
  · intro h h' R R' heq
    have hpoint : ∀ (v : E k) (w : E m), h • v = h' • v ∧ R w = R' w := by
      intro v w
      have hsw : blk k m h R • fermi k m v w = blk k m h' R' • fermi k m v w := by rw [heq]
      rw [blk_smul_fermi k m hAk hIk hA hI h R v w,
          blk_smul_fermi k m hAk hIk hA hI h' R' v w] at hsw
      have h2 := congrArg (fermiInv k m) hsw
      rw [hfermiInv1 (h • v) (R w), hfermiInv1 (h' • v) (R' w)] at h2
      exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
    refine ⟨?_, ?_⟩
    · have h1 : h⁻¹ * h' = 1 := hFaithK (h⁻¹ * h') (fun v => by
        rw [hMulK h⁻¹ h' v, ← (hpoint v 0).1, ← hMulK h⁻¹ h v, inv_mul_cancel, hOneK v])
      exact inv_mul_eq_one.mp h1
    · exact LinearIsometryEquiv.ext (fun w => (hpoint 0 w).2)

end Work.Mostow
