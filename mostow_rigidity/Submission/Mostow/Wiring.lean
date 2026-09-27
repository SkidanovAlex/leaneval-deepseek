import Submission.Mostow.Interfaces

/-!
# Mostow rigidity from the area Props (driver-written glue; DO NOT EDIT)

`mostow_of_areas` proves the challenge statement from the area Props of `Interfaces.lean`.
The Props `VisualProp`, `BaryProp`, `GeomFiniteProp`, `CuspRecognitionProp` do not appear here:
they are hypotheses of the area lemmas that prove `NatMapEquivProp`, `NatMapJacProp`,
`NatMapSurjProp`, `QIProp`.
-/

open LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Submission.Mostow

theorem boundaryMap_of_areas {n : ℕ} (hQI : QIProp n) (hBE : BoundaryExtProp n)
    (Γ Λ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) (hΛ : HypLattice Λ) (f : Γ ≃* Λ) :
    ∃ φ : E n → E n, Set.BijOn φ (Sph n) (Sph n) ∧ ContinuousOn φ (Sph n) ∧
      ∀ γ : Γ, ∀ ξ ∈ Sph n, φ (bd (γ : PO n 1) ξ) = bd (f γ : PO n 1) (φ ξ) := by
  obtain ⟨Φ, hΦ, heq⟩ := hQI Γ Λ hΓ hΛ f
  obtain ⟨φ, hbij, hcont, hequiv⟩ := hBE Φ hΦ
  exact ⟨φ, hbij, hcont, fun γ => hequiv γ (f γ) (heq γ)⟩

theorem natMap_of_areas {n : ℕ} (hNE : NatMapEquivProp n) (hNJ : NatMapJacProp n)
    (hNS : NatMapSurjProp n) (hQI : QIProp n) (hBE : BoundaryExtProp n)
    (Γ Λ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) (hΛ : HypLattice Λ) (f : Γ ≃* Λ) :
    ∃ F : E n → E n, ContDiff ℝ 1 F ∧ Function.Surjective F ∧
      (∀ (γ : Γ) (u : E n), F (γ • u) = (f γ : PO n 1) • F u) ∧ (∀ u, hjac F u ≤ 1) ∧
      (∀ u, hjac F u = 1 → ∀ v, gH (F u) (fderiv ℝ F u v) = gH u v) := by
  obtain ⟨φ, hbij, hcont, heq⟩ := boundaryMap_of_areas hQI hBE Γ Λ hΓ hΛ f
  obtain ⟨hC, hJ, hEq⟩ := hNJ φ hbij hcont
  exact ⟨natMap φ, hC, hNS φ hbij hcont,
    fun γ u => hNE φ hbij hcont γ (f γ) (heq γ) u, hJ, hEq⟩

theorem mostow_of_areas (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBr : BridgeProp n) (hNE : NatMapEquivProp n) (hNJ : NatMapJacProp n)
    (hNS : NatMapSurjProp n) (hV : VolumeProp n) (hL : LocalIsomProp n)
    (hQI : QIProp n) (hBE : BoundaryExtProp n)
    (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (covol_Γ : covolume Γ (PO n 1) ≠ ⊤) (covol_Λ : covolume Λ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) : ∃ g : PO n 1, ∀ γ : Γ, f γ = g * γ * g⁻¹ := by
  obtain ⟨-, -, -, hone, hmul, hfaith, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, hsurj, -⟩ := hI
  have hΓ : HypLattice Γ := hBr Γ disc_Γ inferInstance covol_Γ
  have hΛ : HypLattice Λ := hBr Λ disc_Λ inferInstance covol_Λ
  obtain ⟨F, hFC, hFS, hFE, hFJ, hFeq⟩ := natMap_of_areas hNE hNJ hNS hQI hBE Γ Λ hΓ hΛ f
  obtain ⟨F', hF'C, hF'S, hF'E, hF'J, -⟩ :=
    natMap_of_areas hNE hNJ hNS hQI hBE Λ Γ hΛ hΓ f.symm
  obtain ⟨DΓ, hDΓ, -⟩ := hΓ.2
  obtain ⟨DΛ, hDΛ, -⟩ := hΛ.2
  have h1 := hV Γ Λ hΓ hΛ f.toMonoidHom F hFC hFS hFE hFJ DΓ DΛ hDΓ hDΛ
  have h2 := hV Λ Γ hΛ hΓ f.symm.toMonoidHom F' hF'C hF'S hF'E hF'J DΛ DΓ hDΛ hDΓ
  have hjac1 : ∀ u, hjac F u = 1 := h1.2 h2.1
  have hiso : ∀ u v, hdist (F u) (F v) = hdist u v := hL F hFC (fun u => hFeq u (hjac1 u))
  obtain ⟨g, hg⟩ := hsurj F hiso
  refine ⟨g, fun γ => ?_⟩
  have key : ∀ u : E n, ((g * (γ : PO n 1))⁻¹ * ((f γ : PO n 1) * g)) • u = u := by
    intro u
    have e1 : (f γ : PO n 1) • (g • u) = g • ((γ : PO n 1) • u) := by
      rw [← hg, ← hg]; exact (hFE γ u).symm
    calc ((g * (γ : PO n 1))⁻¹ * ((f γ : PO n 1) * g)) • u
        = (g * (γ : PO n 1))⁻¹ • ((f γ : PO n 1) • (g • u)) := by rw [hmul, hmul]
      _ = (g * (γ : PO n 1))⁻¹ • (g • ((γ : PO n 1) • u)) := by rw [e1]
      _ = (g * (γ : PO n 1))⁻¹ • ((g * (γ : PO n 1)) • u) := by rw [hmul g]
      _ = ((g * (γ : PO n 1))⁻¹ * (g * (γ : PO n 1))) • u := by rw [hmul _ (g * _), hmul g]
      _ = u := by rw [inv_mul_cancel, hone]
  have h := hfaith _ key
  rw [inv_mul_eq_one] at h
  rw [h, mul_inv_cancel_right]

end Submission.Mostow
