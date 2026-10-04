import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.GardDef
import Submission.Work.Diff.STE.Lead.Gal.GardAux
import Submission.Work.Diff.STE.Lead.Gal.gardClauses
import Submission.Work.Diff.STE.Lead.Gal.gardRjBridge
import Submission.Work.Diff.STE.Lead.Gal.gardingLowEnergy
import Submission.Work.Diff.STE.Lead.Gal.residualDataPsi
import Submission.Work.Diff.STE.Lead.Gal.transportExistsAUniformGal
import Submission.Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp
import Submission.Work.Diff.STE.deTurck.pPhi_decomp
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.DeTurckJet
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The support of the localised component `R i h a b` lies in the open `σ i`-ball. -/
lemma gardR_supp_ball (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    Function.support (D.R i h a b) ⊆ {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ < D.σ i} := by
  intro z hz
  have hpsi : D.psi i z ≠ 0 := fun h0 =>
    hz (by simp only [Work.Diff.STE.B3Data.R, h0, zero_mul, mul_zero])
  have hz' : D.ζ i (D.pt i z) ≠ 0 := fun h0 =>
    hpsi (by simp only [Work.Diff.STE.B3Data.psi, h0, mul_zero])
  obtain ⟨hsrc, hlt⟩ := D.hζsupp i (D.pt i z) hz'
  have hzt : z ∈ tsupport (D.χ i) := by
    by_contra hcon
    exact hpsi (by simp only [Work.Diff.STE.B3Data.psi,
      image_eq_zero_of_notMem_tsupport hcon, zero_mul])
  have hcoord : coord (I := I) (D.x₀ i) (D.pt i z) = z := by
    have h1 : (extChartAt I (D.x₀ i)) (D.pt i z)
        = Work.Diff.STE.flatToE (I := I) (D.x₀ i) z :=
      (extChartAt I (D.x₀ i)).right_inv (D.hχtsup i z hzt)
    have key : (Module.finBasis ℝ E).equivFun (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
        = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z := by
      simp only [Work.Diff.STE.flatToE]
      rw [LinearEquiv.apply_symm_apply]
    rw [coord, h1, key]
    ring
  rw [← hcoord]
  exact hlt

/-- On the (open) fundamental cube the periodisation of the localised component is the weighted
orthonormal-frame chart matrix. -/
lemma gardRper_eq_cube (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ∀ k, z k ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    D.Rper i h a b z
      = ((Work.Diff.STE.B3.wf (I := I) (M := M) D i z
          * Work.Diff.STE.B3.Mf (I := I) (M := M) D h i z a b : ℝ) : ℂ) := by
  rw [D.Rper_eq_R i h a b hz]
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3.wf, Work.Diff.STE.B3.Mf, mul_assoc]

end

theorem gardTransport_holds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : 1 ≤ k) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
            ‖z‖ ≤ 2 * D.σ i →
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
          Work.Diff.STE.Lead.Gal.GardData (I := I) (M := M) D hLC k lam' C h hsym hpos hsmooth :=
  fun lam K hlam hK =>
    GardData_of_data (I := I) (M := M) D hLC k hk
      (fun lam K hlam hK =>
        GardA_of_raw (I := I) (M := M)
          (transport_exists_A_uniform (I := I) (M := M) D k lam K hlam hK))
      (fun lam K hlam hK => residualDataPsi (I := I) (M := M) D k lam K hlam hK)
      (fun lam K hlam hK =>
        gardingLowEnergy (I := I) (M := M) D hLC k hk lam K hlam hK
          (GardA_of_raw (I := I) (M := M)
            (transport_exists_A_uniform (I := I) (M := M) D k lam K hlam hK))
          (residualDataPsi (I := I) (M := M) D k lam K hlam hK))
      lam K hlam hK

end Work.Diff.STE.Lead.Gal
