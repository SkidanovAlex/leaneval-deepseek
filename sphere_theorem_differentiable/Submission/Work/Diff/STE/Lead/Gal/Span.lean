import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.D.psi.Core
import Submission.Work.Diff.STE.D.psi.Equiv
import Submission.Work.Diff.STE.D.psi.JetAffine
import Submission.Work.Diff.STE.D.psi.abs_Fz_sub_le
import Submission.Work.Diff.STE.D.psi.abs_Ufun_sub_le
import Submission.Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp
import Submission.Work.Diff.STE.B3.abs_scoeff_le
import Submission.Work.Diff.STE.B3.scoeff_finset_sum_smul
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The span-form Galerkin scheme: the foreground as a span element

`Work.Diff.STE.Lead.galVF2` is the vector field of the *span-form* Galerkin scheme
`u' = J ρ ε (P (J ρ ε u))`.  On the positivity region of `u~(c) = J ρ ε (galState D ε c)` it equals
the Galerkin coefficients of the DeTurck tensor of `u~(c)`.

Since `J ρ ε` is the finite-rank projection onto the span of the symmetrised family `jSym D ε`
(`Work.Diff.STE.Lead.J_eq_genMap_galCoeff`), the foreground is *itself* a span element:

  `u~(c) = J ρ ε (galState D ε c) = genMap D ε (Fcoef c)`,   `Fcoef c := galCoeff D ρ ε (galState D ε c)`,

so that `galVF2 c = galVF2Conc (Fcoef c)` with

  `galVF2Conc z δ = galCoeff D ρ ε (secChart g₀ (genMap D ε δ) (x₀ z.1)) z`

the *concrete* chart expression of the scheme on the pure span element `genMap D ε δ`, and `Fcoef` is
affine in `c`.  This module sets up the vocabulary (`Fcoef`, `spanJet`, `spanPhi`, `SpanDom`,
`SpanPos`, `galVF2Conc`) in which the Lipschitz estimate of `galVF2_lipschitz_on_pos` is phrased.
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The coefficient space of the Galerkin scheme. -/
abbrev Coef (ι₀ : Type*) [Fintype ι₀] (n : ℕ) (ε : ℝ) : Type _ :=
  Work.Diff.STE.B3.JIdx ι₀ n ε → ℝ

/-- The flat coordinate space. -/
abbrev Flat (n : ℕ) : Type _ := Fin n → ℝ

/-- **The coefficient map of the foreground**: `u~(c) = J ρ ε (galState D ε c) = genMap D ε (Fcoef c)`,
i.e. the Galerkin coefficients of the mollified state in the spanning family. -/
noncomputable def Fcoef (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) :
    Coef ι₀ (Module.finrank ℝ E) ε → Coef ι₀ (Module.finrank ℝ E) ε :=
  fun c => Work.Diff.STE.Lead.galCoeff D ρ ε
    (Submission.Diff.STEGal.galState D ε c)

/-- **The pair of spatial `2`-jets of the foreground span element** `genMap D ε δ`, with the fixed
background jet of `g₀`: the second component is the finite linear combination of the chart jets of
the symmetrised spanning family `jSym D ε`, i.e. the chart jet of the pure span element. -/
noncomputable def spanJet (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ε : ℝ) (x₀ : M) (δ : Coef ι₀ (Module.finrank ℝ E) ε)
    (y : Flat (Module.finrank ℝ E)) :
    Work.Diff.STE.deTurck.JetPair (E := E) :=
  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀
      (Work.Diff.STE.flatToE (I := I) x₀ y),
    ∑ z, δ z • Work.Diff.STE.D.chartJetOf (I := I) (M := M)
      (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀
        (Work.Diff.STE.flatToE (I := I) x₀ y))

/-- **The jet-level chart DeTurck expression of the span element**: `pPhi` evaluated at the pair
(background jet of `g₀`, jet of the foreground `genMap D ε δ`). -/
noncomputable def spanPhi (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ε : ℝ) (x₀ : M) :
    Coef ι₀ (Module.finrank ℝ E) ε × Flat (Module.finrank ℝ E) →
      Work.Diff.EXT.MatE (E := E) :=
  fun q => Work.Diff.STE.D.pPhiFun (E := E) (spanJet (I := I) D ε x₀ q.1 q.2)

/-- **The domain of the jet-level chart expression**: the chart coordinate lies in the chart target
and the pair of jets lies in the smoothness locus of `pPhi` (both Gram matrices invertible). -/
def SpanDom (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ε : ℝ) (x₀ : M) :
    Set (Coef ι₀ (Module.finrank ℝ E) ε × Flat (Module.finrank ℝ E)) :=
  {q | Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} ∩
    (fun q => spanJet (I := I) D ε x₀ q.1 q.2) ⁻¹'
      Work.Diff.STE.deTurck.pPhiDom (E := E)

/-- **The positivity condition on the coefficients of the span element**: `genMap D ε δ` is a
positive definite bilinear form. -/
def SpanPos (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (δ : Coef ι₀ (Module.finrank ℝ E) ε) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
    0 < Work.Diff.STE.D.genMap (I := I) (M := M) D ε δ x v v

/-- **The concrete vector field of the span-form scheme**: the Galerkin coefficients of the chart
expression of the DeTurck tensor of the pure span element `genMap D ε δ`.  This is the total
function which agrees with `galVF2` on the positivity region. -/
noncomputable def galVF2Conc (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) :
    Coef ι₀ (Module.finrank ℝ E) ε → Coef ι₀ (Module.finrank ℝ E) ε :=
  fun δ z => (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
    (Work.Diff.STE.D.secChart (I := I) (M := M) g₀
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε δ) (D.x₀ z.1)) z

/-! ## The chart `2`-jet of a pure span element -/

/-- **The chart `2`-jet of the pure span element** `genMap D ε c = Σ_z c z • jSym D ε z` is the
corresponding linear combination of the chart jets of the spanning vectors. -/
theorem chartJetOf_genMap_eq_sum
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Coef ι₀ (Module.finrank ℝ E) ε) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.STE.D.chartJetOf (I := I) (M := M)
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) x₀ y
      = ∑ z, c z • Work.Diff.STE.D.chartJetOf (I := I) (M := M)
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀ y := by
  classical
  have hsummand : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      Work.Diff.STE.D.ChartData (I := I) (M := M)
        (c z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) :=
    fun z => Work.Diff.STE.D.GenMap.chartData_smul (I := I) (M := M) (c z)
      (Work.Diff.STE.D.psi.jSym_chartData (I := I) (M := M) D ε z)
  have hsum : ∀ t : Finset (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε),
      Work.Diff.STE.D.chartJetOf (I := I) (M := M)
          (∑ z ∈ t, c z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀ y
        = ∑ z ∈ t, c z • Work.Diff.STE.D.chartJetOf (I := I) (M := M)
            (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀ y := by
    intro t
    induction t using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        exact Work.Diff.STE.D.psi.chartJetOf_zero (I := I) (M := M) x₀ y
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [Work.Diff.STE.D.psi.chartJetOf_add_of_chartData (I := I) (M := M) x₀ hy
          (c a • Work.Diff.STE.D.jSym (I := I) (M := M) D ε a)
          (∑ z ∈ t, c z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
          (hsummand a)
          (Work.Diff.STE.D.GenMap.chartData_finset_sum (I := I) (M := M) t
            (fun z => c z • Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
            (fun z _ => hsummand z))]
        rw [Work.Diff.STE.D.psi.chartJetOf_smul_of_chartData (I := I) (M := M) x₀ hy (c a)
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε a)
          (Work.Diff.STE.D.psi.jSym_chartData (I := I) (M := M) D ε a), ih]
  exact hsum Finset.univ

/-- The `spanJet` of the foreground coefficients is the jet pair of the foreground section. -/
theorem spanJet_Fcoef (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (x₀ : M) (c : Coef ι₀ (Module.finrank ℝ E) ε) {y : Flat (Module.finrank ℝ E)}
    (hy : Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target) :
    spanJet (I := I) D ε x₀ (Fcoef D ρ ε c) y =
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀
          (Work.Diff.STE.flatToE (I := I) x₀ y),
        Work.Diff.STE.D.chartJetOf (I := I) (M := M)
          (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x₀
            (Work.Diff.STE.flatToE (I := I) x₀ y)) := by
  refine Prod.ext rfl ?_
  show (∑ z, Fcoef D ρ ε c z • Work.Diff.STE.D.chartJetOf (I := I) (M := M)
      (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀
        (Work.Diff.STE.flatToE (I := I) x₀ y)) = _
  rw [← chartJetOf_genMap_eq_sum (I := I) (M := M) (g₀ := g₀) hg D ε x₀ (Fcoef D ρ ε c) hy]
  have hJ : D.J ρ ε (Submission.Diff.STEGal.galState D ε c)
      = Work.Diff.STE.D.genMap (I := I) (M := M) D ε (Fcoef D ρ ε c) :=
    Work.Diff.STE.Lead.J_eq_genMap_galCoeff D ρ ε hε hρ0
      (Submission.Diff.STEGal.galState D ε c)
      (Work.Diff.STE.D.isSymm_addSec_genMap (I := I) (M := M) D ε c)
  rw [hJ]

end

end Work.Diff.STE.Lead.Gal
