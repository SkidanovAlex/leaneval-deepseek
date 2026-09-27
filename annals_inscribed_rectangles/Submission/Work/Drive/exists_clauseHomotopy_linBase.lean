import Mathlib
import Submission.Work.Drive.classRows
import Submission.Work.Drive.endsHomotopyClauses
import Submission.Work.Drive.seamEssentiality
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.refTripleClause

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology
attribute [local instance] Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

/-!
# The `(B)`-lane clause homotopy of the three *sheared linear* charts `linBase A`

`Work.Drive.HasClassLinearization` consumes the clause homotopies of the ends lane in the *chain* form
`Work.Drive.clauseB H0 k`, i.e. the reparametrisation

> `x ↦ H0 k (clauseRho (3 * x 2 - 1), mk2 (x 0) (x 1))`

of a class homotopy `H0` of `ℝP³` (`Work.Drive.refTripleClause`, §3).  The `(B)`-lane producers
(`Work.Drive.exists_homotopyClauses_rotPresentation`, `Work.Drive.exists_diskClassHomotopyParam`, …)
deliver smoothness only in the *chain* form `x ↦ H k (x 2, mk2 (x 0) (x 1))` (`ℝ × ℝ²` carries no
product manifold structure).  This file supplies the bridge, and then instantiates the producer at the
three **sheared linear charts** `Work.Drive.linBase A k` of the ends lane.

The mathematical content here is only the observation of `Work.Drive.endsHomotopyClauses`'s docstring,
that the (B)-lane producer's non-collision hypothesis `hgood` is stated at the *zeros of a weight* `χ`,
so that choosing the weight `χ z = z.im` (the imaginary part) makes the hypothesis hold exactly on the
**real diameter** `z.im = 0` of the disk — which is the form `havoid` in which the genericity of the
sheared family is available (`Work.Drive.exists_linPlaneCharts_hgen` and its `linBase`-forms).  The
geometric inputs of the producer (essentiality of the chart's class map: parallelism at the antipode
with negative factor) come from `Work.Drive.exists_neg_parallelism_of_planeChart`, which needs no
hypothesis beyond `IsPlaneChart` and the class lift.
-/

noncomputable section

/-- The third standard basis vector of `𝔼³`, i.e. the direction of the reparametrisation carried by
`Work.Drive.clauseB`. -/
def clauseRhoBasis : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (![0, 0, 1] : Fin 3 → ℝ)

/-- **The reparametrisation of the chain variable carried by `clauseB`**, as a self-map of `𝔼³`:
it fixes the two plane coordinates and replaces the third by `clauseRho (3 · - 1)`:

> `clauseRhoMap x = (x 0, x 1, clauseRho (3 * x 2 - 1))`. -/
def clauseRhoMap (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  x + (clauseRho (3 * x 2 - 1) - x 2) • clauseRhoBasis

@[simp] lemma clauseRhoMap_apply_zero (x : EuclideanSpace ℝ (Fin 3)) : clauseRhoMap x 0 = x 0 := by
  simp [clauseRhoMap, clauseRhoBasis]

@[simp] lemma clauseRhoMap_apply_one (x : EuclideanSpace ℝ (Fin 3)) : clauseRhoMap x 1 = x 1 := by
  simp [clauseRhoMap, clauseRhoBasis]

@[simp] lemma clauseRhoMap_apply_two (x : EuclideanSpace ℝ (Fin 3)) :
    clauseRhoMap x 2 = clauseRho (3 * x 2 - 1) := by
  simp [clauseRhoMap, clauseRhoBasis]

/-- **The reparametrisation is `C^∞`**: the third coordinate is the smooth function
`clauseRho (3 · - 1)` of the third coordinate, and the two other coordinates are untouched. -/
lemma contMDiff_clauseRhoMap :
    ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) clauseRhoMap := by
  rw [contMDiff_iff_contDiff]
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => 3 * x 2 - 1) := by fun_prop
  have hcr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => clauseRho (3 * x 2 - 1)) :=
    contDiff_clauseRho.comp hc
  have hx2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => x 2) := by fun_prop
  have hsub : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => clauseRho (3 * x 2 - 1) - x 2) := hcr.sub hx2
  exact contDiff_id.add (hsub.smul contDiff_const)

/-- **The bridge between the two forms of the chain smoothness.**  If the chain
`x ↦ H0 k (x 2, mk2 (x 0) (x 1))` is `C^∞` (the only form in which the (B)-lane producers state it,
since `ℝ × ℝ²` carries no product manifold structure), then so is `clauseB H0 k`, which is that chain
precomposed with the smooth reparametrisation `clauseRhoMap` of its first argument. -/
lemma contMDiff_clauseB_of_chain
    (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (k : Fin 3)
    (h : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H0 k (x 2, mk2 (x 0) (x 1)))) :
    ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (clauseB H0 k) := by
  have hcomp := h.comp contMDiff_clauseRhoMap
  have heq : (fun x : EuclideanSpace ℝ (Fin 3) =>
        H0 k (clauseRho (3 * x 2 - 1), mk2 (x 0) (x 1)))
      = ((fun x : EuclideanSpace ℝ (Fin 3) => H0 k (x 2, mk2 (x 0) (x 1))) ∘ clauseRhoMap) := by
    funext x
    simp only [Function.comp_apply, clauseRhoMap_apply_zero, clauseRhoMap_apply_one,
      clauseRhoMap_apply_two]
  rw [show clauseB H0 k = (fun x : EuclideanSpace ℝ (Fin 3) =>
      H0 k (clauseRho (3 * x 2 - 1), mk2 (x 0) (x 1))) from rfl, heq]
  exact hcomp

end

/-- **The clause homotopy of the three sheared linear charts `linBase A k`**, in the exact form the
assembly `Work.Drive.hasClassLinearization_of_endData` consumes: the chain smoothness of `clauseB H0 k`,
the two `(s, y)`-endpoints (the design's rotated charts of `Q` at `s = 0`, the linear disk models
`linPlaneOf (linBase A) cl hcl k` at `s = 1`), and the seam invariance.

The whole analytic input is `Work.Drive.exists_homotopyClauses_rotPresentation`, instantiated at the
rotation angles `designAnglesReal a c'` and the weights `χ k z = z.im`: at the zeros of `χ` (the real
diameter of the disk) the non-collision hypothesis is *literally* `havoid`, and the essentiality of the
chart's class map (the parallelism `V (-z) = c • V z` with negative factor at a boundary point) is
`Work.Drive.exists_neg_parallelism_of_planeChart`. -/
theorem exists_clauseHomotopy_linBase
    {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    (V : ℂ → Work.Drive.Eucl 3) (hVne : ∀ z : ℂ, V z ≠ 0)
    (hVsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hQcls : Work.Drive.IsClassLift Q V hVne)
    (a c' : UnitAddCircle) (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
    (cl : ℝ) (hcl : 0 < cl)
    (havoid : ∀ (k : Fin 3) (z : ℂ), ‖z‖ ≤ 1 → z.im = 0 →
      ¬ ∃ lam : ℝ, lam < 0 ∧
        Work.Drive.linBase A k (Work.Drive.linVecC z)
          = lam • Work.Drive.diagRotL (Work.Drive.designAnglesReal a c' k) (V z)) :
    ∃ H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Work.Drive.Eucl 3),
      (∀ k : Fin 3, ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.clauseB H0 k)) ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        H0 k (0, y) = Work.Drive.planeClassMap
          (Work.Drive.rotPresentation Q (Work.Drive.designAngles a c' k)) y) ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        H0 k (1, y) = Work.Drive.planeClassMap
          (Work.Drive.linPlaneOf (Work.Drive.linBase A) cl hcl k) y) ∧
      (∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
        Work.Drive.onSeam2 y → H0 k (s, Work.Drive.seamInv2 y) = H0 k (s, y)) := by
  -- the essentiality of the chart's class map, from `IsPlaneChart` alone
  obtain ⟨hpar, hneg⟩ := Work.Drive.exists_neg_parallelism_of_planeChart hγ hγne hQ V
    (fun z _ => hVne z) hVsmooth.continuous.continuousOn (fun z hz => (hQcls z).symm)
  -- the (B)-lane producer at `u = designAnglesReal a c'`, `φ = linBase A` and `χ = z ↦ z.im`
  obtain ⟨H, h0, h1, h2, _h3, h4⟩ :=
    Work.Drive.exists_homotopyClauses_rotPresentation Q V hVne hVsmooth hQcls hpar
      (z₀ := 1) (by simp) hneg
      (Work.Drive.designAnglesReal a c') (fun k => Work.Drive.linBase A k) cl hcl
      (fun _ => ⇑Complex.imCLM)
      (fun _ => Complex.imCLM.contDiff)
      (fun _ z _ => map_neg Complex.imCLM z)
      (by
        -- the zeros of `χ` are exactly the real diameter, where `havoid` holds
        intro k z hz hz0
        rintro ⟨lam, heq, hlt⟩
        exact havoid k z hz (by simpa using hz0) ⟨lam, hlt, heq⟩)
  refine ⟨H, fun k => contMDiff_clauseB_of_chain H k (h4 k), ?_, ?_, fun k s y hy => h2 k s y hy⟩
  · intro k y
    rw [show H k (0, y) = Work.Drive.planeClassMap (Work.Drive.rotPresentation Q
      ((Work.Drive.designAnglesReal a c' k : ℝ) : UnitAddCircle)) y from congrFun (h0 k) y]
    rw [Work.Drive.designAnglesReal_coe]
  · intro k y
    rw [show H k (1, y) = Work.Drive.planeClassMap (Work.Drive.diskPlane
      (Work.Drive.linPlaneChart (Work.Drive.linBase A k) cl hcl)) y from congrFun (h1 k) y]
    rfl

end Work.Drive
