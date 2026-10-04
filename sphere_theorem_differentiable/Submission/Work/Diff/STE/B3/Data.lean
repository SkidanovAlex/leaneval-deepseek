import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.GE.onFrameONfield
import Submission.Work.Diff.STE.Man.Sect
import Submission.Work.Diff.STE.fill.exists_chartBump

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3 of the STE design: the finite atlas data (cover, cut-offs, orthonormal frames)

This file packages **all the geometric data** on which the global Galerkin (Friedrichs-mollifier)
scheme of the short-time-existence proof runs, in the form fixed in `DESIGN.md`, SESSION 6, §6:

* a finite index type `ι₀` with chart centres `x₀ i` and radii `σ i > 0`, `2 σ i ≤ 1/4`;
* the *flat* coordinate ball of radius `2 σ i` around `x₀ i` lies in the chart target of `x₀ i`;
* smooth cut-off functions `χ i` on the flat coordinates, with `χ i = 1` on the closed ball of
  radius `σ i`, supported in the open unit cube (so that the localised chart components have a
  smooth periodisation) and with topological support inside the chart target;
* the closed balls of radius `σ i` cover `M`, and a subordinate *normalised weight family*
  `ζ i : M → ℝ` with `ζ i ≥ 0`, `Σ_i ζ i ^ 2 = 1` and `ζ i ≠ 0` only on the `σ i`-ball;
* for each `i` a family `e i a` of globally `C^∞` vector fields which is `g₀`-orthonormal at every
  point whose chart coordinate lies in the closed ball of radius `2 σ i`.

The weights `ζ` enter the components through the *localised weight*
`ψ i z = χ i z * ζ i (pt i z)`, which has `Σ_i ψ i (coord i p)^2 = 1` for every `p : M` (because
`χ i = 1` on the support of `ζ i`): this is the normalisation that makes the composite pairing of
Layer B3 (see `B3/Comp.lean`) equal to the intrinsic `L²(g₀)` pairing.

The `g₀`-orthonormal frames come from `Work.Diff.GE.onFrameONfield`; the covering radii are trimmed
so that the relevant ball is inside the orthonormality neighbourhood, which is why the cover is
constructed here (rather than reusing `Work.Diff.STE.fill.exists_flat_ball_cover` verbatim).
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The **flat coordinate** of `p` in the chart at `x₀`: the `finBasis`-coordinates of the chart
map, translated so that `x₀` has coordinate `0`. -/
def coord (x₀ p : M) : Fin (Module.finrank ℝ E) → ℝ :=
  (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) p)
    - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)

@[simp] lemma coord_apply (x₀ p : M) :
    coord (I := I) x₀ p
      = (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) p)
        - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) := rfl

/-- The closed **coordinate ball** of radius `r` around the chart centre `x₀`. -/
def coordBall (x₀ : M) (r : ℝ) : Set E :=
  {v : E | ‖(Module.finBasis ℝ E).equivFun v
    - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)‖ ≤ r}

/-- The open coordinate ball of radius `r`. -/
def coordBallOpen (x₀ : M) (r : ℝ) : Set E :=
  {v : E | ‖(Module.finBasis ℝ E).equivFun v
    - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)‖ < r}

/-- The set of points whose flat coordinate in the chart at `x₀` has norm `≤ r`. -/
def coordSet (x₀ : M) (r : ℝ) : Set M :=
  {p : M | ‖coord (I := I) x₀ p‖ ≤ r}

/-- `flatToE x₀ z` lies in the closed coordinate ball of radius `r` exactly when `‖z‖ ≤ r`. -/
lemma flatToE_mem_coordBall (x₀ : M) (r : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    flatToE (I := I) x₀ z ∈ coordBall (I := I) (M := M) x₀ r ↔ ‖z‖ ≤ r := by
  have h : (Module.finBasis ℝ E).equivFun (flatToE (I := I) x₀ z)
      = (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z := by
    simp only [flatToE]
    rw [LinearEquiv.apply_symm_apply]
  simp only [coordBall, Set.mem_setOf_eq, h]
  rw [add_sub_cancel_left]

/-- The chart centre lies in the closed coordinate ball of every nonnegative radius. -/
lemma mem_coordBall_self (x₀ : M) {r : ℝ} (hr : 0 ≤ r) :
    (extChartAt I x₀) x₀ ∈ coordBall (I := I) (M := M) x₀ r := by
  simp only [coordBall, Set.mem_setOf_eq]
  rw [sub_self, norm_zero]
  exact hr

/-- The open coordinate ball is open. -/
lemma isOpen_coordBallOpen (x₀ : M) (r : ℝ) :
    IsOpen (coordBallOpen (I := I) (M := M) x₀ r) := by
  have he : Continuous ⇑((Module.finBasis ℝ E).equivFun) := continuous_equivFun_basis _
  have h : coordBallOpen (I := I) (M := M) x₀ r = (Module.finBasis ℝ E).equivFun ⁻¹'
      Metric.ball ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)) r := by
    ext v
    simp only [coordBallOpen, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
  rw [h]
  exact Metric.isOpen_ball.preimage he

/-- The chart centre lies in the open coordinate ball of every positive radius. -/
lemma mem_coordBallOpen_self (x₀ : M) {r : ℝ} (hr : 0 < r) :
    (extChartAt I x₀) x₀ ∈ coordBallOpen (I := I) (M := M) x₀ r := by
  simp only [coordBallOpen, Set.mem_setOf_eq]
  rw [sub_self, norm_zero]
  exact hr

/-- The closed coordinate ball of radius `r` is contained in the open one of radius `r'` when
`r < r'`. -/
lemma coordBall_subset_coordBallOpen {r r' : ℝ} (h : r < r') (x₀ : M) :
    coordBall (I := I) (M := M) x₀ r ⊆ coordBallOpen (I := I) (M := M) x₀ r' :=
  fun _ hv => lt_of_le_of_lt hv h

/-- **The Layer B3 data.** -/
structure B3Data (ι₀ : Type*) [Fintype ι₀] (g₀ : SMet I M) where
  /-- the chart centres -/
  x₀ : ι₀ → M
  /-- the covering radii -/
  σ : ι₀ → ℝ
  hσ : ∀ i, 0 < σ i
  hσ2 : ∀ i, 2 * σ i ≤ 1 / 4
  /-- the closed `2σ`-coordinate ball lies in the chart target -/
  htarget : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * σ i →
    flatToE (I := I) (x₀ i) z ∈ (extChartAt I (x₀ i)).target
  /-- the cut-off functions -/
  χ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ
  hχsm : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i)
  hχ1 : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ σ i → χ i z = 1
  hχtsup : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), z ∈ tsupport (χ i) →
    flatToE (I := I) (x₀ i) z ∈ (extChartAt I (x₀ i)).target
  hχsupp : ∀ i, Function.support (χ i) ⊆
    Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
  /-- the covering property -/
  hcover : ∀ x : M, ∃ i : ι₀, x ∈ (extChartAt I (x₀ i)).source ∧
    ‖coord (I := I) (x₀ i) x‖ ≤ σ i
  /-- the normalised weight family -/
  ζ : ι₀ → M → ℝ
  hζsm : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (ζ i)
  hζnn : ∀ (i : ι₀) (p : M), 0 ≤ ζ i p
  hζsq : ∀ p : M, ∑ i : ι₀, (ζ i p) ^ 2 = 1
  hζsupp : ∀ (i : ι₀) (p : M), ζ i p ≠ 0 →
    p ∈ (extChartAt I (x₀ i)).source ∧ ‖coord (I := I) (x₀ i) p‖ < σ i
  /-- the `g₀`-orthonormal frame families -/
  e : ι₀ → Fin (Module.finrank ℝ E) → (Π p : M, TangentSpace I p)
  hesm : ∀ (i : ι₀) (a : Fin (Module.finrank ℝ E)), CMDiff ∞ (T% (e i a))
  heON : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * σ i →
    IsONFrame g₀ ((extChartAt I (x₀ i)).symm (flatToE (I := I) (x₀ i) z))
      (fun a => e i a _)

variable {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

namespace B3Data

/-- The point of `M` with flat coordinate `z` in the chart at `x₀ i`. -/
def pt (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : M :=
  (extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z)

/-- The **localised weight** of chart `i`: the cut-off `χ i` on the flat side times the normalised
weight `ζ i` at the corresponding point of `M`. -/
def psi (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : ℝ :=
  D.χ i z * D.ζ i (D.pt i z)

/-- The **volume density** of the chart at `x₀ i`: `√det` of the Gram matrix of the coordinate
frame at the point with flat coordinate `z` (so that `dvol_{g₀} = dens i z · dz`). -/
def dens (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
    (flatToE (I := I) (D.x₀ i) z))))

/-- On the `2σ`-ball the chart coordinate of `B3Data.pt` is the flat coordinate. -/
lemma extChartAt_pt (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ i) :
    (extChartAt I (D.x₀ i)) (D.pt i z) = flatToE (I := I) (D.x₀ i) z :=
  (extChartAt I (D.x₀ i)).right_inv (D.htarget i z hz)

/-- The flat coordinate of `pt i z` is `z`, on the `2σ`-ball. -/
lemma coord_pt (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ i) :
    coord (I := I) (D.x₀ i) (D.pt i z) = z := by
  have h : (Module.finBasis ℝ E).equivFun (flatToE (I := I) (D.x₀ i) z)
      = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z := by
    simp only [flatToE]
    rw [LinearEquiv.apply_symm_apply]
  simp only [coord, D.extChartAt_pt i hz, h, add_sub_cancel_left]

/-- `pt i (coord i p) = p` for `p` in the chart source of `x₀ i`. -/
lemma pt_coord (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) {p : M}
    (hp : p ∈ (extChartAt I (D.x₀ i)).source) :
    D.pt i (coord (I := I) (D.x₀ i) p) = p := by
  have harg : (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i))
      + ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p)
        - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)))
      = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p) := by abel
  have h : flatToE (I := I) (D.x₀ i) (coord (I := I) (D.x₀ i) p)
      = (extChartAt I (D.x₀ i)) p := by
    simp only [flatToE, coord]
    rw [harg, LinearEquiv.symm_apply_apply]
  simp only [pt, h]
  exact (extChartAt I (D.x₀ i)).left_inv hp

/-- On the chart source, the localised weight at the flat coordinate of `p` is the cut-off at that
coordinate times the normalised weight at `p`. -/
lemma psi_coord (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) {p : M}
    (hsrc : p ∈ (extChartAt I (D.x₀ i)).source) :
    D.psi i (coord (I := I) (D.x₀ i) p)
      = D.χ i (coord (I := I) (D.x₀ i) p) * D.ζ i p := by
  simp only [psi, D.pt_coord i hsrc]

/-- On the support of the normalised weight, the localised weight at the flat coordinate of `p`
is the normalised weight at `p`.  Consequently `Σ_i ψ i (coord i p)^2 = 1` at every point of the
common chart source. -/
lemma psi_coord_eq_zeta (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) {p : M}
    (h : D.ζ i p ≠ 0) : D.psi i (coord (I := I) (D.x₀ i) p) = D.ζ i p := by
  obtain ⟨hsrc, hlt⟩ := D.hζsupp i p h
  rw [D.psi_coord i hsrc, D.hχ1 i _ (le_of_lt hlt), one_mul]

/-- `pt_coord` in unfolded form: the chart inverse of the flat coordinate of `p` is `p` itself. -/
lemma symm_flatToE_coord (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) {p : M}
    (hp : p ∈ (extChartAt I (D.x₀ i)).source) :
    (extChartAt I (D.x₀ i)).symm
      (flatToE (I := I) (D.x₀ i) (coord (I := I) (D.x₀ i) p)) = p :=
  D.pt_coord i hp

/-- The localised weight vanishes where `χ i` does. -/
lemma psi_eq_zero_of_chi_eq_zero (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (h : D.χ i z = 0) : D.psi i z = 0 := by
  simp only [psi, h, zero_mul]

/-- The support of the localised weight is contained in the open unit cube. -/
lemma psi_supp (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    Function.support (D.psi i) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun z hz => D.hχsupp i (fun h => hz (D.psi_eq_zero_of_chi_eq_zero i h))

end B3Data

/-- **Existence of the Layer B3 data.** -/
theorem exists_B3Data [CompactSpace M] [T2Space M] [I.Boundaryless]
    (hLC : LCSmooth I M) (g₀ : SMet I M) :
    ∃ (ι₀ : Type) (_ : Fintype ι₀), Nonempty (B3Data (I := I) (M := M) ι₀ g₀) := by
  classical
  -- Step 0: comparison between the norm of `E` and the coordinate sup norm.
  obtain ⟨C, hCpos, hC⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ u : Fin (Module.finrank ℝ E) → ℝ,
        ‖(Module.finBasis ℝ E).equivFun.symm u‖ ≤ C * ‖u‖ := by
    let L : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E :=
      ((Module.finBasis ℝ E).equivFun.symm : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E)
    let f : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E := L.toContinuousLinearMap
    refine ⟨max ‖f‖ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun u => ?_⟩
    calc ‖(Module.finBasis ℝ E).equivFun.symm u‖ = ‖f u‖ := rfl
      _ ≤ ‖f‖ * ‖u‖ := f.le_opNorm u
      _ ≤ max ‖f‖ 1 * ‖u‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u)
  have hC' : ∀ v : E, ‖v‖ ≤ C * ‖(Module.finBasis ℝ E).equivFun v‖ := by
    intro v
    have := hC ((Module.finBasis ℝ E).equivFun v)
    rwa [LinearEquiv.symm_apply_apply] at this
  -- Step 1: at every point, a positive coordinate radius whose coordinate ball lies in the chart
  -- target.
  have hrad : ∀ x : M, ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E,
      ‖(Module.finBasis ℝ E).equivFun v
        - (Module.finBasis ℝ E).equivFun ((extChartAt I x) x)‖ < ρ →
      v ∈ (extChartAt I x).target := by
    intro x
    have hmem : (extChartAt I x) x ∈ (extChartAt I x).target := mem_extChartAt_target x
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_extChartAt_target (I := I) x).mem_nhds hmem)
    refine ⟨ε / C, div_pos hε hCpos, fun v hv => hsub ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub2 : (Module.finBasis ℝ E).equivFun (v - (extChartAt I x) x)
        = (Module.finBasis ℝ E).equivFun v
          - (Module.finBasis ℝ E).equivFun ((extChartAt I x) x) :=
      (Module.finBasis ℝ E).equivFun.map_sub _ _
    have h1 : ‖v - (extChartAt I x) x‖
        ≤ C * ‖(Module.finBasis ℝ E).equivFun (v - (extChartAt I x) x)‖ := hC' _
    rw [hsub2] at h1
    have h2 : C * ‖(Module.finBasis ℝ E).equivFun v
          - (Module.finBasis ℝ E).equivFun ((extChartAt I x) x)‖ < C * (ε / C) := by
      gcongr
    have h3 : C * (ε / C) = ε := by field_simp
    linarith
  choose ρ hρpos hρsub using hrad
  -- Step 2: at every point, a positive coordinate radius on which a fixed smooth frame is
  -- `g₀`-orthonormal.
  have hrad2 : ∀ x : M, ∃ (ρ₂ : ℝ) (E' : Fin (Module.finrank ℝ E) →
        (Π y : M, TangentSpace I y)),
      0 < ρ₂ ∧ (∀ a, CMDiff ∞ (T% (E' a))) ∧
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ < ρ₂ →
        IsONFrame g₀ ((extChartAt I x).symm (flatToE (I := I) x z)) (fun a => E' a _) := by
    intro x
    obtain ⟨E', hsm, hON, -⟩ := Work.Diff.GE.onFrameONfield hLC g₀ x
    -- pull the orthonormality statement back along `(extChartAt I x).symm`, which is continuous
    have hON' : ∀ᶠ y in 𝓝 x, IsONFrame g₀ y (fun a => E' a y) := hON
    obtain ⟨V, hVmem, hVsub⟩ := Filter.eventually_iff_exists_mem.mp hON'
    have hcont : ContinuousAt (extChartAt I x).symm ((extChartAt I x) x) :=
      continuousAt_extChartAt_symm (I := I) x
    have hself : (extChartAt I x).symm ((extChartAt I x) x) = x :=
      (extChartAt I x).left_inv (by rw [extChartAt_source]; exact mem_chart_source H x)
    have hpre : (extChartAt I x).symm ⁻¹' V ∈ 𝓝 ((extChartAt I x) x) := by
      have hVmem' : V ∈ 𝓝 ((extChartAt I x).symm ((extChartAt I x) x)) := by rwa [hself]
      exact hcont.preimage_mem_nhds hVmem'
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨ε / (2 * C), E', div_pos hε (by positivity), hsm, ?_⟩
    intro z hz
    apply hVsub
    apply hsub
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : flatToE (I := I) x z - (extChartAt I x) x
        = (Module.finBasis ℝ E).equivFun.symm z := by
      simp only [flatToE]
      rw [LinearEquiv.map_add, LinearEquiv.symm_apply_apply]
      abel
    rw [heq]
    calc ‖(Module.finBasis ℝ E).equivFun.symm z‖ ≤ C * ‖z‖ := hC z
      _ < C * (ε / (2 * C)) := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  choose ρ₂ E' hρ₂pos hE'sm hρ₂ON using hrad2
  -- Step 3: trim the radii so that the `2σ`-ball still lies in both the chart target and the
  -- orthonormality set, and so that `2σ ≤ 1/4`.
  let S : M → ℝ := fun x => min (min (ρ x / 4) (ρ₂ x / 4)) (1 / 16)
  have hSpos : ∀ x, 0 < S x := by
    intro x
    refine lt_min (lt_min (by have := hρpos x; linarith) (by have := hρ₂pos x; linarith))
      (by norm_num)
  have hSle : ∀ x, 2 * S x ≤ 1 / 4 := by
    intro x; have h := min_le_right (min (ρ x / 4) (ρ₂ x / 4)) (1 / 16 : ℝ); linarith
  have hSltρ : ∀ x, 2 * S x < ρ x := by
    intro x; have h := min_le_left (min (ρ x / 4) (ρ₂ x / 4)) (1 / 16 : ℝ)
    have h' := min_le_left (ρ x / 4) (ρ₂ x / 4)
    have hp := hρpos x; linarith
  have hSltρ₂ : ∀ x, 2 * S x < ρ₂ x := by
    intro x; have h := min_le_left (min (ρ x / 4) (ρ₂ x / 4)) (1 / 16 : ℝ)
    have h' := min_le_right (ρ x / 4) (ρ₂ x / 4)
    have hp := hρ₂pos x; linarith
  -- Step 4: the corresponding coordinate balls form an open cover of `M`.
  have hOpen : ∀ x : M, IsOpen ((chartAt H x).source ∩
      (extChartAt I x) ⁻¹' coordBallOpen (I := I) (M := M) x (S x)) := fun x =>
    isOpen_extChartAt_preimage (I := I) x (isOpen_coordBallOpen x (S x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt H x).source ∩
      (extChartAt I x) ⁻¹' coordBallOpen (I := I) (M := M) x (S x))
    hOpen
    (fun y _ => Set.mem_iUnion.mpr ⟨y, mem_chart_source H y,
      mem_coordBallOpen_self (I := I) y (hSpos y)⟩)
  -- Step 5: enumerate the finite subcover by `Fin t.card`.
  let x₀ : Fin t.card → M := fun i => ((t.equivFin.symm i : {x // x ∈ t}) : M)
  let σ : Fin t.card → ℝ := fun i => S (x₀ i)
  have hσpos : ∀ i, 0 < σ i := fun i => hSpos (x₀ i)
  have hσle : ∀ i, 2 * σ i ≤ 1 / 4 := fun i => hSle (x₀ i)
  have htarget : ∀ (i : Fin t.card) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * σ i →
      flatToE (I := I) (x₀ i) z ∈ (extChartAt I (x₀ i)).target := by
    intro i z hz
    have hlt : ‖z‖ < ρ (x₀ i) := lt_of_le_of_lt hz (hSltρ (x₀ i))
    have hz' : ‖(Module.finBasis ℝ E).equivFun (flatToE (I := I) (x₀ i) z)
        - (Module.finBasis ℝ E).equivFun ((extChartAt I (x₀ i)) (x₀ i))‖ < ρ (x₀ i) := by
      have h : (Module.finBasis ℝ E).equivFun (flatToE (I := I) (x₀ i) z)
          = (Module.finBasis ℝ E).equivFun ((extChartAt I (x₀ i)) (x₀ i)) + z := by
        simp only [flatToE]
        rw [LinearEquiv.apply_symm_apply]
      rw [h, add_sub_cancel_left]
      exact hlt
    exact hρsub (x₀ i) _ hz'
  have hframeON : ∀ (i : Fin t.card) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * σ i →
      IsONFrame g₀ ((extChartAt I (x₀ i)).symm (flatToE (I := I) (x₀ i) z))
        (fun a => E' (x₀ i) a _) := by
    intro i z hz
    exact hρ₂ON (x₀ i) z (lt_of_le_of_lt hz (hSltρ₂ (x₀ i)))
  have hcoverOpen : ∀ x : M, ∃ i : Fin t.card, x ∈ (extChartAt I (x₀ i)).source ∧
      ‖coord (I := I) (x₀ i) x‖ < σ i := by
    intro y
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    refine ⟨t.equivFin ⟨x, hx⟩, ?_, ?_⟩
    · have hxx : x₀ (t.equivFin ⟨x, hx⟩) = x := by
        simp only [x₀]
        rw [Equiv.symm_apply_apply]
      rw [extChartAt_source, hxx]
      exact hyx.1
    · have hxx : x₀ (t.equivFin ⟨x, hx⟩) = x := by
        simp only [x₀]
        rw [Equiv.symm_apply_apply]
      have hσ : σ (t.equivFin ⟨x, hx⟩) = S x := by simp only [σ, hxx]
      rw [hxx, hσ]
      exact hyx.2
  have hcover : ∀ x : M, ∃ i : Fin t.card, x ∈ (extChartAt I (x₀ i)).source ∧
      ‖coord (I := I) (x₀ i) x‖ ≤ σ i := fun x => by
    obtain ⟨i, h1, h2⟩ := hcoverOpen x
    exact ⟨i, h1, le_of_lt h2⟩
  -- Step 6: a smooth partition of unity subordinate to the balls, normalised so that the squares
  -- sum to one.
  obtain ⟨η, hηsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I) isClosed_univ
    (fun i : Fin t.card => (chartAt H (x₀ i)).source ∩
      (extChartAt I (x₀ i)) ⁻¹' coordBallOpen (I := I) (M := M) (x₀ i) (σ i))
    (fun i => isOpen_extChartAt_preimage _ (isOpen_coordBallOpen _ _))
    (fun x _ => by
      obtain ⟨i, hsrc, hi⟩ := hcoverOpen x
      exact Set.mem_iUnion.mpr ⟨i, ⟨by rwa [extChartAt_source] at hsrc,
        by simpa only [Set.mem_preimage, coordBallOpen, Set.mem_setOf_eq, coord] using hi⟩⟩)
  let T : M → ℝ := fun p => ∑ i : Fin t.card, (η i p) ^ 2
  have hTpos : ∀ p : M, 0 < T p := by
    intro p
    have hsum : ∑ i : Fin t.card, η i p = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using η.sum_eq_one (Set.mem_univ p)
    obtain ⟨i, hi⟩ : ∃ i, η i p ≠ 0 := by
      by_contra h
      push_neg at h
      have hzero : ∑ i : Fin t.card, η i p = 0 := Finset.sum_eq_zero fun i _ => h i
      rw [hsum] at hzero
      exact one_ne_zero hzero
    have hpos : 0 < (η i p) ^ 2 := by positivity
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, hpos⟩
  let ζ : Fin t.card → M → ℝ := fun i p => η i p / Real.sqrt (T p)
  have hζsm : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (ζ i) := by
    intro i
    have hTsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ T := by
      simp only [T]
      exact ContMDiff.sum fun j _ => (η.toFun j).contMDiff.pow 2
    have hsqrt : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun p : M => Real.sqrt (T p)) := by
      intro p
      exact ContMDiffAt.comp p
        (contMDiffAt_iff_contDiffAt.mpr (Real.contDiffAt_sqrt (hTpos p).ne'))
        hTsm.contMDiffAt
    exact (η.toFun i).contMDiff.div₀ hsqrt fun p =>
      (Real.sqrt_pos.mpr (hTpos p)).ne'
  have hζnn : ∀ (i : Fin t.card) (p : M), 0 ≤ ζ i p := by
    intro i p
    exact div_nonneg (η.nonneg i p) (Real.sqrt_nonneg _)
  have hζsq : ∀ p : M, ∑ i : Fin t.card, (ζ i p) ^ 2 = 1 := by
    intro p
    have h : ∑ i : Fin t.card, (ζ i p) ^ 2
        = (∑ i : Fin t.card, (η i p) ^ 2) / T p := by
      simp only [ζ, div_pow, Finset.sum_div, Real.sq_sqrt (le_of_lt (hTpos p))]
    rw [h]
    exact div_self (hTpos p).ne'
  have hζsupp : ∀ (i : Fin t.card) (p : M), ζ i p ≠ 0 →
      p ∈ (extChartAt I (x₀ i)).source ∧ ‖coord (I := I) (x₀ i) p‖ < σ i := by
    intro i p hp
    have hη : η i p ≠ 0 := by
      intro h0
      exact hp (by simp only [ζ, h0, zero_div])
    have hmem : p ∈ tsupport (⇑(η i)) := subset_closure hη
    have hsub := hηsub i hmem
    refine ⟨by rw [extChartAt_source]; exact hsub.1, ?_⟩
    simpa only [Set.mem_preimage, coordBallOpen, Set.mem_setOf_eq, coord] using hsub.2
  -- Step 7: the cut-off functions.
  choose χ hχsm hχ1 hχtsup hχsupp using fun i : Fin t.card =>
    fill.exists_chartBump (I := I) (x₀ i) (hσpos i) (hσle i) (htarget i)
  exact ⟨Fin t.card, inferInstance,
    ⟨x₀, σ, hσpos, hσle, htarget, χ, hχsm, hχ1, hχtsup, hχsupp, hcover,
      ζ, hζsm, hζnn, hζsq, hζsupp,
      fun i => E' (x₀ i), fun i a => hE'sm (x₀ i) a, hframeON⟩⟩

end Work.Diff.STE
