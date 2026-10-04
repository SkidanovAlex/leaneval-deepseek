import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.mat_Rstar_bound
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.tsupport_zeta_subset
import Submission.Work.Diff.STE.D.ChartData_Rstar
import Submission.Work.Diff.STE.D.bump_smul_smooth
import Submission.Work.Diff.STE.D.flatToE_mem_interior_target
import Submission.Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior
import Submission.Work.Diff.STE.D.transMap_interior_contDiffAt
import Submission.Work.Diff.STE.D.dens_interior_contDiffAt
import Submission.Work.Diff.STE.B3.BPair_Rstar
import Submission.Work.EXT.exists_smooth_ONFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer D, step 2: the cross-chart expansion of `R_j (R*_i u)`

For the Layer B3 data `D`, the localised component `R_j F a b` of a section `F` in the chart `j` is
`ψ_j · √dens_j · F (pt_j z) (e_j a) (e_j b)`, and the reconstruction `R*_i u` has the frame
expansion of `B3/Rstar_apply.lean`:

`R*_i u p X Y = ζ_i p · χ_i (coord_i p) · (√dens_i (coord_i p))⁻¹ ·
    Σ_{cd} u_{cd} (coord_i p) · ⟪X, e_i c⟫ · ⟪Y, e_i d⟫`.

Hence, at every flat point `z` (with `T z := coord_i (pt_j z)`),

`R_j (R*_i u) a b z = Σ_{cd} f_{cd} z · u_{cd} (T z)`

for the *explicit* coefficient `coeffFun` below.  The content of the present file is that this
coefficient — built from the chart expressions `ψ_j`, `√dens_j`, `ζ_i ∘ pt_j`, `χ_i ∘ T`,
`√dens_i ∘ T` and the frame pairings — can be replaced by a *globally* `C^∞` function with support
in the centred cube, and simultaneously the transition `T` by a globally `C^∞` map.

Both replacements come from the single device `Work.Diff.STE.D.bump_smul_smooth`: multiply the
junk-valued total function by a smooth bump whose `tsupport` lies inside the open set (`goodSet`)
where the chart expressions are *genuine and smooth*, and which contains the closure of

`Omega := {z | ψ_j z ≠ 0 and ζ_i (pt_j z) ≠ 0}`

— the set where the identity is not forced to be trivial.  Outside `Omega` one has
`ζ_i (pt_j z) = 0` (either genuinely or because `ζ_i` vanishes off the chart source, `hζsupp`), so
`coeffFun` vanishes there and the value of `T` is irrelevant.

The point that makes `goodSet ⊇ closure Omega` *without* `[I.Boundaryless]` is that in the B3 data
all relevant flat coordinates have norm `< σ i ≤ (1/2) · 2σ i`, so they lie in the *interior* of the
chart target (`Work.Diff.STE.D.flatToE_mem_interior_target`): this is exactly what makes the chart
inverse (hence `pt i` and `dens i`) smooth there.
-/

namespace Work.Diff.STE.D

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

set_option linter.unusedSectionVars false

/-- **The flat transition map**: the `i`-flat coordinate of `pt j z`. -/
def tMapFun (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : Fin (Module.finrank ℝ E) → ℝ :=
  Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)

@[simp] lemma tMapFun_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    tMapFun (I := I) (M := M) D i j z
      = Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z) := rfl

/-- **The coefficient of the cross-chart expansion**
`R_j (R*_i u) a b z = Σ_{cd} f_{cd} z · u_{cd} (T z)`. -/
def coeffFun (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) : ℝ :=
  D.psi j z * Real.sqrt (D.dens j z) *
    (D.ζ i (D.pt j z) * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) *
      (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹) *
    (g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z))) *
    (g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z)))

/-- **The flat region on which all the chart expressions of the pair `(i,j)` are genuine *and*
smooth**: the chart `j` is genuine with room to spare at `z`, the point `pt j z` lies in the source
of the chart `i`, and its chart-`i` coordinate is interior to the chart-`i` target. -/
def goodSet (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ interior ((extChartAt I (D.x₀ j)).target) ∧
       D.pt j z ∈ (extChartAt I (D.x₀ i)).source ∧
       (extChartAt I (D.x₀ i)) (D.pt j z) ∈ interior ((extChartAt I (D.x₀ i)).target)}

/-- **The set where the reconstruction genuinely contributes**: `ψ_j z ≠ 0` and the weight
`ζ_i (pt_j z)` does not vanish. -/
def Omega (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | D.psi j z ≠ 0 ∧ D.ζ i (D.pt j z) ≠ 0}

section Algebra

/-- **Distributing a constant product over a double sum.** -/
lemma factor_sum {n : ℕ} (A K : ℝ) (X Y : Fin n → ℝ) (g : Fin n → Fin n → ℝ) :
    (∑ c, ∑ d, (A * K * X c * Y d) * g c d)
      = A * (K * (∑ c, ∑ d, g c d * X c * Y d)) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
  (a b : Fin (Module.finrank ℝ E))

/-- **The cross-chart expansion, pointwise and for every coefficient family `u`.** -/
lemma R_Rstar_expansion_pointwise
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.R j (D.Rstar i u) a b z
      = ∑ c, ∑ d, coeffFun (I := I) (M := M) D i j a b c d z
          * u c d (tMapFun (I := I) (M := M) D i j z) := by
  rw [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3.mat_Rstar_apply_eq D i j u a b z]
  simp only [coeffFun, tMapFun]
  rw [factor_sum]

end Algebra

section Geometry

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)

/-- The closed flat `σ i`-ball is compact. -/
lemma isCompact_sigmaClosedBall
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    IsCompact (Work.Diff.STE.B3.sigmaClosedBall (I := I) (M := M) D i) := by
  rw [show Work.Diff.STE.B3.sigmaClosedBall (I := I) (M := M) D i
      = Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) from by
    ext z
    simp only [Work.Diff.STE.B3.sigmaClosedBall, Set.mem_ofPred_eq, Metric.mem_closedBall,
      dist_eq_norm, sub_zero]]
  exact isCompact_closedBall _ _

/-- `Omega` is contained in the closed flat `σ j`-ball. -/
lemma Omega_subset_sigmaClosedBall :
    Omega (I := I) (M := M) D i j ⊆ Work.Diff.STE.B3.sigmaClosedBall D j :=
  fun _ hz => le_of_lt (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hz.1)

/-- The closure of `Omega` is compact. -/
lemma isCompact_closure_Omega : IsCompact (closure (Omega (I := I) (M := M) D i j)) :=
  (isCompact_sigmaClosedBall (I := I) (M := M) D j).of_isClosed_subset isClosed_closure
    (closure_minimal (Omega_subset_sigmaClosedBall (I := I) (M := M) D i j)
      (isCompact_sigmaClosedBall (I := I) (M := M) D j).isClosed)

/-- The parametrisation `pt j` is continuous on the closure of `Omega`. -/
lemma continuousOn_pt_closure_Omega :
    ContinuousOn (fun z => D.pt j z) (closure (Omega (I := I) (M := M) D i j)) :=
  (Work.Diff.STE.B3.continuousOn_pt_sigmaClosedBall' (I := I) D j).mono
    (closure_minimal (Omega_subset_sigmaClosedBall (I := I) (M := M) D i j)
      (isCompact_sigmaClosedBall (I := I) (M := M) D j).isClosed)

/-- **On the closure of `Omega`, `pt j z` lies in the source of the chart `i`.** -/
lemma pt_mem_source_of_mem_closure_Omega {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ closure (Omega (I := I) (M := M) D i j)) :
    D.pt j z ∈ (extChartAt I (D.x₀ i)).source := by
  have h1 : Set.MapsTo (fun z => D.pt j z) (Omega (I := I) (M := M) D i j)
      (tsupport (D.ζ i)) := by
    intro w hw
    exact subset_closure (fun h0 => hw.2 h0)
  have h2 := Set.MapsTo.closure_of_continuousOn h1
    (continuousOn_pt_closure_Omega (I := I) (M := M) D i j)
  have h3 : D.pt j z ∈ tsupport (D.ζ i) := by
    have h4 := h2 hz
    rwa [(isClosed_tsupport (D.ζ i)).closure_eq] at h4
  exact Work.Diff.STE.D.tsupport_zeta_subset (I := I) D i h3

/-- `pt j` composed with the chart-`i` coordinate is continuous on the closure of `Omega`. -/
lemma continuousOn_coord_pt_closure_Omega :
    ContinuousOn (fun z => Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
      (closure (Omega (I := I) (M := M) D i j)) := by
  intro z hz
  exact (Work.Diff.STE.B3.rp_continuousAt_coord (I := I) (D.x₀ i)
      (pt_mem_source_of_mem_closure_Omega (I := I) (M := M) D i j hz)).comp_continuousWithinAt
    ((continuousOn_pt_closure_Omega (I := I) (M := M) D i j).continuousWithinAt hz)

/-- On the closure of `Omega`, the chart-`i` coordinate of `pt j z` has norm `≤ σ i`. -/
lemma norm_coord_le_sigma_of_mem_closure_Omega {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ closure (Omega (I := I) (M := M) D i j)) :
    ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)‖ ≤ D.σ i := by
  have h1 : Set.MapsTo (fun z => Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
      (Omega (I := I) (M := M) D i j)
      (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)) := by
    intro w hw
    simpa only [Metric.mem_ball, dist_zero_right] using (D.hζsupp i (D.pt j w) hw.2).2
  have h2 := Set.MapsTo.closure_of_continuousOn h1
    (continuousOn_coord_pt_closure_Omega (I := I) (M := M) D i j)
  have h3 := h2 hz
  rwa [closure_ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.hσ i).ne',
    Metric.mem_closedBall, dist_zero_right] at h3

/-- **The flat `i`-coordinate of a point of the chart-`i` source is the chart-`i` image.** -/
lemma flatToE_coord {p : M} (_hp : p ∈ (extChartAt I (D.x₀ i)).source) :
    Work.Diff.STE.flatToE (I := I) (D.x₀ i) (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
      = (extChartAt I (D.x₀ i)) p := by
  have harg : (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i))
      + ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p)
        - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)))
      = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p) := by abel
  simp only [Work.Diff.STE.flatToE, Work.Diff.STE.coord]
  rw [harg, LinearEquiv.symm_apply_apply]

/-- **The closure of `Omega` is contained in `goodSet`.** -/
lemma closure_Omega_subset_goodSet :
    closure (Omega (I := I) (M := M) D i j) ⊆ goodSet (I := I) (M := M) D i j := by
  intro z hz
  have hzb : ‖z‖ ≤ D.σ j :=
    closure_minimal (Omega_subset_sigmaClosedBall (I := I) (M := M) D i j)
      (isCompact_sigmaClosedBall (I := I) (M := M) D j).isClosed hz
  have hcoord : (extChartAt I (D.x₀ i)) (D.pt j z)
      = Work.Diff.STE.flatToE (I := I) (D.x₀ i)
        (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) :=
    (flatToE_coord (I := I) (M := M) D i
      (pt_mem_source_of_mem_closure_Omega (I := I) (M := M) D i j hz)).symm
  exact ⟨Work.Diff.STE.D.flatToE_mem_interior_target (I := I) D j z hzb,
    pt_mem_source_of_mem_closure_Omega (I := I) (M := M) D i j hz,
    by
      rw [hcoord]
      exact Work.Diff.STE.D.flatToE_mem_interior_target (I := I) D i _
        (norm_coord_le_sigma_of_mem_closure_Omega (I := I) (M := M) D i j hz)⟩

/-- **`goodSet` is open.** -/
lemma isOpen_goodSet : IsOpen (goodSet (I := I) (M := M) D i j) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hz1, hz2, hz3⟩ := hz
  have hpt : ContinuousAt (D.pt j) z :=
    (Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz1).continuousAt
  have hflat : ContinuousAt (Work.Diff.STE.flatToE (I := I) (D.x₀ j)) z :=
    (Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ j)).continuous.continuousAt
  have h1 : Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹'
      interior ((extChartAt I (D.x₀ j)).target) ∈ 𝓝 z :=
    hflat.preimage_mem_nhds (isOpen_interior.mem_nhds hz1)
  have h2 : D.pt j ⁻¹' (extChartAt I (D.x₀ i)).source ∈ 𝓝 z :=
    hpt.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) (D.x₀ i)).mem_nhds hz2)
  have h3 : (fun w => (extChartAt I (D.x₀ i)) (D.pt j w)) ⁻¹'
      interior ((extChartAt I (D.x₀ i)).target) ∈ 𝓝 z :=
    ((continuousAt_extChartAt' (I := I) hz2).comp hpt).preimage_mem_nhds
      (isOpen_interior.mem_nhds hz3)
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem h1 h2) h3) ?_
  intro w hw
  exact ⟨hw.1.1, hw.1.2, hw.2⟩

end Geometry

section Smoothness

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
  (a b : Fin (Module.finrank ℝ E))

/-- The transition map is `C^∞` at every point of `goodSet`. -/
lemma tMapFun_contDiffAt {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (tMapFun (I := I) (M := M) D i j) z := by
  show ContDiffAt ℝ (⊤ : ℕ∞)
    (fun w => Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w)) z
  exact Work.Diff.STE.D.transMap_interior_contDiffAt (I := I) D i j z hz.1 hz.2.1

lemma tMapFun_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) (tMapFun (I := I) (M := M) D i j)
      (goodSet (I := I) (M := M) D i j) :=
  fun _ hz => (tMapFun_contDiffAt (I := I) (M := M) D i j hz).contDiffWithinAt

/-- `ζ i ∘ pt j` is `C^∞` at every point of `goodSet`. -/
lemma contDiffAt_zeta_pt {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ i (D.pt j w)) z := by
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz.1
  exact contMDiffAt_iff_contDiffAt.mp (((D.hζsm i).contMDiffAt).comp z hpt)

/-- The localised weight `ψ j` is `C^∞` at every point of `goodSet`. -/
lemma contDiffAt_psi {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (D.psi j) z := by
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz.1
  have hζ : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ j (D.pt j w)) z :=
    contMDiffAt_iff_contDiffAt.mp (((D.hζsm j).contMDiffAt).comp z hpt)
  show ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.χ j w * D.ζ j (D.pt j w)) z
  simpa only [Pi.mul_apply] using (D.hχsm j).contDiffAt.mul hζ

/-- The metric pairing of two smooth fields, composed with `pt j`, is `C^∞` at a point of
`goodSet`. -/
lemma contDiffAt_pairing_pt (k : ι₀) (c' d' : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : z ∈ goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (D.e k c' (D.pt j w)) (D.e i d' (D.pt j w))) z := by
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz.1
  have hpair := Work.EXT.ONF.pairing g₀ (D.pt j z)
    ((D.hesm k c').contMDiffAt) ((D.hesm i d').contMDiffAt)
  exact contMDiffAt_iff_contDiffAt.mp (hpair.comp z hpt)

/-- **The coefficient is `C^∞` at every point of `goodSet`.** -/
lemma coeffFun_contDiffAt (c d : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : z ∈ goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coeffFun (I := I) (M := M) D i j a b c d) z := by
  have hpsi : ContDiffAt ℝ (⊤ : ℕ∞) (D.psi j) z := contDiffAt_psi (I := I) (M := M) D i j hz
  have hdj : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens j) z :=
    Work.Diff.STE.D.dens_interior_contDiffAt (I := I) D j z hz.1
  have hdjpos : D.dens j z ≠ 0 :=
    (Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) D j (interior_subset hz.1)).ne'
  have hsj : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => Real.sqrt (D.dens j w)) z :=
    (Real.contDiffAt_sqrt hdjpos).comp z hdj
  have hzi : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ i (D.pt j w)) z :=
    contDiffAt_zeta_pt (I := I) (M := M) D i j hz
  have hT : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w)) z :=
    tMapFun_contDiffAt (I := I) (M := M) D i j hz
  have hchi : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w))) z :=
    (D.hχsm i).contDiffAt.comp z hT
  have hflat : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
      = (extChartAt I (D.x₀ i)) (D.pt j z) :=
    flatToE_coord (I := I) (M := M) D i hz.2.1
  have hdi : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens i)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) :=
    Work.Diff.STE.D.dens_interior_contDiffAt (I := I) D i _ (by rw [hflat]; exact hz.2.2)
  have hdipos : 0 < D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) :=
    Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) D i
      (by rw [hflat]; exact interior_subset hz.2.2)
  have hsi : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Real.sqrt (D.dens i y))
      (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) :=
    (Real.contDiffAt_sqrt hdipos.ne').comp _ hdi
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i)
        (D.pt j w))))⁻¹) z := by
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i)
          (D.pt j w)))) z :=
      ContDiffAt.comp (x := z)
        (f := fun w => Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w)) hsi hT
    exact hcomp.inv (Real.sqrt_pos.mpr hdipos).ne'
  have hpair1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (D.e j a (D.pt j w)) (D.e i c (D.pt j w))) z :=
    contDiffAt_pairing_pt (I := I) (M := M) D i j j a c hz
  have hpair2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (D.e j b (D.pt j w)) (D.e i d (D.pt j w))) z :=
    contDiffAt_pairing_pt (I := I) (M := M) D i j j b d hz
  have hK : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => D.ζ i (D.pt j w) * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w))
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w))))⁻¹) z :=
    (hzi.mul hchi).mul hinv
  show ContDiffAt ℝ (⊤ : ℕ∞) (coeffFun (I := I) (M := M) D i j a b c d) z
  exact (((hpsi.mul hsj).mul hK).mul hpair1).mul hpair2

lemma coeffFun_contDiffOn (c d : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coeffFun (I := I) (M := M) D i j a b c d)
      (goodSet (I := I) (M := M) D i j) :=
  fun _ hz => (coeffFun_contDiffAt (I := I) (M := M) D i j a b c d hz).contDiffWithinAt

end Smoothness

theorem R_Rstar_expansion2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ∃ (T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ))
      (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) T ∧
      (∀ c d, ContDiff ℝ (⊤ : ℕ∞) (f c d)) ∧
      (∀ c d, Function.support (f c d) ⊆
        Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) ∧
      (∀ (c d : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        D.psi j z = 0 → f c d z = 0) ∧
      ∀ (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
            (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
        (z : Fin (Module.finrank ℝ E) → ℝ), D.psi j z ≠ 0 →
        D.R j (D.Rstar i u) a b z = ∑ c, ∑ d, f c d z * u c d (T z) := by
  classical
  have hK : IsCompact (closure (Omega (I := I) (M := M) D i j)) :=
    isCompact_closure_Omega (I := I) (M := M) D i j
  have hU : IsOpen (goodSet (I := I) (M := M) D i j) :=
    isOpen_goodSet (I := I) (M := M) D i j
  have hKU : closure (Omega (I := I) (M := M) D i j)
      ⊆ goodSet (I := I) (M := M) D i j :=
    closure_Omega_subset_goodSet (I := I) (M := M) D i j
  choose φf hφf using fun (cd : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) =>
    Work.Diff.STE.D.bump_smul_smooth (closure (Omega (I := I) (M := M) D i j))
      (goodSet (I := I) (M := M) D i j) hK hU hKU
      (coeffFun (I := I) (M := M) D i j a b cd.1 cd.2)
      (coeffFun_contDiffOn (I := I) (M := M) D i j a b cd.1 cd.2)
  choose φT hφT using
    Work.Diff.STE.D.bump_smul_smooth (closure (Omega (I := I) (M := M) D i j))
      (goodSet (I := I) (M := M) D i j) hK hU hKU
      (tMapFun (I := I) (M := M) D i j)
      (tMapFun_contDiffOn (I := I) (M := M) D i j)
  refine ⟨fun z => φT z • tMapFun (I := I) (M := M) D i j z,
    fun c d z => φf (c, d) z * coeffFun (I := I) (M := M) D i j a b c d z,
    hφT.2.2.2, ?_, ?_, ?_, ?_⟩
  · intro c d
    simpa only [smul_eq_mul] using (hφf (c, d)).2.2.2
  · intro c d z hz
    have hne : D.psi j z ≠ 0 := fun h0 =>
      hz (by simp only [coeffFun, h0, mul_zero, zero_mul])
    exact D.psi_supp j hne
  · intro c d z hz0
    simp only [coeffFun, hz0, mul_zero, zero_mul]
  · intro u z hz
    rw [R_Rstar_expansion_pointwise (I := I) (M := M) D i j a b u z]
    by_cases hzeta : D.ζ i (D.pt j z) = 0
    · have hcoeff : ∀ c d, coeffFun (I := I) (M := M) D i j a b c d z = 0 := fun c d =>
        by simp only [coeffFun, hzeta, mul_zero, zero_mul]
      simp only [hcoeff, mul_zero, zero_mul, Finset.sum_const_zero]
    · have hzO : z ∈ Omega (I := I) (M := M) D i j := ⟨hz, hzeta⟩
      have hφz : ∀ c d, φf (c, d) z = 1 :=
        fun c d => (hφf (c, d)).2.1 z (subset_closure hzO)
      have hφTz : φT z = 1 := hφT.2.1 z (subset_closure hzO)
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro d _
      simp only [tMapFun, hφz c d, hφTz, one_mul, one_smul]

end

end Work.Diff.STE.D
