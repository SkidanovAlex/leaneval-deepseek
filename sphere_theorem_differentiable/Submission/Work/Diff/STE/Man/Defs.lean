/-
# The manifold layer of the short-time existence proof: chart packaging

This file fixes the **vocabulary** of the manifold layer (design §B/§C of `STE/DESIGN.md`): the
translation between a chart of `M` and the flat torus `(Fin n → ℝ)` on which the flat analytic core
(`Work.Diff.STE.Flat.TorusShortTimeExistenceSymm`) is stated.

Fix a chart centre `x₀ : M`, let `n = Module.finrank ℝ E`, `bB = Module.finBasis ℝ E`,
`y₀ = extChartAt I x₀ x₀` (the chart coordinate of the centre).

* `chartCoord x₀ p = bB.equivFun (extChartAt I x₀ p - y₀)` — the *torus coordinate* of a point of
  the chart (translated so that the centre is `0`);
* `chartCoordSymm x₀ z = y₀ + bB.equivFun.symm z` — its inverse on the model space;
* `flatChartMat g x₀ z = chartMatFun g x₀ (chartCoordSymm x₀ z)` — the chart matrix of the metric
  `g`, read as a function of the torus coordinate (a real `MatE`-valued function);
* `torBump r` — a smooth bump on `(Fin n → ℝ)`, `1` on the closed ball of radius `r/2` and
  supported in the open ball of radius `r`;
* `chartDatumR g x₀ r` — the *periodisation* of the localised chart matrix
  `z ↦ flatChartMat g x₀ 0 + torBump r z • (flatChartMat g x₀ z - flatChartMat g x₀ 0)`,
  i.e. the smooth `1`-periodic positive-definite matrix-valued function which agrees with the chart
  matrix of `g` on a neighbourhood of `0`.  This is the initial datum `u₀` (for `g = g₀`) and the
  background jet `(Abar, Lbar, Bbar)` (same function) of the flat Cauchy problem;
* `chartDatum g x₀ r` — the same, as a complex matrix (`Torus n`) for the flat theory;
* `linMatOf` / `bilMatOf` — the (continuous, linear) extensions of coordinate-indexed jet families
  to the model space `E`, converting the flat jets `Fin n → MatE` into the `LinMat`/`BilMat` of
  `Work.Diff.STE.DeTurck.pPhi`;
* `chartNonlin bg` — the chart nonlinearity `Φ` fed to the flat theorem: it evaluates `pPhi` at the
  background jets `(bg, ∂bg, ∂²bg)` and at the jets `(A, L, B)` of the unknown.

The properties of these objects (smoothness, periodicity, positive definiteness, the agreement with
the chart matrix near `0`, `IsDeTurckNonlin`, `ConjEquivNonlin`, and the jet symmetry) are proved in
the sibling files of this directory.
-/
import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.STE.DeTurckJet
import Submission.Work.Diff.STE.DeTurckField
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.deTurck.pPhi_decomp
import Submission.Work.Diff.STE.deTurck.pPhi_symm
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.Man

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

/-- The number of coordinates. -/
abbrev dim (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] : ℕ :=
  Module.finrank ℝ E

/-- The chart coordinate of the centre: `y₀ = extChartAt I x₀ x₀`. -/
noncomputable def chartCentre (I : ModelWithCorners ℝ E H) (x₀ : M) : E :=
  (extChartAt I x₀) x₀

/-- **The torus coordinate of a point of the chart at `x₀`**: the coordinates of the chart image in
the canonical basis `bB`, translated so that the chart centre is the origin. -/
noncomputable def chartCoord (I : ModelWithCorners ℝ E H) (x₀ : M) (p : M) :
    Fin (dim E) → ℝ :=
  (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) p - chartCentre I x₀)

/-- **The inverse of the torus coordinate**: the chart image of the torus coordinate `z`. -/
noncomputable def chartCoordSymm (I : ModelWithCorners ℝ E H) (x₀ : M)
    (z : Fin (dim E) → ℝ) : E :=
  chartCentre I x₀ + (Module.finBasis ℝ E).equivFun.symm z

@[simp] lemma chartCoordSymm_apply (x₀ : M) (z : Fin (dim E) → ℝ) :
    chartCoordSymm I x₀ z
      = chartCentre I x₀ + (Module.finBasis ℝ E).equivFun.symm z := rfl

/-- **The chart matrix of a metric in torus coordinates**: the Gram matrix of the coordinate frame
of the chart at `x₀`, evaluated at the point with torus coordinate `z`. -/
noncomputable def flatChartMat (g : SMet I M) (x₀ : M) :
    (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E) :=
  fun z => Work.Diff.EXT.chartMatFun g x₀ (chartCoordSymm I x₀ z)

@[simp] lemma flatChartMat_apply (g : SMet I M) (x₀ : M) (z : Fin (dim E) → ℝ)
    (i j : Fin (dim E)) :
    flatChartMat g x₀ z i j
      = Work.Diff.EXT.chartMatFun g x₀ (chartCoordSymm I x₀ z) i j := rfl

/-! ## The partial derivatives of a family of matrices -/

/-- The `c`-th partial derivative of a normed-space-valued function on the torus coordinate.  This
generalises `Work.Diff.STE.pd` (which is the case of a `ℂ`-valued function) to matrix-valued
families. -/
noncomputable def dpd {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (c : Fin (dim E)) (f : (Fin (dim E) → ℝ) → β) : (Fin (dim E) → ℝ) → β :=
  fun z => fderiv ℝ f z (Pi.single c 1)

lemma dpd_eq_pd (c : Fin (dim E)) (f : (Fin (dim E) → ℝ) → ℂ) :
    dpd (E := E) c f = pd c f := rfl

/-! ## Sizes of the canonical basis vectors -/

/-- Uniform bound on the size of the canonical basis vectors, used to control the size of
`bB.equivFun.symm z` in terms of `‖z‖`. -/
noncomputable def bBnorm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ℝ :=
  ∑ i : Fin (dim E), ‖(Module.finBasis ℝ E) i‖ + 1

lemma bBnorm_pos : 0 < bBnorm E := by
  simp only [bBnorm]
  have : 0 ≤ ∑ i : Fin (dim E), ‖(Module.finBasis ℝ E) i‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  linarith

lemma norm_equivFun_symm_le (z : Fin (dim E) → ℝ) :
    ‖(Module.finBasis ℝ E).equivFun.symm z‖ ≤ bBnorm E * ‖z‖ := by
  rw [Module.Basis.equivFun_symm_apply]
  calc ‖∑ i, z i • (Module.finBasis ℝ E) i‖
      ≤ ∑ i, ‖z i • (Module.finBasis ℝ E) i‖ := norm_sum_le _ _
    _ = ∑ i, |z i| * ‖(Module.finBasis ℝ E) i‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, ‖z‖ * ‖(Module.finBasis ℝ E) i‖ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm z i) (norm_nonneg _)
    _ = ‖z‖ * ∑ i, ‖(Module.finBasis ℝ E) i‖ := by rw [Finset.mul_sum]
    _ ≤ ‖z‖ * bBnorm E := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        simp only [bBnorm]
        linarith [show (0 : ℝ) ≤ 1 by norm_num]
    _ = bBnorm E * ‖z‖ := by ring

/-! ## The bump and the periodised chart matrix -/

/-- The `ContDiffBump` used to localise the chart data. -/
noncomputable def torBumpC (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : Fin (dim E) → ℝ) :=
  ContDiffBump.mk (r / 2) r (by linarith) (by linarith)

/-- **A smooth bump on the flat torus coordinate**: `1` on the closed ball of radius `r/2` and
supported in the open ball of radius `r`. -/
noncomputable def torBump (r : ℝ) (hr : 0 < r) : (Fin (dim E) → ℝ) → ℝ :=
  (torBumpC (E := E) r hr : (Fin (dim E) → ℝ) → ℝ)

@[simp] lemma torBump_apply (r : ℝ) (hr : 0 < r) (z : Fin (dim E) → ℝ) :
    torBump (E := E) r hr z = (torBumpC (E := E) r hr : (Fin (dim E) → ℝ) → ℝ) z := rfl

lemma torBump_contDiff (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (torBump (E := E) r hr) :=
  ContDiffBump.contDiff (torBumpC (E := E) r hr)

lemma torBump_one (r : ℝ) (hr : 0 < r) {z : Fin (dim E) → ℝ}
    (hz : z ∈ Metric.closedBall (0 : Fin (dim E) → ℝ) (r / 2)) :
    torBump (E := E) r hr z = 1 :=
  ContDiffBump.one_of_mem_closedBall (torBumpC (E := E) r hr) hz

lemma torBump_zero (r : ℝ) (hr : 0 < r) {z : Fin (dim E) → ℝ}
    (hz : r ≤ dist z (0 : Fin (dim E) → ℝ)) : torBump (E := E) r hr z = 0 :=
  ContDiffBump.zero_of_le_dist (torBumpC (E := E) r hr) hz

lemma torBump_nonneg (r : ℝ) (hr : 0 < r) (z : Fin (dim E) → ℝ) :
    0 ≤ torBump (E := E) r hr z := ContDiffBump.nonneg (torBumpC (E := E) r hr)

lemma torBump_le_one (r : ℝ) (hr : 0 < r) (z : Fin (dim E) → ℝ) :
    torBump (E := E) r hr z ≤ 1 := ContDiffBump.le_one (torBumpC (E := E) r hr)

lemma torBump_support_subset (r : ℝ) (hr : 0 < r) :
    Function.support (torBump (E := E) r hr) ⊆ Metric.ball (0 : Fin (dim E) → ℝ) r :=
  le_of_eq (ContDiffBump.support_eq (torBumpC (E := E) r hr))

/-- The localised chart matrix of `g` in torus coordinates: the chart matrix near `0`, cut off by
the bump (so that it is compactly supported inside the unit cube when `r ≤ 1/4`). -/
noncomputable def chartDatumLoc (g : SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (z : Fin (dim E) → ℝ) : Work.Diff.EXT.MatE (E := E) :=
  torBump (E := E) r hr z • (flatChartMat g x₀ z - flatChartMat g x₀ 0)

/-- The complex-valued, entrywise localised chart matrix: the `(i,j)` entry of `chartDatumLoc`,
viewed as a complex-valued function of the torus coordinate. -/
noncomputable def chartDatumLocC (g : SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (i j : Fin (dim E)) : (Fin (dim E) → ℝ) → ℂ :=
  fun z => ((chartDatumLoc g x₀ r hr z) i j : ℂ)

/-- **The periodised chart matrix** (complex-valued): the smooth `1`-periodic matrix-valued
function obtained by periodising the localised chart matrix,
`M₀ + Σ_{m ∈ ℤⁿ} w (z + m)` with `M₀ = flatChartMat g x₀ 0` and `w = chartDatumLoc`.  It agrees with
the chart matrix of `g` near `0`. -/
noncomputable def chartDatumC (g : SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r) :
    (Fin (dim E) → ℝ) → Fin (dim E) → Fin (dim E) → ℂ :=
  fun z i j =>
    (flatChartMat g x₀ 0 i j : ℂ)
      + ∑' m : Fin (dim E) → ℤ, chartDatumLocC g x₀ r hr i j (z + iVec m)

/-- The real part of the periodised chart matrix: the matrix of the local metric in the torus
coordinate. -/
noncomputable def chartDatumR (g : SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (z : Fin (dim E) → ℝ) (i j : Fin (dim E)) : ℝ :=
  (chartDatumC (I := I) g x₀ r hr z i j).re

/-- The periodised chart matrix as a **complex** matrix-valued function on the torus: the initial
datum `u₀` and the background jet data of the flat Cauchy problem. -/
noncomputable def chartDatum (g : SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r) :
    Work.Diff.STE.Flat.Torus (dim E) :=
  chartDatumC (I := I) g x₀ r hr

@[simp] lemma chartDatum_apply (g : SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (z : Fin (dim E) → ℝ) (i j : Fin (dim E)) :
    chartDatum (I := I) g x₀ r hr z i j = chartDatumC (I := I) g x₀ r hr z i j := rfl

@[simp] lemma chartDatum_re (g : SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r)
    (z : Fin (dim E) → ℝ) :
    Work.Diff.STE.Flat.reMat (chartDatum (I := I) g x₀ r hr z)
      = chartDatumR (I := I) g x₀ r hr z := rfl

/-- The complex matrix with real entries given by `A` (the canonical embedding of the real matrices
into the complex ones). -/
noncomputable def ofRealMat (A : Work.Diff.EXT.MatE (E := E)) :
    Work.Diff.STE.Flat.MatC (dim E) :=
  fun i j => (A i j : ℂ)

@[simp] lemma ofRealMat_apply (A : Work.Diff.EXT.MatE (E := E)) (i j : Fin (dim E)) :
    ofRealMat A i j = (A i j : ℂ) := rfl

@[simp] lemma reMat_ofRealMat (A : Work.Diff.EXT.MatE (E := E)) :
    Work.Diff.STE.Flat.reMat (ofRealMat A) = A := rfl

lemma ofRealMat_add (A B : Work.Diff.EXT.MatE (E := E)) :
    ofRealMat (A + B) = ofRealMat A + ofRealMat B := by
  funext i j
  simp only [ofRealMat_apply, Pi.add_apply, Complex.ofReal_add]

/-- The real part of a complex matrix, as an element of `MatE = Fin n → Fin n → ℝ` (the same
function as `Work.Diff.STE.Flat.reMat`, with the type ascription needed to avoid `Matrix`-instance
inference). -/
noncomputable def reMatE (A : Work.Diff.STE.Flat.MatC (dim E)) : Work.Diff.EXT.MatE (E := E) :=
  fun i j => (A i j).re

@[simp] lemma reMatE_apply (A : Work.Diff.STE.Flat.MatC (dim E)) (i j : Fin (dim E)) :
    reMatE A i j = (A i j).re := rfl

lemma reMatE_eq_reMat (A : Work.Diff.STE.Flat.MatC (dim E)) :
    reMatE A = Work.Diff.STE.Flat.reMat A := rfl

@[simp] lemma reMatE_conjMat (A : Work.Diff.STE.Flat.MatC (dim E)) :
    reMatE (Work.Diff.STE.Flat.conjMat A) = reMatE A := by
  funext i j
  simp only [reMatE_apply, Work.Diff.STE.Flat.conjMat_apply, Complex.star_def, Complex.conj_re]

/-! ## Converting coordinate-indexed jets into `LinMat`/`BilMat` -/

/-- The continuous linear map `E →L[ℝ] F` whose values on the canonical basis are `L c`. -/
noncomputable def linMatOf {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Fin (dim E) → F) : E →L[ℝ] F :=
  ((Module.finBasis ℝ E).constr ℝ L).toContinuousLinearMap

lemma linMatOf_bB {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Fin (dim E) → F) (c : Fin (dim E)) :
    linMatOf (E := E) L (Module.finBasis ℝ E c) = L c := by
  simp only [linMatOf, LinearMap.coe_toContinuousLinearMap', Module.Basis.constr_basis]

/-- The continuous bilinear map `E →L[ℝ] E →L[ℝ] F` whose values on pairs of canonical basis
vectors are `B c d`. -/
noncomputable def bilMatOf {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : Fin (dim E) → Fin (dim E) → F) : E →L[ℝ] E →L[ℝ] F :=
  ((Module.finBasis ℝ E).constr ℝ (fun c => linMatOf (E := E) (B c))).toContinuousLinearMap

lemma bilMatOf_bB {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : Fin (dim E) → Fin (dim E) → F) (c d : Fin (dim E)) :
    bilMatOf (E := E) B (Module.finBasis ℝ E c) (Module.finBasis ℝ E d) = B c d := by
  simp only [bilMatOf, LinearMap.coe_toContinuousLinearMap', Module.Basis.constr_basis,
    linMatOf_bB]

/-! ## The chart nonlinearity

The nonlinearity fed to the flat Cauchy problem must satisfy `Work.Diff.STE.Flat.IsDeTurckNonlin`,
i.e. it must be of the shape `secOpFlat A B + N (x, (A, L))` for **all** jets `(A, L, B)` with
`det (reMat A) ≠ 0`, and it must agree with the true chart DeTurck operator on the jets that actually
occur (jets of a smooth symmetric metric: `A` and `L` symmetric in the matrix indices, `B` symmetric
both in the derivative slots and in the matrix indices).

The coordinate operator `pPhi` does **not** have this shape as a function of all jets: the difference
`pPhi A L B - secOp A B` is independent of `B` only when `A` is symmetric and `B` is symmetric in
both pairs of its slots (verified numerically in `Scratch_room/deTurck_jet_sym.py`; the
DeTurck cancellation is an identity about *metric* jets).  We therefore define the flat
nonlinearity with the principal part made explicit,

  `chartNonlin bg (x, (A, L, B)) = secOpFlat A B + ↑(pN (bg x) (∂bg x) (∂²bg x) A L)`,

which by construction is of DeTurck shape (with `N (x,(A,L)) = ↑(pN (bg x) (∂bg x) (∂²bg x) A L)`), and
which agrees with `↑(pPhi (...))` on the symmetric jets by `Work.Diff.STE.DeTurck.pPhi_decomp`.
Note that `pN` does not involve `B` at all. -/

/-- **The chart nonlinearity `Φ`** fed to the flat Cauchy problem: the scalar principal part
`secOpFlat A B` plus the lower-order part `pN` evaluated at the background jets `(bg, ∂bg, ∂²bg)` of
the (periodised) background chart matrix `bg` and at the (real parts of the) value and first jet of
the unknown. -/
noncomputable def chartNonlin (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E)) :
    (Fin (dim E) → ℝ) × Work.Diff.STE.Flat.Jet (dim E) →
      Work.Diff.STE.Flat.MatC (dim E) :=
  fun p i j =>
    (Work.Diff.STE.Flat.secOpFlat p.2.1 p.2.2.2 i j
      + ((Work.Diff.STE.DeTurck.pN
          (bg p.1)
          (linMatOf (E := E) (fun c => dpd (E := E) c bg p.1))
          (bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) p.1))
          (reMatE p.2.1)
          (linMatOf (E := E) (fun c => reMatE (p.2.2.1 c)))) i j : ℂ))

/-- The lower-order part of the chart nonlinearity: `N (x, (A,L)) = ↑(pN (bg x) (∂bg x) (∂²bg x) A L)`.
By construction `chartNonlin bg (x, (A,L,B)) = secOpFlat A B + chartNonlinN bg (x, (A,L))`. -/
noncomputable def chartNonlinN (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E)) :
    (Fin (dim E) → ℝ) ×
        (Work.Diff.STE.Flat.MatC (dim E) × (Fin (dim E) → Work.Diff.STE.Flat.MatC (dim E))) →
      Work.Diff.STE.Flat.MatC (dim E) :=
  fun p i j =>
    (Work.Diff.STE.DeTurck.pN
      (bg p.1)
      (linMatOf (E := E) (fun c => dpd (E := E) c bg p.1))
      (bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) p.1))
      (reMatE p.2.1)
      (linMatOf (E := E) (fun c => reMatE (p.2.2 c))) i j : ℂ)

@[simp] lemma chartNonlin_apply (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (p : (Fin (dim E) → ℝ) × Work.Diff.STE.Flat.Jet (dim E)) (i j : Fin (dim E)) :
    chartNonlin (E := E) bg p i j =
      (Work.Diff.STE.Flat.secOpFlat p.2.1 p.2.2.2 i j
        + ((Work.Diff.STE.DeTurck.pN
            (bg p.1)
            (linMatOf (E := E) (fun c => dpd (E := E) c bg p.1))
            (bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) p.1))
            (reMatE p.2.1)
            (linMatOf (E := E) (fun c => reMatE (p.2.2.1 c)))) i j : ℂ)) := rfl

@[simp] lemma chartNonlinN_apply (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (p : (Fin (dim E) → ℝ) ×
        (Work.Diff.STE.Flat.MatC (dim E) × (Fin (dim E) → Work.Diff.STE.Flat.MatC (dim E))))
    (i j : Fin (dim E)) :
    chartNonlinN (E := E) bg p i j =
      (Work.Diff.STE.DeTurck.pN
        (bg p.1)
        (linMatOf (E := E) (fun c => dpd (E := E) c bg p.1))
        (bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) p.1))
        (reMatE p.2.1)
        (linMatOf (E := E) (fun c => reMatE (p.2.2 c))) i j : ℂ) := rfl

/-- The defining decomposition of the chart nonlinearity. -/
lemma chartNonlin_eq_secOpFlat_add (bg : (Fin (dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (x : Fin (dim E) → ℝ)
    (A : Work.Diff.STE.Flat.MatC (dim E))
    (L : Fin (dim E) → Work.Diff.STE.Flat.MatC (dim E))
    (B : Fin (dim E) → Fin (dim E) → Work.Diff.STE.Flat.MatC (dim E)) :
    chartNonlin (E := E) bg (x, (A, L, B))
      = Work.Diff.STE.Flat.secOpFlat A B + chartNonlinN (E := E) bg (x, (A, L)) := rfl

end

end Work.Diff.STE.Man
