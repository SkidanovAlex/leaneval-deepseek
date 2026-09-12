import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Submission.Commons.Analysis.InnerProductSpace.isometry_inner_map
import Submission.Commons.Analysis.Calculus.ContDiff.crossProduct
import Submission.Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually
import Submission.Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
import Submission.Commons.Analysis.Calculus.FDeriv.secondDeriv_orth_tangent
import Submission.Commons.Analysis.InnerProductSpace.orthonormal_frame_decomp
import Submission.Commons.Analysis.InnerProductSpace.span_of_orth_normal
import Submission.Commons.Analysis.InnerProductSpace.orthonormal_triple_expansion
import Submission.Commons.LinearAlgebra.ker_line_of_finrank_two
import Submission.PaperBand.EmbeddingFacts
open OptimalMoebius
open Topology ContDiff
open scoped BigOperators
open scoped Matrix
open InnerProductGeometry

set_option autoImplicit false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The bend-foliation layer, part 1: the tangent frame of the immersion

(Roadmap item 1, first object.)  For a smooth isometric immersion
`f : unitStrip → ℝ³` (an `IsMoebiusEmbedding`), the derivative at each point
is a linear isometry `ℝ² →ₗ ℝ³`.  Its columns give an *orthonormal tangent
frame* `(e₀, e₁)` of the image surface.  The next object of the theory
(upcoming) is the unit normal `N = e₀ × e₁` and the shape operator
`dN`; the *bend* through a point is the straight segment tangent to
`ker dN`, the direction in which the normal does not turn.  Because
`N` is constant along a bend, the image is straight there — that is how the
paper's §2.1 produces the bend foliation.

This file establishes the first object of that layer: the frame
`(e₀, e₁, N)` — verified *orthonormal* at every point of the strip, with
`N = e₀ × e₁` the unit normal.  It uses
`Commons.Analysis.InnerProductSpace.inner_map_map_of_isometry`
(polarization) to pass from the derivative's norm preservation
(`EmbeddingFacts.fderiv_norm_eq`) to inner-product preservation, and
`InnerProductGeometry.norm_ofLp_crossProduct` for `‖N‖ = 1`.

Status: the frame `(e₀, e₁, N)` is orthonormal at every point of the
strip, and `x ↦ tangent₀ f x` and `x ↦ tangent₁ f x` are `C∞` on the
interior `stripInterior` of the strip (via `contDiffOn_fderivWithin_unitStrip`,
which identifies the within-derivative with the genuine derivative there).

Status: the frame `(e₀, e₁, N)` is orthonormal at every point of the
strip, and all three frame components — `tangent₀`, `tangent₁`,
`unitNormal` — are `C∞` on the interior `stripInterior`
(`contDiffOn_tangent₀/₁` via `contDiffOn_fderivWithin_unitStrip`,
`contDiffOn_unitNormal` via the Commons cross-product result
`Commons.Analysis.Calculus.ContDiff.crossProduct`, proved by a fleet agent).
The shape operator `x ↦ dN f x` is defined, agrees with the ordinary
derivative of the normal on `stripInterior` (`dN_eq_fderiv`), is `C∞` there
(`contDiffOn_dN`), and `bendDir f x = LinearMap.ker (dN f x).toLinearMap`
is the kernel (bend-direction) subspace.

Status of step (1) (flatness of the shape operator):
  * `dN_tangent_valued` (⟪dN v, N⟫ = 0), the Weingarten relations
    `dN_tangent₁_relation`/`dN_tangent₀_relation` (⟪dN eᵢ, e_j⟫ =
    −⟪N, ∂ᵢ e_j⟫), the symmetry `shapeOperator_symm`, and the third-mixed-
    partial commutation `thirdMixedPartials_commute₀₁₀` are PROVED here;
  * pure-normality of the second derivatives (`f_ij ⊥ e_k` in orthonormal
    coordinates) is provided by the fleet-proved commons lemma
    `Commons.Analysis.Calculus.FDeriv.secondDeriv_orth_tangent`
    (instantiation on `f` pending);
  * target `shapeOperator_det_zero` (det of `dNentry` is 0) is recorded with
    its p,q,r / pr−q² decomposition in
    `Submission/Work/shapeOperator_det_zero_skeleton.lean`.

Status of step (1) (flatness of the shape operator):
  * `dN_tangent_valued`, the Weingarten relations, `shapeOperator_symm`,
    `thirdMixedPartials_commute₀₁₀`, and the instantiation
    `secondDeriv_normal_interior` (pure-normality of the second derivatives
    of `f`, via the fleet-proved
    `Commons.Analysis.Calculus.FDeriv.secondDeriv_orth_tangent`) are PROVED
    here;
  * target `shapeOperator_det_zero` (det of `dNentry` is 0) remains open;
    the remaining steps are: convert the normality statements to the tangent
    functions, prove the orthonormal-frame decomposition (a vector
    orthogonal to both tangents is a multiple of `N`), apply the
    derivative-of-zero-inner-product identity to `⟪∂₁t₀, tᵢ⟫ ≡ 0` and
    `⟪∂₀t₀, t₁⟫ ≡ 0` to identify `⟪D, t₁⟫` in two ways (D the common
    third-partial derivative), and run the `pr = q²` algebra.

Status of this layer (bend directions):
  * `shapeOperator_det_zero` (flatness) is PROVED;
  * `bendDir_is_line` is PROVED: on the interior, wherever `dN f x ≠ 0` the
    kernel `bendDir f x = ker (dN f x)` is spanned by one nonzero vector —
    the unique *bend direction* of paper §2.1 Lemma `mc` (via the commons
    `Commons.LinearAlgebra.ker_line_of_finrank_two` and the kernel-vector
    step `shape_ker_of_mulVec` + the frame expansion).

Next obligations of this layer (not yet formalized here):
  * along a curve tangent to `ker dN` the normal is constant, so the image is
    a straight segment (the local "bend");
  * the global bend foliation of the band (Proposition `main0` of §2.1).
-/

noncomputable section
namespace Submission.PaperBand

/-- The two coordinate tangent vectors of `f` (the columns of `df`). -/
def tangent₀ (f : ℝ² → ℝ³) (x : ℝ²) : ℝ³ :=
  fderivWithin ℝ f unitStrip x !₂[1, 0]

/-- The two coordinate tangent vectors of `f` (the columns of `df`). -/
def tangent₁ (f : ℝ² → ℝ³) (x : ℝ²) : ℝ³ :=
  fderivWithin ℝ f unitStrip x !₂[0, 1]

lemma norm_basis₀ : ‖(!₂[1, 0] : ℝ²)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

lemma norm_basis₁ : ‖(!₂[0, 1] : ℝ²)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

lemma inner_basis₀₁ : inner ℝ (!₂[1, 0] : ℝ²) !₂[0, 1] = 0 := by
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_two]

/-- The tangent vector `e₀ = df(1,0)` is a unit vector on the strip. -/
lemma tangent₀_norm {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, ‖tangent₀ f x‖ = 1 := by
  intro x hx
  have h := fderiv_norm_eq hf x hx !₂[1, 0]
  simpa [tangent₀] using h.trans (by rw [norm_basis₀])

/-- The tangent vector `e₁ = df(0,1)` is a unit vector on the strip. -/
lemma tangent₁_norm {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, ‖tangent₁ f x‖ = 1 := by
  intro x hx
  have h := fderiv_norm_eq hf x hx !₂[0, 1]
  simpa [tangent₁] using h.trans (by rw [norm_basis₁])

/-- The tangent vectors `e₀` and `e₁` are orthogonal on the strip: the frame
`(e₀, e₁)` is orthonormal, since `df` preserves inner products. -/
lemma tangent₀₁_orthogonal {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, inner ℝ (tangent₀ f x) (tangent₁ f x) = 0 := by
  intro x hx
  let L : ℝ² →ₗ[ℝ] ℝ³ := (fderivWithin ℝ f unitStrip x).toLinearMap
  have hL : ∀ v : ℝ², ‖L v‖ = ‖v‖ := by
    intro v
    exact fderiv_norm_eq hf x hx v
  have hint : inner ℝ (L !₂[1, 0]) (L !₂[0, 1]) = inner ℝ (!₂[1, 0] : ℝ²) !₂[0, 1] :=
    Commons.Analysis.InnerProductSpace.inner_map_map_of_isometry L hL !₂[1, 0] !₂[0, 1]
  rw [inner_basis₀₁] at hint
  simpa [tangent₀, tangent₁, L] using hint

/-- Combined: the tangent frame is orthonormal at every point of the strip. -/
lemma tangent_frame_orthonormal {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip,
      ‖tangent₀ f x‖ = 1 ∧ ‖tangent₁ f x‖ = 1 ∧ inner ℝ (tangent₀ f x) (tangent₁ f x) = 0 := by
  intro x hx
  exact ⟨tangent₀_norm hf x hx, tangent₁_norm hf x hx, tangent₀₁_orthogonal hf x hx⟩

/-- The unit normal of the immersion:
`N = e₀ × e₁` (in the convention of the paper's §2.1, where
`{ker dη, im dη, η}` is an orthonormal frame along a bend). -/
def unitNormal (f : ℝ² → ℝ³) (x : ℝ²) : ℝ³ :=
  WithLp.toLp 2 (WithLp.ofLp (tangent₀ f x) ⨯₃ WithLp.ofLp (tangent₁ f x))

/-- The normal `N = e₀ × e₁` is a unit vector on the strip (the frame
`(e₀, e₁, N)` is orthonormal). -/
lemma unitNormal_norm {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, ‖unitNormal f x‖ = 1 := by
  intro x hx
  unfold unitNormal
  rw [InnerProductGeometry.norm_ofLp_crossProduct]
  have h0 : ‖tangent₀ f x‖ = 1 := tangent₀_norm hf x hx
  have h1 : ‖tangent₁ f x‖ = 1 := tangent₁_norm hf x hx
  have h01 : inner ℝ (tangent₀ f x) (tangent₁ f x) = 0 := tangent₀₁_orthogonal hf x hx
  have hang : angle (tangent₀ f x) (tangent₁ f x) = Real.pi / 2 :=
    (inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp h01
  have hsin : Real.sin (angle (tangent₀ f x) (tangent₁ f x)) = 1 := by
    exact (sin_eq_one_iff_angle_eq_pi_div_two).mpr hang
  rw [h0, h1, hsin]
  norm_num

/-- The normal `N` is orthogonal to `e₀` on the strip. -/
lemma tangent₀_normal_orthogonal {a : ℝ} {f : ℝ² → ℝ³} (_hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, inner ℝ (tangent₀ f x) (unitNormal f x) = 0 := by
  intro x hx
  unfold unitNormal
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp
  rw [dotProduct_comm]
  exact dot_self_cross (WithLp.ofLp (tangent₀ f x)) (WithLp.ofLp (tangent₁ f x))

/-- The normal `N` is orthogonal to `e₁` on the strip. -/
lemma tangent₁_normal_orthogonal {a : ℝ} {f : ℝ² → ℝ³} (_hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, inner ℝ (tangent₁ f x) (unitNormal f x) = 0 := by
  intro x hx
  unfold unitNormal
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp
  rw [dotProduct_comm]
  exact dot_cross_self (WithLp.ofLp (tangent₀ f x)) (WithLp.ofLp (tangent₁ f x))

/-- The frame `(e₀, e₁, N)` is orthonormal at every point of the strip. -/
lemma orthonormal_frame {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip,
      ‖tangent₀ f x‖ = 1 ∧ ‖tangent₁ f x‖ = 1 ∧ ‖unitNormal f x‖ = 1 ∧
      inner ℝ (tangent₀ f x) (tangent₁ f x) = 0 ∧
      inner ℝ (tangent₀ f x) (unitNormal f x) = 0 ∧
      inner ℝ (tangent₁ f x) (unitNormal f x) = 0 := by
  intro x hx
  exact ⟨tangent₀_norm hf x hx, tangent₁_norm hf x hx, unitNormal_norm hf x hx,
    tangent₀₁_orthogonal hf x hx, tangent₀_normal_orthogonal hf x hx,
    tangent₁_normal_orthogonal hf x hx⟩

/-- The interior of the unit strip: `0 < x 0 < 1`. -/
def stripInterior : Set ℝ² := {x | x 0 ∈ Set.Ioo (0 : ℝ) 1}

lemma stripInterior_isOpen : IsOpen stripInterior := by
  change IsOpen ((fun x : ℝ² => x 0) ⁻¹' (Set.Ioo (0 : ℝ) 1))
  exact isOpen_Ioo.preimage (by fun_prop)

lemma stripInterior_subset_unitStrip : stripInterior ⊆ unitStrip := by
  intro x hx
  have hx0 : x 0 ∈ Set.Ioo (0 : ℝ) 1 := by simpa [stripInterior] using hx
  simpa [unitStrip] using (Set.Ioo_subset_Icc_self hx0)

lemma unitStrip_mem_nhds_of_mem_stripInterior {x : ℝ²} (hx : x ∈ stripInterior) :
    unitStrip ∈ 𝓝 x :=
  Filter.mem_of_superset (IsOpen.mem_nhds stripInterior_isOpen hx) stripInterior_subset_unitStrip

/-- The within-derivative `x ↦ fderivWithin f unitStrip x` is `C∞` on the
interior of the strip: there it agrees with the genuine derivative of `f`,
which is `C∞` because `f` is `C∞` on the open strip. -/
lemma contDiffOn_fderivWithin_unitStrip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun x : ℝ² => fderivWithin ℝ f unitStrip x) stripInterior := by
  have hcont : ContDiffOn ℝ ∞ f stripInterior := hf.smooth.mono stripInterior_subset_unitStrip
  have hdf : ContDiffOn ℝ ∞ (fun x => fderivWithin ℝ f stripInterior x) stripInterior :=
    hcont.fderivWithin stripInterior_isOpen.uniqueDiffOn (by simp)
  refine hdf.congr ?_
  intro x hx
  have h1 : fderivWithin ℝ f unitStrip x = fderiv ℝ f x :=
    fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_mem_stripInterior hx)
  have h2 : fderivWithin ℝ f stripInterior x = fderiv ℝ f x :=
    fderivWithin_of_isOpen stripInterior_isOpen hx
  rw [h1, h2]

/-- `x ↦ tangent₀ f x` is `C∞` on the interior of the strip. -/
lemma contDiffOn_tangent₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun x : ℝ² => tangent₀ f x) stripInterior := by
  have hd := contDiffOn_fderivWithin_unitStrip hf
  have hc : ContDiffOn ℝ ∞ (fun _ : ℝ² => (!₂[1, 0] : ℝ²)) stripInterior := contDiffOn_const
  have happ : ContDiffOn ℝ ∞ (fun x : ℝ² => (fderivWithin ℝ f unitStrip x) !₂[1, 0])
      stripInterior := ContDiffOn.clm_apply hd hc
  simpa [tangent₀] using happ

/-- `x ↦ tangent₁ f x` is `C∞` on the interior of the strip. -/
lemma contDiffOn_tangent₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun x : ℝ² => tangent₁ f x) stripInterior := by
  have hd := contDiffOn_fderivWithin_unitStrip hf
  have hc : ContDiffOn ℝ ∞ (fun _ : ℝ² => (!₂[0, 1] : ℝ²)) stripInterior := contDiffOn_const
  have happ : ContDiffOn ℝ ∞ (fun x : ℝ² => (fderivWithin ℝ f unitStrip x) !₂[0, 1])
      stripInterior := ContDiffOn.clm_apply hd hc
  simpa [tangent₁] using happ

/-- The **shape operator**: derivative of the unit normal along the band.  At
`x` this is the within-derivative (over the unit strip) of `x ↦ unitNormal f x`,
a linear map `ℝ² →ₗ ℝ³`.  On the interior of the strip — once
`unitNormal` is known to be `C∞` there (via the delegated Commons lemma
`Commons.Analysis.Calculus.ContDiff.crossProduct`) — it agrees with the
ordinary derivative, and its kernel is the *bend direction*: the ruling
direction along which the normal is constant and the image is straight
(paper §2.1). -/
def dN (f : ℝ² → ℝ³) (x : ℝ²) : ℝ² →L[ℝ] ℝ³ :=
  fderivWithin ℝ (fun y : ℝ² => unitNormal f y) unitStrip x

/-- On the interior of the strip the shape operator is the ordinary derivative
of the unit normal (no differentiability hypothesis needed: both sides are
the total derivatives, which coincide because the strip is a neighborhood of
every interior point). -/
lemma dN_eq_fderiv {f : ℝ² → ℝ³} {x : ℝ²} (hx : x ∈ stripInterior) :
    dN f x = fderiv ℝ (fun y : ℝ² => unitNormal f y) x := by
  unfold dN
  exact fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_mem_stripInterior hx)

/-- The **bend direction** at `x`: the kernel of the shape operator — the
set of tangent directions `v` along which the normal does not change
(`dN · v = 0`).  The pre-bends of the band foliation (once constructed) are
straight segments parallel to these directions. -/
def bendDir (f : ℝ² → ℝ³) (x : ℝ²) : Submodule ℝ ℝ² :=
  LinearMap.ker (dN f x).toLinearMap

/-- A direction in the kernel of the shape operator is one along which the
unit normal is stationary: `v ∈ bendDir f x` iff `dN f x v = 0`. -/
lemma mem_bendDir_iff {f : ℝ² → ℝ³} {x : ℝ²} {v : ℝ²} :
    v ∈ bendDir f x ↔ dN f x v = 0 := by
  rfl

/-- `x ↦ unitNormal f x` is `C∞` on the interior of the strip: the cross
product of the two smooth tangent frame components. -/
lemma contDiffOn_unitNormal {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun x : ℝ² => unitNormal f x) stripInterior := by
  unfold unitNormal
  exact Commons.Analysis.Calculus.ContDiff.crossProduct (contDiffOn_tangent₀ hf)
    (contDiffOn_tangent₁ hf)

/-- The shape operator `x ↦ dN f x` is `C∞` on the interior of the strip. -/
lemma contDiffOn_dN {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun x : ℝ² => dN f x) stripInterior := by
  have hN := contDiffOn_unitNormal hf
  have hdf : ContDiffOn ℝ ∞
      (fun x : ℝ² => fderivWithin ℝ (fun y : ℝ² => unitNormal f y) stripInterior x)
      stripInterior :=
    hN.fderivWithin stripInterior_isOpen.uniqueDiffOn (by simp)
  refine hdf.congr ?_
  intro x hx
  have h1 : fderivWithin ℝ (fun y : ℝ² => unitNormal f y) stripInterior x =
      fderiv ℝ (fun y : ℝ² => unitNormal f y) x :=
    fderivWithin_of_isOpen stripInterior_isOpen hx
  have h2 : dN f x = fderiv ℝ (fun y : ℝ² => unitNormal f y) x := dN_eq_fderiv hx
  rw [h1, h2]

/-- The coordinate entries of the shape operator over the frame
`(e₀ = df(1,0), e₁ = df(0,1))` and the tangent frame `(tangent₀, tangent₁)`:
`dNentry f x i j = ⟪dN f x (eᵢ), tangent_j f x⟫` where `eᵢ` is the `i`-th
coordinate basis vector of the domain.  In orthonormal coordinates the
2×2 matrix with these entries represents the shape operator; its
determinant is the Gaussian curvature factor whose vanishing expresses
flatness. -/
def dNentry (f : ℝ² → ℝ³) (x : ℝ²) : Fin 2 → Fin 2 → ℝ := fun i j =>
  inner ℝ (dN f x (if i = 0 then !₂[1, 0] else !₂[0, 1]))
    (if j = 0 then tangent₀ f x else tangent₁ f x)

/-- **Weingarten-type identity**: the shape operator is tangent-valued — the
derivative of the unit normal is orthogonal to the normal itself,
`⟪dN f x v, N x⟫ = 0`, on the interior of the strip.  (Proof: differentiate
`⟪N, N⟫ = ‖N‖² = 1`.)  This is the first identity needed for the symmetry and
flatness of the shape operator. -/
lemma dN_tangent_valued {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ v : ℝ², inner ℝ (dN f x v) (unitNormal f x) = 0 := by
  intro x hx v
  let N : ℝ² → ℝ³ := fun y => unitNormal f y
  have hdifOn : DifferentiableOn ℝ N stripInterior :=
    (contDiffOn_unitNormal hf).differentiableOn (by simp)
  have hdif : DifferentiableAt ℝ N x :=
    (hdifOn x hx).differentiableAt (IsOpen.mem_nhds stripInterior_isOpen hx)
  have hinnerUnit : ∀ y ∈ unitStrip, inner ℝ (N y) (N y) = 1 := by
    intro y hy
    have hn : ‖unitNormal f y‖ = 1 := unitNormal_norm hf y hy
    rw [inner_self_eq_norm_sq_to_K]
    simp [N, hn]
  have hEqOn : ∀ y ∈ stripInterior, inner ℝ (N y) (N y) = 1 := by
    intro y hy
    exact hinnerUnit y (stripInterior_subset_unitStrip hy)
  have hEq : (fun y : ℝ² => inner ℝ (N y) (N y)) =ᶠ[𝓝 x] (fun _ : ℝ² => (1 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact hEqOn y hy
  have hc : HasFDerivAt (fun _ : ℝ² => (1 : ℝ)) (0 : ℝ² →L[ℝ] ℝ) x :=
    hasFDerivAt_const (1 : ℝ) x
  have hgder : HasFDerivAt (fun y : ℝ² => inner ℝ (N y) (N y)) (0 : ℝ² →L[ℝ] ℝ) x :=
    hc.congr_of_eventuallyEq hEq
  have hfderivg : fderiv ℝ (fun y : ℝ² => inner ℝ (N y) (N y)) x = 0 := hgder.fderiv
  have hfv := fderiv_inner_apply (𝕜 := ℝ) hdif hdif v
  have hzero : inner ℝ (N x) (fderiv ℝ N x v) + inner ℝ (fderiv ℝ N x v) (N x) = 0 := by
    rw [← hfv]
    rw [hfderivg]
    simp
  have hdN : fderiv ℝ N x = dN f x := by
    simpa [N] using (dN_eq_fderiv (f := f) hx).symm
  have hNv : inner ℝ (N x) (dN f x v) + inner ℝ (dN f x v) (N x) = 0 := by
    simpa [hdN] using hzero
  have hsym := real_inner_comm (x := N x) (y := dN f x v)
  rw [hsym] at hNv
  linarith

/-- On the interior of the strip the tangent vector `tangent₀ f x` is the
genuine derivative of `f` applied to the first basis vector. -/
lemma tangent₀_eq_fderiv {f : ℝ² → ℝ³} {x : ℝ²} (hx : x ∈ stripInterior) :
    tangent₀ f x = fderiv ℝ f x !₂[1, 0] := by
  unfold tangent₀
  rw [fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_mem_stripInterior hx)]

/-- On the interior of the strip the tangent vector `tangent₁ f x` is the
genuine derivative of `f` applied to the second basis vector. -/
lemma tangent₁_eq_fderiv {f : ℝ² → ℝ³} {x : ℝ²} (hx : x ∈ stripInterior) :
    tangent₁ f x = fderiv ℝ f x !₂[0, 1] := by
  unfold tangent₁
  rw [fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_mem_stripInterior hx)]

/-- The tangent frame component functions are differentiable at interior
points of the strip. -/
lemma differentiableAt_tangent₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (fun y : ℝ² => tangent₀ f y) x := by
  intro x hx
  exact ((contDiffOn_tangent₀ hf).differentiableOn (by simp) x hx).differentiableAt
    (IsOpen.mem_nhds stripInterior_isOpen hx)

/-- The tangent frame component functions are differentiable at interior
points of the strip. -/
lemma differentiableAt_tangent₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (fun y : ℝ² => tangent₁ f y) x := by
  intro x hx
  exact ((contDiffOn_tangent₁ hf).differentiableOn (by simp) x hx).differentiableAt
    (IsOpen.mem_nhds stripInterior_isOpen hx)

/-- The unit normal is orthogonal to `tangent₀` (in the order needed by the
product-rule identity), at every point. -/
lemma unitNormal_orth_tangent₀ (f : ℝ² → ℝ³) :
    ∀ y : ℝ², inner ℝ (unitNormal f y) (tangent₀ f y) = 0 := by
  intro y
  unfold unitNormal
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- The unit normal is orthogonal to `tangent₁` (in the order needed by the
product-rule identity), at every point. -/
lemma unitNormal_orth_tangent₁ (f : ℝ² → ℝ³) :
    ∀ y : ℝ², inner ℝ (unitNormal f y) (tangent₁ f y) = 0 := by
  intro y
  unfold unitNormal
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- **Weingarten relation for `e₁`**: on the interior of the strip,
`⟪dN f x e₀, tangent₁ f x⟫ = −⟪N x, ∂₀ tangent₁ x⟫` where `∂₀ tangent₁ x` is
the derivative of `y ↦ tangent₁ f y` at `x` in the direction `e₀ = (1,0)`
(i.e. `f_uv`).  Derived by differentiating the identity `⟪N, tangent₁⟫ = 0`. -/
lemma dN_tangent₁_relation {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      inner ℝ (dN f x !₂[1, 0]) (tangent₁ f x) =
        - inner ℝ (unitNormal f x)
            (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]) := by
  intro x hx
  let N : ℝ² → ℝ³ := fun y => unitNormal f y
  have hdifN : DifferentiableAt ℝ N x := by
    exact (((contDiffOn_unitNormal hf).differentiableOn (by simp) x hx).differentiableAt
      (IsOpen.mem_nhds stripInterior_isOpen hx))
  have hzero : (fun y : ℝ² => inner ℝ (N y) (tangent₁ f y)) =ᶠ[𝓝 x]
      (fun _ : ℝ² => (0 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact unitNormal_orth_tangent₁ f y
  have hmain := Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually
    (E := ℝ³) (G := ℝ²) (f := N) (g := fun y : ℝ² => tangent₁ f y) (x := x)
    hdifN (differentiableAt_tangent₁ hf x hx) hzero !₂[1, 0]
  have hdN : fderiv ℝ N x = dN f x := by
    simpa [N] using (dN_eq_fderiv (f := f) hx).symm
  have hmain' : inner ℝ (dN f x !₂[1, 0]) (tangent₁ f x) +
      inner ℝ (unitNormal f x) (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]) = 0 := by
    simpa [hdN, N] using hmain
  linarith

/-- **Weingarten relation for `e₀`**: on the interior of the strip,
`⟪dN f x e₁, tangent₀ f x⟫ = −⟪N x, ∂₁ tangent₀ x⟫` where `∂₁ tangent₀ x` is
the derivative of `y ↦ tangent₀ f y` at `x` in the direction `e₁ = (0,1)`
(i.e. `f_vu`).  Derived by differentiating the identity `⟪N, tangent₀⟫ = 0`. -/
lemma dN_tangent₀_relation {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      inner ℝ (dN f x !₂[0, 1]) (tangent₀ f x) =
        - inner ℝ (unitNormal f x)
            (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) := by
  intro x hx
  let N : ℝ² → ℝ³ := fun y => unitNormal f y
  have hdifN : DifferentiableAt ℝ N x := by
    exact (((contDiffOn_unitNormal hf).differentiableOn (by simp) x hx).differentiableAt
      (IsOpen.mem_nhds stripInterior_isOpen hx))
  have hzero : (fun y : ℝ² => inner ℝ (N y) (tangent₀ f y)) =ᶠ[𝓝 x]
      (fun _ : ℝ² => (0 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact unitNormal_orth_tangent₀ f y
  have hmain := Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually
    (E := ℝ³) (G := ℝ²) (f := N) (g := fun y : ℝ² => tangent₀ f y) (x := x)
    hdifN (differentiableAt_tangent₀ hf x hx) hzero !₂[0, 1]
  have hdN : fderiv ℝ N x = dN f x := by
    simpa [N] using (dN_eq_fderiv (f := f) hx).symm
  have hmain' : inner ℝ (dN f x !₂[0, 1]) (tangent₀ f x) +
      inner ℝ (unitNormal f x) (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) = 0 := by
    simpa [hdN, N] using hmain
  linarith

/-- Symmetry of the shape-operator matrix on the interior of the strip: the
off-diagonal entries are equal because the mixed partials of the smooth map
`f` commute.  (Holds for any smooth unit normal field of a `C³` immersion;
no isometry is needed.) -/
lemma dNentry_symm_core {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, dNentry f x 0 1 = dNentry f x 1 0 := by
  intro x hx
  unfold dNentry
  simp
  have h01 := dN_tangent₁_relation hf x hx
  have h10 := dN_tangent₀_relation hf x hx
  have he1 : (fun y : ℝ² => tangent₁ f y) =ᶠ[𝓝 x] (fun y => fderiv ℝ f y !₂[0, 1]) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact tangent₁_eq_fderiv hy
  have he0 : (fun y : ℝ² => tangent₀ f y) =ᶠ[𝓝 x] (fun y => fderiv ℝ f y !₂[1, 0]) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact tangent₀_eq_fderiv hy
  have h2 : ContDiffOn ℝ 2 f stripInterior :=
    (hf.smooth.mono stripInterior_subset_unitStrip).of_le (by decide)
  have hconv := Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
    (E := ℝ²) (F := ℝ³) (s := stripInterior) (f := f) (x := x)
    stripInterior_isOpen hx h2 !₂[0, 1] !₂[1, 0]
  have hmix : fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0] =
      fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1] := by
    calc
      fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]
          = fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[0, 1]) x !₂[1, 0] := by
            rw [Filter.EventuallyEq.fderiv_eq he1]
      _ = fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[1, 0]) x !₂[0, 1] := hconv
      _ = fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1] := by
            rw [Filter.EventuallyEq.fderiv_eq he0]
  have hcd : inner ℝ (unitNormal f x)
        (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]) =
      inner ℝ (unitNormal f x)
        (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) := by
    rw [hmix]
  linarith

/-- The shape-operator coordinate matrix is symmetric on the interior of the
strip. -/
lemma shapeOperator_symm {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ i j : Fin 2, dNentry f x i j = dNentry f x j i := by
  intro x hx i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact dNentry_symm_core hf x hx
  · exact (dNentry_symm_core hf x hx).symm
  · rfl

/-- The derivative family `y ↦ fderiv f y e₀` is `C∞` on the interior of the
strip (it agrees there with the smooth `tangent₀`). -/
lemma contDiffOn_fderiv_dir₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun z : ℝ² => fderiv ℝ f z !₂[1, 0]) stripInterior := by
  refine (contDiffOn_tangent₀ hf).congr ?_
  intro z hz
  exact (tangent₀_eq_fderiv hz).symm

/-- The derivative family `y ↦ fderiv f y e₁` is `C∞` on the interior of the
strip (it agrees there with the smooth `tangent₁`). -/
lemma contDiffOn_fderiv_dir₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun z : ℝ² => fderiv ℝ f z !₂[0, 1]) stripInterior := by
  refine (contDiffOn_tangent₁ hf).congr ?_
  intro z hz
  exact (tangent₁_eq_fderiv hz).symm

/-- Third mixed partials of `f` commute on the interior: differentiating the
first-derivative map `y ↦ fderiv f y e₀` twice, the two orders agree —
`(f_uv)_u = (f_uu)_v`.  This is `secondDirectional_commute_two` applied to
`y ↦ fderiv f y e₀` (which is `C²` because `f` is `C∞`). -/
lemma thirdMixedPartials_commute₀₁₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => fderiv ℝ f z !₂[1, 0]) y !₂[0, 1])
          x !₂[1, 0] =
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => fderiv ℝ f z !₂[1, 0]) y !₂[1, 0])
          x !₂[0, 1] := by
  intro x hx
  let F : ℝ² → ℝ³ := fun z => fderiv ℝ f z !₂[1, 0]
  have hF2 : ContDiffOn ℝ 2 F stripInterior :=
    (contDiffOn_fderiv_dir₀ hf).of_le (by decide)
  have hc := Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
    (E := ℝ²) (F := ℝ³) (s := stripInterior) (f := F) (x := x)
    stripInterior_isOpen hx hF2 !₂[0, 1] !₂[1, 0]
  simpa [F] using hc

/-- On the interior of the strip the derivative of `f` is a linear isometry
(norm-preserving) in every direction. -/
lemma fderiv_norm_eq_interior {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ y ∈ stripInterior, ∀ v : ℝ², ‖fderiv ℝ f y v‖ = ‖v‖ := by
  intro y hy v
  have hc : fderivWithin ℝ f unitStrip y = fderiv ℝ f y :=
    fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_mem_stripInterior hy)
  have h := fderiv_norm_eq hf y (stripInterior_subset_unitStrip hy) v
  simpa [hc] using h

/-- On the interior of the strip the two coordinate tangent fields are
orthogonal. -/
lemma inner_fderivs_interior {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ y ∈ stripInterior,
      inner ℝ (fderiv ℝ f y !₂[1, 0]) (fderiv ℝ f y !₂[0, 1]) = 0 := by
  intro y hy
  let L : ℝ² →ₗ[ℝ] ℝ³ := (fderiv ℝ f y).toLinearMap
  have hL : ∀ v : ℝ², ‖L v‖ = ‖v‖ := by
    intro v
    exact fderiv_norm_eq_interior hf y hy v
  have hint := Commons.Analysis.InnerProductSpace.inner_map_map_of_isometry L hL !₂[1, 0] !₂[0, 1]
  rw [inner_basis₀₁] at hint
  simpa [L] using hint

/-- **Instantiation of `secondDeriv_orth_tangent`**: on the interior of the
strip every second directional derivative of the isometric immersion `f` is
orthogonal to both tangent fields (pure-normal second derivatives). -/
lemma secondDeriv_normal_interior {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[1, 0]) x !₂[0, 1])
          (fderiv ℝ f x !₂[0, 1]) = 0 ∧
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[1, 0]) x !₂[0, 1])
          (fderiv ℝ f x !₂[1, 0]) = 0 ∧
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[1, 0]) x !₂[1, 0])
          (fderiv ℝ f x !₂[0, 1]) = 0 ∧
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[0, 1]) x !₂[0, 1])
          (fderiv ℝ f x !₂[1, 0]) = 0 := by
  intro x hx
  have h2 : ContDiffOn ℝ 2 f stripInterior :=
    (hf.smooth.mono stripInterior_subset_unitStrip).of_le (by decide)
  have hunit₀ : ∀ y ∈ stripInterior, ‖fderiv ℝ f y !₂[1, 0]‖ = 1 := by
    intro y hy
    rw [fderiv_norm_eq_interior hf y hy]
    exact norm_basis₀
  have hunit₁ : ∀ y ∈ stripInterior, ‖fderiv ℝ f y !₂[0, 1]‖ = 1 := by
    intro y hy
    rw [fderiv_norm_eq_interior hf y hy]
    exact norm_basis₁
  exact Commons.Analysis.Calculus.FDeriv.secondDeriv_orth_tangent
    (E := ℝ²) (F := ℝ³) (s := stripInterior) (f := f) (x := x)
    (u := !₂[1, 0]) (v := !₂[0, 1])
    stripInterior_isOpen hx h2 hunit₀ hunit₁ (inner_fderivs_interior hf)

/-- **Normality in tangent-function form**: on the interior of the strip each
second derivative of the tangent frame (in coordinate directions) is
orthogonal to both tangent vectors.  This is `secondDeriv_normal_interior`
rewritten with the smooth tangent fields `tangent₀, tangent₁`. -/
lemma secondDeriv_normal_tangent {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      (inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) (tangent₀ f x) = 0 ∧
       inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) (tangent₁ f x) = 0 ∧
       inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) (tangent₁ f x) = 0 ∧
       inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) (tangent₀ f x) = 0) := by
  intro x hx
  rcases (secondDeriv_normal_interior hf x hx) with ⟨h1, h2, h3, h4⟩
  have he0 : (fun y : ℝ² => tangent₀ f y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y !₂[1, 0]) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact tangent₀_eq_fderiv hy
  have he1 : (fun y : ℝ² => tangent₁ f y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y !₂[0, 1]) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact tangent₁_eq_fderiv hy
  have convA : fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[1, 0]) x !₂[0, 1] =
      fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1] := by
    rw [← Filter.EventuallyEq.fderiv_eq he0]
  have convB : fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[1, 0]) x !₂[1, 0] =
      fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0] := by
    rw [← Filter.EventuallyEq.fderiv_eq he0]
  have convC : fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[0, 1]) x !₂[0, 1] =
      fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1] := by
    rw [← Filter.EventuallyEq.fderiv_eq he1]
  constructor
  · rw [convA.symm, tangent₀_eq_fderiv hx]
    exact h2
  constructor
  · rw [convA.symm, tangent₁_eq_fderiv hx]
    exact h1
  constructor
  · rw [convB.symm, tangent₁_eq_fderiv hx]
    exact h3
  · rw [convC.symm, tangent₀_eq_fderiv hx]
    exact h4

/-- **Same-direction normality**: differentiating the unit identities
`⟪tangent₀, tangent₀⟫ = 1` and `⟪tangent₁, tangent₁⟫ = 1` gives
`⟪∂₀ t₀, t₀⟫ = 0` and `⟪∂₁ t₁, t₁⟫ = 0` on the interior. -/
lemma secondDeriv_normal_sameDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) (tangent₀ f x) = 0 ∧
      inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) (tangent₁ f x) = 0 := by
  intro x hx
  let g₀ : ℝ² → ℝ := fun y => inner ℝ (tangent₀ f y) (tangent₀ f y)
  let g₁ : ℝ² → ℝ := fun y => inner ℝ (tangent₁ f y) (tangent₁ f y)
  have hg₀ : g₀ =ᶠ[𝓝 x] (fun _ : ℝ² => (1 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    have ht : ‖tangent₀ f y‖ = 1 := tangent₀_norm hf y (stripInterior_subset_unitStrip hy)
    dsimp [g₀]
    rw [inner_self_eq_norm_sq_to_K]
    rw [ht]
    norm_num
  have hg₁ : g₁ =ᶠ[𝓝 x] (fun _ : ℝ² => (1 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    have ht : ‖tangent₁ f y‖ = 1 := tangent₁_norm hf y (stripInterior_subset_unitStrip hy)
    dsimp [g₁]
    rw [inner_self_eq_norm_sq_to_K]
    rw [ht]
    norm_num
  have hd0 : DifferentiableAt ℝ (fun y : ℝ² => tangent₀ f y) x := differentiableAt_tangent₀ hf x hx
  have hd1 : DifferentiableAt ℝ (fun y : ℝ² => tangent₁ f y) x := differentiableAt_tangent₁ hf x hx
  have hfd0 : fderiv ℝ g₀ x = 0 := by
    have hc : HasFDerivAt g₀ (0 : ℝ² →L[ℝ] ℝ) x :=
      (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hg₀
    exact hc.fderiv
  have hfd1 : fderiv ℝ g₁ x = 0 := by
    have hc : HasFDerivAt g₁ (0 : ℝ² →L[ℝ] ℝ) x :=
      (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hg₁
    exact hc.fderiv
  have hv0 := fderiv_inner_apply (𝕜 := ℝ) hd0 hd0 !₂[1, 0]
  have hv1 := fderiv_inner_apply (𝕜 := ℝ) hd1 hd1 !₂[0, 1]
  constructor
  · have hmain0 : inner ℝ (tangent₀ f x) (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) +
        inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) (tangent₀ f x) = 0 := by
      rw [← hv0]
      rw [hfd0]
      simp
    have hsym := real_inner_comm (x := tangent₀ f x) (y := fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0])
    rw [hsym] at hmain0
    linarith
  · have hmain1 : inner ℝ (tangent₁ f x) (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) +
        inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) (tangent₁ f x) = 0 := by
      rw [← hv1]
      rw [hfd1]
      simp
    have hsym := real_inner_comm (x := tangent₁ f x) (y := fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1])
    rw [hsym] at hmain1
    linarith

/-- **Frame decomposition for `A := ∂₀t₀`**: the second derivative of the
tangent frame along `e₀` is a multiple of the unit normal, on the interior. -/
lemma secondDeriv_frame_decomp₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0] =
        inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) (unitNormal f x) •
          unitNormal f x := by
  intro x hx
  let w : ℝ³ := fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]
  have hxn : x ∈ unitStrip := stripInterior_subset_unitStrip hx
  have hc := Commons.Analysis.InnerProductSpace.orthonormal_frame_decomp
    (a := tangent₀ f x) (b := tangent₁ f x) (c := unitNormal f x) (w := w)
    (tangent₀_norm hf x hxn) (tangent₁_norm hf x hxn) (unitNormal_norm hf x hxn)
    (tangent₀₁_orthogonal hf x hxn)
    (tangent₀_normal_orthogonal hf x hxn)
    (tangent₁_normal_orthogonal hf x hxn)
    ((secondDeriv_normal_sameDir hf x hx).1)
    (secondDeriv_normal_tangent hf x hx).2.2.1
  simpa [w] using hc

/-- **Frame decomposition for `B := ∂₁t₀`**: the mixed second derivative of
the tangent frame is a multiple of the unit normal, on the interior. -/
lemma secondDeriv_frame_decomp₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1] =
        inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) (unitNormal f x) •
          unitNormal f x := by
  intro x hx
  let w : ℝ³ := fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]
  have hxn : x ∈ unitStrip := stripInterior_subset_unitStrip hx
  have hc := Commons.Analysis.InnerProductSpace.orthonormal_frame_decomp
    (a := tangent₀ f x) (b := tangent₁ f x) (c := unitNormal f x) (w := w)
    (tangent₀_norm hf x hxn) (tangent₁_norm hf x hxn) (unitNormal_norm hf x hxn)
    (tangent₀₁_orthogonal hf x hxn)
    (tangent₀_normal_orthogonal hf x hxn)
    (tangent₁_normal_orthogonal hf x hxn)
    ((secondDeriv_normal_tangent hf x hx).1)
    (secondDeriv_normal_tangent hf x hx).2.1
  simpa [w] using hc

/-- **Frame decomposition for `C := ∂₁t₁`**: the second derivative of the
tangent frame along `e₁` is a multiple of the unit normal, on the interior. -/
lemma secondDeriv_frame_decomp₂ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1] =
        inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) (unitNormal f x) •
          unitNormal f x := by
  intro x hx
  let w : ℝ³ := fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]
  have hxn : x ∈ unitStrip := stripInterior_subset_unitStrip hx
  have hc := Commons.Analysis.InnerProductSpace.orthonormal_frame_decomp
    (a := tangent₀ f x) (b := tangent₁ f x) (c := unitNormal f x) (w := w)
    (tangent₀_norm hf x hxn) (tangent₁_norm hf x hxn) (unitNormal_norm hf x hxn)
    (tangent₀₁_orthogonal hf x hxn)
    (tangent₀_normal_orthogonal hf x hxn)
    (tangent₁_normal_orthogonal hf x hxn)
    ((secondDeriv_normal_tangent hf x hx).2.2.2)
    (secondDeriv_normal_sameDir hf x hx).2
  simpa [w] using hc

/-- Mixed partials of the tangent fields commute: `∂₀t₁ = ∂₁t₀` (both equal
`f_uv`) on the interior of the strip. -/
lemma mixedSym_tangent {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0] =
        fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1] := by
  intro x hx
  have h2 : ContDiffOn ℝ 2 f stripInterior :=
    (hf.smooth.mono stripInterior_subset_unitStrip).of_le (by decide)
  have hswap := Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
    (E := ℝ²) (F := ℝ³) (s := stripInterior) (f := f) (x := x)
    stripInterior_isOpen hx h2 !₂[0, 1] !₂[1, 0]
  have he0 : (fun y : ℝ² => tangent₀ f y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y !₂[1, 0]) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact tangent₀_eq_fderiv hy
  have he1 : (fun y : ℝ² => tangent₁ f y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y !₂[0, 1]) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact tangent₁_eq_fderiv hy
  calc
    fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]
        = fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[0, 1]) x !₂[1, 0] := by
          rw [Filter.EventuallyEq.fderiv_eq he1]
    _ = fderiv ℝ (fun y : ℝ² => fderiv ℝ f y !₂[1, 0]) x !₂[0, 1] := hswap
    _ = fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1] := by
          rw [Filter.EventuallyEq.fderiv_eq he0]

/-- **First product-rule identification** (differentiating `⟪B, t₁⟫ ≡ 0` in the
`e₀` direction): with `D := ∂₀(∂₁t₀) x` and `B := ∂₁t₀ x`,
`⟪D, t₁ x⟫ = −⟪B x, B x⟫` on the interior. -/
lemma detIdent₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[0, 1])
          x !₂[1, 0]) (tangent₁ f x) =
        - inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1])
            (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) := by
  intro x hx
  let F : ℝ² → ℝ³ := fun y => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[0, 1]
  let T₁ : ℝ² → ℝ³ := fun y => tangent₁ f y
  have htau : ContDiffOn ℝ ∞ (fun z : ℝ² => tangent₀ f z) stripInterior :=
    contDiffOn_tangent₀ hf
  have hFdiff : DifferentiableAt ℝ F x := by
    have hdfw : ContDiffOn ℝ ∞
        (fun y : ℝ² => fderivWithin ℝ (fun z : ℝ² => tangent₀ f z) stripInterior y)
        stripInterior :=
      htau.fderivWithin stripInterior_isOpen.uniqueDiffOn (by decide)
    have hpt : ∀ y ∈ stripInterior,
        fderiv ℝ (fun z : ℝ² => tangent₀ f z) y =
          fderivWithin ℝ (fun z : ℝ² => tangent₀ f z) stripInterior y := by
      intro y hy
      exact (fderivWithin_of_isOpen stripInterior_isOpen hy).symm
    have hdf : ContDiffOn ℝ ∞ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y)
        stripInterior := hdfw.congr hpt
    have hc : ContDiffOn ℝ ∞ (fun y : ℝ² => (fderiv ℝ (fun z : ℝ² => tangent₀ f z) y) !₂[0, 1])
        stripInterior := ContDiffOn.clm_apply hdf contDiffOn_const
    exact ((hc.differentiableOn (by simp)) x hx).differentiableAt
      (IsOpen.mem_nhds stripInterior_isOpen hx)
  have hzero : (fun y : ℝ² => inner ℝ (F y) (T₁ y)) =ᶠ[𝓝 x]
      (fun _ : ℝ² => (0 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact (secondDeriv_normal_tangent hf y hy).2.1
  have hmain := Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually
    (E := ℝ³) (G := ℝ²) (f := F) (g := T₁) (x := x)
    hFdiff (differentiableAt_tangent₁ hf x hx) hzero !₂[1, 0]
  have hmix := mixedSym_tangent hf x hx
  have hgoal : inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[0, 1])
          x !₂[1, 0]) (tangent₁ f x) +
      inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1])
          (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) = 0 := by
    simpa [F, T₁, hmix] using hmain
  linarith

/-- Third directional derivatives of the (smooth) tangent field `t₀` commute
on the interior: `∂₀(∂₁t₀) = ∂₁(∂₀t₀)`.  This is
`secondDirectional_commute_two` applied to the `C²` map `y ↦ tangent₀ f y`. -/
lemma thirdDeriv_tangent_commute {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[0, 1])
          x !₂[1, 0] =
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[1, 0])
          x !₂[0, 1] := by
  intro x hx
  have ht2 : ContDiffOn ℝ 2 (fun z : ℝ² => tangent₀ f z) stripInterior :=
    (contDiffOn_tangent₀ hf).of_le (by decide)
  exact Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
    (E := ℝ²) (F := ℝ³) (s := stripInterior) (f := fun z : ℝ² => tangent₀ f z) (x := x)
    stripInterior_isOpen hx ht2 !₂[0, 1] !₂[1, 0]

/-- **Second product-rule identification** (differentiating `⟪A, t₁⟫ ≡ 0` in
the `e₁` direction): with `D := ∂₁(∂₀t₀) x`, `A := ∂₀t₀ x` and
`C := ∂₁t₁ x`, `⟪D, t₁ x⟫ = −⟪A x, C x⟫` on the interior. -/
lemma detIdent₂ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[1, 0])
          x !₂[0, 1]) (tangent₁ f x) =
        - inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0])
            (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) := by
  intro x hx
  let A : ℝ² → ℝ³ := fun y => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[1, 0]
  let T₁ : ℝ² → ℝ³ := fun y => tangent₁ f y
  have hAdiff : DifferentiableAt ℝ A x := by
    have htau : ContDiffOn ℝ ∞ (fun z : ℝ² => tangent₀ f z) stripInterior :=
      contDiffOn_tangent₀ hf
    have hdfw : ContDiffOn ℝ ∞
        (fun y : ℝ² => fderivWithin ℝ (fun z : ℝ² => tangent₀ f z) stripInterior y)
        stripInterior :=
      htau.fderivWithin stripInterior_isOpen.uniqueDiffOn (by decide)
    have hpt : ∀ y ∈ stripInterior,
        fderiv ℝ (fun z : ℝ² => tangent₀ f z) y =
          fderivWithin ℝ (fun z : ℝ² => tangent₀ f z) stripInterior y := by
      intro y hy
      exact (fderivWithin_of_isOpen stripInterior_isOpen hy).symm
    have hdf : ContDiffOn ℝ ∞ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y)
        stripInterior := hdfw.congr hpt
    have hc : ContDiffOn ℝ ∞ (fun y : ℝ² => (fderiv ℝ (fun z : ℝ² => tangent₀ f z) y) !₂[1, 0])
        stripInterior := ContDiffOn.clm_apply hdf contDiffOn_const
    exact ((hc.differentiableOn (by simp)) x hx).differentiableAt
      (IsOpen.mem_nhds stripInterior_isOpen hx)
  have hzero : (fun y : ℝ² => inner ℝ (A y) (T₁ y)) =ᶠ[𝓝 x]
      (fun _ : ℝ² => (0 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact (secondDeriv_normal_tangent hf y hy).2.2.1
  have hmain := Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually
    (E := ℝ³) (G := ℝ²) (f := A) (g := T₁) (x := x)
    hAdiff (differentiableAt_tangent₁ hf x hx) hzero !₂[0, 1]
  have hgoal : inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[1, 0])
          x !₂[0, 1]) (tangent₁ f x) +
      inner ℝ (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0])
          (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) = 0 := by
    simpa [A, T₁] using hmain
  linarith

/-- **Diagonal Weingarten relation for `e₀`**: on the interior,
`⟪dN f x e₀, tangent₀ f x⟫ = −⟪N x, ∂₀ tangent₀ x⟫`. -/
lemma weingarten_diag₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      inner ℝ (dN f x !₂[1, 0]) (tangent₀ f x) =
        - inner ℝ (unitNormal f x)
            (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) := by
  intro x hx
  let N : ℝ² → ℝ³ := fun y => unitNormal f y
  have hdifN : DifferentiableAt ℝ N x := by
    exact (((contDiffOn_unitNormal hf).differentiableOn (by simp) x hx).differentiableAt
      (IsOpen.mem_nhds stripInterior_isOpen hx))
  have hzero : (fun y : ℝ² => inner ℝ (N y) (tangent₀ f y)) =ᶠ[𝓝 x]
      (fun _ : ℝ² => (0 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact unitNormal_orth_tangent₀ f y
  have hmain := Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually
    (E := ℝ³) (G := ℝ²) (f := N) (g := fun y : ℝ² => tangent₀ f y) (x := x)
    hdifN (differentiableAt_tangent₀ hf x hx) hzero !₂[1, 0]
  have hdN : fderiv ℝ N x = dN f x := by
    simpa [N] using (dN_eq_fderiv (f := f) hx).symm
  have hmain' : inner ℝ (dN f x !₂[1, 0]) (tangent₀ f x) +
      inner ℝ (unitNormal f x)
        (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) = 0 := by
    simpa [hdN, N] using hmain
  linarith

/-- **Diagonal Weingarten relation for `e₁`**: on the interior,
`⟪dN f x e₁, tangent₁ f x⟫ = −⟪N x, ∂₁ tangent₁ x⟫`. -/
lemma weingarten_diag₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      inner ℝ (dN f x !₂[0, 1]) (tangent₁ f x) =
        - inner ℝ (unitNormal f x)
            (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) := by
  intro x hx
  let N : ℝ² → ℝ³ := fun y => unitNormal f y
  have hdifN : DifferentiableAt ℝ N x := by
    exact (((contDiffOn_unitNormal hf).differentiableOn (by simp) x hx).differentiableAt
      (IsOpen.mem_nhds stripInterior_isOpen hx))
  have hzero : (fun y : ℝ² => inner ℝ (N y) (tangent₁ f y)) =ᶠ[𝓝 x]
      (fun _ : ℝ² => (0 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact unitNormal_orth_tangent₁ f y
  have hmain := Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually
    (E := ℝ³) (G := ℝ²) (f := N) (g := fun y : ℝ² => tangent₁ f y) (x := x)
    hdifN (differentiableAt_tangent₁ hf x hx) hzero !₂[0, 1]
  have hdN : fderiv ℝ N x = dN f x := by
    simpa [N] using (dN_eq_fderiv (f := f) hx).symm
  have hmain' : inner ℝ (dN f x !₂[0, 1]) (tangent₁ f x) +
      inner ℝ (unitNormal f x)
        (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) = 0 := by
    simpa [hdN, N] using hmain
  linarith

/-- **Flatness of the shape operator**: on the interior of the strip the
determinant of the shape-operator matrix vanishes (`pr = q²`), because the
immersion is isometric: the second derivatives of `f` are pure normal
(`A = pN`, `B = qN`, `C = rN`), and the equality of third mixed partials
expanded in the frame gives `pr = q²`.  Equivalently, the second fundamental
form has a kernel: the bend direction. -/
lemma shapeOperator_det_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, Matrix.det (Matrix.of (dNentry f x)) = 0 := by
  intro x hx
  let e₀ : ℝ² := !₂[1, 0]
  let e₁ : ℝ² := !₂[0, 1]
  let Nx : ℝ³ := unitNormal f x
  let A : ℝ³ := fderiv ℝ (fun y : ℝ² => tangent₀ f y) x e₀
  let B : ℝ³ := fderiv ℝ (fun y : ℝ² => tangent₀ f y) x e₁
  let C : ℝ³ := fderiv ℝ (fun y : ℝ² => tangent₁ f y) x e₁
  let p : ℝ := inner ℝ A Nx
  let q : ℝ := inner ℝ B Nx
  let r : ℝ := inner ℝ C Nx
  have hxn : x ∈ unitStrip := stripInterior_subset_unitStrip hx
  have hNunit : inner ℝ Nx Nx = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    rw [unitNormal_norm hf x hxn]
    norm_num
  have hA : A = p • Nx := by
    simpa [A, p, Nx, e₀] using secondDeriv_frame_decomp₀ hf x hx
  have hB : B = q • Nx := by
    simpa [B, q, Nx, e₁] using secondDeriv_frame_decomp₁ hf x hx
  have hC : C = r • Nx := by
    simpa [C, r, Nx, e₁] using secondDeriv_frame_decomp₂ hf x hx
  -- third partials identify D: detIdent₁ vs detIdent₂
  have hD : fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[0, 1])
        x !₂[1, 0] =
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[1, 0])
        x !₂[0, 1] :=
    thirdDeriv_tangent_commute hf x hx
  have hI1 : inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[0, 1])
        x !₂[1, 0]) (tangent₁ f x) = - inner ℝ B B := by
    simpa [B, e₁] using detIdent₁ hf x hx
  have hI2 : inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => tangent₀ f z) y !₂[1, 0])
        x !₂[0, 1]) (tangent₁ f x) = - inner ℝ A C := by
    simpa [A, C, e₀, e₁] using detIdent₂ hf x hx
  have hcomp : inner ℝ B B = inner ℝ A C := by
    rw [hD] at hI1
    rw [hI2] at hI1
    linarith
  have hAC : inner ℝ A C = p * r := by
    rw [hA, hC]
    rw [inner_smul_left, inner_smul_right, hNunit]
    simp
  have hBB : inner ℝ B B = q * q := by
    rw [hB]
    rw [inner_smul_left, inner_smul_right, hNunit]
    simp
  have hprod : p * r = q * q := by
    nlinarith [hcomp, hAC, hBB]
  -- entries of the shape matrix in terms of p, q, r
  have hE00 : dNentry f x 0 0 = -p := by
    unfold dNentry
    simp
    rw [weingarten_diag₀ hf x hx]
    congr 1
    rw [real_inner_comm]
  have hE11 : dNentry f x 1 1 = -r := by
    unfold dNentry
    simp
    rw [weingarten_diag₁ hf x hx]
    congr 1
    rw [real_inner_comm]
  have hE01 : dNentry f x 0 1 = -q := by
    unfold dNentry
    simp
    rw [dN_tangent₁_relation hf x hx]
    congr 1
    have hmix := mixedSym_tangent hf x hx
    rw [real_inner_comm, hmix]
  have hE10 : dNentry f x 1 0 = -q := by
    unfold dNentry
    simp
    rw [dN_tangent₀_relation hf x hx]
    congr 1
    rw [real_inner_comm]
  -- final determinant computation
  rw [Matrix.det_fin_two]
  rw [Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply]
  rw [hE00, hE11, hE01, hE10]
  nlinarith [hprod]

/-- Any vector of `ℝ²` is the sum of its coordinate multiples of the two
standard basis vectors. -/
lemma vec_eq_basis (v : ℝ²) :
    v = (v 0) • (!₂[1, 0] : ℝ²) + (v 1) • (!₂[0, 1] : ℝ²) := by
  ext i <;> fin_cases i <;> simp

/-- The shape operator is tangent-valued as a *range* statement: on the
interior of the strip the image of `dN f x` lies in the span of the tangent
frame `{tangent₀ f x, tangent₁ f x}`. -/
lemma dN_range_sub_span {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      LinearMap.range (dN f x).toLinearMap ≤
        Submodule.span ℝ ({tangent₀ f x, tangent₁ f x} : Set ℝ³) := by
  intro x hx
  rintro w ⟨v, rfl⟩
  apply Commons.Analysis.InnerProductSpace.span_of_orth_normal
    (t₀ := tangent₀ f x) (t₁ := tangent₁ f x) (Nx := unitNormal f x)
    (w := (dN f x).toLinearMap v)
  · exact tangent₀_norm hf x (stripInterior_subset_unitStrip hx)
  · exact tangent₁_norm hf x (stripInterior_subset_unitStrip hx)
  · exact unitNormal_norm hf x (stripInterior_subset_unitStrip hx)
  · exact tangent₀₁_orthogonal hf x (stripInterior_subset_unitStrip hx)
  · exact tangent₀_normal_orthogonal hf x (stripInterior_subset_unitStrip hx)
  · exact tangent₁_normal_orthogonal hf x (stripInterior_subset_unitStrip hx)
  · exact dN_tangent_valued hf x hx v

/-- **Kernel-vector step**: if the (transposed) shape matrix annihilates a
coordinate vector `w`, then the shape operator kills the corresponding domain
vector.  (The shape matrix is the Gram representation of `dN` over the frame
`(e₀̂,e₁̂) → (t₀,t₁)`; a zero left-kernel vector is a zero of `dN`.) -/
lemma shape_ker_of_mulVec {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ w : Fin 2 → ℝ,
      ((Matrix.of (dNentry f x))ᵀ).mulVec w = 0 →
      (dN f x) (WithLp.toLp 2 w) = 0 := by
  intro x hx w hw
  have hxn : x ∈ unitStrip := stripInterior_subset_unitStrip hx
  let v : ℝ³ := (dN f x) (WithLp.toLp 2 w)
  let b₀ : ℝ² := !₂[1, 0]
  let b₁ : ℝ² := !₂[0, 1]
  let t₀ : ℝ³ := tangent₀ f x
  let t₁ : ℝ³ := tangent₁ f x
  let Nx : ℝ³ := unitNormal f x
  have hbv : (WithLp.toLp 2 w) = (w 0) • b₀ + (w 1) • b₁ := by
    ext i <;> fin_cases i <;> simp [b₀, b₁]
  have hmv₀ : dNentry f x 0 0 * w 0 + dNentry f x 1 0 * w 1 = 0 := by
    have h0 := congr_fun hw (0 : Fin 2)
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Fin.sum_univ_two] using h0
  have hmv₁ : dNentry f x 0 1 * w 0 + dNentry f x 1 1 * w 1 = 0 := by
    have h1 := congr_fun hw (1 : Fin 2)
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Fin.sum_univ_two] using h1
  have hv₀ : inner ℝ v t₀ = 0 := by
    dsimp [v]
    calc
      inner ℝ ((dN f x) (WithLp.toLp 2 w)) (tangent₀ f x)
          = inner ℝ ((dN f x) ((w 0) • b₀ + (w 1) • b₁)) (tangent₀ f x) := by
              rw [hbv]
      _ = (w 0) * inner ℝ ((dN f x) b₀) (tangent₀ f x) +
          (w 1) * inner ℝ ((dN f x) b₁) (tangent₀ f x) := by
              rw [map_add, map_smul, map_smul, inner_add_left, inner_smul_left, inner_smul_left]
              simp
      _ = (w 0) * dNentry f x 0 0 + (w 1) * dNentry f x 1 0 := by
              simp [dNentry, b₀, b₁]
      _ = 0 := by nlinarith [hmv₀]
  have hv₁ : inner ℝ v t₁ = 0 := by
    dsimp [v]
    calc
      inner ℝ ((dN f x) (WithLp.toLp 2 w)) (tangent₁ f x)
          = inner ℝ ((dN f x) ((w 0) • b₀ + (w 1) • b₁)) (tangent₁ f x) := by
              rw [hbv]
      _ = (w 0) * inner ℝ ((dN f x) b₀) (tangent₁ f x) +
          (w 1) * inner ℝ ((dN f x) b₁) (tangent₁ f x) := by
              rw [map_add, map_smul, map_smul, inner_add_left, inner_smul_left, inner_smul_left]
              simp
      _ = (w 0) * dNentry f x 0 1 + (w 1) * dNentry f x 1 1 := by
              simp [dNentry, b₀, b₁]
      _ = 0 := by nlinarith [hmv₁]
  have hvN : inner ℝ v Nx = 0 := by
    dsimp [v, Nx]
    exact dN_tangent_valued hf x hx (WithLp.toLp 2 w)
  change v = 0
  have hexp : v = inner ℝ v t₀ • t₀ + inner ℝ v t₁ • t₁ + inner ℝ v Nx • Nx := by
    apply Commons.Analysis.InnerProductSpace.orthonormal_triple_expansion
      (t₀ := t₀) (t₁ := t₁) (Nx := Nx) (v := v)
    · simpa [t₀] using tangent₀_norm hf x hxn
    · simpa [t₁] using tangent₁_norm hf x hxn
    · simpa [Nx] using unitNormal_norm hf x hxn
    · simpa [t₀, t₁] using tangent₀₁_orthogonal hf x hxn
    · simpa [t₀, Nx] using tangent₀_normal_orthogonal hf x hxn
    · simpa [t₁, Nx] using tangent₁_normal_orthogonal hf x hxn
  rw [hexp, hv₀, hv₁, hvN]
  simp


/-- **The bend direction is a line**: on the interior of the strip, wherever
the shape operator is nonzero, its kernel `bendDir f x` is spanned by a
single nonzero vector (the unique bend direction of paper §2.1, Lemma `mc`). -/
lemma bendDir_is_line {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, dN f x ≠ 0 →
      ∃ v : ℝ², v ≠ 0 ∧ bendDir f x = Submodule.span ℝ {v} := by
  intro x hx hT
  unfold bendDir
  have hM0 : Matrix.det (Matrix.of (dNentry f x)) = 0 := shapeOperator_det_zero hf x hx
  have hMt : Matrix.det ((Matrix.of (dNentry f x))ᵀ) = 0 := by
    simpa [Matrix.det_transpose] using hM0
  rcases ((Matrix.exists_mulVec_eq_zero_iff
      (M := ((Matrix.of (dNentry f x))ᵀ))).2 hMt) with ⟨w, hwne, hw0⟩
  have huT : (dN f x).toLinearMap (WithLp.toLp 2 w) = 0 :=
    shape_ker_of_mulVec hf x hx w hw0
  have hker : (dN f x).toLinearMap.ker ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨WithLp.toLp 2 w, ?_, ?_⟩
    · exact LinearMap.mem_ker.2 huT
    · intro hz
      have hof := congrArg (WithLp.ofLp (p := 2)) hz
      have hw0' : w = 0 := by simpa using hof
      exact hwne hw0'
  have hT' : (dN f x).toLinearMap ≠ 0 := by
    intro hz
    apply hT
    apply ContinuousLinearMap.ext
    intro v
    have hf := congrArg (fun φ : ℝ² →ₗ[ℝ] ℝ³ => φ v) hz
    simpa using hf
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by
    simpa using (Module.finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))
  simpa using (Commons.LinearAlgebra.ker_line_of_finrank_two
    (K := ℝ) (E := EuclideanSpace ℝ (Fin 2)) (F := EuclideanSpace ℝ (Fin 3))
    (T := (dN f x).toLinearMap) hfin hker hT')

/-- Rewriting the frame decomposition of `A := ∂₀t₀` in terms of the shape
matrix entry: `∂₀t₀ x = −dNentry f x 0 0 • N x` on the interior. -/
lemma secondDeriv_dNentry₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0] =
        - dNentry f x 0 0 • unitNormal f x := by
  intro x hx
  have hA := secondDeriv_frame_decomp₀ hf x hx
  have hE : dNentry f x 0 0 = - inner ℝ
      (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) (unitNormal f x) := by
    rw [show dNentry f x 0 0 = inner ℝ (dN f x !₂[1, 0]) (tangent₀ f x) by simp [dNentry]]
    rw [weingarten_diag₀ hf x hx]
    congr 1
    rw [real_inner_comm]
  simpa [hE] using hA

/-- Rewriting the frame decomposition of `B := ∂₁t₀` in terms of the shape
matrix entry: `∂₁t₀ x = −dNentry f x 1 0 • N x` on the interior. -/
lemma secondDeriv_dNentry₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1] =
        - dNentry f x 1 0 • unitNormal f x := by
  intro x hx
  have hB := secondDeriv_frame_decomp₁ hf x hx
  have hE : dNentry f x 1 0 = - inner ℝ
      (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) (unitNormal f x) := by
    rw [show dNentry f x 1 0 = inner ℝ (dN f x !₂[0, 1]) (tangent₀ f x) by simp [dNentry]]
    rw [dN_tangent₀_relation hf x hx]
    congr 1
    rw [real_inner_comm]
  simpa [hE] using hB

/-- Rewriting the frame decomposition of `C := ∂₁t₁` in terms of the shape
matrix entry: `∂₁t₁ x = −dNentry f x 1 1 • N x` on the interior. -/
lemma secondDeriv_dNentry₂ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1] =
        - dNentry f x 1 1 • unitNormal f x := by
  intro x hx
  have hC := secondDeriv_frame_decomp₂ hf x hx
  have hE : dNentry f x 1 1 = - inner ℝ
      (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) (unitNormal f x) := by
    rw [show dNentry f x 1 1 = inner ℝ (dN f x !₂[0, 1]) (tangent₁ f x) by simp [dNentry]]
    rw [weingarten_diag₁ hf x hx]
    congr 1
    rw [real_inner_comm]
  simpa [hE] using hC

/-- **Kernel quadratic relations**: if `v = (c₀, c₁)` lies in the kernel of
`dN` at an interior point, then for each `j` the contraction
`c₀·S₀ⱼ + c₁·S₁ⱼ` of the shape matrix vanishes (this is `⟪dN v, t_j⟫ = 0`
written in the frame). -/
lemma kernel_inner_relations {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ v : ℝ²,
      dN f x v = 0 →
      (v 0) * dNentry f x 0 0 + (v 1) * dNentry f x 1 0 = 0 ∧
      (v 0) * dNentry f x 0 1 + (v 1) * dNentry f x 1 1 = 0 := by
  intro x hx v hv0
  let e0 : ℝ² := !₂[1, 0]
  let e1 : ℝ² := !₂[0, 1]
  have hve : v = (v 0) • e0 + (v 1) • e1 := by simpa [e0, e1] using vec_eq_basis v
  have hi₀ : inner ℝ (dN f x v) (tangent₀ f x) = 0 := by rw [hv0]; simp
  have hi₁ : inner ℝ (dN f x v) (tangent₁ f x) = 0 := by rw [hv0]; simp
  constructor
  · -- inner (dN v)(t₀) = (v 0) * dNentry f x 0 0 + (v 1) * dNentry f x 1 0:
    have hcalc : inner ℝ (dN f x v) (tangent₀ f x) =
        (v 0) * dNentry f x 0 0 + (v 1) * dNentry f x 1 0 := by
      calc
        inner ℝ (dN f x v) (tangent₀ f x)
            = inner ℝ (dN f x ((v 0) • e0 + (v 1) • e1)) (tangent₀ f x) :=
              congrArg (fun u : ℝ² => inner ℝ (dN f x u) (tangent₀ f x)) hve
        _ = (v 0) * inner ℝ (dN f x e0) (tangent₀ f x) +
            (v 1) * inner ℝ (dN f x e1) (tangent₀ f x) := by
              rw [map_add, map_smul, map_smul, inner_add_left, inner_smul_left, inner_smul_left]
              simp
        _ = (v 0) * dNentry f x 0 0 + (v 1) * dNentry f x 1 0 := by
              simp [dNentry, e0, e1]
    simpa [hcalc] using hi₀
  · have hcalc : inner ℝ (dN f x v) (tangent₁ f x) =
        (v 0) * dNentry f x 0 1 + (v 1) * dNentry f x 1 1 := by
      calc
        inner ℝ (dN f x v) (tangent₁ f x)
            = inner ℝ (dN f x ((v 0) • e0 + (v 1) • e1)) (tangent₁ f x) :=
              congrArg (fun u : ℝ² => inner ℝ (dN f x u) (tangent₁ f x)) hve
        _ = (v 0) * inner ℝ (dN f x e0) (tangent₁ f x) +
            (v 1) * inner ℝ (dN f x e1) (tangent₁ f x) := by
              rw [map_add, map_smul, map_smul, inner_add_left, inner_smul_left, inner_smul_left]
              simp
        _ = (v 0) * dNentry f x 0 1 + (v 1) * dNentry f x 1 1 := by
              simp [dNentry, e0, e1]
    simpa [hcalc] using hi₁

/-- **Quadratic form vanishes on kernel vectors**: if `dN f x v = 0`, then
`vᵀ S v = 0` for the shape matrix `S = dNentry f x` — the scalar that will
give `D²f(v,v) = −(vᵀ S v)·N x = 0`. -/
lemma quadForm_zero_of_kernel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ v : ℝ²,
      dN f x v = 0 →
      (v 0)^2 * dNentry f x 0 0 + (v 0) * (v 1) * dNentry f x 0 1 +
        (v 1) * (v 0) * dNentry f x 1 0 + (v 1)^2 * dNentry f x 1 1 = 0 := by
  intro x hx v hv0
  rcases (kernel_inner_relations hf x hx v hv0) with ⟨r0, r1⟩
  have hs := shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)
  rw [hs]
  rw [hs] at r1
  have hfac : (v 0) * ((v 0) * dNentry f x 0 0 + (v 1) * dNentry f x 1 0) +
      (v 1) * ((v 0) * dNentry f x 1 0 + (v 1) * dNentry f x 1 1) = 0 := by
    rw [r0, r1]
    ring
  nlinarith [hfac]

end Submission.PaperBand
end
