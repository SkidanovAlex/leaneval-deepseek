import Submission.PaperBand.Codazzi
import Submission.PaperBand.McStraight
import Submission.Commons.Algebra.Matrix.symm_det0_kernel_perp_ne
import Submission.Commons.Analysis.InnerProductSpace.orthonormal_triple_expansion

open OptimalMoebius Topology ContDiff
open scoped BigOperators
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Flat stops are impossible — rotated shape-operator machinery (GREEN, zero sorry)

Part 1 (GREEN this session) of the global-rigidity core.  Target: a
straight kernel segment through a point of `U = {dN ≠ 0}` cannot stop at an
interior *flat* point `p` (`dN f p = 0`).  Combined with
`KernelMaximal.kernel_segment_two_sided` this makes every bend reach the
strip boundary (closes `GlobalRigidity.no_flat_endpoint_global` and
`main0_test.bends_reach_boundary_test`), bypassing the whole S4
ε-contraction/connector machinery (Bricks D/E and the flat-set-structure
crux of session_status12): the flat stop is ruled out by a purely local
one-variable ODE.

## Mathematics (paper & pencil — done, see session_status25)
Along the segment the shape operator `S = dN` satisfies `S(x) w₀ = 0` and
`S(x) ≠ 0`; at the stop `S(p) = 0`.  In the basis `(W, U)`, `W = w₀`,
`U = perp W`, the matrix of `S` has entries `(A,B,C)` (the quadratic forms
`nfsA/nfsB/nfsC`, equal to `⟪ŜP, df Q⟫` by `nfsA_eq_inner` & friends), so
along the arc `A = B = 0` and `C =: γ ≠ 0`, with `γ(0) = 0` at `p`.
Codazzi in the constant frame (here: `nfs_codazzi₀`: `A_U = B_W`,
`nfs_codazzi₁`: `B_U = C_W`, both proved for the generic quadratic entry
`nfsGen_codazzi₀/₁` in any constant basis) plus flatness
(`nfs_det_zero`: `AC − B² = 0`) give, from the second transverse derivative
of `AC − B² ≡ 0` at arc points, the one-variable ODE
`γ γ'' = 2 (γ')²` along the arc.  A smooth `γ` with `γ(0) = 0`, `γ ≠ 0` on
`(0,δ)` satisfying the ODE there does not exist (reciprocal affine, hence
bounded, contradicts `γ → 0`).  Hence flat stops are impossible.

## GREEN in this file (part 1 — rotated-frame infrastructure)
* `perp`, coordinates `perp_0/perp_1`, `inner_perp_self`;
* `nfsA/nfsB/nfsC`, `nfsGen` (generic quadratic entry for constant basis
  vectors), and the inner-product identities `nfsA_eq_inner`,
  `nfsB_eq_inner`, `nfsC_eq_inner` (via `entry_gen`);
* kernel vanishing `nfsA_zero_of_kernel`, `nfsB_zero_of_kernel`;
* flatness in the rotated basis `nfs_det_zero` (`AC − B² = 0`);
* differentiability of the rotated entries;
* derivative decomposition `fderiv_decomp_coords`; the derivative of the
  generic entry `fderiv_nfsGen`;
* **rotated Codazzi** `nfs_codazzi₀` (`A_U = B_W`) and `nfs_codazzi₁`
  (`B_U = C_W`), via the basis-free `nfsGen_codazzi₀/₁`.

## Next (part 2, later sessions)
`dN_eq_zero_of_entries` (⟹ `γ ≠ 0` on the arc from `dN ≠ 0`), the
pullback/ODE derivation (`γ γ'' = 2γ'²` along the arc), the 1-D
contradiction lemma, and the assembly `no_flat_stop` → (with
`KernelMaximal.kernel_segment_two_sided`) `bends_reach_boundary_test` →
Prop main0 → Lemma T → Lemma G.
-/


noncomputable section
namespace Submission.PaperBand

/-- The perpendicular of `W` with the same norm. -/
noncomputable def perp (W : ℝ²) : ℝ² := !₂[-W 1, W 0]

lemma perp_0 (W : ℝ²) : (perp W) 0 = -W 1 := by simp [perp]
lemma perp_1 (W : ℝ²) : (perp W) 1 = W 0 := by simp [perp]

lemma inner_perp_self (W : ℝ²) : inner ℝ (perp W) W = 0 := by
  rw [PiLp.inner_apply]
  simp [perp]
  ring

/-- A vector is the linear combination of the standard basis with its
coordinates. -/
lemma vec_eq_coords (V : ℝ²) : V = V 0 • (!₂[1,0] : ℝ²) + V 1 • (!₂[0,1] : ℝ²) := by
  ext i <;> fin_cases i <;> simp

/-- Tangent vector in direction `V` decomposes over the tangent frame. -/
lemma fderiv_decomp_tangent {f : ℝ² → ℝ³} {x : ℝ²} (hx : x ∈ stripInterior) (V : ℝ²) :
    fderiv ℝ f x V = V 0 • tangent₀ f x + V 1 • tangent₁ f x := by
  rw [vec_eq_coords V, map_add, map_smul, map_smul]
  rw [tangent₀_eq_fderiv hx, tangent₁_eq_fderiv hx]
  simp

/-- Shape-operator entry `(0,0)` in the rotated basis `(W, perp W)` (equal to
`⟪dN W, df W⟫`, see `nfsA_eq_inner`). -/
noncomputable def nfsA (f : ℝ² → ℝ³) (W : ℝ²) : ℝ² → ℝ := fun x =>
  (W 0)^2 * S00f f x + 2 * (W 0 * W 1) * S10f f x + (W 1)^2 * S11f f x

/-- Shape-operator entry `(0,1)` in the rotated basis (with `U = perp W`). -/
noncomputable def nfsB (f : ℝ² → ℝ³) (W : ℝ²) : ℝ² → ℝ := fun x =>
  (W 0 * (-W 1)) * S00f f x + (W 0 * W 0 - W 1 * W 1) * S10f f x +
    (W 1 * W 0) * S11f f x

/-- Shape-operator entry `(1,1)` in the rotated basis (with `U = perp W`). -/
noncomputable def nfsC (f : ℝ² → ℝ³) (W : ℝ²) : ℝ² → ℝ := fun x =>
  (-W 1)^2 * S00f f x + 2 * ((-W 1) * W 0) * S10f f x + (W 0)^2 * S11f f x

/-- Bilinear expansion: `⟪dN P, df Q⟫` in the entry functions. -/
lemma entry_gen {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (P Q : ℝ²) :
    inner ℝ (dN f x P) (fderiv ℝ f x Q) =
      (P 0 * Q 0) * S00f f x + (P 0 * Q 1 + P 1 * Q 0) * S10f f x + (P 1 * Q 1) * S11f f x := by
  have hdNP : dN f x P = P 0 • dN f x !₂[1,0] + P 1 • dN f x !₂[0,1] := by
    rw [vec_eq_coords P, map_add, map_smul, map_smul]
    simp
  have hdfQ : fderiv ℝ f x Q = Q 0 • tangent₀ f x + Q 1 • tangent₁ f x :=
    fderiv_decomp_tangent hx Q
  rw [hdNP, hdfQ]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have h00 : inner ℝ (dN f x !₂[1,0]) (tangent₀ f x) = S00f f x := by
    simp [S00f, dNentry]
  have h01 : inner ℝ (dN f x !₂[1,0]) (tangent₁ f x) = S10f f x := by
    rw [S10f]
    rw [← shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)]
    simp [dNentry]
  have h10 : inner ℝ (dN f x !₂[0,1]) (tangent₀ f x) = S10f f x := by
    simp [S10f, dNentry]
  have h11 : inner ℝ (dN f x !₂[0,1]) (tangent₁ f x) = S11f f x := by
    simp [S11f, dNentry]
  rw [h00, h01, h10, h11]
  ring

/-- `nfsA f W x = ⟪dN W, df W⟫`. -/
lemma nfsA_eq_inner {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (W : ℝ²) :
    nfsA f W x = inner ℝ (dN f x W) (fderiv ℝ f x W) := by
  rw [entry_gen hf hx W W]
  unfold nfsA
  ring

/-- `nfsB f W x = ⟪dN W, df U⟫` with `U = perp W`. -/
lemma nfsB_eq_inner {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (W : ℝ²) :
    nfsB f W x = inner ℝ (dN f x W) (fderiv ℝ f x (perp W)) := by
  rw [entry_gen hf hx W (perp W)]
  rw [perp_0 W, perp_1 W]
  unfold nfsB
  ring

/-- `nfsC f W x = ⟪dN U, df U⟫` with `U = perp W`. -/
lemma nfsC_eq_inner {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (W : ℝ²) :
    nfsC f W x = inner ℝ (dN f x (perp W)) (fderiv ℝ f x (perp W)) := by
  have hg : inner ℝ (dN f x (perp W)) (fderiv ℝ f x (perp W)) =
      ((perp W) 0 * (perp W) 0) * S00f f x +
        ((perp W) 0 * (perp W) 1 + (perp W) 1 * (perp W) 0) * S10f f x +
        ((perp W) 1 * (perp W) 1) * S11f f x := entry_gen hf hx (perp W) (perp W)
  rw [hg]
  rw [perp_0 W, perp_1 W]
  unfold nfsC
  ring


/-- Kernel kills the rotated `(0,0)` entry: `dN f x W = 0` implies
`nfsA f W x = 0`. -/
lemma nfsA_zero_of_kernel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (W : ℝ²) (hk : dN f x W = 0) : nfsA f W x = 0 := by
  rw [nfsA_eq_inner hf hx W, hk]
  simp

/-- Kernel kills the rotated `(0,1)` entry. -/
lemma nfsB_zero_of_kernel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (W : ℝ²) (hk : dN f x W = 0) : nfsB f W x = 0 := by
  rw [nfsB_eq_inner hf hx W, hk]
  simp

/-- Flatness in the rotated basis: `A·C − B² = 0` on the interior (this is
`det S = 0` in the basis `(W, perp W)`). -/
lemma nfs_det_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (W : ℝ²) :
    ∀ x ∈ stripInterior, nfsA f W x * nfsC f W x - (nfsB f W x)^2 = 0 := by
  intro x hx
  have hg := gauss_scalar hf x hx
  unfold nfsA nfsB nfsC
  have hfac : ((W 0)^2 * S00f f x + 2 * (W 0 * W 1) * S10f f x + (W 1)^2 * S11f f x) *
        ((-W 1)^2 * S00f f x + 2 * ((-W 1) * W 0) * S10f f x + (W 0)^2 * S11f f x) -
      ((W 0 * (-W 1)) * S00f f x + (W 0 * W 0 - W 1 * W 1) * S10f f x + (W 1 * W 0) * S11f f x)^2
      = ((W 0)^2 + (W 1)^2)^2 * (S00f f x * S11f f x - (S10f f x)^2) := by
    ring
  rw [hfac]
  have hzero : S00f f x * S11f f x - (S10f f x)^2 = 0 := by
    nlinarith [hg]
  rw [hzero]
  ring

/-- The rotated entries are differentiable at interior points. -/
lemma differentiableAt_nfsA {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (W : ℝ²) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (nfsA f W) x := by
  intro x hx
  have hd0 : DifferentiableAt ℝ (S00f f) x := differentiableAt_dNentry₀₀ hf x hx
  have hd1 : DifferentiableAt ℝ (S10f f) x := differentiableAt_dNentry₁₀ hf x hx
  have hd2 : DifferentiableAt ℝ (S11f f) x := differentiableAt_dNentry₁₁ hf x hx
  unfold nfsA
  exact ((hd0.const_mul ((W 0)^2)).add (hd1.const_mul (2 * (W 0 * W 1)))).add (hd2.const_mul ((W 1)^2))

/-- The rotated entries are differentiable at interior points. -/
lemma differentiableAt_nfsB {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (W : ℝ²) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (nfsB f W) x := by
  intro x hx
  have hd0 : DifferentiableAt ℝ (S00f f) x := differentiableAt_dNentry₀₀ hf x hx
  have hd1 : DifferentiableAt ℝ (S10f f) x := differentiableAt_dNentry₁₀ hf x hx
  have hd2 : DifferentiableAt ℝ (S11f f) x := differentiableAt_dNentry₁₁ hf x hx
  unfold nfsB
  exact ((hd0.const_mul (W 0 * (-W 1))).add (hd1.const_mul (W 0 * W 0 - W 1 * W 1))).add
    (hd2.const_mul (W 1 * W 0))

/-- The rotated entries are differentiable at interior points. -/
lemma differentiableAt_nfsC {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (W : ℝ²) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (nfsC f W) x := by
  intro x hx
  have hd0 : DifferentiableAt ℝ (S00f f) x := differentiableAt_dNentry₀₀ hf x hx
  have hd1 : DifferentiableAt ℝ (S10f f) x := differentiableAt_dNentry₁₀ hf x hx
  have hd2 : DifferentiableAt ℝ (S11f f) x := differentiableAt_dNentry₁₁ hf x hx
  unfold nfsC
  exact ((hd0.const_mul ((-W 1)^2)).add (hd1.const_mul (2 * ((-W 1) * W 0)))).add
    (hd2.const_mul ((W 0)^2))

/-- The derivative of a differentiable scalar along `V` decomposes over the
standard basis: `fderiv g x V = V0·(fderiv g x e0) + V1·(fderiv g x e1)`. -/
lemma fderiv_decomp_coords {g : ℝ² → ℝ} {x : ℝ²} (hdg : DifferentiableAt ℝ g x) (V : ℝ²) :
    fderiv ℝ g x V = V 0 * fderiv ℝ g x !₂[1,0] + V 1 * fderiv ℝ g x !₂[0,1] := by
  conv_lhs => rw [vec_eq_coords V]
  rw [map_add]
  rw [map_smul, map_smul]
  simp


/-- Generic quadratic entry `⟪ŜP, Q⟫` (as a combination of the standard
entry functions). -/
noncomputable def nfsGen (f : ℝ² → ℝ³) (P Q : ℝ²) : ℝ² → ℝ := fun y =>
  (P 0 * Q 0) * S00f f y + (P 0 * Q 1 + P 1 * Q 0) * S10f f y + (P 1 * Q 1) * S11f f y

lemma nfsA_eq_gen (f : ℝ² → ℝ³) (W : ℝ²) : nfsA f W = nfsGen f W W := by
  funext x
  unfold nfsA nfsGen
  ring

lemma nfsB_eq_gen (f : ℝ² → ℝ³) (W : ℝ²) : nfsB f W = nfsGen f W (perp W) := by
  funext x
  unfold nfsB nfsGen
  rw [perp_0 W, perp_1 W]
  ring

lemma nfsC_eq_gen (f : ℝ² → ℝ³) (W : ℝ²) : nfsC f W = nfsGen f (perp W) (perp W) := by
  funext x
  unfold nfsC nfsGen
  rw [perp_0 W, perp_1 W]
  ring

/-- The derivative of a generic quadratic entry along `V` is the same
quadratic combination of the entry derivatives. -/
lemma fderiv_nfsGen {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (P Q V : ℝ²) :
    fderiv ℝ (nfsGen f P Q) x V =
      (P 0 * Q 0) * fderiv ℝ (S00f f) x V +
        (P 0 * Q 1 + P 1 * Q 0) * fderiv ℝ (S10f f) x V +
        (P 1 * Q 1) * fderiv ℝ (S11f f) x V := by
  have hd0 : DifferentiableAt ℝ (S00f f) x := differentiableAt_dNentry₀₀ hf x hx
  have hd1 : DifferentiableAt ℝ (S10f f) x := differentiableAt_dNentry₁₀ hf x hx
  have hd2 : DifferentiableAt ℝ (S11f f) x := differentiableAt_dNentry₁₁ hf x hx
  have hc (c : ℝ) (g : ℝ² → ℝ) : (fun y : ℝ² => c * g y) = c • g := by
    funext y
    rfl
  unfold nfsGen
  have hfuneq : (fun y : ℝ² => (P 0 * Q 0) * S00f f y + (P 0 * Q 1 + P 1 * Q 0) * S10f f y + (P 1 * Q 1) * S11f f y) =
      (P 0 * Q 0) • S00f f + ((P 0 * Q 1 + P 1 * Q 0) • S10f f + (P 1 * Q 1) • S11f f) := by
    funext y
    simp [smul_eq_mul]
    ring
  rw [hfuneq]
  rw [fderiv_add]
  · rw [fderiv_add]
    · rw [fderiv_const_smul (c := P 0 * Q 0) hd0]
      rw [fderiv_const_smul (c := P 0 * Q 1 + P 1 * Q 0) hd1]
      rw [fderiv_const_smul (c := P 1 * Q 1) hd2]
      simp [smul_eq_mul]
      ring
    · exact hd1.const_smul (P 0 * Q 1 + P 1 * Q 0)
    · exact hd2.const_smul (P 1 * Q 1)
  · exact hd0.const_smul (P 0 * Q 0)
  · exact (hd1.const_smul (P 0 * Q 1 + P 1 * Q 0)).add (hd2.const_smul (P 1 * Q 1))


/-- Codazzi (first equation) for the generic quadratic entry, in an
arbitrary constant basis: `fderiv(gen(P,P)) x Q = fderiv(gen(P,Q)) x P`. -/
lemma nfsGen_codazzi₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (P Q : ℝ²) :
    fderiv ℝ (nfsGen f P P) x Q = fderiv ℝ (nfsGen f P Q) x P := by
  have hd0 : DifferentiableAt ℝ (S00f f) x := differentiableAt_dNentry₀₀ hf x hx
  have hd1 : DifferentiableAt ℝ (S10f f) x := differentiableAt_dNentry₁₀ hf x hx
  have hd2 : DifferentiableAt ℝ (S11f f) x := differentiableAt_dNentry₁₁ hf x hx
  rw [fderiv_nfsGen hf hx P P Q, fderiv_nfsGen hf hx P Q P]
  rw [fderiv_decomp_coords hd0 Q, fderiv_decomp_coords hd0 P]
  rw [fderiv_decomp_coords hd1 Q, fderiv_decomp_coords hd1 P]
  rw [fderiv_decomp_coords hd2 Q, fderiv_decomp_coords hd2 P]
  rw [codazzi₀ hf x hx, codazzi₁ hf x hx]
  ring

/-- Codazzi (second equation) for the generic quadratic entry, in an
arbitrary constant basis: `fderiv(gen(P,Q)) x Q = fderiv(gen(Q,Q)) x P`. -/
lemma nfsGen_codazzi₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (P Q : ℝ²) :
    fderiv ℝ (nfsGen f P Q) x Q = fderiv ℝ (nfsGen f Q Q) x P := by
  have hd0 : DifferentiableAt ℝ (S00f f) x := differentiableAt_dNentry₀₀ hf x hx
  have hd1 : DifferentiableAt ℝ (S10f f) x := differentiableAt_dNentry₁₀ hf x hx
  have hd2 : DifferentiableAt ℝ (S11f f) x := differentiableAt_dNentry₁₁ hf x hx
  rw [fderiv_nfsGen hf hx P Q Q, fderiv_nfsGen hf hx Q Q P]
  rw [fderiv_decomp_coords hd0 Q, fderiv_decomp_coords hd0 P]
  rw [fderiv_decomp_coords hd1 Q, fderiv_decomp_coords hd1 P]
  rw [fderiv_decomp_coords hd2 Q, fderiv_decomp_coords hd2 P]
  rw [codazzi₀ hf x hx, codazzi₁ hf x hx]
  ring

/-- Rotated Codazzi, first equation: with `U = perp W`,
`A_U = B_W` on the interior. -/
lemma nfs_codazzi₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (W : ℝ²) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (nfsA f W) x (perp W) = fderiv ℝ (nfsB f W) x W := by
  intro x hx
  rw [nfsA_eq_gen f W, nfsB_eq_gen f W]
  exact nfsGen_codazzi₀ hf hx W (perp W)

/-- Rotated Codazzi, second equation: with `U = perp W`,
`B_U = C_W` on the interior. -/
lemma nfs_codazzi₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (W : ℝ²) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (nfsB f W) x (perp W) = fderiv ℝ (nfsC f W) x W := by
  intro x hx
  rw [nfsB_eq_gen f W, nfsC_eq_gen f W]
  exact nfsGen_codazzi₁ hf hx W (perp W)


/-- The kernel condition `dN f x W = 0` in entry coordinates: first row
`S₀₀·W₀ + S₁₀·W₁ = 0`. -/
lemma entry_ker_eq₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (W : ℝ²) (hk : dN f x W = 0) :
    dNentry f x 0 0 * W 0 + dNentry f x 1 0 * W 1 = 0 := by
  have hin : inner ℝ (dN f x W) (tangent₀ f x) = 0 := by
    rw [hk]
    simp
  have hg := entry_gen hf hx W (!₂[1,0] : ℝ²)
  simp at hg
  rw [← tangent₀_eq_fderiv hx] at hg
  rw [hg] at hin
  nlinarith

/-- The kernel condition `dN f x W = 0` in entry coordinates: second row
`S₀₁·W₀ + S₁₁·W₁ = 0`. -/
lemma entry_ker_eq₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (W : ℝ²) (hk : dN f x W = 0) :
    dNentry f x 0 1 * W 0 + dNentry f x 1 1 * W 1 = 0 := by
  have hin : inner ℝ (dN f x W) (tangent₁ f x) = 0 := by
    rw [hk]
    simp
  have hg := entry_gen hf hx W (!₂[0,1] : ℝ²)
  simp at hg
  rw [← tangent₁_eq_fderiv hx] at hg
  rw [hg] at hin
  -- restore the entry-notation in hin (simp unfolded the S00f/S11f abbrevs)
  change W 0 * dNentry f x 1 0 + W 1 * dNentry f x 1 1 = 0 at hin
  -- dNentry 0 1 = dNentry 1 0 by symmetry
  rw [← shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)] at hin
  nlinarith


/-- All three standard entries of the shape operator vanishing forces
`dN f x = 0`. -/
lemma dN_zero_of_entries_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior)
    (h00 : dNentry f x 0 0 = 0) (h10 : dNentry f x 1 0 = 0) (h11 : dNentry f x 1 1 = 0) :
    dN f x = 0 := by
  have hxu : x ∈ unitStrip := stripInterior_subset_unitStrip hx
  rcases orthonormal_frame hf x hxu with ⟨ht0, ht1, hN, h01, h0N, h1N⟩
  have h01' : dNentry f x 0 1 = 0 := by
    rw [shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)]
    exact h10
  have hd0 : dN f x !₂[1,0] = 0 := by
    have he := Commons.Analysis.InnerProductSpace.orthonormal_triple_expansion
      (t₀ := tangent₀ f x) (t₁ := tangent₁ f x) (Nx := unitNormal f x)
      (v := dN f x !₂[1,0]) ht0 ht1 hN h01 h0N h1N
    have hi0 : inner ℝ (dN f x !₂[1,0]) (tangent₀ f x) = dNentry f x 0 0 := by simp [dNentry]
    have hi1 : inner ℝ (dN f x !₂[1,0]) (tangent₁ f x) = dNentry f x 0 1 := by simp [dNentry]
    rw [hi0, hi1, h00, h01'] at he
    rw [dN_tangent_valued hf x hx (!₂[1,0] : ℝ²)] at he
    simpa using he
  have hd1 : dN f x !₂[0,1] = 0 := by
    have he := Commons.Analysis.InnerProductSpace.orthonormal_triple_expansion
      (t₀ := tangent₀ f x) (t₁ := tangent₁ f x) (Nx := unitNormal f x)
      (v := dN f x !₂[0,1]) ht0 ht1 hN h01 h0N h1N
    have hi0 : inner ℝ (dN f x !₂[0,1]) (tangent₀ f x) = dNentry f x 1 0 := by simp [dNentry]
    have hi1 : inner ℝ (dN f x !₂[0,1]) (tangent₁ f x) = dNentry f x 1 1 := by simp [dNentry]
    rw [hi0, hi1, h10, h11] at he
    rw [dN_tangent_valued hf x hx (!₂[0,1] : ℝ²)] at he
    simpa using he
  ext v
  have hv : v = v 0 • (!₂[1,0] : ℝ²) + v 1 • (!₂[0,1] : ℝ²) := by
    ext i <;> fin_cases i <;> simp
  rw [hv, map_add, map_smul, map_smul, hd0, hd1]
  simp

/-- A nonzero shape operator has a nonzero standard entry. -/
lemma entry_exists_of_dN_ne_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (hS : dN f x ≠ 0) :
    dNentry f x 0 0 ≠ 0 ∨ dNentry f x 1 0 ≠ 0 ∨ dNentry f x 1 1 ≠ 0 := by
  by_contra h
  push_neg at h
  exact hS (dN_zero_of_entries_zero hf hx h.1 h.2.1 h.2.2)

/-- A nonzero vector has a nonzero coordinate. -/
lemma vec_ne_zero_coord {W : ℝ²} (hW : W ≠ 0) : W 0 ≠ 0 ∨ W 1 ≠ 0 := by
  by_contra h
  push_neg at h
  apply hW
  ext i <;> fin_cases i <;> simp [h.1, h.2]

/-- On the arc of a nonzero-shape-operator kernel segment the rotated
`C`-entry is nonzero (`γ ≠ 0`): `dN f x W = 0`, `dN f x ≠ 0`, `W ≠ 0` force
`nfsC f W x ≠ 0`. -/
lemma nfsC_ne_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (W : ℝ²) (hW : W ≠ 0) (hS : dN f x ≠ 0)
    (hk : dN f x W = 0) : nfsC f W x ≠ 0 := by
  have hM := entry_exists_of_dN_ne_zero hf hx hS
  have hw := vec_ne_zero_coord hW
  have hk0 : dNentry f x 0 0 * W 0 + dNentry f x 1 0 * W 1 = 0 := entry_ker_eq₀ hf hx W hk
  have hk1' : dNentry f x 1 0 * W 0 + dNentry f x 1 1 * W 1 = 0 := by
    have hk1 := entry_ker_eq₁ hf hx W hk
    rw [shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)] at hk1
    exact hk1
  -- the target is the commons lemma's evaluation form
  have hc : nfsC f W x =
      (-W 1)^2 * dNentry f x 0 0 + 2 * ((-W 1) * W 0) * dNentry f x 1 0 + (W 0)^2 * dNentry f x 1 1 := by
    unfold nfsC
    simp [S00f, S10f, S11f]
  rw [hc]
  exact Commons.Algebra.Matrix.symm_det0_kernel_perp_ne
    (a := dNentry f x 0 0) (b := dNentry f x 1 0) (c := dNentry f x 1 1)
    (w0 := W 0) (w1 := W 1) (gauss_scalar hf x hx) hk0 hk1' hw hM


/-- The rotated entries are `C∞` on the strip interior. -/
lemma contDiffOn_nfsA {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (W : ℝ²) :
    ContDiffOn ℝ ∞ (nfsA f W) stripInterior := by
  have h0 : ContDiffOn ℝ ∞ (S00f f) stripInterior := contDiffOn_S00f hf
  have h1 : ContDiffOn ℝ ∞ (S10f f) stripInterior := contDiffOn_S10f hf
  have h2 : ContDiffOn ℝ ∞ (S11f f) stripInterior := contDiffOn_S11f hf
  unfold nfsA
  have he : (fun x : ℝ² => (W 0)^2 * S00f f x + 2 * (W 0 * W 1) * S10f f x + (W 1)^2 * S11f f x)
      = (W 0)^2 • S00f f + (2 * (W 0 * W 1)) • S10f f + (W 1)^2 • S11f f := by
    funext x
    simp
  rw [he]
  exact ((h0.const_smul ((W 0)^2)).add (h1.const_smul (2 * (W 0 * W 1)))).add (h2.const_smul ((W 1)^2))

/-- The rotated entries are `C∞` on the strip interior. -/
lemma contDiffOn_nfsB {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (W : ℝ²) :
    ContDiffOn ℝ ∞ (nfsB f W) stripInterior := by
  have h0 : ContDiffOn ℝ ∞ (S00f f) stripInterior := contDiffOn_S00f hf
  have h1 : ContDiffOn ℝ ∞ (S10f f) stripInterior := contDiffOn_S10f hf
  have h2 : ContDiffOn ℝ ∞ (S11f f) stripInterior := contDiffOn_S11f hf
  unfold nfsB
  have he : (fun x : ℝ² => (W 0 * (-W 1)) * S00f f x + (W 0 * W 0 - W 1 * W 1) * S10f f x + (W 1 * W 0) * S11f f x)
      = (W 0 * (-W 1)) • S00f f + (W 0 * W 0 - W 1 * W 1) • S10f f + (W 1 * W 0) • S11f f := by
    funext x
    simp
  rw [he]
  exact ((h0.const_smul (W 0 * (-W 1))).add (h1.const_smul (W 0 * W 0 - W 1 * W 1))).add
    (h2.const_smul (W 1 * W 0))

/-- The rotated entries are `C∞` on the strip interior. -/
lemma contDiffOn_nfsC {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (W : ℝ²) :
    ContDiffOn ℝ ∞ (nfsC f W) stripInterior := by
  have h0 : ContDiffOn ℝ ∞ (S00f f) stripInterior := contDiffOn_S00f hf
  have h1 : ContDiffOn ℝ ∞ (S10f f) stripInterior := contDiffOn_S10f hf
  have h2 : ContDiffOn ℝ ∞ (S11f f) stripInterior := contDiffOn_S11f hf
  unfold nfsC
  have he : (fun x : ℝ² => (-W 1)^2 * S00f f x + 2 * ((-W 1) * W 0) * S10f f x + (W 0)^2 * S11f f x)
      = (-W 1)^2 • S00f f + (2 * ((-W 1) * W 0)) • S10f f + (W 0)^2 • S11f f := by
    funext x
    simp
  rw [he]
  exact ((h0.const_smul ((-W 1)^2)).add (h1.const_smul (2 * ((-W 1) * W 0)))).add (h2.const_smul ((W 0)^2))

end Submission.PaperBand
