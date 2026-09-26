import Mathlib.Analysis.Calculus.ImplicitContDiff
import Submission.TrisecantCurve
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
import Submission.Commons.Analysis.Calculus.Implicit.implicitFunction_graph
import Submission.Commons.Analysis.Normed.isInvertible_of_det_columns

open LeanEval.KnotTheory.Quadrisecant
open scoped Topology Matrix
open Commons.Analysis.Calculus.FDeriv
open Commons.LinearAlgebra.LinearIndependent
set_option maxHeartbeats 800000

/-!
# Layer A (ix) — the local smooth curve through a general-position trisecant triple

This module completes Milestone 1 (`LocalSmoothCurveTheorem`, declared in
`TrisecantCurve.lean`): at a general-position collinear off-diagonal triple
`(a, b, m)` — i.e. the three knot points are collinear, pairwise distinct,
and the directional derivative of the collinearity map `Φ` has rank two —
a neighbourhood of the triple in the off-diagonal zero set of `Φ` is the
image of an injective `C¹` curve through the triple.

**Strategy (implicit function theorem on the reduced map).**  Let
`P_i, P_j` be two linearly independent hinge partials of `Φ` at the triple
(`PartialRankTwo` witness), and freeze them at the triple.  The **reduced
map** is `H(q) = (⟨Φ q, P_i⟩, ⟨Φ q, P_j⟩) : ℝ³ → ℝ²`.  Its derivative at
the triple is surjective (the Gram columns along the `i`- and `j`-axes are
the invertible Gram matrix of the pair, `pairReduced_fderiv_range_top` below).
Writing the parameter cube as `E₁ × E₂` with `E₁` the remaining coordinate
axis, the partial derivative of `H` along `E₂` is invertible, so the
product-domain implicit function theorem (`ContDiffAt.implicitFunction`,
Mathlib `Analysis.Calculus.ImplicitContDiff`) gives a local `C¹` function
`ψ : ℝ → E₂` whose graph is the local zero set of `H`.  The graph, mapped
back to the real parameter cube, is the curve `γ`.

The zero set of the reduced map is identified with the zero set of `Φ`
itself near the triple by `identification_of_pair_reduced_zero` (the
cross-product orthogonality/spanning argument of Step 3): `Φ(q)` is
orthogonal to `P_i, P_j` (on `H⁻¹(0)`) and always to the chord
`r q₁ − r q₂₁`, and those three vectors span the ambient space near the
triple.  Off-diagonalness is open and holds at the base triple, so the
curve stays inside the off-diagonal locus.

Everything here is verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The `m`-axis curve of `Φ` has derivative `∂_m` at the base triple. -/
lemma hasDerivAt_collinearity_m_axis {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) :
    HasDerivAt (fun s : ℝ => collinearityValue r a b (m + s)) (collPartialM r a b m) 0 := by
  have hd := hasDerivAt_collinearity_directional (h := h) (a := a) (b := b) (m := m)
    (da := 0) (db := 0) (dm := 1)
  have hd1 : HasDerivAt (fun s : ℝ => collinearityValue r a b (m + s))
      ((0 : ℝ) • (cross3 (velocity r a) (r a - r m) + cross3 (r a - r b) (velocity r a)) +
        (0 : ℝ) • cross3 (r a - r m) (velocity r b) + (1 : ℝ) • cross3 (velocity r m) (r a - r b)) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hd
    · filter_upwards with s
      simp
  apply HasDerivAt.congr_deriv hd1
  simp [collPartialM]

/-- The parameter-axis basis vector of index `k` in `RealParamTriple`
(`0 ↦ (1,(0,0))`, `1 ↦ (0,(1,0))`, `2 ↦ (0,(0,1))`). -/
def axisVec (k : Fin 3) : RealParamTriple :=
  (![((1 : ℝ), ((0 : ℝ), (0 : ℝ))), ((0 : ℝ), ((1 : ℝ), (0 : ℝ))),
     ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))] : Fin 3 → RealParamTriple) k

/-- Shift the `k`-th parameter coordinate of a triple by `s`. -/
def shiftAxis (q : RealParamTriple) (k : Fin 3) (s : ℝ) : RealParamTriple :=
  (![(q.1 + s, q.2), (q.1, (q.2.1 + s, q.2.2)), (q.1, (q.2.1, q.2.2 + s))]
    : Fin 3 → RealParamTriple) k

/-- The reduced map with the pair of hinge partials frozen at the base triple
`(a,b,m)`: `H_{ij}(q) = (⟨Φ q, ∂ᵢ⟩, ⟨Φ q, ∂ⱼ⟩)`. -/
def pairReduced (r : ℝ → Space) (a b m : ℝ) (i j : Fin 3) (q : RealParamTriple) : ℝ × ℝ :=
  (inner ℝ (collinearityMap r q) (collPartial r a b m i),
    inner ℝ (collinearityMap r q) (collPartial r a b m j))

/-- The reduced map is smooth for every pair of indices. -/
lemma contDiff_pairReduced {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) (i j : Fin 3) :
    ContDiff ℝ ⊤ (fun q : RealParamTriple => pairReduced r a b m i j q) := by
  unfold pairReduced
  have hPhi : ContDiff ℝ ⊤ (fun q : RealParamTriple => collinearityMap r q) :=
    contDiff_collinearityMap h
  have h1 : ContDiff ℝ ⊤ (fun q : RealParamTriple => inner ℝ (collinearityMap r q) (collPartial r a b m i)) :=
    (contDiff_inner_fixed (collPartial r a b m i)).comp hPhi
  have h2 : ContDiff ℝ ⊤ (fun q : RealParamTriple => inner ℝ (collinearityMap r q) (collPartial r a b m j)) :=
    (contDiff_inner_fixed (collPartial r a b m j)).comp hPhi
  exact h1.prodMk h2

/-- Along the axis of index `k` the collinearity map has derivative `∂_k` at
the base triple (the three axis cases bundled by index). -/
lemma hasDerivAt_collinearity_axis_index {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) (k : Fin 3) :
    HasDerivAt (fun s : ℝ => collinearityMap r (shiftAxis (a, (b, m)) k s)) (collPartial r a b m k) 0 := by
  fin_cases k
  · change HasDerivAt (fun s : ℝ => collinearityValue r (a + s) b m) (collPartialA r a b m) 0
    exact hasDerivAt_collinearity_a_axis h a b m
  · change HasDerivAt (fun s : ℝ => collinearityValue r a (b + s) m) (collPartialB r a b m) 0
    exact hasDerivAt_collinearity_b_axis h a b m
  · change HasDerivAt (fun s : ℝ => collinearityValue r a b (m + s)) (collPartialM r a b m) 0
    exact hasDerivAt_collinearity_m_axis h a b m

/-- The derivative of the reduced map along the axis of index `k` at the base
triple is the Gram column `(⟨∂_k, ∂_i⟩, ⟨∂_k, ∂_j⟩)` (generic column lemma). -/
lemma fderiv_pairReduced_axis {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) (k i j : Fin 3) :
    (fderiv ℝ (fun q : RealParamTriple => pairReduced r a b m i j q) (a, (b, m))) (axisVec k) =
      (inner ℝ (collPartial r a b m k) (collPartial r a b m i),
        inner ℝ (collPartial r a b m k) (collPartial r a b m j)) := by
  let R : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m i j q
  let p : RealParamTriple := (a, (b, m))
  have hD : DifferentiableAt ℝ R p := by
    dsimp [R, p]
    have hc : ContDiff ℝ ⊤ (fun q : RealParamTriple => pairReduced r a b m i j q) :=
      contDiff_pairReduced h a b m i j
    exact (ContDiff.of_le hc le_top).differentiable_one (a, (b, m))
  have hg : HasDerivAt (fun s : ℝ => R (p + s • axisVec k)) ((fderiv ℝ R p) (axisVec k)) 0 :=
    fderiv_along_axis_eq_deriv (H := R) (p := p) (e := axisVec k) hD
  -- compare with the axis curve derivative pushed through the two functionals
  have hg2 : HasDerivAt (fun s : ℝ => pairReduced r a b m i j (shiftAxis p k s))
      (inner ℝ (collPartial r a b m k) (collPartial r a b m i),
        inner ℝ (collPartial r a b m k) (collPartial r a b m j)) 0 := by
    have hgC : HasDerivAt (fun s : ℝ => collinearityMap r (shiftAxis p k s))
        (collPartial r a b m k) 0 := by
      dsimp [p]
      exact hasDerivAt_collinearity_axis_index h a b m k
    have h1 : HasDerivAt (fun s : ℝ => inner ℝ (collinearityMap r (shiftAxis p k s)) (collPartial r a b m i))
        (inner ℝ (collPartial r a b m k) (collPartial r a b m i)) 0 :=
      hasDerivAt_comp_clm hgC ((innerSLFlip ℝ (collPartial r a b m i) : Space →L[ℝ] ℝ))
    have h2 : HasDerivAt (fun s : ℝ => inner ℝ (collinearityMap r (shiftAxis p k s)) (collPartial r a b m j))
        (inner ℝ (collPartial r a b m k) (collPartial r a b m j)) 0 :=
      hasDerivAt_comp_clm hgC ((innerSLFlip ℝ (collPartial r a b m j) : Space →L[ℝ] ℝ))
    have hp := h1.prodMk h2
    apply HasDerivAt.congr_of_eventuallyEq
    · exact hp
    · filter_upwards with s
      simp [pairReduced, shiftAxis]
  have heq : (fun s : ℝ => R (p + s • axisVec k)) = fun s : ℝ => pairReduced r a b m i j (shiftAxis p k s) := by
    funext s
    dsimp [R, p]
    congr 1
    fin_cases k <;> simp [shiftAxis, axisVec]
  have hg' : HasDerivAt (fun s : ℝ => pairReduced r a b m i j (shiftAxis p k s))
      ((fderiv ℝ R p) (axisVec k)) 0 := by
    simpa [heq] using hg
  have huniq := HasDerivAt.unique hg2 hg'
  dsimp [R, p] at huniq
  exact huniq.symm

/-- Every hinge partial is orthogonal to the chord direction `r a − r b`
whenever the triple is collinear (`r a − r m = t • (r a − r b)`): each
partial is a scalar multiple of a velocity-cross vector `v(p_i) × Z`, and
cross products are orthogonal to their second argument. -/
lemma collPartial_orth_chord_index (r : ℝ → Space) {a b m t : ℝ}
    (hW : r a - r m = t • (r a - r b)) (i : Fin 3) :
    inner ℝ (collPartial r a b m i) (r a - r b) = 0 := by
  rw [collPartial_eq_coeff r a b m t hW i]
  rw [inner_smul_left]
  have hz : inner ℝ (cross3 (velocity r (collParam a b m i)) (r a - r b)) (r a - r b) = 0 := by
    have hanti := cross3_anticomm (r a - r b) (velocity r (collParam a b m i))
    rw [hanti]
    rw [inner_neg_left]
    have hzz := Commons.Analysis.CrossProduct.inner_cross3_self_left
      (u := r a - r b) (v := velocity r (collParam a b m i))
    simpa [cross3] using hzz
  simp [hz]

/-- The reduced map vanishes at the base triple if the triple is collinear. -/
lemma pairReduced_base_zero {r : ℝ → Space} (a b m : ℝ) (i j : Fin 3)
    (hΦ : collinearityValue r a b m = 0) :
    pairReduced r a b m i j (a, (b, m)) = (0, 0) := by
  have h0 : collinearityMap r (a, (b, m)) = (0 : Space) := by
    simpa [collinearityValue] using hΦ
  simp [pairReduced, h0]

/-- **Identification for an arbitrary pair of hinge partials**: near a
collinear zero triple with `P_i, P_j` independent, the zero set of the
reduced map `H_{ij}(q) = (⟨Φ q, P_i⟩, ⟨Φ q, P_j⟩)` coincides with the
collinearity zero set of `Φ`. -/
theorem identification_pairReduced_zero {r : ℝ → Space} (hr : IsSmoothKnot r) (a b m : ℝ)
    (i j : Fin 3) (hΦ : collinearityValue r a b m = 0) (hZ : r a - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartial r a b m i, collPartial r a b m j]) :
    ∃ U : Set RealParamTriple, IsOpen U ∧ (a, (b, m)) ∈ U ∧
      ∀ q ∈ U, pairReduced r a b m i j q = (0, 0) → collinearityMap r q = 0 := by
  let PA : Space := collPartial r a b m i
  let PB : Space := collPartial r a b m j
  rcases (chord_parallel_of_collinearity_eq_zero hZ hΦ) with ⟨t, hW⟩
  have hAz : inner ℝ PA (r a - r b) = 0 := by
    simpa [PA] using collPartial_orth_chord_index r hW i
  have hBz : inner ℝ PB (r a - r b) = 0 := by
    simpa [PB] using collPartial_orth_chord_index r hW j
  have hzA : inner ℝ (r a - r b) PA = 0 := by simpa [real_inner_comm] using hAz
  have hzB : inner ℝ (r a - r b) PB = 0 := by simpa [real_inner_comm] using hBz
  have hAB' : LinearIndependent ℝ ![PA, PB] := by simpa [PA, PB] using hLI
  have hZnot : (r a - r b) ∉ Submodule.span ℝ ({PA, PB} : Set Space) :=
    chord_not_mem_span_of_orth hzA hzB hZ
  let K : Submodule ℝ Space := Submodule.span ℝ ({PA, PB} : Set Space)
  let chord : RealParamTriple → Space := fun q => r q.1 - r q.2.1
  have hchord : Continuous chord := by
    have hrc : Continuous r := hr.smooth.continuous
    have h1 : Continuous (fun q : RealParamTriple => r q.1) := hrc.comp continuous_fst
    have h2 : Continuous (fun q : RealParamTriple => r q.2.1) := hrc.comp (continuous_fst.comp continuous_snd)
    dsimp [chord]
    exact h1.sub h2
  have hKclosed : IsClosed (K : Set Space) := by
    dsimp [K]
    exact Submodule.closed_of_finiteDimensional (s := Submodule.span ℝ ({PA, PB} : Set Space))
  let U : Set RealParamTriple := chord ⁻¹' ((K : Set Space)ᶜ)
  refine ⟨U, ?_, ?_, ?_⟩
  · show IsOpen U
    dsimp [U]
    exact hKclosed.isOpen_compl.preimage hchord
  · dsimp [U, K, chord]
    simpa using hZnot
  · intro q hq Hq
    have hqchord' : (r q.1 - r q.2.1) ∉ Submodule.span ℝ ({PA, PB} : Set Space) := by
      dsimp [U, K, chord] at hq
      simpa using hq
    have hrange : Submodule.span ℝ ({PA, PB, r q.1 - r q.2.1} : Set Space) = ⊤ := by
      have hLI2 : LinearIndependent ℝ (![PA, PB] : Fin 2 → Space) := hAB'
      have hnotmem : (r q.1 - r q.2.1) ∉ Submodule.span ℝ (Set.range (![PA, PB] : Fin 2 → Space)) := by
        rw [Commons.LinearAlgebra.Span.range_matrix_cons_two]
        exact hqchord'
      have hLI3 : LinearIndependent ℝ (![PA, PB, r q.1 - r q.2.1] : Fin 3 → Space) := by
        simpa using (hLI2.finSnoc hnotmem)
      exact Commons.LinearAlgebra.Span.span_top_of_three_independent (E := Space) finrank_Space hLI3
    have hxPA : inner ℝ (collinearityMap r q) PA = 0 := by
      have hf := congrArg Prod.fst Hq
      simpa [pairReduced, PA, PB] using hf
    have hxPB : inner ℝ (collinearityMap r q) PB = 0 := by
      have hs := congrArg Prod.snd Hq
      simpa [pairReduced, PA, PB] using hs
    have hxc : inner ℝ (collinearityMap r q) (r q.1 - r q.2.1) = 0 := collinearityMap_orth_chord r q
    have hzero := Commons.Analysis.InnerProductSpace.eq_zero_of_inner_eq_zero_of_span_top (x := collinearityMap r q)
      ({PA, PB, r q.1 - r q.2.1} : Set Space)
    have hxy : ∀ y ∈ ({PA, PB, r q.1 - r q.2.1} : Set Space), inner ℝ (collinearityMap r q) y = 0 := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact hxPA
      · exact hxPB
      · exact hxc
    exact hzero hxy hrange

/-- The derivative of the pair-reduced map at the base triple is surjective
when the pair of hinge partials is independent: `H_{ij}` is a submersion at
the triple (the Gram columns along the `i`- and `j`-axes span `ℝ²`). -/
theorem pairReduced_fderiv_range_top {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (i j : Fin 3)
    (hLI : LinearIndependent ℝ ![collPartial r a b m i, collPartial r a b m j]) :
    LinearMap.range ((fderiv ℝ (fun q : RealParamTriple => pairReduced r a b m i j q) (a, (b, m))).toLinearMap) = ⊤ := by
  let R : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m i j q
  let Pi : Space := collPartial r a b m i
  let Pj : Space := collPartial r a b m j
  let col_i : ℝ × ℝ := (inner ℝ Pi Pi, inner ℝ Pi Pj)
  let col_j : ℝ × ℝ := (inner ℝ Pj Pi, inner ℝ Pj Pj)
  have hci_eq : (fderiv ℝ (fun q : RealParamTriple => pairReduced r a b m i j q) (a, (b, m))) (axisVec i) = col_i := by
    simpa [col_i, Pi, Pj] using fderiv_pairReduced_axis h a b m i i j
  have hcj_eq : (fderiv ℝ (fun q : RealParamTriple => pairReduced r a b m i j q) (a, (b, m))) (axisVec j) = col_j := by
    simpa [col_j, Pi, Pj] using fderiv_pairReduced_axis h a b m j i j
  have hGdet0 : (Matrix.det !![inner ℝ Pi Pi, inner ℝ Pi Pj; inner ℝ Pj Pi, inner ℝ Pj Pj]) ≠ 0 := by
    dsimp [Pi, Pj]
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have hD : col_i.1 * col_j.2 - col_i.2 * col_j.1 ≠ 0 := by
    dsimp [col_i, col_j]
    have hEq : (Matrix.det !![inner ℝ Pi Pi, inner ℝ Pi Pj; inner ℝ Pj Pi, inner ℝ Pj Pj])
        = (inner ℝ Pi Pi) * (inner ℝ Pj Pj) - (inner ℝ Pi Pj) * (inner ℝ Pj Pi) := by
      rw [Matrix.det_fin_two_of]
    rw [← hEq]
    exact hGdet0
  have hLIp : LinearIndependent ℝ ![col_i, col_j] := linearIndependent_pair_prod_of_det_ne_zero hD
  let T : RealParamTriple →ₗ[ℝ] (ℝ × ℝ) :=
    (fderiv ℝ (fun q : RealParamTriple => pairReduced r a b m i j q) (a, (b, m))).toLinearMap
  have hci : col_i ∈ LinearMap.range T := by
    refine ⟨axisVec i, ?_⟩
    dsimp [T]
    exact hci_eq
  have hcj : col_j ∈ LinearMap.range T := by
    refine ⟨axisVec j, ?_⟩
    dsimp [T]
    exact hcj_eq
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod]
    simp
  have hrange : LinearMap.range T = ⊤ :=
    Commons.LinearAlgebra.Span.surjective_of_two_independent_in_range T hci hcj hLIp hfin
  simpa [T] using hrange

/-! ### Assembly: local smooth curve from split-coordinate data

The final curve is produced by the product-domain implicit function theorem
in a **split** of the parameter cube: the cube is written as
`ℝ × (ℝ × ℝ)` with the first factor the curve coordinate and the second
factor (an `ℝ²`) the complementary coordinates over which the zero set is a
graph.  The split is encoded by a homeomorphism pair `(A, B)` between the
split space and the actual triple space (per case: the identity or a
coordinate permutation).  The theorem below packages the whole
neighbourhood bookkeeping once, so the per-pair case proofs only have to
provide the concrete split, the reduced map, its differentiability, its
derivative-invertibility along the second factor, and the identification of
its zero set with the collinearity zero set. -/

/-- The off-diagonal locus is open. -/
lemma isOpen_RealOffDiagonalTriples {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsOpen (RealOffDiagonalTriples r) := by
  have hr : Continuous r := h.smooth.continuous
  have h1 : IsOpen {q : RealParamTriple | r q.1 - r q.2.1 ≠ 0} := by
    exact (isClosed_singleton (x := (0 : Space))).isOpen_compl.preimage
      ((hr.comp continuous_fst).sub (hr.comp (continuous_fst.comp continuous_snd)))
  have h2 : IsOpen {q : RealParamTriple | r q.1 - r q.2.2 ≠ 0} := by
    exact (isClosed_singleton (x := (0 : Space))).isOpen_compl.preimage
      ((hr.comp continuous_fst).sub (hr.comp (continuous_snd.comp continuous_snd)))
  have h3 : IsOpen {q : RealParamTriple | r q.2.2 - r q.2.1 ≠ 0} := by
    exact (isClosed_singleton (x := (0 : Space))).isOpen_compl.preimage
      ((hr.comp (continuous_snd.comp continuous_snd)).sub (hr.comp (continuous_fst.comp continuous_snd)))
  rw [show RealOffDiagonalTriples r = {q | r q.1 - r q.2.1 ≠ 0} ∩
        ({q | r q.1 - r q.2.2 ≠ 0} ∩ {q | r q.2.2 - r q.2.1 ≠ 0}) by
    ext q
    simp [RealOffDiagonalTriples]]
  exact h1.inter (h2.inter h3)

/-- Any neighbourhood of a real point contains an open interval around it. -/
lemma exists_Ioo_subset_of_mem_nhds {x : ℝ} {V : Set ℝ} (hV : V ∈ 𝓝 x) :
    ∃ a b : ℝ, a < x ∧ x < b ∧ Set.Ioo a b ⊆ V := by
  rcases Metric.mem_nhds_iff.mp hV with ⟨δ, hδ, hball⟩
  refine ⟨x - δ, x + δ, by linarith, by linarith, ?_⟩
  intro y hy
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  have hy1 : |y - x| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  simpa [abs_sub_comm] using hy1

/-- **Local smooth curve from split data**:  if the reduced map `red`
(collinear on its zero set near `p`, by `hident`) is smooth, vanishes at `p`
and is a submersion along the second factor of the split (invertibility of
the partial derivative `if₂`), then the off-diagonal collinearity zero set
near `p` is the image of an injective `C¹` curve through `p`. -/
theorem trisecantLocalCurve_of_splitData
    {r : ℝ → Space} (h : IsSmoothKnot r)
    (p : RealParamTriple)
    (hColl : collinearityMap r p = 0) (hOff : p ∈ RealOffDiagonalTriples r)
    (A : ℝ × (ℝ × ℝ) → RealParamTriple) (B : RealParamTriple → ℝ × (ℝ × ℝ))
    (hAcd : ContDiff ℝ ⊤ A) (hBcont : Continuous B)
    (hAB : ∀ z, B (A z) = z) (hBA : ∀ q, A (B q) = q)
    (u : ℝ × (ℝ × ℝ)) (hu : A u = p)
    (red : RealParamTriple → ℝ × ℝ)
    (hCdA : ContDiff ℝ 1 (red ∘ A))
    (hred0 : red p = (0, 0))
    (hred_of_collinear : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0))
    (if₂ : ((fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)).IsInvertible)
    (hident : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0) :
    TrisecantLocalCurve r p := by
  rcases hident with ⟨Uid, hUido, hUidp, hUid⟩
  -- ψ from the product-domain implicit function theorem
  rcases Commons.Analysis.Calculus.Implicit.implicitFunction_graph
    (u := u) (f := red ∘ A)
    (cdf := ContDiff.contDiffAt (n := 1) hCdA)
    (h0 := by
      change red (A u) = (0, 0)
      rw [hu]
      exact hred0)
    (if₂ := if₂) with ⟨ψ, hψu, hψV, hcover⟩
  rcases hψV with ⟨V, hVV, hψcd, hψval⟩
  -- the covering neighbourhood W, in open form
  have hWex : ∃ W : Set (ℝ × (ℝ × ℝ)), IsOpen W ∧ u ∈ W ∧
      ∀ v ∈ W, (red ∘ A) v = (0, 0) → ψ v.1 = v.2 := by
    rcases hcover.exists_mem with ⟨W₀, hW₀u, hW₀⟩
    rcases mem_nhds_iff.mp hW₀u with ⟨W, hWsub, hWopen, hWu⟩
    refine ⟨W, hWopen, hWu, ?_⟩
    intro v hv
    exact hW₀ v (hWsub hv)
  rcases hWex with ⟨W, hWopen, hWu, hW⟩
  -- ψ is C¹ at u.1 (hence continuous), since V is a neighbourhood of u.1
  have hψcdAt : ContDiffAt ℝ 1 ψ u.1 := ContDiffOn.contDiffAt hψcd hVV
  have hψcontAt : ContinuousAt ψ u.1 := hψcdAt.continuousAt
  have hpathcont : ContinuousAt (fun x : ℝ => (x, ψ x)) u.1 := by
    have hfw : ContinuousWithinAt (fun x : ℝ => x) Set.univ u.1 :=
      (continuousAt_id (x := u.1)).continuousWithinAt
    have hgw : ContinuousWithinAt ψ Set.univ u.1 :=
      (continuousWithinAt_univ ψ u.1).mpr hψcontAt
    exact (continuousWithinAt_univ (fun x : ℝ => (x, ψ x)) u.1).mp
      (ContinuousWithinAt.prodMk hfw hgw)
  -- the open set of good curve values
  let Uoff : Set RealParamTriple := RealOffDiagonalTriples r
  have hUoffo : IsOpen Uoff := isOpen_RealOffDiagonalTriples h
  let G : Set RealParamTriple := Uid ∩ Uoff
  have hGo : IsOpen G := hUido.inter hUoffo
  have hGp : p ∈ G := ⟨hUidp, hOff⟩
  -- small intervals around u.1 on which (x,ψx) ∈ W, A(x,ψx) ∈ G, and x ∈ V
  have hS1 : ∃ a b : ℝ, a < u.1 ∧ u.1 < b ∧ ∀ x ∈ Set.Ioo a b, (x, ψ x) ∈ W := by
    rcases exists_Ioo_subset_of_mem_nhds (hpathcont.preimage_mem_nhds
        (hWopen.mem_nhds (by simpa [hψu] using hWu)))
      with ⟨a, b, ha, hb, hab⟩
    refine ⟨a, b, ha, hb, ?_⟩
    intro x hx
    exact hab hx
  rcases hS1 with ⟨a1, b1, ha1, hb1, hS1⟩
  have hS2 : ∃ a b : ℝ, a < u.1 ∧ u.1 < b ∧
      ∀ x ∈ Set.Ioo a b, A (x, ψ x) ∈ G := by
    have hAcontAt : ContinuousAt (fun x : ℝ => A (x, ψ x)) u.1 :=
      (hAcd.continuous.continuousAt.comp hpathcont)
    rcases exists_Ioo_subset_of_mem_nhds (hAcontAt.preimage_mem_nhds
        (hGo.mem_nhds (by simpa [hψu, hu] using hGp)))
      with ⟨a, b, ha, hb, hab⟩
    refine ⟨a, b, ha, hb, ?_⟩
    intro x hx
    exact hab hx
  rcases hS2 with ⟨a2, b2, ha2, hb2, hS2⟩
  have hS0 : ∃ a b : ℝ, a < u.1 ∧ u.1 < b ∧ Set.Ioo a b ⊆ V := exists_Ioo_subset_of_mem_nhds hVV
  rcases hS0 with ⟨a0, b0, ha0, hb0, hS0⟩
  -- pick an interval inside all three
  let a : ℝ := max a0 (max a1 a2)
  let b : ℝ := min b0 (min b1 b2)
  have ha : a < u.1 := by
    dsimp [a]
    exact max_lt ha0 (max_lt ha1 ha2)
  have hb : u.1 < b := by
    dsimp [b]
    exact lt_min hb0 (lt_min hb1 hb2)
  have hIab : ∀ x ∈ Set.Ioo a b,
      x ∈ V ∧ (x, ψ x) ∈ W ∧ A (x, ψ x) ∈ G := by
    intro x hx
    have hxa0 : x ∈ Set.Ioo a0 b0 := by
      constructor
      · exact lt_of_le_of_lt (le_max_left a0 (max a1 a2)) hx.1
      · exact lt_of_lt_of_le hx.2 (min_le_left b0 (min b1 b2))
    have hxa1 : x ∈ Set.Ioo a1 b1 := by
      constructor
      · exact lt_of_le_of_lt (le_trans (le_max_left a1 a2) (le_max_right a0 (max a1 a2))) hx.1
      · exact lt_of_lt_of_le hx.2 (le_trans (min_le_right b0 (min b1 b2)) (min_le_left b1 b2))
    have hxa2 : x ∈ Set.Ioo a2 b2 := by
      constructor
      · exact lt_of_le_of_lt (le_trans (le_max_right a1 a2) (le_max_right a0 (max a1 a2))) hx.1
      · exact lt_of_lt_of_le hx.2 (le_trans (min_le_right b0 (min b1 b2)) (min_le_right b1 b2))
    exact ⟨hS0 hxa0, hS1 x hxa1, hS2 x hxa2⟩

  -- final parameters of the curve
  let lo : ℝ := a - u.1
  let hi : ℝ := b - u.1
  have hlo : lo < 0 := by dsimp [lo]; linarith
  have hhi : 0 < hi := by dsimp [hi]; linarith
  let γ0 : ℝ → RealParamTriple := fun x => A (x, ψ x)
  let γ : ℝ → RealParamTriple := fun t => γ0 (u.1 + t)
  -- the final neighbourhood
  let U : Set RealParamTriple :=
    {q | (B q).1 ∈ Set.Ioo a b} ∩ (G ∩ (B ⁻¹' W))
  have hUo : IsOpen U := by
    dsimp [U]
    have hBfst : Continuous (fun q : RealParamTriple => (B q).1) := continuous_fst.comp hBcont
    exact (isOpen_Ioo.preimage hBfst).inter (hGo.inter (hWopen.preimage hBcont))
  have hUp : p ∈ U := by
    dsimp [U]
    constructor
    · have hBp : (B p).1 = u.1 := by
        calc (B p).1 = (B (A u)).1 := by rw [← hu]
          _ = u.1 := by simp [hAB]
      change (B p).1 ∈ Set.Ioo a b
      rw [hBp]
      exact ⟨ha, hb⟩
    · exact ⟨⟨hUidp, hOff⟩, by simpa [hAB, ← hu] using hWu⟩
  -- curve values: membership, collinearity, off-diagonal
  have hγmem : ∀ t ∈ Set.Ioo lo hi,
      γ t ∈ U ∧ collinearityMap r (γ t) = 0 ∧ γ t ∈ RealOffDiagonalTriples r := by
    intro t ht
    let x : ℝ := u.1 + t
    have hxI : x ∈ Set.Ioo a b := by
      dsimp [x]
      constructor <;> linarith [ht.1, ht.2]
    have hxV : x ∈ V := (hIab x hxI).1
    have hxW : (x, ψ x) ∈ W := (hIab x hxI).2.1
    have hxG : A (x, ψ x) ∈ G := (hIab x hxI).2.2
    have hredγ : red (γ t) = (0, 0) := by
      dsimp [γ, γ0, x]
      exact hψval x hxV
    have hcollγ : collinearityMap r (γ t) = 0 := by
      exact hUid (γ t) hxG.1 hredγ
    have hUmem : γ t ∈ U := by
      change (B (γ t)).1 ∈ Set.Ioo a b ∧ γ t ∈ G ∧ B (γ t) ∈ W
      constructor
      · have hBγ : B (γ t) = (u.1 + t, ψ (u.1 + t)) := by
          dsimp [γ, γ0]
          exact hAB (u.1 + t, ψ (u.1 + t))
        rw [hBγ]
        simpa [x] using hxI
      · constructor
        · simpa [γ, γ0, x] using hxG
        · have hBγ : B (γ t) = (u.1 + t, ψ (u.1 + t)) := by
            dsimp [γ, γ0]
            exact hAB (u.1 + t, ψ (u.1 + t))
          rw [hBγ]
          simpa [x] using hxW
    exact ⟨hUmem, hcollγ, hUmem.2.1.2⟩
  -- covering
  have hcover2 : ∀ q ∈ U, collinearityMap r q = 0 → q ∈ RealOffDiagonalTriples r →
      ∃ t ∈ Set.Ioo lo hi, γ t = q := by
    intro q hqU hcl hqoff
    have hredq : red q = (0, 0) := hred_of_collinear q hcl
    let v : ℝ × (ℝ × ℝ) := B q
    have hvfR : (red ∘ A) v = (0, 0) := by
      dsimp [v]
      rw [hBA]
      exact hredq
    have hvW : v ∈ W := hqU.2.2
    have hψv : ψ v.1 = v.2 := hW v hvW hvfR
    have hvI : v.1 ∈ Set.Ioo a b := hqU.1
    let t : ℝ := v.1 - u.1
    have ht : t ∈ Set.Ioo lo hi := by
      dsimp [t, lo, hi]
      constructor <;> linarith [hvI.1, hvI.2]
    refine ⟨t, ht, ?_⟩
    dsimp [γ, γ0, t, v]
    have hsum : u.1 + ((B q).1 - u.1) = (B q).1 := by ring
    rw [hsum, hψv]
    exact hBA q
  refine ⟨hColl, hOff, U, hUo, hUp, lo, hi, hlo, hhi, γ, ?_, ?_, ?_, ?_, hcover2⟩
  · -- ContDiffOn ℝ 1 γ (Ioo lo hi)
    have hγcd : ContDiffOn ℝ 1 γ (Set.Ioo lo hi) := by
      have hshift : ContDiffOn ℝ 1 (fun t : ℝ => u.1 + t) (Set.Ioo lo hi) := by
        fun_prop
      have hψon : ContDiffOn ℝ 1 ψ (Set.Ioo a b) := by
        refine hψcd.mono ?_
        intro x hx
        exact hS0 ⟨lt_of_le_of_lt (le_max_left a0 (max a1 a2)) hx.1,
          lt_of_lt_of_le hx.2 (min_le_left b0 (min b1 b2))⟩
      have hψsh : ContDiffOn ℝ 1 (fun t : ℝ => ψ (u.1 + t)) (Set.Ioo lo hi) :=
        ContDiffOn.comp hψon hshift (by
          intro t ht
          constructor <;> linarith [ht.1, ht.2])
      have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (u.1 + t, ψ (u.1 + t))) (Set.Ioo lo hi) :=
        hshift.prodMk hψsh
      have hA1 : ContDiff ℝ 1 A := ContDiff.of_le hAcd le_top
      have hcomp2 : ContDiffOn ℝ 1 (fun t : ℝ => A (u.1 + t, ψ (u.1 + t))) (Set.Ioo lo hi) := by
        change ContDiffOn ℝ 1 (A ∘ (fun t : ℝ => (u.1 + t, ψ (u.1 + t)))) (Set.Ioo lo hi)
        exact ContDiff.comp_contDiffOn (g := A) (n := 1) hA1 hpair
      exact hcomp2
    exact hγcd
  · -- injective on (lo,hi)
    intro t1 ht1 t2 ht2 hEq
    have hBγ1 : B (γ t1) = (u.1 + t1, ψ (u.1 + t1)) := by
      dsimp [γ, γ0]
      exact hAB (u.1 + t1, ψ (u.1 + t1))
    have hBγ2 : B (γ t2) = (u.1 + t2, ψ (u.1 + t2)) := by
      dsimp [γ, γ0]
      exact hAB (u.1 + t2, ψ (u.1 + t2))
    have hEq' : (u.1 + t1, ψ (u.1 + t1)) = (u.1 + t2, ψ (u.1 + t2)) := by
      simpa [hBγ1, hBγ2] using congrArg B hEq
    have hfirst : u.1 + t1 = u.1 + t2 := congrArg Prod.fst hEq'
    linarith
  · -- γ 0 = p
    dsimp [γ, γ0]
    rw [add_zero]
    rw [hψu]
    rw [hu]
  · -- values of γ in U, collinear and off-diagonal
    intro t ht
    exact hγmem t ht

/-! ### The three general-position pairs

`LocalSmoothCurveTheorem` calls for a local curve at *any* general-position
triple, where the rank-two witness (`PartialRankTwo`) may name any two of
the three hinge partials.  Each witness pair `(i,j)` admits its own split of
the parameter cube (the remaining coordinate is the curve parameter, the
two witnessed coordinates form the second factor), and this section
instantiates `trisecantLocalCurve_of_splitData` for each of the three
unordered pairs. -/

section CasePairs

-- (A,B): graph over the `m` coordinate; second factor the `(a,b)` plane.
/-- Split for the pair `(A,B)`: `E₁` is the `m`-coordinate, `E₂` the
`(a,b)`-plane: `(t,(x,y)) ↦ (x,(y,t))`. -/
def splitAB : ℝ × (ℝ × ℝ) → RealParamTriple := fun z => (z.2.1, (z.2.2, z.1))
/-- The inverse split of `splitAB`. -/
def unSplitAB : RealParamTriple → ℝ × (ℝ × ℝ) := fun q => (q.2.2, (q.1, q.2.1))

lemma splitAB_contDiff : ContDiff ℝ ⊤ splitAB := by
  unfold splitAB
  fun_prop

lemma unSplitAB_continuous : Continuous unSplitAB := by
  unfold unSplitAB
  fun_prop

lemma unSplitAB_splitAB (z : ℝ × (ℝ × ℝ)) : unSplitAB (splitAB z) = z := by
  ext <;> simp [splitAB, unSplitAB]

lemma splitAB_unSplitAB (q : RealParamTriple) : splitAB (unSplitAB q) = q := by
  ext <;> simp [splitAB, unSplitAB]

/-- **The (A,B) local-curve instance**: if the `a`- and `b`-hinge partials
are the independent pair at a collinear off-diagonal triple, then the
off-diagonal zero set of `Φ` near the triple is an injective `C¹` curve
(graph over the `m`-coordinate). -/
theorem localSmoothCurve_AB {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    TrisecantLocalCurve r (a, (b, m)) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitAB
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitAB
  let u : ℝ × (ℝ × ℝ) := (m, (a, b))
  let red : RealParamTriple → ℝ × ℝ := pairReduced r a b m (0 : Fin 3) (1 : Fin 3)
  have hColl : collinearityMap r p = 0 := by
    dsimp [p]
    exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitAB]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (0 : Fin 3) (1 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hCdA : ContDiff ℝ 1 (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ 1 (fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (1 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (1 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitAB_contDiff le_top)
  -- the partial derivative along the second factor is the Gram matrix
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := hCdA.differentiable_one u
  have hcdR : DifferentiableAt ℝ red (a, (b, m)) :=
    (ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (1 : Fin 3)) le_top).differentiable_one (a, (b, m))
  have hcol1 : D (1, 0) = (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
      inner ℝ (collPartialA r a b m) (collPartialB r a b m)) := by
    dsimp [D]
    have hline : HasDerivAt (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) 0 :=
      fderiv_along_axis_eq_deriv (H := red ∘ A) (p := u) (e := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) hcdAat
    have hpath : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
        fun s : ℝ => red (a + s, (b, m)) := by
      funext s
      change red (A ((m, (a, b)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a + s, (b, m))
      congr 1
      dsimp [A, u, splitAB]
      simp
    have hg' : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) 0 := by
      rw [hpath] at hline
      exact hline
    have hlineR : HasDerivAt (fun s : ℝ => red ((a, (b, m)) + s • axisVec (0 : Fin 3)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3))) 0 :=
      fderiv_along_axis_eq_deriv (H := red) (p := (a, (b, m))) (e := axisVec (0 : Fin 3)) hcdR
    have hpathR : (fun s : ℝ => red (a + s, (b, m))) = fun s : ℝ => red ((a, (b, m)) + s • axisVec (0 : Fin 3)) := by
      funext s
      congr 1
      dsimp [axisVec]
      ext <;> simp
    have hlineR' : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3))) 0 := by
      rw [← hpathR] at hlineR
      exact hlineR
    have huniq := HasDerivAt.unique hlineR' hg'
    have hcol : (fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3)) =
        (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
          inner ℝ (collPartialA r a b m) (collPartialB r a b m)) := by
      dsimp [red]
      simpa [collPartial_eq_A, collPartial_eq_B] using
        (fderiv_pairReduced_axis h a b m (0 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    rw [hcol] at huniq
    simpa [ContinuousLinearMap.comp_apply] using huniq.symm
  have hcol2 : D (0, 1) = (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
      inner ℝ (collPartialB r a b m) (collPartialB r a b m)) := by
    dsimp [D]
    have hline : HasDerivAt (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) 0 :=
      fderiv_along_axis_eq_deriv (H := red ∘ A) (p := u) (e := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) hcdAat
    have hpath : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
        fun s : ℝ => red (a, (b + s, m)) := by
      funext s
      change red (A ((m, (a, b)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b + s, m))
      congr 1
      dsimp [A, u, splitAB]
      simp
    have hg' : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) 0 := by
      rw [hpath] at hline
      exact hline
    have hlineR : HasDerivAt (fun s : ℝ => red ((a, (b, m)) + s • axisVec (1 : Fin 3)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3))) 0 :=
      fderiv_along_axis_eq_deriv (H := red) (p := (a, (b, m))) (e := axisVec (1 : Fin 3)) hcdR
    have hpathR : (fun s : ℝ => red (a, (b + s, m))) = fun s : ℝ => red ((a, (b, m)) + s • axisVec (1 : Fin 3)) := by
      funext s
      congr 1
      dsimp [axisVec]
      ext <;> simp
    have hlineR' : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3))) 0 := by
      rw [← hpathR] at hlineR
      exact hlineR
    have huniq := HasDerivAt.unique hlineR' hg'
    have hcol : (fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3)) =
        (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
          inner ℝ (collPartialB r a b m) (collPartialB r a b m)) := by
      dsimp [red]
      simpa [collPartial_eq_A, collPartial_eq_B] using
        (fderiv_pairReduced_axis h a b m (1 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    rw [hcol] at huniq
    simpa [ContinuousLinearMap.comp_apply] using huniq.symm
  -- invertibility of the partial derivative: Gram determinant is nonzero
  have hgram : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialB r a b m);
        inner ℝ (collPartialB r a b m) (collPartialA r a b m),
        inner ℝ (collPartialB r a b m) (collPartialB r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D) (c₁₁ := inner ℝ (collPartialA r a b m) (collPartialA r a b m))
      (c₁₂ := inner ℝ (collPartialA r a b m) (collPartialB r a b m))
      (c₂₁ := inner ℝ (collPartialB r a b m) (collPartialA r a b m))
      (c₂₂ := inner ℝ (collPartialB r a b m) (collPartialB r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
              inner ℝ (collPartialA r a b m) (collPartialB r a b m);
              inner ℝ (collPartialB r a b m) (collPartialA r a b m),
              inner ℝ (collPartialB r a b m) (collPartialB r a b m)])
            = (inner ℝ (collPartialA r a b m) (collPartialA r a b m)) *
                (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) -
              (inner ℝ (collPartialA r a b m) (collPartialB r a b m)) *
                (inner ℝ (collPartialB r a b m) (collPartialA r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  -- identification of the zero sets
  have hidentAB : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (0 : Fin 3) (1 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_A, collPartial_eq_B] using hLI))
  exact trisecantLocalCurve_of_splitData (r := r) h p hColl hOff A B splitAB_contDiff
    unSplitAB_continuous unSplitAB_splitAB splitAB_unSplitAB u hu red hCdA hred0 hredColl if₂ hidentAB


/-! ### Factorised column helpers for the pair instances -/

/-- If the split path through the second factor direction `d` equals the
concrete triple path `path`, and the latter has derivative `col` along `red`,
then the partial derivative of `red ∘ A` in the direction `d` equals `col`. -/
lemma split_col_helper {red : RealParamTriple → ℝ × ℝ} {A : ℝ × (ℝ × ℝ) → RealParamTriple}
    {u : ℝ × (ℝ × ℝ)} {d : ℝ × ℝ} {path : ℝ → RealParamTriple} {col : ℝ × ℝ}
    (hcdA : DifferentiableAt ℝ (red ∘ A) u)
    (hpath : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), d))) = fun s : ℝ => red (path s))
    (hderv : HasDerivAt (fun s : ℝ => red (path s)) col 0) :
    ((fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)) d = col := by
  have hline : HasDerivAt (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), d)))
      ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), d)) 0 :=
    fderiv_along_axis_eq_deriv (H := red ∘ A) (p := u) (e := ((0 : ℝ), d)) hcdA
  have hline' : HasDerivAt (fun s : ℝ => red (path s))
      ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), d)) 0 := by
    rw [hpath] at hline
    exact hline
  have huniq := HasDerivAt.unique hderv hline'
  have hval : (fderiv ℝ (red ∘ A) u) ((0 : ℝ), d) = col := huniq.symm
  simpa [ContinuousLinearMap.comp_apply] using hval

/-- The derivative of `red` along the parameter axis of index `k` (the axis
path through `p0`) is the Gram column of the pair, i.e. the value of the
axis lemma at index `k`. -/
lemma axis_path_col {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ) (i j k : Fin 3)
    (red : RealParamTriple → ℝ × ℝ) (hred : red = fun q : RealParamTriple => pairReduced r a b m i j q)
    (p0 : RealParamTriple) (hp0 : p0 = (a, (b, m)))
    (path : ℝ → RealParamTriple)
    (hpath : path = fun s : ℝ => p0 + s • axisVec k) :
    HasDerivAt (fun s : ℝ => red (path s))
      (inner ℝ (collPartial r a b m k) (collPartial r a b m i),
        inner ℝ (collPartial r a b m k) (collPartial r a b m j)) 0 := by
  have hcdR : DifferentiableAt ℝ red p0 := by
    rw [hred, hp0]
    exact (ContDiff.of_le (contDiff_pairReduced h a b m i j) le_top).differentiable_one (a, (b, m))
  have hlineR : HasDerivAt (fun s : ℝ => red (p0 + s • axisVec k))
      ((fderiv ℝ red p0) (axisVec k)) 0 :=
    fderiv_along_axis_eq_deriv (H := red) (p := p0) (e := axisVec k) hcdR
  have hlineR' : HasDerivAt (fun s : ℝ => red (path s))
      ((fderiv ℝ red p0) (axisVec k)) 0 := by
    rw [hpath]
    exact hlineR
  have hcol : (fderiv ℝ red p0) (axisVec k) =
      (inner ℝ (collPartial r a b m k) (collPartial r a b m i),
        inner ℝ (collPartial r a b m k) (collPartial r a b m j)) := by
    rw [hred, hp0]
    exact fderiv_pairReduced_axis h a b m k i j
  rw [hcol] at hlineR'
  exact hlineR'

-- (A,M): graph over the `b` coordinate; second factor the `(a,m)` plane.
/-- Split for the pair `(A,M)`: `E₁` is the `b`-coordinate, `E₂` the
`(a,m)`-plane: `(t,(x,y)) ↦ (x,(t,y))`. -/
def splitAM : ℝ × (ℝ × ℝ) → RealParamTriple := fun z => (z.2.1, (z.1, z.2.2))
/-- The inverse split of `splitAM`. -/
def unSplitAM : RealParamTriple → ℝ × (ℝ × ℝ) := fun q => (q.2.1, (q.1, q.2.2))

lemma splitAM_contDiff : ContDiff ℝ ⊤ splitAM := by
  unfold splitAM
  fun_prop

lemma unSplitAM_continuous : Continuous unSplitAM := by
  unfold unSplitAM
  fun_prop

lemma unSplitAM_splitAM (z : ℝ × (ℝ × ℝ)) : unSplitAM (splitAM z) = z := by
  ext <;> simp [splitAM, unSplitAM]

lemma splitAM_unSplitAM (q : RealParamTriple) : splitAM (unSplitAM q) = q := by
  ext <;> simp [splitAM, unSplitAM]

/-- **The (A,M) local-curve instance**. -/
theorem localSmoothCurve_AM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialM r a b m]) :
    TrisecantLocalCurve r (a, (b, m)) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitAM
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitAM
  let u : ℝ × (ℝ × ℝ) := (b, (a, m))
  let red : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q
  have hColl : collinearityMap r p = 0 := by dsimp [p]; exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitAM]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (0 : Fin 3) (2 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hred : red = fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q := rfl
  have hp0 : (a, (b, m)) = (a, (b, m)) := rfl
  have hCdA : ContDiff ℝ 1 (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ 1 (fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (2 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitAM_contDiff le_top)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := hCdA.differentiable_one u
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hpath1 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
      fun s : ℝ => red (a + s, (b, m)) := by
    funext s
    change red (A ((b, (a, m)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a + s, (b, m))
    congr 1
    dsimp [A, u, splitAM]
    simp
  have hd1 : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
      (inner ℝ (collPartial r a b m (0 : Fin 3)) (collPartial r a b m (0 : Fin 3)),
        inner ℝ (collPartial r a b m (0 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a + s, (b, m))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol1 : D (1, 0) = (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
      inner ℝ (collPartialA r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((1 : ℝ), (0 : ℝ)))
      (path := fun s : ℝ => (a + s, (b, m))) (col := (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialM r a b m))) hcdAat hpath1
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hd1)
    simpa using hc
  have hpath2 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
      fun s : ℝ => red (a, (b, m + s)) := by
    funext s
    change red (A ((b, (a, m)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b, m + s))
    congr 1
    dsimp [A, u, splitAM]
    simp
  have hd2 : HasDerivAt (fun s : ℝ => red (a, (b, m + s)))
      (inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (0 : Fin 3)),
        inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (0 : Fin 3) (2 : Fin 3) (2 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b, m + s))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol2 : D (0, 1) = (inner ℝ (collPartialM r a b m) (collPartialA r a b m),
      inner ℝ (collPartialM r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((0 : ℝ), (1 : ℝ)))
      (path := fun s : ℝ => (a, (b, m + s))) (col := (inner ℝ (collPartialM r a b m) (collPartialA r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m))) hcdAat hpath2
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hd2)
    simpa using hc
  have hgram : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialM r a b m);
        inner ℝ (collPartialM r a b m) (collPartialA r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D)
      (c₁₁ := inner ℝ (collPartialA r a b m) (collPartialA r a b m))
      (c₁₂ := inner ℝ (collPartialA r a b m) (collPartialM r a b m))
      (c₂₁ := inner ℝ (collPartialM r a b m) (collPartialA r a b m))
      (c₂₂ := inner ℝ (collPartialM r a b m) (collPartialM r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
              inner ℝ (collPartialA r a b m) (collPartialM r a b m);
              inner ℝ (collPartialM r a b m) (collPartialA r a b m),
              inner ℝ (collPartialM r a b m) (collPartialM r a b m)])
            = (inner ℝ (collPartialA r a b m) (collPartialA r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
              (inner ℝ (collPartialA r a b m) (collPartialM r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialA r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  have hidentAM : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (0 : Fin 3) (2 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hLI))
  exact trisecantLocalCurve_of_splitData (r := r) h p hColl hOff A B splitAM_contDiff
    unSplitAM_continuous unSplitAM_splitAM splitAM_unSplitAM u hu red hCdA hred0 hredColl if₂ hidentAM

-- (B,M): graph over the `a` coordinate; second factor the `(b,m)` plane
-- (the identity split).
/-- Split for the pair `(B,M)` (identity split: `E₁` is the `a`-coordinate,
`E₂` the `(b,m)`-plane). -/
def splitBM : ℝ × (ℝ × ℝ) → RealParamTriple := fun z => z
/-- The inverse split of `splitBM`. -/
def unSplitBM : RealParamTriple → ℝ × (ℝ × ℝ) := fun q => q

lemma splitBM_contDiff : ContDiff ℝ ⊤ splitBM := by
  unfold splitBM
  fun_prop

lemma unSplitBM_continuous : Continuous unSplitBM := by
  unfold unSplitBM
  fun_prop

lemma unSplitBM_splitBM (z : ℝ × (ℝ × ℝ)) : unSplitBM (splitBM z) = z := rfl

lemma splitBM_unSplitBM (q : RealParamTriple) : splitBM (unSplitBM q) = q := rfl

/-- **The (B,M) local-curve instance**. -/
theorem localSmoothCurve_BM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialB r a b m, collPartialM r a b m]) :
    TrisecantLocalCurve r (a, (b, m)) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitBM
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitBM
  let u : ℝ × (ℝ × ℝ) := (a, (b, m))
  let red : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q
  have hColl : collinearityMap r p = 0 := by dsimp [p]; exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitBM]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (1 : Fin 3) (2 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hred : red = fun q : RealParamTriple => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q := rfl
  have hCdA : ContDiff ℝ 1 (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ 1 (fun q : RealParamTriple => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (1 : Fin 3) (2 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitBM_contDiff le_top)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := hCdA.differentiable_one u
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hpath1 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
      fun s : ℝ => red (a, (b + s, m)) := by
    funext s
    change red (A ((a, (b, m)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a, (b + s, m))
    congr 1
    dsimp [A, u, splitBM]
    simp
  have hd1 : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
      (inner ℝ (collPartial r a b m (1 : Fin 3)) (collPartial r a b m (1 : Fin 3)),
        inner ℝ (collPartial r a b m (1 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (1 : Fin 3) (2 : Fin 3) (1 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b + s, m))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol1 : D (1, 0) = (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
      inner ℝ (collPartialB r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((1 : ℝ), (0 : ℝ)))
      (path := fun s : ℝ => (a, (b + s, m))) (col := (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
        inner ℝ (collPartialB r a b m) (collPartialM r a b m))) hcdAat hpath1
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hd1)
    simpa using hc
  have hpath2 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
      fun s : ℝ => red (a, (b, m + s)) := by
    funext s
    change red (A ((a, (b, m)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b, m + s))
    congr 1
    dsimp [A, u, splitBM]
    simp
  have hd2 : HasDerivAt (fun s : ℝ => red (a, (b, m + s)))
      (inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (1 : Fin 3)),
        inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (1 : Fin 3) (2 : Fin 3) (2 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b, m + s))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol2 : D (0, 1) = (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
      inner ℝ (collPartialM r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((0 : ℝ), (1 : ℝ)))
      (path := fun s : ℝ => (a, (b, m + s))) (col := (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m))) hcdAat hpath2
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hd2)
    simpa using hc
  have hgram : (Matrix.det !![inner ℝ (collPartialB r a b m) (collPartialB r a b m),
        inner ℝ (collPartialB r a b m) (collPartialM r a b m);
        inner ℝ (collPartialM r a b m) (collPartialB r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D)
      (c₁₁ := inner ℝ (collPartialB r a b m) (collPartialB r a b m))
      (c₁₂ := inner ℝ (collPartialB r a b m) (collPartialM r a b m))
      (c₂₁ := inner ℝ (collPartialM r a b m) (collPartialB r a b m))
      (c₂₂ := inner ℝ (collPartialM r a b m) (collPartialM r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialB r a b m) (collPartialB r a b m),
              inner ℝ (collPartialB r a b m) (collPartialM r a b m);
              inner ℝ (collPartialM r a b m) (collPartialB r a b m),
              inner ℝ (collPartialM r a b m) (collPartialM r a b m)])
            = (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
              (inner ℝ (collPartialB r a b m) (collPartialM r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialB r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  have hidentBM : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (1 : Fin 3) (2 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hLI))
  exact trisecantLocalCurve_of_splitData (r := r) h p hColl hOff A B splitBM_contDiff
    unSplitBM_continuous unSplitBM_splitBM splitBM_unSplitBM u hu red hCdA hred0 hredColl if₂ hidentBM

/-- In `ℝ³` a pair of vectors is independent independently of their order. -/
lemma linearIndependent_pair_swap_iff (x y : Space) :
    LinearIndependent ℝ ![y, x] ↔ LinearIndependent ℝ ![x, y] := by
  rw [← cross3_ne_zero_iff_linearIndependent_local]
  rw [← cross3_ne_zero_iff_linearIndependent_local]
  constructor
  · intro h
    rw [cross3_anticomm x y] at h
    simpa using h
  · intro h
    rw [cross3_anticomm x y]
    simpa using h

/-- **Milestone 1 (`LocalSmoothCurveTheorem`)**:  at every general-position
collinear off-diagonal triple of a smooth knot, the off-diagonal zero set of
the collinearity map `Φ` has, locally at the triple, the structure of an
injective `C¹` curve through the triple.  The rank-two witness pair
(`PartialRankTwo`) is analysed over its six orderings: the diagonal
orderings are contradictory, and each off-diagonal ordering is the local
curve instance of the corresponding pair (`localSmoothCurve_AB`,
`localSmoothCurve_AM`, `localSmoothCurve_BM`; reversed orderings are
handled by `linearIndependent_pair_swap_iff`). -/
theorem smooth_local_curve_of_general_position (r : ℝ → Space) (h : IsSmoothKnot r) :
    LocalSmoothCurveTheorem r := by
  intro a b m hGP hΦ
  rcases hGP with ⟨hZ, hW, hmb, hP⟩
  rcases hP with ⟨i, j, hij, hLIij⟩
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact localSmoothCurve_AB h a b m hΦ hZ hW hmb
      (by simpa [collPartial_eq_A, collPartial_eq_B] using hLIij)
  · exact localSmoothCurve_AM h a b m hΦ hZ hW hmb
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hLIij)
  · exact localSmoothCurve_AB h a b m hΦ hZ hW hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialA r a b m) (collPartialB r a b m)).mp ?_
        · simpa [collPartial_eq_A, collPartial_eq_B] using hsw
        · simpa [collPartial_eq_A, collPartial_eq_B] using hLIij)
  · exact False.elim (hij rfl)
  · exact localSmoothCurve_BM h a b m hΦ hZ hW hmb
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hLIij)
  · exact localSmoothCurve_AM h a b m hΦ hZ hW hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialA r a b m) (collPartialM r a b m)).mp ?_
        · simpa [collPartial_eq_A, collPartial_eq_M] using hsw
        · simpa [collPartial_eq_A, collPartial_eq_M] using hLIij)
  · exact localSmoothCurve_BM h a b m hΦ hZ hW hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialB r a b m) (collPartialM r a b m)).mp ?_
        · simpa [collPartial_eq_B, collPartial_eq_M] using hsw
        · simpa [collPartial_eq_B, collPartial_eq_M] using hLIij)
  · exact False.elim (hij rfl)
