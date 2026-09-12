import Mathlib
import Submission.GeometryOfNumbers.WedgeBlocks
import Submission.Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank
import Submission.Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq



/-!
# E1(b) for general pure tensors (coordinate model, Lemma 1(b) in full generality)

For a `k`-plane `V = span(range u)` in `RD d` with `V ∩ x₀ᗮ = ⊥` (equivalently, the
block-0 component of the pure tensor `ιMulti u` is nonzero), the distance
`planeResidual V x₀` from `V` to the coordinate plane `x₀ = modelX ℓ` is at most the block
ratio `‖block₁(ιMulti u)‖ / ‖block₀(ιMulti u)‖`.

Structure:
- projection layer: `projMap x` (the orthogonal projection onto `x` as a plain linear map),
  `ker_projMap` (`ker = xᗮ`), `projMap_mem`, `inj_restrict_projMap` (injectivity from
  `V ⊓ xᗮ = ⊥`), `finrank_map_projMap` (the projected plane still has dimension `k`);
- `exists_graph_rep`: the plane `V` admits an orthonormal graph representation
  `e + coff` over its projection: `e ⊆ x₀` orthonormal, `coff ⊆ x₀ᗮ`,
  `span(range (e + coff)) = span(range u)` (i.e. `V = graphSubspace e coff`);
- `planeResidual_pureTensor_le_blockRatio` (**E1(b)-general**): the block-ratio bound for the
  given generator `u`, assembled from the ON-graph bound (`planeResidual_graph_le_blockRatio`,
  WedgeBlocks) via proportionality of the two generators (`iMulti_proportional_of_span_eq`,
  commons) and the resulting invariance of the block ratio under nonzero scalar multiples.

All results here are Mathlib-only (besides the Submission geometry modules WedgeBlocks /
DiagonalFlow / ONGraph which are themselves Mathlib-only).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.Bridge.ONGraph

namespace Submission.WedgeGeneralE1

variable {d : ℕ}

/-- `x.starProjection v = 0` iff `v` is orthogonal to `x` (concrete E-valued form). -/
lemma starProjection_eq_zero_iff_orthogonal (x : Submodule ℝ (RD d)) (v : RD d) :
    x.starProjection v = 0 ↔ v ∈ xᗮ := by
  constructor
  · intro h
    have hproj : x.orthogonalProjectionOnto v = 0 := by
      apply Subtype.ext
      have hc : ((x.orthogonalProjectionOnto v : x) : RD d) = x.starProjection v := by
        rw [Submodule.coe_orthogonalProjectionOnto_apply]
      simpa [h] using hc
    exact (Submodule.orthogonalProjectionOnto_eq_zero_iff (v := v)).mp hproj
  · intro hv
    have hproj : x.orthogonalProjectionOnto v = 0 :=
      (Submodule.orthogonalProjectionOnto_eq_zero_iff (v := v)).mpr hv
    rw [← Submodule.coe_orthogonalProjectionOnto_apply]
    rw [hproj]
    simp

/-- The orthogonal projection onto `x`, as a plain linear endomorphism of `E`. -/
def projMap (x : Submodule ℝ (RD d)) : RD d →ₗ[ℝ] RD d where
  toFun := fun v => x.starProjection v
  map_add' := by intro a b; simp [map_add]
  map_smul' := by intro a b; simp [map_smul]

@[simp] lemma projMap_apply (x : Submodule ℝ (RD d)) (v : RD d) :
    projMap x v = x.starProjection v := rfl

/-- Kernel of the orthogonal projection onto `x` is `xᗮ`. -/
lemma ker_projMap (x : Submodule ℝ (RD d)) :
    LinearMap.ker (projMap x) = xᗮ := by
  ext v
  rw [LinearMap.mem_ker]
  exact starProjection_eq_zero_iff_orthogonal x v

/-- Every vector maps under the projection into `x`. -/
lemma projMap_mem (x : Submodule ℝ (RD d)) (v : RD d) : projMap x v ∈ x := by
  rw [projMap_apply]
  rw [← Submodule.coe_orthogonalProjectionOnto_apply]
  exact (x.orthogonalProjectionOnto v).2

/-- The orthogonal projection restricted to `V` is injective when `V ⊓ xᗮ = ⊥`. -/
lemma inj_restrict_projMap (x V : Submodule ℝ (RD d)) (hbot : V ⊓ xᗮ = ⊥) :
    Function.Injective (fun v : V => projMap x (v : RD d)) := by
  intro a b hab
  apply Subtype.ext
  have hz : projMap x ((a : RD d) - (b : RD d)) = 0 := by
    rw [map_sub]
    have hab' : projMap x (a : RD d) = projMap x (b : RD d) := by simpa using hab
    rw [hab', sub_self]
  have hker : (a : RD d) - (b : RD d) ∈ LinearMap.ker (projMap x) := LinearMap.mem_ker.mpr hz
  have horth : (a : RD d) - (b : RD d) ∈ xᗮ := by
    simpa [ker_projMap] using hker
  have hV : (a : RD d) - (b : RD d) ∈ V := V.sub_mem a.2 b.2
  have hmem : (a : RD d) - (b : RD d) ∈ V ⊓ xᗮ := Submodule.mem_inf.mpr ⟨hV, horth⟩
  have hzero : (a : RD d) - (b : RD d) = 0 := by
    rw [hbot] at hmem
    simpa [Submodule.mem_bot] using hmem
  exact sub_eq_zero.mp hzero

/-- The orthogonal projection of a `k`-dimensional `V` (a basis `u` with `V = span(range u)`)
with `V ⊓ xᗮ = ⊥` has dimension `k`. -/
lemma finrank_map_projMap {k : ℕ} (x : Submodule ℝ (RD d)) (u : Fin k → RD d)
    (hu : LinearIndependent ℝ u) (hbot : (Submodule.span ℝ (Set.range u)) ⊓ xᗮ = ⊥) :
    Module.finrank ℝ ((Submodule.span ℝ (Set.range u)).map (projMap x)) = k := by
  let V : Submodule ℝ (RD d) := Submodule.span ℝ (Set.range u)
  have hfinV : Module.finrank ℝ V = k := by
    simpa [V] using (finrank_span_eq_card (R := ℝ) hu)
  -- f : V →ₗ V.map (projMap x), bijective
  let f : V →ₗ[ℝ] V.map (projMap x) :=
    (projMap x).comp V.subtype |>.codRestrict (V.map (projMap x)) (by
      intro v
      exact Submodule.mem_map.mpr ⟨(v : RD d), v.2, rfl⟩)
  have hinj : Function.Injective f := by
    intro a b hab
    apply inj_restrict_projMap x V hbot
    -- (f a : RD d) = (f b : RD d)
    exact congrArg (fun w : V.map (projMap x) => (w : RD d)) hab
  have hsurj : Function.Surjective f := by
    intro w
    rcases (Submodule.mem_map.mp w.2) with ⟨c, hcV, hc⟩
    refine ⟨⟨c, hcV⟩, ?_⟩
    apply Subtype.ext
    exact hc
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  have heq : V ≃ₗ[ℝ] V.map (projMap x) := LinearEquiv.ofBijective f hbij
  calc
    Module.finrank ℝ ((Submodule.span ℝ (Set.range u)).map (projMap x))
        = Module.finrank ℝ (V.map (projMap x)) := by rfl
    _ = Module.finrank ℝ V := heq.finrank_eq.symm
    _ = k := hfinV

/-- **Graph extraction**: under `V ⊓ x₀ᗮ = ⊥`, the plane `V = span(range u)` admits an
orthonormal graph representation `e + coff` over its projection, with `e ⊆ x₀` ON and
`coff ⊆ x₀ᗮ`, spanning the same `V`. -/
lemma exists_graph_rep {k : ℕ} (ℓ : ℕ) (hk : 0 < k) (u : Fin k → RD d)
    (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (modelX ℓ)ᗮ = ⊥) :
    ∃ (e coff : Fin k → RD d),
      Orthonormal ℝ e ∧ (∀ j, e j ∈ modelX ℓ) ∧ (∀ j, coff j ∈ (modelX ℓ)ᗮ) ∧
      Submodule.span ℝ (Set.range (fun j => e j + coff j)) =
        Submodule.span ℝ (Set.range u) := by
  classical
  let x₀ : Submodule ℝ (RD d) := modelX ℓ
  let V : Submodule ℝ (RD d) := Submodule.span ℝ (Set.range u)
  let P : RD d →ₗ[ℝ] RD d := projMap x₀
  let W : Submodule ℝ (RD d) := V.map P
  have hfinW : Module.finrank ℝ W = k := by
    simpa [V, W, P, x₀] using (finrank_map_projMap (d := d) (k := k) x₀ u hu hbot)
  obtain ⟨e, he_ON, he_memW, he_span⟩ :=
    Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank W hfinW
  -- e j ∈ x₀ (since W = P(V) ⊆ x₀)
  have he_x0 : ∀ j, e j ∈ x₀ := by
    intro j
    have hw : e j ∈ V.map P := by
      change e j ∈ V.map P
      exact he_memW j
    rcases (Submodule.mem_map.mp hw) with ⟨a, haV, ha⟩
    rw [← ha]
    exact projMap_mem x₀ a
  -- preimages vpre j ∈ V with P (vpre j) = e j
  have hpre : ∀ j : Fin k, ∃ c : RD d, c ∈ V ∧ P c = e j := by
    intro j
    have hw : e j ∈ V.map P := by
      change e j ∈ V.map P
      exact he_memW j
    exact Submodule.mem_map.mp hw
  let vpre : Fin k → RD d := fun j => Classical.choose (hpre j)
  have vpre_mem : ∀ j, vpre j ∈ V := fun j => (Classical.choose_spec (hpre j)).1
  have vpre_map : ∀ j, P (vpre j) = e j := fun j => (Classical.choose_spec (hpre j)).2
  let coff : Fin k → RD d := fun j => vpre j - e j
  -- coff j ∈ x₀ᗮ
  have coff_orth : ∀ j, coff j ∈ x₀ᗮ := by
    intro j
    have hP : P (coff j) = 0 := by
      dsimp [coff]
      rw [map_sub]
      rw [vpre_map j]
      have hPe : P (e j) = e j := by
        dsimp [P]
        exact Submodule.starProjection_eq_self_iff.mpr (he_x0 j)
      rw [hPe, sub_self]
    have hker : coff j ∈ LinearMap.ker P := LinearMap.mem_ker.mpr hP
    simpa [P, ker_projMap] using hker
  -- pointwise identity e + coff = vpre and membership of the summands in V
  have hvv : ∀ j, e j + coff j = vpre j := by
    intro j
    dsimp [coff]
    abel
  have hec_mem : ∀ j, e j + coff j ∈ V := by
    intro j
    rw [hvv j]
    exact vpre_mem j
  have hPec : ∀ j, P (e j + coff j) = e j := by
    intro j
    rw [map_add]
    have hPe : P (e j) = e j := by
      dsimp [P]
      exact Submodule.starProjection_eq_self_iff.mpr (he_x0 j)
    have hPc : P (coff j) = 0 := by
      dsimp [coff]
      rw [map_sub]
      rw [vpre_map j]
      have hPe' : P (e j) = e j := by
        dsimp [P]
        exact Submodule.starProjection_eq_self_iff.mpr (he_x0 j)
      rw [hPe', sub_self]
    rw [hPe, hPc, add_zero]
  -- span (range (fun j => e j + coff j)) = V
  have hspan : Submodule.span ℝ (Set.range (fun j => e j + coff j)) = V := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro w hw
      rcases hw with ⟨j, rfl⟩
      simpa [hvv j] using vpre_mem j
    · intro v hv
      have hPvW : P v ∈ W := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      have hPvspan : P v ∈ Submodule.span ℝ (Set.range e) := by
        rw [he_span]
        exact hPvW
      rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := e)).mp hPvspan with ⟨a, ha⟩
      -- ha : ∑ a j • e j = P v
      let wfun : Fin k → RD d := fun j => e j + coff j
      have hsumV : (Finset.univ : Finset (Fin k)).sum (fun j => a j • wfun j) ∈ V := by
        exact V.sum_mem (fun j hj => V.smul_mem (a j) (hec_mem j))
      let s : RD d := (Finset.univ : Finset (Fin k)).sum (fun j => a j • wfun j)
      have hsubV : v - s ∈ V := V.sub_mem hv hsumV
      have hPs : P s = P v := by
        dsimp [s]
        calc
          P ((Finset.univ : Finset (Fin k)).sum (fun j => a j • wfun j))
              = (Finset.univ : Finset (Fin k)).sum (fun j => P (a j • wfun j)) := by
                rw [map_sum]
          _ = (Finset.univ : Finset (Fin k)).sum (fun j => a j • P (wfun j)) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [map_smul]
          _ = (Finset.univ : Finset (Fin k)).sum (fun j => a j • e j) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [hPec j]
          _ = P v := ha
      have hPt : P (v - s) = 0 := by
        rw [map_sub, hPs, sub_self]
      have hker : v - s ∈ LinearMap.ker P := LinearMap.mem_ker.mpr hPt
      have horth : v - s ∈ x₀ᗮ := by simpa [P, ker_projMap] using hker
      have hboth : v - s ∈ V ⊓ x₀ᗮ := Submodule.mem_inf.mpr ⟨hsubV, horth⟩
      have hz : v - s = 0 := by
        have hb : V ⊓ x₀ᗮ = ⊥ := by simpa [V, x₀] using hbot
        rw [hb] at hboth
        simpa [Submodule.mem_bot] using hboth
      have hvs : v = s := sub_eq_zero.mp hz
      rw [hvs]
      dsimp [s]
      exact (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := wfun)).mpr ⟨a, rfl⟩
  refine ⟨e, coff, he_ON, ?_, ?_, ?_⟩
  · intro j
    simpa [x₀] using he_x0 j
  · intro j
    simpa [x₀] using coff_orth j
  · simpa [V] using hspan

/-- **E1(b) for general pure tensors (coordinate model)**: for a `k`-plane
`V = span(range u)` with `V ∩ x₀ᗮ = ⊥` (equivalently block-0 of the wedge `ιMulti u` is
nonzero), the distance `planeResidual V x₀` is at most the block ratio
`‖block₁(ιMulti u)‖ / ‖block₀(ιMulti u)‖`. -/
theorem planeResidual_pureTensor_le_blockRatio {k : ℕ} (ℓ : ℕ) (hk : 0 < k)
    (u : Fin k → RD d) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (modelX ℓ)ᗮ = ⊥) :
    Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u)) (modelX ℓ) ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ := by
  classical
  obtain ⟨e, coff, he_ON, he_x0, hc_orth, hspan⟩ :=
    exists_graph_rep (d := d) (k := k) ℓ hk u hu hbot
  let w : Fin k → RD d := fun j => e j + coff j
  -- w is linearly independent (orthogonal projection onto x₀ sends w j to e j, e ON)
  let P : RD d →ₗ[ℝ] RD d := projMap (modelX ℓ)
  have hPe : ∀ j, P (e j) = e j := by
    intro j
    dsimp [P]
    exact Submodule.starProjection_eq_self_iff.mpr (he_x0 j)
  have hPc : ∀ j, P (coff j) = 0 := by
    intro j
    dsimp [P]
    exact (starProjection_eq_zero_iff_orthogonal (modelX ℓ) (coff j)).mpr (hc_orth j)
  have hPw : ∀ j, P (w j) = e j := by
    intro j
    dsimp [w]
    rw [map_add, hPe j, hPc j, add_zero]
  have heind : LinearIndependent ℝ e := he_ON.linearIndependent
  have hwind : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iffₛ] at heind ⊢
    intro f g hfg
    have hPf := congrArg P hfg
    have hfge : (Finset.univ : Finset (Fin k)).sum (fun j => f j • e j) =
        (Finset.univ : Finset (Fin k)).sum (fun j => g j • e j) := by
      simpa [map_sum, map_smul, hPw] using hPf
    exact heind f g hfge
  -- proportionality: ιMulti u = λ • ιMulti w, λ ≠ 0
  have hspan' : Submodule.span ℝ (Set.range u) = Submodule.span ℝ (Set.range w) := hspan.symm
  rcases Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq (𝕜 := ℝ) (M := RD d) u w hu hwind hspan' with
    ⟨lam, hlam0, hwedge⟩
  -- block-0 of the graph wedge is unit
  have hC0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k w) 0‖ = 1 := by
    dsimp [w]
    exact blockElem_zero_of_graph_norm_one (d := d) (k := k) (ℓ := ℓ) e coff he_ON he_x0 hc_orth hk
  -- scaled block norms
  have hA1 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ =
      |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k w) 1‖ := by
    have hb : blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1 =
        lam • blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k w) 1 := by
      rw [hwedge]
      rw [blockElem_smul]
    rw [hb]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
  have hA0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ =
      |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k w) 0‖ := by
    have hb : blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0 =
        lam • blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k w) 0 := by
      rw [hwedge]
      rw [blockElem_smul]
    rw [hb]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
  -- ratio invariance
  have hratio :
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ =
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k w) 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k w) 0‖ := by
    have ha0 : |lam| ≠ 0 := abs_ne_zero.mpr hlam0
    rw [hA1, hA0, hC0]
    field_simp [ha0]
  -- the graph bound
  have hg := planeResidual_graph_le_blockRatio (d := d) (k := k) (ℓ := ℓ)
    hk e coff he_ON he_x0 hc_orth
  have hgs : Submission.Bridge.ONGraph.graphSubspace e coff = Submodule.span ℝ (Set.range u) := by
    change Submodule.span ℝ (Set.range (fun j => e j + coff j)) = Submodule.span ℝ (Set.range u)
    exact hspan
  have hbound : Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
      (modelX ℓ) ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k w) 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k w) 0‖ := by
    rw [← hgs]
    dsimp [w]
    exact hg
  -- finish
  rw [hratio]
  exact hbound

/-- **Flow-cone ratio bound**: if the two-scale diagonal flow keeps block-0 of `w` as the
dominant component (`c * ‖a_t w‖ ≤ ‖block₀(a_t w)‖`), then the block ratio of the original
vector is at most `a / (c * b)` — the `a_t` eigenvalues are `a^(k-j) b^j`, so block-0 shrinks
like `a^k` while block-1 shrinks like `a^(k-1) b`; the cone condition forces
`‖w₁‖/‖w₀‖ ≤ (1/c)·(a/b)`. -/
lemma blockRatio_le_of_cone {d k : ℕ} (ℓ : ℕ) (hk : 0 < k) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (w : WK d k)
    (hw0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ≠ 0)
    (hcone : c * ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖ ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale a b ℓ)) w) 0‖) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ≤ a / (c * b) := by
  classical
  let aw : WK d k := exteriorPower.map k (scaleMap (twoScale a b ℓ)) w
  have hb0flow : ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ =
      a ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
    dsimp [aw]
    rw [norm_blockElem_map_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b) w
      (by omega : 0 ≤ k) (le_of_lt ha) (le_of_lt hb)]
    congr 1
    · simp
  have hb1flow : ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 1‖ =
      a ^ (k - 1) * b * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ := by
    dsimp [aw]
    rw [norm_blockElem_map_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b) w
      (by exact hk : 1 ≤ k) (le_of_lt ha) (le_of_lt hb)]
    congr 1
    ring
  have hle1 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 1‖ ≤ ‖aw‖ := by
    exact norm_blockElem_le_norm (d := d) (k := k) (ℓ := ℓ) aw (by exact hk : 1 ≤ k)
  -- chain: c * a^(k-1) * b * ‖w₁‖ ≤ a^k * ‖w₀‖
  have hmain : c * (a ^ (k - 1) * b) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ ≤
      a ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
    have hstep : c * ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 1‖ ≤
        a ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
      calc
        c * ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 1‖
            ≤ c * ‖aw‖ := by
              exact mul_le_mul_of_nonneg_left hle1 (le_of_lt hc)
        _ ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ := hcone
        _ = a ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := hb0flow
    rw [hb1flow] at hstep
    ring_nf at hstep ⊢
    exact hstep
  -- positivity
  have hB0pos : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
    exact lt_of_le_of_ne (norm_nonneg _) (by intro h; exact hw0 h.symm)
  -- divide: ‖w₁‖ ≤ (a^k * ‖w₀‖) / (c * a^(k-1) * b)
  have hpos : 0 < c * a ^ (k - 1) * b :=
    mul_pos (mul_pos hc (pow_pos ha _)) hb
  have hmain' : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ ≤
      (a ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖) / (c * a ^ (k - 1) * b) := by
    exact (le_div_iff₀ hpos).mpr (by
      ring_nf at hmain ⊢
      exact hmain)
  -- a^k / (c a^{k-1} b) = a / (c b)
  have hnum : (a ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖) /
        (c * a ^ (k - 1) * b) = (a / (c * b)) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
    have hkm1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
    field_simp [ha.ne', hb.ne', hc.ne']
    rw [← pow_succ, hkm1]
  -- ‖w₁‖ ≤ (a/(c*b)) * ‖w₀‖, then divide by ‖w₀‖
  have hfin : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ ≤
      (a / (c * b)) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
    rw [hnum] at hmain'
    exact hmain'
  exact (div_le_iff₀ hB0pos).mpr hfin

end Submission.WedgeGeneralE1
