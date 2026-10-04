import Mathlib
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.EXT.laplAt_curvNormK_eq
import Submission.Work.Diff.EXT.evolK_bridges
import Submission.Work.Diff.EXT.evolCompK_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Kato (Weitzenböck) identity for `|∇Rm|²`

`Work.Diff.GE.laplAt_dRmNormSq_eq` is reduced to the *general* Kato identity for `|∇^k Rm|²`
(`Work.Diff.EXT.laplAt_curvNormK_eq`, proved in the `Ext`-tower vocabulary) at `k = 1`:

* the left-hand side is `laplAt g (curvNormK g · 1)`, by the frame-independence bridge
  `Work.Diff.EXT.curvNormK_one_eq_dRmNormSq` and locality of `laplAt` in the germ of the function;
* the first term is the level-2 squared norm `curvNormK g x 2`, identified with the sum of the
  squares of the `cov2Rm`-components by the bridge below (the level-2 companion of the proved
  identities `ckt_one_eq_covRm` / `ckt_three_eq_cov3Rm`), together with a reindexing of the sums;
* the second term is converted with the proved bridges `Work.Diff.EXT.sum_fin_one_arrow`,
  `Work.Diff.EXT.covKRm_one` and `Work.Diff.EXT.lapCovKRm_one_eq`, whose right-hand side unfolds to
  `Work.Diff.GE.lapCovRmAt = ∑ m, cov³Rm g x (onFrame m) (onFrame m) ·`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-! ## 1. Locality of `laplAt` -/

/-- `laplAt g · x` only depends on the germ of the function at `x`. -/
private theorem laplAt_congr_of_eventuallyEq_kato (g : SMet I M) {u v : M → ℝ} (x : M)
    (h : u =ᶠ[𝓝 x] v) : laplAt g u x = laplAt g v x := by
  have hmem : {z : M | u z = v z} ∈ 𝓝 x := h
  have hx : x ∈ interior {z : M | u z = v z} := mem_interior_iff_mem_nhds.mpr hmem
  have hinner : ∀ w : TangentSpace I x,
      (fun y : M ↦ mvfderiv I u y (smoothExt x w y))
        =ᶠ[𝓝 x] (fun y : M ↦ mvfderiv I v y (smoothExt x w y)) := by
    intro w
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [mvfderiv_congr_eventuallyEq (I := I)
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)]
  simp only [laplAt, hessAt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mvfderiv_congr_eventuallyEq (I := I) (hinner (onFrame g x i)),
      mvfderiv_congr_eventuallyEq (I := I) h]

/-! ## 2. The level-2 tower bridge -/

/-- **The tower value `∇²Rm` is the `(0,6)`-tensor `∇²Rm` on the values of the fields.**  For smooth
fields `V 0, V 1, A, B, C, D` the `Ext`-tower component `covKRmExt g 2 V A B C D` at `x` equals
`cov2Rm g x (V 0 x) (V 1 x) (A x) (B x) (C x) (D x)`.  Companion of the proved level-1 and level-3
identifications `ckt_one_eq_covRm`, `ckt_two_eq_cov2Rm` and `ckt_three_eq_cov3Rm`: combine
`ckt_mkT_eq` (`covKRmExt g k V B = ckt g k (mkT V B)`) with `ckt_two_eq_cov2Rm` and the value
computations `mkT_castAdd`, `mkT_natAdd`. -/
private theorem kato_covKRmExt_two_eq_cov2Rm (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (V : Fin 2 → (Π y : M, TangentSpace I y)) (A B C D : Π y : M, TangentSpace I y)
    (hV : ∀ i, CMDiff ∞ (T% (V i))) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    Work.Diff.EXT.covKRmExt g 2 V A B C D x
      = Work.Diff.GE.cov2Rm g x (V 0 x) (V 1 x) (A x) (B x) (C x) (D x) := by
  have hG : ∀ i : Fin 6, CMDiff ∞
      (T% ((Work.Diff.EXT.mkT V (rmPQuad A B C D)) i)) := by
    intro i
    refine Fin.addCases (motive := fun i => CMDiff ∞
      (T% ((Work.Diff.EXT.mkT V (rmPQuad A B C D)) i))) ?_ ?_ i
    · intro j
      rw [Work.Diff.EXT.mkT_castAdd]
      exact hV j
    · intro p
      rw [Work.Diff.EXT.mkT_natAdd]
      exact rmPQuad_smooth hA hB hC hD p
  rw [show Work.Diff.EXT.covKRmExt g 2 V A B C D x
        = Work.Diff.EXT.ckt g 2 (Work.Diff.EXT.mkT V (rmPQuad A B C D)) x from
      (Work.Diff.EXT.ckt_mkT_eq g 2 V (rmPQuad A B C D) x).symm]
  rw [Work.Diff.EXT.ckt_two_eq_cov2Rm hLC g (Work.Diff.EXT.mkT V (rmPQuad A B C D)) hG x,
    show Work.Diff.EXT.mkT V (rmPQuad A B C D) 0 = V 0 from by
      rw [show (0 : Fin 6) = Fin.castAdd 4 (0 : Fin 2) from rfl, Work.Diff.EXT.mkT_castAdd],
    show Work.Diff.EXT.mkT V (rmPQuad A B C D) 1 = V 1 from by
      rw [show (1 : Fin 6) = Fin.castAdd 4 (1 : Fin 2) from rfl, Work.Diff.EXT.mkT_castAdd],
    show Work.Diff.EXT.mkT V (rmPQuad A B C D) 2 = A from by
      rw [show (2 : Fin 6) = Fin.natAdd 2 (0 : Fin 4) from rfl, Work.Diff.EXT.mkT_natAdd,
        rmPQuad_zero],
    show Work.Diff.EXT.mkT V (rmPQuad A B C D) 3 = B from by
      rw [show (3 : Fin 6) = Fin.natAdd 2 (1 : Fin 4) from rfl, Work.Diff.EXT.mkT_natAdd,
        rmPQuad_one],
    show Work.Diff.EXT.mkT V (rmPQuad A B C D) 4 = C from by
      rw [show (4 : Fin 6) = Fin.natAdd 2 (2 : Fin 4) from rfl, Work.Diff.EXT.mkT_natAdd,
        rmPQuad_two],
    show Work.Diff.EXT.mkT V (rmPQuad A B C D) 5 = D from by
      rw [show (5 : Fin 6) = Fin.natAdd 2 (3 : Fin 4) from rfl, Work.Diff.EXT.mkT_natAdd,
        rmPQuad_three]]

/-! ## 3. A reindexing of the six frame indices -/

/-- A sum over the function type `Fin 2 → Fin n` followed by four further sums is the same as the sum
over all six indices nested in the order `(m, v, a, b, c, d)`. -/
private theorem sum_twoArrow_reindex {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ ι : Fin 2 → Fin n, ∑ i, ∑ j, ∑ l, ∑ m, F (ι 0) (ι 1) i j l m)
      = ∑ m, ∑ v, ∑ a, ∑ b, ∑ c, ∑ d, F m v a b c d := by
  let e₂ : (Fin 2 → Fin n) ≃ Fin n × Fin n :=
    { toFun := fun ι => (ι 0, ι 1)
      invFun := fun p => ![p.1, p.2]
      left_inv := by
        intro ι
        funext i
        fin_cases i <;> rfl
      right_inv := by
        intro p
        exact Prod.ext rfl rfl }
  rw [Fintype.sum_equiv e₂
      (fun ι : Fin 2 → Fin n => ∑ i, ∑ j, ∑ l, ∑ m, F (ι 0) (ι 1) i j l m)
      (fun p : Fin n × Fin n => ∑ i, ∑ j, ∑ l, ∑ m, F p.1 p.2 i j l m)
      (fun ι => rfl)]
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n =>
    ∑ i, ∑ j, ∑ l, ∑ m, F p.1 p.2 i j l m)]

/-! ## 4. The level-2 squared norm in the `GE` vocabulary -/

/-- **`|∇²Rm|²` in the `GE` vocabulary.**  The `Ext`-tower squared norm `curvNormK g x 2` of `∇²Rm`
equals the sum of the squares of the `cov2Rm`-components in the orthonormal frame `onFrame g x`, the
six derivative/curvature slots being ordered `(m, v, a, b, c, d)`.  Level-2 companion of the proved
`Work.Diff.EXT.curvNormK_one_eq_dRmNormSq`. -/
private theorem curvNormK_two_eq_sum_cov2Rm_aux (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    Work.Diff.EXT.curvNormK g x 2
      = ∑ m, ∑ v, ∑ a, ∑ b, ∑ c, ∑ d,
          (Work.Diff.GE.cov2Rm g x (onFrame g x m) (onFrame g x v) (onFrame g x a)
            (onFrame g x b) (onFrame g x c) (onFrame g x d)) ^ 2 := by
  -- each tower component at level `2` is `cov2Rm` on the values
  have hcov : ∀ (ι : Fin 2 → Fin (Module.finrank ℝ E)) (i j l m : Fin (Module.finrank ℝ E)),
      Work.Diff.EXT.covKRm g x 2 (fun s => onFrame g x (ι s)) (onFrame g x i)
          (onFrame g x j) (onFrame g x l) (onFrame g x m)
        = Work.Diff.GE.cov2Rm g x (onFrame g x (ι 0)) (onFrame g x (ι 1)) (onFrame g x i)
            (onFrame g x j) (onFrame g x l) (onFrame g x m) := by
    intro ι i j l m
    rw [show Work.Diff.EXT.covKRm g x 2 (fun s => onFrame g x (ι s)) (onFrame g x i)
          (onFrame g x j) (onFrame g x l) (onFrame g x m)
        = Work.Diff.EXT.covKRmExt g 2 (fun s => smoothExt x (onFrame g x (ι s)))
            (smoothExt x (onFrame g x i)) (smoothExt x (onFrame g x j))
            (smoothExt x (onFrame g x l)) (smoothExt x (onFrame g x m)) x from rfl,
      kato_covKRmExt_two_eq_cov2Rm hLC g x _
        (smoothExt x (onFrame g x i)) (smoothExt x (onFrame g x j))
        (smoothExt x (onFrame g x l)) (smoothExt x (onFrame g x m))
        (fun s => smoothExt_cmdiff x _) (smoothExt_cmdiff x _) (smoothExt_cmdiff x _)
        (smoothExt_cmdiff x _) (smoothExt_cmdiff x _)]
    simp only [smoothExt_apply]
  have hL : Work.Diff.EXT.curvNormK g x 2
      = ∑ ι : Fin 2 → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
          (Work.Diff.GE.cov2Rm g x (onFrame g x (ι 0)) (onFrame g x (ι 1)) (onFrame g x i)
            (onFrame g x j) (onFrame g x l) (onFrame g x m)) ^ 2 := by
    rw [Work.Diff.EXT.curvNormK_eq_sum_covKRm]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hcov ι i j l m]
  rw [hL, sum_twoArrow_reindex (fun m v a b c d =>
    (Work.Diff.GE.cov2Rm g x (onFrame g x m) (onFrame g x v) (onFrame g x a)
      (onFrame g x b) (onFrame g x c) (onFrame g x d)) ^ 2)]

/-! ## 5. The main computation -/

/-- **The Kato (Weitzenböck) identity for `|∇Rm|²`.**  For a smooth metric `g` and a point `x`,
the Laplacian of the squared norm of the `(0,5)`-tensor `T = ∇Rm` is the sum of the squared norm of
`∇T` and the pairing of `T` with its rough Laplacian:

`Δ|T|² = 2 |∇T|² + 2 ⟨T, ΔT⟩`,

both sides evaluated in the orthonormal frame `onFrame g x`.  Since `|∇T|² ≥ 0`, this gives the
Kato inequality `Δ|T|² ≥ 2 ⟨T, ΔT⟩` used in the assembly of
`Work.Diff.GE.evol_drm_normsq`. -/
theorem laplAt_dRmNormSq_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) {g : SMet I M} (x : M) :
    laplAt g (dRmNormSq g) x
      = 2 * (∑ m, ∑ v, ∑ a, ∑ b, ∑ c, ∑ d,
              (Work.Diff.GE.cov2Rm g x (onFrame g x m) (onFrame g x v) (onFrame g x a)
                (onFrame g x b) (onFrame g x c) (onFrame g x d)) ^ 2)
        + 2 * (∑ v, ∑ a, ∑ b, ∑ c, ∑ d,
              covRm g x (onFrame g x v) (onFrame g x a) (onFrame g x b) (onFrame g x c)
                (onFrame g x d)
              * (∑ m, Work.Diff.GE.cov3Rm g x (onFrame g x m) (onFrame g x m) (onFrame g x v)
                  (onFrame g x a) (onFrame g x b) (onFrame g x c) (onFrame g x d))) := by
  classical
  -- `|∇Rm|²` is the `k = 1` tower norm `curvNormK g · 1`.
  have hev : dRmNormSq g =ᶠ[𝓝 x] (fun y : M ↦ Work.Diff.EXT.curvNormK g y 1) :=
    Filter.Eventually.of_forall fun y => (Work.Diff.EXT.curvNormK_one_eq_dRmNormSq g y).symm
  rw [laplAt_congr_of_eventuallyEq_kato g x hev]
  -- the general Kato identity at `k = 1`
  rw [Work.Diff.EXT.laplAt_curvNormK_eq (I := I) (M := M) g x 1 (by norm_num)]
  -- the level-2 squared norm in the `GE` vocabulary
  rw [show Work.Diff.EXT.curvNormK g x (1 + 1) = Work.Diff.EXT.curvNormK g x 2 from rfl,
    curvNormK_two_eq_sum_cov2Rm_aux hLC g x]
  -- the second sum in the `GE` vocabulary
  rw [Work.Diff.EXT.sum_fin_one_arrow]
  simp only [Work.Diff.EXT.covKRm_one, Work.Diff.EXT.lapCovKRm_one_eq, Work.Diff.GE.lapCovRmAt]

end Work.Diff.GE
