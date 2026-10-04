import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.curvNormK_frame_indep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The evaluation bound for `∇^k Rm`

`Work.Diff.EXT.curvNormK g x k` is the squared norm `|∇^k Rm|²` of the `k`-th covariant derivative
of the curvature, computed as the sum of the squares of the components of `∇^k Rm` in the
orthonormal frame `onFrame g x`.  This file proves the matching *evaluation bound*: the value of
`∇^k Rm` at `x` on `k + 4` tangent vectors is bounded by the square root of that Frobenius norm
times the product of the Euclidean norms of the vectors.

The proof has four inputs.

* `Kpt g x k` (`Submission/Work/Diff/EXT/curvNormK_frame_indep.lean`) is the pointwise value of
  `∇^k Rm` at `x`, and `KptLin hLC g x k` is the `ℝ`-multilinear form with that evaluation map
  (`Kpt_add`, `Kpt_smul`).  Hence the goal is a statement about a `MultilinearMap`, and the
  tensoriality of the tower (which is what makes the value depend only on the vectors and not on the
  `Classical.epsilon`-chosen smooth extensions) is exactly the statement that this map exists.

* `multilinear_frame_bound` (below) is the Hilbert–Schmidt bound `‖T‖ ≤ ‖T‖_Frobenius` for a
  multilinear form, in terms of an orthonormal frame.

* `sum_fin_add_four` reindexes `∑_{w : Fin (k+4) → Fin n}` as the nested sum over
  `ι : Fin k → Fin n` and the four curvature indices, which identifies the Frobenius norm with
  `curvNormK g x k`.

* `Fin.prod_univ_add` splits the product of the norms into the `k` derivative vectors and the four
  curvature vectors.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Expansion in an orthonormal frame -/

/-- **Expansion in an orthonormal family of full cardinality**: `v = ∑ i, ⟪e i, v⟫ • e i`. -/
theorem sum_inner_smul_eq_self_orthonormal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : Fin (Module.finrank ℝ V) → V) (he : Orthonormal ℝ e) (hpos : 0 < Module.finrank ℝ V)
    (v : V) : ∑ i, inner ℝ (e i) v • e i = v := by
  haveI : Nonempty (Fin (Module.finrank ℝ V)) := ⟨⟨0, hpos⟩⟩
  let b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V :=
    basisOfOrthonormalOfCardEqFinrank he (by rw [Fintype.card_fin])
  have hb : (b : Fin (Module.finrank ℝ V) → V) = e :=
    coe_basisOfOrthonormalOfCardEqFinrank he _
  have honb : Orthonormal ℝ (b : Fin (Module.finrank ℝ V) → V) := by rw [hb]; exact he
  have h := (b.toOrthonormalBasis honb).sum_repr' v
  have hco : (b.toOrthonormalBasis honb : Fin (Module.finrank ℝ V) → V) = e := by
    rw [Module.Basis.coe_toOrthonormalBasis]; exact hb
  rw [hco] at h
  exact h

/-- **Parseval's identity** for an orthonormal family of full cardinality:
`⟪v, v⟫ = ∑ i, ⟪e i, v⟫ ^ 2`. -/
theorem sum_sq_inner_eq_inner_self
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : Fin (Module.finrank ℝ V) → V) (he : Orthonormal ℝ e) (hpos : 0 < Module.finrank ℝ V)
    (v : V) : (∑ i, (inner ℝ (e i) v) ^ 2) = inner ℝ v v := by
  have h := he.inner_sum (fun i => inner ℝ (e i) v) (fun i => inner ℝ (e i) v) Finset.univ
  simp only [sum_inner_smul_eq_self_orthonormal e he hpos v] at h
  have h3 : (∑ i : Fin (Module.finrank ℝ V),
        starRingEnd ℝ (inner ℝ (e i) v) * inner ℝ (e i) v)
      = ∑ i, (inner ℝ (e i) v) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_two]
    simp only [starRingEnd_apply, star_trivial]
  rw [h3] at h
  exact h.symm

/-! ## The Hilbert–Schmidt bound for a multilinear form -/

/-- **Hilbert–Schmidt (Frobenius) bound for a multilinear form.**  For a multilinear form `T` on a
finite-dimensional real inner product space and an orthonormal family `e` of full cardinality, the
absolute value of `T` at any point is bounded by the square root of the sum of the squares of the
values of `T` on `e`-tuples, times the product of the norms of the arguments. -/
theorem multilinear_frame_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [CompleteSpace V] {N : ℕ} (hN : 0 < N)
    (T : MultilinearMap ℝ (fun _ : Fin N => V) ℝ)
    (e : Fin (Module.finrank ℝ V) → V) (he : Orthonormal ℝ e) (p : Fin N → V) :
    |T p| ≤ Real.sqrt (∑ w : Fin N → Fin (Module.finrank ℝ V), (T (fun s => e (w s))) ^ 2)
      * ∏ s : Fin N, Real.sqrt (inner ℝ (p s) (p s)) := by
  classical
  by_cases hpos : 0 < Module.finrank ℝ V
  · -- the main case: expand in the frame and apply Cauchy–Schwarz
    have hexp : ∀ s : Fin N, ∑ i, inner ℝ (e i) (p s) • e i = p s := fun s =>
      sum_inner_smul_eq_self_orthonormal e he hpos (p s)
    have hparseval : ∀ s : Fin N, (∑ i, (inner ℝ (e i) (p s)) ^ 2) = inner ℝ (p s) (p s) :=
      fun s => sum_sq_inner_eq_inner_self e he hpos (p s)
    have hinner_nonneg : ∀ s : Fin N, (0 : ℝ) ≤ inner ℝ (p s) (p s) := by
      intro s
      rw [← hparseval s]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    -- multilinearity expansion
    have hTp : T p = ∑ w : Fin N → Fin (Module.finrank ℝ V),
        (∏ s, inner ℝ (e (w s)) (p s)) * T (fun s => e (w s)) := by
      have hp' : p = fun s => ∑ i, inner ℝ (e i) (p s) • e i := by
        funext s; exact (hexp s).symm
      conv_lhs => rw [hp']
      rw [MultilinearMap.map_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [MultilinearMap.map_smul_univ]
      simp only [smul_eq_mul]
    -- Cauchy–Schwarz over the tuples
    have hCS : (∑ w : Fin N → Fin (Module.finrank ℝ V),
          (∏ s, inner ℝ (e (w s)) (p s)) * (T (fun s => e (w s)))) ^ 2
        ≤ (∑ w : Fin N → Fin (Module.finrank ℝ V),
              (∏ s, inner ℝ (e (w s)) (p s)) ^ 2)
          * (∑ w : Fin N → Fin (Module.finrank ℝ V), (T (fun s => e (w s))) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    -- the second factor
    have hfactor : (∑ w : Fin N → Fin (Module.finrank ℝ V),
          (∏ s, inner ℝ (e (w s)) (p s)) ^ 2)
        = ∏ s : Fin N, inner ℝ (p s) (p s) := by
      calc (∑ w : Fin N → Fin (Module.finrank ℝ V), (∏ s, inner ℝ (e (w s)) (p s)) ^ 2)
          = ∑ w : Fin N → Fin (Module.finrank ℝ V),
              ∏ s, (inner ℝ (e (w s)) (p s)) ^ 2 := by
            refine Finset.sum_congr rfl (fun w _ => ?_)
            exact (Finset.prod_pow Finset.univ 2 (fun s => inner ℝ (e (w s)) (p s))).symm
        _ = ∏ s : Fin N, ∑ i, (inner ℝ (e i) (p s)) ^ 2 := by
            rw [Finset.prod_univ_sum
                (t := fun _ : Fin N => (Finset.univ : Finset (Fin (Module.finrank ℝ V))))
                (f := fun s i => (inner ℝ (e i) (p s)) ^ 2), Fintype.piFinset_univ]
        _ = ∏ s : Fin N, inner ℝ (p s) (p s) :=
            Finset.prod_congr rfl (fun s _ => hparseval s)
    -- conclude
    have hprod_nonneg : (0 : ℝ) ≤ ∏ s : Fin N, inner ℝ (p s) (p s) :=
      Finset.prod_nonneg (fun s _ => hinner_nonneg s)
    have hb : |T p| ≤ Real.sqrt ((∏ s : Fin N, inner ℝ (p s) (p s))
        * (∑ w : Fin N → Fin (Module.finrank ℝ V), (T (fun s => e (w s))) ^ 2)) := by
      rw [hTp]
      rw [← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt ?_
      rw [← hfactor]
      exact hCS
    rw [Real.sqrt_mul hprod_nonneg,
      Real.sqrt_prod Finset.univ (fun s _ => hinner_nonneg s),
      mul_comm (∏ s : Fin N, Real.sqrt (inner ℝ (p s) (p s)))
        (Real.sqrt (∑ w : Fin N → Fin (Module.finrank ℝ V), (T (fun s => e (w s))) ^ 2))] at hb
    exact hb
  · -- the degenerate case: `V` is a subsingleton
    have hf0 : Module.finrank ℝ V = 0 := Nat.eq_zero_of_not_pos hpos
    have hzero : ∀ x : V, x = 0 := by
      intro x
      obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff (R := ℝ) (M := V)).mp hf0 x
      rcases smul_eq_zero.mp hax with h' | h'
      · exact absurd h' ha
      · exact h'
    haveI : Subsingleton V := ⟨fun x y => by rw [hzero x, hzero y]⟩
    have hp0 : p = 0 := Subsingleton.elim p 0
    have hT0 : T p = 0 := by
      rw [hp0]
      have h := T.map_update_smul (m := (0 : Fin N → V)) (i := ⟨0, hN⟩) (c := (0 : ℝ))
        (x := (0 : V))
      have e1 : Function.update (0 : Fin N → V) (⟨0, hN⟩ : Fin N) ((0 : ℝ) • (0 : V))
          = (0 : Fin N → V) := by
        funext i; simp [Function.update_apply]
      have e2 : Function.update (0 : Fin N → V) (⟨0, hN⟩ : Fin N) (0 : V)
          = (0 : Fin N → V) := by
        funext i; simp [Function.update_apply]
      rw [e1, e2] at h
      simpa using h
    have hprod0 : ∏ s : Fin N, Real.sqrt (inner ℝ (p s) (p s)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ (⟨0, hN⟩ : Fin N)) ?_
      rw [hzero (p _), inner_zero_right, Real.sqrt_zero]
    rw [hT0, abs_zero, hprod0, mul_zero]

/-! ## The pointwise value of `∇^k Rm` as `Kpt` -/

/-- `covKRm` is `Kpt` on the packed tuple `Fin.append v ![a,b,c,d]`. -/
theorem covKRm_eq_Kpt (g : SMet I M) (x : M) (k : ℕ) (v : Fin k → TangentSpace I x)
    (a b c d : TangentSpace I x) :
    covKRm g x k v a b c d = Kpt g x k (Fin.append v ![a, b, c, d]) := by
  rw [Kpt, ckt_eq_covKRmExt]
  simp only [Fin.append_left, Fin.append_right]
  rfl

/-- `covKRmC` is `Kpt` on the packed tuple. -/
theorem covKRmC_eq_Kpt (g : SMet I M) (x : M) (k : ℕ)
    (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (ι : Fin k → Fin (Module.finrank ℝ E)) (i j l m : Fin (Module.finrank ℝ E)) :
    covKRmC g x f k ι i j l m = Kpt g x k (fun s => f (Fin.append ι ![i, j, l, m] s)) := by
  rw [Kpt, ckt_eq_covKRmExt]
  simp only [Fin.append_left, Fin.append_right]
  rfl

/-- The Frobenius norm of `∇^k Rm` in the frame `onFrame g x` is `curvNormK g x k`. -/
theorem Kpt_component_sum (g : SMet I M) (x : M) (k : ℕ) :
    (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        (Kpt g x k (fun s => onFrame g x (w s))) ^ 2) = curvNormK g x k := by
  rw [curvNormK_eq_sum_covKRm]
  rw [sum_fin_add_four (fun w => (Kpt g x k (fun s => onFrame g x (w s))) ^ 2)]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← covKRmC_eq_Kpt, covKRmC_eq_covKRm]

/-! ## The target -/

theorem covKRmExt_eval_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : Submission.Diff.SMet I M) (x : M) (v : Fin k → TangentSpace I x)
        (a b c d : TangentSpace I x),
        |Work.Diff.EXT.covKRmExt g k (fun i => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) (Submission.Diff.smoothExt x d) x|
          ≤ C * (1 + Real.sqrt (Work.Diff.EXT.curvNormK g x k))
              * (Finset.univ.prod (fun i : Fin k => Real.sqrt (g.inner x (v i) (v i)))
                 * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
                 * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by
  intro k
  refine ⟨1, zero_le_one, ?_⟩
  intro g x v a b c d
  rw [show covKRmExt g k (fun i => smoothExt x (v i)) (smoothExt x a) (smoothExt x b)
        (smoothExt x c) (smoothExt x d) x = Kpt g x k (Fin.append v ![a, b, c, d]) from
      covKRm_eq_Kpt g x k v a b c d]
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hone : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (onFrame g x i) (onFrame g x j)
        = g.inner x (onFrame g x i) (onFrame g x j) from rfl]
    exact Work.Diff.GE.isONFrame_onFrame g x i j
  have hb := multilinear_frame_bound (N := k + 4) (by omega) (KptLin hLC g x k)
    (onFrame g x) hone (Fin.append v ![a, b, c, d])
  have hb2 : |Kpt g x k (Fin.append v ![a, b, c, d])| ≤
      Real.sqrt (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
          (Kpt g x k (fun s => onFrame g x (w s))) ^ 2)
        * ∏ s : Fin (k + 4), Real.sqrt (inner ℝ ((Fin.append v ![a, b, c, d]) s)
            ((Fin.append v ![a, b, c, d]) s)) := hb
  rw [Kpt_component_sum g x k] at hb2
  have hprod : (∏ s : Fin (k + 4), Real.sqrt (inner ℝ ((Fin.append v ![a, b, c, d]) s)
        ((Fin.append v ![a, b, c, d]) s)))
      = (∏ i : Fin k, Real.sqrt (g.inner x (v i) (v i))) * Real.sqrt (g.inner x a a)
        * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) := by
    rw [Fin.prod_univ_add]
    have hFirst : (∏ i : Fin k, Real.sqrt (inner ℝ ((Fin.append v ![a, b, c, d])
          (Fin.castAdd 4 i)) ((Fin.append v ![a, b, c, d]) (Fin.castAdd 4 i))))
        = ∏ i : Fin k, Real.sqrt (g.inner x (v i) (v i)) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Fin.append_left]
      rfl
    have hLast : (∏ j : Fin 4, Real.sqrt (inner ℝ ((Fin.append v ![a, b, c, d])
          (Fin.natAdd k j)) ((Fin.append v ![a, b, c, d]) (Fin.natAdd k j))))
        = Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
          * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) := by
      rw [Fin.prod_univ_four]
      simp only [Fin.append_right]
      rfl
    rw [hFirst, hLast]
    ring
  rw [hprod] at hb2
  have hP : 0 ≤ (∏ i : Fin k, Real.sqrt (g.inner x (v i) (v i))) * Real.sqrt (g.inner x a a)
      * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine hb2.trans ?_
  have h1 : Real.sqrt (curvNormK g x k) ≤ 1 + Real.sqrt (curvNormK g x k) := by
    linarith [Real.sqrt_nonneg (curvNormK g x k)]
  calc Real.sqrt (curvNormK g x k)
        * ((∏ i : Fin k, Real.sqrt (g.inner x (v i) (v i))) * Real.sqrt (g.inner x a a)
          * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d))
      ≤ (1 + Real.sqrt (curvNormK g x k))
        * ((∏ i : Fin k, Real.sqrt (g.inner x (v i) (v i))) * Real.sqrt (g.inner x a a)
          * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) :=
        mul_le_mul_of_nonneg_right h1 hP
    _ = 1 * (1 + Real.sqrt (curvNormK g x k))
        * ((∏ i : Fin k, Real.sqrt (g.inner x (v i) (v i))) * Real.sqrt (g.inner x a a)
          * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by
        ring

end Work.Diff.EXT
