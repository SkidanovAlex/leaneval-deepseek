import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.aCovArr_eq_covKAExt
import Submission.Work.Diff.EXT.covKAExt_frame_eq_smoothExt
import Submission.Work.Diff.EXT.christoffel_bounds_of_core
import Submission.Work.Diff.EXT.gram_data_bounds_v2
import Submission.Work.Diff.EXT.ConnCov.inner_coeff_expansion
import Submission.Work.Diff.EXT.ConnCov.inner_coeff_bound
import Submission.Work.Diff.EXT.ConnCov.aCovArr_compact_bound
import Submission.Work.Diff.EXT.ConnCov.multilinear_expansion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `t`-wise (local) bound for the `∇^{G 0}`-tower of the connection difference

Target: `Work.Diff.EXT.ConnCov.covKAExt_bound_local`.  For every `k` and every `t ∈ Ico (T/2) T`
there is `Ck ≥ 0` with `ValBound G t k (tower (lcOf (G 0)) (fun _ => aOf G t) k) Ck`.

Unlike the uniform-in-`t` statement `Work.Diff.EXT.ConnCov.covKAExt_bound` (which needs the
Gronwall induction of the `ConnCov` plan), the `t`-wise statement only needs *smoothness plus
compactness*: at the fixed time `t` the tower is a smooth `(0,k+3)`-tensor field on the compact
manifold, hence its operator norm with respect to the metric `G t` is finite.

## Route

* In the chart at `x₀`, the value of the tower on arbitrary vectors is the multilinear expansion of
  the *chart recursion* `aCovArr`.  The coefficients of the expansion of a vector `q` in the
  coordinate frame are `(GramInv · q)`-combinations (`inner_coeff_expansion`), bounded by
  `(finrank) · Cl · √Cl · ‖q‖` as soon as the entries of `GramM` and `GramInv` are bounded by `Cl`
  (`inner_coeff_bound`).
* `aCovArr` is smooth in the chart coordinate (`CBound.aCovArr_contDiffAt`), hence bounded on a
  compact set of the chart target (`aCovArr_compact_bound`).
* The entries of `GramM`/`GramInv` are bounded by `gram_data_bounds_v2`.
* The passage from the chart at *each* point `x` to the whole manifold is the standard
  compactness argument (`CompactSpace.elim_nhds_subcover`), each point `x` being covered by the
  open ball of radius `r x` around its own chart coordinate `(extChartAt I x) x`, whose half ball
  lies inside the chart target.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## The coordinate frame spans the tangent space -/

/-- The coordinate frame of the chart at `x₀` spans `T_yM` for every `y` of the chart source. -/
theorem cFrame_span (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) :
    Submodule.span ℝ (Set.range (fun i : Fin (Module.finrank ℝ E) =>
      Work.Diff.GE.cFrame (I := I) x₀ i y)) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 fun w => ?_
  have h := Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis (I := I)
    (b := Module.finBasis ℝ E) x₀ (Submission.Diff.smoothExt y w) hy
  rw [Work.Diff.GE.smoothExt_apply] at h
  rw [h]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Set.mem_range_self i)

/-! ## The packing of the `k + 3` arguments

`vecPack v B` is the `Fin (k+3)`-tuple whose first `k` entries are the direction vectors
`v 0, …, v (k-1)` and whose last three entries are `B 0`, `B 1`, `B 2`. -/

/-- The packed tuple of `k` direction vectors and three value vectors. -/
noncomputable def vecPack {k : ℕ} {y : M} (v : Fin k → TangentSpace I y)
    (B : Fin 3 → TangentSpace I y) : Fin (k + 3) → TangentSpace I y :=
  Fin.addCases (motive := fun _ => TangentSpace I y) v B

lemma vecPack_castAdd {k : ℕ} {y : M} (v : Fin k → TangentSpace I y)
    (B : Fin 3 → TangentSpace I y) (i : Fin k) :
    vecPack (I := I) v B (Fin.castAdd 3 i) = v i := Fin.addCases_left i

lemma vecPack_natAdd {k : ℕ} {y : M} (v : Fin k → TangentSpace I y)
    (B : Fin 3 → TangentSpace I y) (p : Fin 3) :
    vecPack (I := I) v B (Fin.natAdd k p) = B p := Fin.addCases_right p

/-- Splitting a product over `Fin (k+3)` according to the packing. -/
lemma prod_univ_pack {M : Type*} [CommMonoid M] {k : ℕ} {V : Type*} (g : V → M)
    (v : Fin k → V) (B : Fin 3 → V) :
    (∏ s : Fin (k + 3), g (Fin.addCases v B s))
      = (∏ i : Fin k, g (v i)) * g (B 0) * g (B 1) * g (B 2) := by
  rw [Fin.prod_univ_add (a := k) (b := 3)]
  have h1 : (∏ i : Fin k, g (Fin.addCases v B (Fin.castAdd 3 i))) = ∏ i : Fin k, g (v i) :=
    Finset.prod_congr rfl (fun i _ => by rw [Fin.addCases_left])
  have h2 : (∏ j : Fin 3, g (Fin.addCases v B (Fin.natAdd k j))) = g (B 0) * g (B 1) * g (B 2) := by
    rw [Fin.prod_univ_three]
    simp only [Fin.addCases_right]
  rw [h1, h2]
  ac_rfl

/-- The field-level form of the packing: `smoothExt` of the packed tuple is the `mkT3`-packing of
the `smoothExt`-fields. -/
lemma smoothExt_vecPack {k : ℕ} {y : M} (v : Fin k → TangentSpace I y)
    (B : Fin 3 → TangentSpace I y) :
    (fun s : Fin (k + 3) => Submission.Diff.smoothExt y (vecPack (I := I) v B s))
      = Work.Diff.EXT.mkT3 (fun i : Fin k => Submission.Diff.smoothExt y (v i))
          (fun p : Fin 3 => Submission.Diff.smoothExt y (B p)) := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [vecPack_castAdd, Work.Diff.EXT.mkT3_castAdd]
  · intro p
    rw [vecPack_natAdd, Work.Diff.EXT.mkT3_natAdd]

/-- `smoothExt` of a tuple of vectors, written as a `mkT3`-packing. -/
lemma smoothExt_eq_mkT3 {k : ℕ} {y : M} (q : Fin (k + 3) → TangentSpace I y) :
    (fun s : Fin (k + 3) => Submission.Diff.smoothExt y (q s))
      = Work.Diff.EXT.mkT3 (fun i : Fin k => Submission.Diff.smoothExt y (q (Fin.castAdd 3 i)))
          (fun j : Fin 3 => Submission.Diff.smoothExt y (q (Fin.natAdd k j))) := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i; rw [Work.Diff.EXT.mkT3_castAdd]
  · intro j; rw [Work.Diff.EXT.mkT3_natAdd]

/-! ## The tower value is a multilinear form in the vectors -/

/-- **The value of the tower at `y`, as a multilinear form on the `k+3` vectors.**  This is the
tensoriality of `covKAExt` (`ka_val_dep_all`) together with its linearity in each slot
(`TensPropA`). -/
theorem cktA_multilinear (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ) (y : M) :
    ∃ T : MultilinearMap ℝ (fun _ : Fin (k+3) => TangentSpace I y) ℝ,
      ∀ p : Fin (k+3) → TangentSpace I y,
        T p = Work.Diff.EXT.cktA G t k (fun s => Submission.Diff.smoothExt y (p s)) y := by
  classical
  have hP : Work.Diff.EXT.TensPropA G t k := Work.Diff.EXT.ka_all hLC G t k
  have key : ∀ (p : Fin (k+3) → TangentSpace I y),
      ∀ s : Fin (k+3), Work.Diff.EXT.SmA (I := I) (M := M)
        (Submission.Diff.smoothExt y (p s)) :=
    fun p s => Work.Diff.GE.smoothExt_cmdiff y (p s)
  have VD : ∀ (m : Fin (k+3) → TangentSpace I y) (i : Fin (k+3))
      (w : TangentSpace I y) (W : Work.Diff.EXT.TfA (I := I) (M := M)),
      Work.Diff.EXT.SmA (I := I) (M := M) W → W y = w →
      Work.Diff.EXT.cktA G t k
          (fun s => Submission.Diff.smoothExt y ((Function.update m i w) s)) y
        = Work.Diff.EXT.cktA G t k
            (Function.update (fun s => Submission.Diff.smoothExt y (m s)) i W) y := by
    intro m i w W hW hval
    refine Work.Diff.EXT.ka_val_dep_all hLC G t k y (key _) ?_ ?_
    · intro s
      by_cases hs : s = i
      · subst hs; rw [Function.update_self]; exact hW
      · rw [Function.update_of_ne hs]; exact key m s
    · intro s
      by_cases hs : s = i
      · subst hs
        rw [Function.update_self, Function.update_self,
          Work.Diff.GE.smoothExt_apply, hval]
      · rw [Function.update_of_ne hs, Function.update_of_ne hs,
          Work.Diff.GE.smoothExt_apply]
  have hadd : ∀ (m : Fin (k+3) → TangentSpace I y) (i : Fin (k+3)) (x z : TangentSpace I y),
      Work.Diff.EXT.cktA G t k
          (fun s => Submission.Diff.smoothExt y ((Function.update m i (x + z)) s)) y
        = Work.Diff.EXT.cktA G t k
            (fun s => Submission.Diff.smoothExt y ((Function.update m i x) s)) y
          + Work.Diff.EXT.cktA G t k
            (fun s => Submission.Diff.smoothExt y ((Function.update m i z) s)) y := by
    intro m i x z
    have keyX : Work.Diff.EXT.SmA (I := I) (M := M) (Submission.Diff.smoothExt y x) :=
      Work.Diff.GE.smoothExt_cmdiff y x
    have keyZ : Work.Diff.EXT.SmA (I := I) (M := M) (Submission.Diff.smoothExt y z) :=
      Work.Diff.GE.smoothExt_cmdiff y z
    have hlin := congrFun (Work.Diff.EXT.TensPropA_add hP (key m) i keyX keyZ) y
    have hx := VD m i x (Submission.Diff.smoothExt y x) keyX
      (by rw [Work.Diff.GE.smoothExt_apply])
    have hz := VD m i z (Submission.Diff.smoothExt y z) keyZ
      (by rw [Work.Diff.GE.smoothExt_apply])
    have hxz := VD m i (x+z) (Submission.Diff.smoothExt y x + Submission.Diff.smoothExt y z)
      (Work.Diff.EXT.SmA_add keyX keyZ) (by
        rw [Pi.add_apply, Work.Diff.GE.smoothExt_apply, Work.Diff.GE.smoothExt_apply])
    rw [hxz, hlin]
    simp only [Pi.add_apply]
    rw [← hx, ← hz]
  have hsmul : ∀ (m : Fin (k+3) → TangentSpace I y) (i : Fin (k+3)) (c : ℝ)
      (x : TangentSpace I y),
      Work.Diff.EXT.cktA G t k
          (fun s => Submission.Diff.smoothExt y ((Function.update m i (c • x)) s)) y
        = c • Work.Diff.EXT.cktA G t k
            (fun s => Submission.Diff.smoothExt y ((Function.update m i x) s)) y := by
    intro m i c x
    have keyX : Work.Diff.EXT.SmA (I := I) (M := M) (Submission.Diff.smoothExt y x) :=
      Work.Diff.GE.smoothExt_cmdiff y x
    have hsm := congrFun (Work.Diff.EXT.TensPropA_smul hP (key m) i c keyX) y
    have hx := VD m i x (Submission.Diff.smoothExt y x) keyX
      (by rw [Work.Diff.GE.smoothExt_apply])
    have hcx := VD m i (c • x) ((fun _ : M => c) • Submission.Diff.smoothExt y x)
      (Work.Diff.EXT.SmA_smul (contMDiff_const) keyX) (by
        show c • (Submission.Diff.smoothExt y x y) = c • x
        rw [Work.Diff.GE.smoothExt_apply])
    rw [hcx, hsm, hx]
    rfl
  refine ⟨{ toFun := fun p => Work.Diff.EXT.cktA G t k
                (fun s => Submission.Diff.smoothExt y (p s)) y,
             map_update_add' := ?_, map_update_smul' := ?_ }, fun p => rfl⟩
  · intro inst m i x z
    have hinst : inst = instDecidableEqFin (k+3) := Subsingleton.elim _ _
    subst hinst
    exact hadd m i x z
  · intro inst m i c x
    have hinst : inst = instDecidableEqFin (k+3) := Subsingleton.elim _ _
    subst hinst
    exact hsmul m i c x

/-! ## The core estimate in one chart

Given the componentwise bound `|aCovArr …| ≤ A` and the entrywise Gram bounds
`|GramM|, |GramInv| ≤ Cl` on a subset `K` of the chart target, the tower value at `y = pt x₀ u`
(`u ∈ K`) on arbitrary vectors is bounded by `A · (n · (n Cl √Cl))^{k+3}` times the product of the
`G t`-norms. -/

theorem tower_val_bound_chart
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target)
    {A Cl : ℝ} (hA : 0 ≤ A) (hCl : 0 ≤ Cl)
    (hAc : ∀ u ∈ K, ∀ (v : Fin k → Fin (Module.finrank ℝ E))
        (i j l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.aCovArr G x₀ t k v i j l u| ≤ A)
    (hGr : ∀ u ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        |Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ u) i j| ≤ Cl ∧
        |Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ u) i j| ≤ Cl) :
    ∀ u ∈ K, ∀ (v : Fin k → TangentSpace I (Work.Diff.EXT.pt (I := I) x₀ u))
      (a b c : TangentSpace I (Work.Diff.EXT.pt (I := I) x₀ u)),
    |Work.Diff.EXT.ATower.valOp
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) k) (Work.Diff.EXT.pt (I := I) x₀ u) v a b c|
      ≤ A * ((Module.finrank ℝ E : ℝ)
            * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)) ^ (k + 3)
        * (Finset.univ.prod (fun i : Fin k =>
              Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ u) (v i) (v i))))
        * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ u) a a)
        * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ u) b b)
        * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ u) c c) := by
  classical
  intro u hu
  set y : M := Work.Diff.EXT.pt (I := I) x₀ u with hy
  intro v a b c
  have hysrc : y ∈ (chartAt H x₀).source := by
    rw [hy]
    have h1 : (extChartAt I x₀).symm u ∈ (extChartAt I x₀).source :=
      PartialEquiv.map_target (extChartAt I x₀) (hKt hu)
    rwa [extChartAt_source (I := I) x₀] at h1
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  obtain ⟨T, hT⟩ := cktA_multilinear (I := I) (M := M) hLC G t k y
  set σ : Fin (Module.finrank ℝ E) → TangentSpace I y :=
    fun i => Work.Diff.GE.cFrame (I := I) x₀ i y with hσ
  have hspan : Submodule.span ℝ (Set.range σ) = ⊤ := cFrame_span (I := I) (M := M) x₀ hysrc
  set p : Fin (k+3) → TangentSpace I y := vecPack (I := I) v ![a, b, c] with hp
  set lam : Fin (k+3) → Fin (Module.finrank ℝ E) → ℝ :=
    fun s i => ∑ j, (Matrix.of (fun i j => inner ℝ (σ i) (σ j)))⁻¹ i j * inner ℝ (σ j) (p s)
    with hlam
  -- ### the coefficients of the frame expansion
  have hcoeff : ∀ s : Fin (k+3), p s = ∑ i, lam s i • σ i := by
    intro s
    have h := Work.Diff.EXT.ConnCov.inner_coeff_expansion (V := TangentSpace I y) σ hspan (p s)
    rw [hlam]
    exact h
  -- ### the expansion of the multilinear form
  have hexp : T p = ∑ r : Fin (k+3) → Fin (Module.finrank ℝ E),
      (∏ s, lam s (r s)) * T (fun s => σ (r s)) := by
    have hpcongr : (fun s : Fin (k+3) => ∑ i, lam s i • σ i) = p :=
      funext (fun s => (hcoeff s).symm)
    rw [← hpcongr]
    exact Work.Diff.EXT.ConnCov.multilinear_expansion (ι := Fin (k+3)) T
      (Module.finrank ℝ E) lam (fun _ i => σ i)
  -- ### each frame value is an `aCovArr` component
  have hframe : ∀ r : Fin (k+3) → Fin (Module.finrank ℝ E),
      |T (fun s => σ (r s))| ≤ A := by
    intro r
    have h1 : T (fun s => σ (r s))
        = Work.Diff.EXT.covKAExt G t k
            (fun i : Fin k => Submission.Diff.smoothExt y (σ (r (Fin.castAdd 3 i))))
            (Submission.Diff.smoothExt y (σ (r (Fin.natAdd k 0))))
            (Submission.Diff.smoothExt y (σ (r (Fin.natAdd k 1))))
            (Submission.Diff.smoothExt y (σ (r (Fin.natAdd k 2)))) y := by
      rw [hT (fun s => σ (r s)), smoothExt_eq_mkT3, Work.Diff.EXT.cktA_mkT3_eq]
    have h2 : Work.Diff.EXT.covKAExt G t k
            (fun i : Fin k => Submission.Diff.smoothExt y (σ (r (Fin.castAdd 3 i))))
            (Submission.Diff.smoothExt y (σ (r (Fin.natAdd k 0))))
            (Submission.Diff.smoothExt y (σ (r (Fin.natAdd k 1))))
            (Submission.Diff.smoothExt y (σ (r (Fin.natAdd k 2)))) y
        = Work.Diff.EXT.covKAExt G t k
            (fun i : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (r (Fin.castAdd 3 i)))
            (Work.Diff.GE.cFrame (I := I) x₀ (r (Fin.natAdd k 0)))
            (Work.Diff.GE.cFrame (I := I) x₀ (r (Fin.natAdd k 1)))
            (Work.Diff.GE.cFrame (I := I) x₀ (r (Fin.natAdd k 2))) y :=
      (Work.Diff.EXT.covKAExt_frame_eq_smoothExt (I := I) (M := M) hLC G t k x₀ (hKt hu)
        (fun i : Fin k => r (Fin.castAdd 3 i)) (r (Fin.natAdd k 0)) (r (Fin.natAdd k 1))
        (r (Fin.natAdd k 2))).symm
    have h3 : Work.Diff.EXT.covKAExt G t k
            (fun i : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (r (Fin.castAdd 3 i)))
            (Work.Diff.GE.cFrame (I := I) x₀ (r (Fin.natAdd k 0)))
            (Work.Diff.GE.cFrame (I := I) x₀ (r (Fin.natAdd k 1)))
            (Work.Diff.GE.cFrame (I := I) x₀ (r (Fin.natAdd k 2))) y
        = Work.Diff.EXT.aCovArr G x₀ t k (fun i : Fin k => r (Fin.castAdd 3 i))
            (r (Fin.natAdd k 0)) (r (Fin.natAdd k 1)) (r (Fin.natAdd k 2)) u :=
      (Work.Diff.EXT.aCovArr_eq_covKAExt (I := I) (M := M) G x₀ t k
        (fun i : Fin k => r (Fin.castAdd 3 i)) (r (Fin.natAdd k 0)) (r (Fin.natAdd k 1))
        (r (Fin.natAdd k 2)) (hKt hu)).symm
    rw [h1, h2, h3]
    exact hAc u hu _ _ _ _
  -- ### the coefficient bound
  have hdiag : ∀ i : Fin (Module.finrank ℝ E), inner ℝ (σ i) (σ i) ≤ Cl := by
    intro i
    have h := (hGr u hu i i).1
    have hh : Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ u) i i
        = inner ℝ (σ i) (σ i) := rfl
    rw [hh] at h
    exact le_trans (le_abs_self _) h
  have hInv : ∀ i j : Fin (Module.finrank ℝ E),
      |(Matrix.of (fun i j => inner ℝ (σ i) (σ j)))⁻¹ i j| ≤ Cl := by
    intro i j
    have h := (hGr u hu i j).2
    have hh : Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ u) i j
        = (Matrix.of (fun i j => inner ℝ (σ i) (σ j)))⁻¹ i j := rfl
    rw [hh] at h
    exact h
  have hlamB : ∀ (s : Fin (k+3)) (i : Fin (Module.finrank ℝ E)),
      |lam s i| ≤ (Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl * ‖p s‖ := by
    intro s i
    have h := Work.Diff.EXT.ConnCov.inner_coeff_bound (V := TangentSpace I y) σ hCl hdiag hInv
      (p s) i
    rw [hlam]
    exact h
  -- ### the estimate
  have hstep1 : |T p| ≤ ∑ r : Fin (k+3) → Fin (Module.finrank ℝ E),
      (∏ s, |lam s (r s)|) * A := by
    rw [hexp]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun r _ => ?_)
    rw [abs_mul, Finset.abs_prod]
    exact mul_le_mul_of_nonneg_left (hframe r) (Finset.prod_nonneg fun s _ => abs_nonneg _)
  have hstepA : |T p| ≤ (∑ r : Fin (k+3) → Fin (Module.finrank ℝ E),
      (∏ s, |lam s (r s)|)) * A := by
    refine le_trans hstep1 ?_
    rw [Finset.sum_mul]
  have hstep2 : (∑ r : Fin (k+3) → Fin (Module.finrank ℝ E), ∏ s, |lam s (r s)|)
      = ∏ s : Fin (k+3), ∑ i : Fin (Module.finrank ℝ E), |lam s i| := by
    rw [Finset.prod_univ_sum (t := fun _ : Fin (k+3) =>
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (f := fun s i => |lam s i|),
      Fintype.piFinset_univ]
  have hstep3 : ∏ s : Fin (k+3), ∑ i : Fin (Module.finrank ℝ E), |lam s i|
      ≤ ∏ s : Fin (k+3),
        ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)
          * ‖p s‖) := by
    refine Finset.prod_le_prod₀ (fun s _ => Finset.sum_nonneg fun i _ => abs_nonneg _)
      (fun s _ => ?_)
    calc ∑ i : Fin (Module.finrank ℝ E), |lam s i|
        ≤ ∑ _i : Fin (Module.finrank ℝ E),
            ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl * ‖p s‖) :=
          Finset.sum_le_sum fun i _ => hlamB s i
      _ = (Module.finrank ℝ E : ℝ)
            * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl * ‖p s‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)
            * ‖p s‖ := by ring
  have hstep4 : ∏ s : Fin (k+3),
        ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)
          * ‖p s‖)
      = ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)) ^ (k+3)
        * ∏ s : Fin (k+3), ‖p s‖ := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsqrt : ∀ u : TangentSpace I y,
      Real.sqrt (inner ℝ u u) = Real.sqrt ((G t).inner y u u) := fun u => rfl
  have hnorm : ∀ s : Fin (k+3), ‖p s‖ = Real.sqrt (inner ℝ (p s) (p s)) :=
    fun s => norm_eq_sqrt_real_inner _
  have hsplit : (∏ s : Fin (k+3), ‖p s‖)
      = (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner y (v i) (v i))))
        * Real.sqrt ((G t).inner y a a) * Real.sqrt ((G t).inner y b b)
        * Real.sqrt ((G t).inner y c c) := by
    have h1 : (∏ s : Fin (k+3), ‖p s‖)
        = ∏ s : Fin (k+3), Real.sqrt ((G t).inner y (p s) (p s)) := by
      refine Finset.prod_congr rfl (fun s _ => ?_)
      rw [hnorm s]
      exact hsqrt (p s)
    rw [h1, hp]
    have h2 := prod_univ_pack (g := fun u : TangentSpace I y => Real.sqrt ((G t).inner y u u))
      v ![a, b, c]
    simpa only [vecPack, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] using h2
  -- ### the identification of `valOp` with `T p`
  have hvalop : Work.Diff.EXT.ATower.valOp
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) k) y v a b c = T p := by
    have h1 : Work.Diff.EXT.ATower.valOp
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (fun _ => Work.Diff.EXT.aOf G t) k) y v a b c
        = Work.Diff.EXT.cktA G t k (Work.Diff.EXT.mkT3
            (fun i : Fin k => Submission.Diff.smoothExt y (v i))
            (Work.Diff.EXT.trip3 (Submission.Diff.smoothExt y a)
              (Submission.Diff.smoothExt y b) (Submission.Diff.smoothExt y c))) y := by
      rw [Work.Diff.EXT.ATower.valOp, Work.Diff.EXT.ATower.tower_eq_covKAExt]
      exact (Work.Diff.EXT.cktA_mkT3_eq G t k (fun i : Fin k => Submission.Diff.smoothExt y (v i))
        (Work.Diff.EXT.trip3 (Submission.Diff.smoothExt y a)
          (Submission.Diff.smoothExt y b) (Submission.Diff.smoothExt y c)) y).symm
    have h2 : T p = Work.Diff.EXT.cktA G t k (Work.Diff.EXT.mkT3
        (fun i : Fin k => Submission.Diff.smoothExt y (v i))
        (Work.Diff.EXT.trip3 (Submission.Diff.smoothExt y a)
          (Submission.Diff.smoothExt y b) (Submission.Diff.smoothExt y c))) y := by
      have htup : (fun p : Fin 3 => Submission.Diff.smoothExt y (![a, b, c] p))
          = Work.Diff.EXT.trip3 (Submission.Diff.smoothExt y a)
              (Submission.Diff.smoothExt y b) (Submission.Diff.smoothExt y c) := by
        funext j
        fin_cases j <;> rfl
      rw [hT p, hp, smoothExt_vecPack, htup]
    rw [h1]
    exact h2.symm
  rw [hvalop]
  calc |T p|
      ≤ (∑ r : Fin (k+3) → Fin (Module.finrank ℝ E), ∏ s, |lam s (r s)|) * A := hstepA
    _ ≤ (∏ s : Fin (k+3), ∑ i : Fin (Module.finrank ℝ E), |lam s i|) * A := by rw [hstep2]
    _ ≤ (∏ s : Fin (k+3), ((Module.finrank ℝ E : ℝ)
            * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl) * ‖p s‖)) * A :=
        mul_le_mul_of_nonneg_right hstep3 hA
    _ = (((Module.finrank ℝ E : ℝ)
            * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)) ^ (k+3)
          * ∏ s : Fin (k+3), ‖p s‖) * A := by rw [hstep4]
    _ = A * (((Module.finrank ℝ E : ℝ)
            * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)) ^ (k+3)
          * ∏ s : Fin (k+3), ‖p s‖) := by ring
    _ = A * ((Module.finrank ℝ E : ℝ)
            * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)) ^ (k + 3)
          * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner y (v i) (v i))))
          * Real.sqrt ((G t).inner y a a) * Real.sqrt ((G t).inner y b b)
          * Real.sqrt ((G t).inner y c c) := by
        rw [hsplit]; ring

/-! ## From the chart to the whole manifold -/

/-- **A neighbourhood of every point, with a uniform bound on it.**  For the fixed `k` and `t`, the
tower is bounded on an open neighbourhood of every point of `M`, by the chart estimate at that
point. -/
theorem tower_val_bound_nhds
    [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (k : ℕ) {t : ℝ} (ht : t ∈ Set.Ico (T / 2) T) :
    ∀ x : M, ∃ U : Set M, U ∈ 𝓝 x ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ y ∈ U, ∀ (v : Fin k → TangentSpace I y)
        (a b c : TangentSpace I y),
      |Work.Diff.EXT.ATower.valOp
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (fun _ => Work.Diff.EXT.aOf G t) k) y v a b c|
        ≤ D * (Finset.univ.prod (fun i : Fin k =>
              Real.sqrt ((G t).inner y (v i) (v i))))
            * Real.sqrt ((G t).inner y a a) * Real.sqrt ((G t).inner y b b)
            * Real.sqrt ((G t).inner y c c) := by
  intro x₀
  -- the chart coordinate of `x₀`, and a ball around it inside the chart target
  have hsrc : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hmem : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by rwa [extChartAt_source])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hmem)
  set r : ℝ := ε / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hKt : Metric.closedBall ((extChartAt I x₀) x₀) r ⊆ (extChartAt I x₀).target :=
    (Metric.closedBall_subset_ball (by rw [hrdef]; linarith)).trans hball
  have hKc : IsCompact (Metric.closedBall ((extChartAt I x₀) x₀) r) := isCompact_closedBall _ _
  -- the constants
  obtain ⟨A, hA0, hAb⟩ := aCovArr_compact_bound (I := I) (M := M) G x₀ t k
    (Metric.closedBall ((extChartAt I x₀) x₀) r) hKc hKt
  obtain ⟨c, Cl, hc, hCl, _hcCl, hGr⟩ :=
    gram_data_bounds_v2 (I := I) (M := M) G T C hT hC hmet x₀
      (Metric.closedBall ((extChartAt I x₀) x₀) r) hKc hKt
  refine ⟨(extChartAt I x₀) ⁻¹' (Metric.ball ((extChartAt I x₀) x₀) r) ∩ (chartAt H x₀).source,
    Filter.inter_mem ((continuousAt_extChartAt (I := I) x₀).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr)) ((chartAt H x₀).open_source.mem_nhds hsrc),
    A * ((Module.finrank ℝ E : ℝ)
      * ((Module.finrank ℝ E : ℝ) * Cl * Real.sqrt Cl)) ^ (k+3), ?_, ?_⟩
  · refine mul_nonneg hA0 (pow_nonneg ?_ _)
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCl) (Real.sqrt_nonneg _))
  · intro y hy v a b c
    obtain ⟨hyU, hyS⟩ := hy
    have hyK : (extChartAt I x₀) y ∈ Metric.closedBall ((extChartAt I x₀) x₀) r :=
      Metric.ball_subset_closedBall hyU
    have hpy : Work.Diff.EXT.pt (I := I) x₀ ((extChartAt I x₀) y) = y := by
      refine (extChartAt I x₀).left_inv ?_
      rw [extChartAt_source]
      exact hyS
    have hmain := tower_val_bound_chart (I := I) (M := M) hLC G t k x₀
      (Metric.closedBall ((extChartAt I x₀) x₀) r) hKt hA0 hCl
      (fun u hu => hAb u hu) (fun u hu i j => (hGr t ht u hu i j).2)
      ((extChartAt I x₀) y) hyK v a b c
    rwa [hpy] at hmain

theorem covKAExt_bound_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u) :
    ∀ k : ℕ, ∀ t ∈ Set.Ico (T / 2) T, ∃ Ck : ℝ, 0 ≤ Ck ∧
      Work.Diff.EXT.ATower.ValBound G t k
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) k) Ck := by
  intro k t ht
  have hloc := tower_val_bound_nhds (I := I) (M := M) hLC G T C hT hC hmet k ht
  choose U hU D hD0 hDb using hloc
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  refine ⟨∑ x ∈ s, D x, Finset.sum_nonneg (fun x _ => hD0 x), ?_⟩
  intro y v a b c
  have hy : y ∈ ⋃ x ∈ s, U x := by rw [hs]; trivial
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hxs, hyU⟩ := hy
  refine le_trans (hDb x y hyU v a b c) ?_
  have hprod0 : 0 ≤ (Finset.univ.prod (fun i : Fin k =>
        Real.sqrt ((G t).inner y (v i) (v i))))
      * Real.sqrt ((G t).inner y a a) * Real.sqrt ((G t).inner y b b)
      * Real.sqrt ((G t).inner y c c) :=
    mul_nonneg (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun x _ => hD0 x) hxs) (Finset.prod_nonneg
        (fun i _ => Real.sqrt_nonneg _))) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Work.Diff.EXT.ConnCov
