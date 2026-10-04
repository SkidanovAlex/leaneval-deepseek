import Mathlib
import Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShiAux
import Submission.Work.Diff.EXT.aComp_jets
import Submission.Work.Diff.EXT.aCovArr_eq_covKAExt
import Submission.Work.Diff.EXT.covKAExt_frame_eq_smoothExt
import Submission.Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound
import Submission.Work.Diff.EXT.christoffel_bounds_of_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Chart jets of the connection difference from the fixed-connection tower of `aOf`

Target: `Work.Diff.EXT.ConnCov.aComp_jets_of_aOfTower`.

`aComp G x₀ t · i j l` is the chart array of the *lowered* connection difference
`g_t(∇^{g_t} − ∇^{g_0})`, and `aCovArr G x₀ t k v i j l` is its `k`-th covariant derivative with
respect to the *fixed* background connection `∇^{G 0}`, written in the chart recursion with the
background Christoffel symbols `cGam (G 0)`.

The hypothesis `hA` bounds the `∇^{G 0}`-tower of `aOf G t` (in the `ValBound` sense, i.e. on the
smooth extensions of the vectors, with the norms of the metric `G t`).

## Route

1. **`aCovArr` from `hA`.**  `Work.Diff.EXT.aCovArr_eq_covKAExt` identifies the chart recursion with
   the frozen tower `covKAExt G t k` evaluated on the *coordinate frame* `cFrame x₀ ·`; the proved
   `Work.Diff.EXT.covKAExt_frame_eq_smoothExt` replaces the frame by the smooth extensions (this is
   where `hLC` is used), and `valOp_tower_eq_covKAExt` turns that into `valOp`.  So `hA` bounds every
   `aCovArr` value by `B k` times the product of the `G t`-norms of the frame vectors.
2. **The metric factor.**  The diagonal Gram entries of the coordinate frame are controlled uniformly
   on the compact `K'` and on `[T/2,T)` by `hmet` (the exponential comparison with the *fixed*
   metric `G 0`, whose diagonal Gram entries are continuous on the compact `K'`), giving a constant
   `S` with `sqrt(GramM t x i i) ≤ S` there.
3. **Chart jets.**  `Work.Diff.EXT.aComp_jets` converts the bounds on `aCovArr` (levels `≤ K`) plus
   the (unconditional) jet bounds for `cGam (G 0)` and the smoothness of the chart data into a
   uniform bound on all chart derivatives of `aComp` of order `≤ K`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

open Work.Diff.EXT.ATower

/-- Nonnegativity of a Riemannian metric on the diagonal. -/
theorem smet_inner_self_nonneg_acjt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp
  · exact le_of_lt (g.pos x v h)

/-- Elementary product estimate: if `P ≤ S^m` and `si, sj, sl ≤ S` with all quantities nonnegative,
then `Bm * P * si * sj * sl ≤ Bm * S^(m+3)`. -/
private lemma prod_bound_acjt {m : ℕ} {Bm S P si sj sl : ℝ} (hB : 0 ≤ Bm) (hS : 0 ≤ S)
    (_hP0 : 0 ≤ P) (hsi0 : 0 ≤ si) (hsj0 : 0 ≤ sj) (hsl0 : 0 ≤ sl)
    (hP : P ≤ S ^ m) (hsi : si ≤ S) (hsj : sj ≤ S) (hsl : sl ≤ S) :
    Bm * P * si * sj * sl ≤ Bm * S ^ (m + 3) := by
  have hSm : 0 ≤ S ^ m := pow_nonneg hS m
  have h1 : Bm * P ≤ Bm * S ^ m := mul_le_mul_of_nonneg_left hP hB
  have h2 : Bm * P * si ≤ Bm * S ^ m * S :=
    mul_le_mul h1 hsi hsi0 (mul_nonneg hB hSm)
  have h3 : Bm * P * si * sj ≤ Bm * S ^ m * S * S :=
    mul_le_mul h2 hsj hsj0 (mul_nonneg (mul_nonneg hB hSm) hS)
  have h4 : Bm * P * si * sj * sl ≤ Bm * S ^ m * S * S * S :=
    mul_le_mul h3 hsl hsl0 (mul_nonneg (mul_nonneg (mul_nonneg hB hSm) hS) hS)
  calc Bm * P * si * sj * sl ≤ Bm * S ^ m * S * S * S := h4
    _ = Bm * S ^ (m + 3) := by ring

theorem aComp_jets_of_aOfTower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (K : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j ≤ K → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j))
    (x₀ : M) (K' : Set E) (hK'c : IsCompact K') (hK't : K' ⊆ (extChartAt I x₀).target) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ K →
      ∀ (i j l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ C' := by
  classical
  -- ## Step 1: the diagonal Gram entries of the fixed metric `G 0` are bounded on `K'`
  have hGram0b : ∀ i : Fin (Module.finrank ℝ E), ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ y' ∈ K',
      (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y')
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y')) ≤ Ci := by
    intro i
    have hcont : ContinuousOn (fun y' : E =>
        (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y')
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))) K' := by
      intro y hy
      have hcd : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y' : E => Work.Diff.GE.GramM G x₀ 0 (Work.Diff.EXT.pt (I := I) x₀ y') i i) y :=
        Work.Diff.EXT.CBound.GramM_contDiffAt_of_target (I := I) (M := M) G x₀ 0 (hK't hy) i i
      have hca : ContinuousAt (fun y' : E =>
          (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y')
            (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))
            (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))) y := by
        simpa only [Work.Diff.GE.GramM, Work.Diff.GE.mComp] using hcd.continuousAt
      exact hca.continuousWithinAt
    obtain ⟨Ci, hCi⟩ := hK'c.bddAbove_image hcont
    refine ⟨max 1 Ci, le_trans zero_le_one (le_max_left 1 Ci), fun y' hy' =>
      le_trans (hCi ⟨y', hy', rfl⟩) (le_max_right 1 Ci)⟩
  choose Ci hCi using hGram0b
  have hCia : ∀ i : Fin (Module.finrank ℝ E), 0 ≤ Ci i := fun i => (hCi i).1
  have hCib : ∀ (i : Fin (Module.finrank ℝ E)) (y' : E), y' ∈ K' →
      (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y')
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y')) ≤ Ci i :=
    fun i y' hy' => (hCi i).2 y' hy'
  set M0 : ℝ := ∑ i : Fin (Module.finrank ℝ E), Ci i with hM0def
  have hM00 : 0 ≤ M0 := by
    rw [hM0def]
    exact Finset.sum_nonneg (fun i _ => hCia i)
  have hGram0M0 : ∀ y' ∈ K', ∀ i : Fin (Module.finrank ℝ E),
      (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y')
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y')) ≤ M0 := by
    intro y' hy' i
    refine le_trans (hCib i y' hy') ?_
    rw [hM0def]
    exact Finset.single_le_sum (fun j _ => hCia j) (Finset.mem_univ i)
  -- ## Step 2: the comparison constant for the metric on the slab
  set Λ : ℝ := Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) with hΛdef
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛdef]
    exact Real.exp_nonneg _
  set D : ℝ := Λ * M0 with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact mul_nonneg hΛ0 hM00
  set S : ℝ := Real.sqrt D with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact Real.sqrt_nonneg _
  have hC2 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C) := by
    have h1 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ (Module.finrank ℝ E : ℝ) * C := mul_nonneg h1 hC
    linarith
  have hGramD : ∀ t ∈ Set.Ico (T / 2) T, ∀ y' ∈ K', ∀ i : Fin (Module.finrank ℝ E),
      (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y')
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y')) ≤ D := by
    intro t ht y' hy' i
    have ht0 : t ∈ Set.Ico (0 : ℝ) T := ⟨by linarith [hT, ht.1], ht.2⟩
    have hexp : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) ≤ Λ := by
      rw [hΛdef]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt ht.2) hC2)
    calc (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y')
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))
        ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t)
            * (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y')
                (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y'))
                (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y')) :=
          (hmet t ht0 _ _).1
      _ ≤ Λ * M0 := mul_le_mul hexp (hGram0M0 y' hy' i)
          (smet_inner_self_nonneg_acjt (G 0) _ _) hΛ0
      _ = D := by rw [hDdef]
  -- ## Step 3: the chart covariant derivatives `aCovArr` are bounded by the tower data
  have hcore : ∀ m ≤ K, ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K',
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.aCovArr (I := I) (M := M) G x₀ t m v i j l y| ≤ Cm := by
    intro m hm
    refine ⟨B m * S ^ (m + 3), mul_nonneg (hB m) (pow_nonneg hS0 _), ?_⟩
    intro t ht y hy v i j l
    have hyT : y ∈ (extChartAt I x₀).target := hK't hy
    have hbridge : Work.Diff.EXT.aCovArr (I := I) (M := M) G x₀ t m v i j l y
        = valOp (tower (Submission.Diff.lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G t) m)
            (Work.Diff.EXT.pt (I := I) x₀ y)
            (fun s : Fin m => Work.Diff.GE.cFrame (I := I) x₀ (v s)
              (Work.Diff.EXT.pt (I := I) x₀ y))
            (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
            (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))
            (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y)) := by
      rw [Work.Diff.EXT.aCovArr_eq_covKAExt (I := I) (M := M) G x₀ t m v i j l hyT,
        Work.Diff.EXT.covKAExt_frame_eq_smoothExt (I := I) (M := M) hLC G t m x₀ hyT v i j l,
        ← Work.Diff.EXT.ATower.valOp_tower_eq_covKAExt]
    rw [hbridge]
    refine le_trans (hA m hm t ht (Work.Diff.EXT.pt (I := I) x₀ y)
      (fun s : Fin m => Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
      (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
      (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))
      (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y))) ?_
    have hPf : (∏ s : Fin m, Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y)))) ≤ S ^ m := by
      refine le_trans (Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun s : Fin m => Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))))
        (g := fun _ : Fin m => S)
        (fun s _ => Real.sqrt_nonneg _)
        (fun s _ => Real.sqrt_le_sqrt (hGramD t ht y hy (v s)))) ?_
      simp [Finset.prod_const]
    have hP0 : 0 ≤ (∏ s : Fin m, Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y)))) :=
      Finset.prod_nonneg (s := Finset.univ)
        (f := fun s : Fin m => Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))))
        (fun s _ => Real.sqrt_nonneg _)
    exact prod_bound_acjt (hB m) hS0 hP0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) hPf (Real.sqrt_le_sqrt (hGramD t ht y hy i))
      (Real.sqrt_le_sqrt (hGramD t ht y hy j)) (Real.sqrt_le_sqrt (hGramD t ht y hy l))
  -- ## Step 4: the remaining inputs of `aComp_jets`
  have hcGam0 : ∀ m ≤ K, ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ y ∈ K',
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖ ≤ Cc :=
    fun m _ => Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound (I := I) (M := M) G x₀ K'
      hK'c hK't m
  have hsm0 : ∀ y ∈ K', ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y :=
    fun y hy i j l => Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0)
      x₀ (hK't hy) l i j
  have hsmA : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y := by
    intro t ht y hy i j l
    have hyT : y ∈ (extChartAt I x₀).target := hK't hy
    rw [show (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l)
        = fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') l p
              * (Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i j
                  - Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i j) from rfl]
    refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ => ?_
    refine ContDiffAt.mul ?_ ?_
    · exact Work.Diff.EXT.CBound.GramM_contDiffAt_of_target (I := I) (M := M) G x₀ t hyT l p
    · exact (Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G t) x₀ hyT p i j).sub
        (Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀ hyT p i j)
  -- ## Step 5: chart jets of `aComp`
  obtain ⟨C', hC'0, hC'⟩ := Work.Diff.EXT.aComp_jets (I := I) (M := M) G (T / 2) T x₀ K' K
    hK't hcore hcGam0 hsm0 hsmA
  exact ⟨C', hC'0, fun t ht m hm i j l y hy => hC' t ht y hy m hm i j l⟩

end Work.Diff.EXT.ConnCov
