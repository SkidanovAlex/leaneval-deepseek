import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShiAux
import Submission.Work.Diff.EXT.aCovArr_eq_covKAExt
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.EXT.ConnCov.norm_iteratedFDeriv_fderiv_apply_le
import Submission.Work.Diff.EXT.ric_bound_of_curvBound
import Submission.Work.Diff.EXT.covK_germ
import Submission.Work.Diff.EXT.covK_linear
import Submission.Work.Diff.GE.exists_smooth_section_eq_nhds
import Submission.Work.Diff.EXT.ConnCov.rmChartTower_eq_covKRmExt
import Submission.Work.Diff.EXT.ConnCov.rmChartTower_jets
import Submission.Work.Diff.EXT.ConnCov.rmChartTower_jets_weak
import Submission.Work.Diff.EXT.ConnCov.reactArr_jets
import Submission.Work.Diff.EXT.ConnCov.tower3Arr_deriv_time
import Submission.Work.Diff.EXT.ConnCov.chrCoord_jets_bound
import Submission.Work.Diff.EXT.ConnCov.chartData_smooth_on_slab
import Submission.Work.Diff.EXT.ConnCov.aComp_jointSmooth_of_flow
import Submission.Work.Diff.EXT.ConnCov.tower_dAOfBase_congr_germ
import Submission.Work.Diff.EXT.ConnCov.tower3Arr_jets_family
import Submission.Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound
import Submission.Work.Diff.EXT.covKAExt_frame_eq_smoothExt
import Submission.Work.Diff.T.FrameExt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

section Helpers

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- Nonnegativity of a Riemannian metric on the diagonal. -/
private theorem smet_inner_self_nonneg' {g : Submission.Diff.SMet I M} (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp
  · exact le_of_lt (g.pos x v h)

/-- The chart recursion `Work.Diff.EXT.aCovArr` of the connection difference is the general
recursion `tower3Arr` applied to the base array `aCompArr`. -/
theorem aCovArr_eq_tower3Arr (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) :
    ∀ (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
      Work.Diff.EXT.aCovArr (I := I) (M := M) G x₀ t m v i j l
        = tower3Arr (I := I) (M := M) G x₀ t
            (aCompArr (I := I) (M := M) G x₀ t) m v i j l := by
  intro m
  induction m with
  | zero => intro v i j l; rfl
  | succ m ih =>
      intro v i j l
      simp only [Work.Diff.EXT.aCovArr, tower3Arr, ih]

/-- **The diagonal Gram entries of `G t` on a compact chart set are bounded on the slab.**  This is
the comparison `(G t).inner ≤ exp (2 n C t) (G 0).inner` of the hypothesis `hmet` applied to the
diagonal entries of the *coordinate frame*, which are continuous on the compact `K'`. -/
theorem gramDiag_bound
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (x₀ : M) (K' : Set E) (hK'c : IsCompact K') (hK't : K' ⊆ (extChartAt I x₀).target) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (i : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
      (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)) ≤ D := by
  classical
  have h0 : ∀ i : Fin (Module.finrank ℝ E), ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ y' ∈ K',
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
  choose Ci hCi using h0
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
  set Λ : ℝ := Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; exact Real.exp_nonneg _
  have hC2 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C) := by
    have h1 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ (Module.finrank ℝ E : ℝ) * C := mul_nonneg h1 hC
    linarith
  refine ⟨Λ * M0, mul_nonneg hΛ0 hM00, ?_⟩
  intro t ht i y hy
  have ht0 : t ∈ Set.Ico (0 : ℝ) T := ⟨by linarith [hT, ht.1], ht.2⟩
  have hexp : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) ≤ Λ := by
    rw [hΛdef]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt ht.2) hC2)
  calc (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
      ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t)
          * (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y)
              (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
              (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)) :=
        (hmet t ht0 _ _).1
    _ ≤ Λ * M0 := mul_le_mul hexp (hGram0M0 y hy i)
        (smet_inner_self_nonneg' (g := G 0) _ _) hΛ0

/-- **The coordinate-frame components of the moving curvature tower are bounded on the slab.**
This converts Shi's a priori estimate `hShi` (bounds on `|∇^{G t,k}Rm|²` in an orthonormal frame)
into bounds on the components of `∇^{G t,m}Rm` in the *coordinate frame* of the chart at `x₀`, for
all `m ≤ K`, using the germ-locality `covKRmExt_congr_germ`, the value dependence
`covKRmExt_tensorial` and the evaluation bound `covKRmExt_eval_bound`. -/
theorem covKRmExt_frame_bound
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (K : ℕ) (x₀ : M) (K' : Set E) (hK'c : IsCompact K')
    (hK't : K' ⊆ (extChartAt I x₀).target)
    (hGram : ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Set.Ico (T / 2) T,
      ∀ (i : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)) ≤ D) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ m : ℕ, m ≤ K →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.covKRmExt (G t) m
            (fun s : Fin m => Work.Diff.GE.cFrame (I := I) x₀ (v s))
            (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
            (Work.Diff.GE.cFrame (I := I) x₀ k) (Work.Diff.GE.cFrame (I := I) x₀ l)
            (Work.Diff.EXT.pt (I := I) x₀ y)| ≤ Ck := by
  classical
  -- ### uniform evaluation constants
  have hCe : ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ m : ℕ, m ≤ K →
      ∀ (g : Submission.Diff.SMet I M) (x : M) (v : Fin m → TangentSpace I x)
        (a b c d : TangentSpace I x),
        |Work.Diff.EXT.covKRmExt g m (fun i => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) (Submission.Diff.smoothExt x d) x|
          ≤ Ce * (1 + Real.sqrt (Work.Diff.EXT.curvNormK g x m))
              * (Finset.univ.prod (fun i : Fin m => Real.sqrt (g.inner x (v i) (v i)))
                 * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
                 * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by
    refine Work.Diff.EXT.exists_uniform_bound_of_le
      (P := fun m Ce => ∀ (g : Submission.Diff.SMet I M) (x : M)
        (v : Fin m → TangentSpace I x) (a b c d : TangentSpace I x),
        |Work.Diff.EXT.covKRmExt g m (fun i => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) (Submission.Diff.smoothExt x d) x|
          ≤ Ce * (1 + Real.sqrt (Work.Diff.EXT.curvNormK g x m))
              * (Finset.univ.prod (fun i : Fin m => Real.sqrt (g.inner x (v i) (v i)))
                 * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
                 * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)))
      (fun m Ce Ce' h hle g x v a b c d => le_trans (h g x v a b c d)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (by positivity))
          (by positivity))) K
      (fun m _ => Work.Diff.EXT.covKRmExt_eval_bound (I := I) (M := M) hLC m)
  obtain ⟨Ce, hCe0, hCe'⟩ := hCe
  -- ### uniform curvature-norm bounds
  have hCr : ∃ Cr : ℝ, ∀ m : ℕ, m ≤ K → ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      Work.Diff.EXT.curvNormK (G t) x m ≤ Cr := by
    have hσ : 0 < T / 2 := by linarith
    have hσT : T / 2 < T := by linarith
    obtain ⟨Cr, -, hCr⟩ := Work.Diff.EXT.exists_uniform_bound_of_le
      (P := fun m Cr => ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
        Work.Diff.EXT.curvNormK (G t) x m ≤ Cr)
      (fun m Cr Cr' h hle t ht x => le_trans (h t ht x) hle) K
      (fun m _ => by
        obtain ⟨Cm, hCm⟩ := hShi G T C (T / 2) hT hflow hbound hσ hσT m
        exact ⟨max Cm 0, le_max_right _ _,
          fun t ht x => le_trans (hCm t ht x) (le_max_left _ _)⟩)
    exact ⟨Cr, hCr⟩
  obtain ⟨Cr, hCr⟩ := hCr
  -- ### the diagonal Gram bound
  obtain ⟨D, hD0, hD⟩ := hGram
  set S : ℝ := max 1 (Real.sqrt D) with hSdef
  have hS1 : 1 ≤ S := le_max_left _ _
  have hS0 : 0 ≤ S := le_trans zero_le_one hS1
  have hsqrtD : Real.sqrt D ≤ S := le_max_right _ _
  refine ⟨Ce * (1 + Real.sqrt (max Cr 0)) * S ^ (K + 4), ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg hCe0 ?_) (pow_nonneg hS0 _)
    exact add_nonneg zero_le_one (Real.sqrt_nonneg _)
  intro t ht y hy m hm v i j k l
  have hsrc : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
    rw [Work.Diff.EXT.pt, ← extChartAt_source I x₀]
    exact (extChartAt I x₀).map_target (hK't hy)
  -- globally smooth representatives of the coordinate frame agreeing near the point
  have hrep : ∀ (a : Fin (Module.finrank ℝ E)), ∃ X : Π z : M, TangentSpace I z,
      (CMDiff ∞ (T% X)) ∧ X =ᶠ[𝓝 (Work.Diff.EXT.pt (I := I) x₀ y)]
        (Work.Diff.GE.cFrame (I := I) x₀ a) := by
    intro a
    have hev : ∀ᶠ z in 𝓝 (Work.Diff.EXT.pt (I := I) x₀ y),
        ContMDiffAt I I.tangent ∞ (fun z : M => (⟨z, Work.Diff.GE.cFrame (I := I) x₀ a z⟩ :
          TangentBundle I M)) z := by
      filter_upwards [(chartAt H x₀).open_source.mem_nhds hsrc] with z hz
      exact (Work.Diff.EXT.ka_smooth_cFrame (I := I) x₀ a).contMDiffAt
        ((chartAt H x₀).open_source.mem_nhds hz)
    obtain ⟨X, hX, -, hXeq⟩ := Work.Diff.GE.exists_smooth_section_eq_nhds
      (I := I) (X := Work.Diff.GE.cFrame (I := I) x₀ a) hev
    exact ⟨X, hX, hXeq⟩
  choose W hWsm hWeq using hrep
  -- the germ argument
  have hgerm : Work.Diff.EXT.covKRmExt (G t) m
        (fun s : Fin m => Work.Diff.GE.cFrame (I := I) x₀ (v s))
        (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
        (Work.Diff.GE.cFrame (I := I) x₀ k) (Work.Diff.GE.cFrame (I := I) x₀ l)
        (Work.Diff.EXT.pt (I := I) x₀ y)
      = Work.Diff.EXT.covKRmExt (G t) m (fun s : Fin m => W (v s)) (W i) (W j) (W k) (W l)
        (Work.Diff.EXT.pt (I := I) x₀ y) :=
    Work.Diff.EXT.covKRmExt_congr_germ (g := G t) m
      (fun s : Fin m => Work.Diff.GE.cFrame (I := I) x₀ (v s)) (fun s : Fin m => W (v s))
      (Work.Diff.GE.cFrame (I := I) x₀ i) (W i) (Work.Diff.GE.cFrame (I := I) x₀ j) (W j)
      (Work.Diff.GE.cFrame (I := I) x₀ k) (W k) (Work.Diff.GE.cFrame (I := I) x₀ l) (W l)
      (Work.Diff.EXT.pt (I := I) x₀ y) (fun s => (hWeq (v s)).symm)
      ((hWeq i).symm) ((hWeq j).symm) ((hWeq k).symm) ((hWeq l).symm)
  -- the value comparison with the `smoothExt` extensions
  have hval : Work.Diff.EXT.covKRmExt (G t) m (fun s : Fin m => W (v s)) (W i) (W j) (W k) (W l)
        (Work.Diff.EXT.pt (I := I) x₀ y)
      = Work.Diff.EXT.covKRmExt (G t) m
          (fun s : Fin m => Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y)))
          (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)))
          (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y)))
          (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y)))
          (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y)))
          (Work.Diff.EXT.pt (I := I) x₀ y) :=
    Work.Diff.EXT.covKRmExt_tensorial (I := I) (M := M) hLC m (G t)
      (Work.Diff.EXT.pt (I := I) x₀ y) (fun s => W (v s))
      (fun s => Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y)))
      (W i) (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)))
      (W j) (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y)))
      (W k) (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y)))
      (W l) (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y)))
      (fun s => hWsm (v s)) (fun s => Work.Diff.GE.smoothExt_cmdiff _ _)
      (hWsm i) (Work.Diff.GE.smoothExt_cmdiff _ _) (hWsm j) (Work.Diff.GE.smoothExt_cmdiff _ _)
      (hWsm k) (Work.Diff.GE.smoothExt_cmdiff _ _) (hWsm l) (Work.Diff.GE.smoothExt_cmdiff _ _)
      (fun s => (hWeq (v s)).eq_of_nhds.trans (Work.Diff.GE.smoothExt_apply _ _).symm)
      ((hWeq i).eq_of_nhds.trans (Work.Diff.GE.smoothExt_apply _ _).symm)
      ((hWeq j).eq_of_nhds.trans (Work.Diff.GE.smoothExt_apply _ _).symm)
      ((hWeq k).eq_of_nhds.trans (Work.Diff.GE.smoothExt_apply _ _).symm)
      ((hWeq l).eq_of_nhds.trans (Work.Diff.GE.smoothExt_apply _ _).symm)
  rw [hgerm, hval]
  -- the evaluation bound
  have hb := hCe' m hm (G t) (Work.Diff.EXT.pt (I := I) x₀ y)
    (fun s => Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
    (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
    (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))
    (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y))
    (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y))
  refine le_trans hb ?_
  -- each `sqrt` factor is bounded by `S`
  have hSle : ∀ (a : Fin (Module.finrank ℝ E)),
      Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ a (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ a (Work.Diff.EXT.pt (I := I) x₀ y))) ≤ S :=
    fun a => le_trans (Real.sqrt_le_sqrt (hD t ht a y hy)) hsqrtD
  have hprod : Finset.univ.prod (fun s : Fin m => Real.sqrt ((G t).inner
      (Work.Diff.EXT.pt (I := I) x₀ y)
      (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
      (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y)))) ≤ S ^ m := by
    rw [show S ^ m = Finset.univ.prod (fun _ : Fin m => S) by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    exact Finset.prod_le_prod₀ (fun s _ => Real.sqrt_nonneg _) (fun s _ => hSle (v s))
  have hCrb : Real.sqrt (Work.Diff.EXT.curvNormK (G t) (Work.Diff.EXT.pt (I := I) x₀ y) m)
      ≤ Real.sqrt (max Cr 0) := Real.sqrt_le_sqrt (le_trans (hCr m hm t ht _) (le_max_left _ _))
  have hfive : Finset.univ.prod (fun s : Fin m => Real.sqrt ((G t).inner
        (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))))
      * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)))
      * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y)))
      * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y)))
      * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y))) ≤ S ^ (m + 4) := by
    have h2 : Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))) ≤ S := hSle i
    have h3 : Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))) ≤ S := hSle j
    have h4 : Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y))) ≤ S := hSle k
    have h5 : Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y))) ≤ S := hSle l
    have hp1 : Finset.univ.prod (fun s : Fin m => Real.sqrt ((G t).inner
          (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))))
        * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)))
        ≤ S ^ m * S := mul_le_mul hprod h2 (Real.sqrt_nonneg _) (pow_nonneg hS0 m)
    have hp2 : Finset.univ.prod (fun s : Fin m => Real.sqrt ((G t).inner
          (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))))
        * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)))
        * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y)))
        ≤ S ^ m * S * S := mul_le_mul hp1 h3 (Real.sqrt_nonneg _) (by positivity)
    have hp3 : Finset.univ.prod (fun s : Fin m => Real.sqrt ((G t).inner
          (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))))
        * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)))
        * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y)))
        * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y)))
        ≤ S ^ m * S * S * S := mul_le_mul hp2 h4 (Real.sqrt_nonneg _) (by positivity)
    refine le_trans (mul_le_mul hp3 h5 (Real.sqrt_nonneg _) (by positivity)) (le_of_eq ?_)
    calc S ^ m * S * S * S * S = S ^ m * (S * S * S * S) := by ring
      _ = S ^ m * S ^ 4 := by ring
      _ = S ^ (m + 4) := by rw [← pow_add]
  have hpK : S ^ (m + 4) ≤ S ^ (K + 4) := pow_le_pow_right₀ hS1 (by omega)
  have hprod_all : Finset.univ.prod (fun s : Fin m => Real.sqrt ((G t).inner
        (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y))))
      * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)))
      * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y)))
      * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ k (Work.Diff.EXT.pt (I := I) x₀ y)))
      * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y)))
      ≤ S ^ (K + 4) := le_trans hfive hpK
  refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hCrb) hCe0) (by positivity)) ?_
  exact mul_le_mul_of_nonneg_left hprod_all (by positivity)


/-- **Uniform jet bounds for the chart recursion `tower3Arr`** from jet bounds of the base array
and of the background Christoffel symbols.  The jet order decreases by one at each recursion step,
so level `m` is bounded up to order `Mm - m`. -/
theorem tower3Arr_jets
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (K' : Set E) (Mm : ℕ) (hK't : K' ⊆ (extChartAt I x₀).target)
    (hA : ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ Mm → ∀ (i j' l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E => A y' i j' l) y‖ ≤ C)
    (hAsm : ∀ y ∈ K', ∀ (i j' l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => A y' i j' l) y)
    (hΓ : ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ Mm → ∀ (p a b : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
            (Work.Diff.EXT.pt (I := I) x₀ y') p a b) y‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ Mm → ∀ m : ℕ, m ≤ Mm - j →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j' l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E =>
            tower3Arr (I := I) (M := M) G x₀ t A m v i j' l y') y‖ ≤ C := by
  classical
  obtain ⟨Cd, hCd0, hCd⟩ := hA
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := hΓ
  have hΓsm : ∀ (p a b : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (Work.Diff.EXT.pt (I := I) x₀ y') p a b) y :=
    fun p a b y hy => Work.Diff.EXT.CBound.cGam_contDiffAt_of_target
      (I := I) (M := M) (G 0) x₀ (hK't hy) p a b
  -- smoothness of every level
  have hsm : ∀ m : ℕ, m ≤ Mm → ∀ (v : Fin m → Fin (Module.finrank ℝ E))
      (i j' l : Fin (Module.finrank ℝ E)) (y : E), y ∈ K' →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
        tower3Arr (I := I) (M := M) G x₀ t A m v i j' l y') y := by
    intro m
    induction m with
    | zero =>
        intro _ v i j' l y hy
        simpa only [tower3Arr_zero] using hAsm y hy i j' l
    | succ m ih =>
        intro hm v i j' l y hy
        rw [tower3Arr_succ]
        have ihn : ∀ (w : Fin m → Fin (Module.finrank ℝ E))
            (i' j'' l' : Fin (Module.finrank ℝ E)),
            ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
              tower3Arr (I := I) (M := M) G x₀ t A m w i' j'' l' y') y :=
          fun w i' j'' l' => ih (by omega) w i' j'' l' y hy
        have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
            fderiv ℝ (fun z : E => tower3Arr (I := I) (M := M) G x₀ t A m
              (fun s : Fin m => v s.succ) i j' l z) y' (Work.Diff.GE.cBasis (E := E) (v 0))) y :=
          Work.Diff.EXT.CBound.contDiffAt_fderiv_apply'
            (ihn (fun s : Fin m => v s.succ) i j' l)
        have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ r : Fin m,
              ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                  p (v r.succ) (v 0)
                  * tower3Arr (I := I) (M := M) G x₀ t A m
                      (Function.update (fun s : Fin m => v s.succ) r p) i j' l y') y := by
          refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin m))) fun r _ =>
            ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ =>
              ContDiffAt.mul (hΓsm p (v r.succ) (v 0) y hy)
                (ihn (Function.update (fun s : Fin m => v s.succ) r p) i j' l)
        have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
              ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i (v 0)
                  * tower3Arr (I := I) (M := M) G x₀ t A m
                      (fun s : Fin m => v s.succ) p j' l y') y := by
          refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ =>
            ContDiffAt.mul (hΓsm p i (v 0) y hy) (ihn (fun s : Fin m => v s.succ) p j' l)
        have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
              ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j' (v 0)
                  * tower3Arr (I := I) (M := M) G x₀ t A m
                      (fun s : Fin m => v s.succ) i p l y') y := by
          refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ =>
            ContDiffAt.mul (hΓsm p j' (v 0) y hy) (ihn (fun s : Fin m => v s.succ) i p l)
        have h5 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
              ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l (v 0)
                  * tower3Arr (I := I) (M := M) G x₀ t A m
                      (fun s : Fin m => v s.succ) i j' p y') y := by
          refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ =>
            ContDiffAt.mul (hΓsm p l (v 0) y hy) (ihn (fun s : Fin m => v s.succ) i j' p)
        exact (((h1.sub h2).sub h3).sub h4).sub h5
  -- the constants of the estimate
  set Kb : ℝ := max 1 (∑ a : Fin (Module.finrank ℝ E), ‖Work.Diff.GE.cBasis (E := E) a‖)
    with hKbdef
  have hKb0 : 0 ≤ Kb := le_trans zero_le_one (le_max_left _ _)
  have hKbnorm : ∀ a : Fin (Module.finrank ℝ E), ‖Work.Diff.GE.cBasis (E := E) a‖ ≤ Kb := fun a =>
    le_trans (Finset.single_le_sum (f := fun a : Fin (Module.finrank ℝ E) =>
        ‖Work.Diff.GE.cBasis (E := E) a‖) (fun a _ => norm_nonneg _) (Finset.mem_univ a))
      (le_max_right _ _)
  have key : ∀ m : ℕ, m ≤ Mm → ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ Mm - m →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j' l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E =>
          tower3Arr (I := I) (M := M) G x₀ t A m v i j' l y') y‖ ≤ C := by
    intro m
    induction m with
    | zero =>
        intro _
        refine ⟨Cd, hCd0, fun j hj v i j' l y hy => ?_⟩
        have hj' : j ≤ Mm := by simpa using hj
        simpa only [tower3Arr_zero] using hCd j hj' i j' l y hy
    | succ m ih =>
        intro hm
        obtain ⟨Cm, hCm0, hCm⟩ := ih (by omega : m ≤ Mm)
        set B : ℝ := max Cm CΓ with hBdef
        have hB0 : 0 ≤ B := le_trans hCm0 (le_max_left _ _)
        have hCmB : Cm ≤ B := le_max_left _ _
        have hCΓB : CΓ ≤ B := le_max_right _ _
        set P : ℝ := (2 : ℝ) ^ Mm * B * B with hPdef
        have hP0 : 0 ≤ P := by
          rw [hPdef]
          exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hB0) hB0
        set Ns : ℝ := (m : ℝ) * (Module.finrank ℝ E : ℝ)
          + 3 * (Module.finrank ℝ E : ℝ) with hNsdef
        have hNs0 : 0 ≤ Ns := by
          rw [hNsdef]; positivity
        have hNsn : (Module.finrank ℝ E : ℝ) ≤ Ns := by
          rw [hNsdef]
          nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
        have hNsmn : (m : ℝ) * (Module.finrank ℝ E : ℝ) ≤ Ns := by
          rw [hNsdef]
          nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
        refine ⟨Kb * Cm + 4 * (Ns * P), by positivity, fun j hj v i j' l y hy => ?_⟩
        have hjMm : j ≤ Mm := by omega
        have hj1 : j + 1 ≤ Mm - m := by omega
        have hjCm : j ≤ Mm - m := by omega
        -- the two pieces of one recursion step
        set F : E → ℝ := fun y' : E => fderiv ℝ (fun z : E =>
            tower3Arr (I := I) (M := M) G x₀ t A m (fun s : Fin m => v s.succ) i j' l z)
          y' (Work.Diff.GE.cBasis (E := E) (v 0)) with hFdef
        set S1 : E → ℝ := fun y' : E => ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p (v r.succ) (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t A m
                    (Function.update (fun s : Fin m => v s.succ) r p) i j' l y' with hS1def
        set S2 : E → ℝ := fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t A m
                    (fun s : Fin m => v s.succ) p j' l y' with hS2def
        set S3 : E → ℝ := fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j' (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t A m
                    (fun s : Fin m => v s.succ) i p l y' with hS3def
        set S4 : E → ℝ := fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t A m
                    (fun s : Fin m => v s.succ) i j' p y' with hS4def
        have hrec : (fun y' : E => tower3Arr (I := I) (M := M) G x₀ t A (m + 1) v i j' l y')
            = fun y' : E => F y' - S1 y' - S2 y' - S3 y' - S4 y' := by
          funext y'
          simp only [tower3Arr_succ, hFdef, hS1def, hS2def, hS3def, hS4def]
        -- a single-product bound for the correction summands
        have hprod : ∀ (p q : Fin (Module.finrank ℝ E)) (w : Fin m → Fin (Module.finrank ℝ E))
            (i' j'' l' : Fin (Module.finrank ℝ E)),
            ‖iteratedFDeriv ℝ j (fun y' : E =>
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p q (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t A m w i' j'' l' y') y‖ ≤ P := by
          intro p q w i' j'' l'
          refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_mul_le_at_le (k := j) (m := j) (B := B)
            le_rfl (hΓsm p q (v 0) y hy) (hsm m (by omega) w i' j'' l' y hy) hB0 ?_ ?_) ?_
          · intro i hi
            exact le_trans (hCΓ i (le_trans hi hjMm) p q (v 0) y hy) hCΓB
          · intro i hi
            exact le_trans (hCm i (le_trans hi hjCm) w i' j'' l' y hy) hCmB
          · rw [hPdef]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjMm) hB0) hB0
        -- the bound for a sum of `n` summands each bounded by `P`
        have hsingle : ∀ (ψ : Fin (Module.finrank ℝ E) → E → ℝ),
            (∀ p, ContDiffAt ℝ (⊤ : ℕ∞) (ψ p) y) →
            (∀ p, ‖iteratedFDeriv ℝ j (ψ p) y‖ ≤ P) →
            ‖iteratedFDeriv ℝ j (fun y' : E => ∑ p : Fin (Module.finrank ℝ E), ψ p y') y‖
              ≤ (Module.finrank ℝ E : ℝ) * P := by
          intro ψ hψ hψb
          refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_sum_le_at
            (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (φ := ψ) (x := y) (n := j)
            (C := P) (fun p _ => hψ p) (fun p _ => hψb p)) ?_
          refine le_of_eq ?_
          rw [Finset.card_univ, Fintype.card_fin]
        have hb1 : ‖iteratedFDeriv ℝ j S1 y‖ ≤ Ns * P := by
          rw [hS1def]
          refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_sum_le_at
            (s := (Finset.univ : Finset (Fin m)))
            (φ := fun r y' => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p (v r.succ) (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t A m
                    (Function.update (fun s : Fin m => v s.succ) r p) i j' l y')
            (x := y) (n := j) (C := (Module.finrank ℝ E : ℝ) * P) ?_ ?_) ?_
          · intro r _
            exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
              fun p _ => ContDiffAt.mul (hΓsm p (v r.succ) (v 0) y hy)
                (hsm m (by omega) (Function.update (fun s : Fin m => v s.succ) r p) i j' l y hy)
          · intro r _
            exact le_trans (hsingle
              (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                  p (v r.succ) (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t A m
                    (Function.update (fun s : Fin m => v s.succ) r p) i j' l y')
              (fun p => ContDiffAt.mul (hΓsm p (v r.succ) (v 0) y hy)
                (hsm m (by omega) (Function.update (fun s : Fin m => v s.succ) r p) i j' l y hy))
              (fun p => hprod p (v r.succ) (Function.update (fun s : Fin m => v s.succ) r p)
                i j' l)) (by
                nlinarith [hNsmn, hP0, hNs0])
          · have hcard : ((Finset.univ : Finset (Fin m)).card : ℝ) = (m : ℝ) := by
              rw [Finset.card_univ, Fintype.card_fin]
            rw [hcard]
            nlinarith [hNsmn, hP0, hNs0]
        have hb2 : ‖iteratedFDeriv ℝ j S2 y‖ ≤ Ns * P := by
          rw [hS2def]
          refine le_trans (hsingle
            (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i (v 0)
              * tower3Arr (I := I) (M := M) G x₀ t A m
                  (fun s : Fin m => v s.succ) p j' l y')
            (fun p => ContDiffAt.mul (hΓsm p i (v 0) y hy)
              (hsm m (by omega) (fun s : Fin m => v s.succ) p j' l y hy))
            (fun p => hprod p i (fun s : Fin m => v s.succ) p j' l)) ?_
          nlinarith [hNsn, hP0, hNs0]
        have hb3 : ‖iteratedFDeriv ℝ j S3 y‖ ≤ Ns * P := by
          rw [hS3def]
          refine le_trans (hsingle
            (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j' (v 0)
              * tower3Arr (I := I) (M := M) G x₀ t A m
                  (fun s : Fin m => v s.succ) i p l y')
            (fun p => ContDiffAt.mul (hΓsm p j' (v 0) y hy)
              (hsm m (by omega) (fun s : Fin m => v s.succ) i p l y hy))
            (fun p => hprod p j' (fun s : Fin m => v s.succ) i p l)) ?_
          nlinarith [hNsn, hP0, hNs0]
        have hb4 : ‖iteratedFDeriv ℝ j S4 y‖ ≤ Ns * P := by
          rw [hS4def]
          refine le_trans (hsingle
            (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l (v 0)
              * tower3Arr (I := I) (M := M) G x₀ t A m
                  (fun s : Fin m => v s.succ) i j' p y')
            (fun p => ContDiffAt.mul (hΓsm p l (v 0) y hy)
              (hsm m (by omega) (fun s : Fin m => v s.succ) i j' p y hy))
            (fun p => hprod p l (fun s : Fin m => v s.succ) i j' p)) ?_
          nlinarith [hNsn, hP0, hNs0]
        -- the smoothness of the two pieces
        have hFsm : ContDiffAt ℝ (⊤ : ℕ∞) F y := by
          rw [hFdef]
          exact Work.Diff.EXT.CBound.contDiffAt_fderiv_apply'
            (hsm m (by omega) (fun s : Fin m => v s.succ) i j' l y hy)
        have hS1sm : ContDiffAt ℝ (⊤ : ℕ∞) S1 y := by
          rw [hS1def]
          refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin m))) fun r _ =>
            ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ =>
              ContDiffAt.mul (hΓsm p (v r.succ) (v 0) y hy)
                (hsm m (by omega) (Function.update (fun s : Fin m => v s.succ) r p) i j' l y hy)
        have hS2sm : ContDiffAt ℝ (⊤ : ℕ∞) S2 y := by
          rw [hS2def]
          refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ =>
            ContDiffAt.mul (hΓsm p i (v 0) y hy)
              (hsm m (by omega) (fun s : Fin m => v s.succ) p j' l y hy)
        have hS3sm : ContDiffAt ℝ (⊤ : ℕ∞) S3 y := by
          rw [hS3def]
          refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ =>
            ContDiffAt.mul (hΓsm p j' (v 0) y hy)
              (hsm m (by omega) (fun s : Fin m => v s.succ) i p l y hy)
        have hS4sm : ContDiffAt ℝ (⊤ : ℕ∞) S4 y := by
          rw [hS4def]
          refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ =>
            ContDiffAt.mul (hΓsm p l (v 0) y hy)
              (hsm m (by omega) (fun s : Fin m => v s.succ) i j' p y hy)
        -- the `fderiv` term
        have hFb : ‖iteratedFDeriv ℝ j F y‖ ≤ Kb * Cm := by
          rw [hFdef]
          refine le_trans (Work.Diff.EXT.ConnCov.norm_iteratedFDeriv_fderiv_apply_le
            (ψ := fun z : E => tower3Arr (I := I) (M := M) G x₀ t A m
              (fun s : Fin m => v s.succ) i j' l z)
            (y := y) (ζ := Work.Diff.GE.cBasis (E := E) (v 0)) (j := j) ?_) ?_
          · exact hsm m (by omega) (fun s : Fin m => v s.succ) i j' l y hy
          · exact mul_le_mul (hKbnorm (v 0))
              (hCm (j + 1) hj1 (fun s : Fin m => v s.succ) i j' l y hy) (norm_nonneg _) hKb0
        -- assemble
        rw [hrec]
        have hsplit : (fun y' : E => F y' - S1 y' - S2 y' - S3 y' - S4 y')
            = fun y' : E => F y' + (-(S1 + S2 + S3 + S4) y') := by
          funext y'; simp only [Pi.add_apply]; ring
        rw [hsplit]
        refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := F)
          (g := fun y' : E => -(S1 + S2 + S3 + S4) y') (C := Kb * Cm) (D := 4 * (Ns * P))
          hFsm ((((hS1sm.add hS2sm).add hS3sm).add hS4sm).neg) hFb ?_) ?_
        · have h1 : ‖iteratedFDeriv ℝ j (S1 + S2 + S3 + S4) y‖ ≤ 4 * (Ns * P) := by
            have h12 : ‖iteratedFDeriv ℝ j (S1 + S2) y‖ ≤ Ns * P + Ns * P :=
              Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := S1) (g := S2)
                (C := Ns * P) (D := Ns * P) hS1sm hS2sm hb1 hb2
            have h123 : ‖iteratedFDeriv ℝ j (S1 + S2 + S3) y‖ ≤ Ns * P + Ns * P + Ns * P :=
              Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := S1 + S2) (g := S3)
                (C := Ns * P + Ns * P) (D := Ns * P) (hS1sm.add hS2sm) hS3sm h12 hb3
            have h1234 : ‖iteratedFDeriv ℝ j (S1 + S2 + S3 + S4) y‖
                ≤ Ns * P + Ns * P + Ns * P + Ns * P :=
              Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := S1 + S2 + S3) (g := S4)
                (C := Ns * P + Ns * P + Ns * P) (D := Ns * P)
                ((hS1sm.add hS2sm).add hS3sm) hS4sm h123 hb4
            refine le_trans h1234 ?_
            linarith [hNs0, hP0]
          have h2 : (fun y' : E => -(S1 + S2 + S3 + S4) y')
              = -(S1 + S2 + S3 + S4) := rfl
          rw [h2, iteratedFDeriv_neg]
          simpa using h1
        · linarith [hNs0, hP0]
  obtain ⟨Ck, hCk0, hCk⟩ := Work.Diff.EXT.exists_uniform_bound_of_le
    (P := fun m C => ∀ j : ℕ, j ≤ Mm - m →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j' l : Fin (Module.finrank ℝ E)),
        ∀ y ∈ K', ‖iteratedFDeriv ℝ j (fun y' : E =>
          tower3Arr (I := I) (M := M) G x₀ t A m v i j' l y') y‖ ≤ C)
    (fun m C C' h hle j hj v i j' l y hy => le_trans (h j hj v i j' l y hy) hle) Mm
    (fun m hm => key m hm)
  exact ⟨Ck, hCk0, fun j hj m hmj v i j' l y hy => hCk m (by omega) j (by omega) v i j' l y hy⟩

/-- **The values of the chart curvature-tower levels are bounded from Shi's estimate.**  This is the
`hval`-hypothesis of `Work.Diff.EXT.ConnCov.rmChartTower_jets`, obtained from the bridge
`rmChartTower_eq_covKRmExt` (the chart recursion computes `covKRmExt` on the coordinate frame) and
the proved `covKRmExt_frame_bound` (which converts `hShi` into a bound for the coordinate-frame
components), the diagonal Gram bound being supplied by `gramDiag_bound`. -/
theorem rmChartTower_value_bound
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (K : ℕ) (x₀ : M) (K' : Set E) (hK'c : IsCompact K')
    (hK't : K' ⊆ (extChartAt I x₀).target) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ K →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        |rmChartTower (I := I) (M := M) G x₀ t m v i j k l y| ≤ Cv := by
  obtain ⟨D, hD0, hD⟩ := gramDiag_bound (I := I) (M := M) G T C hT hC hmet x₀ K' hK'c hK't
  obtain ⟨Ck, hCk0, hCk⟩ := covKRmExt_frame_bound (I := I) (M := M) hLC G T C hT hC hflow
    hbound hShi K x₀ K' hK'c hK't ⟨D, hD0, hD⟩
  refine ⟨Ck, hCk0, fun t ht m hm v i j k l y hy => ?_⟩
  rw [rmChartTower_eq_covKRmExt (I := I) (M := M) hLC G x₀ t m v i j k l (hK't hy)]
  exact hCk t ht y hy m hm v i j k l

end Helpers

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT.ATower

theorem dAOfTower_chart_bound
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
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (K : ℕ) (x₀ : M) (K' : Set E) (hK'c : IsCompact K')
    (hK't : K' ⊆ (extChartAt I x₀).target)
    (hcomp : ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ K →
      ∀ (i j l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ Ca)
    (hjet : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ K + 1 →
      ∀ (i j : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ Cg) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T,
      ∀ y ∈ K', ∀ (v : Fin K → Fin (Module.finrank ℝ E))
        (i j l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.dAOfBase G t) K
            (fun s : Fin K => Work.Diff.GE.cFrame (I := I) x₀ (v s))
            (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
            (Work.Diff.GE.cFrame (I := I) x₀ l) (Work.Diff.EXT.pt (I := I) x₀ y)| ≤ Ck := by
  classical
  -- **The joint smoothness of the chart array of the connection difference.**
  have hjA : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun p : ℝ × E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ p.1 p.2 i j l) (t, y) :=
    aComp_jointSmooth_of_flow (I := I) (M := M) G T hT hflow x₀ K' hK't
  -- **Step 1: the chart jets of the curvature array `rmChartExpr` up to order `K + 1`.**
  -- The chart recursion of the moving curvature tower bounds its own value levels (`hval`) and the
  -- level of the Christoffel symbols is only needed one order down (`hchr`).
  obtain ⟨Crm, hCrm0, hCrm⟩ := rmChartTower_jets_weak (I := I) (M := M) G x₀ (T / 2) T K' (K + 1)
    hK't
    (rmChartTower_value_bound (I := I) (M := M) hLC G T C hT hC hflow hbound hmet hShi
      (K := K + 1) x₀ K' hK'c hK't)
    (chrCoord_jets_bound (I := I) (M := M) G T C hT hC hmet K x₀ K' hK'c hK't hjet)
    ((chartData_smooth_on_slab (I := I) (M := M) G (T / 2) T (K + 1) x₀ K' hK't hjA).1)
  -- Level `0` of the chart recursion *is* `rmChartExpr` (`rmChartTower_zero`).
  have hrm : ∃ Crm' : ℝ, 0 ≤ Crm' ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ J : ℕ, J ≤ K + 1 →
      ∀ (i j' k l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ J (fun y' : E => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j' k l t
            (Work.Diff.EXT.pt (I := I) x₀ y')) y‖ ≤ Crm' := by
    refine ⟨Crm, hCrm0, fun t ht J hJ i j' k l y hy => ?_⟩
    have hz : (fun y' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t 0
          (Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) i j' k l y')
        = (fun y' : E => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j' k l t
            (Work.Diff.EXT.pt (I := I) x₀ y')) := by
      funext y'
      rw [rmChartTower_zero]
    rw [← hz]
    exact hCrm t ht J hJ 0 (Nat.zero_le _)
      (Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) i j' k l y hy
  -- **Step 2: the chart jets of the reaction array `reactArr` up to order `K`.**
  obtain ⟨Cd, hCd0, hCd⟩ := reactArr_jets (I := I) (M := M) hLC G T C hT hC hflow hbound hmet
    hShi K x₀ K' hK'c hK't hrm hjet hcomp
  -- **Step 3: smoothness of the components of `reactArr` in the chart variable.**
  have hsma := (chartData_smooth_on_slab (I := I) (M := M) G (T / 2) T K x₀ K' hK't hjA).2
  -- **Step 4: the jets of the background Christoffel symbols, uniformly in the order.**
  have hΓ : ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ K →
      ∀ (p a b : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
            (Work.Diff.EXT.pt (I := I) x₀ y') p a b) y‖ ≤ C :=
    Work.Diff.EXT.exists_uniform_bound_of_le
      (P := fun j C => ∀ (p a b : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
            (Work.Diff.EXT.pt (I := I) x₀ y') p a b) y‖ ≤ C)
      (fun j C C' h hle p a b y hy => le_trans (h p a b y hy) hle) K
      (fun j _ => by
        obtain ⟨C, hC0, hC⟩ :=
          Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound (I := I) (M := M) G x₀ K' hK'c hK't j
        exact ⟨C, hC0, fun p a b y hy => hC y hy a b p⟩)
  -- **Step 5: the uniform jet bound of the chart tower of the reaction array.**
  obtain ⟨Ck, hCk0, hCk⟩ := tower3Arr_jets_family (I := I) (M := M) G x₀ (T / 2) T
    (reactArr (I := I) (M := M) G x₀) K' K hK't ⟨Cd, hCd0, hCd⟩ hsma hΓ
  refine ⟨Ck, hCk0, fun t ht y hy v i j l => ?_⟩
  -- **Step 6: the identification of the target's tower with the chart tower of the reaction
  -- array.**  It goes through the chart arrays: the `∇^{G 0}`-tower of `dAOfBase` is the
  -- `t`-derivative of the `∇^{G 0}`-tower of `aOf` (Clairaut in time), and the latter is the chart
  -- recursion `aCovArr`, whose `t`-derivative is the chart tower of `reactArr = ∂_t aComp`.
  have hyT : y ∈ (extChartAt I x₀).target := hK't hy
  have htIoo : t ∈ Set.Ioo 0 T := ⟨by linarith [ht.1, hT], ht.2⟩
  -- a globally smooth field agreeing with each frame vector near the base point
  have hpsrc : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source := by
      have hmem : (extChartAt I x₀).symm y ∈
          (extChartAt I x₀).symm '' (extChartAt I x₀).target := Set.mem_image_of_mem _ hyT
      rwa [PartialEquiv.symm_image_target_eq_source] at hmem
    have h2 : (extChartAt I x₀).source = (chartAt H x₀).source := extChartAt_source I x₀
    show (extChartAt I x₀).symm y ∈ (chartAt H x₀).source
    rw [← h2]
    exact h1
  have hYex : ∀ a : Fin (Module.finrank ℝ E), ∃ Z : Π y : M, TangentSpace I y,
      SmE I M Z ∧ Z =ᶠ[𝓝 (Work.Diff.EXT.pt (I := I) x₀ y)] Work.Diff.GE.cFrame (I := I) x₀ a := by
    intro a
    obtain ⟨Z, hZsm, hZeq⟩ := Work.Diff.T.exists_global_eventuallyEq_symmL (I := I) x₀
      (Work.Diff.GE.cBasis (E := E) a) hpsrc
    refine ⟨Z, hZsm, ?_⟩
    exact hZeq
  choose Y hYsm hYeq using hYex
  -- the pointwise smooth extensions of the frame vectors at the base point
  let Vs : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y) := fun a =>
    Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
      (Work.Diff.GE.cFrame (I := I) x₀ a (Work.Diff.EXT.pt (I := I) x₀ y))
  have hVssm : ∀ a, SmE I M (Vs a) := fun a => Work.Diff.GE.smoothExt_cmdiff _ _
  have hYval : ∀ a, Y a (Work.Diff.EXT.pt (I := I) x₀ y)
      = Vs a (Work.Diff.EXT.pt (I := I) x₀ y) := by
    intro a
    show Y a (Work.Diff.EXT.pt (I := I) x₀ y) = Submission.Diff.smoothExt
      (Work.Diff.EXT.pt (I := I) x₀ y)
      (Work.Diff.GE.cFrame (I := I) x₀ a (Work.Diff.EXT.pt (I := I) x₀ y))
      (Work.Diff.EXT.pt (I := I) x₀ y)
    rw [Work.Diff.GE.smoothExt_apply]
    exact (hYeq a).eq_of_nhds
  -- (a) germ-locality of the tower of `dAOfBase` in its slots
  have hStepA : tower (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.dAOfBase G t) K
        (fun s : Fin K => Work.Diff.GE.cFrame (I := I) x₀ (v s))
        (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
        (Work.Diff.GE.cFrame (I := I) x₀ l) (Work.Diff.EXT.pt (I := I) x₀ y)
      = tower (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.dAOfBase G t) K
        (fun s : Fin K => Y (v s)) (Y i) (Y j) (Y l) (Work.Diff.EXT.pt (I := I) x₀ y) :=
    tower_dAOfBase_congr_germ (I := I) (M := M) G t K
      (fun s : Fin K => Work.Diff.GE.cFrame (I := I) x₀ (v s)) (fun s : Fin K => Y (v s))
      (Work.Diff.GE.cFrame (I := I) x₀ i) (Y i)
      (Work.Diff.GE.cFrame (I := I) x₀ j) (Y j)
      (Work.Diff.GE.cFrame (I := I) x₀ l) (Y l)
      (Work.Diff.EXT.pt (I := I) x₀ y)
      (fun s => (hYeq (v s)).symm) ((hYeq i).symm) ((hYeq j).symm) ((hYeq l).symm)
  -- (b) value dependence of the tower on smooth fields
  have hStepB : tower (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.dAOfBase G t) K
        (fun s : Fin K => Y (v s)) (Y i) (Y j) (Y l) (Work.Diff.EXT.pt (I := I) x₀ y)
      = tower (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.dAOfBase G t) K
        (fun s : Fin K => Vs (v s)) (Vs i) (Vs j) (Vs l) (Work.Diff.EXT.pt (I := I) x₀ y) :=
    dAOf_tower_val_dep (I := I) (M := M) hLC hflow htIoo K (Work.Diff.EXT.pt (I := I) x₀ y)
      (fun s : Fin K => Y (v s)) (fun s : Fin K => Vs (v s))
      (Y i) (Vs i) (Y j) (Vs j) (Y l) (Vs l)
      (fun s => hYsm (v s)) (fun s => hVssm (v s))
      (hYsm i) (hVssm i) (hYsm j) (hVssm j) (hYsm l) (hVssm l)
      (fun s => hYval (v s)) (hYval i) (hYval j) (hYval l)
  -- (c) Clairaut in time: the tower of `dAOfBase` is the `t`-derivative of the tower of `aOf`
  have hStepC : tower (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.dAOfBase G t) K
        (fun s : Fin K => Vs (v s)) (Vs i) (Vs j) (Vs l) (Work.Diff.EXT.pt (I := I) x₀ y)
      = deriv (fun s : ℝ => tower (Submission.Diff.lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G s) K
          (fun s' : Fin K => Vs (v s')) (Vs i) (Vs j) (Vs l)
          (Work.Diff.EXT.pt (I := I) x₀ y)) t :=
    tower_dAOfBase_eq_deriv (I := I) (M := M) hLC hflow htIoo K
      (fun s' : Fin K => Vs (v s')) (Vs i) (Vs j) (Vs l)
      (fun s' => hVssm (v s')) (hVssm i) (hVssm j) (hVssm l) (Work.Diff.EXT.pt (I := I) x₀ y)
  -- (d) the frozen tower of `aOf` is `covKAExt`
  have hStepD : deriv (fun s : ℝ => tower (Submission.Diff.lcOf (G 0))
        (fun _ => Work.Diff.EXT.aOf G s) K (fun s' : Fin K => Vs (v s')) (Vs i) (Vs j) (Vs l)
        (Work.Diff.EXT.pt (I := I) x₀ y)) t
      = deriv (fun s : ℝ => covKAExt G s K (fun s' : Fin K => Vs (v s')) (Vs i) (Vs j) (Vs l)
          (Work.Diff.EXT.pt (I := I) x₀ y)) t := by
    have hfun : (fun s : ℝ => tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G s) K (fun s' : Fin K => Vs (v s')) (Vs i) (Vs j) (Vs l)
          (Work.Diff.EXT.pt (I := I) x₀ y))
        = (fun s : ℝ => covKAExt G s K (fun s' : Fin K => Vs (v s')) (Vs i) (Vs j) (Vs l)
            (Work.Diff.EXT.pt (I := I) x₀ y)) := by
      funext s
      rw [tower_eq_covKAExt]
    rw [hfun]
  -- (e) the frame fields and their pointwise smooth extensions agree in the value
  have hStepE : (fun s : ℝ => covKAExt G s K (fun s' : Fin K => Vs (v s')) (Vs i) (Vs j) (Vs l)
        (Work.Diff.EXT.pt (I := I) x₀ y))
      = fun s : ℝ => aCovArr G x₀ s K v i j l y := by
    funext s
    exact (Work.Diff.EXT.covKAExt_frame_eq_smoothExt (I := I) (M := M) hLC G s K x₀ hyT
        v i j l).symm.trans (aCovArr_eq_covKAExt (I := I) (M := M) G x₀ s K v i j l hyT).symm
  -- (f) the `t`-derivative of the chart recursion is the chart tower of the reaction array
  have hStepF : deriv (fun s : ℝ => aCovArr G x₀ s K v i j l y) t
      = tower3Arr (I := I) (M := M) G x₀ t (reactArr (I := I) (M := M) G x₀ t) K v i j l y := by
    have h1 : (fun s : ℝ => aCovArr G x₀ s K v i j l y)
        = fun s : ℝ => tower3Arr (I := I) (M := M) G x₀ s
            (aCompArr (I := I) (M := M) G x₀ s) K v i j l y := by
      funext s
      rw [congrFun (aCovArr_eq_tower3Arr (I := I) (M := M) G x₀ s K v i j l) y]
    rw [h1]
    exact (tower3Arr_aCompArr_deriv_time (I := I) (M := M) G x₀ (t := t) (y := y) hyT
      (fun i j l => hjA t ht y hy i j l) K v i j l).deriv
  -- assembly
  have hchain : tower (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.dAOfBase G t) K
        (fun s : Fin K => Work.Diff.GE.cFrame (I := I) x₀ (v s))
        (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
        (Work.Diff.GE.cFrame (I := I) x₀ l) (Work.Diff.EXT.pt (I := I) x₀ y)
      = tower3Arr (I := I) (M := M) G x₀ t (reactArr (I := I) (M := M) G x₀ t) K v i j l y := by
    rw [hStepA, hStepB, hStepC, hStepD, hStepE]
    exact hStepF
  rw [hchain]
  have hb := hCk t ht 0 (Nat.zero_le K) K (by omega) v i j l y hy
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb

end Work.Diff.EXT.ConnCov
