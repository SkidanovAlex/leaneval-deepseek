import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ConnCov.aCovArr_bound_of_jets
import Submission.Work.Diff.EXT.ConnCov.cktA_expand
import Submission.Work.Diff.EXT.ConnCov.aCovArr_compact_bound
import Submission.Work.Diff.EXT.aCovArr_eq_covKAExt
import Submission.Work.Diff.EXT.covKAExt_frame_eq_smoothExt
import Submission.Work.Diff.EXT.chartMat_uniform_ell
import Submission.Work.Diff.EXT.sum_chartMatFun_eq_inner

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The fixed-time slice bound for the `∇^{G 0}`-tower of the connection difference

Target: `Work.Diff.EXT.ConnCov.covKAExt_bound_sliceT`.  For the single time `t = T/2` and every `k`
there is `Ck ≥ 0` with

`|∇^{G 0, k} aOf(T/2)(v, a, b, c)| ≤ Ck · ∏ √⟨vᵢ,vᵢ⟩ · √⟨a,a⟩ · √⟨b,b⟩ · √⟨c,c⟩`,

uniformly in the point and in the vectors, the norms being taken with respect to the metric
`G (T/2)` itself.

## Route (self-contained; only the smoothness of the fixed metric `G (T/2)` is used)

* At the chart centre `x₀`, the chart matrix `chartMatFun (G (T/2)) x₀` is (uniformly) positive
  definite on a small ball around the chart coordinate of `x₀` (`chartMatFun_posDef_nhds`), and the
  chart recursion `aCovArr G x₀ (T/2) k` is bounded on the corresponding compact set
  (`aCovArr_compact_bound`, a corollary of the smoothness of `aCovArr` in the chart coordinate).
* For a point `y` in the chart, every tangent vector `q` is a linear combination
  `q = ∑ᵢ λᵢ • σᵢ` of the coordinate frame `σᵢ = cFrame x₀ i y`, with coefficients
  `λᵢ = (bB.coord i) ((trivializationAt … x₀).continuousLinearMapAt ℝ y q)`; the quadratic form of
  the chart matrix is `⟨q,q⟩` (`sum_chartMatFun_eq_inner`), so the uniform positive definiteness
  bounds `∑ᵢ |λᵢ| ≤ √(n/δ) · √⟨q,q⟩` (Cauchy–Schwarz, `frameCoord_bound_local`).
* The value of the tower at `y` is determined by the point values of its arguments
  (`ka_val_dep_all`), so expanding every slot in the frame gives, through the chart recursion
  (`aCovArr_eq_covKAExt`, `cktA_expand`, `ka_locAt`), the sum over all index functions of the
  products of the coefficients times the bounded chart components.
* The passage from each chart centre to the whole manifold is compactness
  (`CompactSpace.elim_nhds_subcover`).

Note that none of `hflow`, `hbound`, `hmet` (nor `hC`) is needed: the statement is a statement about
the single smooth metric `G (T/2)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Toolbox -/

/-- A finite combination of smooth tangent fields with constant coefficients is smooth. -/
private lemma smA_finset_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (Y : ι → TfA (I := I) (M := M)) (hY : ∀ p, SmA (I := I) (M := M) (Y p)) :
    SmA (I := I) (M := M) (fun z => ∑ p ∈ s, c p • Y p z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h : (fun z : M => ∑ p ∈ (∅ : Finset ι), c p • Y p z) = fun _ : M => 0 := by
        funext z; simp
      rw [h]
      exact contMDiff_zeroSection ℝ (fun x : M => TangentSpace I x) (IB := I)
  | insert a s ha ih =>
      have h1 : (fun z : M => ∑ p ∈ insert a s, c p • Y p z)
          = (fun z : M => c a • Y a z) + (fun z : M => ∑ p ∈ s, c p • Y p z) := by
        funext z; rw [Finset.sum_insert ha]; rfl
      rw [h1]
      exact (ContMDiff.smul_section (contMDiff_const (c := c a)) (hY a)).add_section ih

/-- The **frame coefficients** of a tangent vector: the coordinates of `v` in the coordinate frame
of the chart at `x₀` (the inverse of the tangent-bundle trivialisation at `x₀`). -/
private noncomputable def frameCoeff (x₀ : M) (p : M) (v : TangentSpace I p)
    (i : Fin (Module.finrank ℝ E)) : ℝ :=
  (Work.Diff.EXT.bB (E := E)).coord i
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p v)

/-- **The frame coefficients are dominated by the metric norm.**  If the chart matrix of `g` at the
chart coordinate `y` is positive definite with constant `δ`, then the sum of the absolute values of
the frame coefficients of any tangent vector `v` at `p = (extChartAt I x₀).symm y` is at most
`√(n/δ)` times the `g`-norm of `v`. -/
private lemma frameCoord_bound_local
    (g : Submission.Diff.SMet I M) (x₀ : M) (y : E)
    (hy : y ∈ (extChartAt I x₀).target)
    {δ : ℝ} (hδ : 0 < δ)
    (hell : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      δ * ∑ i, (w i) ^ 2
        ≤ ∑ i, ∑ j, w i * w j * Work.Diff.EXT.chartMatFun g x₀ y i j)
    (v : TangentSpace I ((extChartAt I x₀).symm y)) :
    (∑ i, |frameCoeff (I := I) x₀ ((extChartAt I x₀).symm y) v i|)
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) / δ)
          * Real.sqrt (g.inner ((extChartAt I x₀).symm y) v v) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hinner : ∀ (z : M) (u w : TangentSpace I z), g.inner z u w = inner ℝ u w :=
    fun z u w => rfl
  have hpsrc : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      PartialEquiv.map_target (extChartAt I x₀) hy
    rwa [extChartAt_source (I := I) x₀] at h1
  have hbase : (extChartAt I x₀).symm y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hpsrc
  have hsym : (trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm y)
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        ((extChartAt I x₀).symm y) v) = v :=
    Trivialization.symmL_continuousLinearMapAt _ hbase v
  set lam : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => frameCoeff (I := I) x₀ ((extChartAt I x₀).symm y) v i with hlam
  have hcrep : ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
      ((extChartAt I x₀).symm y) v)
      = ∑ i, lam i • Work.Diff.EXT.bB (E := E) i := by
    have hrepr := Module.Basis.sum_repr (Work.Diff.EXT.bB (E := E))
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        ((extChartAt I x₀).symm y) v)
    simp only [hlam, frameCoeff, Module.Basis.coord_apply]
    exact hrepr.symm
  have hv : v = ∑ i, lam i • Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y) := by
    rw [← hsym, hcrep, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
    rfl
  have hquad : ∑ i, ∑ j, lam i * lam j * Work.Diff.EXT.chartMatFun g x₀ y i j
      = g.inner ((extChartAt I x₀).symm y) v v := by
    have hsum : (∑ i, lam i • Submission.Geodesic.frameVector (I := I) x₀
          ((extChartAt I x₀).symm y) (Work.Diff.EXT.bB (E := E) i)) = v := by
      have h1 : (∑ i, lam i • Submission.Geodesic.frameVector (I := I) x₀
            ((extChartAt I x₀).symm y) (Work.Diff.EXT.bB (E := E) i))
          = ∑ i, lam i • Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Work.Diff.GE.cFrame_apply]
      rw [h1, hv]
    rw [Work.Diff.EXT.sum_chartMatFun_eq_inner (I := I) (M := M) g x₀ y lam, hsum]
  have hlow : δ * ∑ i, (lam i) ^ 2 ≤ g.inner ((extChartAt I x₀).symm y) v v := by
    rw [← hquad]; exact hell lam
  have hnn : 0 ≤ g.inner ((extChartAt I x₀).symm y) v v := by
    rw [hinner]; exact real_inner_self_nonneg
  have hsum2 : ∑ i, (lam i) ^ 2 ≤ (g.inner ((extChartAt I x₀).symm y) v v) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have hCS : ∑ i, |lam i| ≤ Real.sqrt (∑ i, (lam i) ^ 2)
      * Real.sqrt ((Module.finrank ℝ E : ℝ)) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun i => |lam i|) (fun _ => (1 : ℝ))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      sq_abs, one_pow] using h
  have hL : (∑ i, |frameCoeff (I := I) x₀ ((extChartAt I x₀).symm y) v i|) = ∑ i, |lam i| := by
    rw [hlam]
  rw [hL]
  refine le_trans hCS ?_
  have hs2 : Real.sqrt (∑ i, (lam i) ^ 2)
      ≤ Real.sqrt ((g.inner ((extChartAt I x₀).symm y) v v) / δ) :=
    Real.sqrt_le_sqrt hsum2
  calc Real.sqrt (∑ i, (lam i) ^ 2) * Real.sqrt ((Module.finrank ℝ E : ℝ))
      ≤ Real.sqrt ((g.inner ((extChartAt I x₀).symm y) v v) / δ)
          * Real.sqrt ((Module.finrank ℝ E : ℝ)) :=
        mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg _)
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) / δ)
          * Real.sqrt (g.inner ((extChartAt I x₀).symm y) v v) := by
        rw [Real.sqrt_div hnn δ, Real.sqrt_div (Nat.cast_nonneg _) δ]
        field_simp

/-- **The frame expansion of a tangent vector.**  If the globally smooth fields `Y i` agree with the
coordinate frame `cFrame x₀ i` near `y`, then the combination of the `Y i` with the frame
coefficients of `v` evaluates at `y` to `v`. -/
private lemma frame_expansion_of_global
    (x₀ y : M) (hy : y ∈ (chartAt H x₀).source)
    (Y : Fin (Module.finrank ℝ E) → TfA (I := I) (M := M))
    (hYeq : ∀ p, Y p =ᶠ[𝓝 y] Work.Diff.GE.cFrame (I := I) x₀ p)
    (v : TangentSpace I y) :
    (∑ p, frameCoeff (I := I) x₀ y v p • Y p) y = v := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hbase : y ∈ e.baseSet := by
    rw [he, TangentBundle.trivializationAt_baseSet]
    exact hy
  have hcoe : (∑ p, frameCoeff (I := I) x₀ y v p • e.symmL ℝ y (Work.Diff.EXT.bB (E := E) p))
      = e.symmL ℝ y (∑ p, frameCoeff (I := I) x₀ y v p • Work.Diff.EXT.bB (E := E) p) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun p _ => (map_smul _ _ _).symm)
  have hrepr : (∑ p, frameCoeff (I := I) x₀ y v p • Work.Diff.EXT.bB (E := E) p)
      = (e.continuousLinearMapAt ℝ y) v := by
    have hb := Module.Basis.sum_repr (Work.Diff.EXT.bB (E := E)) ((e.continuousLinearMapAt ℝ y) v)
    simp only [frameCoeff, Module.Basis.coord_apply]
    exact hb
  rw [Finset.sum_apply]
  have h1 : ∀ p : Fin (Module.finrank ℝ E), Y p y = e.symmL ℝ y (Work.Diff.EXT.bB (E := E) p) :=
    fun p => by rw [(hYeq p).eq_of_nhds]; rfl
  simp only [Pi.smul_apply, h1]
  rw [hcoe, hrepr]
  exact Trivialization.symmL_continuousLinearMapAt e hbase v

/-- The packing of `k` direction vectors and three value vectors into a `Fin (k+3)`-tuple. -/
private noncomputable def vecPackT {k : ℕ} {y : M} (v : Fin k → TangentSpace I y)
    (B : Fin 3 → TangentSpace I y) : Fin (k + 3) → TangentSpace I y :=
  Fin.addCases v B

private lemma vecPackT_castAdd {k : ℕ} {y : M} (v : Fin k → TangentSpace I y)
    (B : Fin 3 → TangentSpace I y) (i : Fin k) :
    vecPackT v B (Fin.castAdd 3 i) = v i := Fin.addCases_left i

private lemma vecPackT_natAdd {k : ℕ} {y : M} (v : Fin k → TangentSpace I y)
    (B : Fin 3 → TangentSpace I y) (p : Fin 3) :
    vecPackT v B (Fin.natAdd k p) = B p := Fin.addCases_right p

/-- Splitting a product over `Fin (k+3)` according to the packing. -/
private lemma prod_univ_vecPackT {k : ℕ} {y : M} (f : TangentSpace I y → ℝ)
    (v : Fin k → TangentSpace I y) (B : Fin 3 → TangentSpace I y) :
    (∏ s : Fin (k + 3), f (vecPackT v B s))
      = (∏ i : Fin k, f (v i)) * f (B 0) * f (B 1) * f (B 2) := by
  have hgen : (fun s : Fin (k + 3) => f (vecPackT v B s))
      = fun s : Fin (k + 3) => f (Fin.addCases v B s) := rfl
  rw [hgen, Fin.prod_univ_add (a := k) (b := 3)]
  have h1 : (∏ i : Fin k, f (Fin.addCases v B (Fin.castAdd 3 i))) = ∏ i : Fin k, f (v i) :=
    Finset.prod_congr rfl (fun i _ => by rw [Fin.addCases_left])
  have h2 : (∏ j : Fin 3, f (Fin.addCases v B (Fin.natAdd k j)))
      = f (B 0) * f (B 1) * f (B 2) := by
    rw [Fin.prod_univ_three]
    simp only [Fin.addCases_right]
  rw [h1, h2]
  ac_rfl

/-- The pointwise smooth extensions of a packed tuple of vectors form the `mkT3`-packing of the
pointwise smooth extensions of the parts. -/
private lemma smoothExt_vecPackT {k : ℕ} {y : M} (v : Fin k → TangentSpace I y)
    (B : Fin 3 → TangentSpace I y) :
    (fun s : Fin (k + 3) => Submission.Diff.smoothExt y (vecPackT v B s))
      = Work.Diff.EXT.mkT3 (fun i : Fin k => Submission.Diff.smoothExt y (v i))
          (fun p : Fin 3 => Submission.Diff.smoothExt y (B p)) := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [vecPackT_castAdd, Work.Diff.EXT.mkT3_castAdd]
  · intro p
    rw [vecPackT_natAdd, Work.Diff.EXT.mkT3_natAdd]

/-- The `mkT3`-packing of the coordinate frame along an index function is the coordinate frame
along that index function. -/
private lemma mkT3_cFrame (x₀ : M) {k : ℕ} (Q : Fin (k + 3) → Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.mkT3 (fun i : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (Q (Fin.castAdd 3 i)))
        (Work.Diff.EXT.trip3 (Work.Diff.GE.cFrame (I := I) x₀ (Q (Fin.natAdd k 0)))
          (Work.Diff.GE.cFrame (I := I) x₀ (Q (Fin.natAdd k 1)))
          (Work.Diff.GE.cFrame (I := I) x₀ (Q (Fin.natAdd k 2))))
      = fun q => Work.Diff.GE.cFrame (I := I) x₀ (Q q) := by
  funext q
  refine Fin.addCases (motive := fun q => Work.Diff.EXT.mkT3
      (fun i : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (Q (Fin.castAdd 3 i)))
      (Work.Diff.EXT.trip3 (Work.Diff.GE.cFrame (I := I) x₀ (Q (Fin.natAdd k 0)))
        (Work.Diff.GE.cFrame (I := I) x₀ (Q (Fin.natAdd k 1)))
        (Work.Diff.GE.cFrame (I := I) x₀ (Q (Fin.natAdd k 2)))) q
      = Work.Diff.GE.cFrame (I := I) x₀ (Q q)) ?_ ?_ q
  · intro i
    rw [Work.Diff.EXT.mkT3_castAdd]
  · intro p
    rw [Work.Diff.EXT.mkT3_natAdd]
    fin_cases p <;> rfl

/-- The sum over all index functions of the products of the coefficients is the product of the
sums. -/
private lemma sum_prod_eq_prod_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (f : ι → κ → ℝ) :
    (∑ Q : ι → κ, ∏ i, f i (Q i)) = ∏ i, ∑ j, f i j := by
  rw [← Fintype.piFinset_univ]
  exact Finset.sum_prod_piFinset (Finset.univ : Finset κ) f

/-! ## The chart-local bound -/

/-- **The `t = T/2` slice bound at a chart centre.**  For every point `x₀` there is a neighbourhood
on which the tower of the connection difference at time `T/2` is bounded by a constant times the
`G (T/2)`-norms of the arguments. -/
private theorem slice_local
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T) (k : ℕ) (x₀ : M) :
    ∃ V : Set M, V ∈ 𝓝 x₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ V, ∀ (v : Fin k → TangentSpace I y) (a b c : TangentSpace I y),
        |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (fun _ => Work.Diff.EXT.aOf G (T / 2)) k) y v a b c|
          ≤ C * (Finset.univ.prod (fun i : Fin k =>
                Real.sqrt ((G (T / 2)).inner y (v i) (v i))))
              * Real.sqrt ((G (T / 2)).inner y a a) * Real.sqrt ((G (T / 2)).inner y b b)
              * Real.sqrt ((G (T / 2)).inner y c c) := by
  classical
  -- uniform positive definiteness of the chart matrix near the chart centre
  obtain ⟨δ, hδpos, Uell, hUell_open, hUell_mem, hell⟩ :=
    Work.Diff.EXT.chartMatFun_posDef_nhds (I := I) (M := M) (G (T / 2)) x₀
  have hχt : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target :=
    PartialEquiv.map_source (extChartAt I x₀) (mem_extChartAt_source (I := I) x₀)
  obtain ⟨r, hrpos, hrsub⟩ : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((extChartAt I x₀) x₀) r ⊆ Uell ∩ (extChartAt I x₀).target := by
    have hmem : Uell ∩ (extChartAt I x₀).target ∈ 𝓝 ((extChartAt I x₀) x₀) :=
      (hUell_open.inter (isOpen_extChartAt_target (I := I) x₀)).mem_nhds ⟨hUell_mem, hχt⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨ε / 2, by linarith, (Metric.closedBall_subset_ball (by linarith)).trans hεsub⟩
  set K : Set E := Metric.closedBall ((extChartAt I x₀) x₀) r with hKdef
  have hKt : K ⊆ (extChartAt I x₀).target := fun z hz => (hrsub hz).2
  have hKell : ∀ z ∈ K, ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      δ * ∑ i, (w i) ^ 2
        ≤ ∑ i, ∑ j, w i * w j * Work.Diff.EXT.chartMatFun (G (T / 2)) x₀ z i j :=
    fun z hz w => hell z (hrsub hz).1 w
  have hKc : IsCompact K := isCompact_closedBall _ _
  obtain ⟨A, hA0, hAb⟩ := Work.Diff.EXT.ConnCov.aCovArr_compact_bound (I := I) (M := M)
    G x₀ (T / 2) k K hKc hKt
  refine ⟨(extChartAt I x₀) ⁻¹' (Metric.ball ((extChartAt I x₀) x₀) r) ∩ (chartAt H x₀).source,
    Filter.inter_mem ((continuousAt_extChartAt (I := I) x₀).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hrpos))
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)),
    A * (Real.sqrt ((Module.finrank ℝ E : ℝ) / δ)) ^ (k + 3), ?_, ?_⟩
  · exact mul_nonneg hA0 (pow_nonneg (Real.sqrt_nonneg _) _)
  · intro y hy v a b c
    obtain ⟨hyball, hysrc⟩ := hy
    have hyK : (extChartAt I x₀) y ∈ K := Metric.ball_subset_closedBall hyball
    have hyT : (extChartAt I x₀) y ∈ (extChartAt I x₀).target := hKt hyK
    have hpty : Work.Diff.EXT.pt (I := I) x₀ ((extChartAt I x₀) y) = y := by
      show (extChartAt I x₀).symm ((extChartAt I x₀) y) = y
      exact (extChartAt I x₀).left_inv (by rw [extChartAt_source (I := I) x₀]; exact hysrc)
    -- the global approximants of the coordinate frame
    have hYexists : ∀ i : Fin (Module.finrank ℝ E), ∃ Z : TfA (I := I) (M := M),
        SmA (I := I) (M := M) Z ∧ Z =ᶠ[𝓝 y] Work.Diff.GE.cFrame (I := I) x₀ i := by
      intro i
      obtain ⟨Z, hZsm, hZeq⟩ := Work.Diff.T.exists_global_eventuallyEq_symmL (I := I) x₀
        (Work.Diff.EXT.bB (E := E) i) hysrc
      exact ⟨Z, hZsm, hZeq⟩
    choose Y hYsm hYeq using hYexists
    -- the packed tuple of vectors and the frame coefficients
    set Bv : Fin 3 → TangentSpace I y := ![a, b, c] with hBv
    set pv : Fin (k + 3) → TangentSpace I y := vecPackT (I := I) v Bv with hpv
    set lam : Fin (k + 3) → Fin (Module.finrank ℝ E) → ℝ :=
      fun q i => frameCoeff (I := I) x₀ y (pv q) i with hlam
    -- the tuple of smooth extensions, and the frame combination tuple
    set F : Fin (k + 3) → TfA (I := I) (M := M) :=
      Work.Diff.EXT.mkT3 (fun i : Fin k => Submission.Diff.smoothExt y (v i))
        (fun p : Fin 3 => Submission.Diff.smoothExt y (Bv p)) with hF
    set Zt : Fin (k + 3) → TfA (I := I) (M := M) :=
      fun q => ∑ i, lam q i • Y i with hZt
    -- the point values
    have hFval : ∀ q, F q y = pv q := by
      intro q
      have h1 : F = fun s : Fin (k + 3) => Submission.Diff.smoothExt y (pv s) := by
        rw [hF, hpv]
        exact (smoothExt_vecPackT (I := I) (y := y) v Bv).symm
      simp only [h1, Work.Diff.GE.smoothExt_apply]
    have hZval : ∀ q, Zt q y = pv q := by
      intro q
      have h := frame_expansion_of_global (I := I) (M := M) x₀ y hysrc Y hYeq (pv q)
      have h2 : Zt q = ∑ i, frameCoeff (I := I) x₀ y (pv q) i • Y i := by
        rw [hZt, hlam]
      rw [h2]
      exact h
    -- smoothness
    have hFsm : ∀ q, SmA (I := I) (M := M) (F q) := by
      intro q
      rw [hF]
      exact Work.Diff.EXT.smA_mkT3 (fun i : Fin k => Work.Diff.GE.smoothExt_cmdiff y (v i))
        (fun p : Fin 3 => Work.Diff.GE.smoothExt_cmdiff y (Bv p)) q
    have hZsm : ∀ q, SmA (I := I) (M := M) (Zt q) := by
      intro q
      have h : Zt q = fun z : M => ∑ p ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          lam q p • Y p z := by
        funext z
        simp only [hZt, Finset.sum_apply, Pi.smul_apply]
      rw [h]
      exact smA_finset_sum_smul Finset.univ (fun i => lam q i) Y hYsm
    -- the value of the tower is the tower on the tuple of smooth extensions
    have hval1 : Work.Diff.EXT.ATower.valOp
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (fun _ => Work.Diff.EXT.aOf G (T / 2)) k) y v a b c
        = Work.Diff.EXT.cktA G (T / 2) k F y := by
      rw [Work.Diff.EXT.ATower.valOp_tower_eq_covKAExt]
      rw [hF]
      exact (Work.Diff.EXT.cktA_mkT3_eq G (T / 2) k
        (fun i : Fin k => Submission.Diff.smoothExt y (v i))
        (fun p : Fin 3 => Submission.Diff.smoothExt y (Bv p)) y).symm
    -- value dependence
    have hvd : Work.Diff.EXT.cktA G (T / 2) k F y = Work.Diff.EXT.cktA G (T / 2) k Zt y :=
      Work.Diff.EXT.ka_val_dep_all (I := I) (M := M) hLC G (T / 2) k y hFsm hZsm
        (fun q => by rw [hFval q, hZval q])
    -- the expansion in the frame
    have hexp : Work.Diff.EXT.cktA G (T / 2) k Zt y
        = ∑ Q : Fin (k + 3) → Fin (Module.finrank ℝ E),
            (∏ q : Fin (k + 3), lam q (Q q)) *
              Work.Diff.EXT.cktA G (T / 2) k (fun q => Y (Q q)) y := by
      have h := Work.Diff.EXT.ConnCov.cktA_expand (I := I) (M := M) hLC G (T / 2) k y
        (F := Zt) (d := fun q i => fun _ : M => lam q i) (V := fun q i => Y i)
        hZsm (fun q i => contMDiff_const) (fun q i => hYsm i)
        (fun q z => by simp only [hZt, Finset.sum_apply, Pi.smul_apply])
      simpa only using h
    -- germ locality: replacing the approximants by the frame
    have hgerm : ∀ Q : Fin (k + 3) → Fin (Module.finrank ℝ E),
        Work.Diff.EXT.cktA G (T / 2) k (fun q => Y (Q q)) y
          = Work.Diff.EXT.cktA G (T / 2) k
              (fun q => Work.Diff.GE.cFrame (I := I) x₀ (Q q)) y := by
      intro Q
      exact ((Work.Diff.EXT.ka_locAt (I := I) (M := M) hLC G (T / 2) k (x := y)
        (F := fun q => Work.Diff.GE.cFrame (I := I) x₀ (Q q))
        (F' := fun q => Y (Q q))
        (fun q => Work.Diff.EXT.smLoc_cFrame (I := I) x₀ hysrc (Q q))
        (fun q => hYsm (Q q))
        (fun q => (hYeq (Q q)).symm)).eq_of_nhds).symm
    -- the chart recursion
    have hchart : ∀ Q : Fin (k + 3) → Fin (Module.finrank ℝ E),
        Work.Diff.EXT.cktA G (T / 2) k (fun q => Work.Diff.GE.cFrame (I := I) x₀ (Q q)) y
          = Work.Diff.EXT.aCovArr G x₀ (T / 2) k (fun i : Fin k => Q (Fin.castAdd 3 i))
              (Q (Fin.natAdd k 0)) (Q (Fin.natAdd k 1)) (Q (Fin.natAdd k 2))
              ((extChartAt I x₀) y) := by
      intro Q
      have hR := Work.Diff.EXT.aCovArr_eq_covKAExt (I := I) (M := M) G x₀ (T / 2) k
        (fun i : Fin k => Q (Fin.castAdd 3 i)) (Q (Fin.natAdd k 0)) (Q (Fin.natAdd k 1))
        (Q (Fin.natAdd k 2)) hyT
      rw [hpty] at hR
      rw [← mkT3_cFrame (I := I) x₀ Q, Work.Diff.EXT.cktA_mkT3_eq]
      exact hR.symm
    -- the sum form of the value
    have hmain : Work.Diff.EXT.cktA G (T / 2) k F y
        = ∑ Q : Fin (k + 3) → Fin (Module.finrank ℝ E),
            (∏ q : Fin (k + 3), lam q (Q q)) *
              Work.Diff.EXT.aCovArr G x₀ (T / 2) k (fun i : Fin k => Q (Fin.castAdd 3 i))
                (Q (Fin.natAdd k 0)) (Q (Fin.natAdd k 1)) (Q (Fin.natAdd k 2))
                ((extChartAt I x₀) y) := by
      rw [hvd, hexp]
      exact Finset.sum_congr rfl (fun Q _ => by rw [hgerm Q, hchart Q])
    -- the bound for the chart components
    have hbd : ∀ Q : Fin (k + 3) → Fin (Module.finrank ℝ E),
        |Work.Diff.EXT.aCovArr G x₀ (T / 2) k (fun i : Fin k => Q (Fin.castAdd 3 i))
            (Q (Fin.natAdd k 0)) (Q (Fin.natAdd k 1)) (Q (Fin.natAdd k 2))
            ((extChartAt I x₀) y)| ≤ A :=
      fun Q => hAb ((extChartAt I x₀) y) hyK _ _ _ _
    -- the bound for the coefficients
    have hcoeff : ∀ q : Fin (k + 3), (∑ i, |lam q i|)
        ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) / δ)
            * Real.sqrt ((G (T / 2)).inner y (pv q) (pv q)) := by
      intro q
      have h := frameCoord_bound_local (I := I) (M := M) (G (T / 2)) x₀ ((extChartAt I x₀) y)
        hyT (δ := δ) hδpos (fun w => hKell _ hyK w) (pv q)
      rw [show (extChartAt I x₀).symm ((extChartAt I x₀) y) = y from hpty] at h
      simpa only [hlam] using h
    -- the numerical combination
    calc |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (fun _ => Work.Diff.EXT.aOf G (T / 2)) k) y v a b c|
        = |∑ Q : Fin (k + 3) → Fin (Module.finrank ℝ E),
              (∏ q : Fin (k + 3), lam q (Q q)) *
                Work.Diff.EXT.aCovArr G x₀ (T / 2) k (fun i : Fin k => Q (Fin.castAdd 3 i))
                  (Q (Fin.natAdd k 0)) (Q (Fin.natAdd k 1)) (Q (Fin.natAdd k 2))
                  ((extChartAt I x₀) y)| := by rw [hval1, hmain]
      _ ≤ ∑ Q : Fin (k + 3) → Fin (Module.finrank ℝ E),
              |(∏ q : Fin (k + 3), lam q (Q q)) *
                Work.Diff.EXT.aCovArr G x₀ (T / 2) k (fun i : Fin k => Q (Fin.castAdd 3 i))
                  (Q (Fin.natAdd k 0)) (Q (Fin.natAdd k 1)) (Q (Fin.natAdd k 2))
                  ((extChartAt I x₀) y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ Q : Fin (k + 3) → Fin (Module.finrank ℝ E),
              (∏ q : Fin (k + 3), |lam q (Q q)|) * A := by
            refine Finset.sum_le_sum (fun Q _ => ?_)
            rw [abs_mul, Finset.abs_prod]
            exact mul_le_mul_of_nonneg_left (hbd Q)
              (Finset.prod_nonneg (fun q _ => abs_nonneg _))
      _ = A * ∑ Q : Fin (k + 3) → Fin (Module.finrank ℝ E),
              ∏ q : Fin (k + 3), |lam q (Q q)| := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun Q _ => by ring)
      _ = A * ∏ q : Fin (k + 3), ∑ i, |lam q i| := by
            congr 1
            exact sum_prod_eq_prod_sum (fun q i => |lam q i|)
      _ ≤ A * ∏ q : Fin (k + 3), (Real.sqrt ((Module.finrank ℝ E : ℝ) / δ)
              * Real.sqrt ((G (T / 2)).inner y (pv q) (pv q))) :=
            mul_le_mul_of_nonneg_left
              (Finset.prod_le_prod₀ (fun q _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
                (fun q _ => hcoeff q)) hA0
      _ = (A * (Real.sqrt ((Module.finrank ℝ E : ℝ) / δ)) ^ (k + 3))
            * ∏ q : Fin (k + 3), Real.sqrt ((G (T / 2)).inner y (pv q) (pv q)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            ring
      _ = (A * (Real.sqrt ((Module.finrank ℝ E : ℝ) / δ)) ^ (k + 3))
            * ((∏ i : Fin k, Real.sqrt ((G (T / 2)).inner y (v i) (v i)))
              * Real.sqrt ((G (T / 2)).inner y a a) * Real.sqrt ((G (T / 2)).inner y b b)
              * Real.sqrt ((G (T / 2)).inner y c c)) := by
            rw [hpv, prod_univ_vecPackT (k := k)
              (f := fun w : TangentSpace I y => Real.sqrt ((G (T / 2)).inner y w w))
              v Bv, hBv]
            rfl
      _ = (A * (Real.sqrt ((Module.finrank ℝ E : ℝ) / δ)) ^ (k + 3))
            * (∏ i : Fin k, Real.sqrt ((G (T / 2)).inner y (v i) (v i)))
              * Real.sqrt ((G (T / 2)).inner y a a) * Real.sqrt ((G (T / 2)).inner y b b)
              * Real.sqrt ((G (T / 2)).inner y c c) := by ring

/-! ## The target -/

theorem covKAExt_bound_sliceT
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
    ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (fun _ => Work.Diff.EXT.aOf G (T / 2)) k) x v a b c|
          ≤ Ck * (Finset.univ.prod (fun i : Fin k =>
                Real.sqrt ((G (T / 2)).inner x (v i) (v i))))
              * Real.sqrt ((G (T / 2)).inner x a a) * Real.sqrt ((G (T / 2)).inner x b b)
              * Real.sqrt ((G (T / 2)).inner x c c) := by
  intro k
  have hloc : ∀ x : M, ∃ V : Set M, V ∈ 𝓝 x ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ V, ∀ (v : Fin k → TangentSpace I y) (a b c : TangentSpace I y),
        |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (fun _ => Work.Diff.EXT.aOf G (T / 2)) k) y v a b c|
          ≤ C * (Finset.univ.prod (fun i : Fin k =>
                Real.sqrt ((G (T / 2)).inner y (v i) (v i))))
              * Real.sqrt ((G (T / 2)).inner y a a) * Real.sqrt ((G (T / 2)).inner y b b)
              * Real.sqrt ((G (T / 2)).inner y c c) :=
    fun x => slice_local (I := I) (M := M) hLC G T hT k x
  choose V hV C hC0 hCbd using hloc
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover V hV
  refine ⟨∑ y ∈ s, C y, Finset.sum_nonneg (fun y _ => hC0 y), ?_⟩
  intro x v a b c
  have hx : x ∈ ⋃ y ∈ s, V y := by rw [hs]; trivial
  simp only [Set.mem_iUnion] at hx
  obtain ⟨y, hys, hyx⟩ := hx
  have hpat : 0 ≤ (∏ i : Fin k, Real.sqrt ((G (T / 2)).inner x (v i) (v i)))
      * Real.sqrt ((G (T / 2)).inner x a a) * Real.sqrt ((G (T / 2)).inner x b b)
      * Real.sqrt ((G (T / 2)).inner x c c) :=
    mul_nonneg (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have h1 : C y * ((∏ i : Fin k, Real.sqrt ((G (T / 2)).inner x (v i) (v i)))
      * Real.sqrt ((G (T / 2)).inner x a a) * Real.sqrt ((G (T / 2)).inner x b b)
      * Real.sqrt ((G (T / 2)).inner x c c))
      ≤ (∑ z ∈ s, C z) * ((∏ i : Fin k, Real.sqrt ((G (T / 2)).inner x (v i) (v i)))
      * Real.sqrt ((G (T / 2)).inner x a a) * Real.sqrt ((G (T / 2)).inner x b b)
      * Real.sqrt ((G (T / 2)).inner x c c)) :=
    mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun z _ => hC0 z) hys) hpat
  refine le_trans (hCbd y x hyx v a b c) ?_
  calc C y * (Finset.univ.prod (fun i : Fin k =>
          Real.sqrt ((G (T / 2)).inner x (v i) (v i))))
        * Real.sqrt ((G (T / 2)).inner x a a) * Real.sqrt ((G (T / 2)).inner x b b)
        * Real.sqrt ((G (T / 2)).inner x c c)
      = C y * ((∏ i : Fin k, Real.sqrt ((G (T / 2)).inner x (v i) (v i)))
          * Real.sqrt ((G (T / 2)).inner x a a) * Real.sqrt ((G (T / 2)).inner x b b)
          * Real.sqrt ((G (T / 2)).inner x c c)) := by ring
    _ ≤ (∑ z ∈ s, C z) * ((∏ i : Fin k, Real.sqrt ((G (T / 2)).inner x (v i) (v i)))
          * Real.sqrt ((G (T / 2)).inner x a a) * Real.sqrt ((G (T / 2)).inner x b b)
          * Real.sqrt ((G (T / 2)).inner x c c)) := h1
    _ = (∑ z ∈ s, C z) * (Finset.univ.prod (fun i : Fin k =>
            Real.sqrt ((G (T / 2)).inner x (v i) (v i))))
          * Real.sqrt ((G (T / 2)).inner x a a) * Real.sqrt ((G (T / 2)).inner x b b)
          * Real.sqrt ((G (T / 2)).inner x c c) := by ring

end Work.Diff.EXT.ConnCov
