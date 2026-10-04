import Mathlib
import Submission.Work.Diff.T.lc_deps
import Submission.Work.Diff.T.clairaut_fderiv_apply
import Submission.Work.Diff.T.metric_pairing_smooth
import Submission.Work.Diff.T.metric_family_deriv
import Submission.Work.Diff.T.dtMet_pairing_smooth
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.T.hasDerivAt_of_eventually_system
import Submission.Work.Diff.T.hasDerivAt_metric_inner_moving

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Contract T2: first variation of the Levi-Civita connection (`LCVariation`)

Main lemma of this file: `Work.Diff.T.lc_variation`.

Strategy:
* `lcOf (G t)` is Mathlib's Levi-Civita connection of the metric `G t`; the Koszul formula
  (`CovariantDerivative.IsLeviCivitaConnection.apply_eq`) determines
  `(G t).inner x (∇^t_X Y) Z` entirely in terms of `G t` and the fields.
* Differentiating that formula in `t` (Clairaut's theorem, applied in the chart at `x`) gives the
  derivative of `t ↦ (G t).inner x (∇^t_X Y) (Z x)`.
* The existence of `∂_t ∇^t_X Y (x)` is obtained by testing against a `(G t₀)`-orthonormal basis
  and solving the resulting (eventual) linear system
  `Ψ t j = K t j - ∑ k Ψ t k * A k j t`.
* Rewriting the result with torsion-freeness and the symmetry of `dtMet` gives the claimed formula.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.Diff.T

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-! ## Elementary helpers -/

/-- `dtMet` is symmetric (each `G t` is a metric). -/
lemma dtMet_comm (G : ℝ → SMet I M) (t₀ : ℝ) (x : M) (u v : TangentSpace I x) :
    dtMet G t₀ x u v = dtMet G t₀ x v u := by
  simp only [dtMet]
  exact congrArg (fun f : ℝ → ℝ ↦ deriv f t₀) (funext fun t ↦ (G t).symm x u v)

/-- The right hand side of the Koszul formula for the metric `G t`, as a function of `t`. -/
noncomputable def koszulForm (G : ℝ → SMet I M) (X Y Z : Π x : M, TangentSpace I x)
    (x : M) : ℝ → ℝ :=
  fun t ↦ mvfderiv I (fun y : M ↦ (G t).inner y (Y y) (Z y)) x (X x)
    + mvfderiv I (fun y : M ↦ (G t).inner y (Z y) (X y)) x (Y x)
    - mvfderiv I (fun y : M ↦ (G t).inner y (X y) (Y y)) x (Z x)
    - (G t).inner x (Y x) (mlieBracket I X Z x)
    - (G t).inner x (Z x) (mlieBracket I Y X x)
    + (G t).inner x (X x) (mlieBracket I Z Y x)

/-- The value at `t₀` of the derivative of `koszulForm`: the same expression with `dtMet` in
place of `(G t).inner`. -/
noncomputable def dtKoszulForm (G : ℝ → SMet I M) (t₀ : ℝ)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (fun y : M ↦ dtMet G t₀ y (Y y) (Z y)) x (X x)
    + mvfderiv I (fun y : M ↦ dtMet G t₀ y (Z y) (X y)) x (Y x)
    - mvfderiv I (fun y : M ↦ dtMet G t₀ y (X y) (Y y)) x (Z x)
    - dtMet G t₀ x (Y x) (mlieBracket I X Z x)
    - dtMet G t₀ x (Z x) (mlieBracket I Y X x)
    + dtMet G t₀ x (X x) (mlieBracket I Z Y x)

/-- **Analytic core.**  Differentiating in `t` the `x`-derivative of the `t`-dependent metric
pairing: for smooth `Y`, `Z`, the function `t ↦ d% ⟪Y,Z⟫_{G t} x v` has derivative obtained by
replacing `(G t).inner` by `dtMet G t₀`.  (Clairaut's theorem in the chart at `x`.) -/
theorem hasDerivAt_mvfderiv_inner
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    {Y Z : Π x : M, TangentSpace I x} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) (v : TangentSpace I x) :
    HasDerivAt (fun t ↦ mvfderiv I (fun y : M ↦ (G t).inner y (Y y) (Z y)) x v)
      (mvfderiv I (fun y : M ↦ dtMet G t₀ y (Y y) (Z y)) x v) t₀ := by
  classical
  -- the coordinate vector of `v` in the chart at `x`
  set w : E := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v with hwdef
  have hv : v = Submission.Geodesic.frameVector (I := I) x x w := by
    rw [hwdef]
    show v = (trivializationAt E (TangentSpace I) x).symmL ℝ x
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v)
    exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (trivializationAt E (TangentSpace I) x) (mem_baseSet_trivializationAt E _ x) v).symm
  -- the chart representative of the pairing
  set Φ : ℝ × E → ℝ := fun p ↦ (G p.1).inner ((extChartAt I x).symm p.2)
      (Y ((extChartAt I x).symm p.2)) (Z ((extChartAt I x).symm p.2)) with hΦdef
  have hpair : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (Y p.2) (Z p.2)) (J ×ˢ univ) :=
    metric_pairing_smooth hJs hY hZ
  have hφsymm : ContMDiffAt 𝓘(ℝ,E) I ∞ (fun u : E ↦ (extChartAt I x).symm u)
      ((extChartAt I x) x) :=
    (contMDiffOn_extChartAt_symm (I := I) x).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x).mem_nhds
        ((extChartAt I x).map_source (mem_extChartAt_source x)))
  have hchart : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) (𝓘(ℝ,ℝ).prod I) ∞
      (fun p : ℝ × E ↦ (p.1, (extChartAt I x).symm p.2)) (t₀, (extChartAt I x) x) :=
    contMDiffAt_fst.prodMk (hφsymm.comp (t₀, (extChartAt I x) x) contMDiffAt_snd)
  have hmem : J ×ˢ (univ : Set M) ∈ 𝓝 (t₀, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hJopen.mem_nhds ht₀) Filter.univ_mem
  have hpairAt : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (Y p.2) (Z p.2)) (t₀, x) :=
    hpair.contMDiffAt hmem
  have hΦmd : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ Φ (t₀, (extChartAt I x) x) := by
    have h := hpairAt.comp_of_eq hchart (by simp)
    simpa only [Function.comp_def, hΦdef] using h
  have hΦcd : ContDiffAt ℝ 2 Φ (t₀, (extChartAt I x) x) := by
    have h' : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ,ℝ) ∞ Φ (t₀, (extChartAt I x) x) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hΦmd
    exact ((contMDiffAt_iff_contDiffAt).mp h').of_le (by norm_num)
  have hcl := clairaut_fderiv_apply hΦcd w
  -- the two sides, rewritten in coordinates
  have hcoords (t : ℝ) (ht : t ∈ J) :
      mvfderiv I (fun y : M ↦ (G t).inner y (Y y) (Z y)) x v
        = fderiv ℝ (fun u : E ↦ Φ (t, u)) ((extChartAt I x) x) w := by
    have hmemt : J ×ˢ (univ : Set M) ∈ 𝓝 (t, x) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (hJopen.mem_nhds ht) Filter.univ_mem
    have hmd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M ↦ (G t).inner y (Y y) (Z y)) x :=
      (((hpair.contMDiffAt hmemt).comp x
        ((contMDiffAt_const (c := t)).prodMk contMDiffAt_id)).mdifferentiableAt (by simp))
    rw [hv, mvfderiv_frameVector_real x (mem_chart_source H x) hmd w]
  have hLHS : (fun t ↦ mvfderiv I (fun y : M ↦ (G t).inner y (Y y) (Z y)) x v) =ᶠ[𝓝 t₀]
      (fun t ↦ fderiv ℝ (fun u : E ↦ Φ (t, u)) ((extChartAt I x) x) w) := by
    filter_upwards [hJopen.mem_nhds ht₀] with t ht
    exact hcoords t ht
  have hRHS : mvfderiv I (fun y : M ↦ dtMet G t₀ y (Y y) (Z y)) x v
      = fderiv ℝ (fun u : E ↦ deriv (fun t : ℝ ↦ Φ (t, u)) t₀) ((extChartAt I x) x) w := by
    rw [hv, mvfderiv_frameVector_real x (mem_chart_source H x)
      ((dtMet_pairing_smooth hJopen hJs ht₀ hY hZ x).mdifferentiableAt (by simp)) w]
    have hfg : (fun u : E ↦ dtMet G t₀ ((extChartAt I x).symm u) (Y ((extChartAt I x).symm u))
        (Z ((extChartAt I x).symm u))) = (fun u : E ↦ deriv (fun t : ℝ ↦ Φ (t, u)) t₀) := by
      funext u
      rfl
    rw [hfg]
  rw [hRHS]
  exact (Filter.EventuallyEq.hasDerivAt_iff hLHS).mpr hcl

/-- The derivative in `t` of the Koszul expression. -/
lemma hasDerivAt_koszulForm
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (X Y Z : Π x : M, TangentSpace I x)
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    HasDerivAt (koszulForm G X Y Z x) (dtKoszulForm G t₀ X Y Z x) t₀ := by
  have h1 := hasDerivAt_mvfderiv_inner (G := G) (J := J) hJopen hJs ht₀ hY hZ x (X x)
  have h2 := hasDerivAt_mvfderiv_inner (G := G) (J := J) hJopen hJs ht₀ hZ hX x (Y x)
  have h3 := hasDerivAt_mvfderiv_inner (G := G) (J := J) hJopen hJs ht₀ hX hY x (Z x)
  have h4 := metric_family_deriv (G := G) (J := J) hJopen hJs ht₀ x (Y x) (mlieBracket I X Z x)
  have h5 := metric_family_deriv (G := G) (J := J) hJopen hJs ht₀ x (Z x) (mlieBracket I Y X x)
  have h6 := metric_family_deriv (G := G) (J := J) hJopen hJs ht₀ x (X x) (mlieBracket I Z Y x)
  have hcomb := ((((h1.add h2).sub h3).sub h4).sub h5).add h6
  convert hcomb using 1 <;> rfl

/-! ## Linearity of `dtMet` (needs differentiability in `t`) -/

lemma dtMet_sub_snd {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) (u v w : TangentSpace I x) :
    dtMet G t₀ x u (v - w) = dtMet G t₀ x u v - dtMet G t₀ x u w := by
  have h1 := metric_family_deriv (G := G) (J := J) hJopen hJs ht₀ x u (v - w)
  have h2 := (metric_family_deriv (G := G) (J := J) hJopen hJs ht₀ x u v).sub
    (metric_family_deriv (G := G) (J := J) hJopen hJs ht₀ x u w)
  have heq : (fun t : ℝ ↦ (G t).inner x u (v - w))
      = (fun t : ℝ ↦ (G t).inner x u v - (G t).inner x u w) := by
    funext t
    exact map_sub ((G t).inner x u) v w
  rw [heq] at h1
  exact h1.unique h2

/-- Is is bilinear in its first argument: `⟪∑ cᵢ • wᵢ, v⟫ = ∑ cᵢ ⟪wᵢ, v⟫`. -/
lemma inner_sum_smul (G : ℝ → SMet I M) (t : ℝ) (x : M) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (w : ι → TangentSpace I x) (v : TangentSpace I x) :
    (G t).inner x (∑ i ∈ s, c i • w i) v = ∑ i ∈ s, c i * ((G t).inner x (w i) v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add, add_apply, map_smul, smul_apply,
        smul_eq_mul, ih]

lemma dtMet_sum_fst {ι : Type*} (s : Finset ι) {G : ℝ → SMet I M} {J : Set ℝ}
    (hJopen : IsOpen J) (hJs : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (c : ι → ℝ) (w : ι → TangentSpace I x) (v : TangentSpace I x) :
    dtMet G t₀ x (∑ i ∈ s, c i • w i) v = ∑ i ∈ s, c i * dtMet G t₀ x (w i) v := by
  have h1 := metric_family_deriv (G := G) (J := J) hJopen hJs ht₀ x (∑ i ∈ s, c i • w i) v
  have h2sum := HasDerivAt.sum (u := s) fun i _ ↦
      (metric_family_deriv (G := G) (J := J) hJopen hJs ht₀ x (w i) v).const_mul (c i)
  have hfun : (∑ i ∈ s, fun y : ℝ ↦ c i * (G y).inner x (w i) v)
      = (fun t : ℝ ↦ ∑ i ∈ s, c i * (G t).inner x (w i) v) := by
    funext t
    rw [Finset.sum_apply]
  rw [hfun] at h2sum
  have heq : (fun t : ℝ ↦ (G t).inner x (∑ i ∈ s, c i • w i) v)
      = (fun t : ℝ ↦ ∑ i ∈ s, c i * (G t).inner x (w i) v) := by
    funext t
    exact inner_sum_smul G t x s c w v
  rw [heq] at h1
  exact h1.unique h2sum

/-! ## Torsion-freeness of `lcOf` and the algebraic identity -/

/-- Torsion-freeness of `lcOf g`, in applied form (the type needs no Riemannian instance). -/
lemma lcOf_torsion_free (g : SMet I M) {U W : Π x : M, TangentSpace I x}
    (hU : CMDiff ∞ (T% U)) (hW : CMDiff ∞ (T% W)) (x : M) :
    lcOf g W x (U x) - lcOf g U x (W x) = mlieBracket I U W x := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have htor : CovariantDerivative.torsion (lcOf g) = 0 := by
    rw [lcOf]
    exact CovariantDerivative.torsion_leviCivitaConnection_eq_zero I
  exact (CovariantDerivative.torsion_eq_zero_iff (cov := lcOf g)).mp htor
    (hU.contMDiffAt.mdifferentiableAt (by simp)) (hW.contMDiffAt.mdifferentiableAt (by simp))

/-- **The algebraic identity behind the first variation formula.**  Using torsion-freeness and the
symmetry of `dtMet`, the `t`-derivative of Koszul's formula is rewritten in the `covDerivSym2`
form of the contract. -/
theorem variation_algebra {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J)
    (hJs : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) {x : M}
    (X Y Z : Π x : M, TangentSpace I x)
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    dtKoszulForm G t₀ X Y Z x - 2 * dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (Z x)
      = covDerivSym2 (lcOf (G t₀)) (dtMet G t₀) X Y Z x
          + covDerivSym2 (lcOf (G t₀)) (dtMet G t₀) Y X Z x
          - covDerivSym2 (lcOf (G t₀)) (dtMet G t₀) Z X Y x := by
  have hP2eq : mvfderiv I (fun y : M ↦ dtMet G t₀ y (Z y) (X y)) x (Y x)
      = mvfderiv I (fun y : M ↦ dtMet G t₀ y (X y) (Z y)) x (Y x) := by
    have hfe : (fun y : M ↦ dtMet G t₀ y (Z y) (X y))
        = (fun y : M ↦ dtMet G t₀ y (X y) (Z y)) := by
      funext y
      exact dtMet_comm G t₀ y (Z y) (X y)
    rw [hfe]
  have ht1 : dtMet G t₀ x (Y x) (mlieBracket I X Z x)
      = dtMet G t₀ x (Y x) (lcOf (G t₀) Z x (X x))
        - dtMet G t₀ x (Y x) (lcOf (G t₀) X x (Z x)) := by
    rw [show mlieBracket I X Z x = lcOf (G t₀) Z x (X x) - lcOf (G t₀) X x (Z x) from
      (lcOf_torsion_free (G t₀) hX hZ x).symm]
    exact dtMet_sub_snd hJopen hJs ht₀ x (Y x) _ _
  have ht2 : dtMet G t₀ x (Z x) (mlieBracket I Y X x)
      = dtMet G t₀ x (Z x) (lcOf (G t₀) X x (Y x))
        - dtMet G t₀ x (Z x) (lcOf (G t₀) Y x (X x)) := by
    rw [show mlieBracket I Y X x = lcOf (G t₀) X x (Y x) - lcOf (G t₀) Y x (X x) from
      (lcOf_torsion_free (G t₀) hY hX x).symm]
    exact dtMet_sub_snd hJopen hJs ht₀ x (Z x) _ _
  have ht3 : dtMet G t₀ x (X x) (mlieBracket I Z Y x)
      = dtMet G t₀ x (X x) (lcOf (G t₀) Y x (Z x))
        - dtMet G t₀ x (X x) (lcOf (G t₀) Z x (Y x)) := by
    rw [show mlieBracket I Z Y x = lcOf (G t₀) Y x (Z x) - lcOf (G t₀) Z x (Y x) from
      (lcOf_torsion_free (G t₀) hZ hY x).symm]
    exact dtMet_sub_snd hJopen hJs ht₀ x (X x) _ _
  have hs1 : dtMet G t₀ x (lcOf (G t₀) X x (Z x)) (Y x)
      = dtMet G t₀ x (Y x) (lcOf (G t₀) X x (Z x)) := dtMet_comm G t₀ x _ _
  have hs2 : dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (Z x)
      = dtMet G t₀ x (Z x) (lcOf (G t₀) Y x (X x)) := dtMet_comm G t₀ x _ _
  have hs3 : dtMet G t₀ x (lcOf (G t₀) X x (Y x)) (Z x)
      = dtMet G t₀ x (Z x) (lcOf (G t₀) X x (Y x)) := dtMet_comm G t₀ x _ _
  simp only [covDerivSym2, dtKoszulForm]
  rw [hP2eq, ht1, ht2, ht3, hs1, hs2, hs3]
  ring

/-! ## The main theorem -/

theorem lc_variation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M) :
    LCVariation I M := by
  intro G J hJopen hJs t₀ ht₀ X Y hX hY x
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  -- a `(G t₀)`-orthonormal basis of the tangent space
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  -- globally smooth sections through the basis vectors
  have hSec : ∀ j : Fin (Module.finrank ℝ E), ∃ W : Π y : M, TangentSpace I y,
      CMDiff ∞ (T% W) ∧ W x = b j :=
    fun j ↦ Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (b j)
  choose W hWs hWv using hSec
  -- the Koszul formula for the metric `G t`, and its derivative in `t`
  have hKos : ∀ (Z : Π y : M, TangentSpace I y), CMDiff ∞ (T% Z) → ∀ t : ℝ,
      (G t).inner x (lcOf (G t) Y x (X x)) (Z x) = (1 / 2) * koszulForm G X Y Z x t :=
    fun Z hZ t ↦ lcOf_apply_inner_koszul G t X Y Z hX hY hZ x
  have hKos' : ∀ (Z : Π y : M, TangentSpace I y), CMDiff ∞ (T% Z) →
      HasDerivAt (koszulForm G X Y Z x) (dtKoszulForm G t₀ X Y Z x) t₀ :=
    fun Z hZ ↦ hasDerivAt_koszulForm hJopen hJs ht₀ X Y Z hX hY hZ x
  have hpair (Z : Π y : M, TangentSpace I y) (hZ : CMDiff ∞ (T% Z)) :
      HasDerivAt (fun t ↦ (G t).inner x (lcOf (G t) Y x (X x)) (Z x))
        ((1 / 2) * dtKoszulForm G t₀ X Y Z x) t₀ :=
    ((hKos' Z hZ).const_mul (1 / 2)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t ↦ hKos Z hZ t)
  -- expansion of the connection in the basis, for every `t`
  have hExp (t : ℝ) : lcOf (G t) Y x (X x)
      = ∑ j, ((G t₀).inner x (lcOf (G t) Y x (X x)) (b j)) • b j := by
    conv_lhs => rw [← OrthonormalBasis.sum_repr' b (lcOf (G t) Y x (X x))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    exact real_inner_comm (lcOf (G t) Y x (X x)) (b j)
  -- the (eventual) linear system solved by the coefficients
  have hident (t : ℝ) (j : Fin (Module.finrank ℝ E)) :
      (G t₀).inner x (lcOf (G t) Y x (X x)) (b j)
        = (1 / 2) * koszulForm G X Y (W j) x t
          - ∑ k, ((G t₀).inner x (lcOf (G t) Y x (X x)) (b k))
              * ((G t).inner x (b k) (b j) - (G t₀).inner x (b k) (b j)) := by
    have h1 := hKos (W j) (hWs j) t
    rw [hWv j] at h1
    have h2 : (G t).inner x (lcOf (G t) Y x (X x)) (b j)
        = ∑ k, ((G t₀).inner x (lcOf (G t) Y x (X x)) (b k)) * ((G t).inner x (b k) (b j)) := by
      conv_lhs => rw [hExp t]
      exact inner_sum_smul G t x Finset.univ
        (fun k ↦ (G t₀).inner x (lcOf (G t) Y x (X x)) (b k)) (fun k ↦ b k) (b j)
    have h3 : (G t₀).inner x (lcOf (G t) Y x (X x)) (b j)
        = ∑ k, ((G t₀).inner x (lcOf (G t) Y x (X x)) (b k)) * ((G t₀).inner x (b k) (b j)) := by
      conv_lhs => rw [hExp t]
      exact inner_sum_smul G t₀ x Finset.univ
        (fun k ↦ (G t₀).inner x (lcOf (G t) Y x (X x)) (b k)) (fun k ↦ b k) (b j)
    have h4 : ∑ k, ((G t₀).inner x (lcOf (G t) Y x (X x)) (b k))
          * ((G t).inner x (b k) (b j) - (G t₀).inner x (b k) (b j))
        = (∑ k, ((G t₀).inner x (lcOf (G t) Y x (X x)) (b k)) * ((G t).inner x (b k) (b j)))
          - ∑ k, ((G t₀).inner x (lcOf (G t) Y x (X x)) (b k)) * ((G t₀).inner x (b k) (b j)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [h4, ← h3, ← h2]
    linarith [h1]
  -- differentiability of the coefficients
  have hderiv (j : Fin (Module.finrank ℝ E)) :
      HasDerivAt (fun t ↦ (G t₀).inner x (lcOf (G t) Y x (X x)) (b j))
        ((1 / 2) * dtKoszulForm G t₀ X Y (W j) x
          - dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (b j)) t₀ := by
    have hsys := hasDerivAt_of_eventually_system
      (ι := Fin (Module.finrank ℝ E))
      (Ψ := fun t (j : Fin (Module.finrank ℝ E)) ↦ (G t₀).inner x (lcOf (G t) Y x (X x)) (b j))
      (K := fun t (j : Fin (Module.finrank ℝ E)) ↦ (1 / 2) * koszulForm G X Y (W j) x t)
      (A := fun k (j : Fin (Module.finrank ℝ E)) t ↦
        (G t).inner x (b k) (b j) - (G t₀).inner x (b k) (b j))
      (K' := fun j ↦ (1 / 2) * dtKoszulForm G t₀ X Y (W j) x)
      (h := fun k j ↦ dtMet G t₀ x (b k) (b j))
      (fun k j ↦ sub_self _)
      (Filter.Eventually.of_forall hident)
      (fun j ↦ (hKos' (W j) (hWs j)).const_mul (1 / 2))
      (fun k j ↦ (metric_family_deriv hJopen hJs ht₀ x (b k) (b j)).sub_const _)
      j
    have hsum : ∑ k, ((G t₀).inner x (lcOf (G t₀) Y x (X x)) (b k)) * dtMet G t₀ x (b k) (b j)
        = dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (b j) := by
      rw [← dtMet_sum_fst Finset.univ hJopen hJs ht₀ x (fun k ↦ (G t₀).inner x
        (lcOf (G t₀) Y x (X x)) (b k)) (fun k ↦ b k) (b j)]
      congr 1
      exact (hExp t₀).symm
    rw [hsum] at hsys
    exact hsys
  -- the derivative of the connection
  have hFderiv : HasDerivAt (fun t ↦ lcOf (G t) Y x (X x))
      (∑ j, ((1 / 2) * dtKoszulForm G t₀ X Y (W j) x
        - dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (b j)) • b j) t₀ := by
    have h1sum := HasDerivAt.sum (u := Finset.univ) fun j _ ↦ (hderiv j).smul_const (b j)
    have hfun : (∑ j ∈ Finset.univ, fun t ↦ ((G t₀).inner x (lcOf (G t) Y x (X x)) (b j)) • b j)
        = (fun t ↦ ∑ j, ((G t₀).inner x (lcOf (G t) Y x (X x)) (b j)) • b j) :=
      funext fun t ↦ Finset.sum_apply _ _ _
    rw [hfun] at h1sum
    refine h1sum.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun t ↦ hExp t
  refine ⟨∑ j, ((1 / 2) * dtKoszulForm G t₀ X Y (W j) x
      - dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (b j)) • b j, ?_, ?_⟩
  · exact hFderiv
  · intro Z hZ
    have h1 := hpair Z hZ
    have h2 := hasDerivAt_metric_inner_moving hJopen hJs ht₀ hFderiv (Z x)
    have huniq : (1 / 2) * dtKoszulForm G t₀ X Y Z x
        = dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (Z x)
          + (G t₀).inner x (∑ j, ((1 / 2) * dtKoszulForm G t₀ X Y (W j) x
              - dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (b j)) • b j) (Z x) :=
      h1.unique h2
    have hval : (G t₀).inner x (∑ j, ((1 / 2) * dtKoszulForm G t₀ X Y (W j) x
          - dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (b j)) • b j) (Z x)
        = (1 / 2) * dtKoszulForm G t₀ X Y Z x
          - dtMet G t₀ x (lcOf (G t₀) Y x (X x)) (Z x) := by
      linarith [huniq]
    rw [hval]
    have halg := variation_algebra (x := x) hJopen hJs ht₀ X Y Z hX hY hZ
    linarith [halg]

end Work.Diff.T
