import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.transport_deTurck_general
import Submission.Work.Diff.STE.B3.mat_jet_bound_of_energy
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.pdList_le_sqrt_CSq
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.B3.mat_jet_bound_global
import Submission.Work.Diff.STE.Lead.Gal.gardLeibnizLocal
import Submission.Work.Diff.STE.Lead.R_pdRList_jet_BNorm
import Submission.Work.Diff.STE.Lead.jet_bound_of_germ_secondOrder
import Submission.Work.Diff.STE.Lead.psiComp_contDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Work.Diff.STE

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The support of the localised component `R i h a b` lies in the open `σ i`-ball: the
normalised weight `ζ i` vanishes off the `σ i`-ball (`B3Data.hζsupp`) and the cut-off `χ i` is
smooth with topological support in the chart target (`B3Data.hχtsup`), so `ψ i = χ i · (ζ i ∘ pt i)`
can only be nonzero where the flat coordinate of `pt i z` is `z` and lies in the `σ i`-ball. -/
lemma R_support_ball (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    Function.support (D.R i h a b) ⊆
      {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ < D.σ i} := by
  intro z hz
  have hpsi : D.psi i z ≠ 0 := fun h0 =>
    hz (by simp only [B3Data.R, h0, zero_mul, mul_zero])
  have hz' : D.ζ i (D.pt i z) ≠ 0 := fun h0 =>
    hpsi (by simp only [B3Data.psi, h0, mul_zero])
  obtain ⟨hsrc, hlt⟩ := D.hζsupp i (D.pt i z) hz'
  have hzt : z ∈ tsupport (D.χ i) := by
    by_contra hcon
    exact hpsi (by simp only [B3Data.psi,
      image_eq_zero_of_notMem_tsupport hcon, zero_mul])
  have hcoord : coord (I := I) (D.x₀ i) (D.pt i z) = z := by
    have h1 : (extChartAt I (D.x₀ i)) (D.pt i z)
        = flatToE (I := I) (D.x₀ i) z :=
      (extChartAt I (D.x₀ i)).right_inv (D.hχtsup i z hzt)
    have key : (Module.finBasis ℝ E).equivFun (flatToE (I := I) (D.x₀ i) z)
        = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z := by
      simp only [flatToE]
      rw [LinearEquiv.apply_symm_apply]
    rw [coord, h1, key]
    ring
  rw [← hcoord]
  exact hlt

/-- If the model space is zero-dimensional, every composite norm vanishes (all the sums involved
are empty). -/
lemma BNorm_eq_zero_of_finrank_eq_zero (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M)) (hn : Module.finrank ℝ E = 0) : D.BNorm k h = 0 := by
  rw [B3Data.BNorm]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ => ?_
  exact absurd a.isLt (by omega)

/-- The partial derivative of the zero function vanishes. -/
lemma pd_zero'' (i : Fin (Module.finrank ℝ E)) :
    pd i (0 : (Fin (Module.finrank ℝ E) → ℝ) → ℂ) = 0 := by
  funext x
  simp only [pd, fderiv_zero, ContinuousLinearMap.zero_apply, Pi.zero_apply]

/-- Every iterated partial derivative of the zero function vanishes. -/
lemma pdVec_zero'' (m : ℕ) (β : Fin m → Fin (Module.finrank ℝ E)) :
    pdVec m β (0 : (Fin (Module.finrank ℝ E) → ℝ) → ℂ) = 0 := by
  have hlist : ∀ l : List (Fin (Module.finrank ℝ E)),
      pdList l (0 : (Fin (Module.finrank ℝ E) → ℝ) → ℂ) = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i t ih =>
        rw [show pdList (i :: t) (0 : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)
          = pd i (pdList t 0) from rfl, ih, pd_zero'']
  simpa only [pdVec] using hlist (List.ofFn β)

theorem BNorm_deTurckSec_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j : ℕ, 0 ≤ B j)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
      (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
      (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h),
      (∀ j : ℕ, D.BNorm j h ≤ B j) →
      (∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v) →
      (∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v) →
      (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
        (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K) →
      D.BNorm k (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsm) ≤ C := by
  classical
  by_cases hn0 : Module.finrank ℝ E = 0
  · refine ⟨0, le_rfl, fun h hsym hpos hsm _ _ _ _ => ?_⟩
    have h0 := BNorm_eq_zero_of_finrank_eq_zero (I := I) (M := M) D k
      (Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsm) hn0
    rw [h0]
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  -- the Sobolev order at which the jet bounds for the localised components are taken
  set k₀ : ℕ := k + 3 + Module.finrank ℝ E with hk₀def
  have hk₀ : Module.finrank ℝ E + 2 * (k + 2) < 2 * k₀ := by
    rw [hk₀def]; omega
  -- ## the three analytic inputs
  -- (1) Sobolev jet bounds for the localised components from the composite norm
  obtain ⟨CRA, hCRAnn, hRAb⟩ :=
    R_pdRList_jet_BNorm (I := I) (M := M) D k₀ (k + 2) hk₀
  -- (2) the jet bound at a point for a function agreeing with a second-order operator
  obtain ⟨CJ, hCJnn, hJb⟩ := jet_bound_of_germ_secondOrder (n := Module.finrank ℝ E) (N := k)
  -- (3) the transport identity of the tame layer
  obtain ⟨_Clam', CT, _hClam'pos, hCTnn, hTb⟩ :=
    Work.Diff.STE.B3.transport_deTurck_general (I := I) (M := M) D hLC k lam K hlam hK
  obtain ⟨Ccsq, hCcsqnn, hcsqp⟩ := CSq_periodization_le_of_sup_bound
    (ι := Fin (Module.finrank ℝ E)) k
  -- ## the constants
  set CD : ℝ := CRA * Real.sqrt (B k₀) with hCDdef
  have hCDnn : 0 ≤ CD := mul_nonneg hCRAnn (Real.sqrt_nonneg _)
  set CG : ℝ := CJ * (CT * CD + CT + 1) with hCGdef
  have hCGnn : 0 ≤ CG :=
    mul_nonneg hCJnn (by nlinarith [hCTnn, hCDnn])
  refine ⟨(Fintype.card ι₀ : ℝ) * (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)
    * (Ccsq * CG ^ 2), by positivity, ?_⟩
  intro h hsym hpos hsm hBN hell hub hjet
  -- the transport data of every chart
  choose A Psi hP using fun j => hTb h hsym hpos hsm hell hub hjet j
  have hRsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b) := fun i a b =>
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsm i a b
  have hAsm' : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (fun y : Fin (Module.finrank ℝ E) → ℝ => A i y c d) := by
    intro i c d
    exact contDiff_pi.mp (contDiff_pi.mp (hP i).2.2.2.1 c) d
  -- ## the composite norm of every component of the DeTurck operator
  have hfin : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      CSq k (fourierCoeff (D.Rper i (Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsm) a b))
        ≤ Ccsq * CG ^ 2 := by
    intro i a b
    set Ph : Bil (I := I) (M := M) := Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsm with hPhdef
    set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
      fun y => ((D.R i Ph a b y : ℝ) : ℂ) with hFdef
    set G : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
      fun y => ((D.R i h a b y : ℝ) : ℂ) with hGdef
    set PsiC : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun y =>
      ((Psi i (y, (fun c d => D.mat i h c d y),
        (fun c d r => pdR r (D.mat i h c d) y)) a b : ℝ) : ℂ) with hPsiCdef
    set Ac : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
      fun c d y => ((A i y c d : ℝ) : ℂ) with hAcdef
    -- ## elementary facts about the four local objects
    have hGsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) G := by
      rw [hGdef]
      exact Complex.ofRealCLM.contDiff.comp (hRsm i a b)
    have hAsm : ∀ c d : Fin (Module.finrank ℝ E),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Ac c d) := by
      intro c d
      rw [hAcdef]
      exact Complex.ofRealCLM.contDiff.comp (hAsm' i c d)
    -- the second partial derivatives of `G` are the complexifications of those of `D.R i h a b`
    have hpd : ∀ c d : Fin (Module.finrank ℝ E), pd c (pd d G)
        = fun y => ((pdR c (pdR d (D.R i h a b)) y : ℝ) : ℂ) := by
      intro c d
      have h1 := cm_pdList_ofReal_smooth [c, d] (D.R i h a b) (hRsm i a b)
      simpa only [pdList, List.foldr_cons, List.foldr_nil, pdRList, hGdef] using h1
    have hPsiCsm : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ i →
        ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) PsiC z := by
      intro z hz
      rw [hPsiCdef]
      exact psiComp_contDiffAt (I := I) (M := M) D h hsm i a b (Psi i)
        (hP i).2.2.2.2.2.1 z hz
    -- ## the germ equality
    have hgermG : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ < 2 * D.σ i →
        F =ᶠ[𝓝 z] ((fun y => ∑ c, ∑ d, Ac c d y * pd c (pd d G) y) + PsiC) := by
      intro z hz
      have hball : ∀ᶠ y in 𝓝 z, ‖y‖ ≤ 2 * D.σ i := by
        refine Filter.eventually_iff_exists_mem.mpr
          ⟨Metric.ball z (2 * D.σ i - ‖z‖),
            Metric.ball_mem_nhds z (by linarith), fun y hy => ?_⟩
        have h1 : ‖y - z‖ < 2 * D.σ i - ‖z‖ := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hy
        calc ‖y‖ = ‖(y - z) + z‖ := by ring_nf
          _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ 2 * D.σ i - ‖z‖ + ‖z‖ := by linarith
          _ = 2 * D.σ i := by ring
      filter_upwards [hball] with y hy
      have hid := (hP i).2.2.2.2.2.2.2 a b y hy
      simp only [hFdef, hPsiCdef, hGdef, hAcdef]
      rw [hid]
      simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hpd c d]
    -- ## the jet bound on the `σ i`-ball
    have hlocal : ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → ‖pdVec m β F z‖ ≤ CG := by
      intro m hm β z hz
      have hz2 : ‖z‖ ≤ 2 * D.σ i := by have := D.hσ i; linarith
      have hAj : ∀ (c d : Fin (Module.finrank ℝ E)) (m' : ℕ), m' ≤ k →
          ∀ β' : Fin m' → Fin (Module.finrank ℝ E), ‖pdVec m' β' (Ac c d) z‖ ≤ CT := by
        intro c d m' hm' β'
        have hh := (hP i).2.2.1 m' hm' β' z c d
        rw [hAcdef]
        exact hh
      have hGj : ∀ (m' : ℕ), m' ≤ k + 2 → ∀ β' : Fin m' → Fin (Module.finrank ℝ E),
          ‖pdVec m' β' G z‖ ≤ CD := by
        intro m' hm' β'
        have hh := hRAb h hsm i a b [] m' β' z (by simpa using hm') hz2
        rw [hGdef]
        refine le_trans hh ?_
        rw [hCDdef]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hBN k₀)) hCRAnn
      have hPsiJ : ∀ (m' : ℕ), m' ≤ k → ∀ β' : Fin m' → Fin (Module.finrank ℝ E),
          ‖pdVec m' β' PsiC z‖ ≤ CT := by
        intro m' hm' β'
        have hh := (hP i).2.2.2.2.2.2.1 m' hm' β' z a b hz2
        rw [hPsiCdef]
        exact hh
      have hCDj : ∀ (c d : Fin (Module.finrank ℝ E)) (m' : ℕ), m' ≤ k →
          ∀ β' : Fin m' → Fin (Module.finrank ℝ E), ‖pdVec m' β' (pd c (pd d G)) z‖ ≤ CD := by
        intro c d m' hm' β'
        have hh := hRAb h hsm i a b [c, d] m' β' z (by simp; omega) hz2
        rw [hpd c d]
        refine le_trans hh ?_
        rw [hCDdef]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hBN k₀)) hCRAnn
      have hg := hgermG z (by have := D.hσ i; linarith)
      exact le_trans (hJb F G PsiC Ac z CT CD CT CD hCTnn hCDnn hCTnn hCDnn
        hAsm hGsm (hPsiCsm z hz2) hg hAj hGj hPsiJ hCDj m hm β)
        (le_of_eq (by rw [hCGdef]))
    -- ## vanishing away from the support of the component
    have hzero_of_far : ∀ z : Fin (Module.finrank ℝ E) → ℝ, D.σ i < ‖z‖ →
        F =ᶠ[𝓝 z] 0 := by
      intro z hz
      have hz' : z ∉ closure (Function.support (D.R i Ph a b)) := by
        intro hmem
        have hsub : closure (Function.support (D.R i Ph a b)) ⊆
            Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) :=
          closure_minimal
            (fun w hw => by
              rw [Metric.mem_closedBall, dist_zero_right]
              exact (R_support_ball (I := I) (M := M) D i Ph a b hw).le)
            Metric.isClosed_closedBall
        have h1 := hsub hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        linarith
      refine Filter.eventually_of_mem
        ((isClosed_closure).isOpen_compl.mem_nhds hz') fun y hy => ?_
      have hy0 : D.R i Ph a b y = 0 :=
        Function.notMem_support.mp fun hmem => hy (subset_closure hmem)
      show ((D.R i Ph a b y : ℝ) : ℂ) = 0
      rw [hy0, Complex.ofReal_zero]
    -- ## the jet bound everywhere
    have hjet' : ∀ (β : Fin k → Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ), ‖pdVec k β F z‖ ≤ CG := by
      intro β z
      by_cases hz : ‖z‖ ≤ D.σ i
      · exact hlocal k le_rfl β z hz
      · push_neg at hz
        have h0 : pdVec k β F z = 0 := by
          rw [csqp_pdVec_congr β (hzero_of_far z hz)]
          exact congrFun (pdVec_zero'' k β) z
        rw [h0]
        simpa using hCGnn
    -- ## smoothness of `F`
    have hFsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : ‖z‖ < 2 * D.σ i
      · have hzt : ‖z‖ ≤ 2 * D.σ i := le_of_lt hz
        have hRHS : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
            ((fun y => ∑ c, ∑ d, Ac c d y * pd c (pd d G) y) + PsiC) z := by
          have h1 : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
              (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ∑ c, ∑ d, Ac c d y * pd c (pd d G) y) := by
            refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
            refine (hAsm c d).mul ?_
            have h2 := csqp_contDiff_pdList_top [c, d] hGsm
            simpa only [pdList, List.foldr_cons, List.foldr_nil] using h2
          exact h1.contDiffAt.add (hPsiCsm z hzt)
        exact hRHS.congr_of_eventuallyEq (hgermG z hz)
      · push_neg at hz
        have hσpos : 0 < D.σ i := D.hσ i
        exact contDiffAt_const.congr_of_eventuallyEq (hzero_of_far z (by linarith))
    -- ## the CSq bound
    have hFsupp : Function.support F ⊆
        Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
      intro y hy
      have hy' : D.R i Ph a b y ≠ 0 := fun h0 =>
        hy (by show ((D.R i Ph a b y : ℝ) : ℂ) = 0; rw [h0, Complex.ofReal_zero])
      exact D.R_support i Ph a b hy'
    have hres := (hcsqp F CG hFsm hFsupp hjet').2
    have hper : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ∑' n : Fin (Module.finrank ℝ E) → ℤ, F (y + fun j => (n j : ℝ))) = D.Rper i Ph a b := by
      funext y
      rw [hFdef]
      show (∑' n : Fin (Module.finrank ℝ E) → ℤ,
        ((D.R i Ph a b (y + fun j => (n j : ℝ)) : ℝ) : ℂ)) = _
      rw [show D.Rper i Ph a b y = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
        ((D.R i Ph a b (y + iVec m) : ℝ) : ℂ) from rfl]
      rfl
    rw [← hper]
    exact hres
  calc D.BNorm k (Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsm)
      = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          CSq k (fourierCoeff (D.Rper i
            (Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsm) a b)) := rfl
    _ ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (Ccsq * CG ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => hfin i a b
    _ = (Fintype.card ι₀ : ℝ) * (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)
          * (Ccsq * CG ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Work.Diff.STE.Lead
