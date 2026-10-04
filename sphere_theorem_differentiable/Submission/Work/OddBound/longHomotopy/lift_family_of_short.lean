import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.longHomotopy.exists_lift_of_short_bis
import Submission.Work.OddBound.longHomotopy.continuousOn_lift_family_of_short
import Submission.Work.OddBound.longHomotopy.continuousOn_curveLength_family

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]

/-- **Monotonicity of the curve length in the upper endpoint.** -/
theorem curveLength_mono_of_le {γ : ℝ → M} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hint : ∀ x y : ℝ, IntervalIntegrable (curveSpeed (I := I) γ) MeasureTheory.volume x y) :
    curveLength (I := I) γ a b ≤ curveLength (I := I) γ a c := by
  have hadd := curveLength_add_of_integrable (I := I) γ (hint a b) (hint b c)
  have hnn := curveLength_nonneg (I := I) γ hbc
  linarith

/-- **Continuity of the speed along the slices of a smooth family.** -/
theorem continuous_curveSpeed_slice {c : ℝ → ℝ → M}
    (hcsm : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I ∞ (fun u : ℝ × ℝ => c u.1 u.2)) (t : ℝ) :
    Continuous (fun s : ℝ => Submission.Length.curveSpeed (I := I) (fun s' : ℝ => c s' t) s) :=
  (continuous_curveSpeed_family (I := I) hcsm).comp (continuous_id.prodMk continuous_const)

/-- The slice `s ↦ c s t` of a jointly smooth family is `C^∞`, hence `C^1` on any interval. -/
theorem contMDiffOn_slice {c : ℝ → ℝ → M} (hcsm : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I ∞
    (fun u : ℝ × ℝ => c u.1 u.2)) (t : ℝ) {a b : ℝ} :
    ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => c s t) (Set.Icc a b) := by
  have h1 : ContMDiff 𝓘(ℝ) (𝓘(ℝ, ℝ × ℝ)) ∞ (fun s : ℝ => (s, t)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  exact ((hcsm.comp h1).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)).contMDiffOn

/-- **The family lift of a family of short curves.**  The analytic core of Klingenberg's long
homotopy argument: a jointly smooth family of curves `s ↦ c s t` starting at `p`, each of length
`< π/√K`, lifts to the tangent space `T_pM` under the exponential map, jointly continuously, with
the norm bound `‖W s t‖ ≤ curveLength (c · t) 0 s`. -/
theorem lift_family_of_short
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {c : ℝ → ℝ → M} {S : ℝ} (hS : 0 < S)
    (hcsm : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I ∞ (fun u : ℝ × ℝ => c u.1 u.2))
    (hbase : ∀ t : ℝ, c 0 t = p)
    (hlen : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) 0 S < Real.pi / Real.sqrt K) :
    ∃ W : ℝ → ℝ → TangentSpace I p,
      Continuous (fun u : ℝ × ℝ => W u.1 u.2) ∧
      (∀ t : ℝ, W 0 t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) S,
        Submission.GlobalExp.GExp (cov := cov) hmet p (W s t) = c s t ∧
        ‖W s t‖ ≤ Submission.Length.curveLength (I := I) (fun r : ℝ => c r t) 0 s) := by
  classical
  -- ## the slice curves are `C¹`
  have hsm : ∀ t : ℝ, ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => c s t) (Set.Icc (0 : ℝ) S) :=
    fun t => contMDiffOn_slice (I := I) hcsm t
  -- ## the per-`t` lifts (as a proof-irrelevant global choice)
  have hex' : ∀ t : ℝ, ∃ W : ℝ → TangentSpace I p,
      (t ∈ Set.Icc (0 : ℝ) 1 →
        ContinuousOn W (Set.Icc (0 : ℝ) S) ∧ W 0 = 0 ∧
        (∀ s ∈ Set.Icc (0 : ℝ) S, GExp (cov := cov) hmet p (W s) = c s t) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) S, ‖W s‖ ≤ curveLength (I := I) (fun s : ℝ => c s t) 0 s)) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · refine ⟨Classical.choose (exists_lift_of_short_bis (cov := cov) hmet htor hK hcurv hS
        (hsm t) (hbase t) (hlen t ht)), fun _ => ?_⟩
      exact Classical.choose_spec (exists_lift_of_short_bis (cov := cov) hmet htor hK hcurv hS
        (hsm t) (hbase t) (hlen t ht))
    · exact ⟨fun _ => 0, fun h => absurd h ht⟩
  let Wf : ℝ → ℝ → TangentSpace I p := fun t => Classical.choose (hex' t)
  have hWf : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ContinuousOn (Wf t) (Set.Icc (0 : ℝ) S) ∧ Wf t 0 = 0 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S, GExp (cov := cov) hmet p (Wf t s) = c s t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S, ‖Wf t s‖ ≤ curveLength (I := I) (fun s : ℝ => c s t) 0 s) :=
    fun t => Classical.choose_spec (hex' t)
  -- ## the norm bound
  have hbnd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) S,
      ‖Wf t s‖ < Real.pi / Real.sqrt K := by
    intro t ht s hs
    have h1 : ‖Wf t s‖ ≤ curveLength (I := I) (fun s : ℝ => c s t) 0 s := (hWf t ht).2.2.2 s hs
    have h2 : curveLength (I := I) (fun s : ℝ => c s t) 0 s
        ≤ curveLength (I := I) (fun s : ℝ => c s t) 0 S :=
      curveLength_mono_of_le hs.1 hs.2
        (fun x y => (continuous_curveSpeed_slice (I := I) hcsm t).intervalIntegrable x y)
    linarith [hlen t ht]
  -- ## joint continuity on the rectangle
  have hrect : ContinuousOn (fun u : ℝ × ℝ => Wf u.2 u.1)
      (Set.Icc (0 : ℝ) S ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine continuousOn_lift_family_of_short (cov := cov) (W := fun σ τ => Wf τ σ)
      hmet htor hK hcurv hS hcsm hbase ?_ ?_ ?_ ?_
    · intro t ht; exact (hWf t ht).1
    · intro t ht; exact (hWf t ht).2.1
    · intro t ht s hs; exact (hWf t ht).2.2.1 s hs
    · intro t ht s hs; exact hbnd t ht s hs
  -- ## the assembled family
  have hcl : Continuous (fun u : ℝ × ℝ =>
      ((Set.projIcc (0 : ℝ) S (le_of_lt hS) u.1 : ℝ), (Set.projIcc (0 : ℝ) 1 (by norm_num) u.2 : ℝ))) := by
    fun_prop
  have hrect' : ContinuousOn (fun u : ℝ × ℝ => Wf u.2 u.1)
      (Set.Icc (0 : ℝ) S ×ˢ Set.Icc (0 : ℝ) 1) := hrect
  refine ⟨fun s t => Wf (Set.projIcc (0 : ℝ) 1 (by norm_num) t)
      (Set.projIcc (0 : ℝ) S (le_of_lt hS) s), ?_, ?_, ?_⟩
  · exact hrect'.comp_continuous hcl fun u =>
      ⟨(Set.projIcc (0 : ℝ) S (le_of_lt hS) u.1).2, (Set.projIcc (0 : ℝ) 1 (by norm_num) u.2).2⟩
  · intro t
    show Wf (Set.projIcc (0 : ℝ) 1 (by norm_num) t) (Set.projIcc (0 : ℝ) S (le_of_lt hS) 0) = 0
    have h0 : (Set.projIcc (0 : ℝ) S (le_of_lt hS) 0 : ℝ) = 0 :=
      congrArg Subtype.val (Set.projIcc_of_mem (le_of_lt hS) ⟨le_rfl, le_of_lt hS⟩)
    rw [h0]
    have hτ : (Set.projIcc (0 : ℝ) 1 (by norm_num) t : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      (Set.projIcc (0 : ℝ) 1 (by norm_num) t).2
    exact (hWf _ hτ).2.1
  · intro t ht s hs
    have hτ : (Set.projIcc (0 : ℝ) 1 (by norm_num) t : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      (Set.projIcc (0 : ℝ) 1 (by norm_num) t).2
    have hσ : (Set.projIcc (0 : ℝ) S (le_of_lt hS) s : ℝ) ∈ Set.Icc (0 : ℝ) S :=
      (Set.projIcc (0 : ℝ) S (le_of_lt hS) s).2
    have ht' : (Set.projIcc (0 : ℝ) 1 (by norm_num) t : ℝ) = t :=
      congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) ht)
    have hs' : (Set.projIcc (0 : ℝ) S (le_of_lt hS) s : ℝ) = s :=
      congrArg Subtype.val (Set.projIcc_of_mem (le_of_lt hS) hs)
    have hτ_eq : (Set.projIcc (0 : ℝ) 1 (by norm_num) t : ℝ) = t :=
      congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) ht)
    have hspec := hWf _ hτ
    constructor
    · have h := hspec.2.2.1 _ hσ
      simpa only [hτ_eq, hs'] using h
    · have h := hspec.2.2.2 _ hσ
      simpa only [hτ_eq, hs'] using h
end Work.OddBound.longHomotopy
