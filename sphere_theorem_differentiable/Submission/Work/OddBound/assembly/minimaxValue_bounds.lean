import Mathlib
import Submission.Work.OddBound.polygonValueBound
import Submission.Work.OddBound.exists_gonEnergy_le_of_balanced_nullhomotopy
import Submission.Work.OddBound.assembly.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.assembly

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

theorem minimaxValue_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {L : ℝ} (hL : 0 < L) (hLlt : L < 2 * Real.pi / Real.sqrt K) {γ : ℝ → M}
    (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) L, Submission.Length.curveSpeed (I := I) γ t = 1)
    (hper : ∀ t : ℝ, γ (t + L) = γ t) (hγ0 : γ 0 = p)
    {ρ : ℝ} (hρ : 0 < ρ) (hρlt : ρ < Real.pi / Real.sqrt K)
    (hρinj : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x ρ)
    {N : ℕ} (hN : 3 ≤ N) (hbig : 4 * Real.pi ^ 2 / (K * ρ ^ 2) < (N : ℝ))
    {Hf : ℝ → ℝ → M} (hcont : Continuous (fun q : ℝ × ℝ => Hf q.1 q.2))
    (hHfper : ∀ s t : ℝ, Hf (s + 1) t = Hf s t)
    (hHfbase : ∀ t : ℝ, Hf 0 t = p)
    (hHf0 : ∀ s : ℝ, Hf s 0 = γ (L * s))
    (hHf1 : ∀ s : ℝ, Hf s 1 = p)
    (hHfpiece : ∀ t : ℝ, ∃ (k : ℕ) (a : Fin (k + 1) → ℝ),
      StrictMono a ∧ a 0 = 0 ∧ a (Fin.last k) = 1 ∧
      ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => Hf s t)
        (Set.Icc (a j.castSucc) (a j.succ)))
    {B : ℝ} (hB : 0 < B)
    (hHflen : ∀ t : ℝ, Submission.Length.curveLength (I := I) (fun s : ℝ => Hf s t) 0 1 ≤ B)
    (hHfbal : ∀ t s : ℝ,
      Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 s
        = s * Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 1) :
    2 * Real.pi ^ 2 / K
        ≤ Work.OddBound.GonMinimaxValue (N := N) (I := I) p
            (Work.OddBound.inscribedGon L γ) (Work.OddBound.constantGon p) ∧
      Work.OddBound.GonMinimaxValue (N := N) (I := I) p
            (Work.OddBound.inscribedGon L γ) (Work.OddBound.constantGon p) ≤ B ^ 2 / 2 := by
  classical
  have hσcont : Continuous (fun τ : ℝ => fun i : Fin (N - 1) =>
      Hf ((((i : ℕ) : ℝ) + 1) / ((N : ℕ) : ℝ)) τ) := by
    refine continuous_pi (fun i => ?_)
    exact hcont.comp (continuous_const.prodMk continuous_id)
  have hσ0 : (fun τ : ℝ => fun i : Fin (N - 1) =>
        Hf ((((i : ℕ) : ℝ) + 1) / ((N : ℕ) : ℝ)) τ) 0
      = Work.OddBound.inscribedGon (N := N) L γ := by
    funext i
    simp only [Work.OddBound.inscribedGon_apply, hHf0]
    congr 1
    ring
  have hσ1 : (fun τ : ℝ => fun i : Fin (N - 1) =>
        Hf ((((i : ℕ) : ℝ) + 1) / ((N : ℕ) : ℝ)) τ) 1
      = Work.OddBound.constantGon (N := N) p := by
    funext i
    simp only [Work.OddBound.constantGon_apply, hHf1]
  have hσb : ∀ t ∈ Set.Icc (0 : ℝ) 1, Work.OddBound.gonEnergy (I := I) p
      ((fun τ : ℝ => fun i : Fin (N - 1) =>
        Hf ((((i : ℕ) : ℝ) + 1) / ((N : ℕ) : ℝ)) τ) t) ≤ B ^ 2 / 2 := by
    intro t ht
    exact Work.OddBound.exists_gonEnergy_le_of_balanced_nullhomotopy (I := I) (cov := cov)
      hmet htor hL hcont hHfper hHfbase hHf0 hHf1 hHfpiece hB hHflen hHfbal N hN t ht
  have hmem : B ^ 2 / 2 ∈ Work.OddBound.GonMinimaxSet (I := I) (N := N) p
      (Work.OddBound.inscribedGon L γ) (Work.OddBound.constantGon p) :=
    ⟨_, hσcont.continuousOn, hσ0, hσ1, hσb⟩
  have hlow : ∀ m ∈ Work.OddBound.GonMinimaxSet (I := I) (N := N) p
      (Work.OddBound.inscribedGon L γ) (Work.OddBound.constantGon p),
      2 * Real.pi ^ 2 / K ≤ m := by
    intro m hm
    obtain ⟨σ, hσc, hσ0', hσ1', hσE⟩ := hm
    have hfmem : ∀ τ : ℝ, min (max τ 0) 1 ∈ Set.Icc (0 : ℝ) 1 := by
      intro τ
      exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
    have hwcont : Continuous (fun τ : ℝ => σ (min (max τ 0) 1)) :=
      hσc.comp_continuous (by fun_prop) hfmem
    have hw0 : (fun τ : ℝ => σ (min (max τ 0) 1)) 0
        = fun i : Fin (N - 1) => γ (L * ((i : ℕ) + 1) / N) := by
      show σ (min (max (0 : ℝ) 0) 1) = _
      rw [show min (max (0 : ℝ) 0) 1 = 0 by norm_num]
      exact hσ0'
    have hw1 : ∀ i : Fin (N - 1), (fun τ : ℝ => σ (min (max τ 0) 1)) 1 i = p := by
      intro i
      have h1 : min (max (1 : ℝ) 0) 1 = 1 := by norm_num
      simp only [h1, hσ1', Work.OddBound.constantGon_apply]
    obtain ⟨τ, hτ, hτle⟩ := Work.OddBound.polygonValueBound (I := I) (cov := cov)
      hmet htor hK hcurv hL hLlt hγsm hgeo hne hunit hper hγ0 hρ hρlt hρinj hN hbig
      (w := fun τ : ℝ => σ (min (max τ 0) 1)) hwcont hw0 hw1
    calc 2 * Real.pi ^ 2 / K
        ≤ Work.OddBound.gonEnergy (I := I) p
            ((fun τ : ℝ => σ (min (max τ 0) 1)) τ) := hτle
      _ = Work.OddBound.gonEnergy (I := I) p (σ (min (max τ 0) 1)) := rfl
      _ ≤ m := hσE _ (hfmem τ)
  have hne : (Work.OddBound.GonMinimaxSet (I := I) (N := N) p
      (Work.OddBound.inscribedGon L γ) (Work.OddBound.constantGon p)).Nonempty := ⟨_, hmem⟩
  have hbdd : BddBelow (Work.OddBound.GonMinimaxSet (I := I) (N := N) p
      (Work.OddBound.inscribedGon L γ) (Work.OddBound.constantGon p)) :=
    ⟨2 * Real.pi ^ 2 / K, hlow⟩
  exact ⟨le_csInf hne hlow, csInf_le hbdd hmem⟩

end Work.OddBound.assembly
