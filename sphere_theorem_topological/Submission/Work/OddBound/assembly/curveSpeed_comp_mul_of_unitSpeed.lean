import Mathlib
import Submission.Work.OddBound.AssemblyKit

/-!
# The unit speed of an `L`-periodic curve, rescaled to arc length

Let `γ : ℝ → M` be a smooth curve that is `L`-periodic (`γ (t + L) = γ t`) and of unit
speed `1` on the fundamental interval `[0, L]` (in the sense of
`Submission.Length.curveSpeed`).  Then:

* the speed of `γ` is constantly `1` on *all* of `ℝ`: by periodicity the velocity — hence the
  speed — is `L`-periodic, and every real number can be shifted by an integer multiple of `L`
  into `[0, L]`;
* consequently the reparametrised curve `r ↦ γ (L * r)`, which traces one period over `[0, 1]`,
  has constant speed `L`, and its length over `[0,1]` is `L`.

The velocity is `L`-periodic because `γ (· + L) = γ` as functions, so by the chain rule
(`Submission.SecondVarGlobal.curveSpeed_comp_add_right`) the speed of the translate at `t` equals
the speed of `γ` at `t + L`, while the speed of a translate agrees with that of `γ` by
`Submission.GeodesicSpeed.curveSpeed_congr_of_eventuallyEq`.

The rescaling uses the affine-reparametrisation lemmas of `Submission.Length`:
`curveSpeed_comp_mul_add` and `curveLength_comp_mul_add_of_pos`.
-/

namespace Work.OddBound.assembly

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

theorem curveSpeed_comp_mul_of_unitSpeed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {L : ℝ} (hL : 0 < L) {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) L, Submission.Length.curveSpeed (I := I) γ t = 1)
    (hper : ∀ t : ℝ, γ (t + L) = γ t) :
    (∀ s : ℝ, Submission.Length.curveSpeed (I := I) (fun r : ℝ => γ (L * r)) s = L) ∧
      Submission.Length.curveLength (I := I) (fun r : ℝ => γ (L * r)) 0 1 = L := by
  have hLne : L ≠ 0 := ne_of_gt hL
  -- `γ` is differentiable everywhere.
  have hmd : ∀ t : ℝ, MDifferentiableAt 𝓘(ℝ) I γ t :=
    fun t => hγsm.contMDiffAt.mdifferentiableAt (by simp)
  -- The translate `γ (· + L)` is `γ` itself.
  have hshift : (fun x : ℝ => γ (x + L)) = γ := by
    funext x
    exact hper x
  -- Hence the speed of `γ` is `L`-periodic.
  have hsper : ∀ t : ℝ, curveSpeed (I := I) γ (t + L) = curveSpeed (I := I) γ t := by
    intro t
    have h1 : curveSpeed (I := I) (fun x : ℝ => γ (x + L)) t = curveSpeed (I := I) γ t :=
      Submission.GeodesicSpeed.curveSpeed_congr_of_eventuallyEq (I := I)
        (γ := fun x : ℝ => γ (x + L)) (γ' := γ) (s := t) (Filter.EventuallyEq.of_eq hshift)
    have h2 : curveSpeed (I := I) (fun x : ℝ => γ (x + L)) t = curveSpeed (I := I) γ (t + L) :=
      Submission.SecondVarGlobal.curveSpeed_comp_add_right (I := I) γ L t (hmd (t + L))
    exact h2.symm.trans h1
  have hgp : Function.Periodic (curveSpeed (I := I) γ) L := fun t => hsper t
  -- Shifting by an integer multiple of `L` brings every time into `[0, L]`, where the speed is `1`.
  have hunit' : ∀ t : ℝ, curveSpeed (I := I) γ t = 1 := by
    intro t
    obtain ⟨n, hn⟩ : ∃ n : ℤ, t + (n : ℝ) * L ∈ Set.Icc (0 : ℝ) L := by
      refine ⟨-⌊t / L⌋, ?_⟩
      have hmm : (⌊t / L⌋ : ℝ) ≤ t / L := Int.floor_le _
      have hlt : t / L < (⌊t / L⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h1 : (⌊t / L⌋ : ℝ) * L ≤ (t / L) * L := mul_le_mul_of_nonneg_right hmm hL.le
      rw [div_mul_cancel₀ (b := L) t hLne] at h1
      have h2 : (t / L) * L < ((⌊t / L⌋ : ℝ) + 1) * L := mul_lt_mul_of_pos_right hlt hL
      rw [div_mul_cancel₀ (b := L) t hLne, add_mul, one_mul] at h2
      have heq : t + (↑(-⌊t / L⌋) : ℝ) * L = t - (⌊t / L⌋ : ℝ) * L := by
        push_cast
        ring
      rw [heq]
      exact ⟨by linarith, by linarith⟩
    have hz : curveSpeed (I := I) γ (t + (n : ℝ) * L) = curveSpeed (I := I) γ t := by
      have h := (hgp.zsmul n) t
      simpa using h
    rw [← hz]
    exact hunit _ hn
  -- `γ (L * ·)` is the affine reparametrisation of `γ` with `c = L`, `d = 0`.
  have hfun : (fun r : ℝ => γ (L * r)) = (fun r : ℝ => γ (L * r + 0)) := by
    funext r
    rw [add_zero]
  constructor
  · intro s
    rw [hfun, curveSpeed_comp_mul_add (I := I) (c := L) (d := 0) (t := s) hL
      (by simpa using hmd (L * s)), add_zero, hunit' (L * s), mul_one]
  · rw [hfun, curveLength_comp_mul_add_of_pos (I := I) (c := L) (d := 0) (a := 0) (b := 1) hL
      (fun t => by simpa using hmd (L * t))]
    simp only [mul_zero, mul_one, add_zero]
    rw [curveLength_def,
      intervalIntegral.integral_congr_Ioo_of_le hL.le
        (fun t ht => hunit t (Set.Ioo_subset_Icc_self ht)),
      intervalIntegral.integral_const]
    simp

end Work.OddBound.assembly
