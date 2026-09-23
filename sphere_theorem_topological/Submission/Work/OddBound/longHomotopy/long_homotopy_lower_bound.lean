import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.Minimax
import Submission.Work.OddBound.longHomotopy.lift_family_of_short
import Submission.Work.OddBound.longHomotopy.lift_of_geodesic_ray
import Submission.Work.OddBound.longHomotopy.eq_at_zero_of_continuous_lift_eq
import Submission.Work.OddBound.longHomotopy.curveLength_comp_sub

/-!
# Klingenberg's long homotopy lemma

The statement `Work.OddBound.LongHomotopyLowerBound`, proved here: every based null-homotopy `H` of a
closed geodesic `γ` of period `L` contains a curve whose two halves (from the base point `s = 0` to
the midpoint `s = 1/2` and from the midpoint to the endpoint `s = 1`) are not both shorter than
`π/√K`.

The proof is Klingenberg's lifting argument (Klingenberg 1962, p. 50; Abresch–Meyer Lemma 4.3):

* both halves of the family lift to the tangent space `T_pM` under `GExp p`
  (`Work.OddBound.longHomotopy.lift_family_of_short`), continuously in the family parameter and with
  the norm bound `‖W s t‖ ≤ curveLength (H · t) 0 s`;
* at the parameter value `t = 0` the two lifted halves are the straight rays of the two halves of the
  geodesic `γ` (`Work.OddBound.longHomotopy.lift_of_geodesic_ray`), namely
  `(1/2) • (L • γ'(0))` and `(1/2) • (-(L • γ'(0)))`;
* at the parameter value `t = 1` the two lifted halves are those of the constant curve, hence both
  are `0`;
* the open-and-closed argument `Work.OddBound.longHomotopy.eq_at_zero_of_continuous_lift_eq` then
  forces the two `t = 0` values to coincide, i.e. `L • γ'(0) = -(L • γ'(0))`, so `γ'(0) = 0` ---
  contradicting the hypothesis that the velocity of `γ` never vanishes.
-/

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **Velocity of an affinely reparametrised curve at time `0`.** -/
private lemma curveVelocity_comp_mul_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ) (a : ℝ) :
    curveVelocity (I := I) (fun s : ℝ => γ (a * s)) 0
      = a • curveVelocity (I := I) γ 0 := by
  have hd : MDifferentiableAt 𝓘(ℝ) I γ (a * 0 + 0) :=
    hγsm.contMDiffAt.mdifferentiableAt (by simp)
  have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := a) (d := 0)
    (t := 0) hd
  rw [show a * 0 + 0 = (0 : ℝ) by ring] at h
  have hfun : (fun s : ℝ => γ (a * s + 0)) = (fun s : ℝ => γ (a * s)) := by
    funext s; rw [add_zero]
  rw [hfun] at h
  rw [show a * 0 = (0 : ℝ) by ring]
  exact h

/-- **Smoothness of an affinely reparametrised curve.** -/
private lemma contMDiff_comp_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ) (a : ℝ) :
    ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => γ (a * s)) := by
  have h1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => a * s) := by
    rw [contMDiff_iff_contDiff]; fun_prop
  have h := hγsm.comp h1
  simpa [Function.comp_def] using h

/-- **A geodesic reparametrised affinely is a geodesic.** -/
private lemma isGeodesicAt_comp_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t) {a : ℝ} (ha : a ≠ 0) :
    ∀ t : ℝ, IsGeodesicAt (I := I) cov (fun s : ℝ => γ (a * s)) t := by
  intro t
  have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := γ) (a := a) (b := 0)
    (c := a * t - 1) (d := a * t + 1) ha hγsm.contMDiffOn (fun y _ => hgeo y) (r := t)
    (by constructor <;> linarith)
  simpa using h

theorem long_homotopy_lower_bound
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
    {p : M} {L : ℝ} (hL : 0 < L) {γ : ℝ → M}
    (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    (hper : ∀ t : ℝ, γ (t + L) = γ t) (h0 : γ 0 = p) :
    Work.OddBound.LongHomotopyLowerBound (I := I) K p L γ := by
  classical
  intro H hH hlen
  rcases hH with ⟨hcsm, hperH, hbaseH, hstartH, hendH⟩
  -- ## the two families of short curves and their lifts
  have hlen₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      curveLength (I := I) (fun s : ℝ => H s t) 0 (1/2) < Real.pi / Real.sqrt K :=
    fun t ht => (hlen t ht).1
  obtain ⟨Wp, hWpc, hWp0, hWpG⟩ :=
    lift_family_of_short (I := I) (cov := cov) hmet htor hK hcurv (p := p) (c := H) (S := 1/2)
      (by norm_num) hcsm hbaseH hlen₁
  have hc₂ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (fun u : ℝ × ℝ => H (1 - u.1) u.2) := by
    have hφ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun u : ℝ × ℝ => (1 - u.1, u.2)) := by
      rw [contMDiff_iff_contDiff]; fun_prop
    have h := hcsm.comp hφ
    simpa [Function.comp_def] using h
  have hbase₂ : ∀ t : ℝ, H (1 - 0) t = p := fun t => by
    simpa using (hperH 0 t).trans (hbaseH t)
  have hlen₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      curveLength (I := I) (fun s : ℝ => H (1 - s) t) 0 (1/2) < Real.pi / Real.sqrt K := by
    intro t ht
    have hcomp := curveLength_comp_sub (I := I) (c := fun s : ℝ => H s t) (a := 1/2) (b := 1)
      (by norm_num) (contMDiffOn_slice (I := I) hcsm t)
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num] at hcomp
    rw [hcomp]
    exact (hlen t ht).2
  obtain ⟨Wm, hWmc, hWm0, hWmG⟩ :=
    lift_family_of_short (I := I) (cov := cov) hmet htor hK hcurv (p := p)
      (c := fun s t => H (1 - s) t) (S := 1/2) (by norm_num) hc₂ hbase₂ hlen₂
  -- ## the two lifts of the half-time curve
  have hc₁ : ContinuousOn (fun t : ℝ => Wp (1/2) t) (Set.Icc (0:ℝ) 1) :=
    (hWpc.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hc₂' : ContinuousOn (fun t : ℝ => Wm (1/2) t) (Set.Icc (0:ℝ) 1) :=
    (hWmc.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hb₁ : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖Wp (1/2) t‖ < Real.pi / Real.sqrt K := by
    intro t ht
    have h1 : ‖Wp (1/2) t‖ ≤ curveLength (I := I) (fun r : ℝ => H r t) 0 (1/2) :=
      ((hWpG t ht) (1/2) ⟨by norm_num, le_refl _⟩).2
    linarith [(hlen t ht).1]
  have hb₂ : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖Wm (1/2) t‖ < Real.pi / Real.sqrt K := by
    intro t ht
    have h1 : ‖Wm (1/2) t‖ ≤ curveLength (I := I) (fun r : ℝ => H (1 - r) t) 0 (1/2) :=
      ((hWmG t ht) (1/2) ⟨by norm_num, le_refl _⟩).2
    linarith [hlen₂ t ht]
  have hG : ∀ t ∈ Set.Icc (0:ℝ) 1,
      GExp (cov := cov) hmet p (Wp (1/2) t) = GExp (cov := cov) hmet p (Wm (1/2) t) := by
    intro t ht
    have h1 : GExp (cov := cov) hmet p (Wp (1/2) t) = H (1/2) t :=
      ((hWpG t ht) (1/2) ⟨by norm_num, le_refl _⟩).1
    have h2 : GExp (cov := cov) hmet p (Wm (1/2) t) = H (1 - 1/2) t :=
      ((hWmG t ht) (1/2) ⟨by norm_num, le_refl _⟩).1
    rw [h1, h2, show (1:ℝ) - 1/2 = 1/2 by norm_num]
  -- ## at the parameter value `1` both lifts are those of the constant curve
  have hend1 : Wp (1/2) 1 = (1/2 : ℝ) • curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
    have hconst : (fun s : ℝ => H s 1) = (fun _ : ℝ => p) := funext hendH
    have hgeo' : ∀ t : ℝ, IsGeodesicAt (I := I) cov (fun s : ℝ => H s 1) t := by
      intro t
      rw [hconst]
      exact (Submission.Geodesic.isGeodesic_const (I := I) cov p) t
    have hsm' : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => H s 1) := by
      have h1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ => (s, (1 : ℝ))) := by
        rw [contMDiff_iff_contDiff]; fun_prop
      have h := hcsm.comp h1
      simpa [Function.comp_def] using h
    have hb : ∀ s ∈ Set.Icc (0:ℝ) (1/2), ‖Wp s 1‖ < Real.pi / Real.sqrt K := by
      intro s hs
      have h1 : ‖Wp s 1‖ ≤ curveLength (I := I) (fun r : ℝ => H r 1) 0 s :=
        ((hWpG 1 ⟨by norm_num, le_refl 1⟩) s hs).2
      have h2 : curveLength (I := I) (fun r : ℝ => H r 1) 0 s
          ≤ curveLength (I := I) (fun r : ℝ => H r 1) 0 (1/2) :=
        curveLength_mono_of_le (I := I) hs.1 hs.2
          (fun x y => (continuous_curveSpeed_slice (I := I) hcsm 1).intervalIntegrable x y)
      linarith [(hlen 1 ⟨by norm_num, le_refl 1⟩).1]
    have hspec := lift_of_geodesic_ray (I := I) (cov := cov) hmet htor hK hcurv (p := p)
      (h := fun s : ℝ => H s 1) (S := 1/2) (by norm_num) hgeo' hsm' (hendH 0)
      (W := fun s : ℝ => Wp s 1) (hWpc.comp (continuous_id.prodMk continuous_const)).continuousOn
      (hWp0 1) (fun s hs => ((hWpG 1 ⟨by norm_num, le_refl 1⟩) s hs).1) hb
    have hv : curveVelocity (I := I) (fun s : ℝ => H s 1) 0
        = curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
      rw [hconst]
    exact (hspec (1/2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1/2 : ℝ) • w) hv)
  have hend2 : Wm (1/2) 1 = (1/2 : ℝ) • curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
    have hconst : (fun s : ℝ => H (1 - s) 1) = (fun _ : ℝ => p) := funext fun s => hendH (1 - s)
    have hgeo' : ∀ t : ℝ, IsGeodesicAt (I := I) cov (fun s : ℝ => H (1 - s) 1) t := by
      intro t
      rw [hconst]
      exact (Submission.Geodesic.isGeodesic_const (I := I) cov p) t
    have hsm' : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => H (1 - s) 1) := by
      have h1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ => (1 - s, (1 : ℝ))) := by
        rw [contMDiff_iff_contDiff]; fun_prop
      have h := hcsm.comp h1
      simpa [Function.comp_def] using h
    have hb : ∀ s ∈ Set.Icc (0:ℝ) (1/2), ‖Wm s 1‖ < Real.pi / Real.sqrt K := by
      intro s hs
      have h1 : ‖Wm s 1‖ ≤ curveLength (I := I) (fun r : ℝ => H (1 - r) 1) 0 s :=
        ((hWmG 1 ⟨by norm_num, le_refl 1⟩) s hs).2
      have h2 : curveLength (I := I) (fun r : ℝ => H (1 - r) 1) 0 s
          ≤ curveLength (I := I) (fun r : ℝ => H (1 - r) 1) 0 (1/2) :=
        curveLength_mono_of_le (I := I) hs.1 hs.2
          (fun x y => (continuous_curveSpeed_slice (I := I) hc₂ 1).intervalIntegrable x y)
      linarith [hlen₂ 1 ⟨by norm_num, le_refl 1⟩]
    have hspec := lift_of_geodesic_ray (I := I) (cov := cov) hmet htor hK hcurv (p := p)
      (h := fun s : ℝ => H (1 - s) 1) (S := 1/2) (by norm_num) hgeo' hsm' (hendH (1 - 0))
      (W := fun s : ℝ => Wm s 1) (hWmc.comp (continuous_id.prodMk continuous_const)).continuousOn
      (hWm0 1) (fun s hs => ((hWmG 1 ⟨by norm_num, le_refl 1⟩) s hs).1) hb
    have hv : curveVelocity (I := I) (fun s : ℝ => H (1 - s) 1) 0
        = curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
      rw [hconst]
    exact (hspec (1/2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1/2 : ℝ) • w) hv)
  have h1eq : Wp (1/2) 1 = Wm (1/2) 1 := hend1.trans hend2.symm
  -- ## the open-and-closed step
  have hclopen : Wp (1/2) 0 = Wm (1/2) 0 :=
    eq_at_zero_of_continuous_lift_eq (I := I) (cov := cov) hmet htor hK hcurv
      hc₁ hc₂' hb₁ hb₂ hG h1eq
  -- ## at the parameter value `0` the lifts are the straight rays of the two halves of `γ`
  have hgeo₁ : ∀ t : ℝ, IsGeodesicAt (I := I) cov (fun s : ℝ => γ (L * s)) t :=
    isGeodesicAt_comp_mul (I := I) (cov := cov) hγsm hgeo (ne_of_gt hL)
  have hsm₁ : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => γ (L * s)) :=
    contMDiff_comp_mul (I := I) hγsm L
  have hb₁' : ∀ s ∈ Set.Icc (0:ℝ) (1/2), ‖Wp s 0‖ < Real.pi / Real.sqrt K := by
    intro s hs
    have h1 : ‖Wp s 0‖ ≤ curveLength (I := I) (fun r : ℝ => H r 0) 0 s :=
      ((hWpG 0 ⟨le_refl 0, by norm_num⟩) s hs).2
    have h2 : curveLength (I := I) (fun r : ℝ => H r 0) 0 s
        ≤ curveLength (I := I) (fun r : ℝ => H r 0) 0 (1/2) :=
      curveLength_mono_of_le (I := I) hs.1 hs.2
        (fun x y => (continuous_curveSpeed_slice (I := I) hcsm 0).intervalIntegrable x y)
    linarith [(hlen 0 ⟨le_refl 0, by norm_num⟩).1]
  have hP : Wp (1/2) 0 = (1/2 : ℝ) • (L • curveVelocity (I := I) γ 0) := by
    have hspec := lift_of_geodesic_ray (I := I) (cov := cov) hmet htor hK hcurv (p := p)
      (h := fun s : ℝ => γ (L * s)) (S := 1/2) (by norm_num) hgeo₁ hsm₁ (by simp [h0])
      (W := fun s : ℝ => Wp s 0) (hWpc.comp (continuous_id.prodMk continuous_const)).continuousOn
      (hWp0 0)
      (fun s hs => (((hWpG 0 ⟨le_refl 0, by norm_num⟩) s hs).1).trans (hstartH s))
      hb₁'
    exact (hspec (1/2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1/2 : ℝ) • w) (curveVelocity_comp_mul_zero (I := I) hγsm L))
  have hgeo₂ : ∀ t : ℝ, IsGeodesicAt (I := I) cov (fun s : ℝ => γ ((-L) * s)) t :=
    isGeodesicAt_comp_mul (I := I) (cov := cov) hγsm hgeo
      (neg_ne_zero.mpr (ne_of_gt hL))
  have hsm₂ : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => γ ((-L) * s)) :=
    contMDiff_comp_mul (I := I) hγsm (-L)
  have hper' : ∀ s : ℝ, γ (L * (1 - s)) = γ ((-L) * s) := by
    intro s
    have h := hper ((-L) * s)
    have he : (-L) * s + L = L * (1 - s) := by ring
    rw [he] at h
    exact h
  have hb₂' : ∀ s ∈ Set.Icc (0:ℝ) (1/2), ‖Wm s 0‖ < Real.pi / Real.sqrt K := by
    intro s hs
    have h1 : ‖Wm s 0‖ ≤ curveLength (I := I) (fun r : ℝ => H (1 - r) 0) 0 s :=
      ((hWmG 0 ⟨le_refl 0, by norm_num⟩) s hs).2
    have h2 : curveLength (I := I) (fun r : ℝ => H (1 - r) 0) 0 s
        ≤ curveLength (I := I) (fun r : ℝ => H (1 - r) 0) 0 (1/2) :=
      curveLength_mono_of_le (I := I) hs.1 hs.2
        (fun x y => (continuous_curveSpeed_slice (I := I) hc₂ 0).intervalIntegrable x y)
    linarith [hlen₂ 0 ⟨le_refl 0, by norm_num⟩]
  have hM : Wm (1/2) 0 = (1/2 : ℝ) • ((-L) • curveVelocity (I := I) γ 0) := by
    have hspec := lift_of_geodesic_ray (I := I) (cov := cov) hmet htor hK hcurv (p := p)
      (h := fun s : ℝ => γ ((-L) * s)) (S := 1/2) (by norm_num) hgeo₂ hsm₂ (by simp [h0])
      (W := fun s : ℝ => Wm s 0) (hWmc.comp (continuous_id.prodMk continuous_const)).continuousOn
      (hWm0 0)
      (fun s hs => (((hWmG 0 ⟨le_refl 0, by norm_num⟩) s hs).1).trans
        (by rw [hstartH (1 - s), hper' s]))
      hb₂'
    exact (hspec (1/2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1/2 : ℝ) • w) (curveVelocity_comp_mul_zero (I := I) hγsm (-L)))
  -- ## contradiction: `L • γ'(0) = -(L • γ'(0))` forces `γ'(0) = 0`
  have hvv : (1/2 : ℝ) • (L • curveVelocity (I := I) γ 0)
      = (1/2 : ℝ) • ((-L) • curveVelocity (I := I) γ 0) :=
    hP.symm.trans (hclopen.trans hM)
  have hLv : L • curveVelocity (I := I) γ 0 = 0 := by
    have h1 : (1/2 : ℝ) • (L • curveVelocity (I := I) γ 0)
        = -((1/2 : ℝ) • (L • curveVelocity (I := I) γ 0)) := by
      nth_rewrite 1 [hvv]
      rw [neg_smul, smul_neg]
    have h3 : (1/2 : ℝ) • (L • curveVelocity (I := I) γ 0)
        + (1/2 : ℝ) • (L • curveVelocity (I := I) γ 0) = 0 := by
      nth_rewrite 1 [h1]
      rw [neg_add_cancel]
    have h4 : (2 : ℝ) • ((1/2 : ℝ) • (L • curveVelocity (I := I) γ 0)) = 0 := by
      rw [two_smul]
      exact h3
    have h5 : (1/2 : ℝ) • (L • curveVelocity (I := I) γ 0) = 0 := by
      rcases (smul_eq_zero.mp h4) with h | h
      · norm_num at h
      · exact h
    rcases (smul_eq_zero.mp h5) with h | h
    · norm_num at h
    · exact h
  have hv : curveVelocity (I := I) γ 0 = 0 := by
    rcases (smul_eq_zero.mp hLv) with h | h
    · exact absurd h (ne_of_gt hL)
    · exact h
  exact hne 0 hv

end Work.OddBound.longHomotopy
