import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.design.RelaxedLHL
import Submission.Work.OddBound.longHomotopy.lift_family_continuity_core
import Submission.Work.OddBound.longHomotopy.curveLength_toolkit
import Submission.Work.OddBound.longHomotopy.exists_lift_of_short_bis
import Submission.Work.OddBound.longHomotopy.eq_at_zero_of_continuous_lift_eq
import Submission.Work.OddBound.longHomotopy.lift_of_geodesic_ray
import Submission.Work.OddBound.longHomotopy.curveLength_comp_sub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Klingenberg's long homotopy lemma, with relaxed regularity

The statement `Work.OddBound.relaxedLHL.long_homotopy_lower_bound_relaxed`, proved here: every based
null-homotopy `c` of a closed geodesic `γ` of period `L` whose slices `s ↦ c s t` are *jointly*
`C^∞` only on `univ ×ˢ Ico 0 1` (and merely *continuous* on the whole plane) such that both halves
of every slice are shorter than `π/√K` is impossible.

The proof is Klingenberg's lifting argument (Klingenberg 1962, p. 50; Abresch–Meyer Lemma 4.3), in
exactly the same shape as the jointly smooth case
(`Work.OddBound.longHomotopy.long_homotopy_lower_bound`), but with the parametric lifting step done
for a merely *continuous* family with `C¹` slices:

* each half of each slice is a curve from `p` of length `< π/√K`, so it lifts under `GExp p` to a
  curve in `T_pM` starting at `0` with the radial norm bound (`exists_lift_of_short_bis`);
* the family of these slice-wise lifts is *jointly* continuous in `(s,t)` by
  `lift_family_continuity_core`, which needs only the continuity of the family and the *strict*
  norm bound `< π/√K` (no smoothness, no injectivity radius of `GExp p`);
* the open-and-closed argument (`eq_at_zero_of_continuous_lift_eq`) at the midpoint `s = 1/2`
  transfers the agreement of the two lifts at `t = 1` (where the slices are constant, so both lifts
  are `0`) to `t = 0`, where the two lifts are the straight rays of the two halves of `γ`;
* hence `L • γ'(0) = -(L • γ'(0))`, i.e. `γ'(0) = 0`, contradicting the hypothesis that the velocity
  of `γ` never vanishes.
-/

namespace Work.OddBound.relaxedLHL

open scoped ContDiff Manifold
open Bundle
open ContDiff
open Set
open MeasureTheory
open scoped Interval

/-- **Velocity of an affinely reparametrised curve at time `0`.** -/
private lemma curveVelocity_comp_mul_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ) (a : ℝ) :
    Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => γ (a * s)) 0
      = a • Submission.Geodesic.curveVelocity (I := I) γ 0 := by
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
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t) {a : ℝ} (ha : a ≠ 0) :
    ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => γ (a * s)) t := by
  intro t
  have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := γ) (a := a) (b := 0)
    (c := a * t - 1) (d := a * t + 1) ha hγsm.contMDiffOn (fun y _ => hgeo y) (r := t)
    (by constructor <;> linarith)
  simpa using h

/-- **The parametric lifting lemma for a merely continuous family of short curves.**

Let `c : ℝ × ℝ → M` be *continuous*, with `c 0 t = p` and with `c (·,t)` of class `C¹` and of length
`< π/√K` on `[0,S]` for every `t ∈ [0,1]` (the slices of the relaxed family of the long homotopy
lemma; no joint smoothness is assumed).  Then the slice-wise lifts under `GExp p` — which exist by
`exists_lift_of_short_bis` — are *jointly* continuous on the rectangle `[0,S] × [0,1]` and satisfy the
strict norm bound `‖W s t‖ < π/√K`.

This is the relaxed form of `Work.OddBound.longHomotopy.lift_family_of_short`: the joint smoothness
of the family is replaced by the continuity of the family, and the joint continuity of the lifts on
the *closed* rectangle is obtained from `lift_family_continuity_core`, which uses only that
continuity, the slice-wise continuity of the lifts and the strict norm bound. -/
private lemma exists_lift_family_of_relaxed_short
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
    {p : M} {c : ℝ → ℝ → M} {S : ℝ} (hS : 0 < S)
    (hcont : Continuous (fun u : ℝ × ℝ => c u.1 u.2))
    (hslice : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => c s t) (Set.Icc (0 : ℝ) S))
    (hbase : ∀ t ∈ Set.Icc (0 : ℝ) 1, c 0 t = p)
    (hlen : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) 0 S < Real.pi / Real.sqrt K) :
    ∃ W : ℝ → ℝ → TangentSpace I p,
      ContinuousOn (fun u : ℝ × ℝ => W u.1 u.2) (Set.Icc (0 : ℝ) S ×ˢ Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, W 0 t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) S,
        Submission.GlobalExp.GExp (cov := cov) hmet p (W s t) = c s t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) S, ‖W s t‖ < Real.pi / Real.sqrt K) := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : CompleteSpace (TangentSpace I p) := inferInstance
  -- ## the slice-wise lifts, fixed once and for all
  have hex : ∀ t : ℝ, ∃ W : ℝ → TangentSpace I p,
      (t ∈ Set.Icc (0 : ℝ) 1 →
        ContinuousOn W (Set.Icc (0 : ℝ) S) ∧ W 0 = 0 ∧
        (∀ s ∈ Set.Icc (0 : ℝ) S,
          Submission.GlobalExp.GExp (cov := cov) hmet p (W s) = c s t) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) S,
          ‖W s‖ ≤ Submission.Length.curveLength (I := I) (fun r : ℝ => c r t) 0 s)) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have h := Work.OddBound.longHomotopy.exists_lift_of_short_bis (I := I) (cov := cov)
        hmet htor hK hcurv (p := p) (h := fun s : ℝ => c s t) (S := S) hS
        (hslice t ht) (hbase t ht) (hlen t ht)
      exact ⟨Classical.choose h, fun _ => Classical.choose_spec h⟩
    · exact ⟨fun _ => 0, fun h => absurd h ht⟩
  let W : ℝ → ℝ → TangentSpace I p := fun s t => Classical.choose (hex t) s
  have hW : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ContinuousOn (fun s : ℝ => W s t) (Set.Icc (0 : ℝ) S) ∧ W 0 t = 0 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S,
        Submission.GlobalExp.GExp (cov := cov) hmet p (W s t) = c s t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S,
        ‖W s t‖ ≤ Submission.Length.curveLength (I := I) (fun r : ℝ => c r t) 0 s) :=
    fun t ht => Classical.choose_spec (hex t) ht
  -- ## the strict norm bound
  have hWb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) S,
      ‖W s t‖ < Real.pi / Real.sqrt K := by
    intro t ht s hs
    have h1 := (hW t ht).2.2.2 s hs
    have h2 := (Work.OddBound.longHomotopy.curveLength_toolkit (I := I) (h := fun r : ℝ => c r t)
      (S := S) (hslice t ht)).2.1 s S hs.1 hs.2 le_rfl
    linarith [hlen t ht]
  -- ## joint continuity on the closed rectangle
  have hWc : ContinuousOn (fun u : ℝ × ℝ => W u.1 u.2)
      (Set.Icc (0 : ℝ) S ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine Work.OddBound.longHomotopy.lift_family_continuity_core
      (X := TangentSpace I p) (Y := M)
      (f := fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v)
      (R := Real.pi / Real.sqrt K)
      (hf := continuous_iff_continuousAt.mpr (fun v =>
        (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p v).continuousAt))
      (hloc := fun v hv =>
        Work.OddBound.longHomotopy.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt
          (cov := cov) hmet htor hK hcurv hv)
      (Φ := fun u : ℝ × ℝ => c u.1 u.2) (hΦ := hcont)
      (W := W) (S := S)
      (fun t ht => (hW t ht).1) (fun t ht => (hW t ht).2.1)
      (fun t ht s hs => (hW t ht).2.2.1 s hs) (fun t ht s hs => hWb t ht s hs)
  exact ⟨W, hWc, fun t ht => (hW t ht).2.1,
    fun t ht s hs => (hW t ht).2.2.1 s hs, fun t ht s hs => hWb t ht s hs⟩

theorem long_homotopy_lower_bound_relaxed
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
    (hper : ∀ t : ℝ, γ (t + L) = γ t) (h0 : γ 0 = p)
    {c : ℝ → ℝ → M}
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) I ∞ (fun u : ℝ × ℝ => c u.1 u.2)
        (Set.univ ×ˢ Set.Ico (0 : ℝ) 1))
    (hcont : Continuous (fun u : ℝ × ℝ => c u.1 u.2))
    (hcper : ∀ s t : ℝ, c (s + 1) t = c s t) (hcbase : ∀ t : ℝ, c 0 t = p)
    (hc0 : ∀ s : ℝ, c s 0 = γ (L * s))
    (hc1 : ∀ s : ℝ, c s 1 = p)
    (hlen : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) 0 (1 / 2) < Real.pi / Real.sqrt K ∧
      Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) (1 / 2) 1 < Real.pi / Real.sqrt K) :
    False := by
  classical
  -- ## 0. the slices are `C¹` on every interval, for `t ∈ [0,1]`
  have hsliceC1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ a b : ℝ,
      ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => c s t) (Set.Icc a b) := by
    intro t ht a b
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have ht' : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht.1, hlt⟩
      have h1 : ContMDiff 𝓘(ℝ) (𝓘(ℝ, ℝ × ℝ)) ∞ (fun s : ℝ => (s, t)) := by
        rw [contMDiff_iff_contDiff]; fun_prop
      have hcomp : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => c s t) (Set.Icc a b) :=
        hsmooth.comp h1.contMDiffOn (fun x _ => ⟨Set.mem_univ _, ht'⟩)
      exact hcomp.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)
    · subst heq
      have hconst : (fun s : ℝ => c s 1) = (fun _ : ℝ => p) := funext (fun s => hc1 s)
      rw [hconst]
      exact contMDiffOn_const
  -- ## 1. the lifts of the two half-families
  obtain ⟨Wp, hWpc, hWp0, hWpG, hWpb⟩ :=
    exists_lift_family_of_relaxed_short (I := I) (cov := cov) hmet htor hK hcurv (p := p) (c := c)
      (S := 1 / 2) (by norm_num) hcont (fun t ht => hsliceC1 t ht 0 (1 / 2))
      (fun t ht => hcbase t) (fun t ht => (hlen t ht).1)
  have hcont₂ : Continuous (fun u : ℝ × ℝ => c (1 - u.1) u.2) := by
    have h1 : Continuous (fun u : ℝ × ℝ => ((1 - u.1), u.2)) := by fun_prop
    exact hcont.comp h1
  have hslice₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => c (1 - s) t) (Set.Icc (0 : ℝ) (1 / 2)) := by
    intro t ht
    have h1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ) 1 (fun s : ℝ => 1 - s) := by
      rw [contMDiff_iff_contDiff]; fun_prop
    exact (hsliceC1 t ht (1 / 2) 1).comp h1.contMDiffOn
      (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hbase₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, c (1 - 0) t = p := by
    intro t ht
    simpa using (hcper 0 t).trans (hcbase t)
  have hlen₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Submission.Length.curveLength (I := I) (fun s : ℝ => c (1 - s) t) 0 (1 / 2)
        < Real.pi / Real.sqrt K := by
    intro t ht
    have hcomp := Work.OddBound.longHomotopy.curveLength_comp_sub (I := I) (c := fun r : ℝ => c r t)
      (a := 1 / 2) (b := 1) (by norm_num) (hsliceC1 t ht (1 / 2) 1)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hcomp
    rw [hcomp]
    exact (hlen t ht).2
  obtain ⟨Wm, hWmc, hWm0, hWmG, hWmb⟩ :=
    exists_lift_family_of_relaxed_short (I := I) (cov := cov) hmet htor hK hcurv (p := p)
      (c := fun s t => c (1 - s) t) (S := 1 / 2) (by norm_num) hcont₂ hslice₂ hbase₂ hlen₂
  -- ## 2. the two lifts of the half-time curve
  have hsec₁ : ContinuousOn (fun t : ℝ => Wp (1 / 2) t) (Set.Icc (0 : ℝ) 1) :=
    hWpc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨⟨by norm_num, le_refl _⟩, ht⟩)
  have hsec₂ : ContinuousOn (fun t : ℝ => Wm (1 / 2) t) (Set.Icc (0 : ℝ) 1) :=
    hWmc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨⟨by norm_num, le_refl _⟩, ht⟩)
  have hb₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Wp (1 / 2) t‖ < Real.pi / Real.sqrt K :=
    fun t ht => hWpb t ht (1 / 2) ⟨by norm_num, le_refl _⟩
  have hb₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Wm (1 / 2) t‖ < Real.pi / Real.sqrt K :=
    fun t ht => hWmb t ht (1 / 2) ⟨by norm_num, le_refl _⟩
  have hG : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Submission.GlobalExp.GExp (cov := cov) hmet p (Wp (1 / 2) t)
        = Submission.GlobalExp.GExp (cov := cov) hmet p (Wm (1 / 2) t) := by
    intro t ht
    rw [hWpG t ht (1 / 2) ⟨by norm_num, le_refl _⟩,
      hWmG t ht (1 / 2) ⟨by norm_num, le_refl _⟩]
    norm_num
  -- ## 3. at the parameter value `1` both lifts are those of the constant curve
  have hend1 : Wp (1 / 2) 1
      = (1 / 2 : ℝ) • Submission.Geodesic.curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
    have hconst : (fun s : ℝ => c s 1) = (fun _ : ℝ => p) := funext (fun s => hc1 s)
    have hgeo' : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => c s 1) t := by
      intro t
      rw [hconst]
      exact Submission.Geodesic.isGeodesic_const (I := I) cov p t
    have hsm' : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => c s 1) := by
      rw [hconst]
      exact contMDiff_const
    have hWc : ContinuousOn (fun s : ℝ => Wp s 1) (Set.Icc (0 : ℝ) (1 / 2)) :=
      hWpc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, ⟨by norm_num, le_refl 1⟩⟩)
    have hspec := Work.OddBound.longHomotopy.lift_of_geodesic_ray (I := I) (cov := cov)
      hmet htor hK hcurv (p := p) (h := fun s : ℝ => c s 1) (S := 1 / 2) (by norm_num)
      hgeo' hsm' (hc1 0) (W := fun s : ℝ => Wp s 1) hWc
      (hWp0 1 ⟨by norm_num, le_refl 1⟩)
      (fun s hs => hWpG 1 ⟨by norm_num, le_refl 1⟩ s hs)
      (fun s hs => hWpb 1 ⟨by norm_num, le_refl 1⟩ s hs)
    have hv : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => c s 1) 0
        = Submission.Geodesic.curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
      rw [hconst]
    exact (hspec (1 / 2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1 / 2 : ℝ) • w) hv)
  have hend2 : Wm (1 / 2) 1
      = (1 / 2 : ℝ) • Submission.Geodesic.curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
    have hconst : (fun s : ℝ => c (1 - s) 1) = (fun _ : ℝ => p) := funext fun s => hc1 (1 - s)
    have hgeo' : ∀ t : ℝ,
        Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => c (1 - s) 1) t := by
      intro t
      rw [hconst]
      exact Submission.Geodesic.isGeodesic_const (I := I) cov p t
    have hsm' : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => c (1 - s) 1) := by
      rw [hconst]
      exact contMDiff_const
    have hWc : ContinuousOn (fun s : ℝ => Wm s 1) (Set.Icc (0 : ℝ) (1 / 2)) :=
      hWmc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, ⟨by norm_num, le_refl 1⟩⟩)
    have hspec := Work.OddBound.longHomotopy.lift_of_geodesic_ray (I := I) (cov := cov)
      hmet htor hK hcurv (p := p) (h := fun s : ℝ => c (1 - s) 1) (S := 1 / 2) (by norm_num)
      hgeo' hsm' (hc1 (1 - 0)) (W := fun s : ℝ => Wm s 1) hWc
      (hWm0 1 ⟨by norm_num, le_refl 1⟩)
      (fun s hs => hWmG 1 ⟨by norm_num, le_refl 1⟩ s hs)
      (fun s hs => hWmb 1 ⟨by norm_num, le_refl 1⟩ s hs)
    have hv : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => c (1 - s) 1) 0
        = Submission.Geodesic.curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
      rw [hconst]
    exact (hspec (1 / 2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1 / 2 : ℝ) • w) hv)
  have h1eq : Wp (1 / 2) 1 = Wm (1 / 2) 1 := hend1.trans hend2.symm
  -- ## 4. the open-and-closed step
  have hclopen : Wp (1 / 2) 0 = Wm (1 / 2) 0 :=
    Work.OddBound.longHomotopy.eq_at_zero_of_continuous_lift_eq (I := I) (cov := cov) hmet htor hK
      hcurv hsec₁ hsec₂ hb₁ hb₂ hG h1eq
  -- ## 5. at the parameter value `0` the lifts are the straight rays of the two halves of `γ`
  have hgeo₁ : ∀ t : ℝ,
      Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => γ (L * s)) t :=
    isGeodesicAt_comp_mul (I := I) (cov := cov) hγsm hgeo (ne_of_gt hL)
  have hsm₁ : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => γ (L * s)) :=
    contMDiff_comp_mul (I := I) hγsm L
  have hsecP : ContinuousOn (fun s : ℝ => Wp s 0) (Set.Icc (0 : ℝ) (1 / 2)) :=
    hWpc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, ⟨le_refl 0, by norm_num⟩⟩)
  have hP : Wp (1 / 2) 0
      = (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0) := by
    have hspec := Work.OddBound.longHomotopy.lift_of_geodesic_ray (I := I) (cov := cov)
      hmet htor hK hcurv (p := p) (h := fun s : ℝ => γ (L * s)) (S := 1 / 2) (by norm_num)
      hgeo₁ hsm₁ (by simp [h0])
      (W := fun s : ℝ => Wp s 0) hsecP
      (hWp0 0 ⟨le_refl 0, by norm_num⟩)
      (fun s hs => (hWpG 0 ⟨le_refl 0, by norm_num⟩ s hs).trans (hc0 s))
      (fun s hs => hWpb 0 ⟨le_refl 0, by norm_num⟩ s hs)
    exact (hspec (1 / 2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1 / 2 : ℝ) • w) (curveVelocity_comp_mul_zero (I := I) hγsm L))
  have hgeo₂ : ∀ t : ℝ,
      Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => γ ((-L) * s)) t :=
    isGeodesicAt_comp_mul (I := I) (cov := cov) hγsm hgeo (neg_ne_zero.mpr (ne_of_gt hL))
  have hsm₂ : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => γ ((-L) * s)) :=
    contMDiff_comp_mul (I := I) hγsm (-L)
  have hper' : ∀ s : ℝ, γ (L * (1 - s)) = γ ((-L) * s) := by
    intro s
    have h := hper ((-L) * s)
    have he : (-L) * s + L = L * (1 - s) := by ring
    rw [he] at h
    exact h
  have hsecM : ContinuousOn (fun s : ℝ => Wm s 0) (Set.Icc (0 : ℝ) (1 / 2)) :=
    hWmc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, ⟨le_refl 0, by norm_num⟩⟩)
  have hM : Wm (1 / 2) 0
      = (1 / 2 : ℝ) • ((-L) • Submission.Geodesic.curveVelocity (I := I) γ 0) := by
    have hspec := Work.OddBound.longHomotopy.lift_of_geodesic_ray (I := I) (cov := cov)
      hmet htor hK hcurv (p := p) (h := fun s : ℝ => γ ((-L) * s)) (S := 1 / 2) (by norm_num)
      hgeo₂ hsm₂ (by simp [h0])
      (W := fun s : ℝ => Wm s 0) hsecM
      (hWm0 0 ⟨le_refl 0, by norm_num⟩)
      (fun s hs => (hWmG 0 ⟨le_refl 0, by norm_num⟩ s hs).trans (by rw [hc0 (1 - s), hper' s]))
      (fun s hs => hWmb 0 ⟨le_refl 0, by norm_num⟩ s hs)
    exact (hspec (1 / 2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1 / 2 : ℝ) • w) (curveVelocity_comp_mul_zero (I := I) hγsm (-L)))
  -- ## 6. contradiction: `L • γ'(0) = -(L • γ'(0))` forces `γ'(0) = 0`
  have hvv : (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)
      = (1 / 2 : ℝ) • ((-L) • Submission.Geodesic.curveVelocity (I := I) γ 0) :=
    hP.symm.trans (hclopen.trans hM)
  have hLv : L • Submission.Geodesic.curveVelocity (I := I) γ 0 = 0 := by
    have h1 : (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)
        = -((1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)) := by
      nth_rewrite 1 [hvv]
      rw [neg_smul, smul_neg]
    have h3 : (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)
        + (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0) = 0 := by
      nth_rewrite 1 [h1]
      rw [neg_add_cancel]
    have h4 : (2 : ℝ) • ((1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0))
        = 0 := by
      rw [two_smul]
      exact h3
    have h5 : (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0) = 0 := by
      rcases (smul_eq_zero.mp h4) with h | h
      · norm_num at h
      · exact h
    rcases (smul_eq_zero.mp h5) with h | h
    · norm_num at h
    · exact h
  have hv : Submission.Geodesic.curveVelocity (I := I) γ 0 = 0 := by
    rcases (smul_eq_zero.mp hLv) with h | h
    · exact absurd h (ne_of_gt hL)
    · exact h
  exact hne 0 hv

end Work.OddBound.relaxedLHL
