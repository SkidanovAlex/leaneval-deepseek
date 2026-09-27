import Mathlib
import Submission.Work.ODE.GlobalFlow
import Submission.Work.ODE.SmoothFlow
import Submission.Work.ODE.CompactSupportBounds
import Submission.Work.Whitney.exists_flow_map_of_compactSupport

/-!
# The flow of a smooth bounded Lipschitz vector field

A smooth vector field `X` on a complete finite dimensional real normed space `E` which is Lipschitz
and bounded (together with its derivative) has a global flow `FL : ℝ → E → E`: `FL 0 = id`,
`FL (s + t) = FL s ∘ FL t`, every curve `s ↦ FL s p` is an integral curve of `X`, and the time
slices `FL s` are smooth for uniformly small times.

This is the generalisation (to an arbitrary `E`, and with the bounds taken as hypotheses rather than
derived from compact support) of `Work.Whitney.exists_flow_map_of_compactSupport`, which is stated
for `EuclideanSpace ℝ (Fin m)` and only gives the time-one map.  The arc-unknotting construction
flows the *product* field `(lam, y) ↦ (1, V lam y)`, which is bounded and Lipschitz but has empty
support, so the compactly supported version does not apply; the version below does.
-/

open scoped Manifold ContDiff
open Topology Set Function MeasureTheory

namespace Work.Whitney.CutPush

/-- **The flow of a smooth bounded Lipschitz field**, with its semigroup law and the smoothness of
its small-time slices. -/
theorem exists_flow_of_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (X : E → E) (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X) {L : NNReal} (hL : LipschitzWith L X)
    {M K : ℝ} (hM : ∀ z, ‖X z‖ ≤ M) (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) :
    ∃ (FL : ℝ → E → E) (δ : ℝ), 0 < δ ∧
      (∀ p, FL 0 p = p) ∧
      (∀ s t p, FL (s + t) p = FL s (FL t p)) ∧
      (∀ p, IsIntegralCurve (fun s => FL s p) (fun _ z => X z)) ∧
      (∀ s, |s| ≤ δ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL s)) := by
  classical
  have hglob : ∀ y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) :=
    fun y => Work.ODE.exists_isIntegralCurve_of_lipschitzWith X hL hM y
  let FL : ℝ → E → E := fun t y => (Classical.choose (hglob y)) t
  have hFL0 : ∀ y, FL 0 y = y := fun y => (Classical.choose_spec (hglob y)).1
  have hFLcurve : ∀ y, IsIntegralCurve (FL · y) (fun _ z => X z) :=
    fun y => (Classical.choose_spec (hglob y)).2
  have hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = FL t y :=
    fun t y => ⟨Classical.choose (hglob y), hFL0 y, hFLcurve y, rfl⟩
  obtain ⟨δ, hδpos, hδsmooth⟩ := Work.ODE.contDiff_flow_timeSlice X hX M K hM hK FL hΦ
  have hsem : ∀ (a b : ℝ) (y : E), FL (a + b) y = FL a (FL b y) := by
    intro a b y
    have h1 : IsIntegralCurve (fun s : ℝ => FL (s + b) y) (fun _ z => X z) := by
      have h := (hFLcurve y).comp_add b
      simpa [Function.comp_def, FL, add_comm] using h
    have h2 : IsIntegralCurve (fun s : ℝ => FL s (FL b y)) (fun _ z => X z) := hFLcurve (FL b y)
    have heq : (fun s : ℝ => FL (s + b) y) 0 = (fun s : ℝ => FL s (FL b y)) 0 := by
      simp [hFL0]
    have huniq := Work.ODE.eq_of_isIntegralCurve (L := L) hL h1 h2 heq
    exact congrFun huniq a
  exact ⟨FL, δ, hδpos, hFL0, hsem, hFLcurve, fun s hs => hδsmooth s hs⟩

/-- **The flow of a smooth compactly supported field** (the bounds are supplied by compact support),
with its semigroup law and the smoothness of its small-time slices. -/
theorem flow_of_compactSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (X : E → E) (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X) (hc : HasCompactSupport X) :
    ∃ (FL : ℝ → E → E) (δ : ℝ), 0 < δ ∧
      (∀ p, FL 0 p = p) ∧
      (∀ s t p, FL (s + t) p = FL s (FL t p)) ∧
      (∀ p, IsIntegralCurve (fun s => FL s p) (fun _ z => X z)) ∧
      (∀ s, |s| ≤ δ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL s)) := by
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by norm_num)
  obtain ⟨L, hL⟩ := Work.ODE.exists_lipschitzWith_of_contDiff_hasCompactSupport hX1 hc
  obtain ⟨M, _hM0, hMb⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport hX.continuous hc
  have hfdc : Continuous (fderiv ℝ X) := hX.continuous_fderiv (by norm_num)
  have hfcs : HasCompactSupport (fderiv ℝ X) := hc.fderiv (𝕜 := ℝ)
  obtain ⟨K, _hK0, hKb⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport hfdc hfcs
  exact exists_flow_of_lipschitz X hX hL hMb hKb

end Work.Whitney.CutPush
