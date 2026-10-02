import Submission.Work.PTGeometric.VerticalFlow
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.transversalApproximation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the Sard step of G3, for a vertical flow

This file isolates the **analytic step** of G3 (`Work.PTGeometric.LocalTransversalApproximation`):
the choice of the perturbation parameter.

Given a `LocalCoreTarget X` with a vertical flow `VF` (the translations of the normal bundle of the
core, `Work.PTGeometric.VerticalFlow`), a local trivialisation `i`, a box `W` on which the translation
is valid for all amounts of norm `≤ δ`, a smooth map `F : M → X.E` whose image of the region where a
smooth cut-off `χ` is positive lies in `W`, the perturbed map

`F_t x := Ψ i (F x) (−(χ x • t))`

satisfies `Phi i (F_t y) = Phi i (F y) − χ y • t` for **every** `y` (the exact vertical translation),
so that the pointwise transversality of `F_t` at a point where it meets the core is exactly the
regularity of the level map `y ↦ Phi i (F y) − χ y • t`, and the parametric Sard theorem
`Work.ThomBordism.Transversality.TransversalApproximation.volume_badSet_eq_zero` (proved) produces a
parameter `t` outside the null set of *critical* parameters.  The conclusion is the pointwise
transversality statement, at every point at which the perturbed map meets the core *inside* the
support of the cut-off.

## Main results

* `Work.PTGeometric.perturbation_Phi_eq` — the exact translation identity for the perturbed map
* `Work.PTGeometric.perturbation_eq_of_chi_eq_zero` — the perturbed map is the identity of the map off
  the support of the cut-off
* `Work.PTGeometric.exists_transverse_perturbation` — the Sard step
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n k : ℕ}

/-- **The exact translation identity for the perturbed map.**

If the box `W` is valid for all amounts of norm `≤ δ`, the cut-off `χ` takes values in `[0,1]` and is
positive only over the preimage of `W`, and `‖t‖ ≤ δ`, then the perturbed map
`F_t x := Ψ i (F x) (−(χ x • t))` satisfies `Phi i (F_t y) = Phi i (F y) − χ y • t` for every `y`. -/
theorem perturbation_Phi_eq (X : LocalCoreTarget n k) (VF : VerticalFlow X) {M : Type*}
    (i : X.locIx) (W : Set X.E) (δ : ℝ) (F : M → X.E) (χ : M → ℝ)
    (t : EuclideanSpace ℝ (Fin k))
    (hbox : ∀ y' ∈ W, ∀ s : EuclideanSpace ℝ (Fin k), ‖s‖ ≤ δ →
      (y', s) ∈ VF.valid i ∧ VF.Ψ i y' s ∈ X.locU i)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχW : ∀ x, χ x ≠ 0 → F x ∈ W) (ht : ‖t‖ ≤ δ) :
    (fun y => X.Phi i (VF.Ψ i (F y) (-(χ y • t)))) = fun y => X.Phi i (F y) - χ y • t := by
  funext y
  by_cases hy : χ y = 0
  · rw [hy, zero_smul, neg_zero, VF.zero_apply, sub_zero]
  · have hyW : F y ∈ W := hχW y hy
    have hnorm : ‖-(χ y • t)‖ ≤ δ := by
      rw [norm_neg, norm_smul]
      calc ‖χ y‖ * ‖t‖ ≤ 1 * δ :=
            mul_le_mul (by rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 y)]; exact hχ1 y) ht
              (norm_nonneg _) zero_le_one
        _ = δ := one_mul δ
    exact VF.Phi_apply i (F y) (-(χ y • t)) (hbox (F y) hyW _ hnorm).1

/-- **Off the support of the cut-off the perturbed map is the original map.** -/
theorem perturbation_eq_of_chi_eq_zero (X : LocalCoreTarget n k) (VF : VerticalFlow X) {M : Type*}
    (i : X.locIx) (F : M → X.E) (χ : M → ℝ) (t : EuclideanSpace ℝ (Fin k)) {x : M}
    (hx : χ x = 0) : VF.Ψ i (F x) (-(χ x • t)) = F x := by
  rw [hx, zero_smul, neg_zero, VF.zero_apply]

/-- **The Sard step of G3**: the choice of the parameter.

`M` is a compact `T2` smooth `(9+k)`-manifold with boundary, `X` a `LocalCoreTarget n k` with a
vertical flow `VF`, `i` a local trivialisation, `W` a box on which the vertical translation is valid
for all amounts of norm `≤ δ`, `F : M → X.E` a `C^∞` map whose image over the region where the smooth
cut-off `χ ∈ [0,1]` is positive lies in `W`, and `χ` vanishes on a neighbourhood of `∂M`.

Then there is a parameter `t` with `‖t‖ ≤ δ` such that at every point `x` where the perturbed map
`F_t x := Ψ i (F x) (−(χ x • t))` meets the core *and* `χ x ≠ 0`, the point `F_t x` lies in the
trivialisation `locU i` and the composite `Phi i ∘ F_t` is a submersion at `x` — i.e. `F_t` is
transverse to the core at `x` through the index `i`.

This is `volume_badSet_eq_zero` (parametric Sard on `M`) applied to `G := Phi i ∘ F` and `χ`: the set
of parameters `t` for which some interior point with `χ x > 0`, `G x = χ x • t` is critical for
`x ↦ G x − χ x • t` is null, hence a parameter in the ball of radius `δ` can be found outside it. -/
theorem exists_transverse_perturbation (X : LocalCoreTarget n k) (VF : VerticalFlow X)
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (F : M → X.E)
    (hF : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (i : X.locIx) (W : Set X.E) (δ : ℝ) (hδ : 0 < δ)
    (hbox : ∀ y' ∈ W, ∀ s : EuclideanSpace ℝ (Fin k), ‖s‖ ≤ δ →
      (y', s) ∈ VF.valid i ∧ VF.Ψ i y' s ∈ X.locU i)
    (χ : M → ℝ)
    (hχ : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχbd : ∃ U : Set M, (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M ⊆ U ∧
      IsOpen U ∧ ∀ x ∈ U, χ x = 0)
    (hχW : ∀ x, χ x ≠ 0 → F x ∈ W) :
    ∃ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ δ ∧
      ∀ x : M, χ x ≠ 0 → VF.Ψ i (F x) (-(χ x • t)) ∈ X.core →
        VF.Ψ i (F x) (-(χ x • t)) ∈ X.locU i ∧
        IsSubmersionAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => X.Phi i (VF.Ψ i (F y) (-(χ y • t)))) x := by
  classical
  set G : M → EuclideanSpace ℝ (Fin k) := fun x => X.Phi i (F x) with hGdef
  have hGsm : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    (X.contMDiff_Phi i).comp hF
  set Bad : Set (EuclideanSpace ℝ (Fin k)) := {t |
    ∃ x, (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).IsInteriorPoint x ∧ 0 < χ x ∧
      G x = χ x • t ∧ ¬ Function.Surjective (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) (fun y => G y - χ y • t) x)}
    with hBaddef
  have hnull : volume Bad = 0 :=
    Work.ThomBordism.Transversality.TransversalApproximation.volume_badSet_eq_zero
      (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) G hGsm χ hχ hχ0
  obtain ⟨t, htBad, htball⟩ : ∃ t, t ∉ Bad ∧ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) δ := by
    by_contra h
    have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) δ ⊆ Bad := by
      intro t ht
      by_contra hc
      exact h ⟨t, hc, ht⟩
    have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) δ) ≤ volume Bad :=
      measure_mono hsub
    rw [hnull] at hle
    exact absurd hle
      (not_le.mpr (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin k)) hδ))
  have htδ : ‖t‖ ≤ δ := by
    have h1 : dist t 0 < δ := Metric.mem_ball.mp htball
    rw [dist_eq_norm, sub_zero] at h1
    exact le_of_lt h1
  refine ⟨t, htδ, ?_⟩
  intro x hxχ hxcore
  have hxW : F x ∈ W := hχW x hxχ
  have htnorm : ‖-(χ x • t)‖ ≤ δ := by
    rw [norm_neg, norm_smul]
    calc ‖χ x‖ * ‖t‖ ≤ 1 * δ :=
          mul_le_mul (by rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 x)]; exact hχ1 x) htδ
            (norm_nonneg _) zero_le_one
      _ = δ := one_mul δ
  have hboxx := hbox (F x) hxW (-(χ x • t)) htnorm
  have hlocU : VF.Ψ i (F x) (-(χ x • t)) ∈ X.locU i := hboxx.2
  refine ⟨hlocU, ?_⟩
  have hfun := perturbation_Phi_eq X VF i W δ F χ t hbox hχ0 hχ1 hχW htδ
  have hzero : X.Phi i (VF.Ψ i (F x) (-(χ x • t))) = 0 :=
    (X.mem_core_iff i _ hlocU).mpr hxcore
  have hGx : G x = χ x • t := by
    have h := congrFun hfun x
    rw [hzero] at h
    exact sub_eq_zero.mp h.symm
  have hxnotbd : x ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M := by
    obtain ⟨U, hU, hUopen, hU0⟩ := hχbd
    intro hxb
    exact hxχ (hU0 x (hU hxb))
  have hint : (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).IsInteriorPoint x :=
    ((modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mpr
      hxnotbd
  have hsurj : Function.Surjective (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (fun y => X.Phi i (VF.Ψ i (F y) (-(χ y • t)))) x) := by
    by_contra hcon
    have hcon' : ¬ Function.Surjective (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) (fun y => G y - χ y • t) x) := by
      rwa [hfun] at hcon
    exact htBad ⟨x, hint, lt_of_le_of_ne (hχ0 x) (Ne.symm hxχ), hGx, hcon'⟩
  have hsm : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => X.Phi i (VF.Ψ i (F y) (-(χ y • t)))) := by
    rw [hfun]
    have h2 : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => χ y • t) := ContMDiff.smul hχ (contMDiff_const (c := t))
    exact hGsm.sub h2
  exact Work.ThomBordism.Transversality.TransversalApproximation.isSubmersionAt_of_surjective_mfderiv
    (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) hsm hint hzero hsurj

end

end Work.PTGeometric
