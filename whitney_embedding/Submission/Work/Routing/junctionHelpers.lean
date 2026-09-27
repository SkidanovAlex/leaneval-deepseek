import Mathlib
import Submission.Work.Noncompact.CompressionTube.CorridorDefs
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm

/-!
# Helpers for the junction arc

Two elementary lemmas used by `Submission.Work.Routing.junctionArcOfChain`:

* `notMem_image_ball_of_germ`: a germ visit at chart distance `≥ r` is outside the chart ball image;
* `reparamChartLine_contMDiff_immersion`: a chart line reparametrised by `φ` with `φ' > 0`
  everywhere and bounded range is a `C^∞` immersion on all of `ℝ`.
-/

namespace Work.Routing

open Set Topology Filter
open scoped Manifold ContDiff _root_.Topology

open Work.Noncompact.CompressionTube in
/-- **A germ visit at parameter `t` is outside the chart ball of radius `r` when `t·‖w‖ ≥ r`.**

If `γ t` is the straight `c`-germ point `c.symm (c p + t • w)` (with the chart argument in the
target) and `t * ‖w‖ ≥ r`, then `γ t` is not in `c.symm '' ball (c p) r`.  This is the elementary
step converting the *chart* distance `t ‖w‖` into a non-membership of the ball image. -/
theorem notMem_image_ball_of_germ {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {p : M}
    {w : EuclideanSpace ℝ (Fin n)} {γ : ℝ → M} {t r : ℝ}
    (ht0 : 0 ≤ t) (hgerm : γ t = c.symm (c p + t • w)) (htgt : c p + t • w ∈ c.target)
    (hballtgt : Metric.ball (c p) r ⊆ c.target) (htr : r ≤ t * ‖w‖) :
    γ t ∉ c.symm '' Metric.ball (c p) r := by
  intro hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  have hyT : y ∈ c.target := hballtgt hy
  have hinj : Set.InjOn c.symm c.target := by
    have h := c.symm.injOn
    rwa [OpenPartialHomeomorph.symm_source] at h
  have hyeq : y = c p + t • w := hinj hyT htgt (by rw [hyx, hgerm])
  have hdist : dist (c p + t • w) (c p) = t * ‖w‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  rw [hyeq] at hy
  have h2 : dist (c p + t • w) (c p) < r := Metric.mem_ball.mp hy
  rw [hdist] at h2
  linarith

open Work.Noncompact.CompressionTube in
/-- **A reparametrised chart line is a smooth immersion.**

For a chart `c` of the maximal atlas, a point `p ∈ c.source`, a non-zero direction `V`, and a smooth
`φ : ℝ → ℝ` with `φ' > 0` everywhere and range inside an interval `(a,b)` on which the chart line
`u ↦ c p + u • V` stays in the chart target, the curve `t ↦ c.symm (c p + φ t • V)` is `C^∞` and an
immersion at every point of `ℝ`.  (The `φ' > 0` hypothesis is what replaces the `t ↦ t` identity:
chaining the chart line with `φ` keeps the immersion as long as `φ'` never vanishes.) -/
theorem reparamChartLine_contMDiff_immersion {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M)
    {p : M} (hp : p ∈ c.source) {V : EuclideanSpace ℝ (Fin n)} (hV : V ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφpos : ∀ t, 0 < deriv φ t)
    {a b : ℝ} (hrange : Set.range φ ⊆ Set.Ioo a b)
    (htgt : ∀ u : ℝ, u ∈ Set.Ioo a b → c p + u • V ∈ c.target) :
    ContMDiff MCreal (MC n) smoothOrder (fun t : ℝ => c.symm (c p + φ t • V)) ∧
      ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) (fun t : ℝ => c.symm (c p + φ t • V))
        t) := by
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  obtain ⟨hLsm, hLimm⟩ := isImmersion_chartLine c hc hp hV isOpen_Ioo htgt
  have hφcd : ContMDiff MCreal MCreal smoothOrder φ := by
    rw [MCreal, smoothOrder, contMDiff_iff_contDiff]
    exact hφ
  have hsm : ContMDiff MCreal (MC n) smoothOrder (fun t : ℝ => c.symm (c p + φ t • V)) := by
    have hcomp : ContMDiffOn MCreal (MC n) smoothOrder
        ((fun u : ℝ => c.symm (c p + u • V)) ∘ φ) Set.univ :=
      hLsm.comp hφcd.contMDiffOn (fun t _ => hrange ⟨t, rfl⟩)
    exact contMDiffOn_univ.mp (by simpa [Function.comp_def] using hcomp)
  refine ⟨hsm, fun t => ?_⟩
  have hLmd : MDifferentiableAt MCreal (MC n) (fun u : ℝ => c.symm (c p + u • V)) (φ t) :=
    (hLsm.contMDiffAt (isOpen_Ioo.mem_nhds (hrange ⟨t, rfl⟩))).mdifferentiableAt hn0
  have hφmd : MDifferentiableAt MCreal MCreal φ t := hφcd.contMDiffAt.mdifferentiableAt hn0
  have hchain : mfderiv MCreal (MC n) (fun t : ℝ => c.symm (c p + φ t • V)) t
      = (mfderiv MCreal (MC n) (fun u : ℝ => c.symm (c p + u • V)) (φ t)).comp
        (mfderiv MCreal MCreal φ t) := by
    have h := mfderiv_comp (I := MCreal) (I' := MCreal) (I'' := MC n)
      (f := φ) (g := fun u : ℝ => c.symm (c p + u • V)) t hLmd hφmd
    simpa [Function.comp_def] using h
  have hφinj : Function.Injective (mfderiv MCreal MCreal φ t) := by
    rw [mfderiv_eq_fderiv]
    have hd : HasDerivAt φ (deriv φ t) t :=
      (hφ.differentiable (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).differentiableAt.hasDerivAt
    have hfd : fderiv ℝ φ t = ContinuousLinearMap.toSpanSingleton ℝ (deriv φ t) :=
      hd.hasFDerivAt.fderiv
    have key : Function.Injective (ContinuousLinearMap.toSpanSingleton ℝ (deriv φ t)) := by
      intro x y hxy
      have h2 : x • deriv φ t = y • deriv φ t := by
        simpa only [ContinuousLinearMap.toSpanSingleton_apply] using hxy
      have h3 : (x - y) • deriv φ t = 0 := by rw [sub_smul, h2, sub_self]
      have h4 : x - y = 0 := by
        rcases smul_eq_zero.mp h3 with h | h
        · exact h
        · exact absurd h (ne_of_gt (hφpos t))
      exact sub_eq_zero.mp h4
    rwa [hfd]
  rw [hchain]
  intro x y hxy
  have hxy' := hxy
  rw [ContinuousLinearMap.comp_apply] at hxy'
  exact hφinj (hLimm (φ t) (hrange ⟨t, rfl⟩) hxy')

end Work.Routing
