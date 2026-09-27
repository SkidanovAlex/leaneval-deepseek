import Mathlib
import Submission.Work.Drive.N2.bandSeparatingMap_of_contMDiff

/-!
# The transport ("foot") map of a level flow

The *foot map* of a level flow: the point where the trajectory of `x` meets a fixed anchor level
`f = a`.  This definition lives in its own module (below the movies' consumers) so that the window
lane can name it without importing the target's own module.
-/

open scoped Manifold ContDiff

namespace Work.Drive.N2

/-- **The transport ("foot") map to the level `a`**: the point at which the trajectory of `x` meets
the level `f = a`, i.e. the time-`(a - f x)` point of the flow. -/
noncomputable def footMap {M : Type*} (Φ : ℝ × M → M) (f : M → ℝ) (a : ℝ) : M → M :=
  fun x => Φ (a - f x, x)


open scoped Manifold ContDiff in
lemma contMDiff_time_shift {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {Φ : ℝ × M → M} (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ) (c : ℝ) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (c, z)) :=
  hΦsm.comp (contMDiff_const.prodMk contMDiff_id)

open scoped Manifold ContDiff in
lemma contMDiff_level_shift {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {Φ : ℝ × M → M} (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (f x - f z, z)) :=
  hΦsm.comp (((contMDiff_const.sub hf)).prodMk contMDiff_id)

open scoped Manifold ContDiff in
set_option backward.isDefEq.respectTransparency false in
/-- **The foot map is smooth, level-injective and `ker df`-immersive, with no range hypothesis.**

This is `Work.Drive.N2.footMap_rows` with the landing row removed: the three rows below are
consequences of the flow laws alone (no level law, hence **no legality hypothesis**).  In the window
assembly the landing row `f (foot x) = c - η` is the only row that needs the legality, so the two
files split the obligations: the rows here are free, and only the landing row has to be supplied by
`Work.Drive.N2.footMap_rows` (or by the conditional level law of the model-adapted flow). -/
theorem footMap_rows_noLaw {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {Φ : ℝ × M → M} (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    (a : ℝ) :
      ContMDiff (𝓡 2) (𝓡 2) ∞ (footMap Φ f a) ∧
      (∀ x y : M, f x = f y → footMap Φ f a x = footMap Φ f a y → x = y) ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
        mfderiv (𝓡 2) (𝓡 2) (footMap Φ f a) x v = 0 → v = 0) := by
  have hsm : ContMDiff (𝓡 2) (𝓡 2) ∞ (footMap Φ f a) := by
    have h1 : ContMDiff (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ (fun z : M => (a - f z, z)) :=
      ((contDiff_const.sub contDiff_id).comp_contMDiff hf).prodMk contMDiff_id
    exact hΦsm.comp h1
  refine ⟨hsm, ?_, ?_⟩
  · intro x y hfxy hxy
    simp only [footMap] at hxy
    have ht : a - f x = a - f y := by rw [hfxy]
    have h1 : Φ (a - f x, x) = Φ (a - f x, y) := by rw [hxy, ht]
    have h2 := congrArg (fun z : M => Φ (-(a - f x), z)) h1
    rw [hΦcomp, hΦcomp, neg_add_cancel, hΦ0, hΦ0] at h2
    exact h2
  · intro x v hv hw
    have hmdT' : MDifferentiableAt (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - a, z))
        (footMap Φ f a x) :=
      (contMDiff_time_shift hΦsm (f x - a)).mdifferentiableAt (by simp)
    have hmdF : MDifferentiableAt (𝓡 2) (𝓡 2) (footMap Φ f a) x :=
      hsm.mdifferentiableAt (by simp)
    have hR : (fun z : M => Φ (f x - a, z)) ∘ (footMap Φ f a)
        = (fun z : M => Φ (f x - f z, z)) := by
      funext y
      simp only [Function.comp_apply, footMap]
      rw [hΦcomp]
      congr 1
      ring_nf
    have hcr := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
      (f := footMap Φ f a) (g := fun z : M => Φ (f x - a, z)) (x := x) hmdT' hmdF v
    have hJ : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v = v :=
      mfderiv_transport_self Φ hΦsm hΦ0 f hf x v hv
    have hone : v = mfderiv (𝓡 2) (𝓡 2)
        ((fun z : M => Φ (f x - a, z)) ∘ (footMap Φ f a)) x v := by
      rw [hR, hJ]
    rw [hone, hcr, hw]
    exact map_zero _

end Work.Drive.N2
