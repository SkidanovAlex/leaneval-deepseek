import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2C.isotopyCalc

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

open scoped Manifold ContDiff Topology in
/-- **The image-local ambient constructor (Tier B1, image-local variant).**  §4 of
`N2Lead/NOTES_LEAD_coherentWindows.md` asks for this variant of
`Work.Drive.N2C.isLevelIsotopy_ambient`: there the post-composition family `F` must be *globally*
injective with globally injective derivative on every slice, while the radial map of the saddle
certificates (the design's `D2c`, `D2d.4`, `D2d.5`) is only injective/immersive *on a neighbourhood
`W` of the images of the level*, and is defined through a bump elsewhere.  So: `e` is a level isotopy
at `b`, `W ⊆ ℝ³` contains the images `e s y` of the level points, `F` is jointly smooth at every
point of `ℝ × W` (the inner map `(s, y) ↦ (s, e s y)` is smooth by `he`, and the chain rule gives the
smoothness row), `F s` is injective *on the images of the level* and has injective derivative there
(chain rule: `mfderiv (F s ∘ e s) y v = fderiv (F s) (e s y) (mfderiv (e s) y v)`), and then
`s ↦ F s ∘ e s` is a level isotopy at `b`.  The result goes in namespace `Work.Drive.N2Lead`. -/
theorem isLevelIsotopy_ambient_local {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {b : ℝ} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (he : Work.Drive.N2C.IsLevelIsotopy f b e)
    {W : Set (EuclideanSpace ℝ (Fin 3))}
    (hW : ∀ (s : ℝ) (y : M), f y = b → e s y ∈ W)
    {F : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : ∀ (s : ℝ) (w : EuclideanSpace ℝ (Fin 3)), w ∈ W →
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F) (s, w))
    (hinj : ∀ (s : ℝ) (x y : M), f x = b → f y = b → F s (e s x) = F s (e s y) → x = y)
    (himm : ∀ (s : ℝ) (y : M), f y = b → ∀ v : TangentSpace (𝓡 2) y,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 →
      fderiv ℝ (F s) (e s y) (mfderiv (𝓡 2) (𝓡 3) (e s) y v) = 0 → v = 0) :
    Work.Drive.N2C.IsLevelIsotopy f b (fun s y => F s (e s y)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness row: the inner map `(s, y) ↦ (s, e s y)` is smooth, then compose with `F`
    intro s y hy
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ((𝓘(ℝ, ℝ)).prod (𝓡 3))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × M => (p.1, e p.1 p.2)) (s, y) :=
      ContMDiffAt.prodMk contMDiff_fst.contMDiffAt (he.1 s y hy)
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => Function.uncurry F (p.1, e p.1 p.2)) (s, y) :=
      (hF s (e s y) (hW s y hy)).comp (s, y) h1
    simpa only [Function.uncurry, Function.comp_def] using h2
  · -- injectivity row: only asked on the level, which is exactly `hinj`'s hypothesis
    intro s x y hx hy hxy
    exact hinj s x y hx hy hxy
  · -- immersivity row: chain rule + the local injectivity of the derivative of `F`
    intro s y hy v hv hw
    have hes : ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (e s) y :=
      (he.1 s y hy).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
    have hFsm : ContMDiffAt (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (F s) (e s y) :=
      (hF s (e s y) (hW s y hy)).comp (e s y) (contMDiffAt_const.prodMk contMDiffAt_id)
    have hchain :
        mfderiv (𝓡 2) (𝓡 3) (fun y : M => F s (e s y)) y v
          = fderiv ℝ (F s) (e s y) (mfderiv (𝓡 2) (𝓡 3) (e s) y v) := by
      have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3)
        (f := e s) (g := F s) (x := y)
        (hFsm.mdifferentiableAt (by simp)) (hes.mdifferentiableAt (by simp)) v
      rw [mfderiv_eq_fderiv] at hc
      exact hc
    exact himm s y hy v hv (by rw [← hchain]; exact hw)

end Work.Drive.N2Lead
