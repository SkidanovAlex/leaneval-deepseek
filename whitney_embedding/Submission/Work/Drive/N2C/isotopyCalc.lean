import Mathlib
import Submission.Work.Drive.N2C.defs

/-!
# The level-isotopy calculus (Tier B of the coherent-window architecture)

`Work.Drive.N2C.IsLevelIsotopy f b e` says that `e : ℝ → M → ℝ³` is a jointly smooth family of
*pictures* of the regular level `f ⁻¹' {b}` (injective there, `ker df`-immersive there).  This module
proves the **calculus** of that notion, i.e. the constructors that the assembly of the compact
`n = 2` case (`Submission/Work/Drive/N2Lead/NOTES_LEAD_coherentWindows.md`, Tier B) consumes:

* `isLevelIsotopy_const` (B1a) — a constant family (the rows of a picture of the level);
* `isLevelIsotopy_comp_time` (B1b) — precomposition with a smooth reparametrisation of the *time*;
* `isLevelIsotopy_ambient` (B1c) — postcomposition by a smooth ambient isotopy of `ℝ³`, each of whose
  slices is injective and immersive, in the form in which the *domain* is the manifold `ℝ × ℝ³`
  (the product model), i.e. the hypothesis is `ContMDiff` of the uncurried family; the
  `ContDiff ℝ`-form is `isLevelIsotopy_ambient_contDiff`.

Everything here is pure chain rule: the isotopy notion is *stated at the level*, so the smoothness row
is only asked at level points, and the two geometric rows are exactly those of `e`.

The Tier B items `isLevelIsotopy_transport` and `isLevelIsotopy_windowMovie` live in the sibling
modules of this directory (proved); `isLevelIsotopy_blend`, `LevelCurves.exists_transition` and
`isLevelIsotopy_roundToRound` are *not* in this module.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter
open Classical

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## B1a: the constant family -/

/-- **A picture of the level is a (constant) level isotopy.** -/
theorem isLevelIsotopy_const {f : M → ℝ} {b : ℝ} {A : M → EuclideanSpace ℝ (Fin 3)}
    (hsm : ∀ y : M, f y = b → ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A y)
    (hinj : ∀ x y : M, f x = b → f y = b → A x = A y → x = y)
    (himm : ∀ y : M, f y = b → ∀ v : TangentSpace (𝓡 2) y,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 → mfderiv (𝓡 2) (𝓡 3) A y v = 0 → v = 0) :
    IsLevelIsotopy f b (fun (_ : ℝ) => A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s y hy
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => p.2) (s, y) := contMDiff_snd.contMDiffAt
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => A p.2) (s, y) := (hsm y hy).comp (s, y) h2
    simpa only [Function.comp_def] using h1
  · intro s x y hx hy hxy
    exact hinj x y hx hy hxy
  · intro s y hy
    exact himm y hy

/-! ## B1b: reparametrising the time -/

/-- **Reparametrising the time of a level isotopy.** -/
theorem isLevelIsotopy_comp_time {f : M → ℝ} {b : ℝ} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (he : IsLevelIsotopy f b e) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) :
    IsLevelIsotopy f b (fun s => e (ρ s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s y hy
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ((𝓘(ℝ, ℝ)).prod (𝓡 2))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × M => (ρ p.1, p.2)) (s, y) :=
      ContMDiffAt.prodMk
        ((hρ.contMDiff.contMDiffAt).comp (s, y) contMDiff_fst.contMDiffAt)
        contMDiff_snd.contMDiffAt
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => e (ρ p.1) p.2) (s, y) :=
      (he.1 (ρ s) y hy).comp (s, y) h1
    simpa only [Function.comp_def] using h2
  · intro s x y hx hy hxy
    exact he.2.1 (ρ s) x y hx hy hxy
  · intro s y hy
    exact he.2.2 (ρ s) y hy

/-! ## B1c: postcomposition by an ambient isotopy of `ℝ³` -/

/-- **Postcomposing a level isotopy by an ambient isotopy of `ℝ³`.**  Every time slice `F s` is
injective and has injective derivative everywhere.  The hypothesis on `F` is stated on the manifold
`ℝ × ℝ³` with the product model (equivalently, `ContDiff ℝ ∞ (Function.uncurry F)`, see
`isLevelIsotopy_ambient_contDiff`). -/
theorem isLevelIsotopy_ambient {f : M → ℝ} {b : ℝ} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (he : IsLevelIsotopy f b e)
    {F : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry F))
    (hFinj : ∀ s : ℝ, Function.Injective (F s))
    (hFimm : ∀ (s : ℝ) (w : EuclideanSpace ℝ (Fin 3)),
      Function.Injective (fderiv ℝ (F s) w)) :
    IsLevelIsotopy f b (fun s y => F s (e s y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s y hy
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ((𝓘(ℝ, ℝ)).prod (𝓡 3))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × M => (p.1, e p.1 p.2)) (s, y) :=
      ContMDiffAt.prodMk contMDiff_fst.contMDiffAt (he.1 s y hy)
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => Function.uncurry F (p.1, e p.1 p.2)) (s, y) :=
      (hF.contMDiffAt).comp (s, y) h1
    simpa only [Function.uncurry, Function.comp_def] using h2
  · intro s x y hx hy hxy
    exact he.2.1 s x y hx hy (hFinj s hxy)
  · intro s y hy v hv hw
    have hes : ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (e s) y :=
      (he.1 s y hy).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
    have hFsm : ContMDiffAt (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (F s) (e s y) :=
      (hF.contMDiffAt).comp (e s y) (contMDiffAt_const.prodMk contMDiffAt_id)
    have himm : Function.Injective (fderiv ℝ (F s) (e s y)) := hFimm s (e s y)
    have hchain :
        mfderiv (𝓡 2) (𝓡 3) (fun y : M => F s (e s y)) y v
          = fderiv ℝ (F s) (e s y) (mfderiv (𝓡 2) (𝓡 3) (e s) y v) := by
      have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3)
        (f := e s) (g := F s) (x := y)
        (hFsm.mdifferentiableAt (by simp)) (hes.mdifferentiableAt (by simp)) v
      rw [mfderiv_eq_fderiv] at hc
      exact hc
    have hz : fderiv ℝ (F s) (e s y) (mfderiv (𝓡 2) (𝓡 3) (e s) y v) = 0 := by
      rw [← hchain]; exact hw
    have he0 : mfderiv (𝓡 2) (𝓡 3) (e s) y v = 0 := by
      have hz' : fderiv ℝ (F s) (e s y) (mfderiv (𝓡 2) (𝓡 3) (e s) y v)
          = fderiv ℝ (F s) (e s y) 0 := by rw [hz, map_zero]
      exact himm hz'
    exact he.2.2 s y hy v hv he0

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **`ContDiff`-form of `isLevelIsotopy_ambient`.**  The hypothesis `ContDiff ℝ ∞ (Function.uncurry F)`
(in the normed space `ℝ × ℝ³`) is the form in which the ambient isotopies of the design are built. -/
theorem isLevelIsotopy_ambient_contDiff {f : M → ℝ} {b : ℝ} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (he : IsLevelIsotopy f b e)
    {F : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F))
    (hFinj : ∀ s : ℝ, Function.Injective (F s))
    (hFimm : ∀ (s : ℝ) (w : EuclideanSpace ℝ (Fin 3)),
      Function.Injective (fderiv ℝ (F s) w)) :
    IsLevelIsotopy f b (fun s y => F s (e s y)) :=
  isLevelIsotopy_ambient he (by
    have h : ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3))) (𝓡 3)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F) :=
      contMDiff_iff_contDiff.mpr hF
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h) hFinj hFimm

end Work.Drive.N2C
