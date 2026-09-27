import Mathlib
import Submission.Work.Whitney.CutPush.spine_composite
import Submission.Work.Whitney.CutPush.arc_unknotting

/-!
# Unknotting the spine when the immersion hypothesis is local

`Work.Whitney.CutPush.exists_unknotting_of_spine` assumes the spine `δ : ℝ → M` to be an *immersion
everywhere* (`∀ t : ℝ, Injective (mfderiv δ t)`).  The bigon data only gives the immersion of the
spine on `Icc 0 1`, and the regularity needed by `arc_unknotting` is likewise only asked on
`Icc 0 1`.  This file provides the local-hypothesis variant.
-/

namespace Work.Drive.Push

open scoped Manifold ContDiff
open Topology Set

/-- **The derivative of `t ↦ f (δ t)` is nonzero on `Icc 0 1`**, from `f` immersive everywhere and
`δ` immersive on `Icc 0 1`. -/
theorem fderiv_comp_spine_ne_zero_local {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (δ : ℝ → M)
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ)
    (hδimm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective
      (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ (fun s : ℝ => f (δ s)) t 1 ≠ 0 := by
  intro t ht hzero
  have hmdF : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t :=
    hδ.mdifferentiableAt (by simp)
  have hmdg : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (δ t) :=
    hf.mdifferentiableAt (by simp)
  have hchain : mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (fun s : ℝ => f (δ s)) t
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (δ t)).comp
        (mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t) := by
    simpa [Function.comp_def] using
      mfderiv_comp (I := modelWithCornersSelf ℝ ℝ)
        (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (I'' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (g := f) (f := δ) t hmdg hmdF
  have h1 : (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (fun s : ℝ => f (δ s)) t) = fderiv ℝ (fun s : ℝ => f (δ s)) t :=
    mfderiv_eq_fderiv
  have h2 : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (δ t))
      ((mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t) 1) = 0 := by
    have h2' : ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (δ t)).comp
        (mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t)) 1 = 0 := by
      rw [← hchain, h1]
      exact hzero
    exact h2'
  have h3 : (mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t) 1 = 0 :=
    himm (δ t) (h2.trans (map_zero _).symm)
  have h4 : (1 : ℝ) = 0 := hδimm t ht (h3.trans (map_zero _).symm)
  norm_num at h4

/-- **Unknotting the spine, with the immersion hypothesis only on `Icc 0 1`.** -/
theorem exists_unknotting_of_spine_local {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (δ : ℝ → M)
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ)
    (hδimm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective
      (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t))
    (hδinj : Set.InjOn δ (Set.Icc (0 : ℝ) 1))
    (O : Set M) (hO : IsOpen O) (hδO : δ '' Set.Icc (0 : ℝ) 1 ⊆ O) (hOinj : Set.InjOn f O) :
    ∃ (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        A (f (δ t)) = f (δ 0) + t • (f (δ 1) - f (δ 0))) := by
  have hm : 4 ≤ 2 * n := by omega
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => f (δ t)) :=
    (Work.Whitney.CutPush.contMDiff_comp_spine f hf δ hδ).contDiff
  have hinj : Set.InjOn (fun t : ℝ => f (δ t)) (Set.Icc (0 : ℝ) 1) :=
    fun s hs t ht hst => hδinj hs ht (hOinj (hδO (mem_image_of_mem δ hs))
      (hδO (mem_image_of_mem δ ht)) hst)
  have hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ (fun s : ℝ => f (δ s)) t 1 ≠ 0 :=
    fun t ht => fderiv_comp_spine_ne_zero_local f hf himm δ hδ hδimm t ht
  exact Work.Whitney.CutPush.arc_unknotting hm (fun t : ℝ => f (δ t)) hc hinj hreg

end Work.Drive.Push
