import Mathlib
import Submission.Work.Whitney.CutPush.spine_composite
import Submission.Work.Whitney.CutPush.arc_unknotting

/-!
# Straightening the spine's image

Second brick of the tube-flattening assembly (`CutPush/NOTES_STATE_S61.md` §2): applying
`arc_unknotting` (`CutPush/arc_unknotting.lean`) to the chord `f ∘ δ` of the spine.  The hypotheses
of `arc_unknotting` are supplied by `CutPush/spine_composite.lean` (`f ∘ δ` is `C^∞` and regular)
and by the injectivity of `f` on `O ⊇ δ '' Icc`.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology Set

/-- **The chord of the spine.**  `arc_unknotting` applied to `f ∘ δ`: a global diffeomorphism of
`ℝ^{2n}` carrying `f (δ t)` to the straight segment `f (δ 0) + t • (f (δ 1) - f (δ 0))`. -/
theorem exists_unknotting_of_spine {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
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
    (hδimm : ∀ t : ℝ, Function.Injective
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
    (contMDiff_comp_spine f hf δ hδ).contDiff
  have hinj : Set.InjOn (fun t : ℝ => f (δ t)) (Set.Icc (0 : ℝ) 1) :=
    fun s hs t ht hst => hδinj hs ht (hOinj (hδO (mem_image_of_mem δ hs))
      (hδO (mem_image_of_mem δ ht)) hst)
  have hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (fun s : ℝ => f (δ s)) t 1 ≠ 0 :=
    fun t _ => fderiv_comp_spine_ne_zero f hf himm δ hδ hδimm t
  exact arc_unknotting hm (fun t : ℝ => f (δ t)) hc hinj hreg

end Work.Whitney.CutPush
