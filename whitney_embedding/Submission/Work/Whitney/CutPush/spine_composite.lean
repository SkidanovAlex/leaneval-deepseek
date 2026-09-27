import Mathlib

/-!
# The composite `f ∘ δ` of an immersion with an immersion of the line

First bricks of the tube-flattening assembly (`CutPush/NOTES_STATE_S61.md` §2): `arc_unknotting`
needs, for the *spine* `δ : ℝ → M`, that `fun t => f (δ t)` is `C^∞` and has non-vanishing
derivative on `Icc 0 1`; and `exists_localised_projection_family` needs an immersion on the
straightened sheet `A₁ ∘ f`.

Both are chain-rule lemmas: `mfderiv_comp` writes the derivative of the composite as a composite of
derivatives, and injectivity/negation of zero propagates through injective linear maps.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology

/-- **The composite of an immersion with an immersed curve is smooth.** -/
theorem contMDiff_comp_spine {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (δ : ℝ → M)
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ) :
    ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => f (δ t)) :=
  hf.comp hδ

/-- **The composite of two immersions is an immersion** (as a statement about `mfderiv`). -/
theorem mfderiv_comp_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hAi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv)
    (hlinv : Function.LeftInverse Ainv A) :
    ∀ x : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (fun y => A (f y)) x) := by
  intro x v w hvw
  -- the derivative of `A` at `f x` is injective, because `Ainv ∘ A = id`
  have hAinj : Function.Injective (fderiv ℝ A (f x)) := by
    intro p q hpq
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (2 * n)) => Ainv (A z))
        ((fderiv ℝ Ainv (A (f x))).comp (fderiv ℝ A (f x))) (f x) :=
      (((hAi.differentiable (by simp)).differentiableAt).hasFDerivAt.comp (f x)
        (((hA.differentiable (by simp)).differentiableAt).hasFDerivAt))
    have h2 : (fun z : EuclideanSpace ℝ (Fin (2 * n)) => Ainv (A z)) = fun z => z :=
      funext hlinv
    have h3 : (fderiv ℝ Ainv (A (f x))).comp (fderiv ℝ A (f x)) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
      rw [← h1.fderiv, h2]
      exact fderiv_id
    have hL : fderiv ℝ A (f x) (p - q) = 0 := by
      rw [map_sub, hpq, sub_self]
    have hM : (fderiv ℝ Ainv (A (f x))) (fderiv ℝ A (f x) (p - q)) = p - q := by
      have h4 := congrArg
        (fun L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) =>
          L (p - q)) h3
      simpa using h4
    rw [hL, map_zero] at hM
    exact sub_eq_zero.mp hM.symm
  -- the chain rule
  have hmdA : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) A (f x) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact (hA.differentiable (by simp)).differentiableAt
  have hmdF : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x :=
    hf.mdifferentiableAt (by simp)
  have hchain : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (fun y => A (f y)) x
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) A (f x)).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x) := by
    simpa [Function.comp_def] using
      mfderiv_comp (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (I'' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (g := A) (f := f) x hmdA hmdF
  have h1 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) A (f x)
      = fderiv ℝ A (f x) := mfderiv_eq_fderiv
  rw [hchain, h1] at hvw
  have h2 : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x) v
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x) w := hAinj hvw
  exact himm x h2

/-- **The composite `f ∘ δ` of two immersions has non-vanishing derivative.**  This is the regularity
hypothesis of `Work.Whitney.CutPush.arc_unknotting` for the chord `f ∘ δ`. -/
theorem fderiv_comp_spine_ne_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
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
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t)) :
    ∀ t : ℝ, fderiv ℝ (fun s : ℝ => f (δ s)) t 1 ≠ 0 := by
  intro t hzero
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
  have h4 : (1 : ℝ) = 0 := hδimm t (h3.trans (map_zero _).symm)
  norm_num at h4

end Work.Whitney.CutPush
