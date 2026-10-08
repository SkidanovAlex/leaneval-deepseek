import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory

/-!
# The restriction multiplicity is invariant under an involutive pullback

Let `K` be a finite subgroup of a finite group `U` with `|K|` invertible in `ℂ`, let
`f : K →* K` be an involutive monoid endomorphism (`f (f x) = x`), and let `a` be a class
function on `U` that is constant along `f` (`a (f k) = a k`).  Then for *any* class
function `μ` on `K`,

`⟨Res_K a, μ ∘ f⟩_K = ⟨Res_K a, μ⟩_K`.

The content is purely combinatorial: `f` is a bijection of `K` (an involution), so
reindexing the summation defining the inner product by `f` turns the first factor
`Res_K a (f k) = a (f k)` into `a k` by the invariance hypothesis.  The general
reindexing statement is isolated as `innerSum_compHom_of_involutive`.
-/

/-- **Reindexing the unscaled inner sum along an involutive endomorphism.**  If `φ : K → ℂ`
is a class function invariant under an involutive monoid endomorphism `f : K →* K`, then
pulling a class function `ψ` back along `f` does not change the unscaled inner sum
`Σ_k φ k · star (ψ k)`. -/
theorem innerSum_compHom_of_involutive {K : Type*} [Group K] [Fintype K]
    (f : K →* K) (hf : ∀ x, f (f x) = x) (φ ψ : ClassFunction K ℂ)
    (hfix : ∀ k : K, φ (f k) = φ k) :
    ClassFunction.innerSum φ (ClassFunction.compHom f ψ) = ClassFunction.innerSum φ ψ := by
  simp only [ClassFunction.innerSum, ClassFunction.compHom_apply]
  -- `f` is a bijection of `K`: it is injective (as `f (f x) = x`) and surjective.
  have hinj : Function.Injective f := fun x y h => by rw [← hf x, ← hf y, h]
  let e : K ≃ K := Equiv.ofBijective f ⟨hinj, fun y => ⟨f y, hf y⟩⟩
  have he : ∀ k, e k = f k := fun k => Equiv.ofBijective_apply f _ k
  -- Reindex the sum over `K` by the bijection `e`.
  have h := Equiv.sum_comp e (fun j : K => φ j * star (ψ j))
  simp only [he] at h
  rw [← h]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [hfix k]

/-- The normalized inner product `⟨Res_K a, ·⟩_K` is invariant under pulling the second
argument back along an involutive endomorphism `f` that fixes `a`. -/
theorem restrictionMultiplicityCompHomOfInvolutive {U : Type} [Group U] [Finite U] [Fintype U]
    (K : Subgroup U) [Fintype K] [Invertible (Nat.card K : ℂ)]
    (f : K →* K) (hf : ∀ x, f (f x) = x) (a : ClassFunction U ℂ)
    (hfix : ∀ k : K, a (f k) = a k) (μ : ClassFunction K ℂ) :
    ClassFunction.restrictionMultiplicity K a (ClassFunction.compHom f μ) =
      ClassFunction.restrictionMultiplicity K a μ := by
  have hfix' : ∀ k : K, ClassFunction.restrict K a (f k) = ClassFunction.restrict K a k := by
    intro k; simp only [ClassFunction.restrict_apply, hfix k]
  -- Both multiplicities are `|K|⁻¹` times the corresponding unscaled inner sum.
  rw [ClassFunction.restrictionMultiplicity, ClassFunction.restrictionMultiplicity,
    ClassFunction.inner, ClassFunction.inner,
    innerSum_compHom_of_involutive f hf (ClassFunction.restrict K a) μ hfix']

end Work.BG
