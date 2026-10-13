import Mathlib
import Submission.Work.DSMap.Mix2

namespace Work.DSCHART

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry

/-- In a homogeneous localization away from `f`, the fraction `f / f ^ 1` is `1` (the numerator
and the denominator are one and the same element). -/
lemma awayMk_self {R : Type*} [CommRing R] {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {σ : Type*} [SetLike σ R] [AddSubgroupClass σ R] {𝒜 : ι → σ} [GradedRing 𝒜]
    {d : ι} {f : R} (hf : f ∈ 𝒜 d) :
    HomogeneousLocalization.Away.mk 𝒜 hf 1 f (by rw [one_smul]; exact hf) = 1 := by
  simp [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk]

/-- `xiSec i j k` is the section `x_k / x_j` of `𝒪` on the chart `X ∩ D₊(x_j)`: it is the image
of the homogeneous localization element `x_k / 1 ∈ A[x]⁰_{x_j}` under the two ring maps
`A[x]⁰_{x_j} → Γ(ℙᴺ_A, D₊(x_j)) → Γ(X, X ∩ D₊(x_j))`, both of which preserve `1`. For `k = j` the
element is `x_j / x_j = 1`. -/
theorem xiSec_self {A : Type*} [CommRing A] {X : Scheme} {N : ℕ}
    (i : X ⟶ DSMap.PSpace A N) (j : Fin (N + 1)) :
    DSMap.Mix2.xiSec i j j = 1 := by
  have h : HomogeneousLocalization.Away.mk (DSMap.PGr A N) (DSMap.Mix2.X_mem_PGr j) 1
      (MvPolynomial.X j) (by rw [one_smul]; exact DSMap.Mix2.X_mem_PGr j) = 1 :=
    awayMk_self (DSMap.Mix2.X_mem_PGr j)
  unfold DSMap.Mix2.xiSec
  rw [h, map_one, map_one]
  rfl

end Work.DSCHART
