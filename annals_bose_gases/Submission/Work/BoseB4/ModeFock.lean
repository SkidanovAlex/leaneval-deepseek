import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.RealFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.ModeFock` — arbitrary mode families on the real bosonic Fock space

FS's second-quantised `a_k` are not the "coordinate" modes `∂/∂x_l` of
`Work.BoseB4.RealFock`, but *superpositions*: `a_k = a(f_k)` for the one-particle
vector `f_k = Q(e^{ikx}χ_Λ) ∈ L²(Λ)`.  This module adds that layer on top of the
coordinate model:

* `annOf m f := Σ_l f_l · (∂/∂x_l)` — annihilation of the superposition with
  coordinate vector `f : Fin m → ℝ`;
* `creOf m f := Σ_l f_l · (mult x_l)` — its adjoint;
* `gram f g := Σ_l f_l g_l` — the Gram product of two coordinate vectors.

The content is that these are a bosonic mode system with the commutator kernel
`[annOf f, creOf g] = gram f g · 1`, i.e. exactly FS `eq:Commutator_general`
once `f_k` is FS's `Q(e^{ikx}χ_Λ)` — whose Gram product
`⟨Q(e^{ikx}χ_Λ), Q(e^{ik'x}χ_Λ)⟩ = χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ)` is the box
computation (`Work.BoseB7.ccrKernel`).  `Work.BoseB4.B7Instance` packages this as
an inhabitant of `Work.BoseB7.FockData`.

The one-particle space here is `Fin m → ℝ` with the standard inner product: the
caller chooses an orthonormal basis of the (finite-dimensional) span of the mode
vectors and passes coordinates.  `Work.BoseB4.Gram` shows that *every* symmetric
positive semidefinite kernel on `Mode` arises this way, so this loses nothing.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- Annihilation of the superposition with coordinate vector `f`:
`annOf m f = Σ_l f_l · ∂/∂x_l`. -/
noncomputable def annOf (m : ℕ) (f : Fin m → ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ l : Fin m, (f l) • ann m l

/-- Creation of the superposition with coordinate vector `f`:
`creOf m f = Σ_l f_l · (multiplication by x_l)`. -/
noncomputable def creOf (m : ℕ) (f : Fin m → ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ l : Fin m, (f l) • cre m l

/-- The Gram product `⟪f, g⟫ = Σ_l f_l g_l` of two coordinate vectors. -/
noncomputable def gram {m : ℕ} (f g : Fin m → ℝ) : ℝ := ∑ l : Fin m, f l * g l

@[simp]
lemma annOf_zero (m : ℕ) : annOf m (0 : Fin m → ℝ) = 0 := by
  simp [annOf]

@[simp]
lemma creOf_zero (m : ℕ) : creOf m (0 : Fin m → ℝ) = 0 := by
  simp [creOf]

@[simp]
lemma gram_zero_left {m : ℕ} (g : Fin m → ℝ) : gram (0 : Fin m → ℝ) g = 0 := by
  simp [gram]

@[simp]
lemma gram_comm {m : ℕ} (f g : Fin m → ℝ) : gram f g = gram g f := by
  simp only [gram]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end Work.BoseB4
