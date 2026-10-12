import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.CFock` — the complex ℓ² space of finitely supported multi-sequences

FS's `thm:Kafz` needs a **complex** Hilbert space for the spectator modes (the
coherent parameter `z` is complex), while the mode lattice of node B7 is real.
The bridge is the complexification of the (real) finitely supported Fock core
`Work.BoseB4.RealFock X = (X →₀ ℕ) →₀ ℝ`.  Mathlib has no `Complexification`,
and no normed/inner-product instance on `Finsupp`, so this module presents the
complex Fock core **as a submodule of Mathlib's `lp`**, where every instance
(`NormedAddCommGroup`, `InnerProductSpace ℂ`) comes from
`Submodule.innerProductSpace`:

* `toLp` — the canonical (injective) linear embedding
  `((X →₀ ℕ) →₀ ℂ) →ₗ[ℂ] lp (fun _ : (X →₀ ℕ) => ℂ) 2`;
* `cfock X` — its range: the complex Fock core, with `InnerProductSpace ℂ` for free;
* `toCFock` — the linear equivalence `((X →₀ ℕ) →₀ ℂ) ≃ₗ[ℂ] cfock X`;
* `annF`/`creF` — the ladder operators of the mode `j` at the `Finsupp` level:
  `annF j` **lowers** the occupation (`(annF j f) γ = √(γ_j+1) f (γ+e_j)` in
  coordinates, i.e. `single γ c ↦ c√(γ_j) · single (γ-e_j)` on basis vectors) and
  `creF j` **raises** it; these are the *normalised* occupation-basis
  conventions, for which `creF j` is the ℓ²-adjoint of `annF j`;
* `annC`/`creC` — their images on `cfock X`, the genuine mode operators.
-/

noncomputable section

open scoped lp

namespace Work.BoseB4

set_option autoImplicit false

/-- The canonical embedding of the complex Fock core `(X →₀ ℕ) →₀ ℂ` into
`ℓ²(X →₀ ℕ)`; injective and `ℂ`-linear. -/
noncomputable def toLp (X : Type*) [DecidableEq X] :
    ((X →₀ ℕ) →₀ ℂ) →ₗ[ℂ] lp (fun _ : (X →₀ ℕ) => ℂ) 2 :=
  Finsupp.lsum ℂ fun α : X →₀ ℕ =>
    lp.singleContinuousLinearMap ℂ (fun _ : (X →₀ ℕ) => ℂ) 2 α

lemma toLp_eq_sum (X : Type*) [DecidableEq X] (f : (X →₀ ℕ) →₀ ℂ) :
    (toLp X f : lp (fun _ : (X →₀ ℕ) => ℂ) 2)
      = ∑ α ∈ f.support, lp.single 2 α (f α) := rfl

lemma toLp_apply (X : Type*) [DecidableEq X] (f : (X →₀ ℕ) →₀ ℂ) (α : X →₀ ℕ) :
    ((toLp X f : lp (fun _ : (X →₀ ℕ) => ℂ) 2) : (X →₀ ℕ) → ℂ) α = f α := by
  rw [toLp_eq_sum, lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single α]
  · rw [lp.coeFn_single, Pi.single_apply, if_pos rfl]
  · intro m _ hm
    rw [lp.coeFn_single, Pi.single_apply, if_neg (Ne.symm hm)]
  · intro hn
    rw [lp.coeFn_single, Pi.single_apply, if_pos rfl]
    simpa [Finsupp.mem_support_iff] using hn

lemma toLp_injective (X : Type*) [DecidableEq X] : Function.Injective (toLp X) := by
  intro f g h
  ext α
  have := congrFun (congrArg (fun v : lp (fun _ : (X →₀ ℕ) => ℂ) 2 => (v : (X →₀ ℕ) → ℂ)) h) α
  simpa [toLp_apply] using this

/-- **The complex Fock core** `(X →₀ ℕ) →₀ ℂ`, presented as a submodule of
`ℓ²(X →₀ ℕ)` so that it inherits `InnerProductSpace ℂ`. -/
noncomputable def cfock (X : Type*) [DecidableEq X] : Submodule ℂ (lp (fun _ : (X →₀ ℕ) => ℂ) 2) :=
  LinearMap.range (toLp X)

/-- The linear equivalence `((X →₀ ℕ) →₀ ℂ) ≃ₗ[ℂ] cfock X`. -/
noncomputable def toCFock (X : Type*) [DecidableEq X] : ((X →₀ ℕ) →₀ ℂ) ≃ₗ[ℂ] cfock X :=
  LinearEquiv.ofInjective (toLp X) (toLp_injective X)

/-! ## The ladder operators of a mode -/

/-- Annihilation of the mode `j` on the complex Fock core: on basis vectors
`(annF j) (single γ c) = c · √(γ_j) · single (γ - e_j)`, i.e. in coordinates
`(annF j f) γ = √(γ_j + 1) · f (γ + e_j)`. -/
noncomputable def annF (X : Type*) [DecidableEq X] (j : X) : ((X →₀ ℕ) →₀ ℂ) →ₗ[ℂ] ((X →₀ ℕ) →₀ ℂ) :=
  Finsupp.lsum ℂ fun γ : X →₀ ℕ =>
    LinearMap.toSpanSingleton ℂ _
      ((Real.sqrt ((γ j : ℝ)) : ℂ) • Finsupp.single (γ - Finsupp.single j 1) (1 : ℂ))

/-- Creation of the mode `j` on the complex Fock core: on basis vectors
`(creF j) (single γ c) = c · √(γ_j + 1) · single (γ + e_j)`, i.e. in coordinates
`(creF j f) γ = √(γ_j) · f (γ - e_j)`. -/
noncomputable def creF (X : Type*) [DecidableEq X] (j : X) : ((X →₀ ℕ) →₀ ℂ) →ₗ[ℂ] ((X →₀ ℕ) →₀ ℂ) :=
  Finsupp.lsum ℂ fun γ : X →₀ ℕ =>
    LinearMap.toSpanSingleton ℂ _
      ((Real.sqrt ((γ j : ℝ) + 1) : ℂ) • Finsupp.single (γ + Finsupp.single j 1) (1 : ℂ))

/-- Annihilation of the mode `j` on `cfock X`. -/
noncomputable def annC (X : Type*) [DecidableEq X] (j : X) : cfock X →ₗ[ℂ] cfock X :=
  (toCFock X).toLinearMap.comp ((annF X j).comp (toCFock X).symm.toLinearMap)

/-- Creation of the mode `j` on `cfock X`. -/
noncomputable def creC (X : Type*) [DecidableEq X] (j : X) : cfock X →ₗ[ℂ] cfock X :=
  (toCFock X).toLinearMap.comp ((creF X j).comp (toCFock X).symm.toLinearMap)

end Work.BoseB4
