import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.GonLib
import Submission.Work.HP.BCSDefs
import Submission.Work.HP.lat_min_attained

/-!
# Definitions for the recursive (Schmidt) lattice point bound

This file sets up the single "peel off a shortest vector and project" step of the
induction that proves `Work.HP.FM.schmidt_bound`.

Given an injective `ℝ`-linear presentation `Φ : (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι`
of a rank-`R` lattice, a primitive vector `u ∈ ℤ^R` and a complementary family
`v : Fin (R-1) → (Fin R → ℤ)` that together with `u` form a `ℤ`-basis of `ℤ^R`, the
projected lattice is presented by `latStep Φ u v`, whose basis vectors are the
orthogonal projections of `Φ (v j)` onto the orthogonal complement of `Φ u`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.FM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The projectional presentation `Ψ` of the lattice obtained by peeling off the shortest
vector `Φ u` and projecting onto its orthogonal complement. -/
def latStep {R : ℕ} (Φ : LatMap (ι := ι) R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    LatMap (ι := ι) (R - 1) :=
  ∑ j : Fin (R - 1),
    (LinearMap.proj j : (Fin (R - 1) → ℝ) →ₗ[ℝ] ℝ).smulRight
      (projU (Φ (fun k => (u k : ℝ))) (Φ (fun k => (v j k : ℝ))))

@[simp] lemma latStep_apply {R : ℕ} (Φ : LatMap (ι := ι) R) (u : Fin R → ℤ)
    (v : Fin (R - 1) → (Fin R → ℤ)) (t : Fin (R - 1) → ℝ) :
    latStep Φ u v t = ∑ j, t j • projU (Φ (fun k => (u k : ℝ))) (Φ (fun k => (v j k : ℝ))) := by
  simp [latStep, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

/-- Casting an integer linear combination of integer vectors, entrywise. -/
lemma cast_sum_smul {R : ℕ} (t : Fin (R - 1) → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    (fun k => ((∑ j, t j • v j) k : ℝ)) = ∑ j, (t j : ℝ) • (fun k => (v j k : ℝ)) := by
  ext k
  simp [Finset.sum_apply, Pi.smul_apply]

/-- The projection of `Φ` applied to an integer vector. -/
lemma latStep_cast {R : ℕ} (Φ : LatMap (ι := ι) R) (u : Fin R → ℤ)
    (v : Fin (R - 1) → (Fin R → ℤ)) (t : Fin (R - 1) → ℤ) :
    latStep Φ u v (fun j => (t j : ℝ))
      = projU (Φ (fun k => (u k : ℝ))) (Φ (fun k => ((∑ j, t j • v j) k : ℝ))) := by
  rw [latStep_apply, cast_sum_smul]
  rw [map_sum Φ (fun j => (t j : ℝ) • (fun k => (v j k : ℝ))) Finset.univ]
  rw [map_sum (projU (Φ fun k => (u k : ℝ)))
        (fun j => Φ ((t j : ℝ) • (fun k => (v j k : ℝ)))) Finset.univ]
  simp only [map_smul]

/-- The data of one inductive step: an injective presentation `Φ`, a shortest primitive
vector `u` and a complementary family `v` completing `u` to a `ℤ`-basis of `ℤ^R`. -/
structure RecData (R : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- the presentation of the ambient lattice -/
  Φ : LatMap (ι := ι) R
  /-- the shortest primitive coefficient vector -/
  u : Fin R → ℤ
  /-- the complementary basis vectors -/
  v : Fin (R - 1) → (Fin R → ℤ)
  /-- injectivity of the presentation -/
  Φ_inj : Function.Injective Φ
  /-- `u` is nonzero -/
  u_ne : u ≠ 0
  /-- `u` is primitive -/
  u_prim : IsPrim u
  /-- `u` and `v` form a `ℤ`-basis of `ℤ^R` -/
  bij : Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i)
  /-- the realifications of `u, v` are `ℝ`-linearly independent -/
  indep : ∀ c : ℝ × (Fin (R - 1) → ℝ),
    c.1 • (fun j => (u j : ℝ)) + ∑ i, c.2 i • (fun j => (v i j : ℝ)) = 0 → c = 0

variable {R : ℕ}

/-- The projected presentation attached to a `RecData`. -/
def RecData.step (D : RecData R ι) : LatMap (ι := ι) (R - 1) := latStep D.Φ D.u D.v

/-- The shortest vector of the ambient lattice, as an element of Euclidean space. -/
def RecData.p (D : RecData R ι) : EuclideanSpace ℝ ι := D.Φ (fun j => (D.u j : ℝ))

/-- The projected step map evaluated on an integer vector. -/
lemma RecData.step_cast (D : RecData R ι) (t : Fin (R - 1) → ℤ) :
    D.step (fun j => (t j : ℝ))
      = projU D.p (D.Φ (fun k => ((∑ j, t j • D.v j) k : ℝ))) := by
  rw [RecData.step, latStep_cast]
  rfl

/-- The decomposition of `Φ` on the `ℤ`-basis `(u, v)`. -/
lemma RecData.Phi_cast_bij (D : RecData R ι) (c : ℤ) (t : Fin (R - 1) → ℤ) :
    D.Φ (fun k => ((c • D.u + ∑ i, t i • D.v i) k : ℝ))
      = (c : ℝ) • D.p + D.Φ (fun k => ((∑ i, t i • D.v i) k : ℝ)) := by
  have h : (fun k => ((c • D.u + ∑ i, t i • D.v i) k : ℝ))
      = (c : ℝ) • (fun k => (D.u k : ℝ)) + ∑ i, (t i : ℝ) • (fun k => (D.v i k : ℝ)) := by
    ext k
    simp [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
  rw [h, map_add, map_smul, RecData.p]
  congr 1
  rw [cast_sum_smul]

end Work.HP.FM
