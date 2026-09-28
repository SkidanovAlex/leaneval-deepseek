import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Q44Setup

/-!
# Setup for `Work.Q44Geom.S_count`

We count the rank-`3` primitive (saturated) sublattices `L ⊆ ℤ^5` on which a fixed
irreducible quartic form `f = formOf 4 4 c` vanishes and whose successive minima are bounded
by `s : Fin 3 → ℝ`.

The proof strategy (see `Submission/Work/Q44Geom/S_count.lean`) is:

* the map `L ↦ span_ℚ L` is injective on saturated lattices, so the lattices through a
  *good pair* of short lattice vectors are counted by `planes44` (the number of isotropic
  `3`-planes through such a pair is bounded), and
* the remaining (`bad`) lattices are counted as cosets of a fixed rank-`2` lattice inside the
  invariant subspace.

This file collects the definitions shared with the delegated lemmas.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Q44Geom

open MvPolynomial

/-- `f44 c`, the quartic form attached to a coefficient vector `c`. -/
abbrev f44 (c : Work.HP.Mon 4 4 → ℤ) : MvPolynomial (Fin 5) ℚ := Work.HP.formOf 4 4 c

/-- The **invariance subspace** of `f`: the space of directions `w` such that
`f(x + t w) = f(x)` for all `x` and all `t`. -/
def invSub (f : MvPolynomial (Fin 5) ℚ) : Submodule ℚ (Fin 5 → ℚ) where
  carrier := {w | ∀ (x : Fin 5 → ℚ) (t : ℚ), MvPolynomial.eval (x + t • w) f = MvPolynomial.eval x f}
  zero_mem' := by intro x t; simp
  add_mem' := by
    intro u v hu hv x t
    have h1 : x + t • (u + v) = (x + t • u) + t • v := by
      simp only [smul_add]; abel
    rw [h1, hv, hu]
  smul_mem' := by
    intro a u hu x t
    have h1 : x + t • (a • u) = x + (t * a) • u := by
      rw [smul_smul]
    rw [h1, hu]

/-- An element of the invariance subspace is a direction of translation invariance. -/
lemma mem_invSub_point {f : MvPolynomial (Fin 5) ℚ} {w : Fin 5 → ℚ} (h : w ∈ invSub f) :
    ∀ x : Fin 5 → ℚ, MvPolynomial.eval (x + w) f = MvPolynomial.eval x f := by
  intro x
  simpa using h x 1

/-- The coefficientwise coercion `ℤ^5 → ℚ^5` as a `ℤ`-linear map. -/
def toRatLM : (Fin 5 → ℤ) →ₗ[ℤ] (Fin 5 → ℚ) where
  toFun v := fun i => (v i : ℚ)
  map_add' u v := by funext i; simp
  map_smul' a v := by funext i; simp

/-- The integral vectors lying in the invariance subspace. -/
def latW (f : MvPolynomial (Fin 5) ℚ) : Submodule ℤ (Fin 5 → ℤ) :=
  Submodule.comap toRatLM ((invSub f).restrictScalars ℤ)

lemma mem_latW_iff {f : MvPolynomial (Fin 5) ℚ} {v : Fin 5 → ℤ} :
    v ∈ latW f ↔ toRatLM v ∈ invSub f := Iff.rfl

/-- `v` is *not* an invariance direction of `f`. -/
def NotInv (f : MvPolynomial (Fin 5) ℚ) (v : Fin 5 → ℤ) : Prop := toRatLM v ∉ invSub f

/-- The ℚ-span of an integral lattice. -/
def ratSpan (L : Submodule ℤ (Fin 5 → ℤ)) : Submodule ℚ (Fin 5 → ℚ) :=
  Submodule.span ℚ (Set.range fun v : L => toRatLM (v : Fin 5 → ℤ))

end Work.Q44Geom
