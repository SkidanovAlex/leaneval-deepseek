/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# `U(G)` is a `*`-ring

The Ore localisation `U(G) = N(G)[(N(G) ∖ {0})⁻¹]` carries the involution of
`Work.ORVonNeumann.Ore.starOre`, because the non-zero-divisors of `N(G)` are stable under `⋆`
(`Work.ORVonNeumann.Ore.star_mem_nonZeroDivisors`).  This makes `U(G)` a `*`-ring and, by
`Work.ORVonNeumann.Ore.starOre_num`, the structure map `N(G) →+* U(G)` a `*`-map.

## Main results

* `Work.ORVonNeumann.VonNeumannAlgebra.instStarAffiliated`, `...instInvolutiveStarAffiliated`,
  `...instStarMulAffiliated`, `...instStarRingAffiliated` — the `*`-structure on `U(G)`;
* `Work.ORVonNeumann.VonNeumannAlgebra.affiliated_star_numerator` —
  `(N(G) →+* U(G))` commutes with `⋆`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.VonNeumannAlgebra
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.U
import Submission.Work.ORVonNeumann.Ore.star_mem_nonZeroDivisors
import Submission.Work.ORVonNeumann.Ore.star_oreLocalization

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORVonNeumann.VonNeumannAlgebra

open Work.ORVonNeumann

variable {G : Type u} [Group G]

/-- The involution hypothesis of `Ore.starOre` for the non-zero-divisors of `N(G)`. -/
theorem starSubset (D : GroupVonNeumannAlgebra G) :
    ∀ s : nonZeroDivisors D.N, star (s : D.N) ∈ nonZeroDivisors D.N :=
  fun s => Ore.star_mem_nonZeroDivisors s.2

/-- **The involution on `U(G)`.** -/
noncomputable instance instStarAffiliated (D : GroupVonNeumannAlgebra G) : Star D.affiliated :=
  ⟨Ore.starOre (starSubset D)⟩

theorem affiliated_star_def (D : GroupVonNeumannAlgebra G) (x : D.affiliated) :
    star x = Ore.starOre (starSubset D) x := rfl

noncomputable instance instInvolutiveStarAffiliated (D : GroupVonNeumannAlgebra G) :
    InvolutiveStar D.affiliated where
  star_involutive x := Ore.starOre_invol (starSubset D) x

noncomputable instance instStarMulAffiliated (D : GroupVonNeumannAlgebra G) : StarMul D.affiliated where
  star_mul x y := Ore.starOre_mul (starSubset D) x y

noncomputable instance instStarAddMonoidAffiliated (D : GroupVonNeumannAlgebra G) :
    StarAddMonoid D.affiliated where
  star_add x y := Ore.starOre_add (starSubset D) x y

noncomputable instance instStarRingAffiliated (D : GroupVonNeumannAlgebra G) : StarRing D.affiliated where
  star_add x y := Ore.starOre_add (starSubset D) x y

/-- The structure map `N(G) →+* U(G)` commutes with the involution. -/
theorem affiliated_star_numerator (D : GroupVonNeumannAlgebra G) (r : D.N) :
    star ((OreLocalization.numeratorRingHom (S := nonZeroDivisors D.N)) r)
      = (OreLocalization.numeratorRingHom (S := nonZeroDivisors D.N)) (star r) :=
  Ore.starOre_num (starSubset D) r

/-- **The lift `ℂ[G] →+* N(G)` is a `*`-map.** -/
theorem liftHom_star (D : GroupVonNeumannAlgebra G) (f : MonoidAlgebra ℂ G) :
    star (liftHom D f) = liftHom D (star f) := by
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro x y hx hy
    rw [map_add, star_add, star_add, map_add, hx, hy]
  · intro g c
    rw [liftHom_apply, liftHom_apply, MonoidAlgebra.star_single, D.lift_single, D.lift_single,
      D.star_smul, D.ρ_star]

/-- **`ℂ[G] →+* U(G)` is a `*`-map**: the group algebra is a `*`-subalgebra of `U(G)`. -/
theorem toU_star (D : GroupVonNeumannAlgebra G) (f : MonoidAlgebra ℂ G) :
    star (toU D f) = toU D (star f) := by
  have h1 : toU D f = (OreLocalization.numeratorRingHom (S := nonZeroDivisors D.N))
      (D.lift f) := toU_apply D f
  have h2 : toU D (star f) = (OreLocalization.numeratorRingHom (S := nonZeroDivisors D.N))
      (D.lift (star f)) := toU_apply D (star f)
  rw [h1, h2, affiliated_star_numerator D (D.lift f)]
  congr 1
  rw [← liftHom_apply D f, ← liftHom_apply D (star f)]
  exact liftHom_star D f

end Work.ORVonNeumann.VonNeumannAlgebra
