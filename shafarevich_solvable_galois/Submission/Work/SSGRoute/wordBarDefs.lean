import Mathlib
import Submission.Work.SSGRoute.prop5.nestedLieDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The mod-`2` free associative algebra on a type `X`, and its Lie part

This module provides the vocabulary for the "mod-`2` free Lie algebra" statements used in the
odd-`j` half of `DiagonalCore`:

* `WordBar X` is `𝔽₂⟨X⟩ = FreeMonoid X →₀ ZMod 2`, the free associative `𝔽₂`-algebra on `X`,
  modelled as functions on the free monoid;
* `redZ X : ℤ⟨X⟩ →+ 𝔽₂⟨X⟩` is coefficient reduction;
* `wordBarσ X σ` is the relabelling action of a permutation `σ` of `X`;
* `barLie X j` is the degree-`j` part of the free `𝔽₂`-Lie algebra on `X`: the `𝔽₂`-span of the
  reductions of the bracket monomials `brkMon X c` of the binary trees of size `j`.
-/

noncomputable section

namespace Work.SSGRoute

open Work.SSGRoute.prop5

/-- The free associative `𝔽₂`-algebra on `X`, as the type of `𝔽₂`-valued functions on words. -/
abbrev WordBar (X : Type*) := FreeMonoid X →₀ ZMod 2

/-- Coefficient reduction `ℤ⟨X⟩ → 𝔽₂⟨X⟩`. -/
def redZ (X : Type*) : prop5.FreeAssoc X →+ WordBar X :=
  { toFun := fun a =>
      MonoidAlgebra.coeff (MonoidAlgebra.mapRingHom (FreeMonoid X) (Int.castRingHom (ZMod 2)) a)
    map_zero' := by simp
    map_add' := by intro a b; simp [MonoidAlgebra.coeff_add] }

/-- The relabelling action of `σ` on `𝔽₂⟨X⟩`. -/
def wordBarσ (X : Type*) (σ : X ≃ X) : WordBar X →ₗ[ZMod 2] WordBar X :=
  Finsupp.linearCombination (ZMod 2) (fun w : FreeMonoid X =>
    Finsupp.single (FreeMonoid.map (σ : X → X) w) (1 : ZMod 2))

/-- `wordBarσ` is `Finsupp.mapDomain` along the relabelling of words. -/
theorem wordBarσ_apply (X : Type*) (σ : X ≃ X) (v : WordBar X) :
    wordBarσ X σ v = Finsupp.mapDomain (FreeMonoid.map (σ : X → X)) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp [wordBarσ]
  | add f g hf hg => rw [map_add, Finsupp.mapDomain_add, hf, hg]
  | single a b =>
      rw [wordBarσ, Finsupp.linearCombination_single, Finsupp.mapDomain_single,
        Finsupp.smul_single]
      simp

@[simp] theorem wordBarσ_single (X : Type*) (σ : X ≃ X) (w : FreeMonoid X) (c : ZMod 2) :
    wordBarσ X σ (Finsupp.single w c) = Finsupp.single (FreeMonoid.map (σ : X → X) w) c := by
  rw [wordBarσ, Finsupp.linearCombination_single]
  simp

/-- The degree-`j` part of the free `𝔽₂`-Lie algebra on `X`: the `𝔽₂`-span of the reductions of the
bracket monomials of the binary trees of size `j`. -/
def barLie (X : Type*) (j : ℕ) : Submodule (ZMod 2) (WordBar X) :=
  Submodule.span (ZMod 2)
    (Set.range fun c : {c : prop5.Magma X // prop5.Magma.size c = j} => redZ X (prop5.brkMon X c.1))

@[simp] theorem redZ_apply (X : Type*) (a : prop5.FreeAssoc X) :
    redZ X a = MonoidAlgebra.coeff
      (MonoidAlgebra.mapRingHom (FreeMonoid X) (Int.castRingHom (ZMod 2)) a) := rfl

end Work.SSGRoute
