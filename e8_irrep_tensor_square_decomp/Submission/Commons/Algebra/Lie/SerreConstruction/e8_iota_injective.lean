import Mathlib
import Submission.Commons.Algebra.Lie.PBW.pbw_standardMonomial_basis

set_option linter.style.haveILetI false

/-!
# Injectivity of `ι : L → U(L)`, and the case `L = e₈(ℂ)`

The universal enveloping algebra `U(L)` of a Lie algebra `L` over a commutative ring `R` comes
with a canonical Lie algebra morphism `UniversalEnvelopingAlgebra.ι R : L → U(L)`, and the
Poincaré–Birkhoff–Witt theorem implies that this map is *injective*: the enveloping algebra is
"large enough" to contain `L`.

Here we deduce injectivity from the PBW standard-monomial basis already available in the shared
commons (`Commons.Algebra.Lie.PBW.standardMonomial_basis`): over a field `K` of characteristic
zero, and for any basis `e : I → L` of `L` whose index type is linearly ordered, the products of
the elements `ι (e i)` over nondecreasing words form a `K`-basis of `U(L)`.  In particular the
family `i ↦ ι (e i)` is linearly independent, so `ι` — a linear map from a free module carrying a
basis to a linearly independent family — is injective.

As a corollary we obtain `e8_iota_injective` for the exceptional Lie algebra `e₈(ℂ)` of the
Serre construction.
-/

universe u

namespace Commons.Algebra.Lie.SerreConstruction

open UniversalEnvelopingAlgebra

/-- **Poincaré–Birkhoff–Witt, injectivity form.**  For a Lie algebra `L` over a field `K` of
characteristic zero, the canonical map `ι : L → U(L)` from `L` to its universal enveloping
algebra is injective. -/
theorem iota_injective_of_field (K L : Type u) [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] :
    Function.Injective
      (UniversalEnvelopingAlgebra.ι K : L → UniversalEnvelopingAlgebra K L) := by
  classical
  letI : LieRing (UniversalEnvelopingAlgebra K L) := LieRing.ofAssociativeRing
  -- every vector space is free: pick a basis of `L` over `K` ...
  obtain ⟨⟨I, e⟩⟩ := Module.Free.exists_basis (R := K) (M := L)
  -- ... and linearly order its index type (well-ordering theorem).
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  -- PBW: the standard monomials form a `K`-basis of `U(L)`.
  obtain ⟨B, hB⟩ := _root_.Commons.Algebra.Lie.PBW.standardMonomial_basis K L I e
  set g : I → UniversalEnvelopingAlgebra K L := fun i => UniversalEnvelopingAlgebra.ι K (e i)
    with hg
  -- The images of the basis vectors of `L` are part of a basis of `U(L)`, hence independent.
  have hli : LinearIndependent K g := by
    let f : I → {w : List I // w.Pairwise (fun a b : I => a ≤ b)} :=
      fun i => ⟨[i], List.pairwise_singleton (· ≤ ·) i⟩
    have hfinj : Function.Injective f := by
      intro i j hij
      exact List.singleton_injective (congrArg Subtype.val hij)
    have h := B.linearIndependent.comp f hfinj
    have hcomp : (B ∘ f) = g := by
      funext i
      simp [f, g, hB]
    rwa [hcomp] at h
  intro x y hxy
  have h0 : UniversalEnvelopingAlgebra.ι K (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  -- `ι` is linear, so it commutes with the expansion of `x - y` in the basis `e`.
  have hkey : Finsupp.linearCombination K g (e.repr (x - y))
      = UniversalEnvelopingAlgebra.ι K (x - y) := by
    have h := Finsupp.apply_linearCombination
      (f := (UniversalEnvelopingAlgebra.ι K).toLinearMap) (v := e) (l := e.repr (x - y))
    rw [e.linearCombination_repr (x - y)] at h
    exact h.symm
  -- Linear independence of the `ι (e i)` forces the coefficients to vanish.
  have hc0 : e.repr (x - y) = 0 :=
    hli.finsuppLinearCombination_injective (by rw [hkey, h0]; simp)
  have hxy0 : x - y = 0 := by
    rw [← e.linearCombination_repr (x - y), hc0]
    simp
  exact sub_eq_zero.mp hxy0

/-- The canonical map `ι : e₈(ℂ) → U(e₈(ℂ))` is injective, i.e. the enveloping algebra of the
exceptional Lie algebra `e₈` contains `e₈` as a Lie subalgebra. -/
theorem e8_iota_injective :
    Function.Injective
      (UniversalEnvelopingAlgebra.ι ℂ :
        LieAlgebra.e₈ ℂ → UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)) := by
  exact iota_injective_of_field ℂ (LieAlgebra.e₈ ℂ)

end Commons.Algebra.Lie.SerreConstruction
