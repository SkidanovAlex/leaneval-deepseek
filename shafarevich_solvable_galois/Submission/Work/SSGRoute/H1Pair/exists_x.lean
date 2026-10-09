/-
# Step 2 of the assembly of `coker_obstruction`: the element `x = pad⁻¹(ω)` of `H₁`

Given a linear form `Φ` on the `1`-cocycles of the contragredient representation `M^∨` which kills
the `1`-coboundaries, there is `x ∈ H₁(G, M)` such that the canonical Tate pairing with `x` computes
`Φ` on every cocycle:

  `tatePairLin M x (H1π b₀) = Φ b₀`   for every cocycle `b₀ : G → M^∨`.

The proof is: descend `Φ` to `H¹(G, M^∨)` (`exists_lift_of_kills_coboundaries`, the general form of
the third clause of `Work.SSGRoute.h1_bridge`), and invert the bijective Tate pairing
(`H1Pair.tatePairLin_bijective`: Tate duality over `𝔽_p`).

The representation `contra M = Rep.of M.ρ.dual` is the one for which `tatePairLin` is *defined*, and
it is exactly the representation on which `Work.SSGRoute.H1Pair.omega_functional_contra` produces the
form `ω` — so no transport of representations occurs anywhere in this step.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.H1Pair.Pairing
import Submission.Work.SSGRoute.H1Pair.Bijective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace Work.SSGRoute.H1Pair

/-- **Descent of a form on the `1`-cocycles of an arbitrary representation to `H¹`**: a linear form
on `cocycles₁ A` which vanishes on `coboundaries₁ A` factors through `H1π`. -/
theorem exists_lift_of_kills_coboundaries {k : Type} [CommRing k] {G : Type} [Group G]
    (A : Rep k G) (lin : ↥(groupCohomology.cocycles₁ A) →ₗ[k] k)
    (hlin : ∀ x : ↥(groupCohomology.cocycles₁ A),
      x.1 ∈ groupCohomology.coboundaries₁ A → lin x = 0) :
    ∃ Lift : groupCohomology.H1 A →ₗ[k] k,
      ∀ x : ↥(groupCohomology.cocycles₁ A), Lift ((groupCohomology.H1π A).hom x) = lin x := by
  have hsurj : Function.Surjective (groupCohomology.H1π A).hom :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H1π A)).1 inferInstance
  have hker : LinearMap.ker (groupCohomology.H1π A).hom ≤ LinearMap.ker lin := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    exact hlin y ((groupCohomology.H1π_eq_zero_iff (A := A) y).1 hy)
  refine ⟨(Submodule.liftQ _ lin hker).comp
    (((groupCohomology.H1π A).hom).quotKerEquivOfSurjective hsurj).symm.toLinearMap, ?_⟩
  intro x
  have h1 : ((((groupCohomology.H1π A).hom).quotKerEquivOfSurjective hsurj).symm.toLinearMap)
      ((groupCohomology.H1π A).hom x) = Submodule.Quotient.mk x :=
    LinearMap.quotKerEquivOfSurjective_symm_apply (f := (groupCohomology.H1π A).hom) hsurj x
  rw [LinearMap.comp_apply, h1, Submodule.liftQ_apply]

/-- **Step 2a** — the inverse of the canonical Tate pairing: for every linear form `Ψ` on
`H¹(G, M^∨)` there is `x ∈ H₁(G, M)` with `tatePairLin M x = Ψ`.  This is Tate duality
(`H1Pair.tatePairLin_bijective`). -/
theorem exists_x_of_functional (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (M : Rep (ZMod p) G) [Finite M.V]
    (Ψ : groupCohomology.H1 (contra M) →ₗ[ZMod p] ZMod p) :
    ∃ x : groupHomology.H1 M,
      ∀ y : groupCohomology.H1 (contra M), tatePairLin M x y = Ψ y := by
  obtain ⟨x, hx⟩ := (tatePairLin_bijective p M).2 Ψ
  exact ⟨x, fun y => by rw [hx]⟩

/-- **Step 2b** — the same, starting from a form on the `1`-cocycles of `M^∨` which kills the
`1`-coboundaries: first descend it to `H¹` (`exists_lift_of_kills_coboundaries`), then invert the
Tate pairing (`exists_x_of_functional`).  This is the form consumed by the assembly, whose form `ω`
(`Work.SSGRoute.H1Pair.omega_functional_contra`) is defined on the cocycles. -/
theorem exists_x_of_Phi (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (M : Rep (ZMod p) G) [Finite M.V]
    (Φ : ↥(groupCohomology.cocycles₁ (contra M)) →ₗ[ZMod p] ZMod p)
    (hΦ : ∀ x : ↥(groupCohomology.cocycles₁ (contra M)),
      x.1 ∈ groupCohomology.coboundaries₁ (contra M) → Φ x = 0) :
    ∃ x : groupHomology.H1 M, ∀ y : ↥(groupCohomology.cocycles₁ (contra M)),
      tatePairLin M x ((groupCohomology.H1π (contra M)).hom y) = Φ y := by
  obtain ⟨Ψ, hΨ⟩ := exists_lift_of_kills_coboundaries (contra M) Φ hΦ
  obtain ⟨x, hx⟩ := exists_x_of_functional p M Ψ
  exact ⟨x, fun y => (hx _).trans (hΨ y)⟩

end Work.SSGRoute.H1Pair
