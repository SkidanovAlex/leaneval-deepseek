import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.E9Nodes.e9_baseS
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E9Nodes

open SSGRoute.PTExt CategoryTheory

/-- **Cohomology over a trivial group vanishes in positive degrees.**  If `H` is a trivial group
(a subsingleton type) then `Rep Coeff H`-modules are just `Coeff`-modules with a trivial action,
`ℤ = unitRep H` is projective (`Rep.trivial_projective_of_subsingleton`), and `Ext` of a projective
object vanishes in positive degrees. -/
theorem extH_subsingleton_of_subsingleton_group {H : Type} [Group H] [Subsingleton H]
    (A : Rep.{0} Coeff H) {n : ℕ} (hn : 1 ≤ n) : Subsingleton (extH A n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact CategoryTheory.Abelian.Ext.subsingleton_of_projective (unitRep H) A m

/-- **Restriction of a positive-degree class to the trivial subgroup vanishes.**  Immediate from
`extH_subsingleton_of_subsingleton_group`: the group `↥(⊥ : Subgroup G)` is trivial. -/
theorem extHRestrict_bot_eq_zero {G : Type} [Group G] {A : Rep.{0} Coeff G} {n : ℕ}
    (hn : 1 ≤ n) (h : extH A n) : extHRestrict (⊥ : Subgroup G) h = 0 := by
  haveI := extH_subsingleton_of_subsingleton_group (H := ↥(⊥ : Subgroup G))
    (A := Rep.res (⊥ : Subgroup G).subtype A) (n := n) hn
  exact Subsingleton.elim _ _

/-- **Unramified places carry unramified classes.**  If the finite place `q` of `L` is unramified
over `k` (ramification index `1`), then its inertia group is trivial, so the only subgroup all of
whose elements lie in the inertia group is `⊥`, and restricting any class of positive degree to
`⊥` gives `0`: the class is unramified at `q`. -/
theorem unramified_isUnramifiedClassAt {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {M : Rep SSGRoute.PTExt.Coeff (L ≃ₐ[k] L)}
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1)
    (h : extH M 1) : IsUnramifiedClassAt q h := by
  intro D hD
  -- the inertia group of an unramified place is trivial
  have hbot : Ideal.inertia (L ≃ₐ[k] L) q.asIdeal = ⊥ :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (q.asIdeal.under (NumberField.RingOfIntegers k)) q.asIdeal).mpr h1
  -- hence every subgroup `D` consisting of inertia elements is trivial
  have hDbot : D = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    have hmem : σ ∈ Ideal.inertia (L ≃ₐ[k] L) q.asIdeal :=
      (isInertiaAt_iff_mem_inertia (k := k) (K := L) q σ).mp (hD σ hσ)
    rw [hbot] at hmem
    exact hmem
  rw [hDbot]
  exact extHRestrict_bot_eq_zero le_rfl h

theorem e9_unramified_all_but_finite (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (M : Rep SSGRoute.PTExt.Coeff (L ≃ₐ[k] L)) (h : SSGRoute.PTExt.extH M 1) :
    ({q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) |
        ¬ SSGRoute.PTExt.IsUnramifiedClassAt q h} : Set _).Finite := by
  refine Set.Finite.subset
    (Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := k) (L := L)) ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq ⊢
  by_contra h1
  exact hq (unramified_isUnramifiedClassAt (M := M) q h1 h)

end Work.SSGRoute.E9Nodes
