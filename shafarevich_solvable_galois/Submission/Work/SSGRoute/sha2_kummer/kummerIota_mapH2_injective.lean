import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Submission.Work.AbsoluteGalois.exists_hom_lift_iff_pullbackCocycle_mem_B2
import Submission.Work.AbsoluteGalois.sectionCocycle_mem_Z2
import Submission.Work.AbsoluteGalois.twisted_splitting_iff_mem_B2
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker_pair
import Submission.Work.AbsoluteKummer.Functoriality
import Submission.Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective
import Submission.Work.AbsoluteKummer.H1Pi.nonempty_h1_pi_equiv
import Submission.Work.AbsoluteKummer.Kummer.kummerQuotientEquiv
import Submission.Work.AbsoluteKummer.Kummer.nonempty_h0_addUnits_equiv
import Submission.Work.AbsoluteKummer.KummerBijective
import Submission.Work.AbsoluteKummer.Rat
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact_H2
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer injection `H²(G_k, μ_p) ↪ H²(G_k, k̄ˣ)`

For a field `k` and a prime `p`, the coefficient map of the Kummer sequence
`1 → μ_p → k̄ˣ →^p k̄ˣ → 1` is injective on `H²`: the classical identification `H²(G_k, μ_p) ↪ Br k`,
whose kernel is `H¹(G_k, k̄ˣ)/p = 0` by Hilbert 90.

The Kummer short exact sequence is built here concretely (with `iota = kummerIota p`,
`pi = kummerPi p`), so that `S.iota` is *definitionally* the Kummer inclusion.  Exactness at
`H²(μ_p)` (`SES.range_deltaH2_eq_ker_mapH2`) identifies the kernel of the coefficient map with the
range of the connecting map `S.deltaH2 : H¹(G_k,k̄ˣ) →+ H²(G_k,μ_p)`, whose source is a subsingleton
(`Hilbert90.H1_eq_zero`); hence the range is `⊥` and the coefficient map is injective.
-/

namespace Work.SSGRoute

open scoped Classical

/-- **The Kummer injection.**  The map `H²(G_k, μ_p) → H²(G_k, k̄ˣ)` induced by the inclusion
`μ_p ↪ k̄ˣ` is injective. -/
theorem kummerIota_mapH2_injective (k : Type) [Field k] [NumberField k] (p : ℕ) [Fact p.Prime]
    (hμ : ∃ ζ : k, IsPrimitiveRoot ζ p) :
    Function.Injective (Work.AbsoluteKummer.mapH2 (G := AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (Work.AbsoluteKummer.Kummer.kummerIota (k := k) p)
      (Work.AbsoluteKummer.Kummer.kummerIota_equivariant (k := k) p)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsGalois k (AlgebraicClosure k) := IsAlgClosure.isGalois k _
  -- the Kummer short exact sequence, built concretely
  let S : Work.AbsoluteKummer.ShortExactSeq (Work.AbsoluteKummer.G k)
      (Additive (rootsOfUnity p (AlgebraicClosure k)))
      (Additive (AlgebraicClosure k)ˣ) (Additive (AlgebraicClosure k)ˣ) :=
    { iota := Work.AbsoluteKummer.Kummer.kummerIota (k := k) p
      pi := Work.AbsoluteKummer.Kummer.kummerPi (k := k) p
      iota_equivariant := Work.AbsoluteKummer.Kummer.kummerIota_equivariant (k := k) p
      pi_equivariant := Work.AbsoluteKummer.Kummer.kummerPi_equivariant (k := k) p
      iota_injective := Work.AbsoluteKummer.Kummer.kummerIota_injective (k := k) p
      pi_surjective := Work.AbsoluteKummer.Kummer.kummerPi_surjective (k := k) p
      range_iota_eq_ker_pi := Work.AbsoluteKummer.Kummer.kummerIota_range_eq_ker_pi (k := k) p
      isDiscreteM := Work.AbsoluteKummer.isDiscreteModule_addRootsOfUnity k p
      isDiscreteN := Work.AbsoluteKummer.isDiscreteModule_addUnits k
      isDiscreteP := Work.AbsoluteKummer.isDiscreteModule_addUnits k }
  -- `S.iota` is `kummerIota p`, definitionally
  have hmap : (Work.AbsoluteKummer.mapH2 (G := AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (Work.AbsoluteKummer.Kummer.kummerIota (k := k) p)
        (Work.AbsoluteKummer.Kummer.kummerIota_equivariant (k := k) p))
      = (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant) := rfl
  -- the connecting map of the Kummer sequence has a subsingleton source, hence zero range
  haveI hsub : Subsingleton
      (Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G k) (Additive (AlgebraicClosure k)ˣ)) :=
    ⟨fun a b => (Work.AbsoluteKummer.Hilbert90.H1_eq_zero (k := k) a).trans
      (Work.AbsoluteKummer.Hilbert90.H1_eq_zero (k := k) b).symm⟩
  have hker : (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker = ⊥ := by
    rw [← Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2 S]
    refine le_antisymm (fun y hy => ?_) bot_le
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [show x = 0 from Subsingleton.elim x 0, map_zero]
    simp
  rw [hmap]
  exact (AddMonoidHom.ker_eq_bot_iff _).mp hker

end Work.SSGRoute
