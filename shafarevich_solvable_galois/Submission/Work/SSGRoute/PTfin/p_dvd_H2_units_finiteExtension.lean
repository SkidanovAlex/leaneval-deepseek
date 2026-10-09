import Mathlib
import Submission.Work.SSGRoute.PTCore.H2_units_level_structure
import Submission.Work.SSGRoute.PTCore.H2_units_infl
import Submission.Work.SSGRoute.PTCore.level_units_H2_cyclic
import Submission.Work.SSGRoute.PT.local_exists_degree_mul_level
import Submission.Work.SSGRoute.PT.p_dvd_H2_units_adicCompletion
import Submission.Work.SSGRoute.PTCore.local_exists_degree_p_level
import Submission.Work.SSGRoute.PT.isSolvable_algEquiv_of_finiteDimensional
import Submission.Work.SSGRoute.PT.h2_equiv_of_equiv
import Submission.Work.SSGRoute.PTfin.levelH2_cyclic_finiteExtension
import Submission.Work.SSGRoute.PTfin.exists_superlevel_p_dvd_index_finiteExtension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PTfin

open Work.SSGRoute.PTCore

/-- **`p`-divisibility of `H²(G_F, F̄ˣ)` for a finite extension `F` of a `Q`-adic field.**

This is the finite-extension form of `Work.SSGRoute.PT.p_dvd_H2_units_adicCompletion`: for `K` a
number field, `Q` a finite place of `K`, `F` a finite extension of the `Q`-adic completion `K_Q`
and `p` a prime, multiplication by `p` is surjective on the continuous cohomology
`H²(G_F, F̄ˣ)`, i.e. every class has a `p`-th root.

The proof is the same abstract level argument as in the base case, now with the two arithmetic
inputs for an arbitrary finite base:

* every finite Galois level `L / F` has cyclic `H²(Gal(L/F), Lˣ)` of order `[L : F]`
  (`Work.SSGRoute.PTfin.levelH2_cyclic_finiteExtension`, from the local fundamental class
  `NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local` and the order
  computation `NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank`);
* every finite Galois level `L` has a finite Galois superlevel `L'` with
  `[L : F] * p ∣ [L' : F]` (`Work.SSGRoute.PTfin.exists_superlevel_p_dvd_index_finiteExtension`).

The level structure (injectivity, nesting, covering of `H²(G_F, F̄ˣ)` by its finite levels) is the
base-field independent `Work.SSGRoute.PTCore.H2_units_level_structure`, and the group-theoretic
assembly is `Work.SSGRoute.PT.surjective_nsmul_of_cover_cyclic`. -/
theorem p_dvd_H2_units_finiteExtension (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F : Type} [Field F] [Algebra (Q.adicCompletion K) F] [FiniteDimensional (Q.adicCompletion K) F] :
    Function.Surjective (fun x : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G F)
      (Additive ((AlgebraicClosure F)ˣ)) => p • x) := by
  -- `F` is an algebra over the characteristic-zero field `K_Q`, hence of characteristic zero, so
  -- its algebraic closure is Galois over it
  haveI hk : CharZero (Q.adicCompletion K) :=
    charZero_of_injective_algebraMap
      (RingHom.injective (algebraMap ℚ (Q.adicCompletion K)))
  have hInj : Function.Injective (algebraMap (Q.adicCompletion K) F) :=
    RingHom.injective (algebraMap (Q.adicCompletion K) F)
  haveI hFc : CharZero F :=
    CharZero.of_addMonoidHom (algebraMap (Q.adicCompletion K) F).toAddMonoidHom (by simp) hInj
  haveI hG : IsGalois F (AlgebraicClosure F) := IsAlgClosure.isGalois F (AlgebraicClosure F)
  refine Work.SSGRoute.PT.surjective_nsmul_of_cover_cyclic
    (ι := FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (lt := fun (L L' : FiniteGaloisIntermediateField F (AlgebraicClosure F)) =>
      (L : IntermediateField F (AlgebraicClosure F)) ≤
        (L' : IntermediateField F (AlgebraicClosure F)))
    (A := fun L => LevelH2 L) (n := fun L => Module.finrank F ↥L)
    (φ := fun L => psiTilde L) p ?_ ?_ ?_ ?_ ?_ ?_
  · -- the degree of a level is positive
    intro L
    rw [Module.finrank_pos_iff_of_free]
    infer_instance
  · -- cyclicity of the level cohomology
    intro L
    exact levelH2_cyclic_finiteExtension Q L
  · -- injectivity of the level inflation
    intro L
    exact psiTilde_injective L
  · -- nesting of the level inflations
    intro L L' h
    exact psiTilde_range_mono L L' h
  · -- every class lives on a finite level
    intro x
    exact psiTilde_range_cover x
  · -- enlargement of a level so that the relative degree is divisible by `p`
    intro L
    exact exists_superlevel_p_dvd_index_finiteExtension p Q L

end Work.SSGRoute.PTfin
