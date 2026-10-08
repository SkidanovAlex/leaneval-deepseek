import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.Main
import Submission.Work.Hering.AppVII.extraspecial_char

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix VII, Part 2: central elements act as scalars of modulus one

Let `G` be a finite group, `χ` an irreducible complex character of `G` and `z` a central
element of `G`.  Then there is a complex number `ω` of modulus one such that
`χ (z * x) = ω * χ x` for every `x : G`.

This is the classical statement that an irreducible character, restricted to the centre, is a
multiple of a linear character.  The proof chooses a simple submodule `N` of the regular module
`ℂ[G]` affording `χ`; the associated representation `ρ = submoduleRep N` is irreducible, and by
Schur's lemma every central element acts on it by a scalar (`centerScalarHom`, proved in
`Work.Hering.AppVII.extraspecial_char`).  Writing `ω` for the scalar attached to `z`, the
character identity `χ (z * x) = ω * χ x` is the multiplicativity of the trace, and `ω` has
modulus one because `lam` is a monoid homomorphism out of the finite centre, so `ω ^ |G| = 1`.
-/

namespace Work.Hering.AppVII

open Classical

theorem part2_central_scalar {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) {z : G} (hz : z ∈ Subgroup.center G) :
    ∃ ω : ℂ, ω * starRingEnd ℂ ω = 1 ∧ ∀ x : G, χ (z * x) = ω * χ x := by
  classical
  -- Choose a simple submodule of the regular module whose character is `χ`.
  obtain ⟨N, hN, hNchar⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hχ
  haveI hsimple : IsSimpleModule (Work.CharCore.groupAlgebra G) N :=
    Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
  haveI hirr : (Work.CharCore.submoduleRep N).IsIrreducible :=
    Work.Clifford.submoduleRep_isIrreducible hN
  haveI hnt : Nontrivial ↥N := IsSimpleModule.nontrivial (Work.CharCore.groupAlgebra G) N
  -- Schur's lemma: the centre acts by scalars.
  obtain ⟨lam, hlam⟩ := centerScalarHom (Work.CharCore.submoduleRep N)
  refine ⟨lam ⟨z, hz⟩, ?_, ?_⟩
  · -- `ω = lam z` has modulus one, because `lam` is a homomorphism out of a finite group.
    have hpow : (lam ⟨z, hz⟩) ^ Fintype.card G = 1 := by
      have h1 : ((⟨z, hz⟩ : Subgroup.center G) ^ Fintype.card G) = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact pow_card_eq_one
      have h2 := congrArg lam h1
      rwa [map_pow, map_one] at h2
    have hrn : (Complex.normSq (lam ⟨z, hz⟩)) ^ Fintype.card G = 1 := by
      rw [← map_pow Complex.normSq (lam ⟨z, hz⟩) (Fintype.card G), hpow, Complex.normSq_one]
    have hne : Fintype.card G ≠ 0 := (Fintype.card_pos_iff.mpr ⟨1⟩).ne'
    have hnorm : Complex.normSq (lam ⟨z, hz⟩) = 1 :=
      (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) hne).mp hrn
    rw [Complex.mul_conj, hnorm, Complex.ofReal_one]
  · -- The character identity, by multiplicativity of the trace.
    intro x
    rw [← hNchar]
    show (LinearMap.trace ℂ ↥N) ((Work.CharCore.submoduleRep N) (z * x))
        = lam ⟨z, hz⟩ * (LinearMap.trace ℂ ↥N) ((Work.CharCore.submoduleRep N) x)
    rw [map_mul, hlam ⟨z, hz⟩]
    rw [show (lam ⟨z, hz⟩ • (1 : ↥N →ₗ[ℂ] ↥N)) * (Work.CharCore.submoduleRep N) x
        = lam ⟨z, hz⟩ • (Work.CharCore.submoduleRep N) x from by ext v; simp]
    rw [map_smul, smul_eq_mul]

end Work.Hering.AppVII
