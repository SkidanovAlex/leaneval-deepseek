import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.TameStructure.GaloisBridge
import Submission.NK.TameStructure.ProfiniteAux.commutator_mem_of_isMaxNormalProCyclicInQuotient
import Submission.NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral
import Submission.NK.TameStructure.ProfiniteAux.isProPrimeToP_of_maxNormalProP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-! ## The residual: the classical local structure theorem -/

/-- **The classical local structure theorem for `G_κ`, as a single residual.**

For a `p`-adic field `κ` with residue field of `q` elements and separable closure `K'`, this
records exactly the arithmetic content of

  `G_κ^{tr} = G_κ/V_κ ≅ Ẑ ⋉ ∏_{ℓ ≠ p} ℤ_ℓ(1)`,

namely: the unramified quotient, the maximality of the tame inertia, the closedness of the wild
inertia, the Frobenius and its normalisation, and the abelianised tame quotient.  Every other
statement of the local structure theory is *proved* from these in the sibling modules of this
directory; the two fields of `NK.TameData.TameInertiaInput` that used to be inputs
(`isProPrimeToP_tameInertia`, `tameInertia_commutator_mem`) are among the consequences.

Note that the residue field cardinality `q` is a *parameter*: for a genuine local field
`κ = K_𝔭` it is pinned to `NK.LocalStructure.residueCard K 𝔭` by the arithmetic of the
completion, and `q` is provably a power of `p` (`NK.TameStructureDeep.q_eq_of_charP`). -/
structure TameRamificationCore (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K'] :
    Prop where
  /-- `p` is a prime number (the residue characteristic of `κ`) -/
  hp : p.Prime
  /-- **NSW (7.5.6), (7.5.7) Corollary**: the unramified quotient is `Ẑ`,
  `G_κ ⧸ I_κ ≅ Gal(κ^ur/κ) ≅ Ẑ` -/
  unramifiedQuotient :
    Nonempty ((Gal(K'/κ) ⧸ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) ≃*
      NK.LocalAnabelian.Zhat)
  /-- **NSW (7.5.7) Corollary; Iwasawa**: `I_κ/V_κ` is the maximal closed normal pro-cyclic
  subgroup of `G_κ^{tr} = G_κ ⧸ V_κ` (equivalently: the maximal tamely ramified extension of `κ`
  is `κ^ur(π^{1/n} : (n,p) = 1)` for a uniformiser `π`, so `I_κ/V_κ ≅ ∏_{ℓ ≠ p} ℤ_ℓ`) -/
  isTameInertia :
    NK.LocalTame.IsMaxNormalProCyclicInQuotient
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p)
  /-- **NSW (7.5.6)**: the normalised Frobenius exists — an element outside `I_κ` acting on the
  roots of unity of order prime to `p` by `ζ ↦ ζ^q` -/
  exists_frobenius : ∃ x : Gal(K'/κ), NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x
  /-- **NSW (12.1.8) Lemma; Iwasawa**: the Frobenius normalisation.  An element of `G_κ` acts on
  the prime-to-`p` roots of unity by `ζ ↦ ζ^q` **iff** it lies outside `I_κ` and conjugates the
  tame inertia `I_κ/V_κ` by the `q`-th power map.  Equivalently: the cyclotomic character
  identifies `G_κ/I_κ ≅ Ẑ` with `ℤ q ⊆ Aut(I_κ/V_κ) = ∏_{ℓ ≠ p} ℤ_ℓ^×`, and it is injective. -/
  frobenius_iff : ∀ x : Gal(K'/κ),
    NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x ↔
      NK.LocalTame.IsTameFrobeniusLift q
        (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
        (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x
  /-- **Shimizu, arXiv:2009.10431, Lemma 2.1** (via local class field theory): the abelianised
  tame quotient is `Ẑ × μ_{q-1}` -/
  abelianisation : Nonempty
    (NK.LocalTame.tameAbelianization (κ := κ) (K' := K') p ≃*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))))

/-! ## Basic API of the residual -/

namespace TameRamificationCore

variable {p q : ℕ} (h : TameRamificationCore p q κ K')

include h

/-- The wild inertia is contained in the inertia subgroup: the first component of the maximality
of `I_κ/V_κ`. -/
theorem wildInertia_le_inertia :
    NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p ≤
      NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p :=
  h.isTameInertia.1

/-- The tame inertia `I_κ/V_κ` is pro-cyclic in the workspace's sense (all finite quotients are
cyclic): the second component of the maximality. -/
theorem isProCyclic_tameInertia :
    NK.LocalTame.IsProCyclic
      ↥(NK.LocalTame.quotientImage (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
        (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p)) :=
  h.isTameInertia.2.2.1

/-- The maximality statement, unpacked: any `J ≥ V_κ` whose image in `G_κ^{tr}` is normal and
pro-cyclic lies in the inertia subgroup. -/
theorem le_inertia_of_isProCyclic {J : Subgroup (Gal(K'/κ))}
    (hJ : NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p ≤ J)
    (hJn : (NK.LocalTame.quotientImage (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      J).Normal)
    (hJc : NK.LocalTame.IsProCyclic
      ↥(NK.LocalTame.quotientImage (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p) J)) :
    J ≤ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p :=
  h.isTameInertia.2.2.2 J hJ hJn hJc

/-- The Frobenius normalisation, in the direction used to produce a Frobenius lift from a
Frobenius element. -/
theorem isTameFrobeniusLift_of_isFrobeniusFor {x : Gal(K'/κ)}
    (hx : NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x) :
    NK.LocalTame.IsTameFrobeniusLift q
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x :=
  (h.frobenius_iff x).mp hx

/-- The Frobenius normalisation, in the direction used to derive the cyclotomic action on the
roots of unity from the action on the tame inertia. -/
theorem actsAsFrobenius_of_isTameFrobeniusLift {x : Gal(K'/κ)}
    (hx : NK.LocalTame.IsTameFrobeniusLift q
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x) :
    NK.LocalAnabelian.ActsAsFrobenius (κ := κ) (K' := K') p q x :=
  ((h.frobenius_iff x).mpr hx).2

/-- The Frobenius element supplied by the residual, together with both of its defining
properties. -/
theorem exists_isFrobeniusFor_and_isTameFrobeniusLift :
    ∃ x : Gal(K'/κ),
      NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x ∧
        NK.LocalTame.IsTameFrobeniusLift q
          (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
          (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x := by
  obtain ⟨x, hx⟩ := h.exists_frobenius
  exact ⟨x, hx, h.isTameFrobeniusLift_of_isFrobeniusFor hx⟩

end TameRamificationCore

end

end NK.TameStructureDeep
