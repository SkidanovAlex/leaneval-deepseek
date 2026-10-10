import Mathlib.FieldTheory.Galois.Notation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.TameStructureDeep.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.TameStructureDeep

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- **The reduced residual: the local structure theorem for `G_κ` with its two unconditional
fields removed.**

Everything in `NK.TameStructureDeep.TameRamificationCore` except `unramifiedQuotient` and
`exists_frobenius`, which are *theorems* for `κ = K_𝔭`
(`NK.TameStructureDeep.tameRamificationCore_adicCompletion`). -/
structure TameRamificationResidual (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K'] :
    Prop where
  /-- `p` is the residue characteristic, a prime -/
  hp : p.Prime
  /-- **NSW (7.5.7) Corollary; Iwasawa**: `I_κ/V_κ` is the maximal closed normal pro-cyclic
  subgroup of `G_κ^{tr}` -/
  isTameInertia :
    NK.LocalTame.IsMaxNormalProCyclicInQuotient
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p)
  /-- **NSW (12.1.8) Lemma; Iwasawa**: the Frobenius normalisation -/
  frobenius_iff : ∀ x : Gal(K'/κ),
    NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x ↔
      NK.LocalTame.IsTameFrobeniusLift q
        (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
        (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x
  /-- **Shimizu, arXiv:2009.10431, Lemma 2.1** (local class field theory): the abelianised tame
  quotient is `Ẑ × μ_{q-1}` -/
  abelianisation : Nonempty
    (NK.LocalTame.tameAbelianization (κ := κ) (K' := K') p ≃*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))))

/-- **The first named classical input of the reduced residual: the Kummer-theoretic structure of
the tame quotient** (NSW, *Cohomology of Number Fields*, (7.5.6), (7.5.7) Corollary, (7.5.11) and
(12.1.8) Lemma; Iwasawa, *On Galois groups of local fields*):

* `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ^{tr}` — equivalently
  `κ^{tr} = κ^ur(π^{1/n} : (n,p) = 1)` for a uniformiser `π`, so `I_κ/V_κ ≅ ∏_{ℓ ≠ p} ℤ_ℓ`;
* the Frobenius normalisation: `ζ ↦ ζ^q` on the prime-to-`p` roots of unity if and only if the
  `q`-th power map on the tame inertia — the Tate twist `I_κ/V_κ ≅ ∏_{ℓ ≠ p} ℤ_ℓ(1)`.

Both are Kummer theory over the unramified base `κ^ur` (which contains every root of unity of
order prime to `p`): the fields `κ^ur(π^{1/n})` are cyclic of degree `n` over `κ^ur` and the
Kummer pairing `Gal(κ^ur(π^{1/n})/κ^ur) × μ_n → μ_n` is `G_κ`-equivariant.  This is the only
mathematical input left for the *ramification* half of the local structure theorem; nothing of it
is available in Mathlib (neither `∏_{ℓ ≠ p} ℤ_ℓ` nor the Kummer pairing over a local field). -/
structure TameQuotientKummer (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K'] : Prop where
  /-- `p` is a prime -/
  hp : p.Prime
  /-- **NSW (7.5.7) Corollary; Iwasawa**: `I_κ/V_κ` is the maximal closed normal pro-cyclic
  subgroup of `G_κ^{tr}` -/
  isTameInertia :
    NK.LocalTame.IsMaxNormalProCyclicInQuotient
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p)
  /-- **NSW (12.1.8) Lemma; Iwasawa**: the Frobenius normalisation -/
  frobenius_iff : ∀ x : Gal(K'/κ),
    NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x ↔
      NK.LocalTame.IsTameFrobeniusLift q
        (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
        (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x

/-- **The second named classical input of the reduced residual: the abelianised tame quotient**
(Shimizu, arXiv:2009.10431, Lemma 2.1, via local class field theory):
`G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}`.  Its content beyond local reciprocity (`κˣ^{∧} ≅ G_κ^{ab}`, proved in
the sibling chapter `Submission/Work/LocalReciprocityLubinTate/`) and the structure of the units
(`NK.TameStructureDeep.Units`, proved here) is the ramification-theoretic half of the
reciprocity dictionary: the image of the wild inertia `V_κ` in `κˣ^{∧}` is exactly the group `U¹`
of principal units. -/
structure TameAbelianisedQuotient (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K'] :
    Prop where
  /-- **Shimizu 2.1**: `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` -/
  abelianisation : Nonempty
    (NK.LocalTame.tameAbelianization (κ := κ) (K' := K') p ≃*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))))

/-- **The reduced residual from its two named classical inputs.** -/
theorem TameRamificationResidual.ofKummerAndAbelianised {p q : ℕ} (h₁ : TameQuotientKummer p q κ K')
    (h₂ : TameAbelianisedQuotient p q κ K') : TameRamificationResidual p q κ K' where
  hp := h₁.hp
  isTameInertia := h₁.isTameInertia
  frobenius_iff := h₁.frobenius_iff
  abelianisation := h₂.abelianisation

/-- **The reduced residual gives the full residual**, once the unramified quotient and the
existence of the normalised Frobenius are supplied.  At `κ = K_𝔭` both come from `Core.lean`. -/
theorem TameRamificationResidual.toCore {p q : ℕ} (h : TameRamificationResidual p q κ K')
    (hunramified : Nonempty
      ((Gal(K'/κ) ⧸ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) ≃*
        NK.LocalAnabelian.Zhat))
    (hexists : ∃ x : Gal(K'/κ),
      NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x) :
    TameRamificationCore p q κ K' where
  hp := h.hp
  unramifiedQuotient := hunramified
  isTameInertia := h.isTameInertia
  exists_frobenius := hexists
  frobenius_iff := h.frobenius_iff
  abelianisation := h.abelianisation

end

end NK.TameStructureDeep
