/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The tame inertia at a `𝔭`-adic completion

This file discharges **deliverables 1 and 2** of the area for a genuine local field
`κ = K_𝔭 = 𝔭.adicCompletion K` and `K'` a separable closure of `κ`:

* `NK.TameStructure.unramifiedQuotient_adicCompletion`:
  `Gal(K'/κ) ⧸ I_κ ≅ Ẑ` (NSW (7.5.6)), from the classical input
  `NK.TameStructure.UnramifiedZhat` (`Gal(κ(μ_{p'})/κ) ≅ Ẑ`) through the Galois-correspondence
  bridge `NK.TameStructure.quotient_inertiaSubgroup_mulEquiv_unramifiedClosure`;
* `NK.TameStructure.tameInertiaInput_adicCompletion`:
  `NK.TameData.TameInertiaInput p (K_𝔭) K'` (NSW (7.5.7) Corollary, (7.5.11); Iwasawa).

Two of the four fields of `TameInertiaInput` are **derived** here, i.e. removed from the input
catalogue:

* the commutator relation `[I_κ, I_κ] ≤ V_κ` (`tameInertia_commutator_mem`): the image of `I_κ` in
  `G_κ/V_κ` is a pro-cyclic *profinite* group (`IsClosed V_κ` makes it a quotient of a compact
  group) and a profinite group all of whose finite quotients are cyclic is abelian
  (`NK.LocalStructure.Tame.commute_of_isProCyclic_of_profinite`);
* the pro-prime-to-`p`-ness of `I_κ/V_κ` (NSW (7.5.11)) (`isProPrimeToP_tameInertia`), via
  `NK.TameStructure.ProfiniteAux.isProPrimeToP_of_maxNormalProP`: a pro-cyclic profinite group
  which is not pro-prime-to-`p` has a nontrivial *characteristic* pro-`p` subgroup, whose preimage
  in `G_κ` would be a normal pro-`p` subgroup strictly containing `V_κ`.

What remains as named input is `NK.TameStructure.TameInertiaStructure` (the maximality of
`I_κ/V_κ` among the closed normal pro-cyclic subgroups of `G_κ/V_κ`, NSW (7.5.7) Corollary, and the
closedness of `V_κ`, Serre IV §2) together with `NK.TameStructure.UnramifiedZhat`.
-/
import Submission.NK.TameStructure.GaloisBridge
import Submission.NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral
import Submission.NK.TameStructure.ProfiniteAux.commutator_mem_of_isMaxNormalProCyclicInQuotient
import Submission.NK.TameStructure.ProfiniteAux.isProPrimeToP_of_maxNormalProP
import Submission.NK.TameData.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructure

universe u

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']

/-! ## The inertia subgroup is closed -/

/-- **The inertia subgroup is closed** in the Krull topology.  `I_κ` is the fixing subgroup of
`κ(μ_{p'})` (`NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure`),
and the fixing subgroup of any intermediate field is closed as long as `K'/κ` is integral
(`NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral`), which a separable
closure always is. -/
theorem inertiaSubgroup_isClosed (p : ℕ) :
    IsClosed (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p :
      Set (Gal(K'/𝔭.adicCompletion K))) := by
  rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure]
  exact NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral _

/-! ## Deliverable 1: the unramified quotient is `Ẑ` -/

/-- **Deliverable 1** (NSW (7.5.6), (7.5.7) Corollary): the maximal unramified quotient of
`G_κ = Gal(K'/κ)` is `Ẑ`,

  `Gal(K'/κ) ⧸ I_κ ≅ Gal(κ(μ_{p'})/κ) ≅ Ẑ`.

The first isomorphism is the Galois correspondence
(`NK.TameStructure.quotient_inertiaSubgroup_mulEquiv_unramifiedClosure`, proved), the second is
the classical input `NK.TameStructure.UnramifiedZhat` (`κ(μ_{p'})` is the maximal unramified
extension of `κ` and its Galois group is `Gal(𝔽̄_q/𝔽_q) ≅ Ẑ`).

This is the field `unramifiedQuotient` of `NK.TameData.TameInertiaInput`. -/
theorem unramifiedQuotient_adicCompletion (p : ℕ) (h : UnramifiedZhat p K 𝔭 K') :
    Nonempty (Gal(K'/𝔭.adicCompletion K) ⧸
      NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p ≃*
      NK.LocalAnabelian.Zhat) := by
  obtain ⟨e1⟩ := quotient_inertiaSubgroup_mulEquiv_unramifiedClosure
    (κ := 𝔭.adicCompletion K) (K' := K') p
  obtain ⟨e2⟩ := h
  exact ⟨e1.trans e2⟩

/-! ## The commutator field, derived from the maximality of the tame inertia -/

/-- **`[I_κ, I_κ] ≤ V_κ`**, derived from the maximality part of the structure of the tame inertia
(NSW (7.5.7) Corollary): `I_κ/V_κ` is pro-cyclic, and — because `V_κ` is closed in the profinite
group `G_κ` — it is a *profinite* pro-cyclic group, hence abelian
(`NK.LocalStructure.Tame.commute_of_isProCyclic_of_profinite`).

This is the field `tameInertia_commutator_mem` of `NK.TameData.TameInertiaInput`, so that field
is *not* an independent input: it follows from `IsMaxNormalProCyclicInQuotient`. -/
theorem tameInertia_commutator_mem (p : ℕ) (h : TameInertiaStructure p K 𝔭 K') :
    ∀ y ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p,
      ∀ z ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p,
        y * z * y⁻¹ * z⁻¹ ∈
          NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p :=
  NK.TameStructure.ProfiniteAux.commutator_mem_of_isMaxNormalProCyclicInQuotient
    h.2 (NK.LocalAnabelian.inertiaSubgroup_normal p) (inertiaSubgroup_isClosed 𝔭 K' p) h.1

/-- **`I_κ/V_κ` is pro-prime-to-`p`** (NSW (7.5.11)), *derived* from the maximality of the wild
inertia: `V_κ` is the maximal normal pro-`p` subgroup
(`NK.LocalTame.wildInertiaSubgroup_isProP`, `NK.LocalTame.le_wildInertiaSubgroup`), it is
closed (`NK.TameStructure.TameInertiaStructure`), and `I_κ/V_κ` is pro-cyclic
(`IsMaxNormalProCyclicInQuotient`), so
`NK.TameStructure.ProfiniteAux.isProPrimeToP_of_maxNormalProP` applies.

This is the field `isProPrimeToP_tameInertia` of `NK.TameData.TameInertiaInput`, so that field
is *not* an independent input either. -/
theorem isProPrimeToP_tameInertia (p : ℕ) (hp : p.Prime) (h : TameInertiaStructure p K 𝔭 K') :
    NK.LocalTame.IsProPrimeToP p
      ↥(NK.LocalTame.tameInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p) := by
  rw [NK.LocalTame.tameInertiaSubgroup_eq_quotientImage]
  exact NK.TameStructure.ProfiniteAux.isProPrimeToP_of_maxNormalProP hp h.2
    (NK.LocalAnabelian.inertiaSubgroup_normal p) (inertiaSubgroup_isClosed 𝔭 K' p)
    (NK.LocalTame.wildInertiaSubgroup_isProP p)
    (fun N hN hNp => NK.LocalTame.le_wildInertiaSubgroup hN hNp)
    (NK.TameData.quotientImage_normal (NK.LocalAnabelian.inertiaSubgroup_normal p)) h.1.2.2.1

/-! ## Deliverable 2: the structure of the tame quotient -/

/-- **Deliverable 2** (NSW (7.5.7) Corollary and (7.5.11); Iwasawa, *On Galois groups of local
fields*): the reduced input catalogue of the structure of the tame quotient,

  `NK.TameData.TameInertiaInput p (K_𝔭) K'`,

for a genuine `p`-adic field `K_𝔭` and a separable closure `K'`.

* the commutator field is *proved* from the maximality statement
  (`NK.TameStructure.tameInertia_commutator_mem`);
* the pro-prime-to-`p`-ness of `I_κ/V_κ` is *proved* from the maximality of `V_κ`
  (`NK.TameStructure.isProPrimeToP_tameInertia`);
* the unramified quotient comes from the Galois correspondence and the classical input
  `NK.TameStructure.UnramifiedZhat`
  (`NK.TameStructure.unramifiedQuotient_adicCompletion`);

the only remaining input is the maximality of `I_κ/V_κ` among the closed normal pro-cyclic
subgroups of `G_κ/V_κ` together with the closedness of `V_κ`
(`NK.TameStructure.TameInertiaStructure`, NSW (7.5.7) Corollary). -/
theorem tameInertiaInput_adicCompletion (p : ℕ) (hp : p.Prime)
    (h : TameInertiaStructure p K 𝔭 K') (hu : UnramifiedZhat p K 𝔭 K') :
    NK.TameData.TameInertiaInput p (𝔭.adicCompletion K) K' where
  hp := hp
  isTameInertia := h.1
  isProPrimeToP_tameInertia := isProPrimeToP_tameInertia 𝔭 K' p hp h
  tameInertia_commutator_mem := tameInertia_commutator_mem 𝔭 K' p h
  unramifiedQuotient := unramifiedQuotient_adicCompletion 𝔭 K' p hu

end

end NK.TameStructure
