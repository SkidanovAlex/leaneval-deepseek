import Mathlib
import Submission.NK.CFTLib.Existence.artinMapOfARL
import Submission.NK.CFTLib.Existence.artinKernel
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.GlobalCFTdeep.hasseNorm_form_universe
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.CFTLib.IdeleHasse.localFaithful_onePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

namespace NK.CFTLib.Existence

/-! **Hasse's norm principle with one place omitted** (Milne, *CFT*, VII.8.1(a) / V.5.3(a)): a global
element which is a local norm at every place except possibly one is a global idèlic norm.

## Status and route (for the prover)

This is the workspace's named crux, here in the `normImage` form; the same assertion already appears
as `NK.CFTLib.Existence.localNormImage_of_forall_ne` (no hypotheses except cyclicity) and as
`NK.CFTLib.IdeleHasse.normImage_of_localNorm_away_one` — both still `sorry`.  The **new input here
is `hARL`**, the ideal-theoretic Artin reciprocity law of Lang, *ANT*, Ch. X §1–2 (an integer modulus
`m` with the ramification clause `𝔭 ∤ m ⟹ 𝔭` unramified, and the product condition for the principal
ideal of any `a ≡ 1 mod m` which is totally positive).

Known pieces (all sorry-free):

* `NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm` — the local–global principle for idèlic norms:
  `x ∈ N_{L/K}𝕀_L ↔ ∀ v, x v ∈ N(L_wˣ)`;
* `NK.GlobalCFTdeep.hasseNorm_form_universe` — Hasse's norm principle for cyclic `L/K`:
  `principalIdele K a ∈ normImage K L → ∃ b : Lˣ, principalIdele K a = normIdeleFun K L (principalIdele L b)`;
* `NK.GlobalCFT.index_normClassSubgroup_eq_finrank` and
  `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic` — the index formula.

These reduce the claim to the *single place* statement (the "local component of the global Artin map
is faithful"): for `v₀` and `a ∈ K_{v₀}ˣ`, if the single-place idèle is in `Kˣ·N_{L/K}𝕀_L` then
`a ∈ N(L_{w₀}ˣ)`.  Equivalently (Milne VII.8.1(a)): the global Artin isomorphism of a cyclic `L/K` is
the product of the local Artin maps, `art = ∏_v θ_v`, hence for `a ∈ Kˣ` with `θ_v(a) = 1` for all
`v ≠ v₀` one has `θ_{v₀}(a) = art(a) = 1` (as `a` is a global element).

The intended input is `hARL`.  Available for the route (`Submission/Work/CFTLib/`) (see also the
docstring of the previous version of this file, kept in the git history):

* `NK.CFTLib.Existence.exists_ideleArtinMap_of_arl` — from `hARL` alone: a modulus `m`, a congruence
  subgroup `U` of modulus `m` with adjustment `𝕀_K = U·Kˣ`, and `art : 𝕀 K →* Gal(L/K)` killing the
  principal idèles and the norms, surjective, and with `art (ideleOfPrime K 𝔭) = Frob_𝔭` for `𝔭 ∤ (m)`;
* `NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup` /
  `NK.CFTLib.Existence.exists_artinIso_of_ideleArtin` — the idèlic Artin map descends to the
  reciprocity isomorphism `C_K ⧸ N_{L/K}C_L ≃* Gal(L/K)`;
* `NK.CFTLib.Arl.closure_isFrobAtPrime_of_notMem_eq_top` — the Frobenius elements away from a finite
  set generate `Gal(L/K)`;
* local class field theory: the local Artin map `θ_v` with kernel the local norm group
  (`Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute`,
  `NK.LocalReciprocity.*`).

The cleanest route to the product formula from `hARL` is the classical *Artin's trick*: the modulus
`m` may be chosen freely large, and one compares `art` with `∏_v θ_v` on a generating set of
`𝕀_K/K^×N𝕀_L`: both kill the norms, both send `ideleOfPrime K 𝔭` to `Frob_𝔭` for `𝔭 ∤ m`, and both
kill the principal idèles once Hilbert reciprocity is known for the cyclotomic extension `K(ζ_n)/K`.
-/

section OnePlaceComparison

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The local comparison at a prime admitting no congruence condition.**

If the one-place idèle `onePlace 𝔭 a` already lies in the congruence subgroup `U` (which is the case
for every `𝔭 ∤ (m)`, since the congruence subgroup of this development imposes conditions only at
the primes dividing `(m)` and at the real places), then the idèlic Artin map takes it to the Artin
symbol of its associated ideal: the adjustment `adjust U hadj (onePlace 𝔭 a)` is a congruence unit, so
its Artin symbol is trivial (`hstep`, the Crux of the construction, which is supplied by
`NK.CFTLib.Arl.artinSym_spanSingleton_eq_one` from the ideal-theoretic reciprocity law).

This is the first half of the classical *Artin's trick* comparison `art = ∏_v θ_v`: together with the
computation of the ideal of a one-place idèle (and the unramified Frobenius normalisation) it gives
Hilbert reciprocity at every finite prime not dividing the modulus. -/
theorem ideleArtin_onePlace_eq_artinSym_idealOf
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    (hstep : ∀ b : Kˣ, NK.GlobalCFT.Idele.principalIdele K b ∈ U →
      NK.CFTLib.Arl.artinSym hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (b : K)) = 1)
    (𝔭 : HeightOneSpectrum (𝓞 K))
    (a : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ)
    (hUone : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a ∈ U) :
    NK.CFTLib.Arl.ideleArtin hcomm U hadj
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a)
      = NK.CFTLib.Arl.artinSym hcomm
          (NK.GlobalCFT.Idele.idealOf
            (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a)) := by
  classical
  show NK.CFTLib.Arl.artinSym hcomm (NK.GlobalCFT.Idele.idealOf
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a *
        NK.GlobalCFT.Idele.principalIdele K (NK.CFTLib.Arl.adjust U hadj
          (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a)))) = _
  have hb : NK.GlobalCFT.Idele.principalIdele K
      (NK.CFTLib.Arl.adjust U hadj
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a)) ∈ U := by
    have h1 := U.mul_mem (U.inv_mem hUone)
      (NK.CFTLib.Arl.adjust_spec U hadj
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a))
    simpa using h1
  rw [NK.GlobalCFT.Idele.idealOf_mul, NK.GlobalCFT.Idele.idealOf_principalIdele,
    NK.CFTLib.Arl.artinSym_mul hcomm (NK.GlobalCFT.Idele.idealOf_ne_zero _)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)), hstep _ hb, mul_one]

/-- **The same comparison in the setting of the reciprocity law**: for the congruence subgroup `U`
of a modulus `m` and the primes `𝔭 ∤ (m)`, the one-place idèle lies in `U` (there is no congruence
condition at `𝔭`), so the previous comparison applies with the Crux `hstep` supplied by
`NK.CFTLib.Arl.artinSym_spanSingleton_eq_one`. -/
theorem ideleArtin_onePlace_eq_artinSym_idealOf_of_notMem
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1)
    (hprinc : ∀ (a : 𝓞 K), a - 1 ∈ Ideal.span {(m : 𝓞 K)} →
      (∀ φ : K →+* ℝ, 0 < φ ((a : K))) →
      ∀ (s : Finset (HeightOneSpectrum (𝓞 K)))
        (e : HeightOneSpectrum (𝓞 K) → ℕ)
        (σ : HeightOneSpectrum (𝓞 K) → Gal(L/K)),
        (∀ p ∈ s, (m : 𝓞 K) ∉ p.asIdeal) →
        Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p →
        (∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (L := L) p (σ p)) →
        (s.toList.map (fun p => σ p ^ e p)).prod = 1)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (a : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ)
    (hUone : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a ∈ U) :
    NK.CFTLib.Arl.ideleArtin hcomm U hadj
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a)
      = NK.CFTLib.Arl.artinSym hcomm
          (NK.GlobalCFT.Idele.idealOf
            (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) a)) := by
  refine ideleArtin_onePlace_eq_artinSym_idealOf hcomm U hadj (fun b hb => ?_) 𝔭 a hUone
  exact NK.CFTLib.Arl.artinSym_spanSingleton_eq_one hcomm m hm hram hprinc b
    ((hU.2 b).mp hb).1 ((hU.2 b).mp hb).2

end OnePlaceComparison

section ReductionAux

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The inverse of `onePlace v a` has value `a⁻¹` at `v` (inlined from
`NK.CFTLib.IdeleHasse.inv_onePlace_apply_self`, so that this file is independent of files under
construction elsewhere in the workspace). -/
theorem inv_onePlace_apply_self (v : NK.GlobalCFT.Place K)
    (a : (NK.GlobalCFT.Place.localField K v)ˣ) :
    ((NK.HassePrinciple.onePlace v a)⁻¹ : NK.GlobalCFT.Idele K) v = a⁻¹ := by
  rw [NK.GlobalCFT.Idele.inv_apply, NK.HassePrinciple.onePlace_apply_self]

/-- The inverse of `onePlace v a` has value `1` away from `v` (inlined). -/
theorem inv_onePlace_apply_ne {V v : NK.GlobalCFT.Place K} (h : V ≠ v)
    (a : (NK.GlobalCFT.Place.localField K v)ˣ) :
    ((NK.HassePrinciple.onePlace v a)⁻¹ : NK.GlobalCFT.Idele K) V = 1 := by
  rw [NK.GlobalCFT.Idele.inv_apply, NK.HassePrinciple.onePlace_apply_ne h, inv_one]

/-- **The reduction of the target to the single-place statement** (inlined from
`NK.CFTLib.IdeleHasse.hasseNorm_onePlace_cyclic_of_onePlace`, which is proved on disk; inlined so
that this file does not depend on a file under construction elsewhere). -/
theorem hasseNorm_onePlace_cyclic_of_onePlace'
    [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L))
    (hQ : ∀ {v : NK.GlobalCFT.Place K} {a : (NK.GlobalCFT.Place.localField K v)ˣ},
      NK.HassePrinciple.onePlace v a ∈
        NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K →
        NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L)
    {x : Kˣ} {v₀ : NK.GlobalCFT.Place K}
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ → ∃ y : NK.GlobalCFT.Idele L,
      NK.GlobalCFT.Idele.principalIdele K x v = NK.GlobalCFT.Idele.normIdeleFun K L y v) :
    ∃ b : Lˣ, NK.GlobalCFT.Idele.principalIdele K x =
      NK.GlobalCFT.Idele.normIdeleFun K L (NK.GlobalCFT.Idele.principalIdele L b) := by
  classical
  set z : NK.GlobalCFT.Idele K := NK.GlobalCFT.Idele.principalIdele K x *
    (NK.HassePrinciple.onePlace v₀ ((NK.GlobalCFT.Idele.principalIdele K x) v₀))⁻¹ with hz
  have hz_apply_self : z v₀ = 1 := by
    rw [hz, NK.GlobalCFT.Idele.mul_apply, inv_onePlace_apply_self, mul_inv_cancel]
  have hz_apply_ne : ∀ V : NK.GlobalCFT.Place K, V ≠ v₀ →
      z V = (NK.GlobalCFT.Idele.principalIdele K x) V := by
    intro V hV
    rw [hz, NK.GlobalCFT.Idele.mul_apply, inv_onePlace_apply_ne hV, mul_one]
  have hzmem : z ∈ NK.GlobalCFT.Idele.normImage K L := by
    rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm]
    intro V
    by_cases hV : V = v₀
    · subst hV
      exact ⟨1, by rw [hz_apply_self, NK.GlobalCFT.Idele.normIdeleFun_one_apply]⟩
    · obtain ⟨y, hy⟩ := h V hV
      exact ⟨y, by rw [hz_apply_ne V hV]; exact hy⟩
  have hmem : NK.HassePrinciple.onePlace v₀ ((NK.GlobalCFT.Idele.principalIdele K x) v₀) ∈
      NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K := by
    have h1 : NK.HassePrinciple.onePlace v₀ ((NK.GlobalCFT.Idele.principalIdele K x) v₀)
        = z⁻¹ * NK.GlobalCFT.Idele.principalIdele K x := by
      rw [hz, mul_inv_rev, inv_inv]
      group
    rw [h1]
    exact Subgroup.mul_mem_sup (inv_mem hzmem)
      ((NK.GlobalCFT.Idele.mem_principalSubgroup).mpr ⟨x, rfl⟩)
  obtain ⟨y, hy⟩ := (NK.GlobalCFT.Idele.mem_normImage).mp (hQ hmem)
  have hloc : ∀ v : NK.GlobalCFT.Place K, ∃ y : NK.GlobalCFT.Idele L,
      NK.GlobalCFT.Idele.principalIdele K x v = NK.GlobalCFT.Idele.normIdeleFun K L y v := by
    intro v
    by_cases hv : v = v₀
    · subst hv
      refine ⟨y, ?_⟩
      rw [← NK.HassePrinciple.onePlace_apply_self v
        ((NK.GlobalCFT.Idele.principalIdele K x) v)]
      exact hy v
    · exact h v hv
  exact NK.GlobalCFTdeep.hasseNorm_form_universe x
    ((NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
      (NK.GlobalCFT.Idele.principalIdele K x)).mpr hloc)

end ReductionAux

section Reduction

/-- **The single place statement of Hasse's norm principle** (Milne, *CFT*, V.5.3(a)/VII.8.1(a)):
if the one-place idèle `onePlace v a` lies in `Kˣ · N_{L/K}𝕀_L`, then it lies in `N_{L/K}𝕀_L`,
i.e. `a` is a local norm.

This is *the* arithmetic input (Hilbert's reciprocity law `∑_v inv_v = 0`).  It is deliberately
isolated here: the target theorem is a formal consequence of it (see below), and it is the natural
form in which the classical proofs deliver the product formula.

The statement carries the hypothesis `hARL` (the ideal-theoretic reciprocity law), which is the
intended input, but the proof below does not use it: the statement is *true* for every cyclic
`L/K`, and it is now available on disk unconditionally as
`NK.CFTLib.IdeleHasse.localFaithful_onePlace` (proved, `sorry`-free, in
`Submission/Work/CFTLib/IdeleHasse/localFaithful_onePlace.lean`), proved from the one-place form of
Hilbert reciprocity `NK.CFTLib.IdeleHasse.Descent.hilbertReciprocityOnePlace`.  We simply invoke
it, so `hARL` is redundant here. -/
theorem localFaithful_onePlace_of_arl (hARL : NK.CFTLib.ArtinReciprocityIdeal)
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L))
    {v : NK.GlobalCFT.Place K} {a : (NK.GlobalCFT.Place.localField K v)ˣ}
    (h : NK.HassePrinciple.onePlace v a ∈
      NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K) :
    NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L :=
  NK.CFTLib.IdeleHasse.localFaithful_onePlace hcyc h

/-- **Hasse's norm principle with one place omitted**: a global element which is a local norm at
every place except possibly `v₀` is a global idèlic norm (Milne, *CFT*, VII.8.1(a)).

The proof is the (formal, sorry-free) reduction
`NK.CFTLib.IdeleHasse.hasseNorm_onePlace_cyclic_of_onePlace` together with the local faithfulness
of the components of the global Artin map at the one omitted place. -/
theorem localNormImage_of_forall_ne_of_arl (hARL : NK.CFTLib.ArtinReciprocityIdeal)
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L))
    {x : Kˣ} {v₀ : NK.GlobalCFT.Place K}
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ → ∃ y : NK.GlobalCFT.Idele L,
      NK.GlobalCFT.Idele.principalIdele K x v = NK.GlobalCFT.Idele.normIdeleFun K L y v) :
    NK.GlobalCFT.Idele.principalIdele K x ∈ NK.GlobalCFT.Idele.normImage K L := by
  obtain ⟨b, hb⟩ :=
    hasseNorm_onePlace_cyclic_of_onePlace' (K := K) (L := L) hcyc
      (fun {v} {a} hh => localFaithful_onePlace_of_arl hARL hcyc hh) h
  exact (NK.GlobalCFT.Idele.mem_normImage).mpr
    ⟨NK.GlobalCFT.Idele.principalIdele L b, fun v => congrFun hb v⟩

end Reduction

end NK.CFTLib.Existence
