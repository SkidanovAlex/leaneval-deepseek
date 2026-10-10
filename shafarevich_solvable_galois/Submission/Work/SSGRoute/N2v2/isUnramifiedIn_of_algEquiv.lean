import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.HeckeL.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `IsUnramifiedIn` is invariant under a `K`-algebra isomorphism of the field

`NK.HeckeL.IsUnramifiedIn Q` (for `Q` a finite place of `K`) says that every prime `𝔮` of `L`
lying over `Q` has ramification index `1` over `K`.  If `e : L₁ ≃ₐ[K] L₂`, then `e` restricts to
an isomorphism `𝓞 L₁ ≃ₐ[𝓞 K] 𝓞 L₂` of rings of integers, whence a bijection
`𝔮 ↦ 𝔮.comap e` between primes over `Q`, and the ramification index is unchanged because it is
detected by the exponent of `𝔮` in `Q·𝓞 L` (equivalently, by the ramification index
`ramificationIdx' Q 𝔮` intrinsic to the ring extension, which visibly commutes with `comap`
along an algebra isomorphism — `Ideal.ramificationIdx'_comap_eq`).
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.N2v2

open NumberField IsDedekindDomain

/-- Forward direction of the transport: if `Q` is unramified in `L₁/K` then it is unramified in
`L₂/K`, the primes over `Q` being matched by `comap` along `NumberField.RingOfIntegers.mapAlgEquiv`. -/
private theorem isUnramifiedIn_of_algEquiv_forward {K L₁ L₂ : Type} [Field K] [NumberField K]
    [Field L₁] [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    (e : L₁ ≃ₐ[K] L₂) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L₁) Q →
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L₂) Q := by
  intro h 𝔮 h𝔮
  -- The induced isomorphism of rings of integers.
  let E : (𝓞 L₁) ≃ₐ[𝓞 K] (𝓞 L₂) := NumberField.RingOfIntegers.mapAlgEquiv e
  -- The prime of `L₁` matched with `𝔮` by `E`.
  let Q₁ : Ideal (𝓞 L₁) := 𝔮.asIdeal.comap (E : 𝓞 L₁ →+* 𝓞 L₂)
  haveI hQ₁p : Q₁.IsPrime :=
    Ideal.IsPrime.comap (f := (E : 𝓞 L₁ →+* 𝓞 L₂)) (K := 𝔮.asIdeal)
  have hQ₁ne : Q₁ ≠ ⊥ := by
    intro hbot
    exact 𝔮.ne_bot (Ideal.eq_bot_of_comap_eq_bot' (f := (E : 𝓞 L₁ →+* 𝓞 L₂)) E.surjective hbot)
  haveI h𝔮lies : 𝔮.asIdeal.LiesOver Q.asIdeal := h𝔮
  haveI hQ₁lies : Q₁.LiesOver Q.asIdeal := by
    rw [show Q₁ = (𝔮.asIdeal.comap (E : 𝓞 L₁ →+* 𝓞 L₂)) from rfl]
    exact Ideal.comap_liesOver 𝔮.asIdeal Q.asIdeal (E : 𝓞 L₁ →ₐ[𝓞 K] 𝓞 L₂)
  have hunr : Q₁.ramificationIdx (𝓞 K) = 1 :=
    h ⟨Q₁, hQ₁p, hQ₁ne⟩ hQ₁lies
  -- The ramification index of the prime over `Q` only depends on the underlying prime of `𝓞 L`
  -- (via `ramificationIdx'`), which is transported by `comap` along `E`.
  have h12 : Q.asIdeal.ramificationIdx' 𝔮.asIdeal = Q₁.ramificationIdx (𝓞 K) := by
    rw [← Ideal.ramificationIdx'_comap_eq (p := Q.asIdeal) (e := E) (P := 𝔮.asIdeal)]
    exact Ideal.ramificationIdx'_eq_ramificationIdx Q.asIdeal Q₁ Q.ne_bot
  have h2 : Q.asIdeal.ramificationIdx' 𝔮.asIdeal = 𝔮.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx'_eq_ramificationIdx Q.asIdeal 𝔮.asIdeal Q.ne_bot
  rw [← h2, h12, hunr]

theorem isUnramifiedIn_of_algEquiv {K L₁ L₂ : Type} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    (e : L₁ ≃ₐ[K] L₂) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L₁) Q ↔
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L₂) Q :=
  ⟨isUnramifiedIn_of_algEquiv_forward e Q, isUnramifiedIn_of_algEquiv_forward e.symm Q⟩

end Work.SSGRoute.N2v2
