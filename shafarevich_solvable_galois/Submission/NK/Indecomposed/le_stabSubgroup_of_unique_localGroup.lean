/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neukirch's "the prime is indecomposed" step: uniqueness of the local group forces
`H ≤ D_A`

This is the group-theoretic core of Neukirch's local characterisation of decomposition groups
(Neukirch, Invent. Math. **6** (1969), Theorem 1; CoNF XII (12.1.3)–(12.1.9); A. Ivanov,
arXiv:1309.2801, Corollary `FKSnormalizerproperty`), in the form in which the assembly of
`Submission/Work/Indecomposed/` consumes it.

Let `K` be a number field with separable closure `K'`, `𝔭` a finite prime of `K`, and let `H` be any
subgroup of `G = Gal(K'/K)`.  Suppose that, among the places `A` of `K'` above `𝔭`, all the
*non-trivial* local groups `H ⊓ D_A` coincide:

`huniq : H ⊓ D_A ≠ ⊥ → H ⊓ D_{A'} ≠ ⊥ → H ⊓ D_A = H ⊓ D_{A'}`.

Then `H` is contained in the decomposition group of `A₀`, for any place `A₀` above `𝔭` whose local
group is non-trivial:

`NK.Indecomposed.le_stabSubgroup_of_unique_localGroup`.

## The argument

Fix a place `A₀` over `𝔭` with `N := H ⊓ D_{A₀} ≠ ⊥`.  We show that `H` normalises `N`; then the
FKS normalizer property `NK.LocalDecomposition.normalizer_le_of_ne_bot` (a non-trivial subgroup of
a decomposition group has its normalizer inside that decomposition group) gives `H ≤ N_G(N) ≤ D_{A₀}`.

So let `h ∈ H` and `x ∈ N`.  Since `x` fixes `A₀`, the conjugate `h x h⁻¹` fixes `h • A₀`, i.e.
`h x h⁻¹ ∈ H ⊓ D_{h • A₀}`; and `h • A₀` is again a place over `𝔭`
(`NK.LocalDecomposition.comap_smul`).  If `x = 1` there is nothing to prove.  Otherwise
`h x h⁻¹ ≠ 1` is a witness for `H ⊓ D_{h • A₀} ≠ ⊥`, so `huniq` applied to the places `A₀` and
`h • A₀` gives `H ⊓ D_{h • A₀} = H ⊓ D_{A₀} = N`, and therefore `h x h⁻¹ ∈ N`.

Neither the arithmetic meaning of the places over `𝔭` (beyond `comap` being preserved by the Galois
action) nor the cohomological input enters: this is the purely group-theoretic passage from the
uniqueness of the non-trivial local group to the containment `H ≤ D_A`.
-/
import Mathlib
import Submission.NK.LocalDecomposition.Basic
import Submission.NK.HasseTwist.Localisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace NK.Indecomposed

universe u

/-- **Neukirch's "the prime is indecomposed" step (uniqueness form).**

If all the non-trivial local groups `H ⊓ D_A` of `H` over the finite prime `𝔭` coincide, then `H`
itself is contained in the decomposition group of any place `A₀` over `𝔭` at which the local group
is non-trivial.

The proof shows that `H` normalises `N = H ⊓ D_{A₀} ≠ ⊥`: for `h ∈ H` and `x ∈ N`, the conjugate
`h x h⁻¹` lies in `H ⊓ D_{h • A₀}`, and `huniq` identifies `H ⊓ D_{h • A₀}` with `H ⊓ D_{A₀}` (using
`h x h⁻¹ ≠ 1` as a witness when `x ≠ 1`).  The FKS normalizer property
`NK.LocalDecomposition.normalizer_le_of_ne_bot` then gives `H ≤ N_G(N) ≤ D_{A₀}`. -/
theorem le_stabSubgroup_of_unique_localGroup {K K' : Type u} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A₀ : NK.HasseTwist.PlacesOverPrime K K' 𝔭) (H : Subgroup Gal(K'/K))
    (hVne : H ⊓ NK.BrauerTwist.stabSubgroup A₀.1 ≠ ⊥)
    (huniq : ∀ A A' : NK.HasseTwist.PlacesOverPrime K K' 𝔭,
      H ⊓ NK.BrauerTwist.stabSubgroup A.1 ≠ ⊥ →
      H ⊓ NK.BrauerTwist.stabSubgroup A'.1 ≠ ⊥ →
      H ⊓ NK.BrauerTwist.stabSubgroup A.1 = H ⊓ NK.BrauerTwist.stabSubgroup A'.1) :
    H ≤ NK.BrauerTwist.stabSubgroup A₀.1 := by
  classical
  -- the place `A₀` lies over a finite prime, so its valuation ring is not everything
  have hA : A₀.1.comap (algebraMap K K') ≠ ⊤ := by
    rw [A₀.2]
    exact NK.HasseTwist.isDedekindDomain_valuationSubringAtPrime_ne_top 𝔭
  -- it suffices to see `H ≤ N_G(H ⊓ D_{A₀})`: the normalizer of a non-trivial subgroup of a
  -- decomposition group is contained in that decomposition group (FKS)
  refine le_trans ?_ (NK.LocalDecomposition.normalizer_le_of_ne_bot A₀.1 hA
    (H ⊓ NK.BrauerTwist.stabSubgroup A₀.1) hVne inf_le_right)
  rw [Subgroup.le_normalizer_iff]
  intro h hh x hx
  have hmemH : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh)
  -- the conjugate of `A₀` by `h` is again a place over `𝔭`
  let A' : NK.HasseTwist.PlacesOverPrime K K' 𝔭 :=
    ⟨h • A₀.1, by rw [NK.LocalDecomposition.comap_smul]; exact A₀.2⟩
  -- `x` fixes `A₀`, hence `h * x * h⁻¹` fixes `h • A₀`
  have hmemStab' : h * x * h⁻¹ ∈ NK.BrauerTwist.stabSubgroup A'.1 := by
    have hxstab : x • A₀.1 = A₀.1 := MulAction.mem_stabilizer_iff.mp hx.2
    rw [MulAction.mem_stabilizer_iff]
    show (h * x * h⁻¹) • (h • A₀.1) = h • A₀.1
    rw [← mul_smul, show (h * x * h⁻¹) * h = h * x by group, mul_smul, hxstab]
  by_cases hx1 : x = 1
  · -- then `h * x * h⁻¹ = 1` is in `H ⊓ D_{A₀}` for trivial reasons
    subst hx1
    rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · -- otherwise `h * x * h⁻¹ ≠ 1` witnesses that the local group at `h • A₀` is non-trivial,
    -- and the uniqueness hypothesis identifies it with `H ⊓ D_{A₀}`
    have hne1 : H ⊓ NK.BrauerTwist.stabSubgroup A'.1 ≠ ⊥ := by
      intro hbot
      have hmem : h * x * h⁻¹ ∈ (⊥ : Subgroup Gal(K'/K)) := by
        rw [← hbot]
        exact ⟨hmemH, hmemStab'⟩
      rw [Subgroup.mem_bot] at hmem
      exact hx1 (mul_left_cancel (mul_right_cancel (by rw [hmem]; simp)))
    rw [huniq A₀ A' hVne hne1]
    exact ⟨hmemH, hmemStab'⟩

end NK.Indecomposed
