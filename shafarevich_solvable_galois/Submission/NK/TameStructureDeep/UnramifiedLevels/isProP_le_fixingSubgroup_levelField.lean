/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Every normal pro-`p` subgroup fixes all the prime-to-`p` unramified levels

Let `K` be a number field, `𝔭` a finite place, `κ = K_𝔭` its `𝔭`-adic completion, `K'` a
separable closure of `κ`, `q = residueCard K 𝔭` the residue cardinality and `p` the residue
characteristic.  For every `d ≠ 0` the *level* `d` of `κ^ur = κ(μ_{p'})` is

  `levelField 𝔭 d = κ⟮ζ_{q ^ d - 1}⟯`,

a cyclic extension of `κ` of degree `d` (`Gal(κ⟮ζ_{q^d-1}⟯/κ) ≅ ℤ/d`,
`NK.TameStructureDeep.Degree.levelEquiv`).

**The theorem.**  If `N ⊴ Gal(K'/κ)` is pro-`p` in the finite-quotient sense
(`NK.LocalTame.IsProP`) and `d` is prime to `p`, then `N` fixes `levelField 𝔭 d`
pointwise.

This is the "prime-to-`p` half" of the statement that the wild inertia lies in the inertia
(NSW (7.5.7) Corollary): for every prime `ℓ ≠ p` and every `n ≥ 1`, a normal pro-`p` subgroup `N`
acts trivially on `κ^{ur,ℓ^n}`, i.e. its image in `Gal(κ^ur/κ) ≅ Ẑ` lies in `ℓ^n Ẑ`.

*Proof.*  Restriction to the level gives `Gal(K'/κ) →* Gal(κ⟮ζ_{q^d-1}⟯/κ) ≅ ℤ/d`; its kernel is
the fixing subgroup of the level.  The image of `N` in `ℤ/d` is a quotient of `N` by the kernel of
the restricted map, which has finite index because `Gal(κ⟮ζ_{q^d-1}⟯/κ)` is finite; hence, `N`
being pro-`p`, that image has `p`-power order `p ^ k`.  By Lagrange it divides `d`, and `p ^ k`
prime to `d` forces `p ^ k = 1`: the image is trivial, i.e. `N` lies in the kernel.  The
group-theoretic step is isolated as `eq_one_of_isProP_of_coprime_card`.

The hypothesis `d` prime to `p` cannot be dropped: the `p`-part of `Gal(κ^ur/κ) = Ẑ` is *not*
killed by pro-`p` subgroups in general (the wild inertia has a nontrivial pro-`p` quotient of the
unramified `ℤ_p`-tower).
-/
import Mathlib
import Submission.NK.TameStructureDeep.Degree.unramifiedLevels
import Submission.NK.TameStructureDeep.Degree.orderOf_residueCard_pow_sub_one
import Submission.NK.TameStructureDeep.Degree.galoisGroup_adjoin_primitiveRoot_mulEquiv
import Submission.NK.TameStructureDeep.Degree.galoisGroup_unramifiedClosure_mulEquiv
import Submission.NK.TameStructureDeep.Unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.TameStructureDeep.UnramifiedLevels

/-- **A homomorphism from a pro-`p` group to a finite group of order prime to `p` is trivial.**

Indeed the kernel of `f` has finite index, so `IsProP` makes its index `p ^ k`; the index of the
kernel is the order of the image, which by Lagrange divides `Nat.card A`, a number prime to `p`;
so `p ^ k = 1` and the kernel is everything. -/
theorem eq_one_of_isProP_of_coprime_card {M A : Type*} [Group M] [Group A] [Finite A]
    {p : ℕ} (hM : NK.LocalTame.IsProP p M) (f : M →* A) (hcop : Nat.Coprime p (Nat.card A)) :
    f = 1 := by
  -- the kernel has finite index because its index is the (finite) order of the image
  have hfin : f.ker.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_ker]
    haveI : Finite ↥f.range := Finite.of_injective Subtype.val Subtype.val_injective
    exact Nat.card_pos.ne'
  -- pro-`p`-ness turns the index into a power of `p`
  obtain ⟨k, hk⟩ := hM f.ker hfin
  have hcard : Nat.card ↥f.range = p ^ k := by rw [← Subgroup.index_ker f, hk]
  -- Lagrange: the order of the image divides `Nat.card A`
  have hdvd : Nat.card ↥f.range ∣ Nat.card A := Subgroup.card_subgroup_dvd_card _
  rw [hcard] at hdvd
  -- a power of `p` dividing a number prime to `p` is `1`
  have h1 : p ^ k = 1 := (hcop.pow_left k).eq_one_of_dvd hdvd
  exact MonoidHom.ker_eq_top_iff.mp (Subgroup.index_eq_one.mp (hk.trans h1))

/-- **Every normal pro-`p` subgroup of `Gal(K'/κ)` fixes the unramified level of degree `d`**,
for `d` prime to `p`.  See the module documentation for the proof and for the discussion of the
hypotheses. -/
theorem isProP_le_fixingSubgroup_levelField {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {p d : ℕ} (hp : p.Prime) (hd0 : d ≠ 0) (hcop : Nat.Coprime d p)
    {N : Subgroup (Gal(K'/𝔭.adicCompletion K))} (hN : N.Normal)
    (hpro : NK.LocalTame.IsProP p ↥N) :
    N ≤ (NK.TameStructureDeep.Degree.levelField (K := K) (K' := K') 𝔭 d).fixingSubgroup := by
  classical
  haveI : NeZero d := ⟨hd0⟩
  set L := NK.TameStructureDeep.Degree.levelField (K := K) (K' := K') 𝔭 d with hL
  -- the level `d` is cyclic of degree `d` over `κ`
  have hcardGalois : Nat.card (Gal(↥L / 𝔭.adicCompletion K)) = d := by
    have h := Nat.card_congr
      (NK.TameStructureDeep.Degree.levelEquiv (K := K) (K' := K') 𝔭 d hd0).toEquiv
    rw [h.symm]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  haveI : Fintype (Gal(↥L / 𝔭.adicCompletion K)) :=
    Fintype.ofEquiv (Multiplicative (ZMod d))
      (NK.TameStructureDeep.Degree.levelEquiv (K := K) (K' := K') 𝔭 d hd0).toEquiv
  -- restriction to the level, restricted to `N`
  let ψ : ↥N →* Gal(↥L / 𝔭.adicCompletion K) :=
    (AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) ↥L).comp N.subtype
  -- `N` is pro-`p` and `Gal(κ⟮ζ_{q^d-1}⟯/κ) ≅ ℤ/d` has order prime to `p`
  have hψ : ψ = 1 := by
    refine eq_one_of_isProP_of_coprime_card hpro ψ ?_
    rw [hcardGalois]
    exact hcop.symm
  -- hence every `σ ∈ N` restricts to `1` on the level, i.e. fixes it pointwise
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1 : ((AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) ↥L) σ) = 1 := by
    have h2 : ψ ⟨σ, hσ⟩ = 1 := by
      have h3 := congrArg (fun g => g ⟨σ, hσ⟩) hψ
      simpa using h3
    simpa [ψ] using h2
  have h3 : ((AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) ↥L) σ) ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [h1]; rfl
  have h4 := congrArg Subtype.val h3
  rw [AlgEquiv.restrictNormalHom_apply] at h4
  exact h4

end NK.TameStructureDeep.UnramifiedLevels
