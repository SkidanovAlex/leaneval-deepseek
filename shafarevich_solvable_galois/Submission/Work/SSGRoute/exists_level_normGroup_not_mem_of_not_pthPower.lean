import Mathlib
import Submission.Work.SSGRoute.exists_level_normGroup_eq_of_index_prime
import Submission.Work.SSGRoute.LocalCFTAggregatorDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Separation of a non-`p`-th power by a norm group of a degree-`p` extension

For a number field `K`, a finite place `Q` of `K`, with completion `F = Q.adicCompletion K`, and a
prime `p`, the local norm-group correspondence (`exists_level_normGroup_eq_of_index_prime`) says
that *every* subgroup `U ≤ Fˣ` of index `p` is the norm group `N_{E/F} Eˣ` of a finite Galois
extension `E/F` of degree `p`.  Hence, to exhibit a degree-`p` extension `E/F` whose norm group
avoids a prescribed unit `a ∈ Fˣ`, it suffices to produce *some* subgroup of `Fˣ` of index `p` not
containing `a`.

The latter is a purely group-theoretic statement, proved here for an arbitrary abelian group:
if `a` is not a `p`-th power, then `a` lies outside a subgroup of index `p`.  Indeed `A / A^p` is
an elementary abelian `p`-group, i.e. a vector space over `𝔽_p = ZMod p`, and the class of `a` is
nonzero; a nonzero vector of a vector space has a linear functional equal to `1` on it
(`Module.Projective.exists_dual_eq_one`), and the kernel of the resulting character
`A →* Multiplicative (ZMod p)` is a subgroup of index `p` on which `a` is nontrivial.

This is the "existence" half of the local Kummer/reciprocity bookkeeping: combined with
`normGroup_eq_iff`, it is the statement that a unit which is not a norm from the cyclic extension
of degree `p` can be *witnessed* by such an extension.
-/

namespace Work.SSGRoute

/-- **Separation of a non-`p`-th power by an index-`p` subgroup.**

Let `A` be a commutative group, `p` a prime and `a : A` an element which is not a `p`-th power.
Then there is a subgroup `U ≤ A` of index exactly `p` with `a ∉ U`.

The group ``A ⧸ A^p`` has exponent `p`, hence is a vector space over `𝔽_p`; the image of `a` is a
nonzero vector, so there is an `𝔽_p`-linear functional `f` with `f a = 1`
(`Module.Projective.exists_dual_eq_one`).  The multiplicative form `χ` of `f` on `A` is a
surjective homomorphism onto the group `Multiplicative (ZMod p)` of order `p`, and `χ.ker` is the
required subgroup (of index `Nat.card (Multiplicative (ZMod p)) = p`), on which `a` is nontrivial
because `χ a ≠ 1`. -/
theorem exists_subgroup_index_prime_notMem_of_not_pow_eq {A : Type*} [CommGroup A]
    (p : ℕ) [Fact p.Prime] (a : A) (ha : ∀ b : A, b ^ p ≠ a) :
    ∃ U : Subgroup A, U.index = p ∧ a ∉ U := by
  classical
  -- the subgroup of `p`-th powers, and the fact that `a` is not in it
  let N : Subgroup A := (powMonoidHom p).range
  have hNn : N.Normal := Subgroup.normal_of_isMulCommutative N
  have haN : a ∉ N := by
    intro h
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp h
    exact ha b (by rwa [powMonoidHom_apply] at hb)
  -- the quotient `A ⧸ A^p` has exponent `p`
  have hexp : ∀ v : A ⧸ N, v ^ p = 1 := by
    intro v
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N v
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨g, by rw [powMonoidHom_apply]⟩
  -- hence it is an `𝔽_p`-vector space
  have hmod : Module (ZMod p) (Additive (A ⧸ N)) :=
    AddCommGroup.zmodModule (n := p) (fun x => by
      have hx : x = Additive.ofMul x.toMul := (ofMul_toMul x).symm
      rw [hx, ← ofMul_pow, ofMul_eq_zero]
      exact hexp x.toMul)
  -- the class of `a` is a nonzero vector
  have hā : Additive.ofMul ((QuotientGroup.mk' N) a) ≠ (0 : Additive (A ⧸ N)) := by
    intro h
    refine haN ?_
    have h1 : (QuotientGroup.mk' N) a = 1 := ofMul_eq_zero.mp h
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hfree : Module.Free (ZMod p) (Additive (A ⧸ N)) := Module.Free.of_divisionRing (ZMod p) _
  -- a linear functional taking the value `1` on it
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod p) hā
  -- its multiplicative form
  let χ : A →* Multiplicative (ZMod p) :=
    { toFun := fun x => Multiplicative.ofAdd (f (Additive.ofMul ((QuotientGroup.mk' N) x)))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, ofMul_mul, map_add, ofAdd_add] }
  have hχa : χ a ≠ 1 := by
    intro h
    have h1 : f (Additive.ofMul ((QuotientGroup.mk' N) a)) = 0 := by
      simpa [χ] using h
    rw [hf] at h1
    exact one_ne_zero h1
  -- `χ` is surjective, since it takes the value `1` on the nonzero class of `a`
  have hfr : f.range = ⊤ := by
    have h1 : (1 : ZMod p) ∈ f.range := ⟨_, hf⟩
    rw [Submodule.eq_top_iff']
    intro c
    simpa using f.range.smul_mem c h1
  have hχsurj : Function.Surjective χ := by
    intro y
    obtain ⟨c, rfl⟩ : ∃ c : ZMod p, Multiplicative.ofAdd c = y := ⟨y.toAdd, ofAdd_toAdd y⟩
    have hc : c ∈ f.range := by rw [hfr]; exact Submodule.mem_top
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hc
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N x.toMul
    exact ⟨g, by
      show Multiplicative.ofAdd (f (Additive.ofMul ((QuotientGroup.mk' N) g))) = Multiplicative.ofAdd c
      rw [hg, ofMul_toMul, hx]⟩
  -- the kernel of `χ` has index `p` and misses `a`
  refine ⟨χ.ker, ?_, ?_⟩
  · rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective χ hχsurj).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  · intro h
    exact hχa h

/-- **A unit which is not a `p`-th power is not a norm from some degree-`p` extension.**

For a number field `K`, a finite place `Q` of `K` and a prime `p`: given a unit
`a ∈ (Q.adicCompletion K)ˣ` which is not a `p`-th power, there is a finite Galois extension
`E / Q.adicCompletion K` of degree `p` (i.e. `Nat.card (E ≃ₐ[F] E) = p`) whose norm group does not
contain `a`.

Route: `exists_subgroup_index_prime_notMem_of_not_pow_eq` produces a subgroup `U ≤ Fˣ` of index `p`
with `a ∉ U`; the local norm-group correspondence
(`exists_level_normGroup_eq_of_index_prime`, resting on local class field theory) realises `U` as
`N_{E/F} Eˣ` for a finite Galois `E/F` of degree `p`; then `a ∉ N_{E/F} Eˣ` follows. -/
theorem exists_level_normGroup_not_mem_of_not_pthPower {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (p : ℕ) [Fact p.Prime] (a : (Q.adicCompletion K)ˣ)
    (ha : ∀ b : (Q.adicCompletion K)ˣ, b ^ p ≠ a) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra (Q.adicCompletion K) E)
      (_ : FiniteDimensional (Q.adicCompletion K) E) (_ : IsGalois (Q.adicCompletion K) E),
      Nat.card (E ≃ₐ[Q.adicCompletion K] E) = p ∧
        a ∉ NK.LocalReciprocity.normGroup (Q.adicCompletion K) E := by
  obtain ⟨U, hUidx, haU⟩ := exists_subgroup_index_prime_notMem_of_not_pow_eq (p := p) a ha
  obtain ⟨E, hF, hA, hfd, hgal, hcard, hnorm⟩ :=
    exists_level_normGroup_eq_of_index_prime Q p U hUidx
  exact ⟨E, hF, hA, hfd, hgal, hcard, by rw [hnorm]; exact haU⟩

end Work.SSGRoute
