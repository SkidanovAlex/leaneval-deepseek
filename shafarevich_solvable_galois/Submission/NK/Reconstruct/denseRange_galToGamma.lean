import Mathlib
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.proj_surjective
import Submission.NK.Reconstruct.exists_frobElement
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Density of the canonical map `G_K → Γ_K`

`NK.Reconstruct.galToGamma ℓ : Gal(K'/K) →* Gamma K K' ℓ` is the canonical map from the absolute
Galois group of `K` to Shimizu's ℓ-adic abelianisation `Γ_K = lim_{L} ℓ-part(Gal(L/K)^{ab})`
(`NK.Reconstruct.galToGamma`), sending an automorphism `g` to the coherent family of the
ℓ-primary components of the images of its restrictions `g|_L`.

This file proves that this map has **dense range** — the statement that the group-theoretic
statements about `G_K` (in particular the density of the Frobenius elements,
`NK.Reconstruct.topologicalClosure_isFrobElement_eq_top`) can be transported to `Γ_K`, where the
abelianised argument of Shimizu's §4 takes place.  It is item 1 of the plan of `README` §17.

## The proof

The map is *not* proved surjective (which would need the compactness of `G_K`): density is what the
abelianised argument uses, and density follows from the surjectivity of `galToGamma` at a *single*
finite level, which is elementary.

* `surjective_galToGamma_proj` — for every finite normal level `L` of `K'/K` and every
  `x ∈ Γ_{L,ℓ} = ℓ-part(Gal(L/K)^{ab})` there is `g : Gal(K'/K)` with `Γ_{L,ℓ}`-component `x`.
  Indeed `ellComp ℓ` is onto the ℓ-primary part (`ellComp_eq_self`), the abelianisation
  `Gal(L/K) → Gal(L/K)^{ab}` is onto, and the restriction `Gal(K'/K) → Gal(L/K)` is onto because
  `L/K` is normal and `K'/K` is Galois (`AlgEquiv.restrictNormalHom_surjective`).
* `denseRange_galToGamma` — the topology of `Γ_K` is the topology induced from the product of the
  *discrete* finite level groups, so a neighbourhood of `f ∈ Γ_K` contains the set of `y` agreeing
  with `f` on a *finite* set `I` of levels (`isOpen_pi_iff` applied to an open set of the product,
  `isOpen_induced_iff` for the subtype `Γ_K`).  Choosing an upper bound `T` of `I` and lifting the
  single component `f_T ∈ Γ_{T,ℓ}` with `surjective_galToGamma_proj`, the coherence of `f` and of
  `galToGamma g` (`Gamma.proj_compatible`) makes `galToGamma g` agree with `f` on `I`, hence lie in
  the given neighbourhood.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped Pointwise

section Level

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- **`galToGamma` is surjective at each finite level**: every element of the ℓ-primary part of the
abelianisation of a finite normal level `L/K` is the ℓ-primary component of the restriction of some
automorphism of `K'/K`.

The ℓ-primary projection `ellComp ℓ` is onto the ℓ-primary part (`ellComp_eq_self`), the
abelianisation of a group is a quotient of it, and the restriction `Gal(K'/K) → Gal(L/K)` is
surjective because `L/K` is normal and `K'/K` is Galois
(`AlgEquiv.restrictNormalHom_surjective`). -/
theorem surjective_galToGamma_proj (ℓ : ℕ) (L : FrobLevel K K') (x : LevelEllPart L.L ℓ) :
    ∃ g : Gal(K'/K), Gamma.proj L (galToGamma (K := K) (K' := K') ℓ g) = x := by
  classical
  -- an element of the abelianisation whose ℓ-primary component is `x`
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective ((x : LevelEllPart L.L ℓ) : LevelAbelianization L.L)
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(↥L.L/K), Abelianization.of σ = (x : LevelAbelianization L.L) :=
    ⟨b, hb⟩
  -- it is the restriction of an automorphism of `K'`
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥L.L) (E := K') σ
  exact ⟨g, by
    rw [galToGamma_proj, levelComponent, hg, hσ]
    exact ellComp_eq_self x⟩

/-- **The range of `galToGamma` is dense.**

The topology of `Γ_K` is the topology induced from the product of the finite (discrete) level
groups `Γ_{L,ℓ}`: a neighbourhood of `f ∈ Γ_K` contains the set of `y ∈ Γ_K` agreeing with `f` on
some *finite* set `I` of levels.  Given `I` and an upper bound `T` of it, any lift of the component
`f_T ∈ Γ_{T,ℓ}` (`surjective_galToGamma_proj`) agrees with `f` on `I`, by coherence of the
projective system (`Gamma.proj_compatible`). -/
theorem denseRange_galToGamma {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) :
    DenseRange ⇑(galToGamma (K := K) (K' := K') ℓ) := by
  classical
  rw [denseRange_iff_closure_range]
  refine Set.eq_univ_iff_forall.mpr (fun f => ?_)
  rw [mem_closure_iff]
  intro o ho hfo
  -- an open set of the limit is, near `f`, a finite cylinder
  rw [isOpen_induced_iff] at ho
  obtain ⟨U, hU, rfl⟩ := ho
  obtain ⟨I, u, hu, hIU⟩ :=
    isOpen_pi_iff.mp hU (f : ∀ L : FrobLevel K K', LevelEllPart L.L ℓ) hfo
  -- it suffices to agree with `f` on the finite set `I` of levels
  have key : ∃ g : Gal(K'/K), ∀ a ∈ I,
      Gamma.proj a (galToGamma (K := K) (K' := K') ℓ g) ∈ u a := by
    by_cases hI : I.Nonempty
    · -- take an upper bound `T` of `I` and lift `f_T`
      obtain ⟨L₀, hL₀⟩ := hI
      obtain ⟨T, hT, -⟩ := projSurj_finset_exists_upper_bound (K := K) (K' := K') L₀ I
      obtain ⟨g, hg⟩ := surjective_galToGamma_proj (K := K) (K' := K') ℓ T (Gamma.proj T f)
      refine ⟨g, fun a ha => ?_⟩
      have hle : a.L ≤ T.L := hT a ha
      have h1 : Gamma.proj a (galToGamma (K := K) (K' := K') ℓ g) = Gamma.proj a f := by
        rw [← Gamma.proj_compatible (K := K) (K' := K') a T hle
            (galToGamma (K := K) (K' := K') ℓ g),
          hg, Gamma.proj_compatible (K := K) (K' := K') a T hle f]
      rw [h1]
      exact (hu a ha).2
    · -- no constraint at all
      refine ⟨1, fun a ha => ?_⟩
      have hIe : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      rw [hIe] at ha
      exact absurd ha (Finset.notMem_empty a)
  obtain ⟨g, hg⟩ := key
  exact ⟨galToGamma (K := K) (K' := K') ℓ g, hIU (by rw [Set.mem_pi]; exact hg), ⟨g, rfl⟩⟩

end Level

end NK.Reconstruct
