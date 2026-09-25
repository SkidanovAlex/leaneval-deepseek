import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.ellPart
import Submission.NK.Reconstruct.GammaSup
import Submission.NK.Reconstruct.ellRestrict_comp
import Submission.NK.Reconstruct.exists_frobElement

/-!
# The canonical surjection `G_K → Γ_K` (Shimizu §4, item 1 of the plan)

Let `K` be a number field and `K'` a separable closure of `K`.  `Γ_K = Gamma K K' ℓ` is the
projective limit of the ℓ-primary parts `Γ_{L,ℓ} = (Gal(L/K)^{ab})^{(ℓ)}` of the abelianisations of
the finite normal levels `L/K` of `K'/K` (`NK.Reconstruct.GammaObject`).  This file builds the
map

  `galToGamma ℓ : Gal(K'/K) →* Gamma K K' ℓ`,

sending an automorphism `g` to the coherent family of the ℓ-primary components of the images of its
restrictions `g|L` in `Ab(Gal(L/K))`.

This is the bridge that lets the *group-theoretic* statements about `G_K` (in particular the
density of the Frobenius elements, `NK.Reconstruct.topologicalClosure_isFrobElement_eq_top`) be
transported to `Γ_K`, where the abelianised argument of Shimizu's §4 takes place.  It is item 1 of
the plan of README §17.

## Contents

* `ellComp_one`, `ellCoprimeRel_mul`, `ellComp_mul`, `eq_ellComp_of_ellCoprimeRel`,
  `ellComp_eq_self` — the elementary API of the ℓ-primary projection `ellComp`;
* `levelComponent ℓ L g` — the ℓ-primary component of `g|L` in `Ab(Gal(L/K))`;
* `levelRestrictHom_restrictNormalHom`, `ellRestrict_ellComp` — its compatibility with the
  transition maps;
* `levelComponent_compatible` — the coherence of the family, whence `galToGamma`;
* `galToGamma_proj` — its defining projection formula.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

open scoped Pointwise

/-! ## The elementary API of the ℓ-primary projection -/

section EllCompAPI

variable {A : Type*} [CommGroup A] [Finite A]

/-- The ℓ-primary component of `1` is `1`. -/
theorem ellComp_one (ℓ : ℕ) : ellComp ℓ (1 : A) = 1 := by
  refine Subtype.ext ?_
  exact eq_of_mem_ellPart_of_ellCoprimeRel (ellComp ℓ 1).2 (one_mem _)
    (ellCoprimeRel_symm (ellCoprimeRel_ellComp ℓ (1 : A)))

/-- **The ℓ-coprimality relation is multiplicative.**  If `y` differs from `x` by a factor of order
coprime to `ℓ` and `v` from `u`, then `y * v` differs from `x * u` by a factor of order coprime to
`ℓ` (the product of the two orders). -/
theorem ellCoprimeRel_mul {ℓ : ℕ} {x y u v : A} (h : EllCoprimeRel ℓ x y)
    (h' : EllCoprimeRel ℓ u v) : EllCoprimeRel ℓ (x * u) (y * v) := by
  obtain ⟨m, hm, hxy⟩ := h
  obtain ⟨m', hm', huv⟩ := h'
  refine ⟨m * m', hm.mul_left hm', ?_⟩
  have hsplit : (x * u) * (y * v)⁻¹ = (x * y⁻¹) * (u * v⁻¹) := by
    rw [mul_inv_rev]
    ac_rfl
  rw [hsplit, mul_pow,
    show ((x * y⁻¹) ^ (m * m')) = 1 by rw [pow_mul, hxy, one_pow],
    show ((u * v⁻¹) ^ (m * m')) = 1 by
      rw [show m * m' = m' * m from Nat.mul_comm m m', pow_mul, huv, one_pow],
    mul_one]

/-- **The ℓ-primary component is multiplicative.** -/
theorem ellComp_mul (ℓ : ℕ) (x y : A) : ellComp ℓ (x * y) = ellComp ℓ x * ellComp ℓ y := by
  refine Subtype.ext ?_
  refine eq_of_mem_ellPart_of_ellCoprimeRel (ellComp ℓ (x * y)).2
    (mul_mem (ellComp ℓ x).2 (ellComp ℓ y).2) ?_
  exact ellCoprimeRel_trans (ellCoprimeRel_symm (ellCoprimeRel_ellComp ℓ (x * y)))
    (ellCoprimeRel_mul (ellCoprimeRel_ellComp ℓ x) (ellCoprimeRel_ellComp ℓ y))

/-- **An element of the ℓ-primary part is ℓ-coprime-related to `x` iff it is the ℓ-primary
component of `x`.** -/
theorem eq_ellComp_of_ellCoprimeRel {ℓ : ℕ} {x : A} {y : ellPart A ℓ}
    (h : EllCoprimeRel ℓ x (y : A)) : y = ellComp ℓ x := by
  refine Subtype.ext (eq_of_mem_ellPart_of_ellCoprimeRel (x := (y : A))
    (y := ((ellComp ℓ x : ellPart A ℓ) : A)) y.2 (ellComp ℓ x).2 ?_)
  exact ellCoprimeRel_trans (ellCoprimeRel_symm h) (ellCoprimeRel_ellComp ℓ x)

/-- The ℓ-primary projection is the identity on the ℓ-primary part. -/
theorem ellComp_eq_self {ℓ : ℕ} (x : ellPart A ℓ) : ellComp ℓ (x : A) = x :=
  (eq_ellComp_of_ellCoprimeRel (x := (x : A)) (y := x)
    ⟨1, Nat.coprime_one_left ℓ, by simp⟩).symm

end EllCompAPI

/-! ## The ℓ-primary component of the restriction of an automorphism -/

section Level

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- **The ℓ-primary component of `g` at the finite level `L`**: the image of the restriction of `g`
to `L` in the abelianisation of `Gal(L/K)`, projected to its ℓ-primary part. -/
noncomputable def levelComponent (ℓ : ℕ) (L : FrobLevel K K') (g : Gal(K'/K)) :
    LevelEllPart L.L ℓ :=
  ellComp ℓ (Abelianization.of (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L.L g))

/-- **The restriction maps of the projective system are the restrictions of automorphisms**: for
levels `L ⊆ M` of `K'/K`, restricting `g|M` further to `L` gives `g|L`. -/
theorem levelRestrictHom_restrictNormalHom (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (g : Gal(K'/K)) :
    levelRestrictHom L M h (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M.L g) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L.L g := by
  ext y
  rw [levelRestrictHom_apply_coe]
  simp only [AlgEquiv.restrictNormalHom_apply]

/-- **The ℓ-primary projection commutes with the transition maps**: the two ways of reading off the
ℓ-primary component of `g` at a sublevel `L ⊆ M` agree. -/
theorem ellRestrict_ellComp (ℓ : ℕ) (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (x : LevelAbelianization M.L) :
    ellRestrict ℓ L M h (ellComp ℓ x) = ellComp ℓ (levelRestrict L M h x) := by
  have h1 : EllCoprimeRel ℓ (levelRestrict L M h x)
      (((ellRestrict ℓ L M h (ellComp ℓ x) : LevelEllPart L.L ℓ)) :
        LevelAbelianization L.L) := by
    rw [ellRestrict_coe]
    exact ellCoprimeRel_map (levelRestrict L M h) (ellCoprimeRel_ellComp ℓ x)
  have h2 : EllCoprimeRel ℓ (levelRestrict L M h x)
      ((ellComp ℓ (levelRestrict L M h x) : LevelEllPart L.L ℓ) :
        LevelAbelianization L.L) :=
    ellCoprimeRel_ellComp ℓ (levelRestrict L M h x)
  exact Eq.trans
    (eq_ellComp_of_ellCoprimeRel (x := levelRestrict L M h x)
      (y := ellRestrict ℓ L M h (ellComp ℓ x)) h1)
    ((eq_ellComp_of_ellCoprimeRel (x := levelRestrict L M h x)
      (y := ellComp ℓ (levelRestrict L M h x)) h2).symm)

/-- **The family of the ℓ-primary components of `g` is coherent**: this is what makes `galToGamma`
well defined. -/
theorem levelComponent_compatible (ℓ : ℕ) (g : Gal(K'/K)) :
    Compatible ℓ (fun L : FrobLevel K K' => levelComponent ℓ L g) := by
  intro L M h
  show ellRestrict ℓ L M h (levelComponent ℓ M g) = levelComponent ℓ L g
  rw [levelComponent, ellRestrict_ellComp, levelComponent, levelRestrict,
    Abelianization.map_of, levelRestrictHom_restrictNormalHom]

/-- **The underlying function of the canonical map `Gal(K'/K) → Γ_K`**: `g` is sent to the
coherent family of the ℓ-primary components of its restrictions. -/
noncomputable def galToGammaFun (ℓ : ℕ) (g : Gal(K'/K)) : Gamma K K' ℓ :=
  Gamma.mk (fun L => levelComponent ℓ L g) (levelComponent_compatible ℓ g)

/-- **The defining formula of `galToGammaFun`**. -/
theorem galToGammaFun_proj (ℓ : ℕ) (L : FrobLevel K K') (g : Gal(K'/K)) :
    Gamma.proj L (galToGammaFun (K := K) (K' := K') ℓ g) = levelComponent ℓ L g :=
  Gamma.proj_mk _ _ _

/-- `galToGammaFun` is unital. -/
theorem galToGammaFun_one (ℓ : ℕ) : galToGammaFun (K := K) (K' := K') ℓ 1 = 1 := by
  refine Gamma.ext (fun L => ?_)
  simp only [galToGammaFun_proj, map_one, levelComponent, map_one, ellComp_one]

/-- `galToGammaFun` is multiplicative. -/
theorem galToGammaFun_mul (ℓ : ℕ) (g h : Gal(K'/K)) :
    galToGammaFun (K := K) (K' := K') ℓ (g * h) =
      galToGammaFun (K := K) (K' := K') ℓ g * galToGammaFun (K := K) (K' := K') ℓ h := by
  refine Gamma.ext (fun L => ?_)
  simp only [galToGammaFun_proj, map_mul, levelComponent, ellComp_mul]

/-- **The canonical map `Gal(K'/K) →* Γ_K`**: the coherent family of the ℓ-primary components of
the restrictions of `g` to the finite levels of `K'/K`.  This is the map whose existence is item 1
of the plan of README §17; it is the bridge from the group theory of `G_K` to the abelianised
`Γ_K`. -/
noncomputable def galToGamma (ℓ : ℕ) : Gal(K'/K) →* Gamma K K' ℓ where
  toFun := galToGammaFun (K := K) (K' := K') ℓ
  map_one' := galToGammaFun_one ℓ
  map_mul' := galToGammaFun_mul ℓ

/-- **The defining formula of `galToGamma`**. -/
theorem galToGamma_proj (ℓ : ℕ) (L : FrobLevel K K') (g : Gal(K'/K)) :
    Gamma.proj L (galToGamma (K := K) (K' := K') ℓ g) = levelComponent ℓ L g :=
  galToGammaFun_proj ℓ L g

end Level

end NK.Reconstruct
