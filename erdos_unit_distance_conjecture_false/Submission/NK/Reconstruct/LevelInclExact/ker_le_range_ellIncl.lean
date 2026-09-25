import Mathlib
import Submission.NK.Reconstruct.gammaBaseChange
import Submission.NK.Reconstruct.LevelInclExact.levelInclHom_range_eq_ker_levelRestrictHom
import Submission.NK.Reconstruct.abelianization_range_inclusion_eq_ker_quotient
import Submission.NK.Reconstruct.proj_surjective

/-!
# The kernel of the level restriction lies in the range of the level inclusion

For finite Galois levels `L ⊆ M` of `K'/K` the level inclusion `ellIncl ℓ L M h` and the level
restriction `ellRestrict ℓ L M h` are the two maps induced by

  `Gal(M/L) ↪ Gal(M/K) ↠ Gal(L/K)`

on the ℓ-primary parts of the abelianisations.  This file proves the *exactness* statement

`(ellRestrict ℓ L M h).ker ≤ (ellIncl ℓ L M h).range`,

i.e. that an ℓ-primary element of `Γ_{M,ℓ}(K) = ℓ-part(Gal(M/K)^{ab})` restricting to `1` in
`Γ_{L,ℓ}(K)` comes from `Γ_{M,ℓ}(L) = ℓ-part(Gal(M/L)^{ab})`.  (The reverse inclusion is the
formal `ellIncl_range_le_ker_ellRestrict`; together they give
`ellIncl_range_eq_ker_ellRestrict`.)

## The two ingredients

* **Group level** (`abelianization_ker_le_range_of_range_eq_ker`).  For groups `G, H, Q` and
  homomorphisms `f : G →* H`, `g : H →* Q` that are *exact* at `H` (`f.range = g.ker`) with `g`
  surjective, the induced maps on abelianisations are exact at `Ab(H)`:
  `(Ab g).ker ≤ (Ab f).range`.  The proof is elementary: writing an element of `Ab(H)` as
  `of σ`, the hypothesis `of (g σ) = 1` says that `g σ` is a commutator, hence `g σ = g h` for some
  `h ∈ [H,H]` (here the surjectivity of `g` is used, so that `[Q,Q] = g([H,H])`), and then
  `h⁻¹σ ∈ g.ker = f.range =: N`; finally `of σ = of (h · h⁻¹σ) = of (h⁻¹σ)` because `of` kills
  `[H,H]`, and `range (Ab f) = of '' N`.
  (The general statement without surjectivity of `g` is *false*; the surjectivity is what makes
  `Gal(L/K)` the quotient of `Gal(M/K)` by `Gal(M/L)`.)

* **Primary decomposition** (`exists_mem_ellPart_of_mem_range`).  The `ℓ`-primary-part functor is
  right exact on finite abelian groups: if `x` is ℓ-primary and lies in the range of `φ : A →* B`
  with `A` finite, then `x` is in the range of the restriction of `φ` to the ℓ-primary part of
  `A`.  Concretely, for a preimage `a` of `x` and the primary splitting `a = a^c · (a · (a^c)⁻¹)`
  of `NK.Reconstruct.projSurj_exists_pow_ellPart_split`, the complementary factor maps to
  `x · (x^c)⁻¹`, which is both ℓ-primary and of order coprime to `ℓ`, hence trivial
  (`NK.Reconstruct.projSurj_eq_one_of_mem_ellPart_of_coprime`); so `x = φ (a^c)` with `a^c`
  ℓ-primary.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3 and Ch. XII;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

/-- **Exactness of abelianisation.**  If `f : G →* H` and `g : H →* Q` are exact at `H` (that is,
`f.range = g.ker`) and `g` is surjective, then the induced maps on abelianisations are exact at
`Ab(H)`: the kernel of `Ab(g)` is contained in the range of `Ab(f)`.

The surjectivity of `g` is essential: it makes `[Q,Q] = g([H,H])`, so that the commutator
subgroup of `Q` can be pulled back to `[H,H] · f.range`. -/
theorem abelianization_ker_le_range_of_range_eq_ker {G H Q : Type*} [Group G] [Group H] [Group Q]
    (f : G →* H) (g : H →* Q) (hg : Function.Surjective g) (hfg : f.range = g.ker) :
    (Abelianization.map g).ker ≤ (Abelianization.map f).range := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  -- every element of `Ab(H)` is the class of an element of `H`
  obtain ⟨σ, hσx⟩ := QuotientGroup.mk'_surjective (commutator H) x
  rw [abelianization_range_map]
  have hx' : Abelianization.map g (Abelianization.of σ) = 1 := by
    rw [← hσx] at hx; exact hx
  rw [Abelianization.map_of] at hx'
  -- `g σ` is a commutator of `Q`
  have hσ : g σ ∈ commutator Q := by
    rw [← Abelianization.ker_of]
    exact MonoidHom.mem_ker.mpr hx'
  -- and, since `g` is surjective, it is the image of a commutator of `H`
  have hcomm : commutator Q = Subgroup.map g (commutator H) := by
    have h := Subgroup.map_commutator (⊤ : Subgroup H) (⊤ : Subgroup H) g
    rw [Subgroup.map_top_of_surjective g hg] at h
    exact h.symm
  obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.mp (hcomm ▸ hσ)
  -- so `h⁻¹ σ` lies in the kernel of `g`, i.e. in the range of `f`
  have hn : h⁻¹ * σ ∈ g.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
  rw [← hfg] at hn
  -- and `h` dies in `Ab(H)`
  have hh1 : Abelianization.of h = 1 := by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of]
    exact hh
  refine Subgroup.mem_map.mpr ⟨h⁻¹ * σ, hn, ?_⟩
  rw [map_mul, map_inv, hh1, inv_one, one_mul]
  exact hσx

/-- **The ℓ-primary part functor is right exact on finite abelian groups.**  If `x` is ℓ-primary and
lies in the range of `φ : A →* B` with `A` finite, then `x = φ y` for some ℓ-primary `y`.

For a preimage `a` of `x`, the primary splitting `a = a ^ c · (a * (a ^ c)⁻¹)` has ℓ-primary first
factor and second factor of order coprime to `ℓ`; the image of the second factor is
`x * (x ^ c)⁻¹`, which is ℓ-primary and of order coprime to `ℓ`, hence trivial. -/
theorem exists_mem_ellPart_of_mem_range {A B : Type*} [CommGroup A] [CommGroup B] [Finite A]
    (ℓ : ℕ) (φ : A →* B) {x : B} (hx : x ∈ ellPart B ℓ) (hxr : x ∈ φ.range) :
    ∃ y ∈ ellPart A ℓ, φ y = x := by
  obtain ⟨a, rfl⟩ := hxr
  obtain ⟨c, m, hcop, hsplit⟩ := projSurj_exists_pow_ellPart_split A ℓ
  refine ⟨a ^ c, (hsplit a).1, ?_⟩
  have hmem1 : φ (a ^ c) ∈ ellPart B ℓ :=
    ellPart_map_le ℓ φ (Subgroup.mem_map_of_mem φ (hsplit a).1)
  have hmem : φ (a * (a ^ c)⁻¹) ∈ ellPart B ℓ := by
    rw [map_mul, map_inv]
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hmem1)
  have hpow : (φ (a * (a ^ c)⁻¹)) ^ m = 1 := by
    rw [← map_pow, (hsplit a).2, map_one]
  have hone := projSurj_eq_one_of_mem_ellPart_of_coprime hmem hcop hpow
  rw [map_mul, map_inv] at hone
  exact (mul_inv_eq_one.mp hone).symm

end NK.Reconstruct

namespace NK.Reconstruct.LevelInclExact

/-- **The kernel of the level restriction lies in the range of the level inclusion.**  For finite
Galois levels `L ⊆ M` of `K'/K`, every ℓ-primary element of `Γ_{M,ℓ}(K)` restricting to `1` in
`Γ_{L,ℓ}(K)` comes from `Γ_{M,ℓ}(L)`.

The proof combines the two ingredients: the ℓ-restriction is `Ab(levelRestrictHom)` on ℓ-parts,
whose kernel at the level of abelianisations is the range of `Ab(levelInclHom)` by exactness of
`Gal(M/L) ↪ Gal(M/K) ↠ Gal(L/K)` (`abelianization_ker_le_range_of_range_eq_ker`), and the ℓ-primary
part functor is right exact (`exists_mem_ellPart_of_mem_range`). -/
theorem ker_le_range_ellIncl {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) (L M : FrobLevel K K')
    (h : L.L ≤ M.L) : (ellRestrict ℓ L M h).ker ≤ (ellIncl ℓ L M h).range := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  -- `x` lies in the kernel of the map on abelianisations
  have hxker : (x : LevelAbelianization M.L) ∈ (levelRestrict L M h).ker := by
    rw [MonoidHom.mem_ker]
    have := congrArg (fun y : LevelEllPart L.L ℓ => (y : LevelAbelianization L.L)) hx
    simpa [ellRestrict_coe] using this
  -- hence in the range of the abelianised level inclusion
  have hxrange : (x : LevelAbelianization M.L) ∈
      (Abelianization.map (levelInclHom L M h)).range :=
    abelianization_ker_le_range_of_range_eq_ker (levelInclHom L M h) (levelRestrictHom L M h)
      (projSurj_levelRestrictHom_surj h) (levelInclHom_range_eq_ker_levelRestrictHom L M h) hxker
  -- and the ℓ-primary part functor is right exact
  obtain ⟨y, hy, hyx⟩ := exists_mem_ellPart_of_mem_range ℓ
    (Abelianization.map (levelInclHom L M h)) x.2 hxrange
  exact ⟨⟨y, hy⟩, Subtype.ext (by rw [ellIncl_coe]; exact hyx)⟩

end NK.Reconstruct.LevelInclExact
