import Mathlib
import Submission.NK.Reconstruct.baseChange
import Submission.NK.Reconstruct.proj_surjective
import Submission.NK.Reconstruct.abelianization_range_inclusion_eq_ker_quotient
import Submission.NK.Reconstruct.exists_pow_projection_ellPart
import Submission.NK.Reconstruct.LevelInclExact.levelInclHom_range_eq_ker_levelRestrictHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exactness of the level inclusion `ellIncl` against the level restriction `ellRestrict`

For two finite Galois levels `L ⊆ M` of `K'/K` (`NK.Reconstruct.FrobLevel`), the group-level
exactness of Galois theory (`LevelInclExact.levelInclHom_range_eq_ker_levelRestrictHom`)

  `1 → Gal(M/L) → Gal(M/K) → Gal(L/K) → 1`

induces, by functoriality of the abelianisation, an exact sequence of finite abelian groups

  `Ab(Gal(M/L)) → Ab(Gal(M/K)) → Ab(Gal(L/K))`

(`abelianization_range_eq_ker_of_range_eq_ker`), and the content of this file is that the
ℓ-primary parts of that sequence are **again exact in the middle**:

  `(ellIncl ℓ L M h).range = (ellRestrict ℓ L M h).ker`,

i.e. the exactness of the inclusion of the two projective systems of ℓ-parts at the level of the
ℓ-parts themselves.  Equivalently, writing `f : A →* B` and `g : B →* C` for the two abelianised
maps, the ℓ-part functor commutes with the "middle" of the sequence:

  `f(A_ℓ) = B_ℓ ⊓ ker g`   (`ellPart_map_eq_inf_ker`).

## Why the ℓ-part step is not formal

The functor `A ↦ A_ℓ = {a | ∃ n, a ^ ℓ ^ n = 1}` is *not* exact in the middle in general: an
ℓ-primary element `b ∈ B` lying in the image of `f` need not be the image of an ℓ-primary element
of `A` (take `f : ℤ → ℤ/ℓ`).  The missing ingredient is **finiteness of `A`**, and the argument
used here is a uniform "projection onto the ℓ-primary part":

* by `exists_pow_projection_ellPart` applied to `A × B`, there is a single exponent `c` such that
  `x ^ c` is ℓ-primary for every `x : A × B` *and* the "error term" `x * (x ^ c)⁻¹` is killed by an
  integer `m` coprime to `ℓ` (`NK.Reconstruct.exists_pow_projection_ellPart`);
* applied to `(a, b)` with `f a = b`, this gives `a ^ c` and `b ^ c` ℓ-primary, with the error term
  `b * (b ^ c)⁻¹` also ℓ-primary;
* coprimality of `m` and `ℓ` then forces that error term to be trivial, so `b = b ^ c = f (a ^ c)`
  exhibits `b` as the image of the ℓ-primary element `a ^ c`.

The same finiteness/ℓ-primary projection is what makes the ℓ-part functor exact on *surjections*
(`NK.Reconstruct.ellPart_map_eq_of_surjective`, the engine of `ellRestrict_surjective`).

## Contents

* `abelianization_map_one` — the abelianisation of the trivial homomorphism is trivial;
* `comp_eq_one_of_range_le_ker` — a composite whose first range lies in the second kernel is trivial;
* `abelianization_range_eq_ker_of_range_eq_ker` — exactness at the middle term of the abelianisation
  (`Ab(H) → Ab(G) → Ab(C)`) of a homomorphism `φ : H →* G` whose range is the kernel of a surjection
  `ψ : G →* C`;
* `ellPart_map_eq_inf_ker` — the ℓ-part of the middle term is the intersection of the ℓ-part with the
  kernel (in the case `range f = ker g`);
* `ellIncl_range_eq_ker_ellRestrict` — **the target**: the level inclusion and the level restriction
  are exact on the ℓ-primary parts.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct.LevelInclExact

/-! ## Exactness of the abelianisation at the middle term -/

/-- **The abelianisation of the trivial homomorphism is trivial.**  `Abelianization.map` is a
functor, hence carries identities to identities; the statement is recorded separately because its
pointwise form `(Ab.map 1) x = 1` is not reachable by `simp` (it holds by extensionality of
homomorphisms out of an abelianisation). -/
theorem abelianization_map_one {G H : Type*} [Group G] [Group H] :
    Abelianization.map (1 : G →* H) = 1 := by
  refine Abelianization.hom_ext _ _ ?_
  ext g
  simp

/-- **A composite whose first range lies in the second kernel is trivial.**  If `φ.range ≤ ψ.ker`
then `ψ ∘ φ = 1`, the identity being the trivial homomorphism `H →* C`. -/
theorem comp_eq_one_of_range_le_ker {G H C : Type*} [Group G] [Group H] [Group C]
    (φ : H →* G) (ψ : G →* C) (h : φ.range ≤ ψ.ker) : ψ.comp φ = 1 := by
  refine MonoidHom.ext fun a => ?_
  show ψ (φ a) = 1
  rw [← MonoidHom.mem_ker]
  exact h (MonoidHom.mem_range.mpr ⟨a, rfl⟩)

/-- **Exactness of the abelianisation at the middle term.**  If `ψ : G →* C` is surjective and the
range of `φ : H →* G` is the kernel of `ψ`, then the induced maps on abelianisations are exact at
`Ab(G)`:

  `(Abelianization.map φ).range = (Abelianization.map ψ).ker`.

Both inclusions are the two halves of the exactness of `H → G → C` at `G`, transported along the
projection `G ↠ Ab(G) = G ⧸ [G,G]`:

* `ψ ∘ φ = 1`, hence `Ab(ψ) ∘ Ab(φ) = Ab(ψ ∘ φ) = 1`;
* if `Ab(ψ) z = 1` and `Ab.of σ = z`, then `ψ σ ∈ [C,C]`; surjectivity of `ψ` gives
  `[C,C] = ψ([G,G])` (`Subgroup.map_commutator`), so `ψ σ = ψ c` for some `c ∈ [G,G]`, whence
  `c⁻¹ σ ∈ ker ψ = range φ` and `z = Ab.of σ = Ab.of (φ x)` for a preimage `x`. -/
theorem abelianization_range_eq_ker_of_range_eq_ker {G H C : Type*} [Group G] [Group H] [Group C]
    (φ : H →* G) (ψ : G →* C) (hψ : Function.Surjective ψ) (h : φ.range = ψ.ker) :
    (Abelianization.map φ).range = (Abelianization.map ψ).ker := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    have h1 : ψ.comp φ = 1 := comp_eq_one_of_range_le_ker φ ψ (le_of_eq h)
    rw [← MonoidHom.comp_apply, Abelianization.map_comp, h1]
    exact DFunLike.congr_fun (abelianization_map_one (G := H) (H := C)) x
  · intro z hz
    rw [MonoidHom.mem_ker] at hz
    -- lift the element of `Ab(G)` to `G`
    have hofsurj : Function.Surjective (Abelianization.of : G →* Abelianization G) :=
      MonoidHom.range_eq_top.mp (MonoidHom.range_eq_top.mpr
        (QuotientGroup.mk'_surjective (commutator G)))
    obtain ⟨σ, rfl⟩ := hofsurj z
    rw [Abelianization.map_of] at hz
    -- `ψ σ` dies in the abelianisation of `C`
    have hmem : ψ σ ∈ commutator C := by
      rw [← Abelianization.ker_of]
      exact MonoidHom.mem_ker.mpr hz
    -- the commutator of the quotient is the image of the commutator
    have hcomm : (commutator G).map ψ = commutator C := by
      rw [commutator_def C, commutator_def G, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ]
    rw [← hcomm] at hmem
    obtain ⟨c, hc, hcψ⟩ := Subgroup.mem_map.mp hmem
    -- `σ` differs from a commutator by an element of `ker ψ = range φ`
    have hker : c⁻¹ * σ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcψ, inv_mul_cancel]
    rw [← h] at hker
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hker
    refine ⟨Abelianization.of x, ?_⟩
    rw [Abelianization.map_of, hx, map_mul, map_inv]
    have hc1 : Abelianization.of c = 1 := by
      rw [← MonoidHom.mem_ker, Abelianization.ker_of]
      exact hc
    rw [hc1, inv_one, one_mul]

/-! ## Exactness of the ℓ-primary parts at the middle term -/

/-- **The ℓ-part functor is exact at the middle term** for finite commutative groups: if
`f : A →* B` has range the kernel of `g : B →* C`, then the ℓ-primary part of `B` meets `ker g`
exactly in the image of the ℓ-primary part of `A`:

  `Subgroup.map f (ellPart A ℓ) = ellPart B ℓ ⊓ g.ker`.

The inclusion `⊆` is immediate.  For the converse, given `b ∈ B` in the ℓ-part and killed by `g`,
choose `a` with `f a = b` and apply the projection onto the ℓ-primary part of the *finite* group
`A × B` (`exists_pow_projection_ellPart`) to the single element `(a, b)`: the resulting exponent `c`
makes `a ^ c` and `b ^ c` ℓ-primary while the error term `b * (b ^ c)⁻¹` is killed by an integer
coprime to `ℓ`; the error term is ℓ-primary as well (it is a quotient of two ℓ-primary elements of
the *same* `B`), so it is trivial.  Hence `b = b ^ c = f (a ^ c)` with `a ^ c` ℓ-primary. -/
theorem ellPart_map_eq_inf_ker {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
    [Finite A] [Finite B] (ℓ : ℕ) (f : A →* B) (g : B →* C) (h : f.range = g.ker) :
    Subgroup.map f (ellPart A ℓ) = ellPart B ℓ ⊓ g.ker := by
  refine le_antisymm ?_ ?_
  · rw [le_inf_iff]
    refine ⟨ellPart_map_le ℓ f, ?_⟩
    rw [Subgroup.map_le_iff_le_comap]
    intro a ha
    rw [Subgroup.mem_comap]
    rw [← h]
    exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
  · intro b hb
    rw [Subgroup.mem_inf, MonoidHom.mem_ker] at hb
    obtain ⟨hbE, hbg⟩ := hb
    have hbrange : b ∈ f.range := by rw [h]; exact hbg
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hbrange
    -- the uniform exponent produced by the projection onto the ℓ-primary part of `A × B`
    obtain ⟨c, hc⟩ := exists_pow_projection_ellPart (A := A × B) ℓ
    have h1 := (hc (a, b)).1
    have h2 := (hc (a, b)).2
    rw [mem_ellPart_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have haE : a ^ c ∈ ellPart A ℓ := by
      rw [mem_ellPart_iff]
      exact ⟨n, congrArg Prod.fst hn⟩
    have hbEc : b ^ c ∈ ellPart B ℓ := by
      rw [mem_ellPart_iff]
      exact ⟨n, congrArg Prod.snd hn⟩
    -- the error term is killed by an integer coprime to `ℓ` ...
    obtain ⟨m, hcop, hm⟩ := h2
    have hbm : (b * (b ^ c)⁻¹) ^ m = 1 := congrArg Prod.snd hm
    -- ... and is ℓ-primary, because `b` and `b ^ c` are
    have hzE : b * (b ^ c)⁻¹ ∈ ellPart B ℓ := mul_mem hbE (inv_mem hbEc)
    obtain ⟨N, hN⟩ := (mem_ellPart_iff ℓ (b * (b ^ c)⁻¹)).mp hzE
    have hz : b = b ^ c := by
      rw [← mul_inv_eq_one]
      rw [← orderOf_eq_one_iff]
      have hdvd : orderOf (b * (b ^ c)⁻¹) ∣ (m.gcd (ℓ ^ N)) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hbm) (orderOf_dvd_of_pow_eq_one hN)
      rw [(hcop.pow_right N).gcd_eq_one, Nat.dvd_one] at hdvd
      exact hdvd
    refine Subgroup.mem_map.mpr ⟨a ^ c, haE, ?_⟩
    rw [map_pow, ha, hz.symm]

/-! ## The level inclusion is exact against the level restriction -/

/-- **Exactness of the level inclusion against the level restriction on the ℓ-primary parts.**  For
finite Galois levels `L ⊆ M` of `K'/K`, the range of the level inclusion
`ellIncl ℓ L M h : Γ_{M,ℓ}(L) → Γ_{M,ℓ}(K)` (forgetting the `L`-structure of an automorphism of
`M`) is the kernel of the level restriction
`ellRestrict ℓ L M h : Γ_{M,ℓ}(K) → Γ_{L,ℓ}(K)` (restricting an automorphism of `M` to `L`).

The proof combines the three ingredients above: the Galois-theoretic exactness at the group level
(`levelInclHom_range_eq_ker_levelRestrictHom`), its abelianisation
(`abelianization_range_eq_ker_of_range_eq_ker`, using the surjectivity
`levelRestrictHom_surjective` of the restriction), and the exactness of the ℓ-primary parts
(`ellPart_map_eq_inf_ker`, using finiteness of the two abelianisations — automatic, they are
abelianisations of finite Galois groups).  The two constructions of the statement are the "
forget the `L`-structure" map `ellIncl` and the transition map `ellRestrict` of the projective
system of ℓ-parts. -/
theorem ellIncl_range_eq_ker_ellRestrict {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) (L M : FrobLevel K K')
    (h : L.L ≤ M.L) : (ellIncl ℓ L M h).range = (ellRestrict ℓ L M h).ker := by
  classical
  -- exactness at the group level, and surjectivity of the level restriction
  have hAB := levelInclHom_range_eq_ker_levelRestrictHom L M h
  have hsurj := levelRestrictHom_surjective L M h
  -- exactness at the level of the abelianisations
  have hexact : (Abelianization.map (levelInclHom L M h)).range
      = (Abelianization.map (levelRestrictHom L M h)).ker :=
    abelianization_range_eq_ker_of_range_eq_ker _ _ hsurj hAB
  -- the two group maps compose to the identity (`levelInclHom` lands in `ker levelRestrictHom`)
  have hcomp : (levelRestrictHom L M h).comp (levelInclHom L M h) = 1 :=
    comp_eq_one_of_range_le_ker _ _ (le_of_eq hAB)
  -- exactness at the level of the ℓ-primary parts
  have hparts := ellPart_map_eq_inf_ker ℓ
    (Abelianization.map (levelInclHom L M h)) (Abelianization.map (levelRestrictHom L M h)) hexact
  refine le_antisymm ?_ ?_
  · -- the inclusion lands in the kernel of the restriction
    rintro y ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [ellRestrict_coe, ellIncl_coe, levelRestrict, ← MonoidHom.comp_apply,
      Abelianization.map_comp, hcomp]
    exact DFunLike.congr_fun (abelianization_map_one
      (G := Gal(↥(levelExtend L M h).L/↥L.L)) (H := Gal(↥L.L/K))) x.1
  · -- an ℓ-primary element killed by the restriction comes from an ℓ-primary element
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hy1 : (y : LevelAbelianization (K := K) (K' := K') M.L)
        ∈ (Abelianization.map (levelRestrictHom L M h)).ker := by
      rw [MonoidHom.mem_ker]
      have h2 := congrArg (fun t : ↥(LevelEllPart (K := K) (K' := K') L.L ℓ) =>
        (t : LevelAbelianization (K := K) (K' := K') L.L)) hy
      simpa [ellRestrict_coe, levelRestrict] using h2
    have hyB : (y : LevelAbelianization (K := K) (K' := K') M.L)
        ∈ Subgroup.map (Abelianization.map (levelInclHom L M h))
            (ellPart (LevelAbelianization (K := ↥L.L) (K' := K')
              (levelExtend L M h).L) ℓ) := by
      rw [hparts]
      exact ⟨y.2, hy1⟩
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hyB
    exact ⟨⟨x, hx⟩, Subtype.ext (by rw [ellIncl_coe, hfx])⟩

end NK.Reconstruct.LevelInclExact
