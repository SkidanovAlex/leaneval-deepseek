import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFTdeep.exists_sub_smul_eq_of_subsingleton_tateCohomology_neg_one
import Submission.NK.GlobalCFTdeep.prod_smul_mk_eq_one_of_normIdeleHom_eq
import Submission.NK.GlobalCFTdeep.prod_smul_mul_principalIdele_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-! ## Auxiliary computations

Two small general facts are recorded here: the norm map of the `ℤ[G]`-module `Additive A` attached
to a `MulDistribMulAction` of a finite group on a commutative group is the product of the
translates, and the product over `Gal(L/K)` of the translates of a unit of `L` is the canonical
image of its field norm. -/

/-- **The norm map on `Additive A` is the product of the translates.**
For a finite group `G` acting on a commutative group `A` by group automorphisms, the norm of the
`ℤ[G]`-module `Additive A` (i.e. `∑ g, g • -` in additive notation) evaluated at `Additive.ofMul a`
is `Additive.ofMul (∏ g, g • a)`. -/
theorem norm_ofMulDistribMulAction_eq_ofMul {G A : Type} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (a : A) :
    (Representation.ofMulDistribMulAction G A).norm (Additive.ofMul a) =
      Additive.ofMul (∏ g : G, g • a) := by
  refine Additive.toMul.injective ?_
  simpa using Representation.norm_ofMulDistribMulAction_eq (G := G) (M := A) (Additive.ofMul a)

/-- `Additive.ofMul` turns a finite product into a sum. -/
theorem sum_ofMul_eq_ofMul_prod {ι : Type} [Fintype ι] {A : Type} [CommMonoid A] (f : ι → A) :
    (∑ i, Additive.ofMul (f i)) = Additive.ofMul (∏ i, f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ih]; rfl

/-- **The product of the translates of a unit is the image of its norm.**  For a finite Galois
extension `L/K` and `b ∈ Lˣ`, the product over `Gal(L/K)` of the translates `σ • b` equals the
canonical image in `Lˣ` of the field norm `N_{L/K}(b) ∈ Kˣ`. -/
theorem prod_smul_eq_map_algebraMap_norm {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (b : Lˣ) :
    (∏ σ : L ≃ₐ[K] L, σ • b) =
      Units.map (algebraMap K L).toMonoidHom (Units.map (Algebra.norm K) b) := by
  ext
  simp [Algebra.norm_eq_prod_automorphisms]

/-- **Hasse's norm theorem (norm form) from the vanishing of `Ĥ⁻¹`.** Let `L/K` be a finite
Galois extension of number fields with cyclic Galois group.  If `Ĥ⁻¹(Gal(L/K), C_L) = 0` then an
element `a ∈ Kˣ` whose principal idèle is a norm from the idèles of `L` is a norm from `Lˣ`:
`Kˣ ∩ N_{L/K}𝕀_L = N_{L/K}Lˣ`.

Proof route (Milne, *Class Field Theory*, Lemma 5.2): the short exact sequence
`1 → Lˣ → 𝕀_L → C_L → 1` of `ℤ[Gal(L/K)]`-modules has a six-term exact sequence in Tate
cohomology (`TateCohomology.exact₁`, `exact₃` for the map of Tate complexes induced by a short
exact sequence of representations), which in degrees `-1, 0, 1` reads
`Ĥ⁻¹(G,C_L) → Ĥ⁰(G,Lˣ) → Ĥ⁰(G,𝕀_L) → Ĥ⁰(G,C_L) → H¹(G,Lˣ)`.
Under the identifications `Ĥ⁰(G,Lˣ) = Kˣ/N_{L/K}Lˣ` and `Ĥ⁰(G,𝕀_L) = 𝕀_K/N_{L/K}𝕀_L`
(`Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso`; the `C_L` side is the
already proved `NK.GlobalCFT.globalCFT_H0Computation`), the middle map `α` is induced by the
inclusion of principal idèles.  Exactness gives
`ker α = im(Ĥ⁻¹(G,C_L) → Ĥ⁰(G,Lˣ)) = 0`, i.e. `α` is injective, which is exactly the assertion:
`principalIdele K a ∈ N_{L/K}𝕀_L` means `α(a) = 0`, so `a = 0` in `Kˣ/N_{L/K}Lˣ`, i.e.
`a ∈ N_{L/K}Lˣ`.

Infrastructure that may have to be built (only the `C_L` side exists on disk): the short exact
sequence `1 → Lˣ → 𝕀_L → C_L → 1` of `ℤ[Gal(L/K)]`-modules as a `ShortComplex (Rep ℤ G)` with
`ShortExact`, its middle term being `IdeleClassGroup.rep K L`; and the identification of the
`G`-invariants of `𝕀_L` with `𝕀_K` (the norm subgroup part being `N_{L/K}𝕀_L`, which is the very
definition of `Idele.normImage`). -/
theorem hasseNorm_of_subsingleton_tateCohomology_neg_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (h : Subsingleton (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) (-1))) :
    ∀ a : Kˣ, NK.GlobalCFT.Idele.principalIdele K a ∈ NK.GlobalCFT.Idele.normImage K L →
      ∃ b : Lˣ, NK.GlobalCFT.Idele.principalIdele K a =
        NK.GlobalCFT.Idele.normIdeleFun K L (NK.GlobalCFT.Idele.principalIdele L b) := by
  intro a ha
  -- `y` is an idèle of `L` whose norm is the principal idèle of `a`
  obtain ⟨y, hy⟩ := Idele.mem_normImage.mp ha
  have hnorm : Idele.normIdeleHom K L y = Idele.principalIdele K a :=
    Idele.ext fun v => (hy v).symm
  -- the product over `Gal(L/K)` of the translates of the class of `y` in `C_L` is trivial
  have hprod : (∏ σ : L ≃ₐ[K] L, σ • IdeleClassGroup.mk L y) = 1 :=
    prod_smul_mk_eq_one_of_normIdeleHom_eq y a hnorm
  -- the `ℤ[G]`-module `C_L`, with its norm map written as the product of the translates
  let ρ : Representation ℤ (L ≃ₐ[K] L) (Additive (IdeleClassGroup L)) :=
    Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L)
  have hx₀ : ρ.norm (Additive.ofMul (IdeleClassGroup.mk L y)) = 0 := by
    change (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L)).norm
      (Additive.ofMul (IdeleClassGroup.mk L y)) = 0
    rw [norm_ofMulDistribMulAction_eq_ofMul, hprod]
    rfl
  -- a generator of the cyclic group `Gal(L/K)`
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hgen : Subgroup.zpowers σ₀ = ⊤ := (Subgroup.eq_top_iff' (Subgroup.zpowers σ₀)).mpr hσ₀
  -- `Ĥ⁻¹(G, C_L) = 0`: the class of `y` is a coboundary
  obtain ⟨w, hw⟩ := exists_sub_smul_eq_of_subsingleton_tateCohomology_neg_one ρ h σ₀ hgen
    (x := Additive.ofMul (IdeleClassGroup.mk L y)) hx₀
  set c : IdeleClassGroup L := Additive.toMul w with hc
  have hkey : Additive.toMul (ρ σ₀ w) = σ₀ • c := by
    have hw' : w = Additive.ofMul c := rfl
    rw [hw']
    change Additive.toMul ((Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L)) σ₀
      (Additive.ofMul c)) = σ₀ • c
    simp
  have hq : σ₀ • c * c⁻¹ = IdeleClassGroup.mk L y := by
    have h3 := congrArg Additive.toMul hw
    rw [toMul_sub, toMul_ofMul, hkey, div_eq_mul_inv] at h3
    exact h3
  -- lift the coboundary relation to the idèles: `y` differs from `σ₀ • x / x` by a principal idèle
  obtain ⟨x, hx⟩ := IdeleClassGroup.mk_surjective L c
  have hq' : IdeleClassGroup.mk L y = IdeleClassGroup.mk L (σ₀ • x * x⁻¹) := by
    rw [← hq, ← hx, IdeleClassGroup.smul_mk, map_mul, map_inv]
  have hmem : y⁻¹ * (σ₀ • x * x⁻¹) ∈ Idele.principalSubgroup L :=
    IdeleClassGroup.mk_eq_mk_iff.mp hq'
  obtain ⟨b', hb'⟩ := Idele.mem_principalSubgroup.mp hmem
  have hy_eq : y = (σ₀ • x * x⁻¹) * Idele.principalIdele L (b'⁻¹) := by
    have hz : y * Idele.principalIdele L b' = σ₀ • x * x⁻¹ := by
      rw [hb']; group
    rw [← hz, map_inv]
    group
  -- the idèle inclusion `𝕀 K →* 𝕀 L` attached to a choice of places of `L` over the places of `K`
  obtain ⟨u, hu⟩ : ∃ u : Place L → Place K, ∀ w, Place.LiesOver w (u w) :=
    ⟨fun w => Classical.choose (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w),
     fun w => Classical.choose_spec (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)⟩
  obtain ⟨φ, hφ⟩ := Inclusion.globalCFT_ideleInclusion_exists (K := K) (L := L) u hu
  -- the product of the translates of `y` is the image of the norm of `y`
  have h1 : (∏ σ : L ≃ₐ[K] L, σ • y) =
      Idele.principalIdele L (Units.map (algebraMap K L).toMonoidHom a) := by
    rw [Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom u hu φ hφ y, hnorm,
      Inclusion.globalCFT_ideleInclusion_principalIdele u hu φ hφ a]
  have h2 : (∏ σ : L ≃ₐ[K] L, σ • y) =
      Idele.principalIdele L (∏ σ : L ≃ₐ[K] L, σ • b'⁻¹) := by
    rw [hy_eq]
    exact prod_smul_mul_principalIdele_eq σ₀ x b'⁻¹
  -- hence `b'⁻¹` norm is `a`: this is Hasse's norm theorem
  have h3 : Units.map (algebraMap K L).toMonoidHom a = ∏ σ : L ≃ₐ[K] L, σ • b'⁻¹ :=
    Inclusion.globalCFT_principalIdele_injective L (h1.symm.trans h2)
  have h4 : Units.map (Algebra.norm K) b'⁻¹ = a := by
    refine Units.map_injective (f := (algebraMap K L).toMonoidHom) (RingHom.injective _) ?_
    rw [← prod_smul_eq_map_algebraMap_norm (K := K) (L := L) b'⁻¹]
    exact h3.symm
  refine ⟨b'⁻¹, ?_⟩
  rw [← h4, ← Idele.normIdeleHom_principalIdele b'⁻¹]
  rfl

end NK.GlobalCFTdeep
