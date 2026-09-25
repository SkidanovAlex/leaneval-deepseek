import Mathlib
import Submission.Work.CFT.Kummer.Defs

/-!
# Kummer duality for finite Galois extensions

Let `K` be a field containing a primitive `p`-th root of unity `ζ`, and let `L/K` be a finite
Galois extension.  Write `Δ = Lˣ^p ∩ Kˣ` for the group of *Kummer generators* of `L/K` and
`G = Gal(L/K)`.  The Kummer pairing
`G × Δ → μ_p(L)`, `(σ, d) ↦ σ(α)/α` (where `α^p = d`, `α ∈ Lˣ`)
is well defined, lands in the group `μ_p(L) = rootsOfUnity p L` of `p`-th roots of unity of `L`
(which is contained in `K` because `ζ` generates all of them), is bilinear, and induces an
isomorphism
`Δ / Kˣ^p ≃* Hom(G, μ_p(L))`.
Injectivity is the triviality of the pairing on `p`-th powers, surjectivity is Hilbert's
theorem 90 (equivalently, the standard resolvent argument using Dedekind's independence of
characters).  This is the statement proved here.

The file is a small self-contained chapter: the Kummer character attached to a generator,
its multiplicativity in the generator, the identification of the kernel with `Kˣ^p`, and
the resolvent construction producing a generator for a prescribed character.
-/

open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.CFT.Kummer

section Main

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

/-- The image in `Lˣ` of a unit `ζ` of `K`. -/
private def zetaL (ζ : Kˣ) : Lˣ := Units.map (algebraMap K L).toMonoidHom ζ

/-- Every `K`-algebra automorphism of `L` fixes the image of an element of `Kˣ`. -/
private lemma map_algebraMap_units (σ : L ≃ₐ[K] L) (c : Kˣ) :
    Units.map σ.toRingEquiv.toMonoidHom (Units.map (algebraMap K L).toMonoidHom c)
      = Units.map (algebraMap K L).toMonoidHom c := by
  apply Units.ext
  simp only [Units.coe_map]
  exact AlgEquiv.commutes σ (c : K)

variable {p : ℕ} [NeZero p] {ζ : Kˣ}

/-- If `ζ` is a primitive `p`-th root of unity in `L`, then every `p`-th root of unity in `L`
is a power of `ζ`, and therefore fixed by every `K`-algebra automorphism of `L`. -/
private lemma map_units_of_mem_rootsOfUnity
    (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p)
    (σ : L ≃ₐ[K] L) {ω : Lˣ} (hω : ω ∈ rootsOfUnity p L) :
    Units.map σ.toRingEquiv.toMonoidHom ω = ω := by
  obtain ⟨i, -, hi⟩ := hζu.eq_pow_of_mem_rootsOfUnity hω
  rw [← hi, map_pow]
  congr 1
  exact map_algebraMap_units σ ζ

/-- Version of `map_units_of_mem_rootsOfUnity` for the underlying elements of `L`. -/
private lemma apply_rootsOfUnity
    (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p)
    (σ : L ≃ₐ[K] L) {ω : Lˣ} (hω : ω ∈ rootsOfUnity p L) :
    σ ((ω : Lˣ) : L) = ((ω : Lˣ) : L) := by
  have h := congrArg (fun u : Lˣ => (u : L)) (map_units_of_mem_rootsOfUnity hζu σ hω)
  simpa [Units.coe_map] using h

/-- The Kummer ratio `σ(α)/α` depends only on `α ^ p`. -/
private lemma kummerRatio_congr (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p)
    (σ : L ≃ₐ[K] L) {α β : Lˣ} (h : α ^ p = β ^ p) :
    Units.map σ.toRingEquiv.toMonoidHom α / α
      = Units.map σ.toRingEquiv.toMonoidHom β / β := by
  have hγ : α / β ∈ rootsOfUnity p L := by
    rw [mem_rootsOfUnity, div_pow, h, div_self']
  have hfix := map_units_of_mem_rootsOfUnity hζu σ hγ
  have hα : Units.map σ.toRingEquiv.toMonoidHom α
      = (α / β) * Units.map σ.toRingEquiv.toMonoidHom β := by
    conv_lhs => rw [← div_mul_cancel α β]
    rw [map_mul, hfix]
  rw [hα, div_eq_div_iff_mul_eq_mul, mul_comm (α / β) (Units.map σ.toRingEquiv.toMonoidHom β),
    mul_assoc, div_mul_cancel]

/-- An auxiliary identity in a commutative group. -/
private lemma div_eq_div_mul_div {G : Type*} [CommGroup G] (x a b : G) :
    x / a = x / b * (b / a) := by
  rw [div_mul_div_comm, div_eq_div_iff_mul_eq_mul, mul_assoc]

/-- A chosen `p`-th root in `L` of a Kummer generator `d ∈ Kˣ`. -/
private def kummerRoot (d : kummerGenerators K L p) : Lˣ :=
  Classical.choose ((mem_pthPowerSubgroup).mp d.2)

private lemma kummerRoot_pow (d : kummerGenerators K L p) :
    kummerRoot d ^ p = Units.map (algebraMap K L).toMonoidHom (d : Kˣ) :=
  Classical.choose_spec ((mem_pthPowerSubgroup).mp d.2)

/-- The Kummer ratio `σ(α_d)/α_d` attached to a generator `d` and `σ ∈ Gal(L/K)`. -/
private def kummerRatio (d : kummerGenerators K L p) (σ : L ≃ₐ[K] L) : Lˣ :=
  Units.map σ.toRingEquiv.toMonoidHom (kummerRoot d) / kummerRoot d

private lemma kummerRatio_mem (d : kummerGenerators K L p) (σ : L ≃ₐ[K] L) :
    kummerRatio d σ ∈ rootsOfUnity p L := by
  rw [mem_rootsOfUnity, kummerRatio, div_pow, ← map_pow, kummerRoot_pow, map_algebraMap_units,
    div_self']

private lemma unitsMap_mul_apply (σ τ : L ≃ₐ[K] L) (α : Lˣ) :
    Units.map (σ * τ).toRingEquiv.toMonoidHom α
      = Units.map σ.toRingEquiv.toMonoidHom (Units.map τ.toRingEquiv.toMonoidHom α) := by
  rw [show ((σ * τ).toRingEquiv.toMonoidHom : L →* L)
        = (σ.toRingEquiv.toMonoidHom).comp (τ.toRingEquiv.toMonoidHom) from rfl, Units.map_comp]
  rfl

private lemma unitsMap_one_apply (α : Lˣ) :
    Units.map ((1 : L ≃ₐ[K] L).toRingEquiv.toMonoidHom) α = α := by
  apply Units.ext
  show (1 : L ≃ₐ[K] L) (α : L) = (α : L)
  exact AlgEquiv.one_apply (α : L)

/-- The Kummer character of `L/K` attached to the generator `d`: `σ ↦ σ(α_d)/α_d`. -/
private def kummerChar (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p)
    (d : kummerGenerators K L p) : (L ≃ₐ[K] L) →* rootsOfUnity p L where
  toFun σ := ⟨kummerRatio d σ, kummerRatio_mem d σ⟩
  map_one' := by
    apply Subtype.ext
    show kummerRatio d 1 = 1
    rw [kummerRatio, unitsMap_one_apply, div_self']
  map_mul' σ τ := by
    apply Subtype.ext
    show kummerRatio d (σ * τ) = kummerRatio d σ * kummerRatio d τ
    have step1 : kummerRatio d (σ * τ) = Units.map σ.toRingEquiv.toMonoidHom
        (Units.map τ.toRingEquiv.toMonoidHom (kummerRoot d)) / kummerRoot d := by
      rw [kummerRatio, unitsMap_mul_apply]
    rw [step1, div_eq_div_mul_div]
    have hp : (Units.map τ.toRingEquiv.toMonoidHom (kummerRoot d)) ^ p = (kummerRoot d) ^ p := by
      rw [← map_pow, kummerRoot_pow, map_algebraMap_units]
    rw [kummerRatio_congr hζu σ hp]
    rfl

/-- The Kummer character is trivial on `p`-th powers. -/
private lemma kummerChar_eq_one_of_mem (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p)
    {d : kummerGenerators K L p} (hd : (d : Kˣ) ∈ pthPowerSubgroup Kˣ p) :
    kummerChar hζu d = 1 := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  obtain ⟨c, hc⟩ := mem_pthPowerSubgroup.mp hd
  show kummerRatio d σ = 1
  have hp : kummerRoot d ^ p = (Units.map (algebraMap K L).toMonoidHom c) ^ p := by
    rw [kummerRoot_pow, ← hc, map_pow]
  rw [kummerRatio, kummerRatio_congr hζu σ hp, map_algebraMap_units σ c, div_self']

/-- If the Kummer character of `d` is trivial, then `d` is a `p`-th power in `K`. -/
private lemma mem_pthPower_of_kummerChar_eq_one (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p)
    {d : kummerGenerators K L p} (h : kummerChar hζu d = 1) :
    (d : Kˣ) ∈ pthPowerSubgroup Kˣ p := by
  have hfix : ∀ σ : L ≃ₐ[K] L, σ ((kummerRoot d : Lˣ) : L) = ((kummerRoot d : Lˣ) : L) := by
    intro σ
    have hσ : kummerChar hζu d σ = 1 := by rw [h]; rfl
    have hσ1 : Units.map σ.toRingEquiv.toMonoidHom (kummerRoot d) / kummerRoot d = 1 := by
      have := congrArg (fun u : rootsOfUnity p L => (u : Lˣ)) hσ
      simpa [kummerChar, kummerRatio] using this
    have hx : Units.map σ.toRingEquiv.toMonoidHom (kummerRoot d) = kummerRoot d :=
      div_eq_one.mp hσ1
    have := congrArg (fun u : Lˣ => (u : L)) hx
    simpa [Units.coe_map] using this
  have hmem : ((kummerRoot d : Lˣ) : L) ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed _).mpr hfix
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hmem
  have ha0 : a ≠ 0 := by
    intro h0
    have hz : ((kummerRoot d : Lˣ) : L) = 0 := by rw [← ha, h0, map_zero]
    exact Units.ne_zero (kummerRoot d) hz
  let c : Kˣ := Units.mk0 a ha0
  have hc : Units.map (algebraMap K L).toMonoidHom c = kummerRoot d := by
    apply Units.ext
    rw [Units.coe_map, Units.val_mk0]
    exact ha
  refine mem_pthPowerSubgroup.mpr ⟨c, ?_⟩
  apply (Units.map_injective (RingHom.injective (algebraMap K L)))
  rw [map_pow, hc, kummerRoot_pow]

/-- `kummerChar` is multiplicative in the generator. -/
private lemma kummerChar_mul (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p)
    (d1 d2 : kummerGenerators K L p) :
    kummerChar hζu (d1 * d2) = kummerChar hζu d1 * kummerChar hζu d2 := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  show kummerRatio (d1 * d2) σ = kummerRatio d1 σ * kummerRatio d2 σ
  have hp : kummerRoot (d1 * d2) ^ p = (kummerRoot d1 * kummerRoot d2) ^ p := by
    rw [kummerRoot_pow (d1 * d2), mul_pow, kummerRoot_pow d1, kummerRoot_pow d2]
    simp
  rw [kummerRatio, kummerRatio, kummerRatio, kummerRatio_congr hζu σ hp, map_mul,
    ← div_mul_div_comm]

private lemma kummerChar_one (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p) :
    kummerChar hζu (1 : kummerGenerators K L p) = 1 := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  show kummerRatio 1 σ = 1
  have hp : kummerRoot (1 : kummerGenerators K L p) ^ p = (1 : Lˣ) ^ p := by
    rw [kummerRoot_pow]; simp
  rw [kummerRatio, kummerRatio_congr hζu σ hp, map_one, div_self']

/-- The Kummer pairing `Δ → Hom(Gal(L/K), μ_p(L))`. -/
private def kummerPairingHom (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p) :
    kummerGenerators K L p →* ((L ≃ₐ[K] L) →* rootsOfUnity p L) where
  toFun d := kummerChar hζu d
  map_one' := kummerChar_one hζu
  map_mul' := kummerChar_mul hζu

/-- The kernel of the Kummer pairing is the subgroup of `p`-th powers. -/
private lemma ker_kummerPairingHom (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p) :
    (kummerPairingHom hζu).ker
      = (pthPowerSubgroup Kˣ p).comap (kummerGenerators K L p).subtype := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact mem_pthPower_of_kummerChar_eq_one hζu hx
  · intro x hx
    rw [MonoidHom.mem_ker]
    exact kummerChar_eq_one_of_mem hζu hx

/-- **Hilbert 90 / resolvent**: every character of `Gal(L/K)` with values in `μ_p(L)` is the
Kummer character of some element of `L`. -/
private lemma exists_resolvent (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p)
    (χ : (L ≃ₐ[K] L) →* rootsOfUnity p L) :
    ∃ α : Lˣ, ∀ σ : L ≃ₐ[K] L, Units.map σ.toRingEquiv.toMonoidHom α
      = (χ σ : rootsOfUnity p L) * α := by
  let χv : (L ≃ₐ[K] L) →* Lˣ := (rootsOfUnity p L).subtype.comp χ
  have hχv_mem : ∀ σ : L ≃ₐ[K] L, χv σ ∈ rootsOfUnity p L := fun σ => (χ σ).2
  have hli : LinearIndependent L (fun σ : L ≃ₐ[K] L => (σ.toAlgHom).toLinearMap) :=
    (linearIndependent_toLinearMap K L L).comp (fun σ : L ≃ₐ[K] L => σ.toAlgHom)
      AlgEquiv.coe_toAlgHom_injective
  have hex : ∃ c : L, (∑ σ : L ≃ₐ[K] L, ((χv σ : Lˣ) : L)⁻¹ * σ c) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hzero :
        (∑ σ : L ≃ₐ[K] L, ((χv σ : Lˣ) : L)⁻¹ • (σ.toAlgHom).toLinearMap) = 0 := by
      ext x
      simpa [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h x
    have hcoef :=
      (Fintype.linearIndependent_iff.mp hli) (fun σ => ((χv σ : Lˣ) : L)⁻¹) hzero
    have h1 := hcoef 1
    have hone : ((χv 1 : Lˣ) : L)⁻¹ = (1 : L) := by rw [map_one χv, Units.val_one, inv_one]
    rw [hone] at h1
    exact one_ne_zero h1
  obtain ⟨c₀, hc₀⟩ := hex
  let α : Lˣ := Units.mk0 (∑ σ : L ≃ₐ[K] L, ((χv σ : Lˣ) : L)⁻¹ * σ c₀) hc₀
  have hα : (α : L) = ∑ σ : L ≃ₐ[K] L, ((χv σ : Lˣ) : L)⁻¹ * σ c₀ := Units.val_mk0 hc₀
  have hσ : ∀ σ : L ≃ₐ[K] L, Units.map σ.toRingEquiv.toMonoidHom α = χv σ * α := by
    intro σ
    apply Units.ext
    rw [Units.coe_map, Units.val_mul, hα]
    show σ (∑ τ : L ≃ₐ[K] L, ((χv τ : Lˣ) : L)⁻¹ * τ c₀)
      = ((χv σ : Lˣ) : L) * ∑ τ : L ≃ₐ[K] L, ((χv τ : Lˣ) : L)⁻¹ * τ c₀
    have hsum : σ (∑ τ : L ≃ₐ[K] L, ((χv τ : Lˣ) : L)⁻¹ * τ c₀)
        = ∑ τ : L ≃ₐ[K] L, ((χv τ : Lˣ) : L)⁻¹ * (σ * τ) c₀ := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have hfix := apply_rootsOfUnity hζu σ (hχv_mem τ)
      rw [map_mul, map_inv₀, hfix, ← AlgEquiv.mul_apply]
    rw [hsum]
    have hreindex : (∑ τ : L ≃ₐ[K] L, ((χv τ : Lˣ) : L)⁻¹ * (σ * τ) c₀)
        = ∑ ρ : L ≃ₐ[K] L, ((χv (σ⁻¹ * ρ) : Lˣ) : L)⁻¹ * ρ c₀ := by
      rw [← Equiv.sum_comp (Equiv.mulLeft σ)
        (fun ρ : L ≃ₐ[K] L => ((χv (σ⁻¹ * ρ) : Lˣ) : L)⁻¹ * ρ c₀)]
      refine Finset.sum_congr rfl fun τ _ => ?_
      show ((χv τ : Lˣ) : L)⁻¹ * (σ * τ) c₀
        = ((χv (σ⁻¹ * (σ * τ)) : Lˣ) : L)⁻¹ * (σ * τ) c₀
      rw [inv_mul_cancel_left]
    rw [hreindex]
    have hcoef : ∀ ρ : L ≃ₐ[K] L,
        ((χv (σ⁻¹ * ρ) : Lˣ) : L)⁻¹
          = ((χv σ : Lˣ) : L) * ((χv ρ : Lˣ) : L)⁻¹ := by
      intro ρ
      have h1 : ((χv (σ⁻¹ * ρ) : Lˣ) : L)
          = ((χv σ : Lˣ) : L)⁻¹ * ((χv ρ : Lˣ) : L) := by
        rw [map_mul, map_inv]
        simp
      rw [h1, mul_inv_rev, inv_inv]
      exact mul_comm _ _
    rw [Finset.sum_congr rfl fun ρ _ => by rw [hcoef ρ]]
    rw [show (∑ ρ : L ≃ₐ[K] L,
            ((χv σ : Lˣ) : L) * ((χv ρ : Lˣ) : L)⁻¹ * ρ c₀)
          = ∑ ρ : L ≃ₐ[K] L,
            ((χv σ : Lˣ) : L) * (((χv ρ : Lˣ) : L)⁻¹ * ρ c₀) from
        Finset.sum_congr rfl fun ρ _ => mul_assoc _ _ _, Finset.mul_sum]
  refine ⟨α, fun σ => ?_⟩
  exact hσ σ

/-- The Kummer pairing is surjective. -/
private lemma kummerPairingHom_surjective (hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p) :
    Function.Surjective (kummerPairingHom (K := K) (L := L) (p := p) hζu) := by
  intro χ
  obtain ⟨α, hασ⟩ := exists_resolvent hζu χ
  have hαp_fixed : ∀ σ : L ≃ₐ[K] L, σ ((α : L) ^ p) = (α : L) ^ p := by
    intro σ
    have hval : σ (α : L) = (((χ σ : rootsOfUnity p L) : Lˣ) : L) * (α : L) := by
      have h := congrArg (fun u : Lˣ => (u : L)) (hασ σ)
      simpa [Units.coe_map, Units.val_mul] using h
    have hχp : (((χ σ : rootsOfUnity p L) : Lˣ) : L) ^ p = 1 := by
      have hmem : ((χ σ : rootsOfUnity p L) : Lˣ) ^ p = 1 :=
        (mem_rootsOfUnity p (((χ σ : rootsOfUnity p L) : Lˣ))).mp (χ σ).2
      simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Lˣ => (u : L)) hmem
    rw [map_pow, hval, mul_pow, hχp, one_mul]
  obtain ⟨a, ha⟩ : ∃ a : K, algebraMap K L a = (α : L) ^ p :=
    IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hαp_fixed)
  have ha0 : a ≠ 0 := by
    intro h0
    have hz : (α : L) ^ p = 0 := by rw [← ha, h0, map_zero]
    exact (pow_ne_zero p (Units.ne_zero α)) hz
  let d : Kˣ := Units.mk0 a ha0
  have hdval : (d : K) = a := Units.val_mk0 ha0
  have hd : d ∈ kummerGenerators K L p := by
    refine mem_pthPowerSubgroup.mpr ⟨α, ?_⟩
    apply Units.ext
    rw [Units.coe_map, hdval, Units.val_pow_eq_pow_val]
    exact ha.symm
  let D : kummerGenerators K L p := ⟨d, hd⟩
  refine ⟨D, ?_⟩
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  show kummerRatio D σ = ((χ σ : rootsOfUnity p L) : Lˣ)
  have hp : kummerRoot D ^ p = α ^ p := by
    rw [kummerRoot_pow]
    apply Units.ext
    rw [Units.coe_map, show ((D : Kˣ) : K) = a from hdval, Units.val_pow_eq_pow_val]
    exact ha
  rw [kummerRatio, kummerRatio_congr hζu σ hp, hασ σ, mul_div_cancel_right]

end Main

/-- **Kummer duality.**  If `K` contains a primitive `p`-th root of unity `ζ` and `L/K` is a
finite Galois extension, then the group of Kummer generator classes `(Lˣ^p ∩ Kˣ)/Kˣ^p` is
isomorphic to the group of homomorphisms `Gal(L/K) → μ_p(L)`. -/
theorem kummer_equiv (p : ℕ) (hp : p.Prime) {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ p) :
    Nonempty (Work.CFT.Kummer.kummerGeneratorsQuotient K L p ≃*
      ((L ≃ₐ[K] L) →* rootsOfUnity p L)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζu : IsPrimitiveRoot (zetaL (K := K) (L := L) ζ) p :=
    hζ.map_of_injective (Units.map_injective (RingHom.injective (algebraMap K L)))
  have hker := ker_kummerPairingHom (K := K) (L := L) (p := p) hζu
  exact ⟨QuotientGroup.liftEquiv
    ((pthPowerSubgroup Kˣ p).comap (kummerGenerators K L p).subtype)
    (kummerPairingHom_surjective (K := K) (L := L) (p := p) hζu) hker.symm⟩

end Work.CFT.Kummer
