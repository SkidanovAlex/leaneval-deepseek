/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A finite subextension of `κ^tr / κ^ur` has degree prime to `p`

Let `κ = K_𝔭` be a `p`-adic field (`p = resCharAt 𝔭` its residue characteristic), `K'` a separable
closure of `κ`, `U₀ = κ^{ur}` the maximal unramified extension (`unramifiedClosure p`) and
`T = κ^{tr} = κ^{ur}(π^{1/n} : (n,p) = 1)` the maximal tamely ramified extension
(`tameClosure p π`), for a uniformiser `π` of `κ`.

The main result of this file is `coprime_finrank_of_le_tameClosure`: **every finite subextension
`L/κ^{ur}` of `κ^{tr}/κ^{ur}` has degree prime to `p`**.  This is the arithmetic input of the
pro-prime-to-`p`-ness of the tame inertia `I_κ/V_κ = Gal(κ^{tr}/κ^{ur})`
(`isProPrimeToP_of_openNormal_index`).

The proof: by the primitive element theorem, `L = κ^{ur}⟮α⟯` for a single `α`, and
`exists_kummerLayer_of_mem_tameClosure` puts `α` inside a Kummer layer `κ^{ur} ⊔ κ⟮β⟯` with
`β ^ n = π` and `p ∤ n`.  Hence `[L : κ^{ur}] ∣ [κ^{ur}⟮β⟯ : κ^{ur}]`, and the Kummer-degree bound
`[κ^{ur}⟮β⟯ : κ^{ur}] ∣ n` (the auxiliary lemma `kummer_finrank_dvd` below, proved by the classical
Kummer pairing `σ ↦ σβ/β ∈ μ_n`) gives `[L : κ^{ur}] ∣ n`, whence the coprimality with `p`.

-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.TameInertiaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Tame

noncomputable section

/-- **Kummer degree bound.**  Let `E/F` be a Galois extension, `n > 0`, `α ∈ E` with
`α ^ n = a` for some `a ∈ F` (an element of the *base* field, so that `Gal(E/F)` fixes `a`), and
assume that every `n`-th root of unity of `E` already lies in `F`.  Then
`[F⟮α⟯ : F] ∣ n`.

Indeed `σ ↦ σ α / α` is a group homomorphism `Gal(E/F) →* μ_n(E)` (it is multiplicative because
`τ α / α ∈ μ_n(E) ⊆ F` is fixed by `σ`), with kernel `F⟮α⟯.fixingSubgroup`; hence
`[F⟮α⟯ : F] = F⟮α⟯.fixingSubgroup.index = Nat.card (range)`, and the image lies in the cyclic
group `μ_n(E)`, whose cardinality divides `n`. -/
private theorem kummer_finrank_dvd {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsGalois F E] {n : ℕ} (hn : 0 < n) {a : F} {α : E}
    (hα : α ^ n = algebraMap F E a)
    (hμ : ∀ ζ : E, ζ ^ n = 1 → ζ ∈ (⊥ : IntermediateField F E)) :
    Module.finrank F ↥(F⟮α⟯) ∣ n := by
  classical
  by_cases hα0 : α = 0
  · -- the degenerate case `α = 0`, i.e. `a = 0`: then `F⟮α⟯ = ⊥` has degree `1`
    have hmem : α ∈ (⊥ : IntermediateField F E) := by
      rw [hα0]
      exact IntermediateField.mem_bot.mpr ⟨0, by simp⟩
    rw [IntermediateField.finrank_adjoin_simple_eq_one_iff.mpr hmem]
    exact one_dvd n
  · haveI : NeZero n := ⟨hn.ne'⟩
    have ha : algebraMap F E a ≠ 0 := by rw [← hα]; exact pow_ne_zero n hα0
    let L : IntermediateField F E := IntermediateField.adjoin F ({α} : Set E)
    have hαL : α ∈ L := IntermediateField.subset_adjoin F _ (Set.mem_singleton α)
    -- `σ α / α` is an `n`-th root of unity
    have hroot : ∀ σ : Gal(E/F), (σ α / α) ^ n = 1 := by
      intro σ
      have h1 : (σ α) ^ n = algebraMap F E a := by rw [← map_pow, hα, AlgEquiv.commutes]
      rw [div_pow, h1, hα, div_self ha]
    -- the Kummer homomorphism `σ ↦ σ α / α`
    let φ : Gal(E/F) →* rootsOfUnity n E :=
      { toFun := fun σ => rootsOfUnity.mkOfPowEq (σ α / α) (hroot σ)
        map_one' := by
          apply Subtype.ext; apply Units.ext
          simp only [rootsOfUnity.coe_mkOfPowEq, OneMemClass.coe_one, Units.val_one]
          rw [AlgEquiv.one_apply, div_self hα0]
        map_mul' := by
          intro σ τ
          apply Subtype.ext; apply Units.ext
          simp only [Subgroup.coe_mul, rootsOfUnity.coe_mkOfPowEq]
          obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp (hμ (τ α / α) (hroot τ))
          have hfix : σ (τ α / α) = τ α / α := by rw [← hy, AlgEquiv.commutes]
          have hσα : σ α ≠ 0 := fun h => hα0 (σ.injective (by rw [h, map_zero]))
          rw [AlgEquiv.mul_apply]
          calc σ (τ α) / α = σ (τ α / α) * (σ α / α) := by
                rw [map_div₀]; field_simp
            _ = (τ α / α) * (σ α / α) := by rw [hfix]
            _ = (σ α / α) * (τ α / α) := by ring }
    have hφ : ∀ σ : Gal(E/F), ((φ σ : Eˣ) : E) = σ α / α := fun σ => rfl
    -- the kernel of `φ` is the fixing subgroup of `F⟮α⟯`
    have hker : φ.ker = L.fixingSubgroup := by
      ext σ
      rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
      constructor
      · intro hσ x hx
        have hσα : σ α = α := by
          have h1 : σ α / α = 1 := by rw [← hφ σ, hσ]; simp
          exact (div_eq_one_iff_eq hα0).mp h1
        refine IntermediateField.adjoin_induction F (s := ({α} : Set E))
          (p := fun x _ => σ x = x) ?_ ?_ ?_ ?_ ?_ hx
        · intro x hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx, hσα]
        · intro x
          exact AlgEquiv.commutes σ x
        · intro x y _ _ hx hy
          rw [map_add, hx, hy]
        · intro x _ hx
          rw [map_inv₀, hx]
        · intro x y _ _ hx hy
          rw [map_mul, hx, hy]
      · intro hσ
        have hσα : σ α = α := hσ α hαL
        apply Subtype.ext; apply Units.ext
        simp only [OneMemClass.coe_one, Units.val_one]
        rw [hφ σ, hσα, div_self hα0]
    -- `[F⟮α⟯ : F] = Nat.card (range φ)`
    have hfin : Module.finrank F ↥L = Nat.card φ.range := by
      calc Module.finrank F ↥L = L.fixingSubgroup.index :=
            IntermediateField.finrank_eq_fixingSubgroup_index E L
        _ = φ.ker.index := by rw [hker]
        _ = Nat.card φ.range := Subgroup.index_ker φ
    rw [hfin]
    -- `Nat.card (range φ) ∣ Nat.card (μ_n(E)) ∣ n`
    refine (Subgroup.card_subgroup_dvd_card φ.range).trans ?_
    haveI : IsCyclic (rootsOfUnity n E) := inferInstance
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity n E)
    have hcard : Nat.card (rootsOfUnity n E) = orderOf g :=
      (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    rw [hcard]
    refine orderOf_dvd_iff_pow_eq_one.mpr ?_
    apply Subtype.ext
    simpa using (mem_rootsOfUnity n (g : Eˣ)).mp g.2

/-- **A finite subextension of `κ^{tr}/κ^{ur}` has degree prime to `p`.**

With `κ = K_𝔭` (`p = resCharAt 𝔭`), `U₀ = κ^{ur}` realised as
`NK.LocalAnabelian.unramifiedClosure p ⊆ K'` and `T = κ^{tr} = tameClosure p π`, every
intermediate field `L` of `K'/κ^{ur}` whose carrier lies in `κ^{tr}` and which is finite over
`κ^{ur}` satisfies `Nat.Coprime p [L : κ^{ur}]`. -/
theorem coprime_finrank_of_le_tameClosure {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K}
    (L : IntermediateField
      (↥(NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭))) K')
    (hL : (L : Set K') ⊆ ((NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K)
        (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭) π :
          IntermediateField (𝔭.adicCompletion K) K') : Set K'))
    [FiniteDimensional
      (↥(NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭))) L] :
    Nat.Coprime (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      (Module.finrank
        (↥(NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭))) L) := by
  classical
  let p : ℕ := NK.TameStructureDeep.Tame.resCharAt 𝔭
  have hp : p.Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  let U : IntermediateField (𝔭.adicCompletion K) K' :=
    NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') p
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI hfd : FiniteDimensional ↥U ↥L := inferInstance
  haveI hgal : IsGalois ↥U K' := IsGalois.tower_top_of_isGalois (𝔭.adicCompletion K) ↥U K'
  haveI hsep : Algebra.IsSeparable ↥U K' :=
    Algebra.isSeparable_tower_top_of_isSeparable (𝔭.adicCompletion K) ↥U K'
  haveI : Algebra.IsSeparable ↥U ↥L := Algebra.IsSeparable.of_algHom ↥U K' L.val
  -- a primitive element of `L` over `κ^{ur}`
  obtain ⟨α, hαtop⟩ := Field.exists_primitive_element ↥U ↥L
  have hL_eq : L = IntermediateField.adjoin ↥U ({α.1} : Set K') := by
    rw [← IntermediateField.lift_adjoin_simple (F := ↥U) L α, hαtop, IntermediateField.lift_top]
  -- `α` lies in `κ^{tr}`, hence in a Kummer layer `κ^{ur} ⊔ κ⟮β⟯`, `β ^ n = π`, `p ∤ n`
  have hαT : (α : K') ∈ NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K)
      (K' := K') p (π : 𝔭.adicCompletion K) := hL α.2
  obtain ⟨n, β, hn, hβ, hmem⟩ :=
    NK.TameStructureDeep.Tame.exists_kummerLayer_of_mem_tameClosure (κ := 𝔭.adicCompletion K)
      (K' := K') p hp hαT
  -- the Kummer layer is a subfield of `κ^{ur}⟮β⟯`
  have hle : (U ⊔ IntermediateField.adjoin (𝔭.adicCompletion K) ({β} : Set K')) ≤
      IntermediateField.restrictScalars (𝔭.adicCompletion K)
        (IntermediateField.adjoin ↥U ({β} : Set K')) := by
    rw [sup_le_iff]
    constructor
    · intro x hx
      rw [IntermediateField.mem_restrictScalars]
      have := IntermediateField.algebraMap_mem (IntermediateField.adjoin ↥U ({β} : Set K'))
        (⟨x, hx⟩ : ↥U)
      simpa using this
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx, IntermediateField.coe_restrictScalars]
      exact IntermediateField.subset_adjoin ↥U _ (Set.mem_singleton β)
  have hαβ : (α : K') ∈ (IntermediateField.adjoin ↥U ({β} : Set K') : Set K') := by
    have h := hle hmem
    rwa [IntermediateField.mem_restrictScalars] at h
  have hLle : L ≤ IntermediateField.adjoin ↥U ({β} : Set K') := by
    rw [hL_eq, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hαβ
  have hdvd1 : Module.finrank ↥U ↥L ∣
      Module.finrank ↥U ↥(IntermediateField.adjoin ↥U ({β} : Set K')) :=
    IntermediateField.finrank_dvd_of_le_right hLle
  -- the Kummer degree bound
  have hnpos : 0 < n := Nat.pos_of_ne_zero (fun h => hn (h ▸ dvd_zero p))
  have hβa : β ^ n = algebraMap ↥U K'
      (algebraMap (𝔭.adicCompletion K) ↥U (π : 𝔭.adicCompletion K)) := by
    rw [← IsScalarTower.algebraMap_apply (𝔭.adicCompletion K) ↥U K'
      (π : 𝔭.adicCompletion K)]
    exact hβ
  have hμ : ∀ ζ : K', ζ ^ n = 1 → ζ ∈ (⊥ : IntermediateField ↥U K') := by
    intro ζ hζ
    refine IntermediateField.mem_bot.mpr ⟨⟨ζ, ?_⟩, ?_⟩
    · exact NK.TameStructureDeep.Tame.mem_unramifiedClosure_of_pow_eq_one hn hζ
    · rfl
  have hdvd2 : Module.finrank ↥U ↥(IntermediateField.adjoin ↥U ({β} : Set K')) ∣ n :=
    kummer_finrank_dvd hnpos hβa hμ
  -- conclude
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  exact hn (hdvd.trans (hdvd1.trans hdvd2))

end

end NK.TameStructureDeep.Tame

