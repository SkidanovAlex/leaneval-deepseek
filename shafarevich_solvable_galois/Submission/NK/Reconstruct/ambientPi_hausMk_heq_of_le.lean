import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Submission.NK.Reconstruct.lemma4f4_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Descending the Shimizu identity `σ̄ ∘ π_{L/K₁} = π_{L/K₂}` to a sublevel

Let `Ω` be a separable closure of `ℚ`, `K₁ K₂ L N` finite Galois levels of `Ω/ℚ` with
`K₁.L, K₂.L ⊆ N.L ⊆ L.L`, and `σ̄ : Γ_{K₁} ≃* Γ_{K₂}` an isomorphism of Shimizu's ℓ-adic
abelianisations (`NK.Reconstruct.Gamma`).  The main theorem of this file,

`NK.Reconstruct.ambientPi_hausMk_heq_of_le`,

says that if the identity `σ̄ ∘ π_{L/K₁} = π_{L/K₂}` holds on `Γ_L` *after* passing to the
Hausdorff torsion-free quotient `Γ^{tf}` (`NK.Reconstruct.gammaHausMk`, the quotient of
`NK.Reconstruct.Gamma` by the subgroup invisible to every continuous homomorphism into `ℤ_ℓ`),
then it holds *a fortiori* on the smaller level `N ⊆ L`:

`gammaHausMk (σ̄ (π_{N/K₁} γ)) = gammaHausMk (π_{N/K₂} γ)` for every `γ ∈ Γ_N`.

## The argument

This is the "open subgroup" step of Shimizu's Lemma 4f.4 (arXiv:2009.10431), run on the
torsion-free quotient instead of on `Γ` itself:

* the base-change map is transitive, `π_{L/K} = π_{N/K} ∘ π_{L/N}` for
  `K ⊆ N ⊆ L` (`NK.Reconstruct.ambientPi_comp`, proved here from
  `NK.Reconstruct.gammaBaseChangeHom_galToGamma` and the surjectivity of
  `NK.Reconstruct.galToGamma`);
* by `NK.Reconstruct.finite_coker_gammaBaseChangeHom` the cokernel of `π_{L/N} : Γ_L → Γ_N` is
  finite, so for `m := #Γ_{L,ℓ}` (the order of the finite ℓ-part of `Gal(L/N)^{ab}`) every
  `γ ∈ Γ_N` satisfies `γ ^ m ∈ range π_{L/N}`: pick `γ' ∈ Γ_L` with `π_{L/N} γ' = γ ^ m`;
* transitivity turns the identity at `γ'` into `(σ̄ (π_{N/K₁} γ))^m = (π_{N/K₂} γ)^m` in the
  torsion-free group `Γ_{K₂}^{tf}`, i.e. `(gammaHausMk (σ̄ π_{N/K₁}γ) · (gammaHausMk (π_{N/K₂}γ))⁻¹)^m = 1`;
* `Γ^{tf}` being torsion-free (`NK.Reconstruct.gammaHaus_pow_eq_one`), the `m`-th power of the
  discrepancy is trivial only if the discrepancy is.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-! ## Transitivity of the base change -/

/-- **Transitivity of Shimizu's base change `π_{L/K} : Γ_L → Γ_K`**: for finite Galois levels
`K ⊆ N ⊆ L` of `Ω/ℚ` the base change of the largest level factors through the intermediate one,

`π_{L/K} = π_{N/K} ∘ π_{L/N}`.

This is the functoriality of restriction of scalars on the ℓ-adic abelianisations.  It is proved by
testing against `galToGamma` (`NK.Reconstruct.galToGamma_surjective`): both composites send an
automorphism `σ` of `Ω/↥L.L` to the ℓ-adic abelianisation of the restriction of `σ` to `Ω/↥K.L`,
which does not depend on whether one restricts first to `Ω/↥N.L`
(`NK.Reconstruct.gammaBaseChangeHom_galToGamma`). -/
theorem ambientPi_comp (K N L : FrobLevel ℚ Ω) [IsSepClosure ↥(K.L) Ω]
    [IsSepClosure ↥(N.L) Ω] (hK : K.L ≤ N.L) (hNL : N.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    (ambientPi (NumFieldIn.ofFrobLevel K) N hK ℓ).comp
      (ambientPi (NumFieldIn.ofFrobLevel N) L hNL ℓ)
      = ambientPi (NumFieldIn.ofFrobLevel K) L (hK.trans hNL) ℓ := by
  refine MonoidHom.ext fun f => ?_
  obtain ⟨σ, rfl⟩ := galToGamma_surjective (K := ↥(L.L)) (K' := Ω) ℓ f
  rw [MonoidHom.comp_apply]
  have h1 : ambientPi (NumFieldIn.ofFrobLevel N) L hNL ℓ (galToGamma (K := ↥(L.L)) (K' := Ω) ℓ σ)
      = galToGamma (K := ↥(N.L)) (K' := Ω) ℓ (galRestrict hNL σ) :=
    gammaBaseChangeHom_galToGamma (K := ↥(N.L)) (K' := Ω) ℓ (levelExtendGen (NumFieldIn.ofFrobLevel N) L hNL) σ
  rw [h1]
  have h2 : ambientPi (NumFieldIn.ofFrobLevel K) N hK ℓ (galToGamma (K := ↥(N.L)) (K' := Ω) ℓ (galRestrict hNL σ))
      = galToGamma (K := ↥(K.L)) (K' := Ω) ℓ (galRestrict hK (galRestrict hNL σ)) :=
    gammaBaseChangeHom_galToGamma (K := ↥(K.L)) (K' := Ω) ℓ (levelExtend K N hK) (galRestrict hNL σ)
  rw [h2]
  have h3 : ambientPi (NumFieldIn.ofFrobLevel K) L (hK.trans hNL) ℓ (galToGamma (K := ↥(L.L)) (K' := Ω) ℓ σ)
      = galToGamma (K := ↥(K.L)) (K' := Ω) ℓ (galRestrict (hK.trans hNL) σ) :=
    gammaBaseChangeHom_galToGamma (K := ↥(K.L)) (K' := Ω) ℓ (levelExtend K L (hK.trans hNL)) σ
  rw [h3]
  exact congrArg (galToGamma (K := ↥(K.L)) (K' := Ω) ℓ) (AlgEquiv.ext (fun x => rfl))

/-- **The identity `σ̄ ∘ π_{L/K₁} = π_{L/K₂}` on `Γ_L` descends to the sublevel `N ⊆ L`**, after
passing to the Hausdorff torsion-free quotients `Γ^{tf} = NK.Reconstruct.GammaHaus`.

Since the cokernel of `π_{L/N} : Γ_L → Γ_N` is finite, every `γ ∈ Γ_N` has a power `γ ^ m` in the
image of `π_{L/N}`; the identity at the corresponding `γ' ∈ Γ_L` gives the `m`-th powers of the two
sides equal in the torsion-free group `Γ_{K₂}^{tf}`, whence the sides themselves are equal
(`NK.Reconstruct.gammaHaus_pow_eq_one`). -/
theorem ambientPi_hausMk_heq_of_le {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K₁ K₂ L N : FrobLevel ℚ Ω) [IsSepClosure ↥(K₁.L) Ω] [IsSepClosure ↥(K₂.L) Ω]
    [IsSepClosure ↥(N.L) Ω]
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (hN₁ : K₁.L ≤ N.L) (hN₂ : K₂.L ≤ N.L) (hNL : N.L ≤ L.L)
    (ℓ : ℕ) [Fact ℓ.Prime] (σbar : Gamma ↥(K₁.L) Ω ℓ ≃* Gamma ↥(K₂.L) Ω ℓ)
    (heq : ∀ (γ : Gamma ↥(L.L) Ω ℓ),
      gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar (ambientPi (NumFieldIn.ofFrobLevel K₁) L h₁ ℓ γ))
        = gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (ambientPi (NumFieldIn.ofFrobLevel K₂) L h₂ ℓ γ))
    (γ : Gamma ↥(N.L) Ω ℓ) :
    gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar (ambientPi (NumFieldIn.ofFrobLevel K₁) N hN₁ ℓ γ))
      = gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (ambientPi (NumFieldIn.ofFrobLevel K₂) N hN₂ ℓ γ) := by
  -- The exponent killing the finite cokernel of `π_{L/N}`.
  let m : ℕ := Nat.card (LevelEllPart (K := ↥(N.L)) (K' := Ω) (levelExtendGen (NumFieldIn.ofFrobLevel N) L hNL).L ℓ)
  have hm : m ≠ 0 := (Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩).ne'
  -- `γ ^ m` lies in the range of `π_{L/N}`: it lies in the kernel of the projection to the
  -- finite level `L` of `N`.
  have hmem : γ ^ m ∈ (ambientPi (NumFieldIn.ofFrobLevel N) L hNL ℓ).range := by
    have hker : γ ^ m ∈
        (Gamma.proj (K := ↥(N.L)) (K' := Ω) (ℓ := ℓ) (levelExtendGen (NumFieldIn.ofFrobLevel N) L hNL)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      simpa [m] using
        pow_card_eq_one' (x := Gamma.proj (K := ↥(N.L)) (K' := Ω) (ℓ := ℓ) (levelExtendGen (NumFieldIn.ofFrobLevel N) L hNL) γ)
    rwa [ker_proj_eq_range_gammaBaseChangeHom ℓ (levelExtendGen (NumFieldIn.ofFrobLevel N) L hNL)] at hker
  obtain ⟨γ', hγ'⟩ := hmem
  -- Transitivity of the base change: `π_{N/K}(π_{L/N} γ') = π_{L/K} γ'`.
  have hcomp₁ := ambientPi_comp K₁ N L hN₁ hNL ℓ
  have hcomp₂ := ambientPi_comp K₂ N L hN₂ hNL ℓ
  have key₁ : (ambientPi (NumFieldIn.ofFrobLevel K₁) N hN₁ ℓ γ) ^ m = ambientPi (NumFieldIn.ofFrobLevel K₁) L h₁ ℓ γ' := by
    rw [← map_pow, ← hγ']
    exact DFunLike.congr_fun hcomp₁ γ'
  have key₂ : (ambientPi (NumFieldIn.ofFrobLevel K₂) N hN₂ ℓ γ) ^ m = ambientPi (NumFieldIn.ofFrobLevel K₂) L h₂ ℓ γ' := by
    rw [← map_pow, ← hγ']
    exact DFunLike.congr_fun hcomp₂ γ'
  -- The `m`-th powers of the two sides agree in `Γ_{K₂}^{tf}`, by the hypothesis at `γ'`.
  have hpow : (gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar (ambientPi (NumFieldIn.ofFrobLevel K₁) N hN₁ ℓ γ))) ^ m
      = (gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (ambientPi (NumFieldIn.ofFrobLevel K₂) N hN₂ ℓ γ)) ^ m := by
    rw [← map_pow, ← map_pow (f := σbar), key₁, heq γ', ← key₂, map_pow]
  -- `Γ_{K₂}^{tf}` is torsion-free, so the discrepancy itself is trivial.
  have hratio : gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar (ambientPi (NumFieldIn.ofFrobLevel K₁) N hN₁ ℓ γ))
      * (gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (ambientPi (NumFieldIn.ofFrobLevel K₂) N hN₂ ℓ γ))⁻¹ = 1 := by
    refine gammaHaus_pow_eq_one (y := gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
      (σbar (ambientPi (NumFieldIn.ofFrobLevel K₁) N hN₁ ℓ γ))
      * (gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (ambientPi (NumFieldIn.ofFrobLevel K₂) N hN₂ ℓ γ))⁻¹) hm ?_
    rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  exact mul_inv_eq_one.mp hratio

end NK.Reconstruct
