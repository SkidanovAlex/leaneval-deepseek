import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.InvAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open NumberField

/-- Two ring homs `Ω →+* ℂ` that agree on the base field `k` differ by a `k`-algebra
automorphism of the algebraic closure `Ω`. -/
theorem exists_algEquiv_of_comp_eq {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (ψ φ' : Ω →+* ℂ)
    (h : ψ.comp (algebraMap k Ω) = φ'.comp (algebraMap k Ω)) :
    ∃ ρ : Ω ≃ₐ[k] Ω, φ' = ψ.comp ρ.toRingHom := by
  letI : Algebra k ℂ := (ψ.comp (algebraMap k Ω)).toAlgebra
  have hψal : ∀ x : k, ψ (algebraMap k Ω x) = algebraMap k ℂ x :=
    fun x => (RingHom.congr_fun (RingHom.algebraMap_toAlgebra (ψ.comp (algebraMap k Ω))) x).symm
  have hφal : ∀ x : k, φ' (algebraMap k Ω x) = algebraMap k ℂ x :=
    fun x => ((RingHom.congr_fun h x).symm).trans (hψal x)
  let Ψ : Ω →ₐ[k] ℂ := AlgHom.mk ψ hψal
  let Φ : Ω →ₐ[k] ℂ := AlgHom.mk φ' hφal
  let A : IntermediateField k ℂ := algebraicClosure k ℂ
  have hΩalg : algebraicClosure k Ω = ⊤ :=
    (algebraicClosure.eq_top_iff k Ω).2 IsAlgClosure.isAlgebraic
  have hmemΨ : ∀ x : Ω, Ψ x ∈ A := by
    intro x
    exact (map_mem_algebraicClosure_iff Ψ).2 (by rw [hΩalg]; exact trivial)
  have hmemΦ : ∀ x : Ω, Φ x ∈ A := by
    intro x
    exact (map_mem_algebraicClosure_iff Φ).2 (by rw [hΩalg]; exact trivial)
  let ΨA : Ω →ₐ[k] A := Ψ.codRestrict A.toSubalgebra hmemΨ
  let ΦA : Ω →ₐ[k] A := Φ.codRestrict A.toSubalgebra hmemΦ
  haveI : IsAlgClosure k A := inferInstance
  have hbijΨ : Function.Bijective ΨA :=
    (Algebra.IsAlgebraic.algHom_bijective₂ ΨA (IsAlgClosure.equiv k Ω A).symm.toAlgHom).1
  have hbijΦ : Function.Bijective ΦA :=
    (Algebra.IsAlgebraic.algHom_bijective₂ ΦA (IsAlgClosure.equiv k Ω A).symm.toAlgHom).1
  refine ⟨(AlgEquiv.ofBijective ΦA hbijΦ).trans (AlgEquiv.ofBijective ΨA hbijΨ).symm, ?_⟩
  ext x
  have key : (AlgEquiv.ofBijective ΨA hbijΨ)
      ((AlgEquiv.ofBijective ΨA hbijΨ).symm
        ((AlgEquiv.ofBijective ΦA hbijΦ) x)) = (AlgEquiv.ofBijective ΦA hbijΦ) x :=
    AlgEquiv.apply_symm_apply _ _
  have key2 := congr_arg (Subtype.val) key
  have key3 : ψ (((AlgEquiv.ofBijective ΦA hbijΦ).trans (AlgEquiv.ofBijective ΨA hbijΨ).symm) x)
      = φ' x := by
    rw [AlgEquiv.trans_apply]
    exact key2
  exact key3.symm

/-- If `φt ∘ c = conj ∘ φt`, `φ' ∘ c' = conj ∘ φ'` and `φ' = φt ∘ τ` then `c' = τ⁻¹ c τ`. -/
theorem seam_conj {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (c c' τ : Ω ≃ₐ[k] Ω) (φt φ' : Ω →+* ℂ)
    (hc : ∀ x : Ω, φt (c x) = starRingEnd ℂ (φt x))
    (hc' : ∀ x : Ω, φ' (c' x) = starRingEnd ℂ (φ' x))
    (hφ : ∀ x : Ω, φ' x = φt (τ x)) :
    c' = τ⁻¹ * c * τ := by
  have hinj : Function.Injective φt := RingHom.injective φt
  have h1 : ∀ x : Ω, φt (τ (c' x)) = φt (c (τ x)) := by
    intro x
    rw [← hφ (c' x), hc' x, hφ x, hc (τ x)]
  have h2 : ∀ x : Ω, (τ * c') x = (c * τ) x := by
    intro x
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    exact hinj (h1 x)
  have h3 : τ * c' = c * τ := AlgEquiv.ext h2
  calc c' = 1 * c' := by rw [one_mul]
    _ = (τ⁻¹ * τ) * c' := by rw [inv_mul_cancel]
    _ = τ⁻¹ * (τ * c') := by rw [mul_assoc]
    _ = τ⁻¹ * (c * τ) := by rw [h3]
    _ = τ⁻¹ * c * τ := by rw [mul_assoc]

/-- Involutions with Galois-conjugate linked places are conjugate.  If `c, c'` are involutions
`≠ 1` of `Ω/k` with seam embeddings `φ, φ'` (`φ ∘ c = conj ∘ φ`, `φ' ∘ c' = conj ∘ φ'`), and
`σ • mk (φ|_K) = mk (φ'|_K)` for some `σ ∈ Gal(K/k)`, then `c' = τ c τ⁻¹` for some `τ ∈ Gal(Ω/k)`.
With `hCdisj` this makes the places `wc c` (`c ∈ C`) lie in pairwise distinct `Gal(K/k)`-orbits.

Route.  Lift `σ` to `τ₀ ∈ Gal(Ω/k)` (`AlgEquiv.restrictNormalHom_surjective`).  The hypothesis and
`NumberField.InfinitePlace.mk_eq_iff` give `φ'|_K = ψ|_K` or `φ'|_K = conj ∘ ψ|_K` with
`ψ = φ ∘ τ₀⁻¹`.  Replace `φ` by `conj ∘ φ` in the second case (it is still a seam embedding for `c`).
Two embeddings of `Ω` into `ℂ` that agree on `K` differ by `ρ ∈ Gal(Ω/K)`: both images are the
algebraic closure of the image of `K` in `ℂ`, so `ρ := ψ⁻¹ ∘ φ'` is defined (`IsAlgClosure`,
`AlgEquiv.ofInjective`-style).  So `φ' = φ ∘ τ` with `τ = τ₀⁻¹ ρ`, and
`φ ∘ τ ∘ c' = conj ∘ φ ∘ τ = φ ∘ c ∘ τ`; injectivity of `φ` gives `c' = τ⁻¹ c τ`. -/
theorem wc_orbit_injective (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (c c' : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (hc'2 : c' ^ 2 = 1) (hc'1 : c' ≠ 1) (φ φ' : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hφ' : ∀ x : Ω, φ' (c' x) = starRingEnd ℂ (φ' x)) (σ : ↥K ≃ₐ[k] ↥K)
    (hσ : σ • NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω))) =
      NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ'.comp (algebraMap (↥K) Ω)))) :
    ∃ τ : Ω ≃ₐ[k] Ω, c' = τ * c * τ⁻¹ := by
  obtain ⟨τ₀, hτ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥K) Ω σ
  have hsymm : ∀ x : ↥K, τ₀.symm ((algebraMap (↥K) Ω) x) = (algebraMap (↥K) Ω) (σ.symm x) := by
    intro x
    have h := AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K τ₀ (σ.symm x)
    rw [hτ₀, AlgEquiv.apply_symm_apply] at h
    have h' : (algebraMap (↥K) Ω) x = τ₀ ((algebraMap (↥K) Ω) (σ.symm x)) := by
      simpa only [IntermediateField.algebraMap_apply] using h
    rw [h', AlgEquiv.symm_apply_apply]
  have hcomp : (algebraMap (↥K) Ω).comp (σ.symm : ↥K →+* ↥K)
      = (τ₀.symm : Ω →+* Ω).comp (algebraMap (↥K) Ω) := by
    ext x
    change (algebraMap (↥K) Ω) (σ.symm x) = τ₀.symm ((algebraMap (↥K) Ω) x)
    exact (hsymm x).symm
  have hmk : NumberField.InfinitePlace.mk ((φ.comp (τ₀.symm : Ω →+* Ω)).comp (algebraMap (↥K) Ω))
      = NumberField.InfinitePlace.mk (φ'.comp (algebraMap (↥K) Ω)) := by
    have step : σ • NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω))
        = NumberField.InfinitePlace.mk ((φ.comp (τ₀.symm : Ω →+* Ω)).comp (algebraMap (↥K) Ω)) := by
      rw [NumberField.InfinitePlace.smul_mk]
      congr 1
      simp only [RingHom.comp_assoc, hcomp]
    have hσ' := hσ
    rw [NK.GlobalCFT.Place.smul_ofInfinite] at hσ'
    have hσ'' := NK.GlobalCFT.Place.ofInfinite_inj.mp hσ'
    rw [← step, hσ'']
  rw [NumberField.InfinitePlace.mk_eq_iff] at hmk
  have hmain : ∃ φt : Ω →+* ℂ,
      (∀ x : Ω, φt (c x) = starRingEnd ℂ (φt x)) ∧
      (((φt.comp (τ₀.symm : Ω →+* Ω)).comp (algebraMap (↥K) Ω)) = φ'.comp (algebraMap (↥K) Ω)) := by
    rcases hmk with hcase | hcase
    · exact ⟨φ, hφ, hcase⟩
    · exact ⟨ComplexEmbedding.conjugate φ,
        (by intro x
            rw [ComplexEmbedding.conjugate_coe_eq φ (c x),
                ComplexEmbedding.conjugate_coe_eq φ x, hφ x]), hcase⟩
  obtain ⟨φt, hseam, hagree⟩ := hmain
  have hk : (φt.comp (τ₀.symm : Ω →+* Ω)).comp (algebraMap k Ω) = φ'.comp (algebraMap k Ω) := by
    ext x
    have := RingHom.congr_fun hagree (algebraMap k ↥K x)
    simpa only [RingHom.comp_apply, IsScalarTower.algebraMap_apply k ↥K Ω] using this
  obtain ⟨ρ, hρ⟩ := exists_algEquiv_of_comp_eq (φt.comp (τ₀.symm : Ω →+* Ω)) φ' hk
  refine ⟨(τ₀.symm * ρ)⁻¹, ?_⟩
  have hφτ : ∀ x : Ω, φ' x = φt ((τ₀.symm * ρ) x) := by
    intro x
    have h1 : ((φt.comp (τ₀.symm : Ω →+* Ω)).comp ρ.toRingHom) x = φt ((τ₀.symm * ρ) x) := by
      simp only [RingHom.comp_apply, AlgEquiv.mul_apply]
      rfl
    rw [← h1]
    exact RingHom.congr_fun hρ x
  have hc := seam_conj c c' (τ₀.symm * ρ) φt φ' hseam hφ' hφτ
  rw [hc, inv_inv]

end Work.SSGRoute.PT
