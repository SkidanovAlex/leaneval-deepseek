import Mathlib

set_option linter.style.haveILetI false

namespace NK.NUV2.LC.RouteB

/-- **The Kummer character of a `p`-th root.**  Let `k` be a field containing a primitive `p`-th root
of unity `ζ`, let `K'` be a separable closure of `k`, let `a ∈ kˣ` and let `α ∈ K'` satisfy
`α^p = a`.  Then there is a group homomorphism `χ : Gal(K'/k) →* Multiplicative (ZMod p)` whose
kernel is exactly the set of those `σ` with `σ α = α`. -/
theorem kummerCharacter {k K' : Type} [Field k] [Field K'] [Algebra k K'] [IsSepClosure k K']
    (p : ℕ) (hp : p.Prime) {ζ : k} (hζ : IsPrimitiveRoot ζ p) (a : kˣ) {α : K'}
    (hα : α ^ p = algebraMap k K' (a : k)) :
    ∃ χ : Gal(K'/k) →* Multiplicative (ZMod p),
      ∀ σ : Gal(K'/k), χ σ = 1 ↔ σ α = α := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- `ζ` remains a primitive `p`-th root of unity in `K'`
  have hζ' : IsPrimitiveRoot (algebraMap k K' ζ) p :=
    hζ.map_of_injective (algebraMap k K').injective
  have hζne : algebraMap k K' ζ ≠ 0 := hζ'.ne_zero hp.ne_zero
  -- the same root, viewed as a unit of `K'`
  let μ : K'ˣ := Units.mk0 (algebraMap k K' ζ) hζne
  have hμval : (↑μ : K') = algebraMap k K' ζ := Units.val_mk0 hζne
  have hμ' : IsPrimitiveRoot (↑μ : K') p := by rw [hμval]; exact hζ'
  have hμ : IsPrimitiveRoot μ p :=
    (IsPrimitiveRoot.coe_units_iff (M := K') (k := p) (ζ := μ)).mp hμ'
  -- the `p`-th roots of unity in `K'` are exactly the powers of `μ`
  have hzp : Subgroup.zpowers μ = rootsOfUnity p K' := hμ.zpowers_eq
  have hα0 : α ≠ 0 := by
    intro h
    have h2 : algebraMap k K' (a : k) = 0 := by rw [← hα, h, zero_pow hp.ne_zero]
    exact a.ne_zero ((map_eq_zero_iff _ (algebraMap k K').injective).mp h2)
  have hpoweq : ∀ σ : Gal(K'/k), (σ α) ^ p = α ^ p := by
    intro σ
    rw [← map_pow, hα, AlgEquiv.commutes]
  have hσα : ∀ σ : Gal(K'/k), σ α ≠ 0 := by
    intro σ h
    exact (pow_ne_zero p hα0) (by rw [← hpoweq σ, h, zero_pow hp.ne_zero])
  -- the Kummer cocycle `σ ↦ σ α / α`
  let zu : Gal(K'/k) → K'ˣ := fun σ => Units.mk0 (σ α / α) (div_ne_zero (hσα σ) hα0)
  have hval : ∀ σ, (zu σ : K') = σ α / α := fun σ => Units.val_mk0 _
  have hzu_one : ∀ σ, zu σ ^ p = 1 := by
    intro σ
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hval σ, div_pow, hpoweq σ,
      div_self (pow_ne_zero p hα0)]
  have hmem : ∀ σ, zu σ ∈ rootsOfUnity p K' :=
    fun σ => (mem_rootsOfUnity p (zu σ)).mpr (hzu_one σ)
  have hmemZ : ∀ σ, zu σ ∈ Subgroup.zpowers μ := fun σ => by rw [hzp]; exact hmem σ
  -- the cocycle is fixed by the Galois action (it is a root of unity, i.e. a power of `ζ`)
  have hfix : ∀ τ σ : Gal(K'/k), σ ((zu τ : K'ˣ) : K') = ((zu τ : K'ˣ) : K') := by
    intro τ σ
    obtain ⟨i, _hi, he⟩ := hμ.eq_pow_of_mem_rootsOfUnity (hmem τ)
    rw [← he, Units.val_pow_eq_pow_val, map_pow]
    have hσμ : σ (μ : K') = (μ : K') := by rw [hμval, AlgEquiv.commutes]
    rw [hσμ]
  -- hence it is a group homomorphism
  have hzu_mul : ∀ σ τ : Gal(K'/k), zu (σ * τ) = zu σ * zu τ := by
    intro σ τ
    apply Units.ext
    have hτ : τ α = (zu τ : K') * α := by rw [hval τ, div_mul_cancel₀ _ hα0]
    change ((zu (σ * τ) : K'ˣ) : K') = ((zu σ * zu τ : K'ˣ) : K')
    rw [Units.val_mul]
    calc ((zu (σ * τ) : K'ˣ) : K')
        = (σ * τ) α / α := hval (σ * τ)
      _ = σ (τ α) / α := by rw [AlgEquiv.mul_apply]
      _ = σ ((zu τ : K') * α) / α := by rw [hτ]
      _ = (σ (zu τ : K') * σ α) / α := by rw [map_mul]
      _ = ((zu τ : K') * σ α) / α := by rw [hfix τ σ]
      _ = (zu τ : K') * (σ α / α) := by rw [mul_div_assoc]
      _ = (zu τ : K') * (zu σ : K') := by rw [hval σ]
      _ = (zu σ : K') * (zu τ : K') := by rw [mul_comm]
  let w : Gal(K'/k) →* Subgroup.zpowers μ :=
    MonoidHom.mk' (fun σ => ⟨zu σ, hmemZ σ⟩) (fun σ τ => by
      apply Subtype.ext
      exact hzu_mul σ τ)
  -- transport along the (additive) isomorphism between `ZMod p` and the powers of `μ`
  let e' : Subgroup.zpowers μ ≃* Multiplicative (ZMod p) :=
    hμ.zmodEquivZPowers.symm.toMultiplicativeRight
  refine ⟨e'.toMonoidHom.comp w, fun σ => ?_⟩
  rw [MonoidHom.comp_apply]
  have h1 : e'.toMonoidHom (w σ) = e' (w σ) := rfl
  rw [h1, MulEquiv.map_eq_one_iff]
  rw [Subtype.ext_iff, Units.ext_iff]
  rw [show ((w σ : Subgroup.zpowers μ) : K'ˣ) = zu σ from rfl]
  rw [Subgroup.coe_one, Units.val_one]
  rw [hval σ, div_eq_one_iff_eq hα0]

end NK.NUV2.LC.RouteB
