import Mathlib

namespace Work.CFTLib.InvCharCrux

/-- The kernel of the restriction homomorphism `Gal(K'/F) →* Gal(K/F)` (`K` a normal intermediate
field of `K'/F`), used to state the main result below. -/
private abbrev kerRestrictHom (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra F K]
    [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] [Normal F K] : Type :=
  (AlgEquiv.restrictNormalHom (F := F) (K₁ := K') K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker

/-- **Restriction to a normal intermediate field, as a surjection onto its Galois group.** Let `F ⊆ K ⊆ K'` be a scalar tower of fields with `K/F` normal and `M ⊆ K'` a normal `K`-intermediate field. Then there is a surjective group homomorphism from `N = ker (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K))` onto the `K`-automorphism group of `M` whose kernel is the set of elements of `N` fixing `M` pointwise. Each `n ∈ N` fixes `K` pointwise, hence is `K`-linear, and `n(M) = M` because `M/K` is normal, so `n|_M` is a `K`-algebra automorphism of `M`. Surjectivity follows from `AlgEquiv.restrictNormalHom_surjective` for the base `K` (with intermediate field `M` and ambient `K'`), and the kernel description from `IntermediateField.mem_fixingSubgroup_iff` / `AlgEquiv.restrictNormal_eq_one_iff`. -/
theorem restrictKerHom {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] [Normal F K] [Normal K K'] (M : IntermediateField K K') [Normal K M] : ∃ ρ : (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker →* (↥M ≃ₐ[K] ↥M), Function.Surjective ρ ∧ ∀ n, ρ n = 1 ↔ ∀ x : ↥M, (n : K' ≃ₐ[F] K') x = x := by
  classical
  -- Every element of the kernel of the restriction to `K` fixes `K` pointwise.
  have ker_fixes_K : ∀ (n : kerRestrictHom F K K') (x : K),
      (n : K' ≃ₐ[F] K') (algebraMap K K' x) = algebraMap K K' x := by
    intro n x
    have hn : (n : K' ≃ₐ[F] K').restrictNormal K = 1 := by
      change (AlgEquiv.restrictNormalHom (F := F) (K₁ := K') K) (n : K' ≃ₐ[F] K') = 1
      exact MonoidHom.mem_ker.mp n.2
    have h := AlgEquiv.restrictNormal_commutes (χ := (n : K' ≃ₐ[F] K')) (E := K) (K₁ := K')
      (K₂ := K') x
    rw [hn, AlgEquiv.one_apply] at h
    exact h.symm
  -- A kernel element, viewed as a `K`-algebra automorphism.
  let toKAut : kerRestrictHom F K K' → (K' ≃ₐ[K] K') :=
    fun n => { (n : K' ≃ₐ[F] K') with commutes' := ker_fixes_K n }
  have toKAut_apply : ∀ (n : kerRestrictHom F K K') (x : K'), toKAut n x = (n : K' ≃ₐ[F] K') x :=
    fun _ _ => rfl
  let toKAutHom : kerRestrictHom F K K' →* (K' ≃ₐ[K] K') :=
    MonoidHom.mk' toKAut fun _ _ => AlgEquiv.ext fun _ => rfl
  have toKAutHom_apply : ∀ n, toKAutHom n = toKAut n := fun _ => rfl
  -- A `K`-algebra automorphism of `K'` is an `F`-algebra automorphism.
  have toFAut_commutes : ∀ (σ : K' ≃ₐ[K] K') (x : F),
      σ (algebraMap F K' x) = algebraMap F K' x := by
    intro σ x
    rw [IsScalarTower.algebraMap_apply F K K']
    exact σ.commutes (algebraMap F K x)
  let toFAut : (K' ≃ₐ[K] K') → (K' ≃ₐ[F] K') := fun σ => { σ with commutes' := toFAut_commutes σ }
  have toFAut_apply : ∀ (σ : K' ≃ₐ[K] K') (x : K'), toFAut σ x = σ x := fun _ _ => rfl
  have toFAut_mem_ker : ∀ σ : K' ≃ₐ[K] K',
      toFAut σ ∈ (AlgEquiv.restrictNormalHom (F := F) (K₁ := K') K).ker := by
    intro σ
    rw [MonoidHom.mem_ker]
    apply AlgEquiv.ext
    intro x
    apply (algebraMap K K').injective
    show algebraMap K K' ((toFAut σ).restrictNormal K x) = algebraMap K K' ((1 : K ≃ₐ[F] K) x)
    rw [AlgEquiv.restrictNormal_commutes (χ := toFAut σ) (E := K) (K₁ := K') (K₂ := K') x,
      toFAut_apply, AlgEquiv.one_apply]
    exact σ.commutes x
  let ofKAut : (K' ≃ₐ[K] K') → kerRestrictHom F K K' := fun σ => ⟨toFAut σ, toFAut_mem_ker σ⟩
  have toKAut_ofKAut : ∀ σ : K' ≃ₐ[K] K', toKAut (ofKAut σ) = σ := by
    intro σ
    apply AlgEquiv.ext
    intro _
    rfl
  -- The restriction map, on the kernel.
  have hρ : ∀ n, ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M).comp toKAutHom) n
      = (toKAut n).restrictNormal ↥M := fun _ => rfl
  refine ⟨(AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M).comp toKAutHom, ?_, ?_⟩
  · -- surjectivity: restriction `Gal(K'/K) →* Gal(M/K)` is onto, and every `K`-automorphism of
    -- `K'` is (as a function) an `F`-automorphism of `K'` lying in the kernel.
    intro τ
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥M) (E := K') τ
    exact ⟨ofKAut σ, by rw [hρ, toKAut_ofKAut]; exact hσ⟩
  · -- kernel: an element restricts to the identity iff it fixes `M` pointwise.
    intro n
    constructor
    · intro hn x
      have h := AlgEquiv.restrictNormal_apply M (toKAut n) x
      have hn' : (toKAut n).restrictNormal ↥M = 1 := by rw [← hρ]; exact hn
      calc (n : K' ≃ₐ[F] K') ↑x = toKAut n ↑x := (toKAut_apply n ↑x).symm
        _ = ↑(((toKAut n).restrictNormal ↥M) x) := h.symm
        _ = ↑x := by rw [hn']; simp
    · intro h
      rw [hρ]
      apply AlgEquiv.ext (R := K)
      intro x
      apply (algebraMap ↥M K').injective
      simp only [IntermediateField.algebraMap_apply]
      rw [AlgEquiv.restrictNormal_apply M (toKAut n) x, toKAut_apply n]
      simpa using h x

end Work.CFTLib.InvCharCrux
