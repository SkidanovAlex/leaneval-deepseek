import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.Work.SSGRoute.isUnit_natCast_of_not_dvd_residueChar
import Submission.Work.SSGRoute.residueField_residue_pow_eq_one

namespace Work.SSGRoute

set_option linter.style.haveILetI false

/-- **The local inertia subgroup fixes the prime-to-`p` roots of unity of `ℚ̄`.**

If `σ` is an element of the decomposition group of a finite place `A'` of `ℚ̄` whose image under
the identification `D_{A'} ≃* Gal(κ̄/κ)` (`κ = ℚ_ℓ` the local field of `A'`) lies in the local
inertia subgroup `I_κ` (the fixing subgroup of `κ(μ_{p'})`), then `σ` itself fixes every root of
unity of `ℚ̄` of order prime to `p = residueChar A'`.

The point of the `TameData` hypothesis is only to be able to *replace* the opaque identification
`NK.FrobeniusBridge.localGaloisEquiv A'` by the explicit `NK.ResidueFrob.localGaloisEquivAdjoin
A'`; for the latter, inertia membership unwinds to the statement that the restriction
`σ̂|_M` of `σ` to `M = κ·ℚ̄` fixes the prime-to-`p` roots of unity of `M`, and those are exactly
the images of the prime-to-`p` roots of unity of `ℚ̄`. -/
theorem fixes_rootsOfUnity_of_mem_inertia
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (p q : ℕ) (hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A')
      (NK.FrobeniusBridge.localClosure A'))
    (σ : ↥(SSGRoute.decomp ℚ A'.1))
    (h : NK.FrobeniusBridge.localGaloisEquiv A' σ ∈
      NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A')
        (K' := NK.FrobeniusBridge.localClosure A') p) :
    ∀ (n : ℕ), ¬ p ∣ n → ∀ ζ : SSGRoute.QBar, IsPrimitiveRoot ζ n →
      (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) ζ = ζ := by
  -- switch from the opaque identification to the explicit one
  letI : Algebra (NK.FrobeniusBridge.localField A') (NK.NeukirchUchida.placeCompletion A'.1) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion
      (Submission.NeukirchUchida.primeOf A'.1 A'.2) A'.1
      (Submission.NeukirchUchida.primeOf_spec A'.1 A'.2)).toAlgebra
  let pp := Submission.NeukirchUchida.primeOf A'.1 A'.2
  let hA := Submission.NeukirchUchida.primeOf_spec A'.1 A'.2
  let halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ pp,
      algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion pp A'.1 hA z :=
    fun z => rfl
  let hW := NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
    pp A'.1 hA
  let σ' : ↥(NK.Mine.decompositionGroupOf ℚ SSGRoute.QBar A'.1) := σ
  have h' : NK.ResidueFrob.localGaloisEquivAdjoin A' σ ∈
      NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A')
        (K' := NK.FrobeniusBridge.localClosure A') p := by
    have hiff := NK.LocalTame.inertiaOfDecomposition_iff_of_localIso
      (D := ↥(SSGRoute.decomp ℚ A'.1)) hT
      (NK.ResidueFrob.localGaloisEquivAdjoin A') (NK.FrobeniusBridge.localGaloisEquiv A') σ
    exact hiff.mpr h
  have hun : NK.ResidueFrob.localGaloisEquivAdjoin A' σ =
      NK.ResidueFrob.adjoinLocalIso pp A'.1 hA halg hW σ' := rfl
  rw [hun] at h'
  -- the explicit identification acts on `κ̄` by `ζ ↦ φ (σ̂|_M (φ⁻¹ ζ))`
  have hval2 : ∀ u : NK.FrobeniusBridge.localClosure A',
      ((NK.ResidueFrob.adjoinLocalIso pp A'.1 hA halg hW) σ') u =
        (NK.ResidueFrob.adjoinSepEquiv pp A'.1 hA halg)
          ((NK.NeukirchUchida.decompositionToAdjoin pp A'.1 hA halg σ')
            ((NK.ResidueFrob.adjoinSepEquiv pp A'.1 hA halg).symm u)) := by
    intro u
    simp only [NK.ResidueFrob.adjoinLocalIso, MulEquiv.trans_apply, AlgEquiv.autCongr_apply,
      AlgEquiv.trans_apply, NK.ResidueFrob.decompositionAdjoinEquiv_apply]
  intro n hn ζ hζ
  let φ : ↥(NK.NeukirchUchida.adjoinPlaceCompletion pp A'.1) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ pp]
      SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ pp) :=
    NK.ResidueFrob.adjoinSepEquiv pp A'.1 hA halg
  have hw_prim : IsPrimitiveRoot (φ (NK.NeukirchUchida.coInAdjoin pp A'.1 ζ)) n :=
    (hζ.map_of_injective (NK.ResidueFrob.coInAdjoinHom_injective pp A'.1)).map_of_injective
      φ.injective
  have hfix := (NK.LocalAnabelian.mem_inertiaSubgroup_iff p _).mp h' n hn _ hw_prim
  rw [hval2, AlgEquiv.symm_apply_apply] at hfix
  have key : (NK.NeukirchUchida.decompositionToAdjoin pp A'.1 hA halg σ')
      (NK.NeukirchUchida.coInAdjoin pp A'.1 ζ) = NK.NeukirchUchida.coInAdjoin pp A'.1 ζ :=
    φ.injective hfix
  have h2 : NK.NeukirchUchida.coInAdjoin pp A'.1
        ((σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) ζ) = NK.NeukirchUchida.coInAdjoin pp A'.1 ζ := by
    rw [← NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin pp A'.1 hA halg σ' ζ]
    exact key
  exact NK.ResidueFrob.coInAdjoinHom_injective pp A'.1 h2

/-- **Fixing the prime-to-`p` roots of unity of `ℚ̄` forces inertia.**

Let `A'` be a finite place of `ℚ̄` over `ℚ`, `p` its residue characteristic and `σ` an element of
its decomposition group.  If `σ` fixes every root of unity of `ℚ̄` of order prime to `p`, then `σ`
acts trivially on the residue field of `A'`, i.e. `σ` is an inertia element.

The residue field `k` of `A'` is the algebraic closure `𝔽̄_p` of the residue field `𝔽_p` of `ℚ`:
it is the union of the residue fields `𝓞 L ⧸ P_L` of the finite levels `L`, each a finite extension
of `𝔽_p`.  Hence every element of `k` is `0` or a root of unity of order prime to `p`
(`residueField_residue_pow_eq_one`); a primitive `N`-th root of unity of `k` (`N` prime to `p`)
lifts to a primitive `N`-th root of unity of `ℚ̄` inside the valuation ring `A'.1`
(`isUnit_natCast_of_not_dvd_residueChar` supplies that `N` is a unit of `A'.1`, so that the
reduction map is injective on the `N`-torsion), which `σ` fixes; as every element of `kˣ` is the
residue of a root of unity, `σ` acts trivially on `k`. -/
theorem isInertia_of_fixes_rootsOfUnity
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) (p : ℕ)
    (hp : p = Work.SSGRoute.residueChar A')
    (σ : ↥(SSGRoute.decomp ℚ A'.1))
    (hfix : ∀ (n : ℕ), ¬ p ∣ n → ∀ ζ : SSGRoute.QBar, IsPrimitiveRoot ζ n →
      (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) ζ = ζ) :
    SSGRoute.IsInertia ℚ A'.1 (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) := by
  haveI : IsSepClosed SSGRoute.QBar := IsSepClosure.sep_closed ℚ
  refine ⟨σ.property, ?_⟩
  intro x hx
  let g : ↥(A'.1.decompositionSubgroup ℚ) := ⟨σ, σ.property⟩
  -- `g` acts trivially on the residue field
  have hfixres : ∀ b : ↥A'.1,
      IsLocalRing.residue ↥A'.1 (g • b) = IsLocalRing.residue ↥A'.1 b := by
    intro b
    rw [IsLocalRing.ResidueField.residue_smul]
    rcases residueField_residue_pow_eq_one A' p hp b with h0 | ⟨N, hNpos, hNp, hNpow⟩
    · rw [h0, smul_zero]
    · -- a primitive `N`-th root of unity of `ℚ̄`, lying in `A'.1`
      haveI : NeZero N := ⟨hNpos.ne'⟩
      obtain ⟨ζ₀, hζ₀⟩ :=
        NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := SSGRoute.QBar) (n := N)
      have hζ₀mem : ζ₀ ∈ A'.1 :=
        NK.TameStructureDeep.Tame.mem_valuationSubring_of_isPrimitiveRoot A'.1 hζ₀ hNpos.ne'
      let ζ₀A : ↥A'.1 := ⟨ζ₀, hζ₀mem⟩
      have hζ₀A : IsPrimitiveRoot ζ₀A N :=
        (IsPrimitiveRoot.coe_submonoidClass_iff (N := A'.1) (ζ := ζ₀A)).mp hζ₀
      have hunit : IsUnit (N : ↥A'.1) := isUnit_natCast_of_not_dvd_residueChar A' p hp hNp
      -- the residue of `ζ₀A` is a primitive `N`-th root of unity of `k`
      have hη : IsPrimitiveRoot (IsLocalRing.residue ↥A'.1 ζ₀A) N :=
        NK.ResidueFrob.isPrimitiveRoot_residue hζ₀A
          (fun w hw hres => NK.ResidueFrob.residue_injective_on_torsion hunit hw hres)
      -- the residue of `b` is a power of it
      obtain ⟨j, -, hj⟩ := hη.eq_pow_of_pow_eq_one hNpow
      -- `g` fixes `ζ₀A`, hence its residue
      have hgζ : g • ζ₀A = ζ₀A := by
        apply Subtype.ext
        rw [NK.Ramification.coe_smul]
        exact hfix N hNp ζ₀ hζ₀
      rw [← hj]
      calc (MulSemiringAction.toRingEquiv ↥(A'.1.decompositionSubgroup ℚ)
              (IsLocalRing.ResidueField ↥A'.1)) g ((IsLocalRing.residue ↥A'.1) ζ₀A ^ j)
          = (MulSemiringAction.toRingEquiv ↥(A'.1.decompositionSubgroup ℚ)
              (IsLocalRing.ResidueField ↥A'.1)) g ((IsLocalRing.residue ↥A'.1) ζ₀A) ^ j := by
            rw [map_pow]
        _ = ((IsLocalRing.residue ↥A'.1) (g • ζ₀A)) ^ j := by
            rw [MulSemiringAction.toRingEquiv_apply_apply, ← IsLocalRing.ResidueField.residue_smul
              ↥(A'.1.decompositionSubgroup ℚ) g ζ₀A]
        _ = ((IsLocalRing.residue ↥A'.1) ζ₀A) ^ j := by rw [hgζ]
  let w : ↥A'.1 := g • (⟨x, hx⟩ : ↥A'.1) - ⟨x, hx⟩
  have hmem : w ∈ IsLocalRing.maximalIdeal ↥A'.1 := by
    change g • (⟨x, hx⟩ : ↥A'.1) - ⟨x, hx⟩ ∈ IsLocalRing.maximalIdeal ↥A'.1
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hfixres, sub_self]
  have hlt : A'.1.valuation (w : SSGRoute.QBar) < 1 :=
    (ValuationSubring.valuation_lt_one_iff A'.1 w).mp hmem
  simpa [w, NK.Ramification.coe_smul] using hlt

theorem isInertia_of_mem_inertia
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (p q : ℕ) (hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A')
      (NK.FrobeniusBridge.localClosure A'))
    (hq : NK.ResidueFrob.ResidueCardMatches A' q)
    (hp : p = Work.SSGRoute.residueChar A')
    (σ : ↥(SSGRoute.decomp ℚ A'.1))
    (h : NK.FrobeniusBridge.localGaloisEquiv A' σ ∈
      NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A')
        (K' := NK.FrobeniusBridge.localClosure A') p) :
    SSGRoute.IsInertia ℚ A'.1 (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) :=
  isInertia_of_fixes_rootsOfUnity A' p hp σ
    (fixes_rootsOfUnity_of_mem_inertia A' p q hT σ h)

end Work.SSGRoute
