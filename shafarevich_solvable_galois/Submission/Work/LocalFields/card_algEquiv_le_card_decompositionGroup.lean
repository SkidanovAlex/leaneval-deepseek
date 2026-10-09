import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.CompletionLocalField
import Submission.Work.LocalFields.valuation_smul_of_mem_stabilizer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

/-! ## Automorphisms of a finite extension of a local field preserve the ring of integers

A ring automorphism `σ` of a finite-dimensional extension `F/k` of non-archimedean local fields
is `k`-linear, hence continuous.  As `𝒪[F]` is compact, `σ '' 𝒪[F]` is compact, hence bounded,
and a bounded subring of `F` containing `1` is contained in the unit ball `𝒪[F]`. -/
section AutoInteger

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]
  [Valued k ℤᵐ⁰] [Valued F ℤᵐ⁰] [IsLocalField k] [IsLocalField F] [ContinuousSMul k F]

theorem mapsTo_integer_of_algEquiv (σ : F ≃ₐ[k] F) :
    Set.MapsTo σ (𝒪[F] : Set F) (𝒪[F] : Set F) := by
  have hcont : Continuous (σ : F → F) :=
    σ.toLinearMap.continuous_of_finiteDimensional
  have hK : IsCompact (𝒪[F] : Set F) := by
    have h1 : IsCompact (Set.univ : Set 𝒪[F]) := isCompact_univ
    have h2 : IsCompact (Subtype.val '' (Set.univ : Set 𝒪[F])) :=
      h1.image continuous_subtype_val
    rwa [Set.image_univ, Subtype.range_val] at h2
  have hbd : Bornology.IsBounded (σ '' (𝒪[F] : Set F)) := (hK.image hcont).isBounded
  rw [isBounded_iff_forall_norm_le] at hbd
  obtain ⟨C, hC⟩ := hbd
  intro x hx
  show Valued.v (σ x) ≤ 1
  have hnorm : ‖σ x‖ ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have hpow : ∀ n : ℕ, ‖σ x‖ ^ n ≤ C := by
      intro n
      have hmem : σ x ^ n ∈ σ '' (𝒪[F] : Set F) :=
        ⟨x ^ n, 𝒪[F].pow_mem hx n, by rw [map_pow]⟩
      have h' := hC _ hmem
      rwa [norm_pow] at h'
    obtain ⟨n, hn⟩ :=
      (Filter.Tendsto.eventually_gt_atTop (tendsto_pow_atTop_atTop_of_one_lt h) C).exists
    exact absurd (hpow n) (not_le.mpr hn)
  exact (Valued.toNormedField.norm_le_one_iff).mp hnorm

end AutoInteger

section Main

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- If `τ ∈ Gal(L/K)` preserves the `w`-adic unit ball of `L`, then `τ ∈ D_w`. -/
theorem mem_decompositionGroup_of_valuation_le_one
    (v : FinitePrime K) (w : FinitePrime L) [hw : w.asIdeal.LiesOver v.asIdeal] (τ : Gal(L/K))
    (h : ∀ x : L, w.valuation L x ≤ 1 ↔ w.valuation L (τ x) ≤ 1) :
    τ ∈ decompositionGroup K w := by
  -- the strict inequality version, via inversion
  have hlt : ∀ x : L, w.valuation L x < 1 ↔ w.valuation L (τ x) < 1 := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    have hxτ : τ x ≠ 0 := fun hx0 => hx (τ.injective (by rw [hx0, map_zero]))
    have key : ∀ y : L, y ≠ 0 → (1 ≤ w.valuation L y ↔ w.valuation L y⁻¹ ≤ 1) := by
      intro y hy
      rw [map_inv₀]
      have hyv : w.valuation L y ≠ 0 := fun h0 => hy (((w.valuation L).zero_iff).mp h0)
      have hpos : (0 : ℤᵐ⁰) < w.valuation L y := WithZero.pos_iff_ne_zero.mpr hyv
      exact (inv_le_one₀ hpos).symm
    rw [← not_le, ← not_le, key x hx, key (τ x) hxτ]
    have hinv : (τ x)⁻¹ = τ x⁻¹ := (map_inv₀ (τ : L →+* L) x).symm
    rw [hinv]
    exact not_congr (h x⁻¹)
  rw [mem_decompositionGroup_iff, Ideal.pointwise_smul_def]
  let e : 𝓞 L ≃+* 𝓞 L := MulSemiringAction.toRingEquiv Gal(L/K) (𝓞 L) τ
  have he : (e : 𝓞 L →+* 𝓞 L) = MulSemiringAction.toRingHom Gal(L/K) (𝓞 L) τ := by
    simp only [e]; rfl
  rw [← he]
  have hgal : ∀ a : 𝓞 L, τ (a : L) = (e a : L) := fun a => gal_algebraMap τ a
  have hae : ∀ a : 𝓞 L, a ∈ w.asIdeal ↔ e a ∈ w.asIdeal := by
    intro a
    have hlt' : w.valuation L ((a : 𝓞 L) : L) < 1 ↔
        w.valuation L ((e a : 𝓞 L) : L) < 1 := by
      have := hlt ((a : 𝓞 L) : L)
      rwa [hgal a] at this
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w a,
        ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w (e a),
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := L) w a,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := L) w (e a)]
    exact hlt'
  ext a
  rw [← RingEquiv.apply_symm_apply e a]
  exact (mem_map_ringEquiv e w.asIdeal (e.symm a)).trans (hae (e.symm a))

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem card_algEquiv_le_card_decompositionGroup {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal]
    [Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [ContinuousSMul (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)] :
    Nat.card ((Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
        (Work.LocalFields.Completion L w)) ≤
      Nat.card (Work.LocalFields.decompositionGroup K w) := by
  let φ : L →ₐ[K] (Completion L w) := IsScalarTower.toAlgHom K L (Completion L w)
  have hφ_apply : ∀ y : L, φ y = algebraMap L (Completion L w) y := fun y => rfl
  haveI hnormal : Normal K φ.fieldRange := Normal.of_algEquiv (AlgHom.equivFieldRange φ)
  let σL : ((Completion L w) ≃ₐ[Completion K v] (Completion L w)) → Gal(L/K) := fun σ =>
    (AlgHom.equivFieldRange φ).trans
      ((AlgEquiv.restrictNormal (σ.restrictScalars K) φ.fieldRange).trans
        (AlgHom.equivFieldRange φ).symm)
  have hφsymm : ∀ y : φ.fieldRange,
      algebraMap L (Completion L w) ((AlgHom.equivFieldRange φ).symm y) = (y : Completion L w) := by
    intro y
    have h := congrArg (fun z : φ.fieldRange => (z : Completion L w))
      (AlgEquiv.apply_symm_apply (AlgHom.equivFieldRange φ) y)
    rw [AlgHom.equivFieldRange_apply_coe, hφ_apply] at h
    exact h
  have hcomm : ∀ (σ : (Completion L w) ≃ₐ[Completion K v] (Completion L w)) (x : L),
      σ (algebraMap L (Completion L w) x) = algebraMap L (Completion L w) (σL σ x) := by
    intro σ x
    have h1 : σL σ x = (AlgHom.equivFieldRange φ).symm
        ((AlgEquiv.restrictNormal (σ.restrictScalars K) φ.fieldRange)
          ((AlgHom.equivFieldRange φ) x)) := rfl
    rw [h1, hφsymm]
    rw [show (((AlgEquiv.restrictNormal (σ.restrictScalars K) φ.fieldRange)
          ((AlgHom.equivFieldRange φ) x)) : Completion L w)
        = (algebraMap ↥(φ.fieldRange) (Completion L w))
            ((AlgEquiv.restrictNormal (σ.restrictScalars K) φ.fieldRange)
              ((AlgHom.equivFieldRange φ) x)) from rfl]
    rw [AlgEquiv.restrictNormal_commutes]
    rw [show (algebraMap ↥(φ.fieldRange) (Completion L w)) ((AlgHom.equivFieldRange φ) x)
        = algebraMap L (Completion L w) x from by
      simpa [AlgHom.equivFieldRange_apply_coe] using hφ_apply x]
    rfl
  have hle : ∀ (σ : (Completion L w) ≃ₐ[Completion K v] (Completion L w)) (x : L),
      w.valuation L x ≤ 1 ↔ w.valuation L (σL σ x) ≤ 1 := by
    intro σ x
    have hz : ∀ z : Completion L w, Valued.v (σ z) ≤ 1 ↔ Valued.v z ≤ 1 := by
      intro z
      constructor
      · intro hz
        have h1 : σ.symm (σ z) ∈ (𝒪[Completion L w] : Set (Completion L w)) :=
          mapsTo_integer_of_algEquiv σ.symm hz
        rwa [σ.symm_apply_apply] at h1
      · intro hz
        exact mapsTo_integer_of_algEquiv σ hz
    have hval : ∀ y : L, Valued.v ((y : Completion L w)) = w.valuation L y :=
      fun y => IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe L w y
    rw [← hval x, ← hval (σL σ x)]
    rw [show (((σL σ x : L)) : Completion L w) = σ ((x : L) : Completion L w)
        from (hcomm σ x).symm]
    exact (hz ((x : L) : Completion L w)).symm
  have hD : ∀ σ, σL σ ∈ decompositionGroup K w := fun σ =>
    mem_decompositionGroup_of_valuation_le_one v w (σL σ) (hle σ)
  have hinj : Function.Injective σL := by
    intro σ τ hστ
    have hgen : Algebra.adjoin (Completion K v)
        (Set.range (algebraMap L (Completion L w))) = ⊤ := by
      set S := Algebra.adjoin (Completion K v) (Set.range (algebraMap L (Completion L w)))
      have hclosed : IsClosed (S : Set (Completion L w)) := by
        haveI : FiniteDimensional (Completion K v) ↥(S.toSubmodule) :=
          Submodule.finiteDimensional_of_le (le_top)
        exact Submodule.closed_of_finiteDimensional S.toSubmodule
      have hdense : DenseRange (algebraMap L (Completion L w)) :=
        IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L w
      have hrange : Set.range (algebraMap L (Completion L w)) ⊆ (S : Set (Completion L w)) :=
        Algebra.subset_adjoin
      have huniv : (Set.univ : Set (Completion L w)) ⊆ (S : Set (Completion L w)) := by
        have hd : closure (Set.range (algebraMap L (Completion L w))) = Set.univ :=
          hdense.closure_range
        rw [← hd]
        exact closure_minimal hrange hclosed
      exact Algebra.eq_top_iff.mpr (fun z => huniv (Set.mem_univ z))
    have hAlg : σ.toAlgHom = τ.toAlgHom := by
      refine AlgHom.ext_of_adjoin_eq_top hgen (fun x hx => ?_)
      obtain ⟨y, rfl⟩ := hx
      change σ (algebraMap L (Completion L w) y) = τ (algebraMap L (Completion L w) y)
      rw [hcomm σ y, hcomm τ y, hστ]
    exact AlgEquiv.ext (fun z => congrFun (congrArg DFunLike.coe hAlg) z)
  have hΦinj : Function.Injective
      (fun σ : (Completion L w) ≃ₐ[Completion K v] (Completion L w) =>
        (⟨σL σ, hD σ⟩ : decompositionGroup K w)) := by
    intro σ τ hστ
    exact hinj (Subtype.ext_iff.mp hστ)
  exact Nat.card_le_card_of_injective _ hΦinj

end Main

end Work.LocalFields
