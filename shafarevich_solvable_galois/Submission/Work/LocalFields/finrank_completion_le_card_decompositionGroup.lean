import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.card_decompositionGroup
import Submission.Work.LocalFields.valuation_smul_of_mem_stabilizer
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-! ## A `K_v`-algebra automorphism of `L_w` preserves the valuation ring

The extension `L_w/K_v` is finite-dimensional, so every `K_v`-algebra automorphism `σ` of `L_w`
is continuous with continuous inverse (`LinearMap.continuous_of_finiteDimensional`).  Hence
`σ '' 𝒪[L_w]` and `σ⁻¹ '' 𝒪[L_w]` are compact, hence bounded, subrings of the field `L_w`; a
bounded subring of `L_w` is contained in `𝒪[L_w]` (a subring containing an element of norm `> 1`
contains its unbounded sequence of powers).  Therefore `σ '' 𝒪[L_w] = 𝒪[L_w]`. -/

section Preserve

variable (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
  [hw : w.asIdeal.LiesOver v.asIdeal]
  [Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
  [ContinuousSMul (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
  [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]

/-- A `K_v`-algebra automorphism of `L_w` maps `𝒪[L_w]` into itself. -/
theorem valued_le_one_of_algEquiv
    (σ : (Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
      Work.LocalFields.Completion L w)) :
    ∀ a : Work.LocalFields.Completion L w, Valued.v a ≤ 1 → Valued.v (σ a) ≤ 1 := by
  intro a ha
  haveI : FiniteDimensional (Work.LocalFields.Completion K v)
      (Work.LocalFields.Completion L w) := inferInstance
  haveI : CompactSpace (𝒪[Work.LocalFields.Completion L w]) := IsLocalField.instCompactInteger
  have hcomp : IsCompact (𝒪[Work.LocalFields.Completion L w] :
      Set (Work.LocalFields.Completion L w)) := by
    have h1 : IsCompact (Set.univ : Set (𝒪[Work.LocalFields.Completion L w])) := isCompact_univ
    have h2 : Continuous (fun x : (𝒪[Work.LocalFields.Completion L w]) =>
        (x : Work.LocalFields.Completion L w)) := continuous_subtype_val
    have := h1.image h2
    simpa using this
  have hσ : Continuous σ := (σ.toAlgHom.toLinearMap).continuous_of_finiteDimensional
  have hcomp' : IsCompact (σ '' (𝒪[Work.LocalFields.Completion L w] :
      Set (Work.LocalFields.Completion L w))) := hcomp.image hσ
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : Work.LocalFields.Completion L w)).1 hcomp'.isBounded
  have hbound : ∀ y : (𝒪[Work.LocalFields.Completion L w]),
      ‖σ ((y : 𝒪[Work.LocalFields.Completion L w]) : Work.LocalFields.Completion L w)‖ ≤ C := by
    intro y
    have hy : σ (y : Work.LocalFields.Completion L w) ∈ σ '' (𝒪[Work.LocalFields.Completion L w] :
        Set (Work.LocalFields.Completion L w)) := ⟨(y : Work.LocalFields.Completion L w), y.2, rfl⟩
    have := hC hy
    simpa [Metric.mem_closedBall] using this
  have hmain : ∀ y : (𝒪[Work.LocalFields.Completion L w]),
      ‖σ ((y : 𝒪[Work.LocalFields.Completion L w]) : Work.LocalFields.Completion L w)‖ ≤ 1 := by
    intro y
    by_contra h
    push_neg at h
    have hxn : ∀ n : ℕ, ‖σ ((y : 𝒪[Work.LocalFields.Completion L w]) :
        Work.LocalFields.Completion L w)‖ ^ n ≤ C := by
      intro n
      have := hbound (y ^ n)
      simpa [map_pow, norm_pow] using this
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    exact absurd (hxn n) (not_le.mpr hn)
  have hamem : a ∈ (𝒪[Work.LocalFields.Completion L w] :
      Set (Work.LocalFields.Completion L w)) :=
    (Valuation.mem_integer_iff (Valued.v (R := Work.LocalFields.Completion L w)) a).mpr ha
  have hfin : ‖σ a‖ ≤ 1 := hmain ⟨a, hamem⟩
  rwa [Valued.toNormedField.norm_le_one_iff] at hfin

end Preserve

section PreserveFull

variable (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
  [hw : w.asIdeal.LiesOver v.asIdeal]
  [Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
  [ContinuousSMul (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
  [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]

/-- A `K_v`-algebra automorphism of `L_w` preserves the valuation ring. -/
theorem valued_le_one_iff_of_algEquiv
    (σ : (Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
      Work.LocalFields.Completion L w)) :
    ∀ a : Work.LocalFields.Completion L w, Valued.v (σ a) ≤ 1 ↔ Valued.v a ≤ 1 := by
  intro a
  constructor
  · intro h
    haveI : FiniteDimensional (Work.LocalFields.Completion K v)
        (Work.LocalFields.Completion L w) := inferInstance
    have hσ : Continuous σ.symm :=
      ((σ.symm).toAlgHom.toLinearMap).continuous_of_finiteDimensional
    have := valued_le_one_of_algEquiv v w σ.symm (σ a) h
    simpa using this
  · intro h
    exact valued_le_one_of_algEquiv v w σ a h

/-- A `K_v`-algebra automorphism of `L_w` preserves the maximal ideal, expressed as the strict
inequality `Valued.v _ < 1`. -/
theorem valued_lt_one_iff_of_algEquiv
    (σ : (Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
      Work.LocalFields.Completion L w)) :
    ∀ a : Work.LocalFields.Completion L w, Valued.v (σ a) < 1 ↔ Valued.v a < 1 := by
  have hle := valued_le_one_iff_of_algEquiv v w σ
  intro a
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hsa : σ a ≠ 0 := fun h => ha (σ.injective (by rw [h, map_zero]))
    have hpos : (0 : ℤᵐ⁰) < Valued.v (σ a) := (Valuation.pos_iff _).mpr hsa
    have hposa : (0 : ℤᵐ⁰) < Valued.v a := (Valuation.pos_iff _).mpr ha
    have e1 : (1 ≤ Valued.v (σ a)) ↔ (Valued.v (σ a))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀, or_iff_right (not_le.mpr hpos)]
    have e3 : (1 ≤ Valued.v a) ↔ (Valued.v a)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀, or_iff_right (not_le.mpr hposa)]
    have e2 : (Valued.v (σ a))⁻¹ = Valued.v (σ a⁻¹) := by
      rw [map_inv₀ σ a, map_inv₀]
    have h1 : (1 ≤ Valued.v (σ a)) ↔ (1 ≤ Valued.v a) := by
      rw [e1, e2, hle (a⁻¹), map_inv₀]
      exact e3.symm
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle a, not_congr h1]

end PreserveFull

/-! ## The restriction of a local automorphism to `L` lies in the decomposition group -/

/-- If `ρ ∈ Gal(L/K)` preserves the valuation `w` on the level of the unit ball
(`w.valuation L (ρ x) < 1 ↔ w.valuation L x < 1`), then `ρ` stabilizes `w`, i.e. lies in the
decomposition group.  Indeed `w.asIdeal` is exactly the set of integral elements of `L` with
`w`-adic valuation `< 1`. -/
theorem mem_decompositionGroup_of_val_lt_one (w : FinitePrime L) (ρ : Gal(L/K))
    (h : ∀ x : L, w.valuation L (ρ x) < 1 ↔ w.valuation L x < 1) :
    ρ ∈ decompositionGroup K w := by
  rw [mem_decompositionGroup_iff, Ideal.pointwise_smul_def]
  set e := MulSemiringAction.toRingEquiv Gal(L/K) (𝓞 L) ρ with he
  have hcoe : ∀ x : 𝓞 L, ((e x : 𝓞 L) : L) = ρ ((x : 𝓞 L) : L) := by
    intro x
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact (gal_algebraMap ρ x).symm
  have hmem : ∀ x : 𝓞 L, e x ∈ w.asIdeal ↔ x ∈ w.asIdeal := by
    intro x
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem,
      ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := L) w (e x),
      ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := L) w x]
    have h2 : w.valuation L (((e x : 𝓞 L) : L)) = w.valuation L (ρ (((x : 𝓞 L) : L))) := by
      rw [hcoe x]
    rw [h2, h (((x : 𝓞 L) : L))]
  change Ideal.map (e : 𝓞 L →+* 𝓞 L) w.asIdeal = w.asIdeal
  apply Ideal.ext
  intro y
  rw [Ideal.mem_map_iff_of_surjective (e : 𝓞 L →+* 𝓞 L) e.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact (hmem (e.symm y)).mp (by rwa [e.apply_symm_apply])

/-! ## The main theorem -/

theorem finrank_completion_le_card_decompositionGroup {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal]
    [Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [ContinuousSMul (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)] :
    Module.finrank (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w) ≤
      Nat.card (Work.LocalFields.decompositionGroup K w) := by
  rw [finrank_completion_eq_card_algEquiv v w]
  have hcont : ∀ σ : (Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
      Work.LocalFields.Completion L w), Continuous σ := fun σ =>
    (σ.toAlgHom.toLinearMap).continuous_of_finiteDimensional
  have hmem : ∀ σ : (Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
      Work.LocalFields.Completion L w),
      (AlgEquiv.restrictScalars K σ).restrictNormal L ∈
        Work.LocalFields.decompositionGroup K w := by
    intro σ
    refine mem_decompositionGroup_of_val_lt_one w _ ?_
    intro x
    have hr : algebraMap L (Work.LocalFields.Completion L w)
          ((AlgEquiv.restrictScalars K σ).restrictNormal L x)
        = σ (algebraMap L (Work.LocalFields.Completion L w) x) :=
      AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) L x
    have hcoe : ∀ y : L, (y : Work.LocalFields.Completion L w) =
        algebraMap L (Work.LocalFields.Completion L w) y := fun y => rfl
    have h1 : w.valuation L ((AlgEquiv.restrictScalars K σ).restrictNormal L x)
        = Valued.v (σ (algebraMap L (Work.LocalFields.Completion L w) x)) := by
      rw [← IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe L w
            ((AlgEquiv.restrictScalars K σ).restrictNormal L x), hcoe, hr]
    rw [h1, valued_lt_one_iff_of_algEquiv v w σ (algebraMap L (Work.LocalFields.Completion L w) x),
      ← hcoe x, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe L w x]
  have hinj : Function.Injective (fun σ : (Work.LocalFields.Completion L w ≃ₐ[
        Work.LocalFields.Completion K v] Work.LocalFields.Completion L w) =>
      (⟨(AlgEquiv.restrictScalars K σ).restrictNormal L, hmem σ⟩ :
        Work.LocalFields.decompositionGroup K w)) := by
    intro σ₁ σ₂ h
    have h2 : (AlgEquiv.restrictScalars K σ₁).restrictNormal L =
        (AlgEquiv.restrictScalars K σ₂).restrictNormal L := congrArg Subtype.val h
    have hcomp : ⇑σ₁ ∘ (algebraMap L (Work.LocalFields.Completion L w))
        = ⇑σ₂ ∘ (algebraMap L (Work.LocalFields.Completion L w)) := by
      funext x
      simp only [Function.comp_apply]
      calc σ₁ (algebraMap L (Work.LocalFields.Completion L w) x)
          = algebraMap L (Work.LocalFields.Completion L w)
              ((AlgEquiv.restrictScalars K σ₁).restrictNormal L x) :=
            (AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ₁) L x).symm
        _ = algebraMap L (Work.LocalFields.Completion L w)
              ((AlgEquiv.restrictScalars K σ₂).restrictNormal L x) := by rw [h2]
        _ = σ₂ (algebraMap L (Work.LocalFields.Completion L w) x) :=
            AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ₂) L x
    have heq := DenseRange.equalizer
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L w)
      (hcont σ₁) (hcont σ₂) hcomp
    exact AlgEquiv.ext (fun x => congrFun heq x)
  exact Nat.card_le_card_of_injective _ hinj

end Work.LocalFields
