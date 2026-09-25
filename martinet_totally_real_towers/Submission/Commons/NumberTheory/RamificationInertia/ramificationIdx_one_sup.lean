import Mathlib
import Submission.Commons.NumberTheory.RamificationInertia.ramificationIdx_one_of_sup_eq_top

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.RamificationInertia

open NumberField

/-- **Transport of the ramification index along a base-preserving algebra equivalence.**

If `e : S ≃ₐ[R] S'` is an isomorphism of `R`-algebras and `Q` is a prime of `S'` lying over
`p : Ideal R` with `p ≠ ⊥`, then the prime `Q.comap e` of `S` lying over `p` has the same
ramification index over `R` as `Q`.

Proof: both ramification indices agree with the multiplicity-based definition
`Ideal.ramificationIdx'` (`Ideal.ramificationIdx'_eq_ramificationIdx`), and `ramificationIdx'` is
invariant under an algebra isomorphism (`Ideal.ramificationIdx'_comap_eq`). -/
theorem ramificationIdx_comap_algEquiv {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] [IsDomain R] [IsDedekindDomain S] [IsDedekindDomain S']
    [Module.IsTorsionFree R S] [Module.IsTorsionFree R S']
    (p : Ideal R) (hp : p ≠ ⊥) (e : S ≃ₐ[R] S') (Q : Ideal S') [Q.IsPrime] [Q.LiesOver p] :
    (Q.comap e).ramificationIdx R = Q.ramificationIdx R := by
  haveI : (Q.comap e).IsPrime := Ideal.IsPrime.comap e
  haveI : (Q.comap e).LiesOver p := Ideal.comap_liesOver Q p e
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx p (Q.comap e) hp,
      ← Ideal.ramificationIdx'_eq_ramificationIdx p Q hp,
      Ideal.ramificationIdx'_comap_eq p e Q]

open NumberField in
/-- **Unramifiedness is preserved by composita, in the form needed for the maximal unramified
pro-`p` extension.**

Let `L` and `M` be finite-dimensional Galois intermediate fields of `AlgebraicClosure F` over a
number field `F`.  If every prime of `𝓞 L` and of `𝓞 M` over a prime `𝔭` of `𝓞 F` has ramification
index `1`, then so does every prime of `𝓞 ↥(L ⊔ M)` over `𝔭`.

Proof: reduce to
`Commons.NumberTheory.RamificationInertia.ramificationIdx_one_of_sup_eq_top` (being proved in
parallel at that path) by viewing `L` and `M` as intermediate fields of `↥(L ⊔ M)` (e.g. via
`IntermediateField.comap` along the inclusion into `AlgebraicClosure F`), and transport the
ramification-index hypotheses along the inclusion.  Alternatively prove it directly using
`Commons.NumberTheory.RamificationInertia.inertia_map_restrictNormalHom_le` and
`Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one`
(both already in the commons). -/
theorem ramificationIdx_one_sup {F : Type*} [Field F] [NumberField F]
    (L M : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L] [FiniteDimensional F M]
    [IsGalois F ↥L] [IsGalois F ↥M]
    (hL : ∀ (𝔭 : Ideal (RingOfIntegers F)) (𝔓 : Ideal (RingOfIntegers ↥L)), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥L) → 𝔓.ramificationIdx (RingOfIntegers F) = 1)
    (hM : ∀ (𝔭 : Ideal (RingOfIntegers F)) (𝔓 : Ideal (RingOfIntegers ↥M)), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥M) → 𝔓.ramificationIdx (RingOfIntegers F) = 1) :
    ∀ (𝔭 : Ideal (RingOfIntegers F)) (𝔓 : Ideal (RingOfIntegers ↥(L ⊔ M))), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥(L ⊔ M)) → 𝔓.ramificationIdx (RingOfIntegers F) = 1 := by
  intro 𝔭 𝔓 h𝔭 h𝔭ne h𝔓
  obtain ⟨h𝔓prime, h𝔓lies⟩ := h𝔓
  haveI : 𝔓.IsPrime := h𝔓prime
  haveI : 𝔓.LiesOver 𝔭 := h𝔓lies
  -- The intermediate fields are themselves number fields.
  haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
  haveI : NumberField ↥M := NumberField.of_module_finite F ↥M
  -- The compositum `L ⊔ M` is a finite Galois extension of `F`, hence a number field.
  haveI : FiniteDimensional F ↥(L ⊔ M) := IntermediateField.finiteDimensional_sup L M
  haveI : Algebra.IsSeparable F ↥(L ⊔ M) := inferInstance
  haveI : Normal F ↥(L ⊔ M) := inferInstance
  haveI : IsGalois F ↥(L ⊔ M) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  haveI : NumberField ↥(L ⊔ M) := NumberField.of_module_finite F ↥(L ⊔ M)
  -- View `L` and `M` as intermediate fields of `↥(L ⊔ M)`.
  let L' : IntermediateField F ↥(L ⊔ M) := IntermediateField.restrict (le_sup_left : L ≤ L ⊔ M)
  let M' : IntermediateField F ↥(L ⊔ M) := IntermediateField.restrict (le_sup_right : M ≤ L ⊔ M)
  haveI : FiniteDimensional F ↥L' :=
    Module.Finite.equiv (IntermediateField.restrictAlgEquiv (le_sup_left : L ≤ L ⊔ M)).toLinearEquiv
  haveI : FiniteDimensional F ↥M' :=
    Module.Finite.equiv (IntermediateField.restrictAlgEquiv (le_sup_right : M ≤ L ⊔ M)).toLinearEquiv
  haveI : IsGalois F ↥L' :=
    IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv (le_sup_left : L ≤ L ⊔ M))
  haveI : IsGalois F ↥M' :=
    IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv (le_sup_right : M ≤ L ⊔ M))
  haveI : NumberField ↥L' := NumberField.of_module_finite F ↥L'
  haveI : NumberField ↥M' := NumberField.of_module_finite F ↥M'
  -- Their supremum is everything.
  have hTop : (⊤ : IntermediateField F ↥(L ⊔ M)).map (L ⊔ M).val = L ⊔ M := by
    conv_rhs => rw [← IntermediateField.fieldRange_val (L ⊔ M)]
    ext x
    simp [IntermediateField.mem_map]
  have hLmap : L'.map (L ⊔ M).val = L := by
    change (IntermediateField.restrict (le_sup_left : L ≤ L ⊔ M)).map (L ⊔ M).val = L
    rw [← IntermediateField.lift, IntermediateField.lift_restrict]
  have hMmap : M'.map (L ⊔ M).val = M := by
    change (IntermediateField.restrict (le_sup_right : M ≤ L ⊔ M)).map (L ⊔ M).val = M
    rw [← IntermediateField.lift, IntermediateField.lift_restrict]
  have hlift : IntermediateField.lift (L' ⊔ M') =
      IntermediateField.lift (⊤ : IntermediateField F ↥(L ⊔ M)) := by
    rw [IntermediateField.lift, IntermediateField.lift,
      (IntermediateField.gc_map_comap (L ⊔ M).val).l_sup]
    rw [hLmap, hMmap, hTop]
  have hsup : L' ⊔ M' = ⊤ := (IntermediateField.lift_injective (L ⊔ M)).eq_iff.mp hlift
  -- Transport the ramification hypotheses from `L` and `M` to `L'` and `M'`.
  have hL' : ∀ 𝔓L' : Ideal (𝓞 ↥L'), 𝔓L' ∈ 𝔭.primesOver (𝓞 ↥L') →
      𝔓L'.ramificationIdx (𝓞 F) = 1 := by
    intro Q' hQ'
    haveI : Q'.IsPrime := hQ'.1
    haveI : Q'.LiesOver 𝔭 := hQ'.2
    let e : ↥L ≃ₐ[F] ↥L' := IntermediateField.restrictAlgEquiv (le_sup_left : L ≤ L ⊔ M)
    let φ : 𝓞 ↥L ≃ₐ[𝓞 F] 𝓞 ↥L' := RingOfIntegers.mapAlgEquiv e
    have htrans : (Q'.comap φ).ramificationIdx (𝓞 F) = Q'.ramificationIdx (𝓞 F) :=
      ramificationIdx_comap_algEquiv 𝔭 h𝔭ne φ Q'
    haveI : (Q'.comap φ).IsPrime := Ideal.IsPrime.comap φ
    haveI : (Q'.comap φ).LiesOver 𝔭 := Ideal.comap_liesOver Q' 𝔭 φ
    have h1 : (Q'.comap φ).ramificationIdx (𝓞 F) = 1 :=
      hL 𝔭 (Q'.comap φ) h𝔭 h𝔭ne ⟨inferInstance, inferInstance⟩
    rw [← htrans]; exact h1
  have hM' : ∀ 𝔓M' : Ideal (𝓞 ↥M'), 𝔓M' ∈ 𝔭.primesOver (𝓞 ↥M') →
      𝔓M'.ramificationIdx (𝓞 F) = 1 := by
    intro Q' hQ'
    haveI : Q'.IsPrime := hQ'.1
    haveI : Q'.LiesOver 𝔭 := hQ'.2
    let e : ↥M ≃ₐ[F] ↥M' := IntermediateField.restrictAlgEquiv (le_sup_right : M ≤ L ⊔ M)
    let φ : 𝓞 ↥M ≃ₐ[𝓞 F] 𝓞 ↥M' := RingOfIntegers.mapAlgEquiv e
    have htrans : (Q'.comap φ).ramificationIdx (𝓞 F) = Q'.ramificationIdx (𝓞 F) :=
      ramificationIdx_comap_algEquiv 𝔭 h𝔭ne φ Q'
    haveI : (Q'.comap φ).IsPrime := Ideal.IsPrime.comap φ
    haveI : (Q'.comap φ).LiesOver 𝔭 := Ideal.comap_liesOver Q' 𝔭 φ
    have h1 : (Q'.comap φ).ramificationIdx (𝓞 F) = 1 :=
      hM 𝔭 (Q'.comap φ) h𝔭 h𝔭ne ⟨inferInstance, inferInstance⟩
    rw [← htrans]; exact h1
  exact Commons.NumberTheory.RamificationInertia.ramificationIdx_one_of_sup_eq_top
    (F := F) (X := ↥(L ⊔ M)) L' M' hsup 𝔭 h𝔭 h𝔭ne 𝔓 hL' hM'

end Commons.NumberTheory.RamificationInertia
