import Mathlib
import Submission.Commons.NumberTheory.NumberField.tame_totallyRamified_different_not_pow_dvd
import Submission.Commons.NumberTheory.NumberField.different_dvd_iff_ramificationIdx_ne_one
import Submission.Commons.FieldTheory.IntermediateField.exists_finset_of_le_iSup_of_finiteDimensional
import Submission.Commons.NumberTheory.RamificationInertia.ramificationIdx_one_sup
import Submission.Commons.NumberTheory.RamificationInertia.ramificationIdx_one_iSup_finset
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx

open scoped NumberField Classical
open NumberField

noncomputable section
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.NumberField

/-- Ramification index one at a fixed prime, transported across an equality of intermediate fields. -/
theorem ramificationIdx_eq_one_transport_at {F : Type*} [Field F] [NumberField F]
    {L M : IntermediateField F (AlgebraicClosure F)} [FiniteDimensional F L] [FiniteDimensional F M]
    (hLM : L = M) (𝔭 : Ideal (NumberField.RingOfIntegers F)) (_h𝔭 : 𝔭.IsPrime) (h𝔭ne : 𝔭 ≠ ⊥)
    (hL : ∀ (𝔓 : Ideal (NumberField.RingOfIntegers ↥L)),
      𝔓 ∈ 𝔭.primesOver (NumberField.RingOfIntegers ↥L) →
      𝔓.ramificationIdx (NumberField.RingOfIntegers F) = 1) :
    ∀ (𝔓 : Ideal (NumberField.RingOfIntegers ↥M)),
      𝔓 ∈ 𝔭.primesOver (NumberField.RingOfIntegers ↥M) →
      𝔓.ramificationIdx (NumberField.RingOfIntegers F) = 1 := by
  intro 𝔓 h𝔓
  obtain ⟨h𝔓prime, h𝔓lies⟩ := h𝔓
  haveI : 𝔓.IsPrime := h𝔓prime
  haveI : 𝔓.LiesOver 𝔭 := h𝔓lies
  haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
  haveI : NumberField ↥M := NumberField.of_module_finite F ↥M
  let e : ↥L ≃ₐ[F] ↥M := IntermediateField.equivOfEq hLM
  let φ : 𝓞 ↥L ≃ₐ[𝓞 F] 𝓞 ↥M := RingOfIntegers.mapAlgEquiv e
  have htrans : (𝔓.comap φ).ramificationIdx (𝓞 F) = 𝔓.ramificationIdx (𝓞 F) :=
    Commons.NumberTheory.RamificationInertia.ramificationIdx_comap_algEquiv 𝔭 h𝔭ne φ 𝔓
  haveI : (𝔓.comap φ).IsPrime := inferInstance
  haveI : (𝔓.comap φ).LiesOver 𝔭 := Ideal.comap_liesOver 𝔓 𝔭 φ
  rw [← htrans]
  exact hL (𝔓.comap φ) ⟨inferInstance, inferInstance⟩

/-- Unramifiedness at a fixed prime is preserved by composita (at that prime). -/
theorem ramificationIdx_one_sup_at {F : Type*} [Field F] [NumberField F]
    (L M : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L] [FiniteDimensional F M]
    [IsGalois F ↥L] [IsGalois F ↥M]
    (𝔭 : Ideal (RingOfIntegers F)) (h𝔭 : 𝔭.IsPrime) (h𝔭ne : 𝔭 ≠ ⊥)
    (𝔓 : Ideal (RingOfIntegers ↥(L ⊔ M))) (h𝔓 : 𝔓.IsPrime) (h𝔓lies : 𝔓.LiesOver 𝔭)
    (hL : ∀ (𝔓L : Ideal (RingOfIntegers ↥L)), 𝔓L ∈ 𝔭.primesOver (RingOfIntegers ↥L) →
      𝔓L.ramificationIdx (RingOfIntegers F) = 1)
    (hM : ∀ (𝔓M : Ideal (RingOfIntegers ↥M)), 𝔓M ∈ 𝔭.primesOver (RingOfIntegers ↥M) →
      𝔓M.ramificationIdx (RingOfIntegers F) = 1) :
    𝔓.ramificationIdx (RingOfIntegers F) = 1 := by
  haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
  haveI : NumberField ↥M := NumberField.of_module_finite F ↥M
  haveI : FiniteDimensional F ↥(L ⊔ M) := IntermediateField.finiteDimensional_sup L M
  haveI : Algebra.IsSeparable F ↥(L ⊔ M) := inferInstance
  haveI : Normal F ↥(L ⊔ M) := inferInstance
  haveI : IsGalois F ↥(L ⊔ M) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  haveI : NumberField ↥(L ⊔ M) := NumberField.of_module_finite F ↥(L ⊔ M)
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
  have hL' : ∀ 𝔓L' : Ideal (𝓞 ↥L'), 𝔓L' ∈ 𝔭.primesOver (𝓞 ↥L') →
      𝔓L'.ramificationIdx (𝓞 F) = 1 := by
    intro Q' hQ'
    haveI : Q'.IsPrime := hQ'.1
    haveI : Q'.LiesOver 𝔭 := hQ'.2
    let e : ↥L ≃ₐ[F] ↥L' := IntermediateField.restrictAlgEquiv (le_sup_left : L ≤ L ⊔ M)
    let φ : 𝓞 ↥L ≃ₐ[𝓞 F] 𝓞 ↥L' := RingOfIntegers.mapAlgEquiv e
    have htrans : (Q'.comap φ).ramificationIdx (𝓞 F) = Q'.ramificationIdx (𝓞 F) :=
      Commons.NumberTheory.RamificationInertia.ramificationIdx_comap_algEquiv 𝔭 h𝔭ne φ Q'
    haveI : (Q'.comap φ).IsPrime := Ideal.IsPrime.comap φ
    haveI : (Q'.comap φ).LiesOver 𝔭 := Ideal.comap_liesOver Q' 𝔭 φ
    have h1 : (Q'.comap φ).ramificationIdx (𝓞 F) = 1 :=
      hL (Q'.comap φ) ⟨inferInstance, inferInstance⟩
    rw [← htrans]; exact h1
  have hM' : ∀ 𝔓M' : Ideal (𝓞 ↥M'), 𝔓M' ∈ 𝔭.primesOver (𝓞 ↥M') →
      𝔓M'.ramificationIdx (𝓞 F) = 1 := by
    intro Q' hQ'
    haveI : Q'.IsPrime := hQ'.1
    haveI : Q'.LiesOver 𝔭 := hQ'.2
    let e : ↥M ≃ₐ[F] ↥M' := IntermediateField.restrictAlgEquiv (le_sup_right : M ≤ L ⊔ M)
    let φ : 𝓞 ↥M ≃ₐ[𝓞 F] 𝓞 ↥M' := RingOfIntegers.mapAlgEquiv e
    have htrans : (Q'.comap φ).ramificationIdx (𝓞 F) = Q'.ramificationIdx (𝓞 F) :=
      Commons.NumberTheory.RamificationInertia.ramificationIdx_comap_algEquiv 𝔭 h𝔭ne φ Q'
    haveI : (Q'.comap φ).IsPrime := Ideal.IsPrime.comap φ
    haveI : (Q'.comap φ).LiesOver 𝔭 := Ideal.comap_liesOver Q' 𝔭 φ
    have h1 : (Q'.comap φ).ramificationIdx (𝓞 F) = 1 :=
      hM (Q'.comap φ) ⟨inferInstance, inferInstance⟩
    rw [← htrans]; exact h1
  haveI : 𝔓.IsPrime := h𝔓
  haveI : 𝔓.LiesOver 𝔭 := h𝔓lies
  exact Commons.NumberTheory.RamificationInertia.ramificationIdx_one_of_sup_eq_top
    (F := F) (X := ↥(L ⊔ M)) L' M' hsup 𝔭 h𝔭 h𝔭ne 𝔓 hL' hM'

/-- Unramifiedness at a fixed prime is preserved by finite composita (at that prime). -/
theorem ramificationIdx_one_iSup_finset_at {F : Type*} [Field F] [NumberField F] {ι : Type*}
    (s : Finset ι) (f : ι → IntermediateField F (AlgebraicClosure F))
    [∀ i, FiniteDimensional F ↥(f i)] [∀ i, IsGalois F ↥(f i)]
    (𝔭 : Ideal (RingOfIntegers F)) (h𝔭 : 𝔭.IsPrime) (h𝔭ne : 𝔭 ≠ ⊥)
    (h : ∀ i, ∀ (𝔓 : Ideal (RingOfIntegers ↥(f i))),
      𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥(f i)) → 𝔓.ramificationIdx (RingOfIntegers F) = 1) :
    ∀ (𝔓 : Ideal (RingOfIntegers ↥(⨆ i ∈ s, f i))),
      𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥(⨆ i ∈ s, f i)) →
      𝔓.ramificationIdx (RingOfIntegers F) = 1 := by
  classical
  let Q : Finset ι → Prop := fun s =>
    IsGalois F ↥(⨆ i ∈ s, f i) ∧
      (∀ (𝔓 : Ideal (RingOfIntegers ↥(⨆ i ∈ s, f i))),
        𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥(⨆ i ∈ s, f i)) →
        𝔓.ramificationIdx (RingOfIntegers F) = 1)
  have hQ : ∀ s, Q s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        constructor
        · have hbot : (⨆ i ∈ (∅ : Finset ι), f i) = ⊥ := by simp
          rw [hbot]
          infer_instance
        · have hbot : (⨆ i ∈ (∅ : Finset ι), f i) =
              (⊥ : IntermediateField F (AlgebraicClosure F)) := by simp
          exact ramificationIdx_eq_one_transport_at hbot.symm 𝔭 h𝔭 h𝔭ne
            (fun 𝔓 h𝔓 => Commons.NumberTheory.RamificationInertia.ramificationIdx_one_bot
              𝔭 𝔓 h𝔭 h𝔭ne h𝔓)
    | insert a t ha ih =>
        obtain ⟨ihGal, ihRam⟩ := ih
        have hsup : (⨆ i ∈ insert a t, f i) = f a ⊔ ⨆ i ∈ t, f i := by
          rw [← Finset.sup_eq_iSup, Finset.sup_insert, Finset.sup_eq_iSup]
        constructor
        · rw [hsup]
          haveI : IsGalois F ↥(⨆ i ∈ t, f i) := ihGal
          infer_instance
        · have hsup' : f a ⊔ ⨆ i ∈ t, f i = ⨆ i ∈ insert a t, f i := hsup.symm
          haveI : IsGalois F ↥(⨆ i ∈ t, f i) := ihGal
          have hRHS : ∀ (𝔓 : Ideal (RingOfIntegers ↥(f a ⊔ ⨆ i ∈ t, f i))),
              𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥(f a ⊔ ⨆ i ∈ t, f i)) →
              𝔓.ramificationIdx (RingOfIntegers F) = 1 := by
            intro 𝔓 h𝔓
            obtain ⟨hprime, hlies⟩ := h𝔓
            exact ramificationIdx_one_sup_at (f a) (⨆ i ∈ t, f i) 𝔭 h𝔭 h𝔭ne
              𝔓 hprime hlies (h a) ihRam
          exact ramificationIdx_eq_one_transport_at hsup' 𝔭 h𝔭 h𝔭ne hRHS
  exact (hQ s).2



attribute [local instance] FractionRing.liftAlgebra

/-- Descent of unramifiedness at a fixed prime along a tower of number fields. -/
theorem ramificationIdx_one_tower_at {K E L : Type*} [Field K] [NumberField K]
    [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (𝔭 : Ideal (𝓞 K)) (_h𝔭 : 𝔭.IsPrime) (h𝔭ne : 𝔭 ≠ ⊥)
    (hL : ∀ (Q : Ideal (𝓞 L)), Q ∈ 𝔭.primesOver (𝓞 L) → Q.ramificationIdx (𝓞 K) = 1) :
    ∀ (P : Ideal (𝓞 E)), P ∈ 𝔭.primesOver (𝓞 E) → P.ramificationIdx (𝓞 K) = 1 := by
  intro P hP
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver 𝔭 := hPlies
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭ne P
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  by_contra he
  have hPdvd : P ∣ differentIdeal (𝓞 K) (𝓞 E) := by
    by_contra hcon
    exact he ((ramificationIdx_one_iff_not_dvd_differentIdeal (E := K) (K := E) P hPprime).mp hcon)
  obtain ⟨Q, hQmax, hQlies⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 E) (S := 𝓞 L) P
  haveI : Q.LiesOver P := hQlies
  haveI : Q.IsPrime := hQmax.isPrime
  haveI : Q.LiesOver 𝔭 := Ideal.LiesOver.trans Q P 𝔭
  have hQe : Q.ramificationIdx (𝓞 K) = 1 := hL Q ⟨inferInstance, inferInstance⟩
  have hQdvd : Q ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    rw [Ideal.dvd_iff_le]
    have htrans : differentIdeal (𝓞 K) (𝓞 L) =
        differentIdeal (𝓞 E) (𝓞 L) *
          (differentIdeal (𝓞 K) (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 L)) :=
      differentIdeal_eq_differentIdeal_mul_differentIdeal (A := 𝓞 K) (B := 𝓞 E) (C := 𝓞 L)
    rw [htrans]
    have hmapP : Ideal.map (algebraMap (𝓞 E) (𝓞 L)) P ≤ Q := by
      rw [Ideal.map_le_iff_le_comap]
      exact le_of_eq (Ideal.LiesOver.over (P := Q) (p := P))
    exact le_trans Ideal.mul_le_right
      (le_trans (Ideal.map_mono (Ideal.dvd_iff_le.mp hPdvd)) hmapP)
  exact (ramificationIdx_one_iff_not_dvd_differentIdeal (E := K) (K := L) Q inferInstance).mpr hQe hQdvd



/-- Descent of unramifiedness at a fixed prime from a finite compositum to a subfield. -/
theorem ramificationIdx_one_of_le_at {F : Type*} [Field F] [NumberField F]
    {M L : IntermediateField F (AlgebraicClosure F)} [FiniteDimensional F M] [FiniteDimensional F L]
    [NumberField ↥M] [NumberField ↥L] (hLM : L ≤ M)
    (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsPrime) (h𝔭ne : 𝔭 ≠ ⊥)
    (hM : ∀ Q : Ideal (𝓞 ↥M), Q ∈ 𝔭.primesOver (𝓞 ↥M) → Q.ramificationIdx (𝓞 F) = 1) :
    ∀ P : Ideal (𝓞 ↥L), P ∈ 𝔭.primesOver (𝓞 ↥L) → P.ramificationIdx (𝓞 F) = 1 := by
  intro P hP
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver 𝔭 := hPlies
  let Lr : IntermediateField F ↥M := IntermediateField.restrict hLM
  haveI : FiniteDimensional F ↥Lr :=
    Module.Finite.equiv (IntermediateField.restrictAlgEquiv hLM).toLinearEquiv
  haveI : NumberField ↥Lr := NumberField.of_module_finite F ↥Lr
  have hLr : ∀ Pr : Ideal (𝓞 ↥Lr), Pr ∈ 𝔭.primesOver (𝓞 ↥Lr) → Pr.ramificationIdx (𝓞 F) = 1 :=
    ramificationIdx_one_tower_at (K := F) (E := ↥Lr) (L := ↥M) 𝔭 h𝔭 h𝔭ne hM
  let e : ↥L ≃ₐ[F] ↥Lr := IntermediateField.restrictAlgEquiv hLM
  let φ : 𝓞 ↥L ≃ₐ[𝓞 F] 𝓞 ↥Lr := RingOfIntegers.mapAlgEquiv e
  have htrans : (P.comap φ.symm).ramificationIdx (𝓞 F) = P.ramificationIdx (𝓞 F) :=
    Commons.NumberTheory.RamificationInertia.ramificationIdx_comap_algEquiv 𝔭 h𝔭ne φ.symm P
  haveI : (P.comap φ.symm).IsPrime := inferInstance
  haveI : (P.comap φ.symm).LiesOver 𝔭 := Ideal.comap_liesOver P 𝔭 φ.symm
  have h1 : (P.comap φ.symm).ramificationIdx (𝓞 F) = 1 :=
    hLr (P.comap φ.symm) ⟨inferInstance, inferInstance⟩
  rw [← htrans]
  exact h1

set_option linter.unusedVariables false

/-- **The support of the relative different is preserved under passing to finite Galois
subextensions of a sup.**

Let `F` be a number field, `S` a finite set of natural numbers, and `f i` a family of
finite-dimensional Galois intermediate fields of `AlgebraicClosure F` such that the relative
different `differentIdeal (𝓞 F) (𝓞 ↥(f i))` is supported over `S` (i.e. every prime dividing it
lies over `(q)` for some `q ∈ S`).  Then any finite-dimensional Galois `L ≤ ⨆ i, f i` also has
its relative different `differentIdeal (𝓞 F) (𝓞 L)` supported over `S`.

This is the "support" analogue of
`Commons.FieldTheory.Galois.differentIdeal_eq_top_of_le_iSup_finite_unramified`: it reduces to the
statement that unramifiedness at a *fixed* prime is preserved by finite composita
(`ramificationIdx_one_iSup_finset_at`) together with the descent of unramifiedness along a tower
(`ramificationIdx_one_of_le_at`). -/
theorem differentIdeal_supp_le_iSup_finset {F : Type*} [Field F] [NumberField F] (S : Finset ℕ)
    {ι : Type*} {f : ι → IntermediateField F (AlgebraicClosure F)}
    [∀ i, NumberField ↥(f i)]
    (hfd : ∀ i, FiniteDimensional F ↥(f i)) (hgal : ∀ i, IsGalois F ↥(f i))
    (hsup : ∀ i, ∀ (P : Ideal (NumberField.RingOfIntegers ↥(f i))), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥(f i)) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)))
    {L : IntermediateField F (AlgebraicClosure F)} [NumberField ↥L]
    [FiniteDimensional F ↥L] [IsGalois F ↥L]
    (hL : L ≤ ⨆ i, f i) :
    ∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
  classical
  haveI hfdI : ∀ i, FiniteDimensional F ↥(f i) := hfd
  haveI hgalI : ∀ i, IsGalois F ↥(f i) := hgal
  intro P hPprime hPne hPdvd
  by_contra hno
  push Not at hno
  obtain ⟨s, hs⟩ :=
    Commons.FieldTheory.IntermediateField.exists_finset_of_le_iSup_of_finiteDimensional hL
  let M : IntermediateField F (AlgebraicClosure F) := ⨆ i ∈ s, f i
  have hLM : L ≤ M := hs
  haveI : NumberField ↥M := NumberField.of_module_finite F ↥M
  -- the prime of `𝓞 F` below `P`
  let 𝔭 : Ideal (𝓞 F) := P.under (𝓞 F)
  haveI h𝔭prime : 𝔭.IsPrime := inferInstance
  have h𝔭ne : 𝔭 ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 F) hPne
  -- Every prime of `𝓞 ↥(f i)` over `𝔭` is unramified over `𝓞 F`.
  have hunram : ∀ i, ∀ 𝔓 : Ideal (𝓞 ↥(f i)),
      𝔓 ∈ 𝔭.primesOver (𝓞 ↥(f i)) → 𝔓.ramificationIdx (𝓞 F) = 1 := by
    intro i 𝔓 h𝔓
    obtain ⟨h𝔓prime, h𝔓lies⟩ := h𝔓
    haveI : 𝔓.IsPrime := h𝔓prime
    haveI : 𝔓.LiesOver 𝔭 := h𝔓lies
    have h𝔓ne : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭ne 𝔓
    by_contra he
    have h𝔓dvd : 𝔓 ∣ differentIdeal (𝓞 F) (𝓞 ↥(f i)) := by
      by_contra hcon
      exact he ((ramificationIdx_one_iff_not_dvd_differentIdeal (E := F) (K := ↥(f i))
        𝔓 h𝔓prime).mp hcon)
    obtain ⟨q, hqS, hq⟩ := hsup i 𝔓 h𝔓prime h𝔓ne h𝔓dvd
    have h𝔭q : 𝔭.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      Ideal.LiesOver.tower_bot 𝔓 𝔭 (Ideal.span ({(q : ℤ)} : Set ℤ))
    exact hno q hqS (Ideal.LiesOver.trans P 𝔭 (Ideal.span ({(q : ℤ)} : Set ℤ)))
  -- The finite compositum `M` is unramified at `𝔭`.
  have hM : ∀ Q : Ideal (𝓞 ↥M), Q ∈ 𝔭.primesOver (𝓞 ↥M) → Q.ramificationIdx (𝓞 F) = 1 :=
    ramificationIdx_one_iSup_finset_at s f 𝔭 h𝔭prime h𝔭ne hunram
  -- Descent to `L ≤ M`.
  have hLunram : ∀ P' : Ideal (𝓞 ↥L), P' ∈ 𝔭.primesOver (𝓞 ↥L) → P'.ramificationIdx (𝓞 F) = 1 :=
    ramificationIdx_one_of_le_at hLM 𝔭 h𝔭prime h𝔭ne hM
  have hPmem : P ∈ 𝔭.primesOver (𝓞 ↥L) := ⟨hPprime, inferInstance⟩
  have he1 : P.ramificationIdx (𝓞 F) = 1 := hLunram P hPmem
  exact ((ramificationIdx_one_iff_not_dvd_differentIdeal (E := F) (K := ↥L) P hPprime).mpr he1)
    hPdvd

end Commons.NumberTheory.NumberField
