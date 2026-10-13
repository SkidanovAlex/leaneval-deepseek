import Submission.Work.DSAM3.Main

/-! # DSAM3: API for the model-level splitting predicate

Interface lemmas for `DSMap.Mix.ModSplit` (frozen) and its `A`-linear form `ModSplitA`:
monotonicity in the ideal, multiplication of the value (AM1, `A`-form), extension of scalars
(the easy direction of AM2), and the `A`-form of the retraction transport (AM3).
-/

open scoped TensorProduct
open CategoryTheory

namespace Work.DSAM3

universe a

variable {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
  (ε : ModuleCat.of A A ⟶ P.X 0)

/-- A splitting modulo `I` is a splitting modulo any larger ideal `J`: compose with the quotient
map `D ⧸ I → D ⧸ J`. -/
theorem modSplitA_mono {D : Type a} [CommRing D] (ψ : A →+* D) {I J : Ideal D} (hIJ : I ≤ J)
    (c : D) (h : ModSplitA P ε ψ I c) : ModSplitA P ε ψ J c := by
  letI : Algebra A D := ψ.toAlgebra
  obtain ⟨t, ht1, ht2⟩ := h
  have hle : (I : Submodule D D) ≤ Submodule.comap (LinearMap.id : D →ₗ[D] D) (J : Submodule D D) :=
    fun x hx => hIJ hx
  refine ⟨(LinearMap.restrictScalars A (Submodule.mapQ (I : Submodule D D) (J : Submodule D D)
    (LinearMap.id : D →ₗ[D] D) hle)).comp t, ?_, ?_⟩
  · ext x
    have h0 : t ((P.d (-1) 0).hom x) = 0 := by
      simpa using LinearMap.congr_fun ht1 x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.restrictScalars_apply,
      h0, map_zero]
  · rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, ht2]
    rw [← Ideal.Quotient.mk_eq_mk]
    rw [← Ideal.Quotient.mk_eq_mk (I := J) c]
    exact Submodule.mapQ_apply _ _ _ c

/-- A splitting modulo `I` is a splitting modulo any larger ideal `J`. -/
theorem modSplit_mono {D : Type a} [CommRing D] (ψ : A →+* D) {I J : Ideal D} (hIJ : I ≤ J)
    (c : D) (h : DSMap.Mix.ModSplit P ε ψ I c) : DSMap.Mix.ModSplit P ε ψ J c :=
  (modSplit_iff_ModSplitA P ε ψ J c).mpr
    (modSplitA_mono P ε ψ hIJ c ((modSplit_iff_ModSplitA P ε ψ I c).mp h))

/-- AM1 in the `A`-linear form: a splitting with value `c` gives one with value `c * d`. -/
theorem modSplitA_mul {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) (c d : D)
    (h : ModSplitA P ε ψ I c) : ModSplitA P ε ψ I (c * d) := by
  letI : Algebra A D := ψ.toAlgebra
  obtain ⟨t, ht1, ht2⟩ := h
  refine ⟨(Ideal.Quotient.mk I d) • t, ?_, ?_⟩
  · ext x
    have h0 : t ((P.d (-1) 0).hom x) = 0 := by
      simpa using LinearMap.congr_fun ht1 x
    rw [LinearMap.comp_apply, LinearMap.smul_apply, h0, smul_zero, LinearMap.zero_apply]
  · rw [LinearMap.smul_apply, ht2, smul_eq_mul, ← map_mul, mul_comm]

/-- The value can be shrunk by a unit factor: a splitting with value `c * u` gives one with value
`c` when `u` is a unit.  Together with `modSplitA_mul` this says the set of achievable values is
stable under multiplication and inversion by units. -/
theorem modSplitA_of_mul_unit {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) (c : D)
    (u : Dˣ) (h : ModSplitA P ε ψ I (c * u)) : ModSplitA P ε ψ I c := by
  letI : Algebra A D := ψ.toAlgebra
  obtain ⟨t, ht1, ht2⟩ := h
  refine ⟨(Ideal.Quotient.mk I (↑u⁻¹ : D)) • t, ?_, ?_⟩
  · ext x
    have h0 : t ((P.d (-1) 0).hom x) = 0 := by
      simpa using LinearMap.congr_fun ht1 x
    rw [LinearMap.comp_apply, LinearMap.smul_apply, h0, smul_zero, LinearMap.zero_apply]
  · rw [LinearMap.smul_apply, ht2, smul_eq_mul, ← map_mul]
    congr 1
    rw [← mul_assoc, mul_comm (↑u⁻¹ : D) c, mul_assoc, Units.inv_mul, mul_one]

/-- The value can be shrunk by an `IsUnit` factor. -/
theorem modSplitA_of_mul_isUnit {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) (c u : D)
    (hu : IsUnit u) (h : ModSplitA P ε ψ I (c * u)) : ModSplitA P ε ψ I c :=
  modSplitA_of_mul_unit P ε ψ I c hu.unit (by simpa only [hu.unit_spec] using h)

/-- The value can be shrunk by a unit factor, frozen form. -/
theorem modSplit_of_mul_unit {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) (c : D)
    (u : Dˣ) (h : DSMap.Mix.ModSplit P ε ψ I (c * u)) : DSMap.Mix.ModSplit P ε ψ I c :=
  (modSplit_iff_ModSplitA P ε ψ I c).mpr
    (modSplitA_of_mul_unit P ε ψ I c u ((modSplit_iff_ModSplitA P ε ψ I (c * u)).mp h))

/-- The value can be shrunk by an `IsUnit` factor, frozen form. -/
theorem modSplit_of_mul_isUnit {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) (c u : D)
    (hu : IsUnit u) (h : DSMap.Mix.ModSplit P ε ψ I (c * u)) : DSMap.Mix.ModSplit P ε ψ I c :=
  (modSplit_iff_ModSplitA P ε ψ I c).mpr (modSplitA_of_mul_isUnit P ε ψ I c u hu
    ((modSplit_iff_ModSplitA P ε ψ I (c * u)).mp h))

/-- The zero value: a splitting modulo `I` with value `0` always exists. -/
theorem modSplitA_zero {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) :
    ModSplitA P ε ψ I 0 := by
  letI : Algebra A D := ψ.toAlgebra
  refine ⟨0, by simp, ?_⟩
  rw [LinearMap.zero_apply]
  exact (map_zero (Ideal.Quotient.mk I)).symm

/-- The zero value, frozen form. -/
theorem modSplit_zero {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) :
    DSMap.Mix.ModSplit P ε ψ I 0 :=
  (modSplit_iff_ModSplitA P ε ψ I 0).mpr (modSplitA_zero P ε ψ I)

/-- **Extension of scalars** (the easy direction of AM2): a splitting modulo `I` pushes forward
along any `D`-algebra `D'` to a splitting modulo `I · D'`, with value `d ↦ algebraMap d`. -/
theorem modSplitA_baseChange {D D' : Type a} [CommRing D] [CommRing D'] (ψ : A →+* D) [Algebra D D']
    (I : Ideal D) (c : D) (h : ModSplitA P ε ψ I c) :
    ModSplitA P ε ((algebraMap D D').comp ψ) (I.map (algebraMap D D')) (algebraMap D D' c) := by
  letI : Algebra A D := ψ.toAlgebra
  letI : Algebra A D' := ((algebraMap D D').comp ψ).toAlgebra
  haveI : IsScalarTower A D D' := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  obtain ⟨t, ht1, ht2⟩ := h
  have hle : (I : Submodule D D) ≤
      Submodule.comap (Algebra.linearMap D D') ((I.map (algebraMap D D')).restrictScalars D) :=
    fun x hx => Ideal.mem_map_of_mem _ hx
  set q : (D ⧸ I) →ₗ[D] (D' ⧸ I.map (algebraMap D D')) :=
    Submodule.mapQ (I : Submodule D D) ((I.map (algebraMap D D')).restrictScalars D)
      (Algebra.linearMap D D') hle with hq
  refine ⟨(LinearMap.restrictScalars A q).comp t, ?_, ?_⟩
  · ext x
    have h0 : t ((P.d (-1) 0).hom x) = 0 := by
      simpa using LinearMap.congr_fun ht1 x
    show (LinearMap.restrictScalars A q) (t ((P.d (-1) 0).hom x)) = 0
    rw [h0, map_zero]
  · show (LinearMap.restrictScalars A q) (t ((ModuleCat.Hom.hom ε) 1)) =
      Ideal.Quotient.mk (I.map (algebraMap D D')) (algebraMap D D' c)
    rw [ht2, LinearMap.restrictScalars_apply, hq]
    rw [← Ideal.Quotient.mk_eq_mk,
      ← Ideal.Quotient.mk_eq_mk (I := I.map (algebraMap D D')) (algebraMap D D' c)]
    exact Submodule.mapQ_apply _ _ _ c

/-- **AM3 in the `A`-linear form**: transport of a splitting along an almost retraction. -/
theorem modSplitA_of_retraction_proved {D D' : Type a} [CommRing D] [CommRing D']
    (ψ : A →+* D) [Algebra D D'] (I : Ideal D) (σ : D' →ₗ[D] D) (c c' : D)
    (hσI : ∀ x ∈ I.map (algebraMap D D'), σ x ∈ I) (hσ1 : σ 1 = c')
    (h : ModSplitA P ε ((algebraMap D D').comp ψ) (I.map (algebraMap D D')) (algebraMap D D' c)) :
    ModSplitA P ε ψ I (c * c') :=
  (modSplit_iff_ModSplitA P ε ψ I (c * c')).mp
    (modSplit_of_retraction_proved P ε ψ I σ c c' hσI hσ1
      ((modSplit_iff_ModSplitA P ε ((algebraMap D D').comp ψ) (I.map (algebraMap D D'))
        (algebraMap D D' c)).mpr h))

end Work.DSAM3
