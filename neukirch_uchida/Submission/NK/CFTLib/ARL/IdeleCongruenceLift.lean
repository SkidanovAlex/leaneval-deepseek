import Mathlib
import Submission.NK.CFTLib.ARL.Cyclic
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists

/-!
# The idèle–ideal dictionary over the congruence subgroup

Helper lemmas for `NK.CFTLib.ARL.index_principalRay_sup_normIdeals_le`:  the interaction between
the congruence subgroup `NK.CFTLib.Arl.congruenceSubgroup K m ≤ 𝕀 K`, the ideal map
`Idele.idealOf`, the ray `NK.CFTLib.ARL.principalRay K m` and the norm group
`NK.CFTLib.ARL.normIdeals K L m`.

* `idealOfUnitHom_principalIdele`, `unitsToIdealUnits_mem_principalRay` — the principal idèle `(γ)`
  is in the ray `P_m` exactly when `γ ≡ 1 (m)`;
* `count_idealOf_eq_zero_of_congruence` — an idèle which is `≡ 1 (m)` at `𝔭` is a local unit there,
  so its ideal has zero `𝔭`-adic exponent;
* `mem_inf_congruence_of_mul_eq` — the ratio of two congruent idèles is a congruent principal idèle;
* `exists_adjust_congruenceSubgroup` — weak approximation in the congruence form;
* `exists_idealOf_eq_of_mem_Icoprime` — every fractional ideal prime to `m` is the ideal of an idèle
  congruent to `1` modulo `m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ARL

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## Principal idèles and the ray -/

/-- The ideal of a principal idèle is the principal fractional ideal. -/
lemma idealOfUnitHom_principalIdele (γ : Kˣ) :
    IdeleClassGroup.idealOfUnitHom K (Idele.principalIdele K γ) = unitsToIdealUnits K γ := by
  refine Units.ext ?_
  simp only [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, unitsToIdealUnits_coe,
    Idele.idealOf_principalIdele]

/-- The principal ideal `(γ)` lies in the ray `P_m` as soon as `γ` is congruent to `1` modulo
`m` (and positive at the real places). -/
lemma unitsToIdealUnits_mem_principalRay (m : ℕ) {γ : Kˣ}
    (hγ : Idele.principalIdele K γ ∈ NK.CFTLib.Arl.congruenceSubgroup K m) :
    unitsToIdealUnits K γ ∈ principalRay K m :=
  Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩

/-! ## The congruence condition and the ideal -/

/-- An idèle which is congruent to `1` modulo `m` at `𝔭` is a local unit there, so its ideal has
zero `𝔭`-adic exponent. -/
lemma count_idealOf_eq_zero_of_congruence {m : ℕ} {x : Idele K} (hx : x ∈ NK.CFTLib.Arl.congruenceSubgroup K m)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∈ 𝔭.asIdeal) :
    FractionalIdeal.count K 𝔭 (Idele.idealOf x) = 0 := by
  classical
  rw [Idele.count_idealOf, Idele.exp_def]
  have hlt : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1) < 1 :=
    lt_of_le_of_lt (hx.1 𝔭 h𝔭) (NK.CFTLib.Arl.val_natCast_lt_one 𝔭 m h𝔭)
  have hval : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left
      (v := Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := (1 : 𝔭.adicCompletion K))
      (y := ((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1) (by simpa using hlt)
    rw [map_one, show (1 : 𝔭.adicCompletion K) +
      (((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1) =
        ((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) from by ring] at h
    exact h
  rw [hval]
  simp

/-- For idèles `x y` which are congruent to `1` modulo `m`, the ratio `x / y` is a principal
idèle: more precisely, if `x, y ∈ 𝕀 K` are congruent to `1` modulo `m` and `x = y * (γ)` for
`γ : Kˣ`, then `γ` is itself congruent to `1` modulo `m`. -/
lemma mem_inf_congruence_of_mul_eq {m : ℕ} {x y : Idele K} (hx : x ∈ NK.CFTLib.Arl.congruenceSubgroup K m)
    (hy : y ∈ NK.CFTLib.Arl.congruenceSubgroup K m) {γ : Kˣ}
    (h : x = y * Idele.principalIdele K γ) :
    Idele.principalIdele K γ ∈ NK.CFTLib.Arl.congruenceSubgroup K m := by
  have h' : Idele.principalIdele K γ = y⁻¹ * x := by rw [h]; group
  rw [h']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hx

/-- **The adjustment.**  Every idèle can be multiplied by a principal idèle so as to become
congruent to `1` modulo `m`. -/
theorem exists_adjust_congruenceSubgroup (K : Type*) [Field K] [NumberField K] (m : ℕ)
    (hm : 0 < m) (y : Idele K) :
    ∃ d : Kˣ, y * Idele.principalIdele K d ∈ NK.CFTLib.Arl.congruenceSubgroup K m := by
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m := by
    ext x
    rw [hU.1 x]
    rfl
  obtain ⟨d, hd⟩ := hadj y
  exact ⟨d, hUeq ▸ hd⟩

/-! ## Lifting fractional ideals to congruent idèles -/

/-- **Every fractional ideal prime to `m` is the ideal of an idèle congruent to `1` modulo `m`**:
the ideal map sends the congruence subgroup `U_m` onto `I(m)`. -/
theorem exists_idealOf_eq_of_mem_Icoprime {m : ℕ} (hm : 0 < m) (𝔞 : Icoprime K m) :
    ∃ x : Idele K, x ∈ NK.CFTLib.Arl.congruenceSubgroup K m ∧
      IdeleClassGroup.idealOfUnitHom K x = (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  classical
  set f : HeightOneSpectrum (𝓞 K) → ℤ :=
    fun 𝔭 => FractionalIdeal.count K 𝔭 (𝔞.1 : FractionalIdeal (𝓞 K)⁰ K) with hf_def
  have hf : ∀ᶠ 𝔭 in Filter.cofinite, f 𝔭 = 0 :=
    FractionalIdeal.finite_factors (K := K) (I := (𝔞.1 : FractionalIdeal (𝓞 K)⁰ K))
  refine ⟨IdeleClassGroup.ideleOfFun K f hf, ⟨?_, ?_⟩, ?_⟩
  · intro 𝔭 h𝔭
    have hf0 : f 𝔭 = 0 := by
      rw [hf_def]
      exact (mem_Icoprime (K := K) (m := m)).mp 𝔞.2 𝔭 h𝔭
    have h1 : ((IdeleClassGroup.ideleOfFun K f hf (Place.ofFinite 𝔭) :
        (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) = 1 := by
      change ((IdeleClassGroup.unifUnit K 𝔭 ^ (f 𝔭) : (𝔭.adicCompletion K)ˣ) :
        𝔭.adicCompletion K) = 1
      rw [hf0, zpow_zero]
      rfl
    show Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((IdeleClassGroup.ideleOfFun K f hf (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) :
        𝔭.adicCompletion K) - 1) ≤ _
    rw [h1, sub_self, map_zero]
    exact zero_le
  · intro w
    exact NK.CFTLib.Arl.posAtReal_one w
  · refine Units.ext ?_
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0]
    exact IdeleClassGroup.fractionalIdeal_eq_of_count_eq (Idele.idealOf_ne_zero _) 𝔞.1.ne_zero
      (fun 𝔭 => by rw [IdeleClassGroup.count_idealOf_ideleOfFun])

end NK.CFTLib.ARL
