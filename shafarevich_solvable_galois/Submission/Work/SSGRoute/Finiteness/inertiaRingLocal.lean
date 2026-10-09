import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExpInertia
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.differentIdeal_inertiaRing_eq_top
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletion_intCast_eq_padicValInt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

/-!
# The local ring structure of the inertia ring `𝒪_E` of a `p`-adic completion

For a number field `K`, a rational prime `p` with prime `Q₀ = (p)` of `𝓞 ℚ` and a prime `Q | Q₀`
of `𝓞 K`, let `L = Q.adicCompletion K`, `B = 𝒪_L`, `ℤ_p = Q₀.adicCompletionIntegers ℚ`,
`E = ℚ_p(ζ) ⊆ L` and `C = 𝒪_E = integralClosure ℤ_p E`.  This file proves that `C` is a local
ring with maximal ideal `pC = span{p}`, hence that the inclusion `ℤ_p → C` is a local homomorphism.
-/

open scoped NumberField WithZero
open IsDedekindDomain

namespace Work.SSGRoute.Finiteness

open Work.SSGRoute.TatePoitouRoute.FinitenessHM

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
variable (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
variable [hQ : Q.asIdeal.LiesOver Q0.asIdeal]
variable (ζ : Q.adicCompletionIntegers K)

/-- The image of `x ∈ 𝒪_E` under `inertiaMap` has the same image in `L`. -/
lemma inertiaRing_coe_inertiaMap (x : ↥(inertiaRing Q0 Q ζ)) :
    ((inertiaMap Q0 Q ζ x : Q.adicCompletionIntegers K) : Q.adicCompletion K)
      = (x : Q.adicCompletion K) :=
  inertiaMap_apply Q0 Q ζ x

/-- `𝒪_E` is the intersection of `E` with `𝒪_L` inside `L`. -/
lemma inertiaRing_mem_iff (y : ↥(inertiaField Q0 Q ζ)) :
    y ∈ inertiaRing Q0 Q ζ ↔
      (algebraMap ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) y) ∈
        (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) := by
  constructor
  · intro hy
    have h1 : IsIntegral (Q0.adicCompletionIntegers ℚ) y :=
      IsIntegral.algebraMap (IsIntegralClosure.isIntegral (Q0.adicCompletionIntegers ℚ)
        ↥(inertiaField Q0 Q ζ) (⟨y, hy⟩ : ↥(inertiaRing Q0 Q ζ)))
    have h2 : IsIntegral (Q0.adicCompletionIntegers ℚ)
        (algebraMap ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) y) :=
      IsIntegral.algebraMap (R := Q0.adicCompletionIntegers ℚ)
        (A := ↥(inertiaField Q0 Q ζ)) (B := Q.adicCompletion K) h1
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff
      (A := ↥(Q.adicCompletionIntegers K)) (R := Q0.adicCompletionIntegers ℚ)
      (B := Q.adicCompletion K)).mp h2
    rw [← hb]
    exact b.2
  · intro hy
    rw [mem_integralClosure_iff]
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom _ ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K))
      (algebraMap ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K)).injective).mp ?_
    rw [IsScalarTower.coe_toAlgHom']
    let b : ↥(Q.adicCompletionIntegers K) :=
      ⟨algebraMap ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) y, hy⟩
    exact IsIntegral.map (IsScalarTower.toAlgHom (Q0.adicCompletionIntegers ℚ)
        ↥(Q.adicCompletionIntegers K) (Q.adicCompletion K))
      (IsIntegralClosure.isIntegral (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K) b)

/-- For `x ∈ 𝒪_E`, `x` is a unit of `𝒪_E` iff it is a unit of `𝒪_L`. -/
lemma inertiaRing_isUnit_iff (x : ↥(inertiaRing Q0 Q ζ)) :
    IsUnit x ↔ IsUnit (inertiaMap Q0 Q ζ x) := by
  let B := Q.adicCompletionIntegers K
  let E := ↥(inertiaField Q0 Q ζ)
  let M := Q.adicCompletion K
  let iEM : E →+* M := algebraMap E M
  let iBM : B →+* M := algebraMap B M
  have hcoe : iBM (inertiaMap Q0 Q ζ x) = iEM (x : E) :=
    inertiaMap_apply Q0 Q ζ x
  refine ⟨fun h => h.map (inertiaMap Q0 Q ζ).toMonoidHom, fun h => ?_⟩
  obtain ⟨u, hu⟩ := h
  have hcoe' : iBM (u : B) = iEM (x : E) := by rw [← hcoe, hu]
  have hinv' : iBM ((u⁻¹ : Bˣ) : B) = (iBM ((u : Bˣ) : B))⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul, ← Units.val_mul]
    simp
  have hx0 : iEM (x : E) ≠ 0 := by
    rw [← hcoe']
    intro h
    exact u.ne_zero (Subtype.ext h)
  have hmem : ((x : E)⁻¹) ∈ inertiaRing Q0 Q ζ := by
    rw [inertiaRing_mem_iff]
    have h1 : iEM ((x : E)⁻¹) = iBM ((u⁻¹ : Bˣ) : B) := by
      rw [map_inv₀, ← hcoe', hinv']
    rw [h1]
    exact ((u⁻¹ : Bˣ) : B).2
  refine ⟨⟨x, ⟨(x : E)⁻¹, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    apply Subtype.ext
    change iEM ((x : E) * (x : E)⁻¹) = 1
    rw [map_mul, map_inv₀]
    exact mul_inv_cancel₀ hx0
  · apply Subtype.ext
    apply Subtype.ext
    change iEM ((x : E)⁻¹ * (x : E)) = 1
    rw [map_mul, map_inv₀]
    exact inv_mul_cancel₀ hx0

instance inertiaRing_isLocalRing : IsLocalRing ↥(inertiaRing Q0 Q ζ) := by
  refine { exists_pair_ne := ⟨0, 1, zero_ne_one⟩, isUnit_or_isUnit_of_add_one := ?_ }
  intro a b hab
  by_cases ha : IsUnit a
  · exact Or.inl ha
  · refine Or.inr ((inertiaRing_isUnit_iff Q0 Q ζ b).mpr ?_)
    have hφa : (inertiaMap Q0 Q ζ a) ∈
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun h => ha ((inertiaRing_isUnit_iff Q0 Q ζ a).mpr h)
    have hsum : inertiaMap Q0 Q ζ a + inertiaMap Q0 Q ζ b = 1 := by
      rw [← map_add, hab, map_one]
    have hone : (1 : Q.adicCompletionIntegers K) ∉
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal (Q.adicCompletionIntegers K)).ne_top
        (Ideal.eq_top_iff_one _ |>.mpr h)
    have hne : ¬ (1 - inertiaMap Q0 Q ζ a ∈
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := by
      intro h
      apply hone
      rw [show (1 : Q.adicCompletionIntegers K) =
        (1 - inertiaMap Q0 Q ζ a) + inertiaMap Q0 Q ζ a by ring]
      exact (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).add_mem h hφa
    rw [show inertiaMap Q0 Q ζ b = 1 - inertiaMap Q0 Q ζ a by rw [← hsum]; ring]
    exact of_not_not fun h =>
      hne ((IsLocalRing.mem_maximalIdeal _).mpr ((mem_nonunits_iff).mpr h))

lemma inertiaRing_maximalIdeal_eq_comap :
    IsLocalRing.maximalIdeal ↥(inertiaRing Q0 Q ζ) =
      Ideal.comap (inertiaMap Q0 Q ζ).toRingHom
        (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := by
  ext c
  rw [IsLocalRing.mem_maximalIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff]
  exact (inertiaRing_isUnit_iff Q0 Q ζ c).not

/-- A left factor of a unit is a unit. -/
lemma isUnit_of_mul_isUnit_of_comm {S : Type*} [CommRing S] {a b : S} (h : IsUnit (a * b)) :
    IsUnit a := by
  obtain ⟨u, hu⟩ := h
  refine ⟨⟨a, b * ↑u⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← mul_assoc, ← hu, Units.mul_inv]
  · rw [mul_assoc, mul_comm ↑u⁻¹ a, ← mul_assoc, mul_comm b a, ← hu, Units.mul_inv]

section Uniformizer

variable {p : ℕ} [Fact p.Prime]
variable (hQ0 : Q0.asIdeal = Ideal.span
  ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
variable (hD : differentIdeal (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ) = ⊤)

include hQ0 hD in
/-- **`p` is a uniformiser of the inertia ring.**  The different `𝔡_{ℤ_p → 𝒪_E}` is trivial, hence
`ℤ_p → 𝒪_E` is unramified and `𝔪_{ℤ_p}·𝒪_E = 𝔪_{𝒪_E}`, i.e. `𝔪_{𝒪_E} = span{p}`. -/
theorem inertiaRing_maximalIdeal_eq_span_p :
    IsLocalRing.maximalIdeal ↥(inertiaRing Q0 Q ζ) =
      Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)) := by
  classical
  have hmemA : (p : NumberField.RingOfIntegers ℚ) ∈ Q0.asIdeal := by
    rw [hQ0]; exact Ideal.mem_span_singleton_self _
  have hvalQp : Valued.v (R := Q0.adicCompletion ℚ) (Γ₀ := WithZero (Multiplicative ℤ))
      ((p : Q0.adicCompletion ℚ)) = WithZero.exp (-1 : ℤ) := by
    have h :=
      Commons.NumberTheory.NumberField.Completion.val_adicCompletion_intCast_eq_padicValInt
        Q0 p (Fact.out) hmemA (p : ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    rw [show (((p : ℤ) : ℚ) : Q0.adicCompletion ℚ) = ((p : ℕ) : Q0.adicCompletion ℚ) by
        push_cast; ring, padicValInt.self (Fact.out : p.Prime).one_lt] at h
    simpa using h
  have h𝔪ℤp : IsLocalRing.maximalIdeal (Q0.adicCompletionIntegers ℚ) =
      Ideal.span ({(p : Q0.adicCompletionIntegers ℚ)}) :=
    Commons.NumberTheory.NumberField.Completion.maximalIdeal_eq_span_of_valuation_eq_exp_neg_one
      (Valued.v : Valuation (Q0.adicCompletion ℚ) ℤᵐ⁰) hvalQp
  have hvalpM : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((p : Q.adicCompletion K)) =
      WithZero.exp (-(Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) : ℤ)) := by
    have h := Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q0 Q hQ
      (p : Q0.adicCompletion ℚ)
    rw [hvalQp, ← WithZero.exp_nsmul] at h
    have h2 : (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ) (p : Q0.adicCompletion ℚ)
        = (p : Q.adicCompletion K) := map_natCast _ p
    rw [h2] at h
    rw [h]
    congr 1
    simp [nsmul_eq_mul]
  have hpNotUnitB : ¬ IsUnit ((p : Q.adicCompletionIntegers K)) := by
    intro h
    have h1 : Valued.v (((p : Q.adicCompletionIntegers K)) : Q.adicCompletion K) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp h
    rw [show (((p : Q.adicCompletionIntegers K)) : Q.adicCompletion K) = (p : Q.adicCompletion K)
        from map_natCast (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) p] at h1
    rw [hvalpM, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ)
      from WithZero.exp_zero.symm, WithZero.exp_inj] at h1
    have hzero : Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 0 := by omega
    exact (Ideal.ramificationIdx_pos (NumberField.RingOfIntegers ℚ) Q.asIdeal).ne' hzero
  have hpNotUnitC : ¬ IsUnit ((p : ↥(inertiaRing Q0 Q ζ))) := by
    intro h
    refine hpNotUnitB ?_
    have h1 : inertiaMap Q0 Q ζ ((p : ↥(inertiaRing Q0 Q ζ))) =
        (p : Q.adicCompletionIntegers K) := map_natCast _ p
    rw [← h1]
    exact (inertiaRing_isUnit_iff Q0 Q ζ (p : ↥(inertiaRing Q0 Q ζ))).mp h
  haveI : Algebra.EssFiniteType (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ) :=
    Algebra.EssFiniteType.of_finiteType _ _
  haveI hlocHom : IsLocalHom (algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ)) :=
    ⟨fun a ha => by
      by_contra ha'
      have hmem : a ∈ IsLocalRing.maximalIdeal (Q0.adicCompletionIntegers ℚ) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact ha'
      rw [h𝔪ℤp, Ideal.mem_span_singleton] at hmem
      obtain ⟨b, hb⟩ := hmem
      have hsplit : (p : ↥(inertiaRing Q0 Q ζ)) *
          algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ) b =
          algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ) a := by
        rw [← map_natCast (algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ)) p,
          ← map_mul, ← hb]
      have h1 : IsUnit ((p : ↥(inertiaRing Q0 Q ζ)) *
          algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ) b) := by
        rw [hsplit]; exact ha
      exact hpNotUnitC (isUnit_of_mul_isUnit_of_comm h1)⟩
  have hUnram : Algebra.IsUnramifiedAt (Q0.adicCompletionIntegers ℚ)
      (IsLocalRing.maximalIdeal ↥(inertiaRing Q0 Q ζ)) := by
    rw [← not_dvd_differentIdeal_iff]
    intro hdvd
    rw [hD] at hdvd
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(inertiaRing Q0 Q ζ)).ne_top
      (eq_top_iff.mpr (Ideal.dvd_iff_le.mp hdvd))
  haveI hloc : IsLocalization (IsLocalRing.maximalIdeal ↥(inertiaRing Q0 Q ζ)).primeCompl
      ↥(inertiaRing Q0 Q ζ) :=
    IsLocalization.of_le_isUnit fun x hx => by
      have hx' : ¬ (x ∈ IsLocalRing.maximalIdeal ↥(inertiaRing Q0 Q ζ)) := hx
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx'
      exact of_not_not hx'
  have hFF : Algebra.FormallyUnramified (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ) := by
    have e : Localization.AtPrime (IsLocalRing.maximalIdeal ↥(inertiaRing Q0 Q ζ)) ≃ₐ[↥(inertiaRing Q0 Q ζ)]
        ↥(inertiaRing Q0 Q ζ) :=
      IsLocalization.algEquiv (IsLocalRing.maximalIdeal ↥(inertiaRing Q0 Q ζ)).primeCompl _ _
    exact (Algebra.FormallyUnramified.iff_of_equiv (e.restrictScalars
      (Q0.adicCompletionIntegers ℚ))).mp hUnram
  have hmain : (IsLocalRing.maximalIdeal (Q0.adicCompletionIntegers ℚ)).map
      (algebraMap (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ)) =
      IsLocalRing.maximalIdeal ↥(inertiaRing Q0 Q ζ) :=
    ((Algebra.FormallyUnramified.iff_map_maximalIdeal_eq).mp hFF).2
  rw [← hmain, h𝔪ℤp, Ideal.map_span, Set.image_singleton, map_natCast]

end Uniformizer

end

end Work.SSGRoute.Finiteness
