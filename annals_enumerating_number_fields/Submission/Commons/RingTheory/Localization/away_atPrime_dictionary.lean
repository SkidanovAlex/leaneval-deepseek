import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.RingTheory.Localization

open IsLocalization

/-- If `φ : R →+* S` is a surjective ring homomorphism onto a field `S` whose kernel is
"annihilated by its complement", then, viewing `S` as an `R`-algebra via `φ`, it is the
localization of `R` at the complement of `RingHom.ker φ`. -/
theorem isLocalization_primeCompl_ker_of_ann {R S : Type*} [CommRing R] [Field S] (φ : R →+* S)
    [(RingHom.ker φ).IsPrime] (hsurj : Function.Surjective φ)
    (hann : ∀ x ∈ RingHom.ker φ, ∃ c : R, c ∉ RingHom.ker φ ∧ c * x = 0) :
    @IsLocalization R _ (RingHom.ker φ).primeCompl S _ φ.toAlgebra := by
  let _ : Algebra R S := φ.toAlgebra
  have halg : ∀ x : R, algebraMap R S x = φ x := fun x => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [halg]
    exact isUnit_iff_ne_zero.mpr (fun h => y.2 h)
  · intro z
    obtain ⟨x, hx⟩ := hsurj z
    exact ⟨(x, 1), by rw [halg, halg]; simp [hx]⟩
  · intro x y h
    rw [halg, halg] at h
    have hxy : (x - y) ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, h, sub_self]
    obtain ⟨c, hc, hcx⟩ := hann (x - y) hxy
    have hcx' : c * x = c * y := by
      rw [mul_sub] at hcx
      exact sub_eq_zero.mp hcx
    exact ⟨⟨c, hc⟩, by simpa using hcx'⟩

/-- If `φ : R →+* S` is a surjective ring homomorphism onto a field `S` whose kernel is
"annihilated by its complement", then the localization of `R` at the kernel of `φ` is a field. -/
theorem isField_localizationAtPrime_ker_of_ann {R S : Type*} [CommRing R] [Field S] (φ : R →+* S)
    [(RingHom.ker φ).IsPrime] (hsurj : Function.Surjective φ)
    (hann : ∀ x ∈ RingHom.ker φ, ∃ c : R, c ∉ RingHom.ker φ ∧ c * x = 0) :
    IsField (Localization.AtPrime (RingHom.ker φ)) := by
  let _ : Algebra R S := φ.toAlgebra
  have hloc : IsLocalization (RingHom.ker φ).primeCompl S :=
    isLocalization_primeCompl_ker_of_ann φ hsurj hann
  exact MulEquiv.isField (Field.toIsField S)
    (IsLocalization.algEquiv (RingHom.ker φ).primeCompl S
      (Localization.AtPrime (RingHom.ker φ))).toRingEquiv.toMulEquiv.symm

/-- Given a maximal ideal `𝔭` of `A` with `f ∉ 𝔭` and `A_𝔭 ≅ K` for a field `K`, the ring
`B = A_f` has a maximal prime `𝔭'` with `B ⧸ 𝔭' ≅ K`. -/
theorem away_atPrime_dictionary {A K : Type} [CommRing A] [Field K] (𝔭 : Ideal A)
    (hmax : 𝔭.IsMaximal) (f : A) (hf : f ∉ 𝔭)
    (hiso : Nonempty (@Localization.AtPrime _ _ 𝔭 hmax.isPrime ≃+* K)) :
    ∃ (𝔭' : Ideal (Localization.Away f)) (h𝔭' : 𝔭'.IsPrime),
      𝔭'.IsMaximal ∧ IsField (@Localization.AtPrime _ _ 𝔭' h𝔭') ∧
        Nonempty ((Localization.Away f) ⧸ 𝔭' ≃+* K) := by
  have hmax' : 𝔭.IsMaximal := hmax
  have hp' : 𝔭.IsPrime := hmax.isPrime
  -- `A_𝔭` is a field, hence its maximal ideal vanishes and `A ⧸ 𝔭 ≃+* K`
  have hfield : IsField (Localization.AtPrime 𝔭) :=
    MulEquiv.isField (Field.toIsField K) hiso.some.toMulEquiv
  have hbot : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  have hkerPt : 𝔭.map (algebraMap A (Localization.AtPrime 𝔭)) = ⊥ := by
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal, hbot]
  let e1 : A ⧸ 𝔭 ≃+* Localization.AtPrime 𝔭 :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔭 (Localization.AtPrime 𝔭)).trans
      ((Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot _))
  let E : A ⧸ 𝔭 ≃+* K := e1.trans hiso.some
  let ψ : A →+* K := E.toRingHom.comp (Ideal.Quotient.mk 𝔭)
  have hψsurj : ∀ y : K, ∃ a : A, ψ a = y := by
    intro y
    obtain ⟨x, hx⟩ := E.surjective y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, hx⟩
  have hkerψ : RingHom.ker ψ = 𝔭 := by
    ext a
    change ψ a = 0 ↔ a ∈ 𝔭
    change E (Ideal.Quotient.mk 𝔭 a) = 0 ↔ a ∈ 𝔭
    rw [E.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hψf : ψ f ≠ 0 := fun h => hf (by rw [← hkerψ]; exact h)
  -- elements of `𝔭` are annihilated by elements outside `𝔭`
  have hannA : ∀ a : A, a ∈ 𝔭 → ∃ s : A, s ∉ 𝔭 ∧ s * a = 0 := by
    intro a ha
    have hmem : algebraMap A (Localization.AtPrime 𝔭) a ∈
        𝔭.map (algebraMap A (Localization.AtPrime 𝔭)) := Ideal.mem_map_of_mem _ ha
    rw [hkerPt, Ideal.mem_bot] at hmem
    have h0 : algebraMap A (Localization.AtPrime 𝔭) a =
        algebraMap A (Localization.AtPrime 𝔭) 0 := by simpa using hmem
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔭.primeCompl (Localization.AtPrime 𝔭)).mp h0
    exact ⟨(c : A), c.2, by simpa using hc⟩
  -- lift to `A_f`
  have hunitψf : IsUnit (ψ f) := isUnit_iff_ne_zero.mpr hψf
  let φ : Localization.Away f →+* K := IsLocalization.Away.lift (g := ψ) f hunitψf
  have hφcomp : φ.comp (algebraMap A (Localization.Away f)) = ψ :=
    IsLocalization.Away.lift_comp (g := ψ) f hunitψf
  have hφapp : ∀ a : A, φ (algebraMap A (Localization.Away f) a) = ψ a := by
    intro a
    have h := RingHom.congr_fun hφcomp a
    simpa only [RingHom.comp_apply] using h
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, ha⟩ := hψsurj y
    exact ⟨algebraMap A (Localization.Away f) a, by rw [hφapp]; exact ha⟩
  -- the kernel of `φ` is annihilated by its complement
  have hann : ∀ x ∈ RingHom.ker φ,
      ∃ c : Localization.Away f, c ∉ RingHom.ker φ ∧ c * x = 0 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
    have hψa : ψ a = 0 := by
      have h1 : φ (x * algebraMap A (Localization.Away f) (s : A)) =
          φ (algebraMap A (Localization.Away f) a) := congrArg φ hs
      rw [map_mul, hx, zero_mul, hφapp a] at h1
      exact h1.symm
    obtain ⟨s', hs'⟩ : ∃ s' : A, s' ∉ 𝔭 ∧ s' * a = 0 :=
      hannA a (by rw [← hkerψ]; exact hψa)
    refine ⟨algebraMap A (Localization.Away f) s', ?_, ?_⟩
    · rw [RingHom.mem_ker, hφapp s']
      intro h0
      exact hs'.1 (by rw [← hkerψ, RingHom.mem_ker]; exact h0)
    · have hsunit : IsUnit (algebraMap A (Localization.Away f) (s : A)) := by
        obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : A) f).mp s.2
        have h := (IsLocalization.map_units (Localization.Away f)
          (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f)).pow n
        rwa [← map_pow, hn] at h
      have h1 : algebraMap A (Localization.Away f) (s : A) *
          (algebraMap A (Localization.Away f) s' * x) = 0 := by
        rw [mul_comm (algebraMap A (Localization.Away f) (s : A)), mul_assoc, hs, ← map_mul,
          hs'.2, map_zero]
      exact (hsunit.mul_right_eq_zero).mp h1
  have hkerφ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  refine ⟨RingHom.ker φ, RingHom.ker_isPrime φ, ?_, ?_, ?_⟩
  · refine Ideal.Quotient.maximal_of_isField _ ?_
    exact MulEquiv.isField (Field.toIsField K)
      (RingHom.quotientKerEquivOfSurjective hφsurj).toMulEquiv
  · exact isField_localizationAtPrime_ker_of_ann φ hφsurj hann
  · exact ⟨RingHom.quotientKerEquivOfSurjective hφsurj⟩

end Commons.RingTheory.Localization