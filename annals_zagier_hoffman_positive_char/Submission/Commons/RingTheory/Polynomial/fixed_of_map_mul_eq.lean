import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.RingTheory.Polynomial

open _root_.Polynomial

variable {E : Type*} [Field E]

/-- If every coefficient of `P : E[X]` lies in a subfield `F`, then `P` is the image under
`F.subtype` of a polynomial over `F`. -/
lemma exists_map_subtype_eq_of_coeff_mem (F : Subfield E) (P : Polynomial E)
    (h : ∀ n, P.coeff n ∈ F) : ∃ P' : Polynomial F, P'.map F.subtype = P := by
  have hmem : ∀ n, P.coeff n ∈ F.subtype.range := fun n => by
    rw [RingHom.mem_range]; exact ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨P', hP'⟩ := (RingHom.mem_range (f := mapRingHom F.subtype) (y := P)).mp
    ((Polynomial.mem_map_range F.subtype).mpr hmem)
  exact ⟨P', by simpa using hP'⟩

/-- Scaling both `P` and `Q` by the same constant preserves the fixedness relation. -/
lemma map_mul_eq_of_scale {σ : E →+* E} {P Q : Polynomial E} (c : E)
    (h : P.map σ * Q = P * Q.map σ) :
    (C c * P).map σ * (C c * Q) = (C c * P) * (C c * Q).map σ := by
  simp only [Polynomial.map_mul, Polynomial.map_C]
  rw [show C (σ c) * P.map σ * (C c * Q) = C (σ c) * C c * (P.map σ * Q) by ring,
      show C c * P * (C (σ c) * Q.map σ) = C c * C (σ c) * (P * Q.map σ) by ring,
      h, show C (σ c) * C c = C c * C (σ c) by ring]

/-- Descent in the coprime, monic-denominator case: a fixed fraction `P/Q` with `Q` monic and
`P, Q` coprime already has `σ`-invariant numerator and denominator. -/
lemma map_eq_self_of_coprime_monic {σ : E →+* E} (hσ : Function.Injective σ)
    {P Q : Polynomial E} (hP : P ≠ 0) (hQ : Q ≠ 0) (hQmon : Q.Monic)
    (hcop : IsCoprime P Q) (h : P.map σ * Q = P * Q.map σ) :
    P.map σ = P ∧ Q.map σ = Q := by
  have hPdvd : P ∣ P.map σ :=
    hcop.dvd_of_dvd_mul_right (by rw [h]; exact dvd_mul_right P (Q.map σ))
  have hQdvd : Q ∣ Q.map σ := by
    have h1 : Q ∣ P * Q.map σ := by rw [← h]; exact dvd_mul_left Q (P.map σ)
    have h1' : Q ∣ Q.map σ * P := by simpa [mul_comm] using h1
    exact hcop.symm.dvd_of_dvd_mul_right h1'
  obtain ⟨A, hA⟩ := hPdvd
  obtain ⟨B, hB⟩ := hQdvd
  have hAB : A = B := by
    have key : P * (A * Q) = P * (Q * B) := by
      calc P * (A * Q) = (P * A) * Q := by rw [mul_assoc]
        _ = P.map σ * Q := by rw [← hA]
        _ = P * Q.map σ := h
        _ = P * (Q * B) := by rw [hB]
    have h2 : A * Q = Q * B := mul_left_cancel₀ hP key
    rw [mul_comm Q B] at h2
    exact mul_right_cancel₀ hQ h2
  subst hAB
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hA
    exact hP ((Polynomial.map_eq_zero_iff hσ).mp hA)
  have hdeg : A.natDegree = 0 := by
    have h1 : (P.map σ).natDegree = P.natDegree := Polynomial.natDegree_map_eq_of_injective hσ P
    rw [hA, Polynomial.natDegree_mul hP hA0] at h1
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hA hB
  have hr : A.coeff 0 = 1 := by
    have := congrArg Polynomial.leadingCoeff hB
    rw [Polynomial.leadingCoeff_map_of_injective hσ, hQmon.leadingCoeff, map_one,
        Polynomial.leadingCoeff_mul, hQmon.leadingCoeff, Polynomial.leadingCoeff_C,
        one_mul] at this
    exact this.symm
  rw [hr, Polynomial.C_1, mul_one] at hA hB
  exact ⟨hA, hB⟩

/-- **Descent of rational functions along an injective field endomorphism.**
Let `σ : E →+* E` be an injective ring homomorphism of a field `E` and let `F` be its fixed
subfield (`x ∈ F ↔ σ x = x`).  If `P Q : E[X]` with `Q ≠ 0` satisfy `σ(P)·Q = P·σ(Q)`
(coefficientwise `σ`, i.e. the rational function `P/Q` is fixed by the coefficientwise twist),
then `P/Q` can be written as a quotient of polynomials with coefficients in `F`. -/
theorem fixed_of_map_mul_eq {E : Type*} [Field E] (σ : E →+* E) (hσ : Function.Injective σ)
    (F : Subfield E) (hF : ∀ x : E, x ∈ F ↔ σ x = x) (P Q : Polynomial E) (hQ : Q ≠ 0)
    (h : P.map σ * Q = P * Q.map σ) :
    ∃ P' Q' : Polynomial F, Q' ≠ 0 ∧ P'.map F.subtype * Q = P * Q'.map F.subtype := by
  classical
  by_cases hP : P = 0
  · exact ⟨0, 1, one_ne_zero, by simp [hP]⟩
  · let : GCDMonoid (Polynomial E) := EuclideanDomain.gcdMonoid (Polynomial E)
    set d : Polynomial E := gcd P Q with hd
    have hd0 : d ≠ 0 := gcd_ne_zero_of_right hQ
    have hdvdP : d ∣ P := gcd_dvd_left P Q
    have hdvdQ : d ∣ Q := gcd_dvd_right P Q
    set P₁ : Polynomial E := P / d with hP₁
    set Q₁ : Polynomial E := Q / d with hQ₁
    have hPd : d * P₁ = P := EuclideanDomain.mul_div_cancel' hd0 hdvdP
    have hQd : d * Q₁ = Q := EuclideanDomain.mul_div_cancel' hd0 hdvdQ
    have hcop : IsCoprime P₁ Q₁ := isCoprime_div_gcd_div_gcd hQ
    have hP₁0 : P₁ ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hPd; exact hP hPd.symm
    have hQ₁0 : Q₁ ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hQd; exact hQ hQd.symm
    have hrel : P₁.map σ * Q₁ = P₁ * Q₁.map σ := by
      have htmp : (d * P₁).map σ * (d * Q₁) = (d * P₁) * (d * Q₁).map σ := by
        rw [hPd, hQd]; exact h
      rw [Polynomial.map_mul, Polynomial.map_mul] at htmp
      have hdmap : d.map σ ≠ 0 := (Polynomial.map_ne_zero_iff hσ).mpr hd0
      have key : d.map σ * d * (P₁.map σ * Q₁) = d.map σ * d * (P₁ * Q₁.map σ) := by
        ring_nf at htmp ⊢
        exact htmp
      exact mul_left_cancel₀ (mul_ne_zero hdmap hd0) key
    set b : E := Q₁.leadingCoeff with hb
    have hb0 : b ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ₁0
    set P₀ : Polynomial E := C b⁻¹ * P₁ with hP₀
    set Q₀ : Polynomial E := C b⁻¹ * Q₁ with hQ₀
    have hP₀0 : P₀ ≠ 0 := by
      rw [hP₀]; exact mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero hb0)) hP₁0
    have hQ₀0 : Q₀ ≠ 0 := by
      rw [hQ₀]; exact mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero hb0)) hQ₁0
    have hQ₀mon : Q₀.Monic := by
      rw [hQ₀, mul_comm]
      exact Polynomial.monic_mul_leadingCoeff_inv hQ₁0
    have hcop₀ : IsCoprime P₀ Q₀ := by
      rw [hP₀, hQ₀]
      exact (isCoprime_mul_unit_left
        (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hb0))) P₁ Q₁).mpr hcop
    have hrel₀ : P₀.map σ * Q₀ = P₀ * Q₀.map σ := by
      rw [hP₀, hQ₀]
      exact map_mul_eq_of_scale b⁻¹ hrel
    obtain ⟨hP₀fix, hQ₀fix⟩ := map_eq_self_of_coprime_monic hσ hP₀0 hQ₀0 hQ₀mon hcop₀ hrel₀
    have hP'mem : ∀ n, P₀.coeff n ∈ F := fun n => (hF _).mpr (by
      have hh := congrArg (fun p : Polynomial E => p.coeff n) hP₀fix
      rwa [Polynomial.coeff_map] at hh)
    obtain ⟨P', hP'⟩ := exists_map_subtype_eq_of_coeff_mem F P₀ hP'mem
    have hQ'mem : ∀ n, Q₀.coeff n ∈ F := fun n => (hF _).mpr (by
      have hh := congrArg (fun p : Polynomial E => p.coeff n) hQ₀fix
      rwa [Polynomial.coeff_map] at hh)
    obtain ⟨Q', hQ'⟩ := exists_map_subtype_eq_of_coeff_mem F Q₀ hQ'mem
    have hQ'0 : Q' ≠ 0 := by
      intro h0; apply hQ₀0; rw [← hQ', h0, Polynomial.map_zero]
    refine ⟨P', Q', hQ'0, ?_⟩
    rw [hP', hQ', hP₀, hQ₀, ← hPd, ← hQd]
    ring

end Commons.RingTheory.Polynomial