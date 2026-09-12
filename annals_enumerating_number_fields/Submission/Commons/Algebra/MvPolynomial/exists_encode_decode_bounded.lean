import Mathlib
import Submission.Commons.Algebra.MvPolynomial.card_monomials_le
import Submission.Commons.Algebra.MvPolynomial.finite_monomials_bounded_degree

namespace Commons.Algebra.MvPolynomial

/-- The set of polynomials in `r` variables over `ℤ` of total degree at most `d` whose
coefficients are bounded by `K₀` in absolute value can be encoded into a finite code
`Code` with `Nat.card Code ≤ (2*K₀+2)^((d+r).choose r)`, in a way admitting a decoding
map left inverse to the encoding. -/
theorem exists_encode_decode_bounded (r d K₀ : ℕ) :
    ∃ (Code : Type) (_ : Fintype Code)
      (encode : {E : MvPolynomial (Fin r) ℤ // E.totalDegree ≤ d ∧ ∀ μ, |E.coeff μ| ≤ (K₀ : ℤ)} → Code)
      (decode : Code → MvPolynomial (Fin r) ℤ),
      (∀ E, decode (encode E) = E.1) ∧
      Nat.card Code ≤ (2 * K₀ + 2) ^ ((d + r).choose r) := by
  classical
  let X := {E : MvPolynomial (Fin r) ℤ // E.totalDegree ≤ d ∧ ∀ μ, |E.coeff μ| ≤ (K₀ : ℤ)}
  let S := {s : Fin r →₀ ℕ // s.sum (fun _ k => k) ≤ d}
  haveI hfin : Finite S := finite_monomials_bounded_degree r d
  haveI : Fintype S := Fintype.ofFinite S
  let Code := S → Fin (2 * K₀ + 2)
  haveI : Fintype Code := inferInstance
  let encode : X → Code := fun E s =>
    ⟨Int.toNat (E.1.coeff s.1 + (K₀ : ℤ)), by
      have h := abs_le.mp (E.2.2 s.1)
      have h1 : (0 : ℤ) ≤ E.1.coeff s.1 + (K₀ : ℤ) := by linarith [h.1]
      have h2 : E.1.coeff s.1 + (K₀ : ℤ) < ((2 * K₀ + 2 : ℕ) : ℤ) := by
        have hcast : ((2 * K₀ + 2 : ℕ) : ℤ) = 2 * (K₀ : ℤ) + 2 := by push_cast; ring
        rw [hcast]; linarith [h.2]
      exact (Int.toNat_lt h1).mpr h2⟩
  let decode : Code → MvPolynomial (Fin r) ℤ := fun F =>
    if h : ∃ E : X, encode E = F then (Classical.choose h).1 else 0
  have hinj : Function.Injective encode := by
    rintro ⟨P, hP1, hP2⟩ ⟨Q, hQ1, hQ2⟩ hPQ
    have hcoeff : ∀ μ : Fin r →₀ ℕ, μ.sum (fun _ k => k) ≤ d → P.coeff μ = Q.coeff μ := by
      intro μ hμ
      have hval : (encode ⟨P, hP1, hP2⟩ ⟨μ, hμ⟩).val
          = (encode ⟨Q, hQ1, hQ2⟩ ⟨μ, hμ⟩).val :=
        congrArg Fin.val (congrFun hPQ ⟨μ, hμ⟩)
      simp only [encode] at hval
      have hPn : (0 : ℤ) ≤ P.coeff μ + (K₀ : ℤ) := by
        have := (abs_le.mp (hP2 μ)).1; linarith
      have hQn : (0 : ℤ) ≤ Q.coeff μ + (K₀ : ℤ) := by
        have := (abs_le.mp (hQ2 μ)).1; linarith
      have hcast : ((P.coeff μ + (K₀ : ℤ)).toNat : ℤ) = ((Q.coeff μ + (K₀ : ℤ)).toNat : ℤ) := by
        exact_mod_cast hval
      rw [Int.toNat_of_nonneg hPn, Int.toNat_of_nonneg hQn] at hcast
      linarith
    apply Subtype.ext
    ext μ
    by_cases hμ : μ.sum (fun _ k => k) ≤ d
    · exact hcoeff μ hμ
    · have hdμ : d < μ.sum (fun _ k => k) := not_le.mp hμ
      have hPz : P.coeff μ = 0 := by
        rw [← MvPolynomial.notMem_support_iff]
        intro hmem
        have := MvPolynomial.le_totalDegree (p := P) hmem
        omega
      have hQz : Q.coeff μ = 0 := by
        rw [← MvPolynomial.notMem_support_iff]
        intro hmem
        have := MvPolynomial.le_totalDegree (p := Q) hmem
        omega
      rw [hPz, hQz]
  refine ⟨Code, inferInstance, encode, decode, ?_, ?_⟩
  · intro E
    have hex : ∃ E' : X, encode E' = encode E := ⟨E, rfl⟩
    have hdecode : decode (encode E) = (Classical.choose hex).1 := by
      simp only [decode]
      exact dif_pos hex
    rw [hdecode]
    exact congrArg Subtype.val (hinj (Classical.choose_spec hex))
  · have hS : Nat.card S ≤ (d + r).choose r := card_monomials_le r d
    have hcard : Nat.card Code = (2 * K₀ + 2) ^ Nat.card S := by
      show Nat.card (S → Fin (2 * K₀ + 2)) = _
      rw [Nat.card_fun, Nat.card_fin]
    calc Nat.card Code = (2 * K₀ + 2) ^ Nat.card S := hcard
      _ ≤ (2 * K₀ + 2) ^ ((d + r).choose r) := Nat.pow_le_pow_right (by omega) hS

end Commons.Algebra.MvPolynomial
