import Mathlib
import Submission.Commons.FieldTheory.Kummer.binomial_irreducible_iff_forall_prime

/-!
# A Kummer-theoretic consequence of a low-degree factor of `X ^ e - y`

If `K` contains a primitive `e`-th root of unity `ζ`, and an irreducible
polynomial `f` of degree `< e` divides `X ^ e - C y`, then `y` is a `p`-th
power in `K` for some prime `p ∣ e`.

The point is that `X ^ e - C y` is then *reducible*, and Capelli's criterion
in the form `Commons.FieldTheory.Kummer.binomial_irreducible_iff_forall_prime`
says that `X ^ e - C y` is irreducible exactly when `y` is a `p`-th power for
no prime `p ∣ e`.
-/

namespace Commons.FieldTheory.Kummer

theorem exists_prime_pow_of_irreducible_dvd_X_pow_sub_C {K : Type*} [Field K] {e : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ e) {y : K} (hy : y ≠ 0) {f : Polynomial K}
    (hf : Irreducible f) (hdvd : f ∣ Polynomial.X ^ e - Polynomial.C y) (hd : f.natDegree < e) :
    ∃ p : ℕ, p.Prime ∧ p ∣ e ∧ ∃ b : K, b ^ p = y := by
  have he : 0 < e := lt_of_le_of_lt (Nat.zero_le f.natDegree) hd
  have hμ : (primitiveRoots e K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots he).mpr hζ⟩
  have hnotirr : ¬ Irreducible (Polynomial.X ^ e - Polynomial.C y) := by
    intro hirr
    obtain ⟨g, hg⟩ := hdvd
    have hPne : Polynomial.X ^ e - Polynomial.C y ≠ 0 := by
      have hCy : (Polynomial.C y : Polynomial K) ≠ 0 := Polynomial.C_ne_zero.mpr hy
      intro h0
      have h1 := congrArg Polynomial.natDegree h0
      rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_zero] at h1
      omega
    rcases hirr.isUnit_or_isUnit hg with hfu | hgu
    · exact hf.not_isUnit hfu
    · have hdeg := congrArg Polynomial.natDegree hg
      rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_mul hf.ne_zero hgu.ne_zero,
        Polynomial.natDegree_eq_zero_of_isUnit hgu] at hdeg
      omega
  have h :=
    (Commons.FieldTheory.Kummer.binomial_irreducible_iff_forall_prime he hμ).not.mp hnotirr
  push Not at h
  exact h

end Commons.FieldTheory.Kummer
