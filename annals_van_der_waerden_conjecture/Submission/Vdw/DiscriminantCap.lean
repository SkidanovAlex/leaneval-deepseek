import Mathlib
import Submission.Vdw.DedekindIndex
import Submission.Commons.FieldTheory.Polynomial.discr_ne_zero_of_separable
import Submission.Commons.Data.Int.Polynomial.discr_height_bound

open Function Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# Cap on the field discriminant of a box polynomial

For a monic irreducible `f ∈ ℤ[X]` of degree `n` with non-leading
coefficients bounded by `H`, the absolute discriminant of the number field
`K_f = ℚ[x]/(f)` is bounded by

    D_f = |Disc(K_f)| ≤ (2n−1)! · (n·(H+1))^(2n−1)      (`fieldDisc_height_bound`)

This gives the finite upper range `Y < D ≤ Z(H)` over which the Case-I
squarefull tail sum runs (any polynomial-in-`H` cap `Z` works, since the tail
estimate only depends on `log Z`; the cap is the crude determinant bound of
`Commons.Data.Int.Polynomial.discr_height_bound`).

Chain: Dedekind divisibility `fieldDisc_dvd_polyDisc` (|Disc K_f| ∣ Disc(f))
+ nonzeroness of `Disc(f)` for monic separable (i.e. irreducible over ℚ)
polynomials (`Commons.FieldTheory.Polynomial.discr_ne_zero_of_separable`)
give `|Disc K_f| ≤ |Disc(f)|` in the ℤ-absolute value, then the determinant
height bound applies.
-/

namespace Submission.Vdw

noncomputable section

/-- If `a ∣ b` in `ℤ` and `b ≠ 0`, then `|a| ≤ |b|`. -/
private lemma natAbs_le_of_dvd {a b : ℤ} (hab : a ∣ b) (hb : b ≠ 0) : a.natAbs ≤ b.natAbs := by
  obtain ⟨c, hc⟩ := hab
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hb
    rw [hc, hc0, mul_zero]
  have h1 : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hc0
  calc
    a.natAbs = a.natAbs * 1 := by simp
    _ ≤ a.natAbs * c.natAbs := Nat.mul_le_mul_left a.natAbs h1
    _ = (a * c).natAbs := (Int.natAbs_mul a c).symm
    _ = b.natAbs := by rw [hc]

/-- The polynomial discriminant of a monic irreducible integer polynomial is
nonzero (equivalently: irreducible over ℚ ⟹ separable ⟹ `Disc ≠ 0`). -/
private lemma polyDisc_ne_zero_of_irreducible (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hf : f.Monic) : polyDisc f ≠ 0 := by
  have hsepQ : (f.map φℚ).Separable :=
    Irreducible.separable (F := ℚ) (f := f.map φℚ) (Fact.out : Irreducible (f.map φℚ))
  have hdq : Polynomial.discr (f.map φℚ) ≠ 0 :=
    Commons.FieldTheory.Polynomial.discr_ne_zero_of_separable (F := ℚ) (f.map φℚ) (hf.map φℚ) hsepQ
  intro h0
  have hmap0 : Polynomial.discr (f.map φℚ) = 0 := by
    calc
      Polynomial.discr (f.map φℚ) = (polyDisc f : ℚ) := (polyDisc_cast f hf).symm
      _ = 0 := by simp [h0]
  exact hdq hmap0

/-- **Discriminant cap**: for monic irreducible `f` of degree `n` with
`|coeff k| ≤ H` (all `k < n`), the field discriminant satisfies
`D_f ≤ (2n−1)!·(n(H+1))^(2n−1)`. -/
theorem fieldDisc_height_bound (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hf : f.Monic) (n H : ℕ) (hdeg : f.natDegree = n)
    (hcoeff : ∀ k < n, |f.coeff k| ≤ (H : ℤ)) :
    fieldDisc f ≤ (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1) := by
  classical
  have hdiv : (fieldDisc f : ℤ) ∣ polyDisc f := fieldDisc_dvd_polyDisc f hf
  have hpd : polyDisc f ≠ 0 := polyDisc_ne_zero_of_irreducible f hf
  have hle : (fieldDisc f : ℤ).natAbs ≤ (polyDisc f).natAbs := natAbs_le_of_dvd hdiv hpd
  have hmain := Commons.Data.Int.Polynomial.discr_height_bound n H f hf hdeg hcoeff
  calc
    fieldDisc f = (fieldDisc f : ℤ).natAbs := (Int.natAbs_natCast (fieldDisc f)).symm
    _ ≤ (polyDisc f).natAbs := hle
    _ ≤ (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1) := by
          simpa [polyDisc] using hmain

end
end Submission.Vdw
