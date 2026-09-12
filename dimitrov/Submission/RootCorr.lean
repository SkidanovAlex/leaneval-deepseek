import Mathlib.NumberTheory.NumberField.House
import Submission.Powers

/-!
# Root correspondence for power polynomials over ℂ

If `P ∈ ℂ[X]` is monic and splits with root multiset the elements of a
finite set `S`, then `pow2 P = ∏ z∈S (X - C (z^2))`.
-/

noncomputable section

open scoped Complex Polynomial
open Polynomial

namespace Submission.RootCorr

open Submission.Powers

/-- `pow2 P` has the same degree as `P` when `P` is monic. -/
lemma pow2_natDegree {R : Type*} [CommRing R] (P : R[X]) (hP : P.Monic) :
    (pow2 P).natDegree = P.natDegree := by
  classical
  by_cases hsub : Subsingleton R
  · haveI : Subsingleton R := hsub
    have hEq : pow2 P = P := Subsingleton.elim _ _
    rw [hEq]
  · haveI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hsub
    let d : ℕ := P.natDegree
    let Q : R[X] := P * P.comp (-X)
    let a : R := (-1 : R) ^ d
    have hd : P.coeff d = 1 := by
      simpa [d] using hP.leadingCoeff
    have hcomp : (P.comp (-X)).natDegree ≤ d := by
      have h1 := natDegree_comp_le (p := P) (q := (-X : R[X]))
      simpa [d, natDegree_neg] using h1
    have hQdeg : Q.natDegree ≤ 2 * d := by
      have hmul : Q.natDegree ≤ P.natDegree + (P.comp (-X)).natDegree := by
        simpa [Q] using natDegree_mul_le (p := P) (q := P.comp (-X))
      calc
        Q.natDegree ≤ P.natDegree + (P.comp (-X)).natDegree := hmul
        _ ≤ P.natDegree + d := Nat.add_le_add_left hcomp P.natDegree
        _ = 2 * d := by simp [d, two_mul]
    -- upper bound for natDegree (pow2 P)
    have hUpper : (pow2 P).natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hNlt : 2 * d < 2 * N := by omega
      have hnd : natDegree (a • Q) < 2 * N := by
        apply lt_of_le_of_lt _ hNlt
        exact (natDegree_smul_le a Q).trans hQdeg
      calc
        (pow2 P).coeff N = (a • Q).coeff (2 * N) := by
          dsimp [pow2, a, Q]
          rw [evenPart_coeff]
        _ = 0 := coeff_eq_zero_of_natDegree_lt hnd
    -- coefficient at d equals 1
    have hcd : (pow2 P).coeff d = 1 := by
      dsimp [pow2, a, Q]
      rw [evenPart_coeff]
      rw [coeff_smul]
      have hQ2 : Q.coeff (2 * d) = (-1 : R) ^ d := by
        dsimp [Q]
        rw [coeff_mul]
        rw [Finset.sum_eq_single (d, d)]
        · simp [hd, Submission.PowersOdd.coeff_comp_neg_X]
        · intro b hb hbne
          rcases b with ⟨i, j⟩
          have hij : i + j = 2 * d := by simpa using (Finset.mem_antidiagonal.mp hb)
          have hterm : P.coeff i * (P.comp (-X)).coeff j = 0 := by
            by_cases hid : i < d
            · have hjd : d < j := by omega
              have hgj : (P.comp (-X)).coeff j = 0 :=
                coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hcomp hjd)
              simp [hgj]
            · by_cases hjd : j < d
              · have hid' : d < i := by omega
                have hPi : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by simpa [d] using hid')
                simp [hPi]
              · have : i = d ∧ j = d := by omega
                rcases this with ⟨hi, hj⟩
                exfalso
                apply hbne
                simp [hi, hj]
          simpa using hterm
        · intro hnot
          exact False.elim (hnot (by simpa [Finset.mem_antidiagonal] using (show d + d = 2 * d by omega)))
      rw [hQ2]
      -- a * (-1)^d = 1, with a := (-1)^d
      dsimp [a]
      rw [← pow_add]
      have : d + d = 2 * d := by omega
      rw [this, pow_mul]
      simp
    have hone : (1 : R) ≠ 0 := by
      intro h
      have hz : (0 : R) = 1 := h.symm
      haveI : Subsingleton R := subsingleton_of_zero_eq_one hz
      exact hsub (inferInstance : Subsingleton R)
    have hne0 : (pow2 P).coeff d ≠ 0 := by simpa [hcd] using hone
    exact natDegree_eq_of_le_of_coeff_ne_zero hUpper hne0

/-- For a monic polynomial with root set `S` (each element of `S` a root of
multiplicity one and `P = ∏ z∈S (X - z)`), the polynomial `pow2 P` equals
`∏ z∈S (X - z²)`. -/
lemma pow2_eq_prod_sub_sq (S : Finset ℂ) (P : ℂ[X])
    (hP : P = S.prod fun z : ℂ => X - C z) (hmonic : P.Monic) :
    pow2 P = S.prod fun z : ℂ => X - C (z ^ 2) := by
  classical
  have _ : P ≠ 0 := hmonic.ne_zero
  let A : ℂ[X] := S.prod fun z : ℂ => X + C z
  have hdeg : P.natDegree = S.card := by
    rw [hP]
    rw [natDegree_prod_of_monic]
    · simp
    · intro z hz
      exact monic_X_sub_C z
  have hfac : ∀ z : ℂ, (X - C z).comp (-X) = (-1 : ℂ[X]) * (X + C z) := by
    intro z
    have h1 : (X - C z).comp (-X) = -X - C z := by simp
    rw [h1]
    ring
  have hcompA : P.comp (-X) = (-1 : ℂ[X]) ^ S.card * A := by
    rw [hP]
    calc
      (S.prod fun z : ℂ => X - C z).comp (-X)
          = S.prod fun z : ℂ => (X - C z).comp (-X) := by
              rw [prod_comp]
      _ = S.prod fun z : ℂ => (-1 : ℂ[X]) * (X + C z) := by
              apply Finset.prod_congr rfl
              intro z hz
              exact hfac z
      _ = (S.prod fun _ : ℂ => (-1 : ℂ[X])) * S.prod (fun z : ℂ => X + C z) := by
              rw [Finset.prod_mul_distrib]
      _ = (-1 : ℂ[X]) ^ S.card * A := by
              simp [A]
  have hsq : (-1 : ℂ[X]) ^ S.card * (-1 : ℂ[X]) ^ S.card = 1 := by
    rw [← pow_add]
    have : S.card + S.card = 2 * S.card := by omega
    rw [this, pow_mul]
    simp
  have hCpow : C ((-1 : ℂ) ^ S.card) = (-1 : ℂ[X]) ^ S.card := by
    rw [C_pow]
    congr 1
    simp
  have hsmulconv : (-1 : ℂ) ^ S.card • (P * P.comp (-X)) =
        (-1 : ℂ[X]) ^ S.card * (P * P.comp (-X)) := by
    rw [smul_eq_C_mul]
    rw [hCpow]
  have hL : expand ℂ 2 (pow2 P) = P * A := by
    rw [pow2_expand]
    rw [hdeg]
    rw [hsmulconv]
    rw [hcompA]
    have hre : (-1 : ℂ[X]) ^ S.card * (P * ((-1 : ℂ[X]) ^ S.card * A)) = P * A := by
      calc
        (-1 : ℂ[X]) ^ S.card * (P * ((-1 : ℂ[X]) ^ S.card * A))
            = P * ((-1 : ℂ[X]) ^ S.card * ((-1 : ℂ[X]) ^ S.card * A)) := by ring
        _ = P * (((-1 : ℂ[X]) ^ S.card * (-1 : ℂ[X]) ^ S.card) * A) := by ring
        _ = P * A := by
              rw [hsq]
              simp
    exact hre
  have hG : expand ℂ 2 (S.prod fun z : ℂ => X - C (z ^ 2)) = P * A := by
    calc
      expand ℂ 2 (S.prod fun z : ℂ => X - C (z ^ 2))
          = S.prod fun z : ℂ => expand ℂ 2 (X - C (z ^ 2)) := by
              simp [expand_eq_comp_X_pow]
      _ = S.prod fun z : ℂ => X ^ 2 - C (z ^ 2) := by
              apply Finset.prod_congr rfl
              intro z hz
              simp [expand_eq_comp_X_pow]
      _ = S.prod fun z : ℂ => (X - C z) * (X + C z) := by
              apply Finset.prod_congr rfl
              intro z hz
              have hC : C (z ^ 2) = (C z) ^ 2 := by rw [map_pow]
              rw [hC]
              ring
      _ = (S.prod fun z : ℂ => X - C z) * S.prod (fun z : ℂ => X + C z) := by
              rw [Finset.prod_mul_distrib]
      _ = P * A := by
              rw [← hP]
  have hE : expand ℂ 2 (pow2 P) = expand ℂ 2 (S.prod fun z : ℂ => X - C (z ^ 2)) := by
    rw [hL, hG]
  exact (expand_inj (R := ℂ) (p := 2) (by norm_num : 0 < 2)).1 hE

/-- If `z` is a root of `P`, then `z²` is a root of `pow2 P`. -/
lemma pow2_root_of_root {R : Type*} [CommRing R] (P : R[X]) (z : R)
    (hz : P.IsRoot z) : (pow2 P).IsRoot (z ^ 2) := by
  classical
  rw [IsRoot.def]
  rw [pow2_eval_sq]
  rw [hz]
  simp

end Submission.RootCorr

end
