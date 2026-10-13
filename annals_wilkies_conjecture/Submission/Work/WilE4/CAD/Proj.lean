/-
  WilE4 / CAD — the projection data of the cylindrical algebraic decomposition.

  For a family `H` of polynomials in `n + 1` variables, whose *last* variable is the one that is
  projected out, `projData H` is a family of polynomials in the remaining `n` variables that
  determines the "type" of the specialisation of `H` over a base point:

  * `coeffFam H` — all coefficients of every member of `H` with respect to the last variable.
    Their sign pattern decides the *degree* of every specialisation (a coefficient either vanishes
    identically over a cell or has a constant non-zero sign there);
  * `resFam H` — the resultants `resultant (F P) (F Q) a b` of pairs of members, for all degree
    pairs `a ≤ degreeOf P`, `b ≤ degreeOf Q`.  Their sign pattern decides coprimality (and
    squarefreeness, using the derivative tower) of the specialisations.

  `projDataT H` adds the derivative tower: at each level of the recursion the family whose sign
  conditions define the cells must be closed under `pderiv` in the last variable, because that is
  what `Ana.jet_separation` needs to conclude that the cells are connected.
-/
import Submission.Work.WilE4.Poly
import Submission.Work.WilE4.Tower
import Submission.Work.WilE4.CAD.ProjDeg
import Submission.Work.WilE4.CAD.tower_deriv_closed

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

/-! ## Splitting off the last variable -/

/-- `F P` is `P` viewed as a polynomial in its last variable, with coefficients in
`ℝ[X₀,…,X_{n-1}]`.  It is the counterpart of `spec` before evaluation: `spec P x = (F P).map x`. -/
def F {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) : Polynomial (MvPolynomial (Fin n) ℝ) :=
  MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.rename (rot n) P)

theorem spec_eq_map {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) :
    spec P x = (F P).map (MvPolynomial.eval x) := rfl

/-- The `j`-th coefficient of the specialisation is the evaluation of the `j`-th coefficient. -/
theorem coeff_spec {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) (j : ℕ) :
    (spec P x).coeff j = MvPolynomial.eval x ((F P).coeff j) := by
  rw [spec_eq_map, Polynomial.coeff_map]


/-- The coefficients of `F P` do not raise the total degree. -/
theorem totalDegree_coeff_le {d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℝ) (j : ℕ) :
    ((F P).coeff j).totalDegree ≤ P.totalDegree :=
  (totalDegree_coeff_finSucc_le (MvPolynomial.rename (rot d) P) j).trans
    (le_of_eq (rename_totalDegree (rot d) P))

/-! ## The principal subresultant coefficients -/

/-- The rows of the principal-subresultant matrix: the powers `X^{2i}, …, X^{m+n-1}`. -/
def pscRow (m n i : ℕ) : Fin (m + n - 2 * i) → Fin (m + n) :=
  fun k => ⟨2 * i + (k : ℕ), by
    have hk : (k : ℕ) < m + n - 2 * i := k.isLt
    omega⟩

/-- The columns of the principal-subresultant matrix: the multiples `X^k f` (`i ≤ k ≤ n-1`) and
`X^k g` (`i ≤ k ≤ m-1`). -/
def pscCol (m n i : ℕ) : Fin (m + n - 2 * i) → Fin (m + n) :=
  fun k => if hc : (k : ℕ) < n - i then
      ⟨m + i + (k : ℕ), by
        have hk : (k : ℕ) < m + n - 2 * i := k.isLt
        have h1 : i + (k : ℕ) < n := by omega
        omega⟩
    else
      ⟨i + ((k : ℕ) - (n - i)), by
        have hk : (k : ℕ) < m + n - 2 * i := k.isLt
        have hkn : n - i ≤ (k : ℕ) := Nat.le_of_not_lt hc
        have h1 : (k : ℕ) - (n - i) < m - i + 1 := by omega
        omega⟩

/-- The **principal subresultant matrix** of `f` and `g` at the formal degrees `m`, `n` and index
`i` (BPR ch. 4): the submatrix of the Sylvester matrix whose rows are the powers
`X^{2i}, …, X^{m+n-1}` and whose columns are the multiples `X^k f` (`i ≤ k ≤ n-1`) and `X^k g`
(`i ≤ k ≤ m-1`).  Its determinant is the principal subresultant coefficient `s_i(f,g)`.

The maximal minors (the resultants, `resFam`) cannot detect the *degree* of the gcd: two members
sharing a factor have a resultant that vanishes identically, and the crossing of the cofactor roots
is then invisible (`NOTES.md` §2bis).  The subresultant coefficients do detect it: `s_i = 0` for
`i < deg (gcd f g)` and `s_{deg (gcd f g)} ≠ 0` (`psc_eq_zero_of_lt_gcd`,
`psc_gcd_natDegree_ne_zero`), so the vanishing pattern of the `s_i` determines `deg (gcd f g)`.
There are only `min m n + 1` of them per pair, i.e. polynomially many. -/
def pscMat {R : Type*} [CommRing R] (f g : R[X]) (m n i : ℕ) :
    Matrix (Fin (m + n - 2 * i)) (Fin (m + n - 2 * i)) R :=
  (Polynomial.sylvester f g m n).submatrix (pscRow m n i) (pscCol m n i)

/-- The principal subresultant coefficient of `f` and `g` at the formal degrees `m`, `n` and the
index `i`. -/
def psc {R : Type*} [CommRing R] (f g : R[X]) (m n i : ℕ) : R :=
  (pscMat f g m n i).det

/-- Every entry of the principal subresultant matrix is a coefficient of `f` or of `g`. -/
theorem totalDegree_pscMat_entry_le {d : ℕ} (f g : Polynomial (MvPolynomial (Fin d) ℝ))
    (D m n i : ℕ) (hf : ∀ j, (f.coeff j).totalDegree ≤ D) (hg : ∀ j, (g.coeff j).totalDegree ≤ D)
    (a b : Fin (m + n - 2 * i)) : ((pscMat f g m n i) a b).totalDegree ≤ D :=
  totalDegree_sylvester_entry_le f g D m n hf hg _ _

/-- Specialisation commutes with the principal subresultant coefficient. -/
theorem eval_pscMat_det {n : ℕ} (P Q : MvPolynomial (Fin (n + 1)) ℝ) (a b i : ℕ)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x ((pscMat (F P) (F Q) a b i).det)
      = (pscMat (spec P x) (spec Q x) a b i).det := by
  simp only [pscMat, spec_eq_map]
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp [RingHom.mapMatrix_apply, Matrix.submatrix_apply,
    Polynomial.sylvester_map_map (F P) (F Q) a b (MvPolynomial.eval x)]

/-- The principal subresultant coefficients of the pairs of members of `H`, for all degree pairs up
to the degrees in the last variable. -/
def pscFam {n : ℕ} (H : List (MvPolynomial (Fin (n + 1)) ℝ)) : List (MvPolynomial (Fin n) ℝ) :=
  (H ×ˢ H).flatMap fun q =>
    (List.range (q.1.degreeOf (Fin.last n) + 1)).flatMap fun a =>
      (List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
        (List.range (min a b + 1)).map fun i => (pscMat (F q.1) (F q.2) a b i).det

/-- Every principal subresultant coefficient of a pair of members belongs to `pscFam H`. -/
theorem pscFam_mem {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)}
    {P Q : MvPolynomial (Fin (n + 1)) ℝ} (hP : P ∈ H) (hQ : Q ∈ H) {a b : ℕ}
    (ha : a ≤ P.degreeOf (Fin.last n)) (hb : b ≤ Q.degreeOf (Fin.last n)) {i : ℕ}
    (hi : i ≤ min a b) : (pscMat (F P) (F Q) a b i).det ∈ pscFam H := by
  rw [pscFam, List.mem_flatMap]
  refine ⟨(P, Q), List.mem_product.mpr ⟨hP, hQ⟩, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a, List.mem_range.mpr (Nat.lt_succ_of_le ha), ?_⟩
  rw [List.mem_flatMap]
  refine ⟨b, List.mem_range.mpr (Nat.lt_succ_of_le hb), ?_⟩
  rw [List.mem_map]
  exact ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩

theorem pscFam_deg {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : ∀ Q ∈ pscFam H, Q.totalDegree ≤ 2 * D * D := by
  intro Q hQ
  simp only [pscFam, List.mem_flatMap, List.mem_map, List.mem_range] at hQ
  obtain ⟨q, hq, a, ha, b, hb, i, hi, rfl⟩ := hQ
  obtain ⟨hq1, hq2⟩ := List.mem_product.mp hq
  have haD : a ≤ D := (Nat.lt_succ_iff.mp ha).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.1 hq1))
  have hbD : b ≤ D := (Nat.lt_succ_iff.mp hb).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.2 hq2))
  have hminD : min a b ≤ D := by
    rcases le_total a b with h | h
    · rw [min_eq_left h]; exact haD
    · rw [min_eq_right h]; exact hbD
  refine (totalDegree_det_le _ fun i' j' =>
    totalDegree_pscMat_entry_le (F q.1) (F q.2) D a b i
      (fun j => (totalDegree_coeff_le q.1 j).trans (hH q.1 hq1))
      (fun j => (totalDegree_coeff_le q.2 j).trans (hH q.2 hq2)) i' j').trans ?_
  have hab : a + b - 2 * i ≤ 2 * D := by omega
  calc (a + b - 2 * i) * D ≤ (2 * D) * D := Nat.mul_le_mul_right D hab
    _ = 2 * D * D := by ring

theorem pscFam_length {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) :
    (pscFam H).length ≤ (H.length * H.length) * ((D + 1) * (D + 1) * (D + 1)) := by
  rw [pscFam, List.length_flatMap]
  have h1 : ∀ q ∈ H ×ˢ H,
      ((List.range (q.1.degreeOf (Fin.last n) + 1)).flatMap fun a =>
        (List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
          (List.range (min a b + 1)).map fun i =>
            (pscMat (F q.1) (F q.2) a b i).det).length ≤ (D + 1) * ((D + 1) * (D + 1)) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := List.mem_product.mp hq
    have hq1D : q.1.degreeOf (Fin.last n) ≤ D :=
      (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.1 hq1)
    have hq2D : q.2.degreeOf (Fin.last n) ≤ D :=
      (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.2 hq2)
    have h2 : ∀ a ∈ List.range (q.1.degreeOf (Fin.last n) + 1),
        ((List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
          (List.range (min a b + 1)).map fun i =>
            (pscMat (F q.1) (F q.2) a b i).det).length ≤ (D + 1) * (D + 1) := by
      intro a ha
      have haD : a ≤ D := (Nat.lt_succ_iff.mp (List.mem_range.mp ha)).trans hq1D
      rw [List.length_flatMap]
      have h3 : ∀ b ∈ List.range (q.2.degreeOf (Fin.last n) + 1),
          ((List.range (min a b + 1)).map fun i =>
            (pscMat (F q.1) (F q.2) a b i).det).length ≤ D + 1 := by
        intro b hb
        rw [List.length_map, List.length_range]
        have hbD : b ≤ D := (Nat.lt_succ_iff.mp (List.mem_range.mp hb)).trans hq2D
        have : min a b ≤ D := by
          rcases le_total a b with h | h
          · rw [min_eq_left h]; exact haD
          · rw [min_eq_right h]; exact hbD
        omega
      calc ((List.range (q.2.degreeOf (Fin.last n) + 1)).map fun b =>
              ((List.range (min a b + 1)).map fun i =>
                (pscMat (F q.1) (F q.2) a b i).det).length).sum
          ≤ ((List.range (q.2.degreeOf (Fin.last n) + 1)).map fun _ => (D + 1)).sum :=
            List.sum_le_sum h3
        _ = (q.2.degreeOf (Fin.last n) + 1) * (D + 1) := by
            simp [List.map_const', List.sum_replicate, nsmul_eq_mul]
        _ ≤ (D + 1) * (D + 1) := Nat.mul_le_mul_right (D + 1) (by omega)
    rw [List.length_flatMap]
    calc ((List.range (q.1.degreeOf (Fin.last n) + 1)).map fun a =>
            ((List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
              (List.range (min a b + 1)).map fun i =>
                (pscMat (F q.1) (F q.2) a b i).det).length).sum
        ≤ ((List.range (q.1.degreeOf (Fin.last n) + 1)).map fun _ =>
            (D + 1) * (D + 1)).sum := List.sum_le_sum h2
      _ = (q.1.degreeOf (Fin.last n) + 1) * ((D + 1) * (D + 1)) := by
          simp [List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ ≤ (D + 1) * ((D + 1) * (D + 1)) := Nat.mul_le_mul_right _ (by omega)
  calc ((H ×ˢ H).map fun q =>
        ((List.range (q.1.degreeOf (Fin.last n) + 1)).flatMap fun a =>
          (List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
            (List.range (min a b + 1)).map fun i =>
              (pscMat (F q.1) (F q.2) a b i).det).length).sum
      ≤ ((H ×ˢ H).map fun _ => (D + 1) * ((D + 1) * (D + 1))).sum := List.sum_le_sum h1
    _ = (H ×ˢ H).length * ((D + 1) * ((D + 1) * (D + 1))) := by
        simp [List.map_const', List.sum_replicate, nsmul_eq_mul]
    _ = (H.length * H.length) * ((D + 1) * (D + 1) * (D + 1)) := by
        rw [List.length_product]; ring

/-! ## Sign-constancy of the subresultant data -/

/-- **Sign-constancy of the principal subresultant data.**  A family `P` of polynomials in `m + 1`
variables has *subresultant-constant signs* on a set `C` of base points if, for every pair of
members, every pair of degree bounds up to the degrees of the members and every index
`r ≤ min a b`, the signs of the principal subresultant coefficients of the two specialisations
agree at every two points of `C`.

This is the replacement for the hypothesis "the signs of *all* Sylvester minors are constant on
`C`" that `syl_minor_type_const` used: with it, `gcd_spec_natDegree_const_on_C` proves that the
degree of the gcd of two specialisations is constant on `C` (the classical subresultant theorem),
and it is *instantiable* from the projection data `pscFam H ⊆ projData H`, which has polynomially
many members.  (`NOTES.md` §2bis–§2quater.) -/
def PscSignConst {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ)
    (C : Set (Fin m → ℝ)) : Prop :=
  ∀ i j : Fin k, ∀ a b : ℕ, a ≤ (P i).degreeOf (Fin.last m) → b ≤ (P j).degreeOf (Fin.last m) →
    ∀ r : ℕ, r ≤ min a b → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((pscMat (spec (P i) x) (spec (P j) x) a b r).det)
        = SignType.sign ((pscMat (spec (P i) x') (spec (P j) x') a b r).det)

/-! ## The projection family -/

/-- All coefficients of the members of `H` with respect to the last variable. -/
def coeffFam {n : ℕ} (H : List (MvPolynomial (Fin (n + 1)) ℝ)) : List (MvPolynomial (Fin n) ℝ) :=
  H.flatMap fun P => (List.range (P.degreeOf (Fin.last n) + 1)).map fun j => (F P).coeff j

/-- The resultants of pairs of members of `H`, for all degree pairs up to the degrees in the last
variable. -/
def resFam {n : ℕ} (H : List (MvPolynomial (Fin (n + 1)) ℝ)) : List (MvPolynomial (Fin n) ℝ) :=
  (H ×ˢ H).flatMap fun q =>
    (List.range (q.1.degreeOf (Fin.last n) + 1)).flatMap fun a =>
      (List.range (q.2.degreeOf (Fin.last n) + 1)).map fun b =>
        (F q.1).resultant (F q.2) a b

/-- The projection data of a family: coefficients, resultants and principal subresultant
coefficients. -/
def projData {n : ℕ} (H : List (MvPolynomial (Fin (n + 1)) ℝ)) : List (MvPolynomial (Fin n) ℝ) :=
  coeffFam H ++ resFam H ++ pscFam H

/-- The family used one level down: the projection data together with its derivative tower, and the
constant polynomial `0` (which is its own derivative, so that the family is closed under
`pderiv (last)`: for a member of the tower the derivative is `0` — a member — or again a member).

Adding `0` is what makes the strong derivative closure
`∀ i, ∃ j, H.get j = pderiv (last) (H.get i)` available at every level of the decomposition; the
type constancy of the CAD (`syl_minor_type_const`, `baseCell_type_const`) and the cell
connectivity (`CadCells_preconnected`) are stated with that strong form. -/
def projDataT : (n : ℕ) → List (MvPolynomial (Fin (n + 1)) ℝ) → List (MvPolynomial (Fin n) ℝ)
  | 0, H => projData H
  | (_ + 1), H => tower (projData H) ++ [0]

theorem coeffFam_deg {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : ∀ Q ∈ coeffFam H, Q.totalDegree ≤ D := by
  intro Q hQ
  simp only [coeffFam, List.mem_flatMap, List.mem_map, List.mem_range] at hQ
  obtain ⟨P, hP, j, -, rfl⟩ := hQ
  exact (totalDegree_coeff_le P j).trans (hH P hP)

theorem resFam_deg {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : ∀ Q ∈ resFam H, Q.totalDegree ≤ 2 * D * D := by
  intro Q hQ
  simp only [resFam, List.mem_flatMap, List.mem_map, List.mem_range] at hQ
  obtain ⟨q, hq, a, ha, b, hb, rfl⟩ := hQ
  obtain ⟨hq1, hq2⟩ := List.mem_product.mp hq
  have haD : a ≤ D := (Nat.lt_succ_iff.mp ha).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.1 hq1))
  have hbD : b ≤ D := (Nat.lt_succ_iff.mp hb).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.2 hq2))
  refine (totalDegree_resultant_le (F q.1) (F q.2) a b D
    (fun j => (totalDegree_coeff_le q.1 j).trans (hH q.1 hq1))
    (fun j => (totalDegree_coeff_le q.2 j).trans (hH q.2 hq2))).trans ?_
  have hab : a + b ≤ 2 * D := by omega
  calc (a + b) * D ≤ (2 * D) * D := Nat.mul_le_mul_right D hab
    _ = 2 * D * D := by ring

theorem projData_deg {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : ∀ Q ∈ projData H, Q.totalDegree ≤ 2 * D * D + 1 := by
  intro Q hQ
  rw [projData, List.mem_append] at hQ
  rcases hQ with hQ | hQ
  · rw [List.mem_append] at hQ
    rcases hQ with hQ | hQ
    · exact (coeffFam_deg hH Q hQ).trans ((le_two_mul_sq D).trans (Nat.le_add_right _ 1))
    · exact (resFam_deg hH Q hQ).trans (by omega)
  · exact (pscFam_deg hH Q hQ).trans (by omega)

theorem coeffFam_length {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : (coeffFam H).length ≤ H.length * (D + 1) := by
  rw [coeffFam, List.length_flatMap]
  have h1 : ∀ P ∈ H, ((List.range (P.degreeOf (Fin.last n) + 1)).map
      fun j => (F P).coeff j).length ≤ D + 1 := by
    intro P hP
    rw [List.length_map, List.length_range]
    have : P.degreeOf (Fin.last n) ≤ D :=
      (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH P hP)
    omega
  refine (List.sum_le_sum h1).trans (le_of_eq ?_)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul]
  simp

theorem resFam_length {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) :
    (resFam H).length ≤ (H.length * H.length) * ((D + 1) * (D + 1)) := by
  rw [resFam, List.length_flatMap]
  have h1 : ∀ q ∈ H ×ˢ H,
      ((List.range (q.1.degreeOf (Fin.last n) + 1)).flatMap fun a =>
        (List.range (q.2.degreeOf (Fin.last n) + 1)).map fun b =>
          (F q.1).resultant (F q.2) a b).length ≤ (D + 1) * (D + 1) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := List.mem_product.mp hq
    simp only [List.length_flatMap, List.length_map, List.length_range]
    have hq1D : q.1.degreeOf (Fin.last n) ≤ D :=
      (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.1 hq1)
    have hq2D : q.2.degreeOf (Fin.last n) ≤ D :=
      (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.2 hq2)
    rw [List.map_const', List.sum_replicate, List.length_range, nsmul_eq_mul]
    simp only [Nat.cast_id]
    exact Nat.mul_le_mul (by omega) (by omega)
  refine (List.sum_le_sum h1).trans (le_of_eq ?_)
  simp only [List.map_const', List.sum_replicate, List.length_product,
    nsmul_eq_mul, Nat.cast_id]

theorem projData_length {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) :
    (projData H).length
      ≤ H.length * (D + 1) + (H.length * H.length) * ((D + 1) * (D + 1))
        + (H.length * H.length) * ((D + 1) * (D + 1) * (D + 1)) := by
  rw [projData, List.length_append, List.length_append]
  exact Nat.add_le_add (Nat.add_le_add (coeffFam_length hH) (resFam_length hH))
    (pscFam_length hH)

/-! ## The derivative tower -/

theorem tower_deg {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : ∀ Q ∈ tower H, Q.totalDegree ≤ D := by
  intro Q hQ
  simp only [tower, List.mem_flatMap, List.mem_map, List.mem_range] at hQ
  obtain ⟨P, hP, a, -, rfl⟩ := hQ
  exact (totalDegree_iterate_pderiv_le P (Fin.last n) a).trans (hH P hP)

theorem tower_length {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : (tower H).length ≤ H.length * (D + 1) := by
  rw [tower, List.length_flatMap]
  have h1 : ∀ P ∈ H, ((List.range (P.degreeOf (Fin.last n) + 1)).map
      fun a => ((MvPolynomial.pderiv (Fin.last n))^[a]) P).length ≤ D + 1 := by
    intro P hP
    rw [List.length_map, List.length_range]
    have : P.degreeOf (Fin.last n) ≤ D :=
      (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH P hP)
    omega
  refine (List.sum_le_sum h1).trans (le_of_eq ?_)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul]
  simp

/-- Degrees of the family one level down. -/
theorem projDataT_deg {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : ∀ Q ∈ projDataT n H, Q.totalDegree ≤ 2 * D * D + 1 := by
  match n with
  | 0 => exact projData_deg hH
  | k + 1 =>
    intro Q hQ
    rw [projDataT, List.mem_append, List.mem_singleton] at hQ
    rcases hQ with hQ | rfl
    · exact tower_deg (projData_deg hH) Q hQ
    · simp

/-- Length of the family one level down. -/
theorem projDataT_length {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) :
    (projDataT n H).length
      ≤ (H.length * (D + 1) + (H.length * H.length) * ((D + 1) * (D + 1))
          + (H.length * H.length) * ((D + 1) * (D + 1) * (D + 1)) + 1) *
          ((2 * D * D + 1) + 1) := by
  match n with
  | 0 =>
    refine (projData_length hH).trans ?_
    exact (Nat.le_mul_of_pos_right _ (by omega : 0 < (2 * D * D + 1) + 1)).trans
      (Nat.mul_le_mul_right _ (Nat.le_succ _))
  | k + 1 =>
    have hstep : (tower (projData H) ++ [0]).length
        ≤ (projData H).length * ((2 * D * D + 1) + 1) + 1 := by
      rw [List.length_append, List.length_singleton]
      exact Nat.add_le_add_right (tower_length (projData_deg hH)) 1
    refine hstep.trans ?_
    have h1 : (projData H).length * ((2 * D * D + 1) + 1)
        ≤ (H.length * (D + 1) + (H.length * H.length) * ((D + 1) * (D + 1))
            + (H.length * H.length) * ((D + 1) * (D + 1) * (D + 1))) * ((2 * D * D + 1) + 1) :=
      Nat.mul_le_mul_right _ (projData_length hH)
    calc (projData H).length * ((2 * D * D + 1) + 1) + 1
        ≤ (H.length * (D + 1) + (H.length * H.length) * ((D + 1) * (D + 1))
            + (H.length * H.length) * ((D + 1) * (D + 1) * (D + 1))) * ((2 * D * D + 1) + 1)
          + ((2 * D * D + 1) + 1) :=
          Nat.add_le_add h1 (by omega)
      _ = (H.length * (D + 1) + (H.length * H.length) * ((D + 1) * (D + 1))
            + (H.length * H.length) * ((D + 1) * (D + 1) * (D + 1)) + 1) *
          ((2 * D * D + 1) + 1) := by ring

/-- **`projDataT (m+1) H` is closed under `pderiv (Fin.last m)`** (in the strong sense that the
derivative of a member is again a member): the family is `tower (projData H) ++ [0]`, and by
`tower_deriv_closed` the derivative of a member of the tower is either `0` — which is a member —
or again a member of the tower.  This is the `hclosed` hypothesis of `syl_minor_type_const`,
`baseCell_type_const` and `CadCells_preconnected` at the levels of the decomposition below the
first. -/
private theorem projDataT_deriv_closed_aux {m : ℕ} (H : List (MvPolynomial (Fin (m + 1 + 1)) ℝ)) :
    ∀ i : Fin (tower (projData H) ++ [(0 : MvPolynomial (Fin (m + 1)) ℝ)]).length,
      ∃ j : Fin (tower (projData H) ++ [(0 : MvPolynomial (Fin (m + 1)) ℝ)]).length,
        (tower (projData H) ++ [(0 : MvPolynomial (Fin (m + 1)) ℝ)]).get j
          = MvPolynomial.pderiv (Fin.last m)
            ((tower (projData H) ++ [(0 : MvPolynomial (Fin (m + 1)) ℝ)]).get i) := by
  intro i
  have hmem : (tower (projData H) ++ [(0 : MvPolynomial (Fin (m + 1)) ℝ)]).get i
      ∈ tower (projData H) ++ [(0 : MvPolynomial (Fin (m + 1)) ℝ)] := List.get_mem _ i
  rcases List.mem_append.mp hmem with hm | hm
  · rcases tower_deriv_closed (projData H) ((tower (projData H) ++ [(0 : MvPolynomial (Fin (m + 1)) ℝ)]).get i) hm with h0 | hmem2
    · obtain ⟨j', hj'⟩ := List.mem_iff_get.mp
        (List.mem_append_right _ (List.mem_singleton.mpr (rfl : (0 : MvPolynomial (Fin (m + 1)) ℝ) = 0)))
      exact ⟨j', hj'.trans h0.symm⟩
    · obtain ⟨j', hj'⟩ := List.mem_iff_get.mp (List.mem_append_left _ hmem2)
      exact ⟨j', by rw [hj']⟩
  · rw [List.mem_singleton] at hm
    exact ⟨i, by rw [hm]; simp⟩

theorem projDataT_deriv_closed {m : ℕ} (H : List (MvPolynomial (Fin (m + 1 + 1)) ℝ)) :
    ∀ i : Fin (projDataT (m + 1) H).length,
      ∃ j : Fin (projDataT (m + 1) H).length,
        (projDataT (m + 1) H).get j
          = MvPolynomial.pderiv (Fin.last m) ((projDataT (m + 1) H).get i) := by
  simpa only [projDataT] using projDataT_deriv_closed_aux H

end Work.WilE4.CAD
