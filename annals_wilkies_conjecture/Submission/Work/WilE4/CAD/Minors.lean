/-
  WilE4 / CAD — the *enriched* projection data.

  `Proj.lean` records, for each pair of members, the coefficients and the **maximal** Sylvester
  minors (the resultants).  That data is insufficient for the type constancy: a verified
  counterexample (`NOTES.md` §1) satisfies it and still has a varying realised sign-vector set,
  because two members may share a factor `G`, so that every resultant of the pair vanishes
  identically and the crossing of the *cofactor* roots becomes invisible.

  The exact computations recorded in `NOTES.md` §2bis show that the missing information is carried
  by the *non-maximal* Sylvester minors (the classical "subresultant"/Lazard projection data):
  for the counterexample, the leading principal minor of size `5` of the `6 × 6` Sylvester matrix
  of the pair `(P0,P4)` equals `-12500 · x · (x-7) · (x+9)`, so it vanishes precisely at `x = 0` and
  its sign is *not* constant on the window.

  This file defines that extra data and bounds its degree and length, so that the degree recursion
  of `Bounds.lean` continues to work on the enriched family.  All the minors are determinants of
  submatrices of the Sylvester matrix, whose entries are coefficients of the two members, so the
  degree of a minor of size `l` is at most `l * D` where `D` bounds the coefficients.
-/
import Submission.Work.WilE4.CAD.Proj

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial

/-! ## Determinants of submatrices -/

/-- The determinant of the submatrix of `M` with rows `r` and columns `c` (a "minor"). -/
def detSub {d N : ℕ} (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin d) ℝ))
    {l : ℕ} (r c : Fin l → Fin N) : MvPolynomial (Fin d) ℝ :=
  (M.submatrix r c).det

/-- A minor of size `l` of a matrix whose entries have total degree at most `D` has total degree at
most `l * D`. -/
theorem totalDegree_detSub_le {d N : ℕ} (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin d) ℝ))
    {l : ℕ} (r c : Fin l → Fin N) {D : ℕ} (hM : ∀ i j, (M i j).totalDegree ≤ D) :
    (detSub M r c).totalDegree ≤ l * D := by
  rw [detSub, Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun σ _ => ?_
  refine (totalDegree_units_smul_le (Equiv.Perm.sign σ) (∏ i, M.submatrix r c (σ i) i)).trans ?_
  calc (∏ i, M.submatrix r c (σ i) i).totalDegree
      ≤ ∑ i, (M.submatrix r c (σ i) i).totalDegree := totalDegree_prod_le _
    _ ≤ ∑ _i : Fin l, D :=
        Finset.sum_le_sum fun i _ => by
          rw [Matrix.submatrix_apply]; exact hM _ _
    _ = l * D := by simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ## The leading principal minors of a Sylvester matrix -/

/-- Specialising a minor of a Sylvester matrix gives the corresponding minor of the specialised
Sylvester matrix. -/
theorem eval_sylvester_detSub {m : ℕ} (P Q : MvPolynomial (Fin (m + 1)) ℝ) (a b l : ℕ)
    (r c : Fin l → Fin (a + b)) (x : Fin m → ℝ) :
    MvPolynomial.eval x (detSub (Polynomial.sylvester (F P) (F Q) a b) r c)
      = Matrix.det ((Polynomial.sylvester (Work.WilE4.spec P x) (Work.WilE4.spec Q x) a b).submatrix
          r c) := by
  simp only [detSub, spec_eq_map]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.submatrix_apply,
    Polynomial.sylvester_map_map (F P) (F Q) a b (MvPolynomial.eval x)]

/-- The leading principal minors of the Sylvester matrix `sylvester f g a b`: for every `l ≤ a+b`,
the determinant of the submatrix formed by the first `l` rows and columns. -/
def leadMinors {n : ℕ} (P Q : MvPolynomial (Fin (n + 1)) ℝ) (a b : ℕ) :
    List (MvPolynomial (Fin n) ℝ) :=
  (List.finRange (a + b + 1)).map fun l =>
    detSub (Polynomial.sylvester (F P) (F Q) a b)
      (Fin.castLE (Nat.lt_succ_iff.mp l.isLt))
      (Fin.castLE (Nat.lt_succ_iff.mp l.isLt))

theorem leadMinors_deg {n : ℕ} (P Q : MvPolynomial (Fin (n + 1)) ℝ) (a b D : ℕ)
    (hP : ∀ j, ((F P).coeff j).totalDegree ≤ D)
    (hQ : ∀ j, ((F Q).coeff j).totalDegree ≤ D) :
    ∀ R ∈ leadMinors P Q a b, R.totalDegree ≤ (a + b) * D := by
  intro R hR
  rw [leadMinors, List.mem_map] at hR
  obtain ⟨l, hl, rfl⟩ := hR
  have hl' : l.val ≤ a + b := Nat.lt_succ_iff.mp l.isLt
  refine (totalDegree_detSub_le _ _ _ fun i j => ?_).trans (Nat.mul_le_mul_right D hl')
  exact totalDegree_sylvester_entry_le (F P) (F Q) D a b hP hQ i j

theorem leadMinors_length {n : ℕ} (P Q : MvPolynomial (Fin (n + 1)) ℝ) (a b : ℕ) :
    (leadMinors P Q a b).length = a + b + 1 := by
  rw [leadMinors, List.length_map, List.length_finRange]

/-! ## The enriched projection data -/

/-- The extra projection data of a family: for every ordered pair of members and every pair of
degree bounds up to the degrees in the last variable, the leading principal minors of the Sylvester
matrix. -/
def minFam {n : ℕ} (H : List (MvPolynomial (Fin (n + 1)) ℝ)) : List (MvPolynomial (Fin n) ℝ) :=
  (H ×ˢ H).flatMap fun q =>
    (List.range (q.1.degreeOf (Fin.last n) + 1)).flatMap fun a =>
      (List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
        leadMinors q.1 q.2 a b

/-- The projection data of a family, enriched with the non-maximal Sylvester minors. -/
def projData2 {n : ℕ} (H : List (MvPolynomial (Fin (n + 1)) ℝ)) : List (MvPolynomial (Fin n) ℝ) :=
  projData H ++ minFam H

/-- The enriched projection data of a family, together with its derivative tower: what the level
above needs.  (Same shape as `projDataT`.) -/
def projData2T : (n : ℕ) → List (MvPolynomial (Fin (n + 1)) ℝ) → List (MvPolynomial (Fin n) ℝ)
  | 0, H => projData2 H
  | (_ + 1), H => tower (projData2 H)

/-- Every leading principal minor of a pair of members, with degree bounds up to the degrees of the
members, belongs to the enriched projection data. -/
theorem leadMinors_mem_projData2 {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)}
    {P Q : MvPolynomial (Fin (n + 1)) ℝ} (hP : P ∈ H) (hQ : Q ∈ H) {a b : ℕ}
    (ha : a ≤ P.degreeOf (Fin.last n)) (hb : b ≤ Q.degreeOf (Fin.last n))
    {R : MvPolynomial (Fin n) ℝ} (hR : R ∈ leadMinors P Q a b) :
    R ∈ projData2 H := by
  rw [projData2, List.mem_append]
  refine Or.inr ?_
  rw [minFam, List.mem_flatMap]
  refine ⟨(P, Q), List.mem_product.mpr ⟨hP, hQ⟩, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a, List.mem_range.mpr (Nat.lt_succ_of_le ha), ?_⟩
  rw [List.mem_flatMap]
  exact ⟨b, List.mem_range.mpr (Nat.lt_succ_of_le hb), hR⟩

/-- The enriched projection data is part of the family used one level down. -/
theorem projData2_subset_projData2T (k : ℕ) (H : List (MvPolynomial (Fin (k + 1)) ℝ)) :
    ∀ P ∈ projData2 H, P ∈ projData2T k H := by
  match k with
  | 0 => exact fun P hP => hP
  | _ + 1 =>
    intro P hP
    show P ∈ tower (projData2 H)
    rw [tower, List.mem_flatMap]
    exact ⟨P, hP, List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), by simp⟩⟩


theorem minFam_deg {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : ∀ Q ∈ minFam H, Q.totalDegree ≤ 2 * D * D := by
  intro Q hQ
  simp only [minFam, List.mem_flatMap, List.mem_range] at hQ
  obtain ⟨q, hq, a, ha, b, hb, hQ⟩ := hQ
  obtain ⟨hq1, hq2⟩ := List.mem_product.mp hq
  have haD : a ≤ D := (Nat.lt_succ_iff.mp ha).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.1 hq1))
  have hbD : b ≤ D := (Nat.lt_succ_iff.mp hb).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.2 hq2))
  refine (leadMinors_deg q.1 q.2 a b D
    (fun j => (totalDegree_coeff_le q.1 j).trans (hH q.1 hq1))
    (fun j => (totalDegree_coeff_le q.2 j).trans (hH q.2 hq2)) Q hQ).trans ?_
  have hab : a + b ≤ 2 * D := by omega
  calc (a + b) * D ≤ (2 * D) * D := Nat.mul_le_mul_right D hab
    _ = 2 * D * D := by ring

theorem projData2_deg {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) : ∀ Q ∈ projData2 H, Q.totalDegree ≤ 2 * D * D + 1 := by
  intro Q hQ
  rw [projData2, List.mem_append] at hQ
  rcases hQ with hQ | hQ
  · exact (projData_deg hH Q hQ).trans (by omega)
  · exact (minFam_deg hH Q hQ).trans (by omega)

theorem minFam_length {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) :
    (minFam H).length ≤ (H.length * H.length) * ((D + 1) * (D + 1) * (2 * D + 1)) := by
  have hinner : ∀ q ∈ H ×ˢ H, ∀ a : ℕ, a ≤ D →
      ((List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
          leadMinors q.1 q.2 a b).length ≤ (D + 1) * (2 * D + 1) := by
    intro q hq a ha
    obtain ⟨hq1, hq2⟩ := List.mem_product.mp hq
    have hq2D : q.2.degreeOf (Fin.last n) ≤ D :=
      (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.2 hq2)
    have hb : ∀ b ∈ List.range (q.2.degreeOf (Fin.last n) + 1),
        (leadMinors q.1 q.2 a b).length ≤ 2 * D + 1 := by
      intro b hb
      have hbD : b ≤ D := (Nat.lt_succ_iff.mp (List.mem_range.mp hb)).trans hq2D
      rw [leadMinors_length]
      omega
    calc ((List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
            leadMinors q.1 q.2 a b).length
        = ((List.range (q.2.degreeOf (Fin.last n) + 1)).map fun b =>
            (leadMinors q.1 q.2 a b).length).sum := List.length_flatMap
      _ ≤ ((List.range (q.2.degreeOf (Fin.last n) + 1)).map fun _ => (2 * D + 1)).sum :=
          List.sum_le_sum hb
      _ = (q.2.degreeOf (Fin.last n) + 1) * (2 * D + 1) := by
          simp [List.map_const', List.sum_replicate]
      _ ≤ (D + 1) * (2 * D + 1) := Nat.mul_le_mul_right _ (by omega)
  have hout : ∀ q ∈ H ×ˢ H,
      ((List.range (q.1.degreeOf (Fin.last n) + 1)).flatMap fun a =>
        (List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
          leadMinors q.1 q.2 a b).length ≤ (D + 1) * ((D + 1) * (2 * D + 1)) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := List.mem_product.mp hq
    have hq1D : q.1.degreeOf (Fin.last n) ≤ D :=
      (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hH q.1 hq1)
    have ha : ∀ a ∈ List.range (q.1.degreeOf (Fin.last n) + 1),
        ((List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
              leadMinors q.1 q.2 a b).length ≤ (D + 1) * (2 * D + 1) := by
      intro a ha
      exact hinner q hq a ((Nat.lt_succ_iff.mp (List.mem_range.mp ha)).trans hq1D)
    calc ((List.range (q.1.degreeOf (Fin.last n) + 1)).flatMap fun a =>
            (List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
              leadMinors q.1 q.2 a b).length
        = ((List.range (q.1.degreeOf (Fin.last n) + 1)).map fun a =>
            ((List.range (q.2.degreeOf (Fin.last n) + 1)).flatMap fun b =>
              leadMinors q.1 q.2 a b).length).sum := List.length_flatMap
      _ ≤ ((List.range (q.1.degreeOf (Fin.last n) + 1)).map fun _ =>
            ((D + 1) * (2 * D + 1))).sum := List.sum_le_sum ha
      _ = (q.1.degreeOf (Fin.last n) + 1) * ((D + 1) * (2 * D + 1)) := by
          simp [List.map_const', List.sum_replicate]
      _ ≤ (D + 1) * ((D + 1) * (2 * D + 1)) := Nat.mul_le_mul_right _ (by omega)
  rw [minFam, List.length_flatMap]
  refine (List.sum_le_sum hout).trans (le_of_eq ?_)
  simp only [List.map_const', List.sum_replicate, List.length_product, nsmul_eq_mul, Nat.cast_id]
  ring

theorem projData2_length {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)} {D : ℕ}
    (hH : ∀ P ∈ H, P.totalDegree ≤ D) :
    (projData2 H).length ≤ H.length * (D + 1) + (H.length * H.length) * ((D + 1) * (D + 1))
      + (H.length * H.length) * ((D + 1) * (D + 1) * (D + 1))
      + (H.length * H.length) * ((D + 1) * (D + 1) * (2 * D + 1)) := by
  rw [projData2, List.length_append]
  exact Nat.add_le_add (projData_length hH) (minFam_length hH)

end Work.WilE4.CAD
