/-
  WilE4 / CAD — the bridge from the sign conditions of the projection data to the hypotheses of the
  type-constancy lemmas.

  A base cell of the decomposition is a sign condition of `projDataT k H = tower (projData k H)`, so
  on it the signs of all coefficients and all resultants of the members of `H` are fixed.  The two
  membership lemmas here are what turns that into the `hcoeff`/`hres` hypotheses of
  `realized_const_of_signConst_bdd`.
-/
import Submission.Work.WilE4.CAD.Proj

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

variable {k m n : ℕ}

theorem coeffFam_mem {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)}
    {P : MvPolynomial (Fin (n + 1)) ℝ} (hP : P ∈ H) {j : ℕ} (hj : j ≤ P.degreeOf (Fin.last n)) :
    (F P).coeff j ∈ coeffFam H := by
  rw [coeffFam, List.mem_flatMap]
  refine ⟨P, hP, ?_⟩
  rw [List.mem_map]
  exact ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩

theorem coeffFam_mem_projData {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)}
    {P : MvPolynomial (Fin (n + 1)) ℝ} (hP : P ∈ H) {j : ℕ} (hj : j ≤ P.degreeOf (Fin.last n)) :
    (F P).coeff j ∈ projData H :=
  List.mem_append_left _ (List.mem_append_left _ (coeffFam_mem hP hj))

theorem resFam_mem {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)}
    {P Q : MvPolynomial (Fin (n + 1)) ℝ} (hP : P ∈ H) (hQ : Q ∈ H) {a b : ℕ}
    (ha : a ≤ P.degreeOf (Fin.last n)) (hb : b ≤ Q.degreeOf (Fin.last n)) :
    (F P).resultant (F Q) a b ∈ resFam H := by
  rw [resFam, List.mem_flatMap]
  refine ⟨(P, Q), List.mem_product.mpr ⟨hP, hQ⟩, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a, List.mem_range.mpr (Nat.lt_succ_of_le ha), ?_⟩
  rw [List.mem_map]
  exact ⟨b, List.mem_range.mpr (Nat.lt_succ_of_le hb), rfl⟩

theorem resFam_mem_projData {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)}
    {P Q : MvPolynomial (Fin (n + 1)) ℝ} (hP : P ∈ H) (hQ : Q ∈ H) {a b : ℕ}
    (ha : a ≤ P.degreeOf (Fin.last n)) (hb : b ≤ Q.degreeOf (Fin.last n)) :
    (F P).resultant (F Q) a b ∈ projData H :=
  List.mem_append_left _ (List.mem_append_right _ (resFam_mem hP hQ ha hb))

/-- Every principal subresultant coefficient of a pair of members belongs to the projection
data. -/
theorem pscFam_mem_projData {n : ℕ} {H : List (MvPolynomial (Fin (n + 1)) ℝ)}
    {P Q : MvPolynomial (Fin (n + 1)) ℝ} (hP : P ∈ H) (hQ : Q ∈ H) {a b : ℕ}
    (ha : a ≤ P.degreeOf (Fin.last n)) (hb : b ≤ Q.degreeOf (Fin.last n)) {i : ℕ}
    (hi : i ≤ min a b) : (pscMat (F P) (F Q) a b i).det ∈ projData H :=
  List.mem_append_right _ (pscFam_mem hP hQ ha hb hi)

/-- A set on which the sign of every member of a family is constant. -/
def SignConstOn {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ)) (C : Set (Fin m → ℝ)) : Prop :=
  ∀ Q ∈ G, ∀ x ∈ C, ∀ x' ∈ C,
    SignType.sign (MvPolynomial.eval x Q) = SignType.sign (MvPolynomial.eval x' Q)

theorem signConstOn_of_signCond {m : ℕ} {G : List (MvPolynomial (Fin m) ℝ)}
    {v : Fin G.length → SignType} {C : SAd m} (hC : C.set ⊆ signCond G v) :
    SignConstOn G (C.set) := by
  intro Q hQ x hx x' hx'
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hQ
  rw [hC hx i, hC hx' i]

/-- The sign-constancy of the projection data of a family implies the sign-constancy of its
principal subresultant data (the `PscSignConst` hypothesis of
`gcd_spec_natDegree_const_on_C`). -/
theorem pscSignConst_of_signConstOn {m k : ℕ} {H : List (MvPolynomial (Fin (m + 1)) ℝ)}
    {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ} (hP : ∀ i, P i ∈ H) {C : SAd m}
    (hsc : SignConstOn (projData H) C.set) : PscSignConst P C.set := by
  intro i j a b ha hb r hr x hx x' hx'
  have hmem := pscFam_mem_projData (hP i) (hP j) ha hb hr
  have h := hsc _ hmem x hx x' hx'
  rwa [eval_pscMat_det, eval_pscMat_det] at h

end Work.WilE4.CAD
