/-
Area DSCOH — the generator description of the degree-zero part of a chart localization, for the
shift `S(0) = shift 0` of the polynomial ring (which is the polynomial ring with its standard
grading).

`degZero ℳ S = ⨆_{k} (ℳ (k·|S|)) / X_S^k` is defined as an `iSup` of submodules, so a priori an
element of it is only a *finite sum* of generators `m/X_S^k`.  Because the pieces
`ℳ (k·|S|)/X_S^k` are nested — multiplication by `X_S ∈ homSub A n |S|` moves `ℳ (k·|S|)`
into `ℳ ((k+1)·|S|)` and does not change the fraction — the `iSup` is a directed union, and one
single generator suffices: `y ∈ degZero ℳ S ↔ ∃ k m, m ∈ ℳ (k·|S|) ∧ m/X_S^k = y`.

For `ℳ = shift (A := A) (n := n) 0` the pieces are the homogeneous components `homSub A n d`, so
the statement becomes the one below.  The `SetLike.GradedSMul` hypothesis is exactly what makes
the union directed.
-/
import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.Shift
import Submission.Work.DSCOH.shift_gradedSMul
import Submission.Work.DSCOH.divPow_toLoc_mem
import Submission.Work.DSCOH.degZero_exact
import Submission.Work.DSCOH.ShiftToolkit

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The shifted grading `S(0)` is the standard grading of `A[X₀,…,X_{n-1}]`. -/
private lemma shift_zero_eq_homSub : shift (A := A) (n := n) 0 = homSub A n := by
  funext e
  simp [shift]

/-- The product `X_S = ∏_{i∈S} Xᵢ` of the variables indexed by `S` is homogeneous of degree
`|S|`; this is the degree shift by which multiplication by `X_S` moves the grading. -/
private lemma monomial_mem_homSub (S : Finset (Fin n)) :
    monomial (A := A) S ∈ homSub A n S.card := by
  rw [homSub, MvPolynomial.mem_homogeneousSubmodule]
  unfold monomial Var
  simpa using MvPolynomial.IsHomogeneous.prod (R := A) S (fun i => MvPolynomial.X i)
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X A i)

/-- **The pieces of the `degZero` filtration are nested.**  Multiplication by `X_S` maps the
`k`-th piece into the `(k+1)`-st: it shifts the grading by `|S|` (using the `GradedSMul`
structure) and `X_S·m/X_S^{k+1} = m/X_S^k` in the localization. -/
private lemma monotone_degZero_shift_zero_pieces
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) 0)] (S : Finset (Fin n)) :
    Monotone (fun k : ℕ => Submodule.map
      ((divPow (A := A) (M := Poly A n) S k).comp (toLoc (A := A) (M := Poly A n) S))
      (shift (A := A) (n := n) 0 (k * S.card))) := by
  apply monotone_nat_of_le_succ
  intro k
  rintro _ ⟨m, hm, rfl⟩
  refine Submodule.mem_map.mpr ⟨(monomial (A := A) S) ^ 1 * m, ?_, ?_⟩
  · rw [pow_one]
    have hsm := SetLike.GradedSMul.smul_mem (monomial_mem_homSub (A := A) (n := n) S) hm
    rw [vadd_eq_add] at hsm
    rw [show S.card + k * S.card = (k + 1) * S.card from by ring] at hsm
    simpa [smul_eq_mul] using hsm
  · show divPow (A := A) (M := Poly A n) S (k + 1)
        (toLoc (A := A) (M := Poly A n) S ((monomial (A := A) S) ^ 1 * m)) =
      divPow (A := A) (M := Poly A n) S k (toLoc (A := A) (M := Poly A n) S m)
    exact divPow_toLoc_smul_monomial_pow (A := A) (n := n) S k 1 m

theorem mem_degZero_shift_zero_iff {A : Type*} [CommRing A] {n : ℕ}
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) 0)]
    (S : Finset (Fin n)) (y : locAt (A := A) (M := Poly A n) S) :
    y ∈ degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) 0) S ↔
      ∃ (k : ℕ) (m : Poly A n), m ∈ homSub A n (k * S.card) ∧
        divPow (A := A) (M := Poly A n) S k (toLoc (A := A) (M := Poly A n) S m) = y := by
  constructor
  · -- `y` lies in the directed union, hence in a single piece.
    intro hy
    have hy' : y ∈ ⨆ k : ℕ, Submodule.map
        ((divPow (A := A) (M := Poly A n) S k).comp (toLoc (A := A) (M := Poly A n) S))
        (shift (A := A) (n := n) 0 (k * S.card)) := hy
    obtain ⟨k, m, hm, hmy⟩ :=
      (Submodule.mem_iSup_of_directed _
        (monotone_degZero_shift_zero_pieces (A := A) (n := n) S).directed_le).mp hy'
    exact ⟨k, m, by rwa [shift_zero_eq_homSub (A := A) (n := n)] at hm, hmy⟩
  · -- A single generator `m/X_S^k` with `m ∈ homSub A n (k·|S|)` lies in `degZero`.
    rintro ⟨k, m, hm, rfl⟩
    exact divPow_toLoc_mem (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) 0) S k
      (by rwa [← shift_zero_eq_homSub (A := A) (n := n)] at hm)

end Work.DSCOH
