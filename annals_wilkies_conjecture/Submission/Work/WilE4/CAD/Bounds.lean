/-
  WilE4 / CAD — the cell count and the degree of a level of the cylindrical decomposition.

  For a family `H` of polynomials in `n` variables, `CadCells n H` is a list of cells.  We bound

  * `bCellLen n`      — the number of cells,
  * `bCellDeg n`      — the degree of every cell,
  * `bCellBasics n`   — the number of basic sets of every cell,

  as explicit polynomials evaluated at `famDeg H`.  The three recursions are

      |CadCells (k+1) H| ≤ |CadCells k (projDataT k H)| * (2 * (E^2 + 1) + 1)
      (cell C H w).deg   ≤ C.deg + C.basics.length * (2 * E)
      (cell C H w).basics.length = C.basics.length

  with `E = famDeg H`, together with the growth `famDeg (projDataT k H) ≤ 8 * (E + 1)^8` of the
  projection data.  The factor `2 * (E^2 + 1) + 1` is the bound of `realized_signvec_card` on the
  number of sign vectors of a family of univariate polynomials of degree at most `E` that can be
  realised at a point; passing from "realised somewhere over the cell" to "realised at one point of
  the cell" is the type-constancy of the decomposition, which is the only hypothesis of
  `CadCells_length_le`.
-/
import Submission.Work.WilE4.CAD.Size
import Submission.Work.WilE4.CAD.Ops
import Submission.Work.WilE4.CAD.realized_signvec_card
import Submission.Work.WilE4.CAD.CadCells_isUnionOf

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

variable {k m n : ℕ}

/-! ## Monotonicity of `Polynomial.eval` on `ℕ` -/

theorem polynomial_eval_mono (p : Polynomial ℕ) : Monotone fun n : ℕ => p.eval n := by
  intro a b hab
  induction p using Polynomial.induction_on' with
  | monomial k c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab k)
  | add p q hp hq => simpa [Polynomial.eval_add] using add_le_add hp hq

/-! ## The degree of a specialisation -/

/-- The degree in the last variable of the specialisation of `P` at `x` is bounded by the size of
any family containing `P`. -/
theorem natDegree_spec_le_famDeg {m : ℕ} {H : List (MvPolynomial (Fin (m + 1)) ℝ)}
    {P : MvPolynomial (Fin (m + 1)) ℝ} (hP : P ∈ H) (x : Fin m → ℝ) :
    (spec P x).natDegree ≤ famDeg H := by
  have h1 : (spec P x).natDegree ≤ (F P).natDegree := by
    rw [spec_eq_map]
    exact Polynomial.natDegree_map_le
  have h2 : (F P).natDegree = (MvPolynomial.rename (rot m) P).degreeOf 0 := by
    rw [F]
    exact MvPolynomial.natDegree_finSuccEquiv _
  have h3 : (MvPolynomial.rename (rot m) P).degreeOf 0
      ≤ (MvPolynomial.rename (rot m) P).totalDegree :=
    MvPolynomial.degreeOf_le_totalDegree _ _
  have h4 : (MvPolynomial.rename (rot m) P).totalDegree = P.totalDegree :=
    rename_totalDegree (rot m) P
  have h5 : P.totalDegree ≤ famDeg H := totalDegree_le_famDeg hP
  omega

/-! ## The number of realised sign vectors over a cell -/

theorem allSign_nodup (k : ℕ) : (allSign k).Nodup := Finset.nodup_toList _

/-- If a single point of `C` realises every sign vector that is realised anywhere over `C`, then the
number of such sign vectors is bounded by the number of sign vectors of a family of univariate
polynomials of degree at most `famDeg H` (`realized_signvec_card`). -/
theorem card_realizedOn_le {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ)) (C : SAd k)
    (htc : ∃ x ∈ C.set, ∀ w : Fin H.length → SignType, RealizedOn H C w →
      ∃ t : ℝ, ∀ i, SignType.sign ((spec (H.get i) x).eval t) = w i) :
    ((allSign H.length).filter (fun w => RealizedOn H C w)).length
      ≤ 2 * (famDeg H * famDeg H + 1) + 1 := by
  classical
  obtain ⟨x, -, hreal⟩ := htc
  obtain ⟨S, hScard, hSmem⟩ := realized_signvec_card (fun i : Fin H.length => spec (H.get i) x)
    (fun i => natDegree_spec_le_famDeg (List.get_mem H i) x)
  have hsub : ∀ w ∈ (allSign H.length).filter (fun w => RealizedOn H C w), w ∈ S := by
    intro w hw
    rw [List.mem_filter] at hw
    obtain ⟨t, ht⟩ := hreal w (by simpa using hw.2)
    exact hSmem w ⟨t, ht⟩
  have hnd : ((allSign H.length).filter (fun w => RealizedOn H C w)).Nodup :=
    (allSign_nodup H.length).filter _
  calc ((allSign H.length).filter (fun w => RealizedOn H C w)).length
      = ((allSign H.length).filter (fun w => RealizedOn H C w)).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ S.card := Finset.card_le_card fun w hw => hsub w (by simpa using hw)
    _ ≤ 2 * (H.length * famDeg H + 1) + 1 := hScard
    _ ≤ 2 * (famDeg H * famDeg H + 1) + 1 := by
        have hE : H.length ≤ famDeg H := length_le_famDeg H
        have hmul : H.length * famDeg H ≤ famDeg H * famDeg H := Nat.mul_le_mul_right _ hE
        omega

/-- A `filterMap` that keeps the image of the elements satisfying a predicate has the length of the
`filter`. -/
private theorem filterMap_ite_some {α β : Type*} (l : List α) (p : α → Prop) [DecidablePred p]
    (f : α → β) :
    l.filterMap (fun a => if p a then some (f a) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.filterMap_cons, ih]
    by_cases h : p a <;> simp [h]

/-! ## The three bound polynomials -/

/-- An upper bound for `famDeg (projDataT k H)` in terms of `famDeg H`. -/
def projDataTBound : Polynomial ℕ := Polynomial.C 16 * (Polynomial.X + Polynomial.C 1) ^ 9

/-- An upper bound for the number of sign vectors of `H` realised over a cell. -/
def branchBound : Polynomial ℕ :=
  Polynomial.C 2 * (Polynomial.X * Polynomial.X + Polynomial.C 1) + Polynomial.C 1

theorem eval_projDataTBound (E : ℕ) : projDataTBound.eval E = 16 * (E + 1) ^ 9 := by
  simp [projDataTBound]

theorem eval_branchBound (E : ℕ) : branchBound.eval E = 2 * (E * E + 1) + 1 := by
  simp [branchBound]

theorem famDeg_projDataT_le_bound {n : ℕ} (H : List (MvPolynomial (Fin (n + 1)) ℝ)) :
    famDeg (projDataT n H) ≤ projDataTBound.eval (famDeg H) := by
  rw [eval_projDataTBound]
  exact famDeg_projDataT_le H

/-- An upper bound for the number of basic sets of a cell of the level-`n` decomposition. -/
def bCellBasics : ℕ → Polynomial ℕ
  | 0 => Polynomial.C 1
  | (n + 1) => (bCellBasics n).comp projDataTBound

/-- An upper bound for the degree of a cell of the level-`n` decomposition. -/
def bCellDeg : ℕ → Polynomial ℕ
  | 0 => Polynomial.C 0
  | (n + 1) => (bCellDeg n).comp projDataTBound +
      (bCellBasics n).comp projDataTBound * (Polynomial.C 2 * Polynomial.X)

/-- An upper bound for the number of cells of the level-`n` decomposition. -/
def bCellLen : ℕ → Polynomial ℕ
  | 0 => Polynomial.C 1
  | (n + 1) => (bCellLen n).comp projDataTBound * branchBound

/-! ## The recursions -/

/-- Given the type-constancy of the decomposition (every sign vector realised over a cell is
realised at one and the same point of the cell), the number of cells at level `n` is bounded by
`bCellLen n`. -/
theorem CadCells_length_le
    (htc : ∀ (k : ℕ) (H : List (MvPolynomial (Fin (k + 1)) ℝ)) (C : SAd k),
      C ∈ CadCells k (projDataT k H) →
      ∃ x ∈ C.set, ∀ w : Fin H.length → SignType, RealizedOn H C w →
        ∃ t : ℝ, ∀ i, SignType.sign ((spec (H.get i) x).eval t) = w i) :
    ∀ (n : ℕ) (H : List (MvPolynomial (Fin n) ℝ)),
      (CadCells n H).length ≤ (bCellLen n).eval (famDeg H) := by
  intro n
  induction n with
  | zero =>
    intro H
    simp [CadCells, bCellLen]
  | succ k ih =>
    intro H
    have hbound : ∀ C ∈ CadCells k (projDataT k H),
        ((allSign H.length).filterMap fun v =>
          if RealizedOn H C v then some (cell C H v) else none).length
          ≤ branchBound.eval (famDeg H) := by
      intro C hC
      rw [filterMap_ite_some, List.length_map, eval_branchBound]
      exact card_realizedOn_le H C (htc k H C hC)
    have hlen : (CadCells (k + 1) H).length
        = ((CadCells k (projDataT k H)).map fun C =>
            ((allSign H.length).filterMap fun v =>
              if RealizedOn H C v then some (cell C H v) else none).length).sum := by
      rw [CadCells_succ_eq, List.length_flatMap]
    rw [hlen, bCellLen]
    have hstep : ((CadCells k (projDataT k H)).map fun C =>
        ((allSign H.length).filterMap fun v =>
          if RealizedOn H C v then some (cell C H v) else none).length).sum
        ≤ (CadCells k (projDataT k H)).length * branchBound.eval (famDeg H) := by
      calc ((CadCells k (projDataT k H)).map fun C =>
              ((allSign H.length).filterMap fun v =>
                if RealizedOn H C v then some (cell C H v) else none).length).sum
          ≤ ((CadCells k (projDataT k H)).map fun _ => branchBound.eval (famDeg H)).sum :=
            List.sum_le_sum fun C hC => hbound C hC
        _ = (CadCells k (projDataT k H)).length * branchBound.eval (famDeg H) := by
            simp [List.map_const', List.sum_replicate, nsmul_eq_mul]
    refine hstep.trans ?_
    have h1 : (CadCells k (projDataT k H)).length
        ≤ (bCellLen k).eval (projDataTBound.eval (famDeg H)) :=
      (ih (projDataT k H)).trans (polynomial_eval_mono (bCellLen k) (famDeg_projDataT_le_bound H))
    have h2 : (bCellLen k).eval (projDataTBound.eval (famDeg H))
        = ((bCellLen k).comp projDataTBound).eval (famDeg H) :=
      (Polynomial.eval_comp).symm
    rw [h2] at h1
    calc (CadCells k (projDataT k H)).length * branchBound.eval (famDeg H)
        ≤ ((bCellLen k).comp projDataTBound).eval (famDeg H) * branchBound.eval (famDeg H) :=
          Nat.mul_le_mul_right _ h1
      _ = (((bCellLen k).comp projDataTBound) * branchBound).eval (famDeg H) :=
          (Polynomial.eval_mul).symm

/-- The degree of every cell of the level-`n` decomposition is bounded by `bCellDeg n`, and the
number of its basic sets by `bCellBasics n`. -/
theorem CadCells_deg_basics_le :
    ∀ (n : ℕ) (H : List (MvPolynomial (Fin n) ℝ)) (C : SAd n), C ∈ CadCells n H →
      C.deg ≤ (bCellDeg n).eval (famDeg H) ∧
        C.basics.length ≤ (bCellBasics n).eval (famDeg H) := by
  intro n
  induction n with
  | zero =>
    intro H C hC
    rw [mem_CadCells_zero] at hC
    subst hC
    refine ⟨?_, ?_⟩
    · simp [topCell, SAd.deg, BasicD.deg, bCellDeg]
    · simp [topCell, bCellBasics]
  | succ k ih =>
    intro H C hC
    obtain ⟨C₀, hC₀, w, hw, rfl⟩ := (mem_CadCells_succ).mp hC
    obtain ⟨hdeg₀, hbas₀⟩ := ih (projDataT k H) C₀ hC₀
    have hmono := polynomial_eval_mono (bCellDeg k) (famDeg_projDataT_le_bound H)
    have hmono' := polynomial_eval_mono (bCellBasics k) (famDeg_projDataT_le_bound H)
    have hcomp : (bCellDeg k).eval (projDataTBound.eval (famDeg H))
        = ((bCellDeg k).comp projDataTBound).eval (famDeg H) := (Polynomial.eval_comp).symm
    have hcomp' : (bCellBasics k).eval (projDataTBound.eval (famDeg H))
        = ((bCellBasics k).comp projDataTBound).eval (famDeg H) := (Polynomial.eval_comp).symm
    have hdeg1 : (cell C₀ H w).deg ≤ (bCellDeg k).eval (projDataTBound.eval (famDeg H))
        + (bCellBasics k).eval (projDataTBound.eval (famDeg H)) * (2 * famDeg H) :=
      (cell_deg_le C₀ H w).trans
        (add_le_add (hdeg₀.trans hmono)
          (Nat.mul_le_mul_right _ (hbas₀.trans hmono')))
    have hbas1 : (cell C₀ H w).basics.length
        ≤ (bCellBasics k).eval (projDataTBound.eval (famDeg H)) :=
      (le_of_eq (cell_basics_length C₀ H w)).trans (hbas₀.trans hmono')
    refine ⟨?_, ?_⟩
    · refine hdeg1.trans (le_of_eq ?_)
      rw [hcomp, hcomp']
      show Polynomial.eval (famDeg H) ((bCellDeg k).comp projDataTBound) +
            Polynomial.eval (famDeg H) ((bCellBasics k).comp projDataTBound) * (2 * famDeg H) =
          Polynomial.eval (famDeg H)
            ((bCellDeg k).comp projDataTBound +
              (bCellBasics k).comp projDataTBound * (Polynomial.C 2 * Polynomial.X))
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    · refine hbas1.trans (le_of_eq ?_)
      rw [hcomp']
      rfl

end Work.WilE4.CAD
