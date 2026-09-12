import Mathlib
import Submission.ThresholdMeas
import Submission.BernoulliSmallBall
import Submission.NormalCompress
import Submission.IncompReduction
import Submission.GeoBridge
import Submission.Commons.LinearAlgebra.GramSchmidt.gramSchmidt_congr
import Submission.Commons.Measure.Probability.indepFun_measureReal_le_mul_of_fiber_le

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# The random normal: fibre estimates over threshold sublevel sets

Tikhomirov 2020, proof of Theorem~A.  With `Mω := Bω + s·J`, the random unit
normal `Yω := nVec Mω` is measurable w.r.t.\ the first `n−1` columns, so
`Yω` is independent of the last column of `Mω`.  For a fixed unit function
`y` with `threshold p y L ≤ S`, the small ball of the last-column linear form
`|Σᵢ (Mω i last)·yᵢ| = |Σᵢ (Bω i last + s)·yᵢ|` is at most `L·max(2S, r)`
(see `BernoulliSmallBall`).  Integrating over `Yω` and slicing on the
measurable threshold sublevel sets (`ThresholdMeas`) gives the fibre
inequality

`P{normalLe (shiftMatrix s (Bω)) r ∧ threshold p (yfn ω) L ≤ S}
   ≤ L·max(2S,r) · P{threshold p (yfn ω) L ≤ S}`.

This is the estimate that turns the normal-event probability into the sum
over threshold annuli that the Section-3 net argument and the final assembly
use.  (The conditioning map `A := yfn` is built from a measurable clamped
version of `B`, since the challenge hypotheses are law-only.)
-/

namespace Submission.NormalSplit

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators Topology
open Submission.ThresholdMeas
open Submission.Threshold
open Submission.GeoBridge (E exists_measurable_clamped_matrix measureReal_matrix_event_eq_of_ae emb)
open Submission.IncompReduction (nVec shiftMatrix shiftMatrix_apply lastFin nVec_unit normalLe)
open Submission.NormalVectorMatrix (colVec colVec_coeff matrixUnitNormal firstCols
  measurable_matrixUnitNormal measurable_colVec stdBasis)
open Submission.UnitNormal.GramSchmidtExtension
open Submission.BernoulliSmallBall

/-- Inner product of the last column and the unit normal, as a coordinate sum:
`⟨col_last(M), nVec M⟩ = Σᵢ M i last · (nVec M).ofLp i`. -/
lemma inner_normal_col_last {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ) :
    inner ℝ (colVec M (lastFin hn)) (nVec M)
      = ∑ i : Fin n, M i (lastFin hn) * (nVec M).ofLp i := by
  let Y : E n := nVec M
  have hid : inner ℝ (colVec M (lastFin hn)) Y
      = ∑ i : Fin n, (colVec M (lastFin hn)).ofLp i * Y.ofLp i := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply]
  calc
    inner ℝ (colVec M (lastFin hn)) (nVec M)
        = ∑ i : Fin n, (colVec M (lastFin hn)).ofLp i * Y.ofLp i := hid
    _ = ∑ i : Fin n, M i (lastFin hn) * (nVec M).ofLp i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [colVec_coeff]

/-- `normalLe` of the shifted matrix is equivalent to the small ball of the
shifted-last-column linear form on the normal's coordinate function. -/
lemma normalLe_shift_iff {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ) :
    normalLe hn (shiftMatrix s M) r ↔
      |∑ i : Fin n, (M i (lastFin hn) + s) * ((nVec (shiftMatrix s M)).ofLp i)| ≤ r := by
  unfold normalLe
  rw [inner_normal_col_last hn (shiftMatrix s M)]
  have hsum : (∑ i : Fin n, (shiftMatrix s M) i (lastFin hn) * (nVec (shiftMatrix s M)).ofLp i) =
      (∑ i : Fin n, (M i (lastFin hn) + s) * (nVec (shiftMatrix s M)).ofLp i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [shiftMatrix_apply]
  rw [hsum]


/-- Coordinate function of the unit normal of `shiftMatrix s M`. -/
def yfnOf {n : ℕ} (s : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun j : Fin n => (nVec (shiftMatrix s M)).ofLp j

/-- Random coordinate function of the unit normal of `A ω + sJ`. -/
def yfnMap {n : ℕ} {Ω : Type*} (s : ℝ) (A : Ω → Matrix (Fin n) (Fin n) ℝ) : Ω → (Fin n → ℝ) :=
  fun ω => yfnOf s (A ω)

/-- The last-column map of `A ω` (values of the last column). -/
def lastColMap {n : ℕ} {Ω : Type*} (hn : 1 ≤ n)
    (A : Ω → Matrix (Fin n) (Fin n) ℝ) : Ω → (Fin n → ℝ) :=
  fun ω i => A ω i (lastFin hn)

/-- The unit normal only depends on the first `n−1` columns: two matrices that
agree on those columns have the same normal. -/
lemma nVec_eq_of_same_firstCols {n : ℕ} (hn : 1 ≤ n) (M N : Matrix (Fin n) (Fin n) ℝ)
    (hcol : ∀ k : Fin (n - 1), colVec M (emb k) = colVec N (emb k)) :
    nVec M = nVec N := by
  let cM : Fin (n - 1) → E n := fun k => colVec M (emb k)
  let cN : Fin (n - 1) → E n := fun k => colVec N (emb k)
  have hc : ∀ k : Fin (n - 1), cM k = cN k := by
    intro k
    dsimp [cM, cN]
    exact hcol k
  have hgs : ∀ i : Fin (2 * n - 1),
      gs (E n) (stdBasis n) cM i = gs (E n) (stdBasis n) cN i := by
    intro i
    dsimp [gs]
    -- gramSchmidtNormed over extFam; extFam equal pointwise
    have hext : ∀ a : Fin (2 * n - 1),
        extFam (E n) (stdBasis n) cM a = extFam (E n) (stdBasis n) cN a := by
      intro a
      dsimp [extFam]
      by_cases ha : a.val < n - 1
      · rw [dif_pos ha]
        rw [dif_pos ha]
        exact hc ⟨a.val, ha⟩
      · rw [dif_neg ha]
        rw [dif_neg ha]
    exact Commons.LinearAlgebra.GramSchmidt.gramSchmidt_congr (𝕜 := ℝ) (f := extFam (E n) (stdBasis n) cM)
      (g := extFam (E n) (stdBasis n) cN) hext i
  have hsum : gsSumB (E n) (stdBasis n) cM = gsSumB (E n) (stdBasis n) cN := by
    dsimp [gsSumB]
    apply Finset.sum_congr rfl
    intro j hj
    exact hgs (bpos j)
  have hnorm : ‖gsSumB (E n) (stdBasis n) cM‖ = ‖gsSumB (E n) (stdBasis n) cN‖ := by
    rw [hsum]
  have hcM : nVec M = unitNormal (E n) (stdBasis n) cM := by
    dsimp [nVec, cM, matrixUnitNormal, firstCols]
  have hcN : nVec N = unitNormal (E n) (stdBasis n) cN := by
    dsimp [nVec, cN, matrixUnitNormal, firstCols]
  calc
    nVec M = unitNormal (E n) (stdBasis n) cM := hcM
    _ = unitNormal (E n) (stdBasis n) cN := by
        dsimp [unitNormal]
        rw [hsum]
    _ = nVec N := hcN.symm

/-- The coordinate function of the normal is measurable in the matrix entries
(when the entries are measurable). -/
lemma measurable_yfnMap {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (s : ℝ)
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, Measurable (fun ω => A ω i j)) : Measurable (yfnMap s A) := by
  refine measurable_pi_lambda (yfnMap s A) ?_
  intro j
  dsimp [yfnMap, yfnOf]
  have hF : ∀ i j : Fin n, Measurable (fun ω => shiftMatrix s (A ω) i j) := by
    intro i j
    have hEq : (fun ω => shiftMatrix s (A ω) i j) = (fun ω => A ω i j + s) := by
      funext ω
      rw [shiftMatrix_apply]
    rw [hEq]
    exact (hA i j).add measurable_const
  have hcol : ∀ k : Fin (n - 1), Measurable (fun ω => colVec (shiftMatrix s (A ω)) (emb k)) := by
    intro k
    exact measurable_colVec (fun ω => shiftMatrix s (A ω)) hF (emb k)
  have hm : Measurable (fun ω : Ω => nVec (shiftMatrix s (A ω))) := by
    dsimp [nVec, matrixUnitNormal, firstCols]
    change Measurable (fun ω : Ω => unitNormal (E n) (stdBasis n)
        (fun k : Fin (n - 1) => colVec (shiftMatrix s (A ω)) (emb k)))
    exact measurable_unitNormal (E := E n) (b := stdBasis n) hcol
  exact ((by fun_prop : Measurable (fun v : E n => v.ofLp j)).comp hm)

/-- The last-column map is measurable when the entries are measurable. -/
lemma measurable_lastColMap {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (hn : 1 ≤ n)
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, Measurable (fun ω => A ω i j)) : Measurable (lastColMap hn A) := by
  refine measurable_pi_lambda (lastColMap hn A) ?_
  intro i
  dsimp [lastColMap]
  exact hA i (lastFin hn)

lemma measurableSet_fiberPair {n : ℕ} (s r : ℝ) :
    MeasurableSet {p : (Fin n → ℝ) × (Fin n → ℝ) |
      |∑ i : Fin n, (p.2 i + s) * p.1 i| ≤ r} := by
  have hG : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      |∑ i : Fin n, (p.2 i + s) * p.1 i|) := by fun_prop
  change MeasurableSet ((fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      |∑ i : Fin n, (p.2 i + s) * p.1 i|) ⁻¹' (Set.Iic r))
  exact hG (isClosed_Iic.measurableSet)



/-- `emb k` is never the last index (when `1 ≤ n`). -/
lemma emb_ne_lastFin {n : ℕ} (hn : 1 ≤ n) (k : Fin (n - 1)) : emb k ≠ lastFin hn := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [emb, lastFin] at hval
  omega

/-- Finset of the non-last column index pairs. -/
def SFirstFinset {n : ℕ} (hn : 1 ≤ n) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun x => x.2 ≠ lastFin hn)

/-- Finset of the last column index pairs. -/
def SLastFinset {n : ℕ} (hn : 1 ≤ n) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun x => x.2 = lastFin hn)

/-- A pair with `j ≠ lastFin` belongs to `SFirstFinset`. -/
lemma mem_SFirst {n : ℕ} (hn : 1 ≤ n) (i : Fin n) {j : Fin n} (hj : j ≠ lastFin hn) :
    (i, j) ∈ SFirstFinset hn := by
  rw [SFirstFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hj⟩

/-- A pair with `j = lastFin` belongs to `SLastFinset`. -/
lemma mem_SLast {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    (i, lastFin hn) ∈ SLastFinset hn := by
  rw [SLastFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, rfl⟩

/-- Reconstruct a full matrix from the entries at the non-last columns (the
last column is zeroed). -/
def reconstruct {n : ℕ} (hn : 1 ≤ n)
    (ts : {x : Fin n × Fin n // x ∈ SFirstFinset hn} → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j : Fin n => if hj : j ≠ lastFin hn then ts ⟨(i, j), mem_SFirst hn i hj⟩ else 0)

/-- Coordinate measurability of `reconstruct`. -/
lemma measurable_reconstruct_coord {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (hn : 1 ≤ n)
    (ts : Ω → ({x : Fin n × Fin n // x ∈ SFirstFinset hn} → ℝ)) :
    Measurable ts →
      ∀ i j : Fin n, Measurable (fun ω => reconstruct hn (ts ω) i j) := by
  intro hts i j
  simp only [reconstruct, Matrix.of_apply]
  by_cases hj : j ≠ lastFin hn
  · have hEq : (fun ω => (if h : j ≠ lastFin hn then ts ω ⟨(i, j), mem_SFirst hn i h⟩ else 0)) =
        (fun ω => ts ω ⟨(i, j), mem_SFirst hn i hj⟩) := by
      funext ω
      rw [dif_pos hj]
    rw [hEq]
    exact (measurable_pi_apply (δ := {x : Fin n × Fin n // x ∈ SFirstFinset hn})
      (X := fun _ : {x : Fin n × Fin n // x ∈ SFirstFinset hn} => ℝ)
      (⟨(i, j), mem_SFirst hn i hj⟩)).comp hts
  · have hEq : (fun ω => (if h : j ≠ lastFin hn then ts ω ⟨(i, j), mem_SFirst hn i h⟩ else 0)) =
        (fun ω => (0 : ℝ)) := by
      funext ω
      rw [dif_neg hj]
    rw [hEq]
    exact measurable_const

/-- The map `ts ↦ yfnOf s (reconstruct hn ts)` is measurable. -/
lemma measurable_yfnOf_reconstruct {n : ℕ} (hn : 1 ≤ n) (s : ℝ) :
    Measurable (fun ts : ({x : Fin n × Fin n // x ∈ SFirstFinset hn} → ℝ) =>
      yfnOf s (reconstruct hn ts)) := by
  refine measurable_pi_lambda (fun ts => yfnOf s (reconstruct hn ts)) ?_
  intro j
  have hm1 : Measurable (fun ts => nVec (shiftMatrix s (reconstruct hn ts))) := by
    dsimp [nVec, matrixUnitNormal, firstCols]
    change Measurable (fun ts : ({x : Fin n × Fin n // x ∈ SFirstFinset hn} → ℝ) =>
      unitNormal (E n) (stdBasis n)
        (fun k : Fin (n - 1) => colVec (shiftMatrix s (reconstruct hn ts)) (emb k)))
    have hcol : ∀ k : Fin (n - 1), Measurable (fun ts =>
        colVec (shiftMatrix s (reconstruct hn ts)) (emb k)) := by
      intro k
      exact measurable_colVec (fun ts => shiftMatrix s (reconstruct hn ts))
        (by
          intro i j
          have hEq : (fun ts => shiftMatrix s (reconstruct hn ts) i j) =
              (fun ts => reconstruct hn ts i j + s) := by
            funext ts
            rw [shiftMatrix_apply]
          rw [hEq]
          exact (measurable_reconstruct_coord hn (fun ts => ts) (by fun_prop) i j).add measurable_const)
        (emb k)
    exact measurable_unitNormal (E := E n) (b := stdBasis n) hcol
  exact ((by fun_prop : Measurable (fun v : E n => v.ofLp j)).comp hm1)

/-- Last-column extraction map is a measurable function of the last-column
block tuple. -/
lemma measurable_last_extract {n : ℕ} (hn : 1 ≤ n) :
    Measurable (fun tt : ({x : Fin n × Fin n // x ∈ SLastFinset hn} → ℝ) =>
      fun i : Fin n => tt ⟨(i, lastFin hn), mem_SLast hn i⟩) := by
  refine measurable_pi_lambda (fun (tt : ({x : Fin n × Fin n // x ∈ SLastFinset hn} → ℝ)) =>
      fun i : Fin n => tt ⟨(i, lastFin hn), mem_SLast hn i⟩) ?_
  intro i
  exact measurable_pi_apply (δ := {x : Fin n × Fin n // x ∈ SLastFinset hn})
    (X := fun _ : {x : Fin n × Fin n // x ∈ SLastFinset hn} => ℝ)
    (⟨(i, lastFin hn), mem_SLast hn i⟩)




/-- The normal coordinate function computed from a reconstructed matrix equals
the one computed from any matrix agreeing on the first columns. -/
lemma yfnOf_eq_of_first_cols {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (tup : {x : Fin n × Fin n // x ∈ SFirstFinset hn} → ℝ)
    (htup : ∀ (x : Fin n × Fin n) (hx : x ∈ SFirstFinset hn),
      tup ⟨x, hx⟩ = M x.1 x.2) :
    yfnOf s (reconstruct hn tup) = yfnOf s M := by
  unfold yfnOf
  apply congrArg (fun v : E n => fun j : Fin n => v.ofLp j)
  apply nVec_eq_of_same_firstCols hn (shiftMatrix s (reconstruct hn tup)) (shiftMatrix s M)
  intro k
  have hke : emb k ≠ lastFin hn := emb_ne_lastFin hn k
  unfold colVec
  congr 1
  funext i
  have hrec : reconstruct hn tup i (emb k) = M i (emb k) := by
    simp only [reconstruct, Matrix.of_apply]
    rw [dif_pos hke]
    exact htup (i, emb k) (mem_SFirst hn i hke)
  calc
    shiftMatrix s (reconstruct hn tup) i (emb k) = reconstruct hn tup i (emb k) + s := by
        rw [shiftMatrix_apply]
    _ = M i (emb k) + s := by rw [hrec]
    _ = shiftMatrix s M i (emb k) := by
        rw [shiftMatrix_apply]

/-- The unit-normal coordinate function of a measurable matrix family is
independent of the last column map. -/
lemma indepFun_yfnMap_lastColMap {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (hn : 1 ≤ n)
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] (s : ℝ)
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P) :
    ProbabilityTheory.IndepFun (yfnMap s B) (lastColMap hn B) P := by
  let f : (Fin n × Fin n) → Ω → ℝ := fun x ω => B ω x.1 x.2
  have hfmeas : ∀ x : Fin n × Fin n, Measurable (f x) := by
    intro x
    dsimp [f]
    exact hBmeas x.1 x.2
  have hfBind : ProbabilityTheory.iIndepFun f P := by
    simpa [f] using hBind
  have hdisj : Disjoint (SFirstFinset hn) (SLastFinset hn) := by
    rw [Finset.disjoint_left]
    intro x hxF hxG
    have h1 : x.2 ≠ lastFin hn := (Finset.mem_filter.mp hxF).2
    have h2 : x.2 = lastFin hn := (Finset.mem_filter.mp hxG).2
    exact h1 h2
  have htuples := ProbabilityTheory.iIndepFun.indepFun_finset (SFirstFinset hn) (SLastFinset hn)
    hdisj hfBind hfmeas
  -- φ (measurable) and ψ (measurable)
  let φ : ({x : Fin n × Fin n // x ∈ SFirstFinset hn} → ℝ) → (Fin n → ℝ) :=
    fun ts => yfnOf s (reconstruct hn ts)
  let ψ : ({x : Fin n × Fin n // x ∈ SLastFinset hn} → ℝ) → (Fin n → ℝ) :=
    fun tt => fun i : Fin n => tt ⟨(i, lastFin hn), mem_SLast hn i⟩
  have hφm : Measurable φ := by
    dsimp [φ]
    exact measurable_yfnOf_reconstruct hn s
  have hψm : Measurable ψ := by
    dsimp [ψ]
    exact measurable_last_extract hn
  have hcomp := ProbabilityTheory.IndepFun.comp htuples hφm hψm
  -- hcomp : IndepFun (φ ∘ tupF) (ψ ∘ tupG)
  have hAeq : (fun ω : Ω => φ (fun (i : {x : Fin n × Fin n // x ∈ SFirstFinset hn}) => f i.1 ω)) =
      yfnMap s B := by
    funext ω
    dsimp [φ, yfnMap, yfnOf]
    apply congrArg (fun v : E n => fun j : Fin n => v.ofLp j)
    apply nVec_eq_of_same_firstCols hn
      (shiftMatrix s (reconstruct hn (fun (i : {x : Fin n × Fin n // x ∈ SFirstFinset hn}) => f i.1 ω)))
      (shiftMatrix s (B ω))
    intro k
    unfold colVec
    congr 1
    funext i
    have hke : emb k ≠ lastFin hn := emb_ne_lastFin hn k
    calc
      shiftMatrix s (reconstruct hn (fun (i : {x : Fin n × Fin n // x ∈ SFirstFinset hn}) => f i.1 ω)) i (emb k)
          = reconstruct hn (fun (i : {x : Fin n × Fin n // x ∈ SFirstFinset hn}) => f i.1 ω) i (emb k) + s := by
              rw [shiftMatrix_apply]
      _ = f (i, emb k) ω + s := by
              congr 1
              simp only [reconstruct, Matrix.of_apply]
              rw [dif_pos hke]
      _ = shiftMatrix s (B ω) i (emb k) := by
              dsimp [f]
              rw [shiftMatrix_apply]
  have hBeq : (fun ω : Ω => ψ (fun (i : {x : Fin n × Fin n // x ∈ SLastFinset hn}) => f i.1 ω)) =
      lastColMap hn B := by
    funext ω i
    dsimp [ψ, f, lastColMap]
  rw [← hAeq, ← hBeq]
  exact hcomp

/-- Fibre bound over threshold sublevel sets, for a *measurable* matrix
family: `P{normalLe(Mω) r ∧ threshold(Yω) ≤ S} ≤ L·max(2S,r)·P{threshold(Yω) ≤ S}`. -/
theorem normal_fiber_bound_meas {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] (hn : 1 ≤ n) {p : I}
    (Bc : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => Bc ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (Bc · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (Bc · i j) (bernoulliMeasure 1 0 p) P)
    {s L S r : ℝ} (hL : 1 ≤ L) (hS : 0 < S) (hr : 0 < r) :
    P.real {ω : Ω | normalLe hn (shiftMatrix s (Bc ω)) r ∧
        Submission.Threshold.threshold p (yfnMap s Bc ω) L ≤ S}
      ≤ (L * max (2 * S) r) * P.real {ω : Ω |
        Submission.Threshold.threshold p (yfnMap s Bc ω) L ≤ S} := by
  let A : Ω → (Fin n → ℝ) := yfnMap s Bc
  let Z : Ω → (Fin n → ℝ) := lastColMap hn Bc
  let H : Set (Fin n → ℝ) := {y | Submission.Threshold.threshold p y L ≤ S}
  let Sf : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {pp | |∑ i : Fin n, (pp.2 i + s) * pp.1 i| ≤ r}
  let c : ℝ := L * max (2 * S) r
  have hAmeas : Measurable A := measurable_yfnMap s Bc hBmeas
  have hZmeas : Measurable Z := measurable_lastColMap hn Bc hBmeas
  have hAae : AEMeasurable A P := hAmeas.aemeasurable
  have hZae : AEMeasurable Z P := hZmeas.aemeasurable
  have hind : ProbabilityTheory.IndepFun A Z P := by
    dsimp [A, Z]
    exact indepFun_yfnMap_lastColMap hn P s Bc hBmeas hBind
  have hH : MeasurableSet H := by
    dsimp [H]
    exact measurableSet_threshold_sublevel p hL hS
  have hSf : MeasurableSet Sf := by
    dsimp [Sf]
    exact measurableSet_fiberPair s r
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have hL0 : 0 ≤ L := by linarith
    exact mul_nonneg hL0 (le_trans (le_of_lt hr) (le_max_right (2 * S) r))
  -- independence of the last-column entries and their laws
  have hbXind : ProbabilityTheory.iIndepFun (fun i : Fin n => fun ω : Ω => Bc ω i (lastFin hn)) P := by
    have hg : Function.Injective (fun i : Fin n => (i, lastFin hn)) := by
      intro a b h
      exact congrArg Prod.fst h
    have hpre := ProbabilityTheory.iIndepFun.precomp
      (f := fun x : Fin n × Fin n => (Bc · x.1 x.2))
      (g := fun i : Fin n => (i, lastFin hn)) hg hBind
    simpa using hpre
  have hbXmeas : ∀ i : Fin n, Measurable (fun ω : Ω => Bc ω i (lastFin hn)) := by
    intro i
    exact hBmeas i (lastFin hn)
  have hbXlaw : ∀ i : Fin n, HasLaw (fun ω : Ω => Bc ω i (lastFin hn))
      (bernoulliMeasure 1 0 p) P := by
    intro i
    exact hBlaw i (lastFin hn)
  -- the fibre bound over fixed `a`
  have hbound : ∀ a : Fin n → ℝ, a ∈ H → (P.map Z).real {b : Fin n → ℝ | (a, b) ∈ Sf} ≤ c := by
    intro a ha
    dsimp [H] at ha
    have hbb := bernoulli_vector_smallBall_le_of_threshold P
      (X := fun i : Fin n => fun ω : Ω => Bc ω i (lastFin hn))
      hbXmeas hbXind hbXlaw (y := a) hL hr hS ha (s * ∑ i : Fin n, a i) (0 : ℝ)
    have hEvE : {b : Fin n → ℝ | (a, b) ∈ Sf} =
        {b : Fin n → ℝ | |∑ i : Fin n, (b i + s) * a i| ≤ r} := by
      ext b
      dsimp [Sf]
      rfl
    have hPre : Z ⁻¹' {b : Fin n → ℝ | (a, b) ∈ Sf} =
        {ω : Ω | |∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r} := by
      ext ω
      dsimp [Z]
      rfl
    have hMeasE : MeasurableSet {b : Fin n → ℝ | (a, b) ∈ Sf} := by
      rw [hEvE]
      have hG : Measurable (fun b : Fin n → ℝ => |∑ i : Fin n, (b i + s) * a i|) := by
        fun_prop
      change MeasurableSet ((fun b : Fin n → ℝ => |∑ i : Fin n, (b i + s) * a i|) ⁻¹' (Set.Iic r))
      exact hG (isClosed_Iic.measurableSet)
    have hmap : (P.map Z).real {b : Fin n → ℝ | (a, b) ∈ Sf} =
        P.real {ω : Ω | |∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r} := by
      calc
        (P.map Z).real {b : Fin n → ℝ | (a, b) ∈ Sf}
            = P.real (Z ⁻¹' {b : Fin n → ℝ | (a, b) ∈ Sf}) := by
                rw [Measure.real_def, Measure.real_def]
                rw [Measure.map_apply hZmeas hMeasE]
        _ = P.real {ω : Ω | |∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r} := by
                rw [hPre]
    -- transform the sum: Σ (Bc + s)·a = ΣBc·a + s·Σa
    have hSumEq : {ω : Ω | |∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r} =
        {ω : Ω | |(∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * ∑ i : Fin n, a i| ≤ r} := by
      ext ω
      change (|∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r) ↔
          (|(∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * (∑ i : Fin n, a i)| ≤ r)
      have hs : (∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i) =
          (∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * (∑ i : Fin n, a i) := by
        calc
          (∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i)
              = ∑ i : Fin n, (Bc ω i (lastFin hn) * a i + s * a i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
          _ = (∑ i : Fin n, Bc ω i (lastFin hn) * a i) + ∑ i : Fin n, (s * a i) := by
                  rw [Finset.sum_add_distrib]
          _ = (∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * (∑ i : Fin n, a i) := by
                  rw [Finset.mul_sum]
      rw [hs]
    have hbbr : P.real {ω : Ω | |(∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * ∑ i : Fin n, a i| ≤ r} ≤ c := by
      simpa [c] using hbb
    calc
      (P.map Z).real {b : Fin n → ℝ | (a, b) ∈ Sf}
          = P.real {ω : Ω | |∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r} := hmap
      _ = P.real {ω : Ω | |(∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * ∑ i : Fin n, a i| ≤ r} := by
              rw [hSumEq]
      _ ≤ c := hbbr
  -- apply the real fibre lemma
  have hfib := Commons.Measure.Probability.indepFun_measureReal_le_mul_of_fiber_le P A Z hAae hZae hind
    Sf hSf H hH c hc0 hbound
  -- convert the events to the desired form
  have hEvMain : {ω : Ω | normalLe hn (shiftMatrix s (Bc ω)) r ∧
        Submission.Threshold.threshold p (yfnMap s Bc ω) L ≤ S} =
      {ω : Ω | (A ω, Z ω) ∈ Sf ∧ A ω ∈ H} := by
    ext ω
    dsimp [A, Z, Sf, H]
    rw [normalLe_shift_iff hn s (Bc ω) r]
    rfl
  have hEvH : {ω : Ω | A ω ∈ H} = {ω : Ω | Submission.Threshold.threshold p (yfnMap s Bc ω) L ≤ S} := by
    ext ω
    simp [A, H]
  calc
    P.real {ω : Ω | normalLe hn (shiftMatrix s (Bc ω)) r ∧
        Submission.Threshold.threshold p (yfnMap s Bc ω) L ≤ S}
        = P.real {ω : Ω | (A ω, Z ω) ∈ Sf ∧ A ω ∈ H} := by rw [hEvMain]
    _ ≤ c * P.real {ω : Ω | A ω ∈ H} := hfib
    _ = (L * max (2 * S) r) * P.real {ω : Ω |
          Submission.Threshold.threshold p (yfnMap s Bc ω) L ≤ S} := by
        dsimp [c]
        rw [hEvH]



/-- Fibre bound over threshold sublevel sets (law-only hypotheses, via the
measurable clamped representative): with `Mω := Bω + sJ` and `Yω` the unit
normal of `Mω`,
`P{normalLe Mω at r ∧ threshold(Yω) ≤ S} ≤ L·max(2S,r)·P{threshold(Yω) ≤ S}`. -/
theorem normal_fiber_bound {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] (hn : 1 ≤ n) {p : I}
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    {s L S r : ℝ} (hL : 1 ≤ L) (hS : 0 < S) (hr : 0 < r) :
    P.real {ω : Ω | normalLe hn (shiftMatrix s (B ω)) r ∧
        Submission.Threshold.threshold p (yfnOf s (B ω)) L ≤ S}
      ≤ (L * max (2 * S) r) * P.real {ω : Ω |
        Submission.Threshold.threshold p (yfnOf s (B ω)) L ≤ S} := by
  classical
  rcases exists_measurable_clamped_matrix (P := P) B hBind hBlaw with
    ⟨Bc, hcm, hcind, hclaw, hcpt, hcae⟩
  have hmain := normal_fiber_bound_meas P hn (Bc := Bc) hcm hcind hclaw (s := s) (L := L) (S := S) (r := r) hL hS hr
  let S1 : Set (Matrix (Fin n) (Fin n) ℝ) := {M | normalLe hn (shiftMatrix s M) r ∧
      Submission.Threshold.threshold p (yfnOf s M) L ≤ S}
  let S2 : Set (Matrix (Fin n) (Fin n) ℝ) := {M |
      Submission.Threshold.threshold p (yfnOf s M) L ≤ S}
  have hae' : ∀ i j : Fin n, (fun ω => B ω i j) =ᵐ[P] (fun ω => Bc ω i j) :=
    fun i j => (hcae i j).symm
  have htr1 : P.real {ω : Ω | B ω ∈ S1} = P.real {ω : Ω | Bc ω ∈ S1} :=
    measureReal_matrix_event_eq_of_ae P B Bc hae' S1
  have htr2 : P.real {ω : Ω | B ω ∈ S2} = P.real {ω : Ω | Bc ω ∈ S2} :=
    measureReal_matrix_event_eq_of_ae P B Bc hae' S2
  have hmain' : P.real {ω : Ω | Bc ω ∈ S1} ≤
      (L * max (2 * S) r) * P.real {ω : Ω | Bc ω ∈ S2} := by
    simpa [S1, S2, yfnMap] using hmain
  calc
    P.real {ω : Ω | normalLe hn (shiftMatrix s (B ω)) r ∧
        Submission.Threshold.threshold p (yfnOf s (B ω)) L ≤ S}
        = P.real {ω : Ω | B ω ∈ S1} := by rfl
    _ = P.real {ω : Ω | Bc ω ∈ S1} := htr1
    _ ≤ (L * max (2 * S) r) * P.real {ω : Ω | Bc ω ∈ S2} := hmain'
    _ = (L * max (2 * S) r) * P.real {ω : Ω | B ω ∈ S2} := by rw [htr2]
    _ = (L * max (2 * S) r) * P.real {ω : Ω |
          Submission.Threshold.threshold p (yfnOf s (B ω)) L ≤ S} := by rfl


end Submission.NormalSplit
