import Mathlib
import Submission.GeoBridge
import Submission.NormalVectorMatrix
import Submission.ColumnGeom
import Submission.ColumnLaw
import Submission.Commons.Measure.Probability.markov_count_le_sum

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators

noncomputable section

/-!
# Incompressible side of Theorem A: reduction to the random normal

Layer 5, gates (3)+(4).  For a matrix family `B ω + s·J` whose columns are
exchangeable (entries iid Bernoulli(p) plus a constant shift `s`), the
probability of the *incompressible* small-image event
`Ei := {∃ f, sqNorm f = 1 ∧ ¬ compressible(δ,ν) f ∧ actSqFullFn (Bω+s) f ≤ u²}`
is at most `(2/(ν²δ)) · P {|⟨col_last (Mω), Y(Mω)⟩| ≤ 2u√n/ν}` where
`Y(M)` is the measurable unit normal of the first `n−1` columns of `M`.
-/

namespace Submission.IncompReduction

open Classical
attribute [local instance] Classical.propDecidable

open Submission.GeoBridge (E actSqFullFn actSqFullFn_of_matrix emb sqnorm_toEuclideanLin_eq_actSqFull)
open Submission.NormalVectorMatrix (colVec matrixUnitNormal matrixUnitNormal_unit
  matrixUnitNormal_orthogonal_col measurable_colVec measurable_matrixUnitNormal)
open Submission.ColumnGeom (colDist othersSpan abs_inner_le_norm_perp_component colDist_mul_coord_le_normAct)
open Submission.ColumnLaw (colPerm colDist_colPerm measureReal_colPerm_event_eq instMeasurableSpaceMatrix)

/-- The index of the last coordinate of `Fin n` (needs `1 ≤ n`). -/
def lastFin {n : ℕ} (hn : 1 ≤ n) : Fin n := ⟨n - 1, Nat.sub_lt (by omega) (by norm_num)⟩

/-- `shiftMatrix s M := M + s·J` (all entries shifted by `s`). -/
def shiftMatrix {n : ℕ} (s : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  M + Matrix.of (fun _ _ : Fin n => s)

/-- Entry of the shifted matrix. -/
lemma shiftMatrix_apply {n : ℕ} (s : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    shiftMatrix s M i j = M i j + s := by
  simp [shiftMatrix]
  exact Matrix.of_apply (fun _ _ : Fin n => s) i j

/-- Column permutation commutes with the constant shift. -/
lemma colPerm_shift {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (s : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    colPerm σ (shiftMatrix s M) = shiftMatrix s (colPerm σ M) := by
  ext i j
  simp [shiftMatrix, colPerm, Matrix.of_apply]

/-- The transposition that moves column `i` to the last position (and the
former last column to position `i`). -/
def swapLast {n : ℕ} (hn : 1 ≤ n) (i : Fin n) : Equiv (Fin n) (Fin n) :=
  Equiv.swap i (lastFin hn)

lemma swapLast_last {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    swapLast hn i (lastFin hn) = i := by
  simp [swapLast, Equiv.swap_apply_right]

lemma colDist_swapLast {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    colDist (colPerm (swapLast hn i) M) (lastFin hn) = colDist M i := by
  calc
    colDist (colPerm (swapLast hn i) M) (lastFin hn)
        = colDist M (swapLast hn i (lastFin hn)) := by
            exact colDist_colPerm M (swapLast hn i) (lastFin hn)
    _ = colDist M i := by rw [swapLast_last]

/-- The canonical unit normal of the first `n−1` columns of a plain matrix. -/
def nVec {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) : E n :=
  matrixUnitNormal (fun _ : Unit => N) ()

lemma nVec_unit {n : ℕ} (hn : 1 ≤ n) (N : Matrix (Fin n) (Fin n) ℝ) : ‖nVec N‖ = 1 := by
  dsimp [nVec]
  exact matrixUnitNormal_unit hn (fun _ : Unit => N) ()

/-- The canonical unit normal is orthogonal to every one of the first `n−1`
columns. -/
lemma nVec_orthogonal_emb {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (k : Fin (n - 1)) :
    inner ℝ (nVec N) (colVec N (emb k)) = 0 := by
  dsimp [nVec]
  exact matrixUnitNormal_orthogonal_col k (fun _ : Unit => N) ()

/-- The unit normal is orthogonal to the whole span of the first `n−1`
columns. -/
lemma nVec_mem_orthogonal_othersSpan {n : ℕ} (hn : 1 ≤ n) (N : Matrix (Fin n) (Fin n) ℝ) :
    nVec N ∈ (othersSpan N (lastFin hn))ᗮ := by
  let V : Submodule ℝ (E n) := othersSpan N (lastFin hn)
  change nVec N ∈ Vᗮ
  rw [V.mem_orthogonal']
  intro u hu
  have hgen : ∀ s : E n, s ∈ Set.range (fun k : {j : Fin n // j ≠ lastFin hn} =>
        colVec N (k : Fin n)) → inner ℝ (nVec N) s = 0 := by
    rintro s ⟨k, rfl⟩
    have hk_le : (k : Fin n).val < n - 1 := by
      have hne : (k : Fin n).val ≠ n - 1 := by
        intro h
        apply k.property
        apply Fin.ext
        simpa [lastFin] using h
      have hltn : (k : Fin n).val < n := (k : Fin n).isLt
      omega
    let kk : Fin (n - 1) := ⟨(k : Fin n).val, hk_le⟩
    have hemb : emb kk = (k : Fin n) := by
      apply Fin.ext
      simp [kk, emb]
    change inner ℝ (nVec N) (colVec N (k : Fin n)) = 0
    rw [← hemb]
    exact nVec_orthogonal_emb N kk
  refine Submodule.span_induction (s := Set.range (fun k : {j : Fin n // j ≠ lastFin hn} =>
      colVec N (k : Fin n))) (p := fun x hx => inner ℝ (nVec N) x = 0)
    ?mem ?zero ?add ?smul hu
  · intro x hx
    exact hgen x hx
  · simp
  · intro x y hx hy hpx hpy
    rw [inner_add_right]
    rw [hpx, hpy]
    simp
  · intro a x hx hpx
    rw [inner_smul_right]
    rw [hpx]
    simp

/-- The inner product with the canonical normal is at most the distance of the
last column from the span of the others. -/
lemma abs_inner_normal_le_colDist {n : ℕ} (hn : 1 ≤ n) (N : Matrix (Fin n) (Fin n) ℝ) :
    |inner ℝ (colVec N (lastFin hn)) (nVec N)| ≤ colDist N (lastFin hn) := by
  unfold colDist
  exact abs_inner_le_norm_perp_component (othersSpan N (lastFin hn))
    (nVec_unit hn N) (nVec_mem_orthogonal_othersSpan hn N)

/-- Surrogate event for the distance of the last column: inner product with
the canonical normal small. -/
def normalLe {n : ℕ} (hn : 1 ≤ n) (N : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : Prop :=
  |inner ℝ (colVec N (lastFin hn)) (nVec N)| ≤ r

/-- `colDist_last ≤ r` implies the surrogate event. -/
lemma colDist_le_of_normal_le {n : ℕ} (hn : 1 ≤ n) (N : Matrix (Fin n) (Fin n) ℝ) {r : ℝ}
    (h : colDist N (lastFin hn) ≤ r) : normalLe hn N r := by
  exact le_trans (abs_inner_normal_le_colDist hn N) h

/-- The incompressible small-image event at the level of a single matrix. -/
def incEvent {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (δ ν u : ℝ) : Prop :=
  ∃ f : Fin n → ℝ, Commons.LinearAlgebra.Net.sqNorm f = 1 ∧
    ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
    actSqFullFn (fun i j : Fin n => M i j) f ≤ u ^ 2

/-- `¬compressible δν f` and `sqNorm f = 1` give the spread-lemma hypothesis. -/
lemma not_compressible_spread_hyp {n : ℕ} {δ ν : ℝ} {f : Fin n → ℝ}
    (hf1 : Commons.LinearAlgebra.Net.sqNorm f = 1)
    (hnot : ¬ Commons.LinearAlgebra.Net.compressible δ ν f) :
    ∀ z : Fin n → ℝ, Commons.LinearAlgebra.Net.sqNorm (f - z) ≤ ν ^ 2 →
      ¬ (((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) ≤ δ * (n : ℝ)) := by
  intro z hz hδz
  exact hnot ⟨hf1, ⟨z, hz, hδz⟩⟩

/-- On the incompressible event the number of columns whose surrogate (normal
event) holds is at least `⌈(1/2)·ν²·δ·n⌉`. -/
lemma incEvent_count_ge {n : ℕ} (hn2 : 2 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ)
    {δ ν u : ℝ} (hδ0 : 0 < δ) (hν0 : 0 < ν) (hu0 : 0 ≤ u)
    (h : incEvent M δ ν u) :
    Nat.ceil ((1 / 2) * ν ^ 2 * δ * (n : ℝ)) ≤
      (Finset.univ.filter (fun i : Fin n => normalLe (show 1 ≤ n by omega)
          (colPerm (swapLast (show 1 ≤ n by omega) i) M)
            (2 * u * Real.sqrt (n : ℝ) / ν))).card := by
  classical
  let hn1 : 1 ≤ n := by omega
  rcases h with ⟨f, hf1, hnotc, hfimg⟩
  have hnot := not_compressible_spread_hyp hf1 hnotc
  -- ‖M f‖ ≤ u
  have hnrm : ‖M.toEuclideanLin (WithLp.toLp 2 f : E n)‖ ≤ u := by
    have hsq : ‖M.toEuclideanLin (WithLp.toLp 2 f : E n)‖ ^ 2 ≤ u ^ 2 := by
      rw [sqnorm_toEuclideanLin_eq_actSqFull]
      rwa [← actSqFullFn_of_matrix]
    have habs : |‖M.toEuclideanLin (WithLp.toLp 2 f : E n)‖| ≤ |u| := (sq_le_sq.mp hsq)
    have hx0 : 0 ≤ ‖M.toEuclideanLin (WithLp.toLp 2 f : E n)‖ := norm_nonneg _
    rwa [abs_of_nonneg hx0, abs_of_nonneg hu0] at habs
  -- spread
  rcases Commons.LinearAlgebra.Net.incompressible_spread hn1 hδ0 hν0 f hf1 hnot with
    ⟨σ, hσcard, hσcoord⟩
  -- colDist M i ≤ r for i ∈ σ
  have hσcol : ∀ i : Fin n, i ∈ σ → colDist M i ≤ 2 * u * Real.sqrt (n : ℝ) / ν := by
    intro i hi
    have hfge : ν / (2 * Real.sqrt (n : ℝ)) ≤ |f i| := hσcoord i hi
    have hpos1 : 0 < ν / (2 * Real.sqrt (n : ℝ)) := by positivity
    have hfi_pos : 0 < |f i| := lt_of_lt_of_le hpos1 hfge
    have hineq1 : colDist M i ≤ u / |f i| := by
      have hmul := colDist_mul_coord_le_normAct M i f
      exact (le_div_iff₀ hfi_pos).2 (le_trans hmul hnrm)
    have hineq2 : u / |f i| ≤ 2 * u * Real.sqrt (n : ℝ) / ν := by
      have hstep : u / |f i| ≤ u / (ν / (2 * Real.sqrt (n : ℝ))) := by
        exact div_le_div_of_nonneg_left hu0 hpos1 hfge
      have heq : u / (ν / (2 * Real.sqrt (n : ℝ))) =
          2 * u * Real.sqrt (n : ℝ) / ν := by
        field_simp [show ν / (2 * Real.sqrt (n : ℝ)) ≠ 0 by positivity, hν0.ne']
      rw [heq] at hstep
      exact hstep
    exact le_trans hineq1 hineq2
  -- colDist M i ≤ r implies the surrogate event for the permuted matrix
  have hsurr : ∀ i : Fin n, i ∈ σ → normalLe hn1
      (colPerm (swapLast hn1 i) M) (2 * u * Real.sqrt (n : ℝ) / ν) := by
    intro i hi
    have h1 : colDist (colPerm (swapLast hn1 i) M) (lastFin hn1) ≤
        2 * u * Real.sqrt (n : ℝ) / ν := by
      rw [colDist_swapLast]
      exact hσcol i hi
    exact colDist_le_of_normal_le hn1 (colPerm (swapLast hn1 i) M) h1
  -- σ ⊆ counted set
  have hle_card : σ.card ≤ (Finset.univ.filter (fun i : Fin n => normalLe hn1
      (colPerm (swapLast hn1 i) M) (2 * u * Real.sqrt (n : ℝ) / ν))).card := by
    refine Finset.card_le_card ?_
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsurr i hi⟩
  -- σ.card ≥ c₀ ; hence c₀ ≤ count, giving ⌈c₀⌉ ≤ count
  have hc₀ : (1 / 2) * ν ^ 2 * δ * (n : ℝ) ≤ (σ.card : ℝ) := by
    simpa using hσcard
  have hcount_real : (1 / 2) * ν ^ 2 * δ * (n : ℝ) ≤
      ((Finset.univ.filter (fun i : Fin n => normalLe hn1
          (colPerm (swapLast hn1 i) M) (2 * u * Real.sqrt (n : ℝ) / ν))).card : ℝ) := by
    exact le_trans hc₀ (by exact_mod_cast hle_card)
  have hceil : Nat.ceil ((1 / 2) * ν ^ 2 * δ * (n : ℝ)) ≤
      (Finset.univ.filter (fun i : Fin n => normalLe hn1 (colPerm (swapLast hn1 i) M)
          (2 * u * Real.sqrt (n : ℝ) / ν))).card :=
    (Nat.ceil_le (a := (1 / 2) * ν ^ 2 * δ * (n : ℝ))
      (n := (Finset.univ.filter (fun i : Fin n => normalLe hn1 (colPerm (swapLast hn1 i) M)
          (2 * u * Real.sqrt (n : ℝ) / ν))).card)).mpr hcount_real
  simpa using hceil

/-- Positivity of the counting constant `c₀ := (1/2)ν²δn`. -/
lemma count_const_pos {n : ℕ} (hn : 1 ≤ n) {δ ν : ℝ} (hδ0 : 0 < δ) (hν0 : 0 < ν) :
    (0 : ℝ) < (1 / 2) * ν ^ 2 * δ * (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  positivity

/-- The one-over-factor chain: `(1/⌈c₀⌉)·n ≤ 2/(ν²δ)`. -/
lemma ceil_factor_le {n : ℕ} (hn : 1 ≤ n) {δ ν : ℝ} (hδ0 : 0 < δ) (hν0 : 0 < ν) :
    ((1 : ℝ) / (Nat.ceil ((1 / 2) * ν ^ 2 * δ * (n : ℝ)) : ℝ)) * (n : ℝ) ≤
      2 / (ν ^ 2 * δ) := by
  have hcpos : 0 < (1 / 2) * ν ^ 2 * δ * (n : ℝ) := count_const_pos hn hδ0 hν0
  have hc_le_m : (1 / 2) * ν ^ 2 * δ * (n : ℝ) ≤
      (Nat.ceil ((1 / 2) * ν ^ 2 * δ * (n : ℝ)) : ℝ) := by
    exact (Nat.ceil_le).mp (le_rfl)
  have h1 : ((1 : ℝ) / (Nat.ceil ((1 / 2) * ν ^ 2 * δ * (n : ℝ)) : ℝ)) ≤
      1 / ((1 / 2) * ν ^ 2 * δ * (n : ℝ)) := by
    exact one_div_le_one_div_of_le hcpos hc_le_m
  calc
    ((1 : ℝ) / (Nat.ceil ((1 / 2) * ν ^ 2 * δ * (n : ℝ)) : ℝ)) * (n : ℝ)
        ≤ (1 / ((1 / 2) * ν ^ 2 * δ * (n : ℝ))) * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 / (ν ^ 2 * δ) := by
      field_simp [ne_of_gt hcpos, ne_of_gt (mul_pos hν0 hδ0)]

/-- Measurability of the surrogate inner-product function of a matrix. -/
lemma measurable_normalAbs {n : ℕ} (hn : 1 ≤ n) :
    Measurable (fun N : Matrix (Fin n) (Fin n) ℝ =>
      |inner ℝ (colVec N (lastFin hn)) (nVec N)|) := by
  have hcol : Measurable (fun N : Matrix (Fin n) (Fin n) ℝ => colVec N (lastFin hn)) := by
    dsimp [colVec]
    fun_prop
  have hnvec : Measurable (fun N : Matrix (Fin n) (Fin n) ℝ => nVec N) := by
    dsimp [nVec]
    have hA : ∀ i j : Fin n, Measurable (fun N : Matrix (Fin n) (Fin n) ℝ => N i j) := by
      intro i j
      fun_prop
    exact measurable_matrixUnitNormal (fun N : Matrix (Fin n) (Fin n) ℝ => N) hA
  have hinner : Measurable (fun N : Matrix (Fin n) (Fin n) ℝ =>
      inner ℝ (colVec N (lastFin hn)) (nVec N)) := by
    exact (continuous_inner.measurable).comp (Measurable.prodMk hcol hnvec)
  exact hinner.abs

/-- Measurability (set-level) of the surrogate event of a matrix. -/
lemma measurableSet_normalLe {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    MeasurableSet {N : Matrix (Fin n) (Fin n) ℝ | normalLe hn N r} := by
  change MeasurableSet ((fun N : Matrix (Fin n) (Fin n) ℝ =>
    |inner ℝ (colVec N (lastFin hn)) (nVec N)|) ⁻¹' {x : ℝ | x ≤ r})
  exact (measurable_normalAbs hn) (isClosed_Iic.measurableSet)

/-- Measurability of the surrogate inner product for a measurable matrix
family. -/
lemma measurable_normalAbs_family {n : ℕ} (hn : 1 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, Measurable (fun ω => A ω i j)) :
    Measurable (fun ω => |inner ℝ (colVec (A ω) (lastFin hn)) (nVec (A ω))|) := by
  have hcol : Measurable (fun ω => colVec (A ω) (lastFin hn)) :=
    measurable_colVec A hA (lastFin hn)
  have hnv : Measurable (fun ω => nVec (A ω)) := by
    dsimp [nVec]
    exact measurable_matrixUnitNormal A hA
  have hin : Measurable (fun ω => inner ℝ (colVec (A ω) (lastFin hn)) (nVec (A ω))) :=
    (continuous_inner.measurable).comp (Measurable.prodMk hcol hnv)
  exact hin.abs


/-- Entrywise measurability of the shifted family. -/
lemma measurable_shiftMatrix_family {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j)) (s : ℝ) :
    ∀ i j : Fin n, Measurable (fun ω => shiftMatrix s (B ω) i j) := by
  intro i j
  have h : (fun ω => shiftMatrix s (B ω) i j) = fun ω => B ω i j + s := by
    funext ω
    rw [shiftMatrix_apply]
  rw [h]
  exact (hBmeas i j).add measurable_const

/-- Measurability of the shift map on matrices. -/
lemma measurable_shiftMatrix {n : ℕ} (s : ℝ) :
    Measurable (fun X : Matrix (Fin n) (Fin n) ℝ => shiftMatrix s X) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  have hcoord : ∀ i j : Fin n, Measurable (fun X : Matrix (Fin n) (Fin n) ℝ => X i j) := by
    intro i j
    fun_prop
  have h : (fun X : Matrix (Fin n) (Fin n) ℝ => shiftMatrix s X i j) =
      fun X : Matrix (Fin n) (Fin n) ℝ => X i j + s := by
    funext X
    rw [shiftMatrix_apply]
  rw [h]
  exact (hcoord i j).add measurable_const

/-- Column-permuted shifted family is measurable (entries). -/
lemma measurable_colPerm_shift_family {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j)) (s : ℝ)
    (σ : Equiv (Fin n) (Fin n)) :
    ∀ i j : Fin n, Measurable (fun ω => colPerm σ (shiftMatrix s (B ω)) i j) := by
  intro i j
  have h : (fun ω => colPerm σ (shiftMatrix s (B ω)) i j) =
      fun ω => shiftMatrix s (B ω) i (σ j) := by
    funext ω
    rfl
  rw [h]
  exact measurable_shiftMatrix_family B hBmeas s i (σ j)

/-- The law of the shifted Bernoulli family is invariant under column
permutations. -/
lemma map_colPerm_shift_eq_map {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    (s : ℝ) (σ : Equiv (Fin n) (Fin n)) :
    P.map (fun ω => colPerm σ (shiftMatrix s (B ω))) = P.map (fun ω => shiftMatrix s (B ω)) := by
  let T : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ := fun X => shiftMatrix s X
  let M : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => shiftMatrix s (B ω)
  have hTmeas : Measurable T := by
    dsimp [T]
    exact measurable_shiftMatrix s
  have hmeasB : Measurable (fun ω => B ω) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact hBmeas i j
  have hmeasCB : Measurable (fun ω => colPerm σ (B ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact hBmeas i (σ j)
  have hmeasCp : Measurable (fun ω => colPerm σ (M ω)) := by
    -- entries of colPerm σ (shiftMatrix s (Bω)) are measurable
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_colPerm_shift_family B hBmeas s σ i j
  have hmeasM : Measurable (fun ω => M ω) := by
    dsimp [M]
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_shiftMatrix_family B hBmeas s i j
  have hcolPerm_shift_pt : (fun ω => colPerm σ (M ω)) = fun ω => T (colPerm σ (B ω)) := by
    funext ω
    dsimp [M, T]
    rw [colPerm_shift]
  have h1 := Submission.ColumnLaw.map_colPerm_eq_map P B hBmeas hBind hBlaw σ
  change P.map (fun ω => colPerm σ (M ω)) = P.map M
  calc
    P.map (fun ω => colPerm σ (M ω)) = P.map (fun ω => T (colPerm σ (B ω))) := by
      rw [hcolPerm_shift_pt]
    _ = (P.map (fun ω => colPerm σ (B ω))).map T := by
      exact (Measure.map_map hTmeas hmeasCB).symm
    _ = (P.map B).map T := by rw [h1]
    _ = P.map (fun ω => T (B ω)) := by
      exact Measure.map_map hTmeas hmeasB
    _ = P.map M := by
      rfl

/-- Probabilities of measurable matrix events are invariant under column
permutations for the shifted Bernoulli family. -/
theorem measureReal_colPerm_shift_event_eq {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    (s : ℝ) (σ : Equiv (Fin n) (Fin n)) {S : Set (Matrix (Fin n) (Fin n) ℝ)}
    (hS : MeasurableSet S) :
    P.real {ω : Ω | colPerm σ (shiftMatrix s (B ω)) ∈ S} =
      P.real {ω : Ω | shiftMatrix s (B ω) ∈ S} := by
  let M : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => shiftMatrix s (B ω)
  have hmeasCp : Measurable (fun ω => colPerm σ (M ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_colPerm_shift_family B hBmeas s σ i j
  have hmeasM : Measurable (fun ω => M ω) := by
    dsimp [M]
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_shiftMatrix_family B hBmeas s i j
  have hL := map_colPerm_shift_eq_map P B hBmeas hBind hBlaw s σ
  have h1 : P.map M S = P {ω : Ω | M ω ∈ S} := by
    exact Measure.map_apply hmeasM hS
  have h2 : P.map (fun ω => colPerm σ (M ω)) S = P {ω : Ω | colPerm σ (M ω) ∈ S} := by
    exact Measure.map_apply hmeasCp hS
  have hen : P {ω : Ω | colPerm σ (M ω) ∈ S} = P {ω : Ω | M ω ∈ S} := by
    calc
      P {ω : Ω | colPerm σ (M ω) ∈ S} = P.map (fun ω => colPerm σ (M ω)) S := h2.symm
      _ = P.map M S := by rw [hL]
      _ = P {ω : Ω | M ω ∈ S} := h1
  have hreal : P.real {ω : Ω | colPerm σ (M ω) ∈ S} = P.real {ω : Ω | M ω ∈ S} := by
    dsimp [Measure.real]
    rw [hen]
  simpa [M] using hreal

/-- The probability of the incompressible small-image event is at most the
small-ball probability of the last column against the random normal, up to
the factor `(2/(ν²δ))`.  Gate (3)+(4) of the incompressible side. -/
theorem incompressible_bound {n : ℕ} (hn2 : 2 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    (s : ℝ) {δ ν u : ℝ} (hδ0 : 0 < δ) (hν0 : 0 < ν) (hu0 : 0 ≤ u) :
    P.real {ω : Ω | incEvent (shiftMatrix s (B ω)) δ ν u} ≤
      (2 / (ν ^ 2 * δ)) *
        P.real {ω : Ω | normalLe (show 1 ≤ n by omega) (shiftMatrix s (B ω))
            (2 * u * Real.sqrt (n : ℝ) / ν)} := by
  classical
  let hn1 : 1 ≤ n := by omega
  let r : ℝ := 2 * u * Real.sqrt (n : ℝ) / ν
  let m : ℕ := Nat.ceil ((1 / 2) * ν ^ 2 * δ * (n : ℝ))
  let E : Set Ω := {ω : Ω | incEvent (shiftMatrix s (B ω)) δ ν u}
  let C : Ω → ℕ := fun ω => (Finset.univ.filter (fun i : Fin n =>
      normalLe hn1 (colPerm (swapLast hn1 i) (shiftMatrix s (B ω))) r)).card
  -- 1 ≤ m
  have hm1 : 1 ≤ m := by
    dsimp [m]
    have hcpos : 0 < (1 / 2) * ν ^ 2 * δ * (n : ℝ) := count_const_pos hn1 hδ0 hν0
    have hceilpos : 0 < Nat.ceil ((1 / 2) * ν ^ 2 * δ * (n : ℝ)) := Nat.ceil_pos.mpr hcpos
    exact hceilpos
  -- E ⊆ {m ≤ C}
  have hEsub : E ⊆ {ω : Ω | m ≤ C ω} := by
    intro ω hω
    dsimp [E, C, m] at hω ⊢
    -- apply the counting lemma
    have hc := incEvent_count_ge hn2 (shiftMatrix s (B ω)) hδ0 hν0 hu0 hω
    -- hc's normalLe uses (show 1 ≤ n by omega) inside; our filter uses hn1 :
    -- the predicate is propositionally equal
    simpa using hc
  -- per-column events
  let A : Fin n → Set Ω := fun i => {ω : Ω | normalLe hn1
      (colPerm (swapLast hn1 i) (shiftMatrix s (B ω))) r}
  have hAmeas : ∀ i : Fin n, MeasurableSet (A i) := by
    intro i
    dsimp [A]
    let Ap : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => colPerm (swapLast hn1 i) (shiftMatrix s (B ω))
    have hAp : ∀ k j : Fin n, Measurable (fun ω => Ap ω k j) := by
      intro k j
      dsimp [Ap]
      exact measurable_colPerm_shift_family B hBmeas s (swapLast hn1 i) k j
    have hf : Measurable (fun ω => |inner ℝ (colVec (Ap ω) (lastFin hn1)) (nVec (Ap ω))|) :=
      measurable_normalAbs_family hn1 Ap hAp
    have hset : {ω : Ω | normalLe hn1 (Ap ω) r} =
        (fun ω => |inner ℝ (colVec (Ap ω) (lastFin hn1)) (nVec (Ap ω))|) ⁻¹' {x : ℝ | x ≤ r} := by
      ext ω
      rfl
    rw [hset]
    exact hf (isClosed_Iic.measurableSet)
  -- Markov
  have hmark := Commons.Measure.Probability.markov_count_le_sum P A hAmeas (m := m) hm1
  have hCeq : {ω : Ω | m ≤ C ω} = {ω : Ω | m ≤ (Finset.univ.filter (fun i : Fin n => ω ∈ A i)).card} := by
    ext ω
    rfl
  have hmark' : P.real {ω : Ω | m ≤ C ω} ≤ ((1 : ℝ) / (m : ℝ)) * ∑ i : Fin n, P.real (A i) := by
    rw [hCeq]
    exact hmark
  -- per-column probabilities equal the last-column one
  let X : ℝ := P.real {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r}
  have hAsum : (∑ i : Fin n, P.real (A i)) = (n : ℝ) * X := by
    have hAeq : ∀ i : Fin n, P.real (A i) = X := by
      intro i
      dsimp [A, X]
      -- transfer through column permutation
      let S : Set (Matrix (Fin n) (Fin n) ℝ) := {N : Matrix (Fin n) (Fin n) ℝ | normalLe hn1 N r}
      have hSmeas : MeasurableSet S := by
        dsimp [S]
        exact measurableSet_normalLe hn1 r
      have htr := measureReal_colPerm_shift_event_eq P B hBmeas hBind hBlaw s (swapLast hn1 i)
        (S := S) hSmeas
      have hset : {ω : Ω | colPerm (swapLast hn1 i) (shiftMatrix s (B ω)) ∈ S} =
          {ω : Ω | normalLe hn1 (colPerm (swapLast hn1 i) (shiftMatrix s (B ω))) r} := by
        rfl
      have hset2 : {ω : Ω | shiftMatrix s (B ω) ∈ S} =
          {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r} := by
        rfl
      rw [← hset, ← hset2]
      exact htr
    calc
      (∑ i : Fin n, P.real (A i)) = ∑ i : Fin n, X := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hAeq i
      _ = (Fintype.card (Fin n) : ℝ) * X := by
        simp
      _ = (n : ℝ) * X := by
        simp
  -- combine
  have hle1 : P.real E ≤ ((1 : ℝ) / (m : ℝ)) * ∑ i : Fin n, P.real (A i) := by
    exact le_trans (measureReal_mono hEsub (by simpa using (measure_ne_top P _ : P (Set.univ : Set Ω) ≠ ⊤))) hmark'
  -- need P real {m ≤ C} ≠ ⊤ handled by measureReal_mono auto (probability space, C ⊆ univ)
  have hle2 : P.real E ≤ ((1 : ℝ) / (m : ℝ)) * ((n : ℝ) * X) := by
    rw [hAsum] at hle1
    exact hle1
  have hfact : ((1 : ℝ) / (m : ℝ)) * (n : ℝ) ≤ 2 / (ν ^ 2 * δ) := by
    dsimp [m]
    exact ceil_factor_le hn1 hδ0 hν0
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact ENNReal.toReal_nonneg
  have hle3 : P.real E ≤ (2 / (ν ^ 2 * δ)) * X := by
    have hstep : ((1 : ℝ) / (m : ℝ)) * ((n : ℝ) * X) ≤ (2 / (ν ^ 2 * δ)) * X := by
      calc
        ((1 : ℝ) / (m : ℝ)) * ((n : ℝ) * X) = (((1 : ℝ) / (m : ℝ)) * (n : ℝ)) * X := by
          ring
        _ ≤ (2 / (ν ^ 2 * δ)) * X := by
          exact mul_le_mul_of_nonneg_right hfact hX0
    exact le_trans hle2 hstep
  -- unfold E, X (r unfolds too since X := expression in r)
  dsimp [E, X] at hle3
  exact hle3
end Submission.IncompReduction
