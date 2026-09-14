import Mathlib
import Submission.LatticeParam
import Submission.StableCompact
import Submission.VoronoiContinuity
import Submission.Cvp

open Module Real MeasureTheory
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# (P3.1c) coefficient machinery for cell stabilization under basis perturbation

This module contains the analytic core of the P3.1c stabilization lemma
(`cell_mem_stable`, the heart of P3's continuity of `ℒ ↦ γ_{1/t}(V(ℒ))`): given a
full-rank lattice `ℒ₀ = latticeOfMatrix A₀` (i.e. `det A₀ ≠ 0`) and a point `x` off the
tie set of `ℒ₀`, membership of `x` in the Voronoi cell is locally constant along
matrices `A` close to `A₀`.

The engine is a **uniform bounded-coefficient lemma**: lattice points of norm ≤ R have
coefficient vectors (in the columns of `A`) bounded by a constant that is uniform for all
`A` in a neighborhood of `A₀`.  Steps:

* `colsBasis A hdet` — the columns of an invertible matrix form a real basis of `E`
  (`Basis.mk` from `LinearIndependent` (`Matrix.linearIndependent_col_iff`) + `finrank`);
* `coeff_le_of_sum A₀ hdet` — at the fixed matrix: `‖a‖∞ ≤ K₀ · ‖Σ aᵢ • (col A₀ i)‖`
  (from the operator bound of the basis-coordinate equivalence
  `(colsBasis A₀).equivFun`);
* `colSum_diff_le` — `‖colSum A a − colSum A₀ a‖ ≤ (Σᵢ‖col A i − col A₀ i‖)·‖a‖`;
* `delta_uniform_coefficient_bound A₀ hdet R` — ∃δ>0, ∃C, for all `A` whose entries are
  within `δ` of `A₀`'s and all integer coefficient vectors `c`:
  `‖Σᵢ (c i : ℝ) • (col A i)‖ ≤ R` ⟹ `∀ i, |c i| ≤ C`.

Then `cell_mem_stable` transfers membership across the strict (finite) constraints.
-/

noncomputable section
namespace Submission.CellContinuity

open Submission.LatticeParam
open Submission.StableCompact

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "VC" => Submission.Voronoi.voronoi

/-- The linear combination of the columns of `A` with coefficients `a` (an ambient vector). -/
def colSum (A : Matrix (Fin m) (Fin m) ℝ) (a : Fin m → ℝ) : E :=
  ∑ i : Fin m, a i • cols A i

/-- ‖a i‖ ≤ ‖a‖ (functions carry the sup norm). -/
lemma coord_le_sup (a : Fin m → ℝ) (i : Fin m) : |a i| ≤ ‖a‖ := by
  rw [Pi.norm_def]
  exact_mod_cast (Finset.le_sup (f := fun j : Fin m => ‖a j‖₊) (Finset.mem_univ i) :
    ‖a i‖₊ ≤ Finset.univ.sup (fun j => ‖a j‖₊))

/-- The columns of a matrix of nonzero determinant are linearly independent. -/
lemma cols_linearIndependent (A : Matrix (Fin m) (Fin m) ℝ) (hdet : A.det ≠ 0) :
    LinearIndependent ℝ (cols A) := by
  classical
  have hli : LinearIndependent ℝ A.col := by
    exact (Matrix.linearIndependent_col_iff.mpr (Matrix.nonsingular_iff_det_ne_zero.mpr hdet))
  let φ : (Fin m → ℝ) →ₗ[ℝ] E := (coordEquiv (m := m)).symm.toLinearMap
  have hker : φ.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (coordEquiv (m := m)).symm.injective
  have hmap : LinearIndependent ℝ (fun i : Fin m => φ (A.col i)) := by
    simpa [Function.comp_def] using (LinearIndependent.map' (R := ℝ) hli φ hker)
  have hpt : ∀ i : Fin m, φ (A.col i) = cols A i := by
    intro i
    ext j
    dsimp [φ, coordEquiv, cols]
    simp
  have hfam : (fun i : Fin m => φ (A.col i)) = cols A := funext hpt
  exact hfam ▸ hmap

/-- The columns of a matrix of nonzero determinant span `E`. -/
lemma cols_span_top (A : Matrix (Fin m) (Fin m) ℝ) (hli : LinearIndependent ℝ (cols A)) :
    Submodule.span ℝ (Set.range (cols A)) = ⊤ := by
  classical
  have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range (cols A))) = m := by
    rw [finrank_span_eq_card hli]
    simp
  have hE : Module.finrank ℝ E = m := by simp
  exact Submodule.eq_top_of_finrank_eq (S := Submodule.span ℝ (Set.range (cols A))) (by rw [hfr, hE])

/-- The real basis of `E` whose elements are the columns of `A` (`det A ≠ 0`). -/
def colsBasis (A : Matrix (Fin m) (Fin m) ℝ) (hdet : A.det ≠ 0) :
    Module.Basis (Fin m) ℝ E :=
  Module.Basis.mk (cols_linearIndependent A hdet)
    (by rw [cols_span_top A (cols_linearIndependent A hdet)])

/-- `colsBasis` evaluates at the columns of `A`. -/
lemma colsBasis_apply (A : Matrix (Fin m) (Fin m) ℝ) (hdet : A.det ≠ 0) (i : Fin m) :
    colsBasis A hdet i = cols A i := by
  dsimp [colsBasis]
  rw [Module.Basis.coe_mk]

/-- `colSum A a` reconstructs the vector with coordinate coefficients `a` in the column
basis: `colSum A a = (colsBasis A hdet).equivFun.symm a`. -/
lemma colSum_eq_equivFun_symm {A : Matrix (Fin m) (Fin m) ℝ} (hdet : A.det ≠ 0) (a : Fin m → ℝ) :
    colSum A a = (colsBasis A hdet).equivFun.symm a := by
  dsimp [colSum]
  rw [Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [colsBasis_apply A hdet i]

/-- **Fixed-matrix coefficient bound.**  At an invertible matrix `A₀` there is `K₀ > 0`
with `‖a‖ ≤ K₀·‖colSum A₀ a‖` for all coefficient functions `a` (the coordinate map of the
column basis is a bounded linear operator). -/
lemma coeff_le_of_sum (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ a : Fin m → ℝ, ‖a‖ ≤ K₀ * ‖colSum A₀ a‖ := by
  classical
  let b : Module.Basis (Fin m) ℝ E := colsBasis A₀ hdet
  let e : E ≃ₗ[ℝ] (Fin m → ℝ) := b.equivFun
  let ec : E ≃L[ℝ] (Fin m → ℝ) := e.toContinuousLinearEquiv
  rcases (ec : E →L[ℝ] (Fin m → ℝ)).bound with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro a
  have hE : ec (colSum A₀ a) = a := by
    rw [colSum_eq_equivFun_symm (m := m) hdet a]
    change e (b.equivFun.symm a) = a
    exact LinearEquiv.apply_symm_apply e a
  calc
    ‖a‖ = ‖ec (colSum A₀ a)‖ := by rw [hE]
    _ ≤ C * ‖colSum A₀ a‖ := hC (colSum A₀ a)

/-- The (Euclidean) norm of `colSum A a` is bounded by the sup-norm of `a` times the sum
of the column norms. -/
lemma colSum_norm_le (A : Matrix (Fin m) (Fin m) ℝ) (a : Fin m → ℝ) :
    ‖colSum A a‖ ≤ (∑ i : Fin m, ‖cols A i‖) * ‖a‖ := by
  calc
    ‖colSum A a‖ ≤ ∑ i : Fin m, ‖a i • cols A i‖ := by
      dsimp [colSum]
      exact norm_sum_le _ _
    _ ≤ ∑ i : Fin m, (‖a‖ * ‖cols A i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖a i • cols A i‖ = |a i| * ‖cols A i‖ := norm_smul _ _
        _ ≤ ‖a‖ * ‖cols A i‖ := mul_le_mul_of_nonneg_right (coord_le_sup a i) (norm_nonneg _)
    _ = (∑ i : Fin m, ‖cols A i‖) * ‖a‖ := by rw [Finset.sum_mul]; ring

/-- Columns are additive. -/
lemma cols_sub (A A₀ : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    cols (A - A₀) i = cols A i - cols A₀ i := by
  ext j
  simp [cols]

/-- `colSum` is additive in the matrix. -/
lemma colSum_sub (A A₀ : Matrix (Fin m) (Fin m) ℝ) (a : Fin m → ℝ) :
    colSum A a - colSum A₀ a = colSum (A - A₀) a := by
  dsimp [colSum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cols_sub A A₀ i]
  rw [smul_sub]

/-- **Perturbation bound.**  `‖colSum A a − colSum A₀ a‖ ≤ (Σᵢ‖col A i − col A₀ i‖)·‖a‖`. -/
lemma colSum_diff_le (A A₀ : Matrix (Fin m) (Fin m) ℝ) (a : Fin m → ℝ) :
    ‖colSum A a - colSum A₀ a‖ ≤ (∑ i : Fin m, ‖cols A i - cols A₀ i‖) * ‖a‖ := by
  rw [colSum_sub]
  have hsum : (∑ i : Fin m, ‖cols (A - A₀) i‖) = (∑ i : Fin m, ‖cols A i - cols A₀ i‖) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [cols_sub A A₀ i]
  calc
    ‖colSum (A - A₀) a‖ ≤ (∑ i : Fin m, ‖cols (A - A₀) i‖) * ‖a‖ := colSum_norm_le (A - A₀) a
    _ = (∑ i : Fin m, ‖cols A i - cols A₀ i‖) * ‖a‖ := by rw [hsum]

/-- The Euclidean norm is at most the `ℓ¹` norm of the coordinates. -/
lemma norm_le_sum_abs {v : E} : ‖v‖ ≤ ∑ j : Fin m, |v j| := by
  have hsq : ‖v‖ ^ 2 ≤ (∑ j : Fin m, |v j|) ^ 2 := by
    have h1 : ‖v‖ ^ 2 = ∑ j : Fin m, (v j) ^ 2 := by
      simp [PiLp.norm_sq_eq_of_L2]
    rw [h1]
    calc
      (∑ j : Fin m, (v j) ^ 2) = ∑ j : Fin m, |v j| ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [sq_abs]
      _ ≤ (∑ j : Fin m, |v j|) ^ 2 := by
        exact Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
          (f := fun j : Fin m => |v j|) (by intro j hj; exact abs_nonneg _)
  have hnn1 : 0 ≤ ‖v‖ := norm_nonneg v
  have hnn2 : 0 ≤ ∑ j : Fin m, |v j| := Finset.sum_nonneg (fun j hj => abs_nonneg _)
  nlinarith [sq_le_sq.mp hsq]

/-- **Uniform bounded-coefficient lemma.**  Given `det A₀ ≠ 0` and `0 ≤ R`, there is a
`δ > 0` and a bound `C` such that every lattice point of `latticeOfMatrix A` inside the
ball of radius `R` has integer coefficients (in the columns of `A`) bounded by `C`,
uniformly over all `A` whose entries are within `δ` of `A₀`. -/
lemma delta_uniform_coefficient_bound (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℕ, ∀ A : Matrix (Fin m) (Fin m) ℝ,
      (∀ j i : Fin m, |A j i - A₀ j i| < δ) →
      ∀ c : Fin m → ℤ, ‖colSum A (fun i => (c i : ℝ))‖ ≤ R →
        ∀ i : Fin m, Int.natAbs (c i) ≤ C := by
  classical
  rcases coeff_le_of_sum (m := m) A₀ hdet with ⟨K₀, hK₀pos, hK₀⟩
  let δ : ℝ := 1 / (4 * K₀ * (((m : ℝ) ^ 2) + 1))
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδpos, ?_⟩
  -- C := the ceiling of 2·K₀·R
  refine ⟨Nat.ceil (2 * K₀ * R), ?_⟩
  intro A hclose c hc i
  have hK₀_nonneg : 0 ≤ K₀ := le_of_lt hK₀pos
  have hcoeffA : ∀ a : Fin m → ℝ, ‖a‖ ≤ 2 * K₀ * ‖colSum A a‖ := by
    intro a
    have h1 : ‖a‖ ≤ K₀ * ‖colSum A₀ a‖ := hK₀ a
    have h2 : ‖colSum A₀ a‖ ≤ ‖colSum A a‖ + ‖colSum A a - colSum A₀ a‖ :=
      norm_le_norm_add_norm_sub (colSum A a) (colSum A₀ a)
    let eps : ℝ := ∑ i : Fin m, ‖cols A i - cols A₀ i‖
    let D : ℝ := K₀ * eps
    have h3 : ‖colSum A a - colSum A₀ a‖ ≤ eps * ‖a‖ := by
      dsimp [eps]
      exact colSum_diff_le A A₀ a
    have hε : eps ≤ ((m : ℝ) ^ 2) * δ := by
      have hper (i : Fin m) : ‖cols A i - cols A₀ i‖ ≤ (m : ℝ) * δ := by
        calc
          ‖cols A i - cols A₀ i‖ ≤ ∑ j : Fin m, |(cols A i - cols A₀ i) j| := norm_le_sum_abs
          _ = ∑ j : Fin m, |A j i - A₀ j i| := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
          _ ≤ ∑ j : Fin m, δ := by
            apply Finset.sum_le_sum
            intro j hj
            exact le_of_lt (hclose j i)
          _ = (m : ℝ) * δ := by simp
      calc
        eps = ∑ i : Fin m, ‖cols A i - cols A₀ i‖ := rfl
        _ ≤ ∑ i : Fin m, (m : ℝ) * δ := by
          exact Finset.sum_le_sum (fun i hi => hper i)
        _ = ((m : ℝ) ^ 2) * δ := by
          simp [pow_two]
          ring
    have hD : D ≤ 1 / 2 := by
      have hfrac : K₀ * (((m : ℝ) ^ 2) * δ) ≤ 1 / 2 := by
        have hδeq : K₀ * (((m : ℝ) ^ 2) * δ) = ((m : ℝ) ^ 2) / (4 * (((m : ℝ) ^ 2) + 1)) := by
          dsimp [δ]
          field_simp [hK₀pos.ne']
        rw [hδeq]
        have hden : 0 < 4 * (((m : ℝ) ^ 2) + 1) := by positivity
        rw [div_le_iff₀ hden]
        nlinarith [sq_nonneg (m : ℝ)]
      have hεK : K₀ * eps ≤ K₀ * (((m : ℝ) ^ 2) * δ) :=
        mul_le_mul_of_nonneg_left hε hK₀_nonneg
      dsimp [D]
      exact le_trans hεK hfrac
    have h2' : K₀ * ‖colSum A₀ a‖ ≤ K₀ * (‖colSum A a‖ + ‖colSum A a - colSum A₀ a‖) :=
      mul_le_mul_of_nonneg_left h2 hK₀_nonneg
    have h2'' : K₀ * (‖colSum A a‖ + ‖colSum A a - colSum A₀ a‖) =
        K₀ * ‖colSum A a‖ + K₀ * ‖colSum A a - colSum A₀ a‖ := by ring
    have h3' : K₀ * ‖colSum A a - colSum A₀ a‖ ≤ K₀ * (eps * ‖a‖) :=
      mul_le_mul_of_nonneg_left h3 hK₀_nonneg
    have h3'' : K₀ * (eps * ‖a‖) = D * ‖a‖ := by
      dsimp [D]
      ring
    have hs1 : ‖a‖ ≤ K₀ * ‖colSum A a‖ + K₀ * ‖colSum A a - colSum A₀ a‖ := by
      calc
        ‖a‖ ≤ K₀ * ‖colSum A₀ a‖ := h1
        _ ≤ K₀ * (‖colSum A a‖ + ‖colSum A a - colSum A₀ a‖) := h2'
        _ = K₀ * ‖colSum A a‖ + K₀ * ‖colSum A a - colSum A₀ a‖ := h2''
    have h3m : K₀ * ‖colSum A a - colSum A₀ a‖ ≤ D * ‖a‖ := by
      rw [← h3'']
      exact h3'
    have hs2 : K₀ * ‖colSum A a‖ + K₀ * ‖colSum A a - colSum A₀ a‖ ≤
        K₀ * ‖colSum A a‖ + D * ‖a‖ := by nlinarith
    have hmain : ‖a‖ ≤ K₀ * ‖colSum A a‖ + D * ‖a‖ := le_trans hs1 hs2
    have hlin : ‖a‖ ≤ K₀ * ‖colSum A a‖ + (1 / 2) * ‖a‖ := by
      have hm := mul_le_mul_of_nonneg_right hD (norm_nonneg a)
      nlinarith
    have hfin : ‖a‖ ≤ 2 * K₀ * ‖colSum A a‖ := by nlinarith
    exact hfin
  -- step 2: instantiate at a := (c : ℝ) and use ‖colSum A c‖ ≤ R
  let a : Fin m → ℝ := fun i => (c i : ℝ)
  have hb : ‖a‖ ≤ 2 * K₀ * R := by
    calc
      ‖a‖ ≤ 2 * K₀ * ‖colSum A a‖ := hcoeffA a
      _ ≤ 2 * K₀ * R := by
        exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hci : |(c i : ℝ)| ≤ (Nat.ceil (2 * K₀ * R) : ℝ) := by
    calc
      |(c i : ℝ)| = |a i| := rfl
      _ ≤ ‖a‖ := coord_le_sup a i
      _ ≤ 2 * K₀ * R := hb
      _ ≤ (Nat.ceil (2 * K₀ * R) : ℝ) := by exact Nat.le_ceil _
  have hident : |(c i : ℝ)| = (Int.natAbs (c i) : ℝ) := by
    rw [← Int.cast_abs]
    congr 1
    rw [Int.abs_eq_natAbs]
  have hz : Int.natAbs (c i) ≤ Nat.ceil (2 * K₀ * R) := by
    have hci' : ((Int.natAbs (c i) : ℕ) : ℝ) ≤ (Nat.ceil (2 * K₀ * R) : ℝ) := by
      rw [hident] at hci
      exact hci
    exact_mod_cast hci'
  exact hz

lemma colSum_eq_zsmul (A : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℤ) :
    colSum A (fun i => (c i : ℝ)) = ∑ i : Fin m, (c i : ℤ) • cols A i := by
  dsimp [colSum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact Int.cast_smul_eq_zsmul (R := ℝ) (c i) (cols A i)

lemma mem_span_cols_iff (A : Matrix (Fin m) (Fin m) ℝ) (z : E) :
    z ∈ (latticeOfMatrix A : Set E) ↔
      ∃ c : Fin m → ℤ, colSum A (fun i => (c i : ℝ)) = z := by
  constructor
  · intro hz
    change z ∈ (Submodule.span ℤ (Set.range (cols A)) : Set E) at hz
    rcases (Submodule.mem_span_range_iff_exists_fun ℤ).mp hz with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc
      colSum A (fun i => (c i : ℝ)) = ∑ i : Fin m, (c i : ℤ) • cols A i := colSum_eq_zsmul A c
      _ = z := hc
  · rintro ⟨c, hc⟩
    have hmem : (∑ i : Fin m, (c i : ℤ) • cols A i) ∈ (Submodule.span ℤ (Set.range (cols A)) : Set E) := by
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem (p := Submodule.span ℤ (Set.range (cols A))) (r := (c i : ℤ))
      apply Submodule.subset_span (s := Set.range (cols A))
      exact Set.mem_range_self i
    have hz : z = ∑ i : Fin m, (c i : ℤ) • cols A i := by
      calc
        z = colSum A (fun i => (c i : ℝ)) := hc.symm
        _ = ∑ i : Fin m, (c i : ℤ) • cols A i := colSum_eq_zsmul A c
    rw [hz]
    exact hmem

lemma mem_cell_coeff (A : Matrix (Fin m) (Fin m) ℝ) (x : E) :
    x ∈ VC (latticeOfMatrix A) ↔
      ∀ c : Fin m → ℤ,
        inner ℝ x (colSum A (fun i => (c i : ℝ))) ≤ ‖colSum A (fun i => (c i : ℝ))‖ ^ 2 / 2 := by
  constructor
  · intro hxV c
    have hy : colSum A (fun i => (c i : ℝ)) ∈ (latticeOfMatrix A : Set E) :=
      (mem_span_cols_iff A _).mpr ⟨c, rfl⟩
    exact (Submission.Voronoi.mem_voronoi.mp hxV) ⟨colSum A (fun i => (c i : ℝ)), hy⟩
  · intro hc y
    have hyc : (y : E) ∈ (latticeOfMatrix A : Set E) := y.2
    rcases (mem_span_cols_iff A (y : E)).mp hyc with ⟨c, hcy⟩
    have h := hc c
    rw [hcy] at h
    exact h

/-- φ_c(A) := the excess of the constraint: member iff φ ≤ 0. -/
def phi (x : E) (A : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℤ) : ℝ :=
  inner ℝ x (colSum A (fun i => (c i : ℝ))) - ‖colSum A (fun i => (c i : ℝ))‖ ^ 2 / 2

-- the box predicate
def box (A₀ A : Matrix (Fin m) (Fin m) ℝ) (δ : ℝ) : Prop :=
  ∀ j i : Fin m, |A j i - A₀ j i| < δ

-- helpers (norm estimates)
lemma abs_inner_sub (x y y₀ : E) : |inner ℝ x y - inner ℝ x y₀| ≤ ‖x‖ * ‖y - y₀‖ := by
  rw [← inner_sub_right x y y₀]
  exact abs_real_inner_le_norm x (y - y₀)

lemma abs_norm_sq_sub (y y₀ : E) : |‖y‖ ^ 2 - ‖y₀‖ ^ 2| ≤ ‖y - y₀‖ * (‖y‖ + ‖y₀‖) := by
  have hring : ‖y‖ ^ 2 - ‖y₀‖ ^ 2 = (‖y‖ - ‖y₀‖) * (‖y‖ + ‖y₀‖) := by ring
  rw [hring]
  rw [abs_mul]
  have habs : |‖y‖ + ‖y₀‖| = ‖y‖ + ‖y₀‖ := abs_of_nonneg (by positivity)
  rw [habs]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le y y₀) (by positivity)

lemma colSum_box_diff_le (A A₀ : Matrix (Fin m) (Fin m) ℝ) (δ : ℝ)
    (hbox : ∀ j i : Fin m, |A j i - A₀ j i| < δ) (a : Fin m → ℝ) :
    ‖colSum A a - colSum A₀ a‖ ≤ ((m : ℝ) ^ 2) * δ * ‖a‖ := by
  have hper (i : Fin m) : ‖cols A i - cols A₀ i‖ ≤ (m : ℝ) * δ := by
    calc
      ‖cols A i - cols A₀ i‖ ≤ ∑ j : Fin m, |(cols A i - cols A₀ i) j| := norm_le_sum_abs
      _ = ∑ j : Fin m, |A j i - A₀ j i| := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
      _ ≤ ∑ j : Fin m, δ := by
        apply Finset.sum_le_sum
        intro j hj
        exact le_of_lt (hbox j i)
      _ = (m : ℝ) * δ := by simp
  calc
    ‖colSum A a - colSum A₀ a‖ ≤ (∑ i : Fin m, ‖cols A i - cols A₀ i‖) * ‖a‖ := colSum_diff_le A A₀ a
    _ ≤ (∑ i : Fin m, ((m : ℝ) * δ)) * ‖a‖ := by
      exact mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun i hi => hper i)) (norm_nonneg a)
    _ = ((m : ℝ) ^ 2) * δ * ‖a‖ := by
      congr 1
      rw [Finset.sum_const, Finset.card_fin]
      simp [nsmul_eq_mul]
      ring

-- two-sided continuity estimate
lemma phi_sub_abs_le (x : E) (c : Fin m → ℤ) (A A₀ : Matrix (Fin m) (Fin m) ℝ) :
    |phi x A c - phi x A₀ c| ≤
      (‖x‖ + (‖colSum A (fun i => (c i : ℝ))‖ + ‖colSum A₀ (fun i => (c i : ℝ))‖) / 2)
        * ‖colSum A (fun i => (c i : ℝ)) - colSum A₀ (fun i => (c i : ℝ))‖ := by
  let y : E := colSum A (fun i => (c i : ℝ))
  let y0 : E := colSum A₀ (fun i => (c i : ℝ))
  have h1 : |inner ℝ x y - inner ℝ x y0| ≤ ‖x‖ * ‖y - y0‖ := abs_inner_sub x y y0
  have hsq : |‖y‖ ^ 2 - ‖y0‖ ^ 2| ≤ ‖y - y0‖ * (‖y‖ + ‖y0‖) := abs_norm_sq_sub y y0
  have htri : |(inner ℝ x y - inner ℝ x y0) - (‖y‖ ^ 2 / 2 - ‖y0‖ ^ 2 / 2)| ≤
      |inner ℝ x y - inner ℝ x y0| + |‖y‖ ^ 2 / 2 - ‖y0‖ ^ 2 / 2| := by
    have h := abs_add_le (inner ℝ x y - inner ℝ x y0) (-(‖y‖ ^ 2 / 2 - ‖y0‖ ^ 2 / 2))
    rw [abs_neg] at h
    exact h
  have habs : |‖y‖ ^ 2 / 2 - ‖y0‖ ^ 2 / 2| = |‖y‖ ^ 2 - ‖y0‖ ^ 2| / 2 := by
    have hdiv : ‖y‖ ^ 2 / 2 - ‖y0‖ ^ 2 / 2 = (‖y‖ ^ 2 - ‖y0‖ ^ 2) / 2 := by ring
    rw [hdiv]
    rw [abs_div]
    norm_num
  have hmain : |(inner ℝ x y - ‖y‖ ^ 2 / 2) - (inner ℝ x y0 - ‖y0‖ ^ 2 / 2)| ≤
      ‖x‖ * ‖y - y0‖ + ‖y - y0‖ * (‖y‖ + ‖y0‖) / 2 := by
    calc
      |(inner ℝ x y - ‖y‖ ^ 2 / 2) - (inner ℝ x y0 - ‖y0‖ ^ 2 / 2)|
          = |(inner ℝ x y - inner ℝ x y0) - (‖y‖ ^ 2 / 2 - ‖y0‖ ^ 2 / 2)| := by
              congr 1
              ring
      _ ≤ |inner ℝ x y - inner ℝ x y0| + |‖y‖ ^ 2 / 2 - ‖y0‖ ^ 2 / 2| := htri
      _ = |inner ℝ x y - inner ℝ x y0| + |‖y‖ ^ 2 - ‖y0‖ ^ 2| / 2 := by rw [habs]
      _ ≤ ‖x‖ * ‖y - y0‖ + ‖y - y0‖ * (‖y‖ + ‖y0‖) / 2 := by
        exact add_le_add h1 (div_le_div_of_nonneg_right hsq (by norm_num))
  dsimp [phi] at hmain ⊢
  dsimp [y, y0] at hmain ⊢
  nlinarith [hmain]

-- boxed single-constraint continuity
lemma phi_abs_cont (x : E) (c : Fin m → ℤ) (A₀ : Matrix (Fin m) (Fin m) ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin m) (Fin m) ℝ,
      box A₀ A δ → |phi x A c - phi x A₀ c| < ε := by
  classical
  intro ε hε
  let a : Fin m → ℝ := fun i => (c i : ℝ)
  let y0 : E := colSum A₀ a
  let m2 : ℝ := (m : ℝ) ^ 2
  let M : ℝ := ‖y0‖ + m2 * ‖a‖
  let L : ℝ := ‖x‖ + M
  let K : ℝ := L * m2 * (‖a‖ + 1)
  let δ : ℝ := min 1 (ε / (2 * (K + 1)))
  have hMnn : 0 ≤ M := by
    dsimp [M, m2]
    have h1 : 0 ≤ ‖y0‖ := norm_nonneg y0
    have h2 : 0 ≤ ((m : ℝ) ^ 2) * ‖a‖ := mul_nonneg (sq_nonneg _) (norm_nonneg _)
    nlinarith
  have hKnn : 0 ≤ K := by
    dsimp [K, L]
    have hNa1 : 0 ≤ ‖a‖ + 1 := by positivity
    exact mul_nonneg (mul_nonneg (add_nonneg (norm_nonneg x) hMnn) (sq_nonneg (m:ℝ))) hNa1
  have hden : 0 < 2 * (K + 1) := by nlinarith [hKnn]
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hε hden)
  refine ⟨δ, hδpos, ?_⟩
  intro A hbox
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  have hδle1 : δ ≤ 1 := min_le_left _ _
  have hδleK : δ ≤ ε / (2 * (K + 1)) := min_le_right _ _
  have hm2nn : 0 ≤ m2 := by dsimp [m2]; exact sq_nonneg (m : ℝ)
  have hD : ‖colSum A a - y0‖ ≤ m2 * δ * ‖a‖ := by
    dsimp [y0]
    exact colSum_box_diff_le A A₀ δ hbox a
  have hnorm : ‖colSum A a‖ ≤ ‖y0‖ + ‖colSum A a - y0‖ := by
    have hx : colSum A a = y0 + (colSum A a - y0) := by
      dsimp [y0]
      abel
    calc
      ‖colSum A a‖ = ‖y0 + (colSum A a - y0)‖ := by
        conv_lhs => rw [hx]
      _ ≤ ‖y0‖ + ‖colSum A a - y0‖ := norm_add_le y0 (colSum A a - y0)
  have hDnn : 0 ≤ ‖colSum A a - y0‖ := norm_nonneg _
  have hyM : ‖colSum A a‖ ≤ M := by
    dsimp [M, m2]
    calc
      ‖colSum A a‖ ≤ ‖y0‖ + ‖colSum A a - y0‖ := hnorm
      _ ≤ ‖y0‖ + m2 * δ * ‖a‖ := by
        exact add_le_add_right hD ‖y0‖
      _ ≤ ‖y0‖ + m2 * ‖a‖ := by
        -- m2·δ·‖a‖ ≤ m2·‖a‖
        have hδm : m2 * δ ≤ m2 := by
          calc
            m2 * δ ≤ m2 * 1 := mul_le_mul_of_nonneg_left hδle1 hm2nn
            _ = m2 := by ring
        have hδmnn : 0 ≤ m2 * δ := mul_nonneg hm2nn hδnn
        calc
          ‖y0‖ + m2 * δ * ‖a‖ ≤ ‖y0‖ + m2 * ‖a‖ := by
            have h1 : m2 * δ * ‖a‖ ≤ m2 * ‖a‖ := mul_le_mul_of_nonneg_right hδm (norm_nonneg a)
            nlinarith
          _ = ‖y0‖ + m2 * ‖a‖ := rfl
      _ = ‖y0‖ + m2 * ‖a‖ := rfl
  have hηM : ‖y0‖ ≤ M := by
    dsimp [M, m2]
    have h : 0 ≤ m2 * ‖a‖ := mul_nonneg hm2nn (norm_nonneg a)
    nlinarith
  have hφ : |phi x A c - phi x A₀ c| ≤ L * ‖colSum A a - y0‖ := by
    have h0 := phi_sub_abs_le x c A A₀
    -- h0 : |φ−φ₀| ≤ (‖x‖ + (‖colSum A a‖ + ‖colSum A₀ a‖)/2)·‖colSum A a - colSum A₀ a‖
    have hhalf : (‖colSum A a‖ + ‖y0‖) / 2 ≤ M := by nlinarith [hyM, hηM]
    have hL0 : ‖x‖ + (‖colSum A a‖ + ‖y0‖) / 2 ≤ L := by
      dsimp [L]
      nlinarith [hhalf]
    have hLnn : 0 ≤ L := by
      dsimp [L]
      exact add_nonneg (norm_nonneg x) hMnn
    calc
      |phi x A c - phi x A₀ c| ≤ (‖x‖ + (‖colSum A a‖ + ‖y0‖) / 2) * ‖colSum A a - y0‖ := by
        simpa [y0] using h0
      _ ≤ L * ‖colSum A a - y0‖ := mul_le_mul_of_nonneg_right hL0 hDnn
  have hδm2na : m2 * δ * ‖a‖ ≤ m2 * δ * (‖a‖ + 1) := by
    have h1 : ‖a‖ ≤ ‖a‖ + 1 := by linarith
    have hm2δnn : 0 ≤ m2 * δ := mul_nonneg hm2nn hδnn
    calc
      m2 * δ * ‖a‖ ≤ m2 * δ * (‖a‖ + 1) := by
        -- (m2·δ)·‖a‖ ≤ (m2·δ)·(‖a‖+1)
        exact mul_le_mul_of_nonneg_left h1 hm2δnn
      _ = m2 * δ * (‖a‖ + 1) := rfl
  have hLd : L * (m2 * δ * (‖a‖ + 1)) ≤ ε / 2 := by
    have hb : δ * (2 * (K + 1)) ≤ ε := by
      exact (le_div_iff₀ hden).mp hδleK
    -- L·(m2·δ·(‖a‖+1)) = L·m2·(‖a‖+1)·δ ≤ ε/2
    have hmain : L * m2 * (‖a‖ + 1) * δ ≤ ε / 2 := by
      nlinarith [hb, hδnn]
    have hring : L * m2 * (‖a‖ + 1) * δ = L * (m2 * δ * (‖a‖ + 1)) := by ring
    rwa [← hring]
  have hLd0 : L * ‖colSum A a - y0‖ ≤ ε / 2 := by
    have hLnn : 0 ≤ L := by dsimp [L]; exact add_nonneg (norm_nonneg x) hMnn
    calc
      L * ‖colSum A a - y0‖ ≤ L * (m2 * δ * ‖a‖) := by
        exact mul_le_mul_of_nonneg_left hD hLnn
      _ ≤ L * (m2 * δ * (‖a‖ + 1)) := by
        exact mul_le_mul_of_nonneg_left hδm2na hLnn
      _ ≤ ε / 2 := hLd
  calc
    |phi x A c - phi x A₀ c| ≤ L * ‖colSum A a - y0‖ := hφ
    _ ≤ ε / 2 := hLd0
    _ < ε := by linarith

/-- The coefficient box: integer coefficient vectors with entries of absolute value ≤ C. -/
def coeffBox (C : ℕ) : Set (Fin m → ℤ) :=
  {c | ∀ i : Fin m, Int.natAbs (c i) ≤ C}

lemma coeffBox_finite (C : ℕ) : (coeffBox C : Set (Fin m → ℤ)).Finite := by
  classical
  have hset : coeffBox C = Set.univ.pi (fun i : Fin m => {z : ℤ | Int.natAbs z ≤ C}) := by
    ext c
    simp [coeffBox]
  rw [hset]
  refine Set.Finite.pi ?_
  intro i
  have hsub : {z : ℤ | Int.natAbs z ≤ C} ⊆ Set.Icc (-(C : ℤ)) (C : ℤ) := by
    intro z hz
    rw [Set.mem_Icc]
    have hz' : (Int.natAbs z : ℤ) ≤ (C : ℤ) := by exact_mod_cast hz
    have hzle : z ≤ (C : ℤ) := le_trans (Int.le_natAbs (a := z)) hz'
    constructor
    · have hneg : -(z : ℤ) ≤ (C : ℤ) := by
        calc
          -(z : ℤ) ≤ ((Int.natAbs (-z)) : ℤ) := Int.le_natAbs (a := -z)
          _ = ((Int.natAbs z) : ℤ) := by rw [Int.natAbs_neg]
          _ ≤ (C : ℤ) := hz'
      exact (neg_le.mp hneg)
    · exact hzle
  exact (Set.finite_Icc (-(C : ℤ)) (C : ℤ)).subset hsub

/-- In the box the sup-norm of the real coefficients is ≤ C. -/
lemma coeffBox_norm_le (C : ℕ) {c : Fin m → ℤ} (hc : c ∈ (coeffBox C : Set (Fin m → ℤ))) :
    ‖(fun i : Fin m => (c i : ℝ))‖ ≤ (C : ℝ) := by
  classical
  rw [Pi.norm_def]
  exact_mod_cast (Finset.sup_le (by
    intro b hb
    have hb1 : |(c b : ℝ)| ≤ (C : ℝ) := by
      have hci : |(c b : ℝ)| = ((Int.natAbs (c b) : ℕ) : ℝ) := by
        rw [← Int.cast_abs]
        congr 1
        rw [Int.abs_eq_natAbs]
      rw [hci]
      exact_mod_cast (hc b)
    have hb2 : (‖(c b : ℝ)‖₊ : ℝ) ≤ (C : ℝ) := by
      change ‖(c b : ℝ)‖ ≤ (C : ℝ)
      rw [Real.norm_eq_abs]
      exact hb1
    exact_mod_cast hb2))

/-- Strictness of the constraints over a whole coefficient box survives small perturbations:
if every nonzero `c` in the box has `φ_c(A₀) < 0`, then there is a box around `A₀` where all
of them stay strictly negative (finite family + continuity of each `φ_c`). -/
lemma forall_box_strict (x : E) (A₀ : Matrix (Fin m) (Fin m) ℝ) (C : ℕ)
    (hneg : ∀ c : Fin m → ℤ, c ∈ coeffBox C → c ≠ 0 → phi x A₀ c < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin m) (Fin m) ℝ, box A₀ A δ →
      ∀ c : Fin m → ℤ, c ∈ coeffBox C → c ≠ 0 → phi x A c < 0 := by
  classical
  have hfin : (coeffBox C : Set (Fin m → ℤ)).Finite := coeffBox_finite C
  letI : Fintype {c : Fin m → ℤ // c ∈ coeffBox C} := hfin.fintype
  let cont : (c : {c : Fin m → ℤ // c ∈ coeffBox C}) → c.1 ≠ 0 → ∃ δ : ℝ, 0 < δ ∧
      ∀ A : Matrix (Fin m) (Fin m) ℝ, box A₀ A δ → |phi x A c.1 - phi x A₀ c.1| < -(phi x A₀ c.1) / 2 := by
    intro c hc0
    exact phi_abs_cont x c.1 A₀ (-(phi x A₀ c.1) / 2) (by
      have hlt : phi x A₀ c.1 < 0 := hneg c.1 c.2 hc0
      linarith)
  let d : {c : Fin m → ℤ // c ∈ coeffBox C} → ℝ := fun c =>
    if hc0 : c.1 ≠ 0 then Classical.choose (cont c hc0) else 1
  have dpos : ∀ c : {c : Fin m → ℤ // c ∈ coeffBox C}, 0 < d c := by
    intro c
    by_cases hc0 : c.1 ≠ 0
    · dsimp [d]
      rw [dif_pos hc0]
      exact (Classical.choose_spec (cont c hc0)).1
    · dsimp [d]
      rw [dif_neg hc0]
      norm_num
  have dprop : ∀ (c : {c : Fin m → ℤ // c ∈ coeffBox C}) (hc0 : c.1 ≠ 0),
      ∀ A : Matrix (Fin m) (Fin m) ℝ, box A₀ A (d c) →
        |phi x A c.1 - phi x A₀ c.1| < -(phi x A₀ c.1) / 2 := by
    intro c hc0 A hA
    dsimp [d] at hA ⊢
    rw [dif_pos hc0] at hA
    exact (Classical.choose_spec (cont c hc0)).2 A hA
  let S : Finset ℝ := Finset.univ.image d
  let T : Finset ℝ := insert 1 S
  have hTne : T.Nonempty := ⟨1, by simp [T]⟩
  let δ : ℝ := T.min' hTne
  have hδle : ∀ e ∈ T, δ ≤ e := by
    intro e he
    exact Finset.min'_le T e he
  refine ⟨δ, ?_, ?_⟩
  · -- 0 < δ: δ ∈ T and all elements positive
    have hδmem : δ ∈ T := Finset.min'_mem T hTne
    have hallpos : ∀ e ∈ T, 0 < e := by
      intro e he
      dsimp [T] at he
      simp at he
      rcases he with rfl | he
      · norm_num
      · -- e ∈ image d univ: e = d c for some c
        rcases (Finset.mem_image.mp he) with ⟨c, hc, hcd⟩
        rw [← hcd]
        exact dpos c
    exact hallpos δ hδmem
  · intro A hA c hcbox hc0
    let cc : {c : Fin m → ℤ // c ∈ coeffBox C} := ⟨c, hcbox⟩
    have hmem : d cc ∈ T := by
      dsimp [T, S]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨cc, Finset.mem_univ cc, rfl⟩))
    have hle : δ ≤ d cc := hδle (d cc) hmem
    have hAbox : box A₀ A (d cc) := by
      intro j i
      exact lt_of_lt_of_le (hA j i) hle
    have habs := dprop cc hc0 A hAbox
    -- from |φ(A) − φ(A₀)| < −φ(A₀)/2 and φ(A₀) < 0: φ(A) < 0
    have hlt2 := (abs_lt.mp habs).2
    have hφ0 : phi x A₀ cc.1 < 0 := hneg cc.1 cc.2 hc0
    nlinarith

/-- Far lattice points never beat the origin: `2‖x‖ ≤ ‖y‖` implies the `c`-constraint. -/
lemma far_phi (x : E) (A : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℤ)
    (h : 2 * ‖x‖ ≤ ‖colSum A (fun i => (c i : ℝ))‖) : phi x A c ≤ 0 := by
  let y : E := colSum A (fun i => (c i : ℝ))
  have h1 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  have h2 : ‖x‖ * ‖y‖ ≤ ‖y‖ ^ 2 / 2 := by
    have hm : 2 * ‖x‖ * ‖y‖ ≤ ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_right h (norm_nonneg y)
    nlinarith
  dsimp [phi, y]
  nlinarith

lemma phi_zero (x : E) (A : Matrix (Fin m) (Fin m) ℝ) : phi x A 0 = 0 := by
  simp [phi, colSum]

lemma colSum_ne_zero_of_ne_zero (A : Matrix (Fin m) (Fin m) ℝ) (hdet : A.det ≠ 0)
    {c : Fin m → ℤ} (hc0 : c ≠ 0) : colSum A (fun i => (c i : ℝ)) ≠ 0 := by
  intro hcol
  have hE : (colsBasis A hdet).equivFun.symm (fun i => (c i : ℝ)) = 0 := by
    rw [← colSum_eq_equivFun_symm (m := m) hdet]
    exact hcol
  have ha0 : (fun i => (c i : ℝ)) = 0 := by
    exact (colsBasis A hdet).equivFun.symm.map_eq_zero_iff.mp hE
  apply hc0
  funext i
  change c i = (0 : ℤ)
  have hci : ((c i : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by simpa using (congrFun ha0 i)
  exact (Int.cast_inj (α := ℝ)).mp hci

/-- Off the tie set, membership makes every nonzero coefficient constraint strict. -/
lemma phi_strict_of_mem_cell (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0)
    (x : E) (hxV : x ∈ VC (latticeOfMatrix A₀))
    (hx : x ∉ Submission.VoronoiContinuity.tieSet (latticeOfMatrix A₀))
    {c : Fin m → ℤ} (hc0 : c ≠ 0) : phi x A₀ c < 0 := by
  let z : E := colSum A₀ (fun i => (c i : ℝ))
  have hzmem : z ∈ (latticeOfMatrix A₀ : Set E) :=
    (mem_span_cols_iff A₀ z).mpr ⟨c, rfl⟩
  let y : latticeOfMatrix A₀ := ⟨z, hzmem⟩
  have hy0 : y ≠ 0 := by
    intro hyz
    apply colSum_ne_zero_of_ne_zero A₀ hdet hc0
    exact congrArg Subtype.val hyz
  have hle : inner ℝ x (y : E) ≤ ‖(y : E)‖ ^ 2 / 2 := (Submission.Voronoi.mem_voronoi.mp hxV) y
  have hne : inner ℝ x (y : E) ≠ ‖(y : E)‖ ^ 2 / 2 := by
    intro heq
    apply hx
    exact ⟨y, hy0, heq⟩
  have hlt : inner ℝ x (y : E) < ‖(y : E)‖ ^ 2 / 2 := lt_of_le_of_ne hle hne
  dsimp [phi, z, y] at hlt ⊢
  linarith

/-- forward half of cell stabilization: membership in the limit cell is preserved for
matrices close to `A₀` (off the tie set). -/
lemma cell_mem_stable_forward_body (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0)
    (x : E) (hxV : x ∈ VC (latticeOfMatrix A₀))
    (hx : x ∉ Submission.VoronoiContinuity.tieSet (latticeOfMatrix A₀)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin m) (Fin m) ℝ, box A₀ A δ → x ∈ VC (latticeOfMatrix A) := by
  classical
  have hRpos1 : 0 ≤ 2 * ‖x‖ := by positivity
  have hRpos2 : 0 ≤ 2 * ‖x‖ + 1 := by positivity
  rcases delta_uniform_coefficient_bound (m := m) A₀ hdet (2 * ‖x‖) hRpos1 with ⟨δ₁, hδ₁, C₁, hC₁⟩
  rcases delta_uniform_coefficient_bound (m := m) A₀ hdet (2 * ‖x‖ + 1) hRpos2 with ⟨δ₀, hδ₀, C₀, hC₀⟩
  have hstrict₀ : ∀ c : Fin m → ℤ, c ∈ coeffBox C₀ → c ≠ 0 → phi x A₀ c < 0 := by
    intro c hcbox c0
    exact phi_strict_of_mem_cell A₀ hdet x hxV hx c0
  rcases forall_box_strict x A₀ C₀ hstrict₀ with ⟨δ₂, hδ₂, hb2⟩
  let δ₃ : ℝ := 1 / ((((m : ℝ) ^ 2) * ((C₁ : ℝ) + 1)) + 1)
  have hδ₃ : 0 < δ₃ := by
    dsimp [δ₃]
    positivity
  let δ : ℝ := min (min δ₁ δ₂) δ₃
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδpos, ?_⟩
  intro A hA
  have hδ₁le : δ ≤ δ₁ := by
    dsimp [δ]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₂le : δ ≤ δ₂ := by
    dsimp [δ]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₃le : δ ≤ δ₃ := by
    dsimp [δ]
    exact min_le_right _ _
  have hAδ1 : box A₀ A δ₁ := by
    intro j i
    exact lt_of_lt_of_le (hA j i) hδ₁le
  have hAδ2 : box A₀ A δ₂ := by
    intro j i
    exact lt_of_lt_of_le (hA j i) hδ₂le
  have hall : ∀ c : Fin m → ℤ, phi x A c ≤ 0 := by
    intro c
    let a : Fin m → ℝ := fun i => (c i : ℝ)
    by_cases hfar : 2 * ‖x‖ ≤ ‖colSum A a‖
    · -- far: automatic
      exact far_phi x A c hfar
    · have hlt0 : ‖colSum A a‖ < 2 * ‖x‖ := lt_of_not_ge hfar
      -- c is in the uniform box C₁
      have hcC1 : c ∈ coeffBox C₁ := by
        intro i
        exact hC₁ A hAδ1 c (le_of_lt hlt0) i
      have hnaC1 : ‖a‖ ≤ (C₁ : ℝ) := by
        simpa [a] using (coeffBox_norm_le C₁ hcC1)
      -- perturbation of the lattice point is tiny: ‖colSum A a − colSum A₀ a‖ ≤ 1
      have hdiff : ‖colSum A a - colSum A₀ a‖ ≤ 1 := by
        have h1 : ‖colSum A a - colSum A₀ a‖ ≤ ((m : ℝ) ^ 2) * δ * ‖a‖ := by
          simpa [a] using (colSum_box_diff_le A A₀ δ hA a)
        have h2 : ((m : ℝ) ^ 2) * δ * ‖a‖ ≤ ((m : ℝ) ^ 2) * δ * (C₁ : ℝ) := by
          have h1' : ((m : ℝ) ^ 2) * δ ≥ 0 := by positivity
          exact mul_le_mul_of_nonneg_left hnaC1 h1'
        have h3 : ((m : ℝ) ^ 2) * δ * (C₁ : ℝ) ≤ 1 := by
          have hδ₃m : ((m : ℝ) ^ 2) * δ₃ * (C₁ : ℝ) ≤ 1 := by
            dsimp [δ₃]
            have hden : 0 < ((m : ℝ) ^ 2) * ((C₁ : ℝ) + 1) + 1 := by positivity
            have hrew : ((m : ℝ) ^ 2) * (1 / (((m : ℝ) ^ 2) * ((C₁ : ℝ) + 1) + 1)) * (C₁ : ℝ) =
                (((m : ℝ) ^ 2) * (C₁ : ℝ)) / (((m : ℝ) ^ 2) * ((C₁ : ℝ) + 1) + 1) := by ring
            rw [hrew]
            rw [div_le_iff₀ hden]
            nlinarith
          have hδm : ((m : ℝ) ^ 2) * δ ≤ ((m : ℝ) ^ 2) * δ₃ := by
            exact mul_le_mul_of_nonneg_left hδ₃le (by positivity)
          have hm2C1nn : 0 ≤ (C₁ : ℝ) := by positivity
          calc
            ((m : ℝ) ^ 2) * δ * (C₁ : ℝ) = (((m : ℝ) ^ 2) * δ) * (C₁ : ℝ) := by ring
            _ ≤ (((m : ℝ) ^ 2) * δ₃) * (C₁ : ℝ) := mul_le_mul_of_nonneg_right hδm hm2C1nn
            _ = ((m : ℝ) ^ 2) * δ₃ * (C₁ : ℝ) := by ring
            _ ≤ 1 := hδ₃m
        exact le_trans h1 (le_trans h2 h3)
      -- so colSum A₀ a has norm ≤ 2‖x‖ + 1
      have hA0R : ‖colSum A₀ a‖ ≤ 2 * ‖x‖ + 1 := by
        have hnorm : ‖colSum A₀ a‖ ≤ ‖colSum A a‖ + ‖colSum A a - colSum A₀ a‖ := by
          have hx : colSum A₀ a = colSum A a + (colSum A₀ a - colSum A a) := by abel
          calc
            ‖colSum A₀ a‖ = ‖colSum A a + (colSum A₀ a - colSum A a)‖ := by
              conv_lhs => rw [hx]
            _ ≤ ‖colSum A a‖ + ‖colSum A₀ a - colSum A a‖ := norm_add_le _ _
            _ ≤ ‖colSum A a‖ + ‖colSum A a - colSum A₀ a‖ := by
              have hrev : ‖colSum A₀ a - colSum A a‖ = ‖colSum A a - colSum A₀ a‖ := norm_sub_rev _ _
              rw [hrev]
        nlinarith [hnorm, hlt0, hdiff]
      -- hence c is in the A₀-side box C₀
      have hcC0 : c ∈ coeffBox C₀ := by
        intro i
        exact hC₀ A₀ (by intro j i0; simp; linarith) c hA0R i
      by_cases hc0 : c = 0
      · rw [hc0]
        rw [phi_zero]
      · have hlt : phi x A c < 0 := hb2 A hAδ2 c hcC0 hc0
        exact le_of_lt hlt
  exact (mem_cell_coeff A x).mpr (by
    intro c
    have h := hall c
    dsimp [phi] at h
    linarith)

/-- backward half of cell stabilization: non-membership in the limit cell is preserved for
matrices close to `A₀`. -/
lemma cell_mem_stable_backward_body (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0)
    (x : E) (hxV : x ∉ VC (latticeOfMatrix A₀)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin m) (Fin m) ℝ, box A₀ A δ → x ∉ VC (latticeOfMatrix A) := by
  classical
  have hpos : ∃ c : Fin m → ℤ, 0 < phi x A₀ c := by
    by_contra hno
    push_neg at hno
    have hraw : ∀ c : Fin m → ℤ,
        inner ℝ x (colSum A₀ (fun i => (c i : ℝ))) ≤ ‖colSum A₀ (fun i => (c i : ℝ))‖ ^ 2 / 2 := by
      intro c
      have hφ : phi x A₀ c ≤ 0 := hno c
      dsimp [phi] at hφ
      linarith
    exact hxV ((mem_cell_coeff A₀ x).mpr hraw)
  rcases hpos with ⟨c₀, hc₀⟩
  let a0 : Fin m → ℝ := fun i => (c₀ i : ℝ)
  let y0 : E := colSum A₀ a0
  -- a strictly violated constraint can only involve a lattice point inside ball 0 (2‖x‖)
  have hylt : ‖y0‖ < 2 * ‖x‖ := by
    by_contra hge
    have hge' : 2 * ‖x‖ ≤ ‖y0‖ := le_of_not_gt hge
    have hle : inner ℝ x y0 ≤ ‖x‖ * ‖y0‖ := real_inner_le_norm x y0
    have hgt : ‖y0‖ ^ 2 / 2 < inner ℝ x y0 := by
      dsimp [phi] at hc₀
      dsimp [y0, a0] at ⊢
      linarith
    have hmain : ‖y0‖ ^ 2 < 2 * ‖x‖ * ‖y0‖ := by nlinarith
    have hsub : 2 * ‖x‖ * ‖y0‖ ≤ ‖y0‖ * ‖y0‖ := mul_le_mul_of_nonneg_right hge' (norm_nonneg y0)
    nlinarith
  have hε : 0 < phi x A₀ c₀ / 2 := by linarith
  rcases phi_abs_cont x c₀ A₀ (phi x A₀ c₀ / 2) hε with ⟨δ, hδpos, hcont⟩
  refine ⟨δ, hδpos, ?_⟩
  intro A hA hxVA
  have hall := (mem_cell_coeff A x).mp hxVA
  have hle0 : inner ℝ x (colSum A a0) ≤ ‖colSum A a0‖ ^ 2 / 2 := hall c₀
  have hφle0 : phi x A c₀ ≤ 0 := by
    dsimp [phi]
    linarith
  have habs := hcont A hA
  have hbig := (abs_lt.mp habs).1
  nlinarith [hφle0, hbig, hc₀]

/-- unconditional forward (vacuous when `x ∉ VC (latticeOfMatrix A₀)`) -/
lemma cell_mem_stable_forward (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0) (x : E)
    (hx : x ∉ Submission.VoronoiContinuity.tieSet (latticeOfMatrix A₀)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin m) (Fin m) ℝ, box A₀ A δ →
      x ∈ VC (latticeOfMatrix A₀) → x ∈ VC (latticeOfMatrix A) := by
  classical
  by_cases hxV : x ∈ VC (latticeOfMatrix A₀)
  · rcases cell_mem_stable_forward_body A₀ hdet x hxV hx with ⟨δ, hδ, hf⟩
    refine ⟨δ, hδ, ?_⟩
    intro A hA hxV0
    exact hf A hA
  · refine ⟨1, by norm_num, ?_⟩
    intro A hA hxV0
    exfalso
    exact hxV hxV0

/-- unconditional backward (vacuous when `x ∈ VC (latticeOfMatrix A₀)`) -/
lemma cell_mem_stable_backward (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0) (x : E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin m) (Fin m) ℝ, box A₀ A δ →
      x ∉ VC (latticeOfMatrix A₀) → x ∉ VC (latticeOfMatrix A) := by
  classical
  by_cases hxV : x ∈ VC (latticeOfMatrix A₀)
  · refine ⟨1, by norm_num, ?_⟩
    intro A hA hxV0
    exfalso
    exact hxV0 hxV
  · rcases cell_mem_stable_backward_body A₀ hdet x hxV with ⟨δ, hδ, hb⟩
    refine ⟨δ, hδ, ?_⟩
    intro A hA hxV0
    exact hb A hA

/-- **P3.1c**: off the tie set of `latticeOfMatrix A₀`, Voronoi-cell membership is locally
constant in the basis matrix. -/
lemma cell_mem_stable (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0) (x : E)
    (hx : x ∉ Submission.VoronoiContinuity.tieSet (latticeOfMatrix A₀)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin m) (Fin m) ℝ, box A₀ A δ →
      (x ∈ VC (latticeOfMatrix A) ↔ x ∈ VC (latticeOfMatrix A₀)) := by
  classical
  rcases cell_mem_stable_forward A₀ hdet x hx with ⟨δf, hδf, hf⟩
  rcases cell_mem_stable_backward A₀ hdet x with ⟨δb, hδb, hb⟩
  let δ : ℝ := min δf δb
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδf hδb
  refine ⟨δ, hδpos, ?_⟩
  intro A hA
  have hAf : box A₀ A δf := by
    intro j i
    exact lt_of_lt_of_le (hA j i) (min_le_left _ _)
  have hAb : box A₀ A δb := by
    intro j i
    exact lt_of_lt_of_le (hA j i) (min_le_right _ _)
  constructor
  · intro hxVA
    by_contra hxV0
    exact (hb A hAb hxV0) hxVA
  · intro hxV0
    exact hf A hAf hxV0


/-- Sequential stabilization: if matrices `Aₙ` converge (in the matrix product topology) to
`A₀`, then for every `x` off the tie set of `latticeOfMatrix A₀` the cell membership of `x`
is eventually the same for all `Aₙ`.  This is the pointwise input of the P3.2 dominated-
convergence argument for the continuity of `ℒ ↦ γ_{1/t}(V(ℒ))` along convergent stable
basis matrices. -/
lemma cell_mem_eventual (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0) (x : E)
    (hx : x ∉ Submission.VoronoiContinuity.tieSet (latticeOfMatrix A₀))
    (An : ℕ → Matrix (Fin m) (Fin m) ℝ) (hconv : Filter.Tendsto An Filter.atTop (𝓝 A₀)) :
    ∀ᶠ n in Filter.atTop, (x ∈ VC (latticeOfMatrix (An n)) ↔ x ∈ VC (latticeOfMatrix A₀)) := by
  classical
  rcases cell_mem_stable A₀ hdet x hx with ⟨δ, hδpos, hstab⟩
  have hpt (j i : Fin m) : Filter.Tendsto (fun n : ℕ => An n j i) Filter.atTop (𝓝 (A₀ j i)) := by
    have hc : Continuous (fun M : Matrix (Fin m) (Fin m) ℝ => M j i) := by
      exact continuous_apply_apply j i
    exact (Filter.Tendsto.comp (hc.continuousAt (x := A₀)) hconv)
  have hcoords : ∀ j i : Fin m, ∀ᶠ n in Filter.atTop, |An n j i - A₀ j i| < δ := by
    intro j i
    have hd := (Metric.tendsto_nhds.mp (hpt j i)) δ hδpos
    exact hd.mono (by
      intro n hn
      simpa [Real.dist_eq] using hn)
  have hboxE : ∀ᶠ n in Filter.atTop, box A₀ (An n) δ := by
    change ∀ᶠ n in Filter.atTop, ∀ j i : Fin m, |An n j i - A₀ j i| < δ
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro i
    exact hcoords j i
  exact hboxE.mono (fun n hn => hstab (An n) hn)


/-- `latticeOfMatrix A` is discrete when `det A ≠ 0`: its columns are an `ℝ`-basis
(`colsBasis`), and Mathlib's ZLattice instance makes the `ℤ`-span of any real basis discrete;
transport along the (continuous, injective) inclusion of the equal submodule. -/
lemma latticeOfMatrix_discrete (A : Matrix (Fin m) (Fin m) ℝ) (hdet : A.det ≠ 0) :
    DiscreteTopology (latticeOfMatrix A) := by
  classical
  let B : Module.Basis (Fin m) ℝ E := colsBasis A hdet
  let Λ₂ : Submodule ℤ E := Submodule.span ℤ (Set.range B)
  have hfam : (cols A) = B := by
    dsimp [B]
    funext i
    exact (colsBasis_apply A hdet i).symm
  have hrange : Set.range (cols A) = Set.range B := by rw [hfam]
  have hΛ : latticeOfMatrix A = Λ₂ := by
    dsimp [Λ₂]
    change Submodule.span ℤ (Set.range (cols A)) = Submodule.span ℤ (Set.range B)
    rw [hrange]
  have hle : latticeOfMatrix A ≤ Λ₂ := by rw [hΛ]
  haveI : DiscreteTopology Λ₂ := by
    dsimp [Λ₂]
    infer_instance
  let f : latticeOfMatrix A → Λ₂ := fun x => ⟨(x : E), hle x.2⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Λ₂ => (z : E)) hxy
  have hf_cont : Continuous f := by
    have hv : Continuous (fun x : latticeOfMatrix A => (x : E)) := continuous_subtype_val
    exact Continuous.subtype_mk hv (fun x => hle x.2)
  exact DiscreteTopology.of_continuous_injective (β := Λ₂) hf_cont hf_inj

/-- `latticeOfMatrix A` is countable: it is the image of the countable coefficient domain
`Fin m → ℤ` under the (integer) linear-combination map. -/
lemma latticeOfMatrix_countable (A : Matrix (Fin m) (Fin m) ℝ) : Countable (latticeOfMatrix A) := by
  classical
  let φ : (Fin m → ℤ) → E := fun c => ∑ i : Fin m, (c i : ℤ) • cols A i
  have hφ : ∀ c : Fin m → ℤ, colSum A (fun i => (c i : ℝ)) = φ c := by
    intro c
    dsimp [φ]
    exact colSum_eq_zsmul A c
  have hset : (Set.range φ) = (latticeOfMatrix A : Set E) := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact (mem_span_cols_iff A (φ c)).mpr ⟨c, hφ c⟩
    · intro hz
      rcases (mem_span_cols_iff A z).mp hz with ⟨c, hcz⟩
      refine ⟨c, ?_⟩
      calc
        φ c = colSum A (fun i => (c i : ℝ)) := (hφ c).symm
        _ = z := hcz
  have hc : (Set.range φ).Countable := Set.countable_range φ
  have hsetc : ((latticeOfMatrix A : Set E)).Countable := by
    rwa [← hset]
  exact hsetc.to_subtype

/-- The tie set of a nonsingular basis matrix has measure zero (discrete + countable + the
countable-union-of-hyperplanes argument of `VoronoiContinuity.volume_tieSet_zero`). -/
lemma volume_tieSet_zero_of_matrix (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet : A₀.det ≠ 0) :
    volume (Submission.VoronoiContinuity.tieSet (latticeOfMatrix A₀)) = 0 := by
  haveI : DiscreteTopology (latticeOfMatrix A₀) := latticeOfMatrix_discrete A₀ hdet
  haveI : Countable (latticeOfMatrix A₀) := latticeOfMatrix_countable A₀
  exact Submission.VoronoiContinuity.volume_tieSet_zero (ℒ := latticeOfMatrix A₀)

end Submission.CellContinuity
