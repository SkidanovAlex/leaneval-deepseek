import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.KinInt
import Submission.PairInt
import Submission.SliceEnergy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The piece energy decomposes over the cells

The algebraic layer of the bracket: for an assignment piece `φ` (any smooth
function), the numerator `∫ φ·𝓗φ` splits over the cells of the assignment into
per-cell parts plus a nonnegative cross-cell term:

    ∫ φ·𝓗φ  =  Σ_j [ cellKinetic a j φ + cellIntra a j v φ ] + cross(a,φ)

with `cross ≥ 0` for `v ≥ 0` (interactions between particles assigned to
*different* cells are dropped).  Hence

    ∫ φ·𝓗φ  ≥  Σ_j cellOpEnergy a j v φ      (cellOpEnergy := cellKinetic + cellIntra).

The pieces:

  * `cellPairs a j` — pairs `i < l` with both particles in cell `j`;
  * `crossPairs a` — pairs `i < l` in *different* cells;
  * `pairPartition` — the set `{i < l}` is the disjoint union of the
    `cellPairs a j` over all cells and the `crossPairs a`;
  * `cellKinetic a j` / `cellIntra a j v` / `cellOpEnergy a j v` — the
    per-cell kinetic, intra-cell interaction, and their sum;
  * `piece_numerator_ge_cellsum` — the numerator inequality above (kinetic
    splits because each particle belongs to exactly one cell; cross pairs are
    dropped by `v ≥ 0`).

The per-cell lower bound `cellOpEnergy a j v φ ≥ eNeu (cellCount a j) (2ℓ) v ·
‖φ‖²` (the slice/Fubini content, built on `SliceEnergy.sliceWsE_ge_eNeu`) is
the next layer; this module is purely its algebraic base.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "Δ[" i "]" => partialLaplacian i

/-- All ordered particle pairs `i < l`. -/
def allPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)

/-- Pairs of particles both assigned to the cell `j`. -/
def cellPairs {m N : ℕ} (a : Assign m N) (j : CellIdx m) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2 ∧ a p.1 = j ∧ a p.2 = j)

/-- Pairs of particles assigned to different cells (the cross terms, dropped by
`v ≥ 0`). -/
def crossPairs {m N : ℕ} (a : Assign m N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2 ∧ a p.1 ≠ a p.2)

/-- The occupied sets partition the particles: summing over cells and their
occupied sets reproduces the sum over all particles. -/
lemma sum_over_occSets {m N : ℕ} (a : Assign m N) (C : Fin N → ℝ) :
    (∑ j : CellIdx m, ∑ i ∈ occSet a j, C i) = ∑ i : Fin N, C i := by
  classical
  have h1 : (∑ j : CellIdx m, ∑ i ∈ occSet a j, C i)
      = ∑ j : CellIdx m, ∑ i : Fin N, if a i = j then C i else 0 := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [occSet]
    rw [Finset.sum_filter]
  have h2 : (∑ j : CellIdx m, ∑ i : Fin N, if a i = j then C i else 0)
      = ∑ i : Fin N, (∑ j : CellIdx m, if a i = j then C i else 0) := by
    rw [Finset.sum_comm]
  have h3 : ∀ i : Fin N, (∑ j : CellIdx m, if a i = j then C i else 0) = C i := by
    intro i
    simpa using (Fintype.sum_ite_eq (a i) (fun _ : CellIdx m => C i))
  calc
    (∑ j : CellIdx m, ∑ i ∈ occSet a j, C i)
        = ∑ j : CellIdx m, ∑ i : Fin N, if a i = j then C i else 0 := h1
    _ = ∑ i : Fin N, (∑ j : CellIdx m, if a i = j then C i else 0) := h2
    _ = ∑ i : Fin N, C i := by
      refine Finset.sum_congr rfl (fun i hi => h3 i)

/-- For fixed `p`, the sum over cells of the indicator of `a p.1 = j ∧ a p.2 = j`
is the indicator of `a p.1 = a p.2`. -/
lemma cellsum_same_ite {m N : ℕ} (a : Assign m N) (p : Fin N × Fin N) (F : Fin N × Fin N → ℝ) :
    (∑ j : CellIdx m, if (a p.1 = j ∧ a p.2 = j) then F p else 0) =
      if a p.1 = a p.2 then F p else 0 := by
  classical
  calc
    (∑ j : CellIdx m, if (a p.1 = j ∧ a p.2 = j) then F p else 0)
        = ∑ j : CellIdx m, if a p.1 = j then (if a p.2 = j then F p else 0) else 0 := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          by_cases h1 : a p.1 = j <;> by_cases h2 : a p.2 = j <;> simp [h1, h2]
    _ = if a p.2 = a p.1 then F p else 0 := by
          simpa using (Fintype.sum_ite_eq (a p.1) (fun j : CellIdx m =>
            if a p.2 = j then F p else 0))
    _ = if a p.1 = a p.2 then F p else 0 := by
          simp [eq_comm]

/-- The sum of the per-cell pair sums equals the same-cell part of the `allPairs`
sum. -/
lemma sum_cellPairs_indicator {m N : ℕ} (a : Assign m N) (F : Fin N × Fin N → ℝ) :
    (∑ j : CellIdx m, ∑ p ∈ cellPairs a j, F p) =
      ∑ p ∈ allPairs N, if a p.1 = a p.2 then F p else 0 := by
  classical
  have h1 : (∑ j : CellIdx m, ∑ p ∈ cellPairs a j, F p)
      = ∑ j : CellIdx m, ∑ p : Fin N × Fin N,
          if (p.1 < p.2 ∧ a p.1 = j ∧ a p.2 = j) then F p else 0 := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [cellPairs]
    rw [Finset.sum_filter]
  have h2 : (∑ j : CellIdx m, ∑ p : Fin N × Fin N,
        if (p.1 < p.2 ∧ a p.1 = j ∧ a p.2 = j) then F p else 0)
      = ∑ p : Fin N × Fin N, (∑ j : CellIdx m,
          if (p.1 < p.2 ∧ a p.1 = j ∧ a p.2 = j) then F p else 0) := by
    rw [Finset.sum_comm]
  have h3 : ∀ p : Fin N × Fin N,
      (∑ j : CellIdx m, if (p.1 < p.2 ∧ a p.1 = j ∧ a p.2 = j) then F p else 0)
        = if (p.1 < p.2 ∧ a p.1 = a p.2) then F p else 0 := by
    intro p
    by_cases hlt : p.1 < p.2
    · have hcell := cellsum_same_ite a p F
      rw [show (∑ j : CellIdx m, if (p.1 < p.2 ∧ a p.1 = j ∧ a p.2 = j) then F p else 0)
            = (∑ j : CellIdx m, if (a p.1 = j ∧ a p.2 = j) then F p else 0) by
              refine Finset.sum_congr rfl (fun j hj => ?_)
              simp [hlt]]
      rw [hcell]
      simp [hlt]
    · simp [hlt]
  calc
    (∑ j : CellIdx m, ∑ p ∈ cellPairs a j, F p)
        = ∑ j : CellIdx m, ∑ p : Fin N × Fin N,
            if (p.1 < p.2 ∧ a p.1 = j ∧ a p.2 = j) then F p else 0 := h1
    _ = ∑ p : Fin N × Fin N, (∑ j : CellIdx m,
          if (p.1 < p.2 ∧ a p.1 = j ∧ a p.2 = j) then F p else 0) := h2
    _ = ∑ p : Fin N × Fin N, if (p.1 < p.2 ∧ a p.1 = a p.2) then F p else 0 := by
      refine Finset.sum_congr rfl (fun p hp => h3 p)
    _ = ∑ p ∈ allPairs N, if a p.1 = a p.2 then F p else 0 := by
          symm
          rw [allPairs, Finset.sum_filter]
          refine Finset.sum_congr rfl (fun p hp => ?_)
          by_cases h : a p.1 = a p.2 <;> by_cases hlt : p.1 < p.2 <;> simp [h, hlt]

/-- The cross pair sum equals the different-cell part of the `allPairs` sum. -/
lemma sum_crossPairs_indicator {m N : ℕ} (a : Assign m N) (F : Fin N × Fin N → ℝ) :
    (∑ p ∈ crossPairs a, F p) =
      ∑ p ∈ allPairs N, if a p.1 ≠ a p.2 then F p else 0 := by
  classical
  calc
    (∑ p ∈ crossPairs a, F p)
        = ∑ p : Fin N × Fin N, if (p.1 < p.2 ∧ a p.1 ≠ a p.2) then F p else 0 := by
          simp only [crossPairs]
          rw [Finset.sum_filter]
    _ = ∑ p : Fin N × Fin N, if p.1 < p.2 then (if a p.1 ≠ a p.2 then F p else 0) else 0 := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          by_cases hlt : p.1 < p.2 <;> by_cases h : a p.1 ≠ a p.2 <;> simp [h, hlt]
    _ = ∑ p ∈ allPairs N, if a p.1 ≠ a p.2 then F p else 0 := by
          rw [allPairs, Finset.sum_filter]

/-- The pair set `{i < l}` is partitioned into the per-cell pairs and the cross
pairs: sums over `allPairs` split accordingly. -/
lemma pairPartition {m N : ℕ} (a : Assign m N) {f : Fin N × Fin N → ℝ} :
    (∑ p ∈ allPairs N, f p) =
      (∑ j : CellIdx m, ∑ p ∈ cellPairs a j, f p) + ∑ p ∈ crossPairs a, f p := by
  classical
  have hsplit : (∑ p ∈ allPairs N, f p)
      = (∑ p ∈ allPairs N, if a p.1 = a p.2 then f p else 0) +
          (∑ p ∈ allPairs N, if a p.1 ≠ a p.2 then f p else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    by_cases h : a p.1 = a p.2 <;> simp [h]
  rw [hsplit]
  rw [← sum_cellPairs_indicator a f]
  rw [← sum_crossPairs_indicator a f]

/-- The per-cell kinetic energy (operator form, over the whole space). -/
noncomputable def cellKinetic {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {φ : X N → ℝ} : ℝ :=
  ∑ i ∈ occSet a j, ∫ x : X N, φ x * (-(partialLaplacian i φ) x)

/-- The intra-cell interaction energy (over the whole space). -/
noncomputable def cellIntra {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (v : ℝ³ → ℝ) {φ : X N → ℝ} : ℝ :=
  ∫ x : X N, (φ x) ^ 2 * (∑ p ∈ cellPairs a j, v (x p.1 - x p.2))

/-- The per-cell operator energy. -/
noncomputable def cellOpEnergy {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (v : ℝ³ → ℝ) {φ : X N → ℝ} : ℝ :=
  cellKinetic a j (φ := φ) + cellIntra a j v (φ := φ)

/-- Pointwise form of the numerator: `φ·(𝓗φ) = Σ_i φ·(−Δ_iφ) + φ²·Σ_pairs v`. -/
lemma numerator_pointwise {N : ℕ} {v : ℝ³ → ℝ} {φ : X N → ℝ} :
    (fun x : X N => φ x * (_root_.BoseGases.𝓗 N v φ) x) =
      (fun x : X N => (∑ i : Fin N, φ x * (-(partialLaplacian i φ) x)) +
        (φ x) ^ 2 * (∑ p ∈ allPairs N, v (x p.1 - x p.2))) := by
  funext x
  unfold _root_.BoseGases.𝓗 allPairs
  simp only [Finset.sum_filter]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
  · rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    by_cases hlt : p.1 < p.2
    · simp [hlt]
      ring
    · simp [hlt]

/-- The cross interaction is nonnegative for `v ≥ 0`. -/
lemma cross_nonneg {m N : ℕ} {v : ℝ³ → ℝ} (hv : 0 ≤ v) (a : Assign m N)
    {φ : X N → ℝ} : 0 ≤ ∫ x : X N, (φ x) ^ 2 * (∑ p ∈ crossPairs a, v (x p.1 - x p.2)) := by
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg (φ x))
    (Finset.sum_nonneg (fun p hp => hv (x p.1 - x p.2))))

/-- **The piece numerator dominates the sum of the per-cell operator
energies**: the kinetic splits over the cells (each particle belongs to exactly
one), and the cross-cell interactions (≥ `0`) are dropped.  `MemLp v 1` makes
all interaction integrals genuinely integrable (Lean's integral convention
kills non-integrable integrands, which would otherwise corrupt the identity). -/
lemma piece_numerator_ge_cellsum {m N : ℕ} {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (a : Assign m N) {φ : X N → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcs : HasCompactSupport φ) :
    (∫ x : X N, φ x * (_root_.BoseGases.𝓗 N v φ) x) ≥
      ∑ j : CellIdx m, cellOpEnergy a j v (φ := φ) := by
  classical
  let g : Fin N → X N → ℝ := fun i x => φ x * (-(partialLaplacian i φ) x)
  let h : Fin N × Fin N → X N → ℝ := fun p x => (φ x)^2 * v (x p.1 - x p.2)
  let K : X N → ℝ := fun x => ∑ i : Fin N, g i x
  let P : X N → ℝ := fun x => (φ x)^2 * (∑ p ∈ allPairs N, v (x p.1 - x p.2))
  let Cj : CellIdx m → X N → ℝ :=
    fun j x => (φ x)^2 * (∑ p ∈ cellPairs a j, v (x p.1 - x p.2))
  let Cr : X N → ℝ := fun x => (φ x)^2 * (∑ p ∈ crossPairs a, v (x p.1 - x p.2))
  -- integrability
  have hg : ∀ i : Fin N, Integrable (g i) volume := by
    intro i
    dsimp [g]
    exact kinInt_term hφ hcs i
  have hh : ∀ p : Fin N × Fin N, Integrable (h p) volume := by
    intro p
    dsimp [h]
    exact pairInt_sq hv1 hφ.continuous hcs p.1 p.2
  have hK : Integrable K volume := by
    dsimp [K]
    exact integrable_finsetSum (s := Finset.univ) (f := g) (fun i hi => hg i)
  have hP : Integrable P volume := by
    have hP' : P = fun x : X N => ∑ p ∈ allPairs N, h p x := by
      funext x
      dsimp [P, h]
      rw [Finset.mul_sum]
    rw [hP']
    exact integrable_finsetSum (s := allPairs N) (f := fun p x => h p x) (fun p hp => hh p)
  have hCj : ∀ j : CellIdx m, Integrable (Cj j) volume := by
    intro j
    have hCj' : Cj j = fun x : X N => ∑ p ∈ cellPairs a j, h p x := by
      funext x
      dsimp [Cj, h]
      rw [Finset.mul_sum]
    rw [hCj']
    exact integrable_finsetSum (s := cellPairs a j) (f := fun p x => h p x) (fun p hp => hh p)
  have hCr : Integrable Cr volume := by
    have hCr' : Cr = fun x : X N => ∑ p ∈ crossPairs a, h p x := by
      funext x
      dsimp [Cr, h]
      rw [Finset.mul_sum]
    rw [hCr']
    exact integrable_finsetSum (s := crossPairs a) (f := fun p x => h p x) (fun p hp => hh p)
  -- numerator pointwise = K + P
  have hnum : (fun x : X N => φ x * (_root_.BoseGases.𝓗 N v φ) x) = K + P := by
    funext x
    rw [congrFun (numerator_pointwise (N := N) (v := v) (φ := φ)) x]
    dsimp [K, P, g]
  -- the kinetic part
  have hkin : (∫ x, K x) = ∑ j : CellIdx m, cellKinetic a j (φ := φ) := by
    calc
      (∫ x, K x) = ∑ i : Fin N, ∫ x, φ x * (-(partialLaplacian i φ) x) := by
            dsimp [K, g]
            exact integral_finsetSum (s := Finset.univ)
              (f := fun i x => φ x * (-(partialLaplacian i φ) x))
              (fun i hi => hg i)
      _ = ∑ j : CellIdx m, cellKinetic a j (φ := φ) := by
            rw [← sum_over_occSets a (fun i => ∫ x, φ x * (-(partialLaplacian i φ) x))]
            simp [cellKinetic]
  -- cross integrand nonnegative
  have hcross : 0 ≤ ∫ x, Cr x := by
    dsimp [Cr]
    exact cross_nonneg hv a
  -- interaction part: P splits into per-cell + cross
  have hint : (∫ x, P x) = (∑ j : CellIdx m, cellIntra a j v (φ := φ)) + ∫ x, Cr x := by
    have hPpt : P = fun x : X N => (∑ j : CellIdx m, Cj j x) + Cr x := by
      funext x
      dsimp [P, Cj, Cr]
      have hpd := pairPartition a (f := fun p => v (x p.1 - x p.2))
      rw [hpd]
      rw [mul_add]
      rw [Finset.mul_sum]
    have hsumCj : Integrable (fun x => ∑ j : CellIdx m, Cj j x) volume := by
      exact integrable_finsetSum (s := Finset.univ) (f := fun j x => Cj j x) (fun j hj => hCj j)
    calc
      (∫ x, P x) = (∫ x, (∑ j : CellIdx m, Cj j x) + Cr x) := by rw [hPpt]
      _ = (∫ x, ∑ j : CellIdx m, Cj j x) + ∫ x, Cr x := by
            exact integral_add hsumCj hCr
      _ = (∑ j : CellIdx m, ∫ x, Cj j x) + ∫ x, Cr x := by
            rw [integral_finsetSum (s := Finset.univ) (f := fun j x => Cj j x) (fun j hj => hCj j)]
      _ = (∑ j : CellIdx m, cellIntra a j v (φ := φ)) + ∫ x, Cr x := by
            simp [cellIntra, Cj]
  -- assemble
  have hLHS : (∫ x : X N, φ x * (_root_.BoseGases.𝓗 N v φ) x) =
      (∑ j : CellIdx m, cellKinetic a j (φ := φ)) +
        ((∑ j : CellIdx m, cellIntra a j v (φ := φ)) + ∫ x, Cr x) := by
    calc
      (∫ x : X N, φ x * (_root_.BoseGases.𝓗 N v φ) x) = ∫ x, (K + P) x := by rw [hnum]
      _ = (∫ x, K x) + ∫ x, P x := by exact integral_add hK hP
      _ = (∑ j : CellIdx m, cellKinetic a j (φ := φ)) + ∫ x, P x := by rw [hkin]
      _ = (∑ j : CellIdx m, cellKinetic a j (φ := φ)) +
            ((∑ j : CellIdx m, cellIntra a j v (φ := φ)) + ∫ x, Cr x) := by rw [hint]
  -- final inequality
  rw [hLHS]
  have hRHS : (∑ j : CellIdx m, cellOpEnergy a j v (φ := φ))
      = (∑ j : CellIdx m, cellKinetic a j (φ := φ)) +
          ∑ j : CellIdx m, cellIntra a j v (φ := φ) := by
    simp [cellOpEnergy, Finset.sum_add_distrib]
  rw [hRHS]
  linarith [hcross]

end BoseGases

end Submission
