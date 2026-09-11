import Submission.PfExtra
import Submission.Upper0
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open EquiangularLinesFixedAngle
open Filter
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option maxHeartbeats 1200000

/-! Perron--Frobenius for connected graphs: strictly positive Perron vectors and
simplicity of the spectral-radius eigenspace. -/

open Classical in
/-- The `i`-th entry of `A_G *ᵥ u` sums the neighbours' values. -/
lemma adj_mulVec_apply {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n → ℝ) (i : Fin n) :
    (G.adjMatrix ℝ *ᵥ u) i = ∑ j : Fin n, (if G.Adj i j then u j else 0) := by
  classical
  simp [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply]

open Classical in
open Classical in
/-- if `u_i = 0` for a nonnegative eigenvector, then every neighbour also has value `0`. -/
lemma neighbor_zero_of_eigen {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n → ℝ} {lam : ℝ}
    (hu : ∀ i : Fin n, 0 ≤ u i) (hAu : (G.adjMatrix ℝ) *ᵥ u = lam • u)
    {i j : Fin n} (h0 : u i = 0) (hij : G.Adj i j) : u j = 0 := by
  classical
  have hsum0 : (∑ k : Fin n, (if G.Adj i k then u k else 0)) = 0 := by
    have hrow : ((G.adjMatrix ℝ) *ᵥ u) i = lam * u i := by
      have h := congrFun hAu i
      simpa [Pi.smul_apply] using h
    rw [adj_mulVec_apply] at hrow
    rw [h0] at hrow
    linarith
  have hterm0 : ∀ k : Fin n, (if G.Adj i k then u k else 0) = 0 := by
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin n)))
      (f := fun k : Fin n => (if G.Adj i k then u k else 0))
      (fun x hx => by
        by_cases h : G.Adj i x
        · simp [h, hu x]
        · simp [h])) |>.mp hsum0 k (Finset.mem_univ k)
  have hj := hterm0 j
  by_cases hadj : G.Adj i j
  · simpa [hadj] using hj
  · exfalso
    exact hadj hij

open Classical in
/-- propagation along a walk: if `u_i = 0` then every reachable vertex has value `0`. -/
lemma zero_propagates_walk {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n → ℝ} {lam : ℝ}
    (hu : ∀ i : Fin n, 0 ≤ u i) (hAu : (G.adjMatrix ℝ) *ᵥ u = lam • u)
    {i j : Fin n} (h0 : u i = 0) (p : G.Walk i j) : u j = 0 := by
  induction p with
  | nil => simpa using h0
  | cons h q ih =>
    exact ih (neighbor_zero_of_eigen hu hAu h0 h)

open Classical in
/-- if a graph is connected, a nonnegative eigenvector vanishing anywhere is zero. -/
lemma zero_of_connected_eigen {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n → ℝ} {lam : ℝ}
    (hu : ∀ i : Fin n, 0 ≤ u i) (hAu : (G.adjMatrix ℝ) *ᵥ u = lam • u)
    {i : Fin n} (h0 : u i = 0) (hconn : ∀ a b : Fin n, G.Reachable a b) : u = 0 := by
  classical
  apply funext
  intro j
  rcases hconn i j with ⟨p⟩
  exact zero_propagates_walk hu hAu h0 p

open Classical in
/-- the adjacency matrix of a graph is Hermitian. -/
lemma adjMatrix_isHermitian' {n : ℕ} (G : SimpleGraph (Fin n)) :
    (G.adjMatrix ℝ).IsHermitian := adjMatrix_isHermitian G

open Classical in
/-- A nonzero nonnegative eigenvector of a connected graph is everywhere positive. -/
lemma positive_eigenvector_of_connected {n : ℕ} {G : SimpleGraph (Fin n)}
    (hconn : ∀ i j : Fin n, G.Reachable i j) {u : Fin n → ℝ} {lam : ℝ}
    (hu : ∀ i : Fin n, 0 ≤ u i) (hu0 : u ≠ 0) (hAu : (G.adjMatrix ℝ) *ᵥ u = lam • u) :
    ∀ i : Fin n, 0 < u i := by
  classical
  have hex : ∃ i : Fin n, 0 < u i := by
    by_contra hnot
    have hall : ∀ i : Fin n, u i = 0 := by
      intro i
      by_contra hne
      have hpos : 0 < u i := lt_of_le_of_ne (hu i) (Ne.symm hne)
      exact hnot ⟨i, hpos⟩
    apply hu0
    apply funext
    intro i
    exact hall i
  rcases hex with ⟨i₀, hi₀⟩
  intro i
  by_contra hnot
  have hle : u i ≤ 0 := le_of_not_gt hnot
  have hz : u i = 0 := le_antisymm hle (hu i)
  have hzero : u = 0 := zero_of_connected_eigen hu hAu hz hconn
  have hi₀' : u i₀ = 0 := congrFun hzero i₀
  linarith

/-- `A *ᵥ (v - w) = A *ᵥ v - A *ᵥ w`. -/
lemma mulVec_vector_sub {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
    A *ᵥ (v - w) = A *ᵥ v - A *ᵥ w := by
  classical
  funext i
  simp [Matrix.mulVec, Finset.sum_sub_distrib, sub_mul]

open Classical in
/-- The eigenspace of the adjacency of a connected graph is spanned by any nonzero
nonnegative eigenvector. -/
lemma eigenspace_eq_span_of_positive {n : ℕ} {G : SimpleGraph (Fin n)}
    (hconn : ∀ i j : Fin n, G.Reachable i j) {u : Fin n → ℝ} {lam : ℝ}
    (hu : ∀ i : Fin n, 0 ≤ u i) (hu0 : u ≠ 0) (hAu : (G.adjMatrix ℝ) *ᵥ u = lam • u) :
    ∀ w : Fin n → ℝ, (G.adjMatrix ℝ) *ᵥ w = lam • w → ∃ t : ℝ, w = t • u := by
  classical
  have hu_pos : ∀ i : Fin n, 0 < u i := positive_eigenvector_of_connected hconn hu hu0 hAu
  intro w hw
  by_cases hw0 : w = 0
  · refine ⟨0, ?_⟩
    simp [hw0]
  · have hex : ∃ i : Fin n, 0 < u i := by
      by_contra hnot
      have hall : ∀ i : Fin n, u i = 0 := by
        intro i
        by_contra hne
        have hpos : 0 < u i := lt_of_le_of_ne (hu i) (Ne.symm hne)
        exact hnot ⟨i, hpos⟩
      apply hu0
      apply funext
      intro i
      exact hall i
    rcases hex with ⟨i₀, hi₀⟩
    let S : Finset ℝ := (Finset.univ : Finset (Fin n)).image (fun i : Fin n => w i / u i)
    have hS : S.Nonempty := by
      refine ⟨w i₀ / u i₀, ?_⟩
      exact Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩
    let t : ℝ := S.min' hS
    have hge : ∀ i : Fin n, t ≤ w i / u i := by
      intro i
      exact Finset.min'_le S (w i / u i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hnonneg : ∀ i : Fin n, 0 ≤ w i - t * u i := by
      intro i
      have hupos : 0 < u i := hu_pos i
      have hmul : t * u i ≤ w i := (le_div_iff₀ hupos).mp (hge i)
      exact sub_nonneg.mpr hmul
    have hmm : t ∈ S := S.min'_mem hS
    rcases Finset.mem_image.mp hmm with ⟨j₀, hj₀mem, hj₀t⟩
    have hz : (w - t • u) j₀ = 0 := by
      dsimp
      have hupos : 0 < u j₀ := hu_pos j₀
      rw [← hj₀t]
      field_simp [ne_of_gt hupos]
      ring
    have hz_eigen : (G.adjMatrix ℝ) *ᵥ (w - t • u) = lam • (w - t • u) := by
      calc
        (G.adjMatrix ℝ) *ᵥ (w - t • u)
            = (G.adjMatrix ℝ) *ᵥ w - (G.adjMatrix ℝ) *ᵥ (t • u) := by rw [mulVec_vector_sub]
        _ = lam • w - t • (lam • u) := by
              rw [hw, Matrix.mulVec_smul, hAu]
        _ = lam • (w - t • u) := by
              funext a
              simp [Pi.smul_apply]
              ring
    have hzero : w - t • u = 0 := zero_of_connected_eigen hnonneg hz_eigen hz hconn
    refine ⟨t, ?_⟩
    exact sub_eq_zero.mp hzero

end Submission
