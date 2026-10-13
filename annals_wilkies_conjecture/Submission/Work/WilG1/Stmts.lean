import Submission.Work.WilG1.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Classical Filter Topology

namespace Work.WilG1

open WilkiesDesign WilkiesConjecture

/-! Statements planned for delegation (checked here for elaboration only). -/

theorem reindex_mem {S : SOMin} {m n : ℕ} (σ : Fin n → Fin m)
    {a D : ℕ} {b : Polynomial ℕ} {X : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a (b.eval D) n) :
    {z : Fin m → ℝ | z ∘ σ ∈ X} ∈ S.Ω (a + n + 2 * m + 3) ((b + Polynomial.C n).eval D) m := by
  sorry

theorem lt_mem {S : SOMin} {n : ℕ} (D : ℕ) (i j : Fin n) :
    {x : Fin n → ℝ | x i < x j} ∈ S.Ω (n + 3) ((Polynomial.C 3).eval D) n := by
  sorry

theorem le_mem {S : SOMin} {n : ℕ} (D : ℕ) (i j : Fin n) :
    {x : Fin n → ℝ | x i ≤ x j} ∈ S.Ω (n + 4) ((Polynomial.C 4).eval D) n := by
  sorry

theorem closure_mem {S : SOMin} {n : ℕ} {a D : ℕ} {b : Polynomial ℕ} {X : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a (b.eval D) n) :
    closure X ∈ S.Ω (a + 3 * n + 12) ((Polynomial.C 8 * b + Polynomial.C 40).eval D) n := by
  sorry

theorem interior_mem {S : SOMin} {n : ℕ} {a D : ℕ} {b : Polynomial ℕ} {X : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a (b.eval D) n) :
    interior X ∈ S.Ω (a + 3 * n + 14) ((Polynomial.C 8 * b + Polynomial.C 40).eval D) n := by
  sorry

theorem supBall_mem {S : SOMin} {n : ℕ} (D : ℕ) :
    {z : Fin (n + 1) → ℝ | ∀ i : Fin n, z (Fin.castSucc i) ^ 2 < z (Fin.last n) ^ 2} ∈
      S.Ω (n + 4) ((Polynomial.C 4).eval D) (n + 1) := by
  sorry

theorem finite_of_interior_empty {S : SOMin} {a D : ℕ} {b : Polynomial ℕ}
    {A : Set (Fin 1 → ℝ)} (hA : A ∈ S.Ω a (b.eval D) 1) (hint : interior A = ∅) :
    A.Finite := by
  sorry

theorem no_strictLocalMax_interval {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hcont : ∀ x ∈ I, ContinuousAt f x)
    (hmax : ∀ x ∈ I, ∃ δ > 0, ∀ y, y ≠ x → |y - x| < δ → f y < f x) :
    I.Subsingleton := by
  sorry

theorem no_deriv_atTop_interval {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hcont : ∀ x ∈ I, ContinuousAt f x)
    (hlim : ∀ x ∈ I, Tendsto (fun y : ℝ => (f y - f x) / (y - x)) (𝓝[≠] x) atTop) :
    I.Subsingleton := by
  sorry

end Work.WilG1
