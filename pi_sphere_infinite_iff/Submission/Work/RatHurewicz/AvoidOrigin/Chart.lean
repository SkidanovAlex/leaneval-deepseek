import Mathlib
import Submission.Work.RatHurewicz.AvoidOrigin.Class

/-!
# The chart of a cell of the cycle model

For a cell `(i,S)` of `Model D` with `2 < S.card` and a representative `x₀` of a point of its open
cell (`ptSupport x₀ = S`), this module sets up the *chart*: the ball of radius
`ε = ½ · min {x₀ t : t ∈ S}` around `x₀` inside the face spanned by `S` (which is a convex subset
of the simplex all of whose points have support exactly `S`), and its image in `Model D` under
`y ↦ Quotient.mk'' (Sum.inl ⟨i, y⟩)`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.AvoidOrigin

open Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The smallest coordinate of `x₀` on the finset `S`. -/
def minCoord (S : Finset (Fin (n + 2))) (x₀ : stdSimplex ℝ (Fin (n + 2))) (hS : 2 < S.card) : ℝ :=
  S.inf' (Finset.card_pos.mp (by omega)) fun t => (x₀ : Fin (n + 2) → ℝ) t

/-- The radius of the chart: half the smallest coordinate of `x₀` on `S`. -/
def eps (S : Finset (Fin (n + 2))) (x₀ : stdSimplex ℝ (Fin (n + 2))) (hS : 2 < S.card) : ℝ :=
  minCoord S x₀ hS / 2

/-- The closed chart ball: the points of the simplex with support contained in `S` at distance at
most `eps` from `x₀`. -/
def chartBall (S : Finset (Fin (n + 2))) (x₀ : stdSimplex ℝ (Fin (n + 2))) (hS : 2 < S.card) :
    Set (stdSimplex ℝ (Fin (n + 2))) :=
  {y | (∀ t ∉ S, (y : Fin (n + 2) → ℝ) t = 0) ∧
    ‖(y : Fin (n + 2) → ℝ) - (x₀ : Fin (n + 2) → ℝ)‖ ≤ eps S x₀ hS}

/-- The open chart ball. -/
def chartBallOpen (S : Finset (Fin (n + 2))) (x₀ : stdSimplex ℝ (Fin (n + 2)))
    (hS : 2 < S.card) : Set (stdSimplex ℝ (Fin (n + 2))) :=
  {y | (∀ t ∉ S, (y : Fin (n + 2) → ℝ) t = 0) ∧
    ‖(y : Fin (n + 2) → ℝ) - (x₀ : Fin (n + 2) → ℝ)‖ < eps S x₀ hS}

/-- The chart map of the cell `i`. -/
def chartMap {n : ℕ} (D : MData X n x₀) (i : D.Idx) :
    stdSimplex ℝ (Fin (n + 2)) → Model D :=
  fun y => Quotient.mk'' (Sum.inl (⟨i, y⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))))

/-- The chart neighbourhood `V` of the origin of the cell. -/
def chartNhd (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (x : stdSimplex ℝ (Fin (n + 2))) (hS : 2 < S.card) : Set (Model D) :=
  chartMap D i '' chartBallOpen S x hS

/-- The closure `V̄` of the chart neighbourhood: the image of the closed chart ball. -/
def chartNhdClosure (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (x : stdSimplex ℝ (Fin (n + 2))) (hS : 2 < S.card) : Set (Model D) :=
  chartMap D i '' chartBall S x hS

end

end Work.RatHurewicz.AvoidOrigin

namespace Work.RatHurewicz.AvoidOrigin

open Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

theorem minCoord_pos {S : Finset (Fin (n + 2))} {x : stdSimplex ℝ (Fin (n + 2))}
    (hx : ptSupport x = S) (hS : 2 < S.card) : 0 < minCoord S x hS := by
  rw [minCoord, Finset.lt_inf'_iff]
  intro t ht
  have hne : (x : Fin (n + 2) → ℝ) t ≠ 0 := mem_ptSupport.mp (hx ▸ ht)
  exact lt_of_le_of_ne (x.2.1 t) (Ne.symm hne)

theorem eps_pos {S : Finset (Fin (n + 2))} {x : stdSimplex ℝ (Fin (n + 2))}
    (hx : ptSupport x = S) (hS : 2 < S.card) : 0 < eps S x hS := by
  rw [eps]
  linarith [minCoord_pos hx hS]

theorem support_of_mem_chartBall {S : Finset (Fin (n + 2))} {x : stdSimplex ℝ (Fin (n + 2))}
    (hx : ptSupport x = S) (hS : 2 < S.card) {y : stdSimplex ℝ (Fin (n + 2))}
    (hy : y ∈ chartBall S x hS) : ptSupport y = S := by
  obtain ⟨hy0, hynorm⟩ := hy
  have hle : ∀ t ∈ S, (x : Fin (n + 2) → ℝ) t ≤ ‖(y : Fin (n + 2) → ℝ) - (x : Fin (n + 2) → ℝ)‖
      + (y : Fin (n + 2) → ℝ) t := by
    intro t _
    have h : |(y : Fin (n + 2) → ℝ) t - (x : Fin (n + 2) → ℝ) t| ≤
        ‖(y : Fin (n + 2) → ℝ) - (x : Fin (n + 2) → ℝ)‖ := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm ((y : Fin (n + 2) → ℝ)
        - (x : Fin (n + 2) → ℝ)) t
    rw [abs_le] at h
    linarith [h.1]
  ext t
  rw [mem_ptSupport]
  constructor
  · intro h
    by_contra ht
    exact h (hy0 t ht)
  · intro ht
    have hb : ‖(y : Fin (n + 2) → ℝ) - (x : Fin (n + 2) → ℝ)‖ <
        (x : Fin (n + 2) → ℝ) t := by
      have hlt : minCoord S x hS ≤ (x : Fin (n + 2) → ℝ) t := Finset.inf'_le _ ht
      have h2 : ‖(y : Fin (n + 2) → ℝ) - (x : Fin (n + 2) → ℝ)‖ ≤ minCoord S x hS / 2 := by
        rw [← eps]
        exact hynorm
      have := minCoord_pos hx hS
      linarith
    intro hyz
    have hcon := hle t ht
    rw [hyz, add_zero] at hcon
    linarith

end

end Work.RatHurewicz.AvoidOrigin
