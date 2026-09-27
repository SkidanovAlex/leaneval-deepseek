import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# A null vector orthogonal to a timelike vector is zero

For the Minkowski form `mink` on `Fin n ⊕ Fin 1 → ℝ` (spatial part of dimension `n`, one time
direction, signature `(n,1)`), the orthogonal complement of a *timelike* vector is spacelike:
if `u` satisfies `⟨u,u⟩ = -1` (in particular `u ≠ 0`) and `w` is both Minkowski-orthogonal to `u`
and null (`⟨w,w⟩ = 0`), then `w = 0`.

The proof is the elementary Cauchy–Schwarz argument.  Write `u = (u_s, u_0)`, `w = (w_s, w_0)`
with `u_s, w_s` the spatial components.  Then
`⟨u,u⟩ = |u_s|² - u_0² = -1`, `⟨w,w⟩ = |w_s|² - w_0² = 0`, `⟨u,w⟩ = u_s ⬝ w_s - u_0 w_0 = 0`, and
Cauchy–Schwarz in `ℝⁿ` gives `(u_s ⬝ w_s)² ≤ |u_s|² |w_s|²`.  Substituting
`u_s ⬝ w_s = u_0 w_0`, `|w_s|² = w_0²` and `|u_s|² = u_0² - 1` yields
`u_0² w_0² ≤ (u_0² - 1) w_0²`, hence `w_0² ≤ 0`, so `w_0 = 0` and then `|w_s|² = 0`.
-/

namespace Work.Mostow

theorem minkNullOrthTimelike {n : ℕ} (u w : Fin n ⊕ Fin 1 → ℝ)
    (hu : Work.Mostow.mink u u = -1) (hwu : Work.Mostow.mink w u = 0)
    (hw : Work.Mostow.mink w w = 0) : w = 0 := by
  -- The time component of `hu`, `hwu`, `hw`, with the spatial sums kept as such.
  have hu' : (∑ i : Fin n, u (Sum.inl i) * u (Sum.inl i))
      = u (Sum.inr 0) * u (Sum.inr 0) - 1 := by
    have h := hu; simp only [Work.Mostow.mink] at h; linarith
  have hwu' : (∑ i : Fin n, w (Sum.inl i) * u (Sum.inl i))
      = w (Sum.inr 0) * u (Sum.inr 0) := by
    have h := hwu; simp only [Work.Mostow.mink] at h; linarith
  have hw' : (∑ i : Fin n, w (Sum.inl i) * w (Sum.inl i))
      = w (Sum.inr 0) * w (Sum.inr 0) := by
    have h := hw; simp only [Work.Mostow.mink] at h; linarith
  -- Cauchy–Schwarz for the spatial parts.
  have hCS : (∑ i : Fin n, w (Sum.inl i) * u (Sum.inl i)) ^ 2 ≤
      (∑ i : Fin n, w (Sum.inl i) * w (Sum.inl i)) *
        (∑ i : Fin n, u (Sum.inl i) * u (Sum.inl i)) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => w (Sum.inl i)) (fun i => u (Sum.inl i))
    simpa only [pow_two] using h
  -- Hence the time component of `w` vanishes.
  have hw0 : w (Sum.inr 0) * w (Sum.inr 0) = 0 := by
    have hcast : (w (Sum.inr 0) * u (Sum.inr 0)) ^ 2 =
        (w (Sum.inr 0) * w (Sum.inr 0)) * (u (Sum.inr 0) * u (Sum.inr 0)) := by ring
    have hle : w (Sum.inr 0) * w (Sum.inr 0) ≤ 0 := by
      have h := hCS
      rw [hwu', hw', hu'] at h
      linarith [h, hcast]
    exact le_antisymm hle (mul_self_nonneg _)
  -- So the spatial part of `w` also vanishes, being a sum of squares equal to zero.
  have hB0 : (∑ i : Fin n, w (Sum.inl i) * w (Sum.inl i)) = 0 := by rw [hw', hw0]
  have hspat : ∀ i : Fin n, w (Sum.inl i) = 0 := by
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w (Sum.inl i) * w (Sum.inl i) :=
      fun i _ => mul_self_nonneg _
    exact fun i => mul_self_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 hB0 i (Finset.mem_univ i))
  funext x
  rcases x with i | j
  · exact hspat i
  · have hj : j = 0 := Subsingleton.elim j 0
    rw [hj]
    exact mul_self_eq_zero.mp hw0

end Work.Mostow
