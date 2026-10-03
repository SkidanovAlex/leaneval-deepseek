import Mathlib

namespace Work.Pert

/-- Expansion estimate for a map close to the identity: if `Φ` is holomorphic on a convex open
`Q` with `‖Φ' - 1‖ ≤ 1/2` there, then `Φ` is `1/2`-expanding in reverse, i.e.
`‖z - z'‖ ≤ 2 ‖Φ z - Φ z'‖`.  (Used to compare the inverses of two such maps.) -/
theorem inv_close_of_deriv_close {Q : Set ℂ} {Φ : ℂ → ℂ} (hQ : IsOpen Q)
    (hconv : Convex ℝ Q) (hΦ : DifferentiableOn ℂ Φ Q)
    (hder : ∀ v ∈ Q, ‖deriv Φ v - 1‖ ≤ 1 / 2) :
    ∀ z ∈ Q, ∀ z' ∈ Q, ‖z - z'‖ ≤ 2 * ‖Φ z - Φ z'‖ := by
  intro z hz z' hz'
  -- `Φ` is differentiable at every point of the open set `Q`.
  have hdΦ : ∀ v ∈ Q, DifferentiableAt ℂ Φ v := fun v hv => hΦ.differentiableAt (hQ.mem_nhds hv)
  -- Consider `Ψ = Φ - id`; its derivative is `Φ' - 1`, bounded by `1/2` on `Q`.
  have hΨdiff : ∀ v ∈ Q, DifferentiableAt ℂ (Φ - id) v :=
    fun v hv => (hdΦ v hv).sub differentiableAt_id
  have hbound : ∀ v ∈ Q, ‖deriv (Φ - id) v‖ ≤ 1 / 2 := by
    intro v hv
    rw [deriv_sub (hdΦ v hv) differentiableAt_id]
    simpa using hder v hv
  -- Mean value inequality on the convex set `Q`.
  have hmvt :=
    Convex.norm_image_sub_le_of_norm_deriv_le hΨdiff hbound hconv (x := z) (y := z') hz hz'
  have hval : Φ z' - z' - (Φ z - z) = (Φ z' - Φ z) - (z' - z) := by ring
  have h2 : ‖(Φ z' - Φ z) - (z' - z)‖ ≤ 1 / 2 * ‖z' - z‖ := by
    rw [← hval]; exact hmvt
  -- Triangle inequality: `‖z' - z‖ ≤ ‖Φ z' - Φ z‖ + (1/2) ‖z' - z‖`.
  have h3 : ‖z' - z‖ ≤ 1 / 2 * ‖z' - z‖ + ‖Φ z' - Φ z‖ := by
    calc ‖z' - z‖ = ‖(Φ z' - Φ z) - ((Φ z' - Φ z) - (z' - z))‖ := by
          congr 1; ring
      _ ≤ ‖Φ z' - Φ z‖ + ‖(Φ z' - Φ z) - (z' - z)‖ := norm_sub_le _ _
      _ ≤ ‖Φ z' - Φ z‖ + 1 / 2 * ‖z' - z‖ := by linarith
      _ = 1 / 2 * ‖z' - z‖ + ‖Φ z' - Φ z‖ := by ring
  have hkey : (1 / 2) * ‖z' - z‖ ≤ ‖Φ z' - Φ z‖ := by linarith
  calc ‖z - z'‖ = ‖z' - z‖ := norm_sub_rev _ _
    _ = 2 * ((1 / 2) * ‖z' - z‖) := by ring
    _ ≤ 2 * ‖Φ z' - Φ z‖ := by linarith
    _ = 2 * ‖Φ z - Φ z'‖ := by rw [norm_sub_rev (Φ z) (Φ z')]

end Work.Pert
