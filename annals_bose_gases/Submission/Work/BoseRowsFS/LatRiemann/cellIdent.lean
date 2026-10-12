import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS.LatRiemann

/-- Exact second-order expansion of `1/‖p‖²` about the lattice point `P` (with `a = ‖P‖`):

    1/‖p‖² - 1/a² = -2⟨P, p-P⟩/a⁴ + (2⟨P,p-P⟩(‖p‖²-a²) - a²‖p-P‖²)/(a⁴‖p‖²).

The cross term `⟨P, p-P⟩` carries the first-order part; the remaining terms are exactly the
second-order remainder. This is the algebraic identity behind Step 3b of the lattice-Riemann
core (`FINDING_lattice_riemann_core.md`). -/
theorem cellIdent {P p : EuclideanSpace ℝ (Fin 3)} {a : ℝ} (ha : a = ‖P‖) (ha0 : 0 < a)
    (hp0 : 0 < ‖p‖) :
    1 / ‖p‖ ^ 2 - 1 / a ^ 2
      = -2 * inner ℝ P (p - P) / a ^ 4
        + (2 * inner ℝ P (p - P) * (‖p‖ ^ 2 - a ^ 2) - a ^ 2 * ‖p - P‖ ^ 2)
            / (a ^ 4 * ‖p‖ ^ 2) := by
  -- The exact value of the displacement term: `‖p-P‖² = ‖p‖² - 2⟨P,p-P⟩ - a²`.
  have hd : ‖p - P‖ ^ 2 = ‖p‖ ^ 2 - 2 * inner ℝ P (p - P) - a ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm P p, inner_sub_right, real_inner_self_eq_norm_sq,
      ← ha]
    ring
  rw [hd]
  have h0 : a ≠ 0 := ne_of_gt ha0
  have h1 : ‖p‖ ≠ 0 := ne_of_gt hp0
  field_simp
  ring

end Work.BoseRowsFS.LatRiemann
