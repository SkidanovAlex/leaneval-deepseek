import Mathlib
import Submission.Work.Peluse.Ulower.ss_char_dilate

namespace Work.Peluse.Ulower

theorem char_dilate_le {c : ℤ} (hc : c ≠ 0) {F : ℤ → ℂ}
    (hF : Summable fun x : ℤ => ‖F x‖) (r : ℕ) (hr : r < c.natAbs) (β : ℝ) :
    ∃ ξ : ℝ,
      ‖∑' z : ℤ, F (c * (z : ℤ) + (r : ℤ)) * Work.Peluse.ee (β * (z : ℝ))‖ ≤
        ‖∑' x : ℤ, F x * Work.Peluse.ee (ξ * (x : ℝ))‖ :=
  ss_char_dilate hc hF r hr β

end Work.Peluse.Ulower
