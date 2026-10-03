import Mathlib

/-!
# Elementary facts about the Cayley transform `E ↦ (E - 1)/(E + 1)`

For `E + 1 ≠ 0` (so that the transform is defined) we record the two identities

* `1 - ‖(E - 1)/(E + 1)‖^2 = 4 Re E / ‖E + 1‖^2` (the "hyperbolic" form of the Poincaré
  metric inequality), obtained by writing both squared moduli as `re^2 + im^2`;
* `0 ≤ Re E → ‖(E - 1)/(E + 1)‖ ≤ 1`, i.e. the right half-plane is mapped into the closed
  unit disc.

Both are immediate from `‖E ± 1‖^2 = (Re E ± 1)^2 + (Im E)^2` and `‖(E-1)/(E+1)‖^2 =
‖E-1‖^2/‖E+1‖^2`.
-/

namespace Work.Pert.Strip

theorem cayley_facts {E : ℂ} (hE : E + 1 ≠ 0) :
    (1 - ‖(E - 1) / (E + 1)‖ ^ 2 = 4 * E.re / ‖E + 1‖ ^ 2) ∧
    (0 ≤ E.re → ‖(E - 1) / (E + 1)‖ ≤ 1) := by
  have hnorm : ‖E + 1‖ ≠ 0 := norm_ne_zero_iff.mpr hE
  have hden : ‖E + 1‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm
  have hp : ‖E + 1‖ ^ 2 = (E.re + 1) ^ 2 + E.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im]
    ring
  have hm : ‖E - 1‖ ^ 2 = (E.re - 1) ^ 2 + E.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im]
    ring
  have hden' : (E.re + 1) ^ 2 + E.im ^ 2 ≠ 0 := by rw [← hp]; exact hden
  have hkey : 1 - ‖(E - 1) / (E + 1)‖ ^ 2 = 4 * E.re / ‖E + 1‖ ^ 2 := by
    rw [norm_div, div_pow, hp, hm]
    field_simp
    ring
  refine ⟨hkey, fun hre => ?_⟩
  have hle : ‖(E - 1) / (E + 1)‖ ^ 2 ≤ 1 := by
    have h0 : 0 ≤ 4 * E.re / ‖E + 1‖ ^ 2 :=
      div_nonneg (by linarith) (by positivity)
    linarith [hkey]
  have habs := (sq_le_one_iff_abs_le_one (‖(E - 1) / (E + 1)‖)).mp hle
  rwa [abs_of_nonneg (norm_nonneg ((E - 1) / (E + 1)))] at habs

end Work.Pert.Strip
