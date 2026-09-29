import Mathlib
import Submission.CDTPlan.InterfacesA

/-!
# Area `Ψ_A`: shared algebra for the slit and lune maps

Elementary (`ring`-level) algebra underlying the contour map
`ψ_A = -(4/5) · lune (36/5) (-(slitsA ·))` of Calegari--Dimitrov--Tang (arXiv:2408.15403,
eq. (slit) and eq. (firstgobble)), for use by the analytic lemmas on `slit` and `lune`.

For the slit map the two key facts are the *Joukowski relation*
`slit r z + (slit r z)⁻¹ = alpha (z + z⁻¹) + beta` (`slit_joukowski_ab`) and the
factorization `slit r z = z * G z` (`slit_mul`), which makes the removable singularity at
`0` explicit.  For the lune map they are the quadratic relation `lune_quad` together with
`luneF_lune` / `norm_luneF` for the inverse rational map `luneF c w = w(B + Cw)/(C + Bw)`.
-/

namespace Work.APsi

open Submission.CDTPlan Complex
open scoped ComplexConjugate

noncomputable section

/-- `‖rot t‖ = 1`. -/
theorem norm_rot (t : ℝ) : ‖rot t‖ = 1 := by
  rw [rot, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

theorem rot_ne_zero (t : ℝ) : rot t ≠ 0 := by
  intro h
  have := norm_rot t
  rw [h] at this
  simp at this

/-- `(w^{1/2})^2 = w` for the principal square root. -/
theorem cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  rw [one_div]
  exact Complex.cpow_nat_inv_pow _ (by norm_num)

/-- `(x^2)^{1/2} = x` for a positive real `x`. -/
theorem cpow_half_sq_of_pos {x : ℝ} (hx : 0 < x) :
    (((x : ℂ)) ^ 2) ^ (1 / 2 : ℂ) = (x : ℂ) := by
  have h : (1 / 2 : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  rw [h]
  exact Complex.sq_cpow_two_inv (by simpa using hx)

/-! ## The slit map -/

/-- `(1+r)² - 2(r-1)²z + (1+r)²z²`, the Joukowski numerator of the slit map. -/
def slitP (r : ℝ) (z : ℂ) : ℂ :=
  (1 + (r : ℂ)) ^ 2 - 2 * ((r : ℂ) - 1) ^ 2 * z + (1 + (r : ℂ)) ^ 2 * z ^ 2

/-- The radicand `(1+r)² - 2(1-6r+r²)z + (1+r)²z²` of the slit map. -/
def slitQ (r : ℝ) (z : ℂ) : ℂ :=
  (1 + (r : ℂ)) ^ 2 - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2) * z + (1 + (r : ℂ)) ^ 2 * z ^ 2

/-- `(1+r)(z-1)√(Q z)`. -/
def slitR (r : ℝ) (z : ℂ) : ℂ :=
  (1 + (r : ℂ)) * (z - 1) * (slitQ r z) ^ (1 / 2 : ℂ)

/-- The numerator of the slit map. -/
def slitN (r : ℝ) (z : ℂ) : ℂ := slitP r z + slitR r z

/-- The formula for `slit` away from `0`. -/
theorem slit_eq_formula (r : ℝ) (z : ℂ) (hz : z ≠ 0) :
    slit r z = slitN r z / (8 * (r : ℂ) * z) := by
  rw [slit, if_neg hz]
  simp only [slitN, slitP, slitR, slitQ]

/-- The key polynomial identity behind the slit map. -/
theorem slitKey (r : ℝ) (z : ℂ) :
    slitP r z ^ 2 - (1 + (r : ℂ)) ^ 2 * (z - 1) ^ 2 * slitQ r z = (8 * (r : ℂ) * z) ^ 2 := by
  simp only [slitP, slitQ]
  ring

theorem slitR_sq (r : ℝ) (z : ℂ) :
    (slitR r z) ^ 2 = (1 + (r : ℂ)) ^ 2 * (z - 1) ^ 2 * slitQ r z := by
  simp only [slitR]
  rw [mul_pow, mul_pow, cpow_half_sq]

/-- `n ^2 - 2 P n + (8rz)^2 = 0` for the numerator `n` of the slit map. -/
theorem slitN_quad (r : ℝ) (z : ℂ) :
    slitN r z ^ 2 - 2 * slitP r z * slitN r z + (8 * (r : ℂ) * z) ^ 2 = 0 := by
  have hsq := slitR_sq r z
  have hkey := slitKey r z
  simp only [slitN]
  linear_combination -hkey + hsq

theorem slit8_ne_zero (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) :
    (8 * (r : ℂ) * z) ≠ 0 := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  intro h
  rcases mul_eq_zero.mp h with h1 | h2
  · rcases mul_eq_zero.mp h1 with h3 | h4
    · exact absurd h3 (by norm_num)
    · exact hrC h4
  · exact hz h2

/-- **Joukowski relation** for the slit map, division-free form. Only `(√Q)² = Q` is used. -/
theorem slit_quad (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) :
    (slit r z) ^ 2 - (slitP r z / (4 * (r : ℂ) * z)) * slit r z + 1 = 0 := by
  have h8 := slit8_ne_zero r hr z hz
  have hN := slitN_quad r z
  rw [slit_eq_formula r z hz]
  rw [show (slitN r z / (8 * (r : ℂ) * z)) ^ 2
        - (slitP r z / (4 * (r : ℂ) * z)) * (slitN r z / (8 * (r : ℂ) * z)) + 1
      = (slitN r z ^ 2 - 2 * slitP r z * slitN r z + (8 * (r : ℂ) * z) ^ 2)
          / (8 * (r : ℂ) * z) ^ 2 from by
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    field_simp [hrC]
    ring]
  rw [hN]
  exact zero_div _

theorem slit_ne_zero (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) : slit r z ≠ 0 := by
  intro h0
  have h := slit_quad r hr z hz
  rw [h0] at h
  norm_num at h

/-- `R z - P z` at `z = 0`. -/
theorem slitR0 (r : ℝ) (hr : 0 < r) : slitR r 0 - slitP r 0 = -2 * (1 + (r : ℂ)) ^ 2 := by
  have hQ0 : slitQ r 0 = (1 + (r : ℂ)) ^ 2 := by simp only [slitQ]; ring
  have hsq : (((1 + (r : ℂ)) ^ 2) ^ (1 / 2 : ℂ)) = (1 + (r : ℂ)) := by
    have hB : (1 + (r : ℂ)) = ((1 + r : ℝ) : ℂ) := by push_cast; ring
    rw [hB]
    exact cpow_half_sq_of_pos (by linarith)
  simp only [slitR, slitP]
  rw [hQ0, hsq]
  ring

/-- `R z - P z ≠ 0` for every `z` (its value at `z = 0` is `-2(1+r)^2 ≠ 0`). -/
theorem slitRP_ne (r : ℝ) (hr : 0 < r) (z : ℂ) : slitR r z - slitP r z ≠ 0 := by
  intro h
  have hn : slitN r z = 2 * slitP r z := by
    simp only [slitN]
    rw [sub_eq_zero.mp h]
    ring
  have hz : z = 0 := by
    have hquad := slitN_quad r z
    rw [hn] at hquad
    have h8 : (8 * (r : ℂ) * z) = 0 := by
      have : (8 * (r : ℂ) * z) ^ 2 = 0 := by linear_combination hquad
      exact sq_eq_zero_iff.mp this
    rcases mul_eq_zero.mp h8 with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 (by norm_num)
      · exact absurd h4 (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
    · exact h2
  subst hz
  rw [slitR0 r hr] at h
  have h2 : (2 : ℂ) * (1 + (r : ℂ)) ^ 2 = 0 := by linear_combination -h
  have h3 : (1 : ℂ) + (r : ℂ) = 0 := by
    have h4 : (1 + (r : ℂ)) ^ 2 = 0 := (mul_eq_zero.mp h2).resolve_left (by norm_num)
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h4
  have h5 : (1 : ℝ) + r = 0 := by
    apply Complex.ofReal_injective
    push_cast
    exact h3
  linarith

/-- **The removable-singularity factorization** `slit r z = z * G z` with
`G z = -8r/(R z - P z)`, holomorphic and non-vanishing near the origin. -/
theorem slit_mul (r : ℝ) (hr : 0 < r) (z : ℂ) :
    slit r z = z * (-8 * (r : ℂ) / (slitR r z - slitP r z)) := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    simp [slit]
  · have hRP := slitRP_ne r hr z
    have h8 := slit8_ne_zero r hr z hz
    have hn : slitN r z * (slitR r z - slitP r z) = -((8 * (r : ℂ) * z) ^ 2) := by
      have hquad := slitN_quad r z
      have : slitN r z - 2 * slitP r z = slitR r z - slitP r z := by
        simp only [slitN]; ring
      calc slitN r z * (slitR r z - slitP r z)
          = slitN r z * (slitN r z - 2 * slitP r z) := by rw [this]
        _ = -((8 * (r : ℂ) * z) ^ 2) := by
              have hq2 : slitN r z * (slitN r z - 2 * slitP r z)
                  = -((8 * (r : ℂ) * z) ^ 2) := by linear_combination hquad
              exact hq2
    rw [slit_eq_formula r z hz]
    rw [show z * (-8 * (r : ℂ) / (slitR r z - slitP r z))
        = (z * (-8 * (r : ℂ))) / (slitR r z - slitP r z) from by ring]
    rw [div_eq_div_iff h8 hRP]
    linear_combination hn

/-- The Joukowski relation in `P`-form. -/
theorem slit_joukowski (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) :
    slit r z + (slit r z)⁻¹ = slitP r z / (4 * (r : ℂ) * z) := by
  have hq := slit_quad r hr z hz
  have hne := slit_ne_zero r hr z hz
  have hww : slit r z * (slit r z)⁻¹ = 1 := mul_inv_cancel₀ hne
  have h : slit r z * (slit r z + (slit r z)⁻¹ - slitP r z / (4 * (r : ℂ) * z)) = 0 := by
    have h1 : slit r z * (slit r z + (slit r z)⁻¹ - slitP r z / (4 * (r : ℂ) * z))
        = slit r z ^ 2 - (slitP r z / (4 * (r : ℂ) * z)) * slit r z + 1 := by
      rw [show slit r z * (slit r z + (slit r z)⁻¹ - slitP r z / (4 * (r : ℂ) * z))
          = slit r z * slit r z + slit r z * (slit r z)⁻¹
            - slit r z * (slitP r z / (4 * (r : ℂ) * z)) from by ring]
      rw [hww]
      ring
    rw [h1, hq]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne)

/-- The Joukowski relation in the `alpha (z + z⁻¹) + beta` form. -/
theorem slit_joukowski_ab (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) :
    slit r z + (slit r z)⁻¹ =
      ((1 + r) ^ 2 / (4 * r)) * (z + z⁻¹) - ((r - 1) ^ 2 / (2 * r)) := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hzC : z ≠ 0 := hz
  rw [slit_joukowski r hr z hz]
  simp only [slitP]
  field_simp
  push_cast
  ring

/-! ## The lune map -/

/-- `1 + c²`. -/
def luneBr (c : ℝ) : ℝ := 1 + c ^ 2
/-- `c² - 1`. -/
def luneCr (c : ℝ) : ℝ := c ^ 2 - 1
/-- `B = 1 + c²`. -/
def luneB (c : ℝ) : ℂ := (luneBr c : ℂ)
/-- `C = c² - 1`. -/
def luneC (c : ℝ) : ℂ := (luneCr c : ℂ)
/-- The radicand `B²(1+z)² - 16c²z` of the lune map. -/
def luneR (c : ℝ) (z : ℂ) : ℂ := (1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z

/-- The inverse rational map `w ↦ w(B + Cw)/(C + Bw)` of the lune. -/
def luneF (c : ℝ) (w : ℂ) : ℂ := w * (luneB c + luneC c * w) / (luneC c + luneB c * w)

theorem lune_eq (c : ℝ) (z : ℂ) :
    lune c z = (z * luneB c - luneB c + (luneR c z) ^ (1 / 2 : ℂ)) / (2 * luneC c) := by
  simp only [lune, luneB, luneC, luneR, luneBr, luneCr]
  push_cast
  ring

theorem luneBr_pos (c : ℝ) : 0 < luneBr c := by simp only [luneBr]; positivity

theorem luneCr_pos {c : ℝ} (hc : 1 < c) : 0 < luneCr c := by simp only [luneCr]; nlinarith

theorem luneB_ne_zero (c : ℝ) : luneB c ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (luneBr_pos c))

theorem luneC_ne_zero {c : ℝ} (hc : 1 < c) : luneC c ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (luneCr_pos hc))

theorem lune_zero (c : ℝ) : lune c 0 = 0 := by
  rw [lune_eq]
  have hR0 : luneR c 0 = (1 + (c : ℂ) ^ 2) ^ 2 := by simp only [luneR]; ring
  rw [hR0]
  have hsq : (((1 + (c : ℂ) ^ 2) ^ 2) ^ (1 / 2 : ℂ)) = (1 + (c : ℂ) ^ 2) := by
    have hB : (1 + (c : ℂ) ^ 2) = ((1 + c ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hB]
    exact cpow_half_sq_of_pos (by positivity)
  rw [hsq]
  have hnum : 0 * luneB c - luneB c + (1 + (c : ℂ) ^ 2) = 0 := by
    simp only [luneB, luneBr]
    push_cast
    ring
  rw [hnum]
  exact zero_div _

/-- **Quadratic relation** for the lune map. Only `(√R)² = R` is used. -/
theorem lune_quad (c : ℝ) (hc : 1 < c) (z : ℂ) :
    luneC c * (lune c z) ^ 2 + luneB c * (1 - z) * lune c z - luneC c * z = 0 := by
  have hC := luneC_ne_zero hc
  have hsq : ((luneR c z) ^ (1 / 2 : ℂ)) ^ 2 = luneR c z := cpow_half_sq _
  have h2C : 2 * luneC c * lune c z = (luneR c z) ^ (1 / 2 : ℂ) - luneB c * (1 - z) := by
    rw [lune_eq]
    field_simp
    ring
  have hmain : luneR c z - (luneB c * (1 - z)) ^ 2 - 4 * (luneC c) ^ 2 * z = 0 := by
    simp only [luneR, luneB, luneC, luneBr, luneCr]
    push_cast
    ring
  have h4 : (4 * luneC c) * (luneC c * (lune c z) ^ 2 + luneB c * (1 - z) * lune c z
      - luneC c * z) = 0 := by
    calc (4 * luneC c) * (luneC c * (lune c z) ^ 2 + luneB c * (1 - z) * lune c z
            - luneC c * z)
        = ((luneR c z) ^ (1 / 2 : ℂ) - luneB c * (1 - z)) ^ 2
          + 2 * luneB c * (1 - z) * ((luneR c z) ^ (1 / 2 : ℂ) - luneB c * (1 - z))
          - 4 * (luneC c) ^ 2 * z := by
            rw [← h2C]; ring
      _ = ((luneR c z) ^ (1 / 2 : ℂ)) ^ 2 - (luneB c * (1 - z)) ^ 2
          - 4 * (luneC c) ^ 2 * z := by ring
      _ = luneR c z - (luneB c * (1 - z)) ^ 2 - 4 * (luneC c) ^ 2 * z := by rw [hsq]
      _ = 0 := hmain
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by simp [hC])
  · exact h

/-- The denominator `C + B w` of `luneF` does not vanish at `w = lune c z`. -/
theorem lune_pole_ne (c : ℝ) (hc : 1 < c) (z : ℂ) : luneC c + luneB c * lune c z ≠ 0 := by
  intro h
  have hB := luneB_ne_zero c
  have hw : lune c z = -luneC c / luneB c := by
    field_simp
    linear_combination h
  have hq := lune_quad c hc z
  rw [hw] at hq
  field_simp at hq
  have hCB : luneC c ^ 3 - luneC c * luneB c ^ 2 ≠ 0 := by
    have hval : luneC c ^ 3 - luneC c * luneB c ^ 2 = ((-4 * c ^ 2 * (c ^ 2 - 1) : ℝ) : ℂ) := by
      simp only [luneC, luneB, luneBr, luneCr]
      push_cast
      ring
    rw [hval]
    exact Complex.ofReal_ne_zero.mpr (by
      have h1 : (0 : ℝ) < c ^ 2 - 1 := by nlinarith
      positivity)
  exact hCB (by linear_combination hq)

/-- `luneF` is a left inverse of `lune`. -/
theorem luneF_lune (c : ℝ) (hc : 1 < c) (z : ℂ) : luneF c (lune c z) = z := by
  have hq := lune_quad c hc z
  have hne := lune_pole_ne c hc z
  have h' : lune c z * (luneB c + luneC c * lune c z) = z * (luneC c + luneB c * lune c z) := by
    linear_combination hq
  rw [luneF, div_eq_iff hne]
  linear_combination h'

/-- `luneF` maps the unit circle to itself. -/
theorem norm_luneF (c : ℝ) (hc : 1 < c) {w : ℂ} (hw : ‖w‖ = 1) : ‖luneF c w‖ = 1 := by
  have hmul : w * conj w = 1 := by
    rw [Complex.mul_conj]
    have : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw]; norm_num
    rw [this]
    norm_num
  have hden : luneC c + luneB c * w = w * conj (luneB c + luneC c * w) := by
    have h1 : luneC c + luneB c * w = w * (luneB c + luneC c * conj w) := by
      calc luneC c + luneB c * w = luneC c * (w * conj w) + luneB c * w := by rw [hmul]; ring
        _ = w * (luneB c + luneC c * conj w) := by ring
    rw [h1]
    congr 1
    simp only [luneB, luneC, map_add, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  have hnorm : ‖luneC c + luneB c * w‖ = ‖luneB c + luneC c * w‖ := by
    rw [hden, norm_mul, hw, one_mul, Complex.norm_conj]
  have hne : luneC c + luneB c * w ≠ 0 := by
    intro h
    have h1 : luneC c = -(luneB c * w) := by linear_combination h
    have hns : Complex.normSq (luneC c) = Complex.normSq (luneB c) := by
      rw [h1, Complex.normSq_neg, map_mul]
      have : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw]; norm_num
      rw [this, mul_one]
    simp only [luneC, luneB, Complex.normSq_ofReal] at hns
    simp only [luneCr, luneBr] at hns
    nlinarith [hc]
  have hne2 : ‖luneB c + luneC c * w‖ ≠ 0 := by
    rw [← hnorm]
    exact norm_ne_zero_iff.mpr hne
  rw [luneF, norm_div, norm_mul, hnorm, hw, one_mul, div_self hne2]

end

end Work.APsi
