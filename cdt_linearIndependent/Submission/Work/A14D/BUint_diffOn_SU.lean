import Mathlib
import Submission.Work.A14D.BU_defs

/-!
# `Work.A14D.BUint_diffOn_SU`

The integrand of the `i`-th integral slot of `BU`,

`BUint a b c HU HL i z = dyC z · (yC z)⁻¹ ^ i · (HU z + HL (wC z) − GjetA a b c i z)`,

is holomorphic on the half plane `SU` as soon as `HU` is holomorphic on `SU` and `HL` is
holomorphic on `SL`.  Indeed

* `dyC` and `yC` are rational with their only pole at `1`, and `1 ∉ SU`; `yC` has its only zero
  at `0`, and `0 ∉ SU`, so `dyC` and `(yC ·)⁻¹` are holomorphic on `SU`;
* the deck involution `wC z = z/(z−1) = 1 + (z−1)⁻¹` maps `SU` into `SL`
  (`8·Im(w z) + 1 < Re(w z)` is literally the defining inequality `1 < 8·Im z + Re z` of `SU`),
  so `HL ∘ wC` is holomorphic on `SU` by `hHL`;
* `GjetA a b c i` is the finite sum `Σ_{n<i} [yⁿ]G · y(z)ⁿ`, a polynomial in `yC`.
-/

namespace Work.A14D

open Complex Metric

noncomputable section

/-! ## 1. The elementary functions on `SU` -/

/-- `dyC z = y'(z) = (z²−2z)/(z−1)²` is holomorphic on `SU`, which avoids its pole `1`. -/
private lemma dyC_diffOn_SU : DifferentiableOn ℂ dyC SU := by
  unfold dyC
  exact ((differentiableOn_id.pow 2).sub (differentiableOn_const 2 |>.mul differentiableOn_id)).div
    ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    (fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr (fun h => one_notMem_SU (h ▸ hz))))

/-- `yC z = z²/(z−1)` is holomorphic on `SU`. -/
private lemma yC_diffOn_SU : DifferentiableOn ℂ yC SU := by
  unfold yC
  exact (differentiableOn_id.pow 2).div (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz => sub_ne_zero.mpr (fun h => one_notMem_SU (h ▸ hz)))

/-- `wC z = z/(z−1)` is holomorphic on `SU`, which avoids its pole `1`. -/
private lemma wC_diffOn_SU : DifferentiableOn ℂ wC SU := by
  unfold wC
  exact differentiableOn_id.div (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz => sub_ne_zero.mpr (fun h => one_notMem_SU (h ▸ hz)))

/-- `yC` does not vanish on `SU` (its only zero is `0 ∉ SU`). -/
private lemma yC_ne_zero_of_mem_SU {z : ℂ} (hz : z ∈ SU) : yC z ≠ 0 := by
  intro h
  have h1 : z ≠ 1 := fun hz1 => one_notMem_SU (hz1 ▸ hz)
  have hh : z ^ 2 = 0 := by
    have hh := h
    rw [yC] at hh
    field_simp at hh
    simpa using hh
  exact zero_notMem_SU ((sq_eq_zero_iff.mp hh) ▸ hz)

/-- `(yC ·)⁻¹ ^ j` is holomorphic on `SU`. -/
private lemma yC_inv_pow_diffOn_SU (j : ℕ) :
    DifferentiableOn ℂ (fun z => (yC z)⁻¹ ^ j) SU :=
  (yC_diffOn_SU.inv (fun _ hz => yC_ne_zero_of_mem_SU hz)).pow j

/-- The subtracted jets `GjetA a b c i z = Σ_{n<i} [yⁿ]G · y(z)ⁿ` form a polynomial in `yC`,
hence are holomorphic on `SU`. -/
private lemma GjetA_diffOn_SU (a b c : ℤ) (j : ℕ) : DifferentiableOn ℂ (GjetA a b c j) SU := by
  unfold GjetA
  exact DifferentiableOn.fun_sum
    (fun n _ => (differentiableOn_const _).mul (yC_diffOn_SU.pow n))

/-! ## 2. Geometry: `wC` maps `SU` into `SL` -/

private lemma wC_re_sub_one_eq (z : ℂ) (h : z ≠ 1) :
    (wC z).re - 1 = (z.re - 1) / Complex.normSq (z - 1) := by
  have hw : wC z - 1 = (z - 1)⁻¹ := by rw [wC]; field_simp; ring
  have h1 : (wC z).re - 1 = (wC z - 1).re := by simp
  rw [h1, hw, Complex.inv_re]; simp

private lemma wC_im_eq (z : ℂ) (h : z ≠ 1) :
    (wC z).im = - z.im / Complex.normSq (z - 1) := by
  have hw : wC z - 1 = (z - 1)⁻¹ := by rw [wC]; field_simp; ring
  have h1 : (wC z).im = (wC z - 1).im := by simp
  rw [h1, hw, Complex.inv_im]; simp

/-- `wC` maps the half plane `SU` into the half plane `SL`: writing `w = wC z = 1 + (z−1)⁻¹`
and `D = ‖z−1‖² > 0`, one has `Re w − 1 = (Re z − 1)/D`, `Im w = −Im z/D`, so
`8·Im w < Re w − 1` is exactly the inequality `1 < 8·Im z + Re z` defining `SU`. -/
private lemma wC_mapsTo_SU_SL : Set.MapsTo wC SU SL := by
  intro z hz
  have hz' : 1 < 8 * z.im + z.re := mem_SU_iff.mp hz
  have h1 : z ≠ 1 := by intro h; rw [h] at hz'; norm_num at hz'
  rw [mem_SL_iff]
  have hD : 0 < Complex.normSq (z - 1) := by
    rw [Complex.normSq_pos]
    intro h
    have hz1 : z = 1 := sub_eq_zero.mp h
    rw [hz1] at hz'; norm_num at hz'
  have key : 8 * (wC z).im < (wC z).re - 1 := by
    rw [wC_im_eq z h1, wC_re_sub_one_eq z h1]
    field_simp
    linarith
  linarith

/-! ## 3. The integrand -/

theorem BUint_diffOn_SU (a b c : ℤ) {HU HL : ℂ → ℂ}
    (hHU : DifferentiableOn ℂ HU Work.A14D.SU) (hHL : DifferentiableOn ℂ HL Work.A14D.SL) (i : Fin 3) :
    DifferentiableOn ℂ (Work.A14D.BUint a b c HU HL i) Work.A14D.SU := by
  unfold BUint
  exact (dyC_diffOn_SU.mul (yC_inv_pow_diffOn_SU (i : ℕ))).mul
    ((hHU.add (hHL.comp wC_diffOn_SU wC_mapsTo_SU_SL)).sub
      (GjetA_diffOn_SU a b c (i : ℕ)))

end

end Work.A14D
