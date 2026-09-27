/-
A6 `Geo/DualStretch` — vocabulary for the inverse law `stretch_inv` of the stretch.

`stretch` rescales the high mass of every point `x ∈ P.space` by the taper `taperM` and
renormalises.  Here we fix the bookkeeping objects of the rescaled mass decomposition:

* `posCands P hP x`   : the level sets of *positive* `massG`-mass of `x` (a chain of faces of `P`);
* `denOf β p P hP α M x = 1 + (taperM x - 1) * SOf x` : the renormalisation factor `d`;
* `wtOf β p P hP α M x τ` : the rescaled mass of the level set `τ`, i.e. `massG x τ / d` for a low
  level set and `taperM x * massG x τ / d` for a high one.

The point of the stretch is that the stretched point `y = stretch P hP β p α M x` has
`massG y τ = wtOf ... τ` (a decomposition on the *same* chain, with the low masses divided by `d`
and the high masses multiplied by `taperM x / d`), whence the join segment `segOf` is unchanged and
`stretch` is inverted by the stretch with the reciprocal taper.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.coord_spec
import Submission.Work.Geo.DualStretch.massG_api

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

/-! ### The taper is positive -/

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- For `0 < M` the taper takes values in `(0, ∞)`; indeed it lies between `min 1 M` and `max 1 M`. -/
theorem taperM_pos {β α M : ℝ} (hM : 0 < M) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) :
    0 < taperM β p P hP α M x := by
  have h1 : 0 ≤ clamp01 (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2)) :=
    clamp01_nonneg _
  have h2 : clamp01 (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2)) ≤ 1 :=
    clamp01_le_one _
  simp only [taperM]
  by_cases h : (1:ℝ) ≤ M
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M - 1) h1]
  · nlinarith [mul_le_mul_of_nonpos_left h2 (by linarith : M - 1 ≤ (0:ℝ))]

/-- The taper depends on `x` only through the join segment `segOf x`. -/
theorem taperM_congr {β α M : ℝ} {p : ℕ} {P : Cx n} {hP : P.faces.Finite} {x y : E n}
    (h : segOf β p P hP x = segOf β p P hP y) :
    taperM β p P hP α M x = taperM β p P hP α M y := by
  simp only [taperM, h]

/-! ### The rescaled mass decomposition -/

/-- The level sets of positive `massG`-mass of `x`. -/
noncomputable def posCands (P : Cx n) (hP : P.faces.Finite) (x : E n) : Finset (Finset (E n)) :=
  (cands P hP).filter (fun τ => 0 < massG P hP x τ)

/-- The renormalisation factor `d = 1 + (taperM x - 1) * S(x)` of the stretch at `x`. -/
noncomputable def denOf (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (α M : ℝ) (x : E n) :
    ℝ :=
  1 + (taperM β p P hP α M x - 1) * SOf β p P hP x

/-- The mass of the level set `τ` after rescaling the high mass by the taper and renormalising:
`massG x τ / d` on the low side and `taperM x * massG x τ / d` on the high side. -/
noncomputable def wtOf (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (α M : ℝ) (x : E n)
    (τ : Finset (E n)) : ℝ :=
  (if LowFace β p τ then (denOf β p P hP α M x)⁻¹
    else taperM β p P hP α M x * (denOf β p P hP α M x)⁻¹) * massG P hP x τ

/-! ### Elementary sums -/

theorem sum_ite_zero (s : Finset (Finset (E n))) (f : Finset (E n) → ℝ)
    (q : Finset (E n) → Prop) [DecidablePred q] :
    (∑ τ ∈ s, if q τ then 0 else f τ) = ∑ τ ∈ s.filter (fun τ => ¬ q τ), f τ := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  by_cases h : q τ <;> simp [h]

theorem sum_ite_self (s : Finset (Finset (E n))) (f : Finset (E n) → ℝ)
    (q : Finset (E n) → Prop) [DecidablePred q] :
    (∑ τ ∈ s, if q τ then f τ else 0) = ∑ τ ∈ s.filter q, f τ := by
  rw [Finset.sum_filter]

/-- `AOf` and `BOf` add up to the point. -/
theorem AOf_add_BOf {β : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) : AOf β p P hP x + BOf β p P hP x = x := by
  have h := (massG_api P hP hx).2.2.1
  have hsplit : AOf β p P hP x + BOf β p P hP x =
      ∑ τ ∈ cands P hP, massG P hP x τ • bary τ := by
    simp only [AOf, BOf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hL : LowFace β p τ <;> simp [hL]
  rw [hsplit, h]

/-- The defining formula of the stretch at a point of `P.space`. -/
theorem stretch_unfold {β α M : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) :
    stretch P hP β p α M x =
      (denOf β p P hP α M x)⁻¹ •
        (AOf β p P hP x + taperM β p P hP α M x • BOf β p P hP x) := by
  show stretchM β p P hP (taperM β p P hP α M) x =
      (denOf β p P hP α M x)⁻¹ •
        (AOf β p P hP x + taperM β p P hP α M x • BOf β p P hP x)
  unfold stretchM
  rw [ite_eq_left hx]
  rfl

end Work.Geo.DualStretch
