/-
Copied from `Submission.Work.FTS.EllipticEst.M4.s20_honesty` for `Final/slot20_bound_fts`.
Only the `import` lines are redirected (see `Final/slot20_bound_fts.lean` for why):
the copy of `Mine/TopSlotTwo` (`Final/ReHome/TkKit.lean`) drops the `Mine/ShiftLevelOne`
import and the two declarations at the end of that file that use it, which cuts the
`RPFresh/excess_finite` dependency out of the closure.
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound
import Submission.Work.FTS.EllipticEst.M4.Slot20A
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.H2W.Step5.integrable_of_majorant
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_Step5_s20Aesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

open MeasureTheory Set Filter

/-! ## The honesty of the two dominating pieces of the top angular slot at level `2`

The datum `Ψ` of the weak class `TT.EllWeakPos α 2 F Ψ` is only required to be smooth on the
*open* quadrant, with the two `H²`-memberships of `F` and of `∂_θθΨ`; in particular the level-`2`
integrand of `∂_θθΨ` is honest.  Writing `H := ∂_θθΨ`, the `(i,j) = (2,0)` and `(1,0)` summands
of `HkIntegrand α 2 H` are the weighted squares of

  `D_θ²H = sin(2θ)· (2cos(2θ)·∂_θH + sin(2θ)·∂_θ²H)` and `D_θH = sin(2θ)·∂_θH`,

and the two quantities `F₄ = 2w²(∂_θ⁴Ψ)²σ₄` and `F₃ = 8w²(∂_θ³Ψ)²σ₂` are recovered from them by
inverting the triangular relation

  `sin(2θ)·∂_θ²H = D_θ²H / sin(2θ) - 2cos(2θ)·∂_θH`,

which costs only the numerical factor `20 = 4 + 16` (resp. `8`).  Hence both pieces are honest as
soon as `∂_θθΨ ∈ ℋ²`, which is a field of the hypothesis class.  This is the "honesty" input of
the level-`2` Step-5 estimate, and it needs no use of the equation, of the moment conditions or of
the honesty of `F`: only the `ℋ²`-field of `∂_θθΨ` (together with the a.e.-measurability of the
integrands, which is `s20Aesm`). -/

/-- **The weight identity behind the top slot.**  With `Wt α z θ = w z · sin(2θ)^{-γ/2}` and
`σ₄ = sin(2θ)^{4-γ}`,

  `2 w(z)² (∂_θ⁴Ψ z θ)² σ₄(θ) = 2 (sin(2θ)² · ∂_θ⁴Ψ z θ · Wt α z θ)²`.

The right-hand side is the square of a `(2,0)`-shaped expression, so that the two `HkIntegrand`
summands can be combined with it. -/
theorem s20F4_eq_sq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
      = 2 * (Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 4 Ψ z θ
              * Work.Spaces.Wt α z θ) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.bt_sin_nonneg hθ
  have hgam4 : Work.Spaces.gam α ≠ 4 := by
    rw [Work.Spaces.gam]; intro h; linarith
  have hne : (4 : ℝ) + -(Work.Spaces.gam α) ≠ 0 := by
    intro h; exact hgam4 (by linarith)
  have hXc : Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α)
      = Real.sin (2 * θ) ^ (4 : ℕ) * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
    rw [show (4 : ℝ) - Work.Spaces.gam α = (4 : ℝ) + -(Work.Spaces.gam α) from by ring,
        Real.rpow_add' hs hne]
    rw [show Real.sin (2 * θ) ^ (4 : ℝ) = Real.sin (2 * θ) ^ (4 : ℕ) from
      Real.rpow_natCast _ 4]
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.Mine.sig4]
  change 2 * (Work.Spaces.w z) ^ 2
      * (Work.Spaces.pthIter 4 Ψ z θ ^ 2 * (Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α)))
    = 2 * (Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 4 Ψ z θ * Work.Spaces.Wt α z θ) ^ 2
  rw [hXc, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
  ring

/-- The vanishing of `s20F4` at the two angular endpoints (`σ₄` carries the factor
`sin(2θ)^{4-γ}` and `4 - γ ≠ 0` for `γ = 1 + α/10 ≤ 5/4`). -/
theorem s20F4_eq_zero_theta_zero (α : ℝ) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z 0 = 0 := by
  have hpos : 0 < 4 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.Mine.sig4]
  rw [show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero]
  change 2 * Work.Spaces.w z ^ 2
      * (Work.Spaces.pthIter 4 Ψ z 0 ^ 2 * (0 : ℝ) ^ (4 - Work.Spaces.gam α)) = 0
  rw [Real.zero_rpow (ne_of_gt hpos)]
  ring

/-- Vanishing of `s20F4` at `θ = π/2`. -/
theorem s20F4_eq_zero_theta_pi (α : ℝ) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z (Real.pi / 2) = 0 := by
  have hpos : 0 < 4 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.Mine.sig4]
  rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  change 2 * Work.Spaces.w z ^ 2
      * (Work.Spaces.pthIter 4 Ψ z (Real.pi / 2) ^ 2
          * (0 : ℝ) ^ (4 - Work.Spaces.gam α)) = 0
  rw [Real.zero_rpow (ne_of_gt hpos)]
  ring

/-- Vanishing of `s20F4` at `z = 0` (the radial weight `w` vanishes there). -/
theorem s20F4_eq_zero_z (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ 0 θ = 0 := by
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.Spaces.w]
  norm_num

/-- **The pointwise domination on the open quadrant.**  With `H := ∂_θθΨ`,
`D_θ²H = sin²(2θ)∂_θ²H + 2sin(2θ)cos(2θ)∂_θH`, so `sin(2θ)∂_θ²H` is a difference of `D_θ²H/sin(2θ)`
and `2cos(2θ)∂_θH`; squaring with `(a-b)² ≤ 2a² + 2b²`, using `|cos| ≤ 1` and multiplying by
`w²sin(2θ)^{-γ}` turns `F₄` into at most `4` times the `(2,0)` summand plus `16` times the `(1,0)`
summand of `HkIntegrand α 2 H`. -/
theorem s20F4_le_of_int (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ)
    (hdiff : DifferentiableAt ℝ (fun t => deriv (fun t' => Work.Spaces.pthIter 2 Ψ z t') t) θ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
      ≤ 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  have hmain := s20F4_eq_sq α hα hα4 Ψ z θ hθ
  have hE : Work.Spaces.mixed 0 2 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ
      = Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 4 Ψ z θ * Work.Spaces.Wt α z θ
        + 2 * Real.cos (2 * θ) * (Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ
            * Work.Spaces.Wt α z θ) := by
    have h := Work.FTS.EllipticEst.H2W.DthIter_two_eq_pth (Work.Spaces.pthIter 2 Ψ) z θ hdiff
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
        = Work.Spaces.pthIter 4 Ψ z θ := rfl
    have h1 : Work.Spaces.pth (Work.Spaces.pthIter 2 Ψ) z θ
        = Work.Spaces.pthIter 3 Ψ z θ := rfl
    show Work.Spaces.DthIter 2 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ = _
    rw [h, h2, h1]; ring
  have hQ : Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ
      = Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ * Work.Spaces.Wt α z θ := rfl
  have h1 := Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.Spaces.pthIter 2 Ψ) z θ 2 0
    (by norm_num) (by norm_num)
  have h2 := Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.Spaces.pthIter 2 Ψ) z θ 1 0
    (by norm_num) (by norm_num)
  set U : ℝ := Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 4 Ψ z θ * Work.Spaces.Wt α z θ
    with hU
  set V : ℝ := 2 * Real.cos (2 * θ) * (Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ
    * Work.Spaces.Wt α z θ) with hV
  set Q : ℝ := Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ * Work.Spaces.Wt α z θ with hQd
  have h1' : (U + V) ^ 2 ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
    rw [← hE]; exact h1
  have h2' : Q ^ 2 ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
    rw [← hQ]; exact h2
  have hc2 : Real.cos (2 * θ) ^ 2 ≤ 1 := by
    nlinarith [Real.cos_sq_add_sin_sq (2 * θ), sq_nonneg (Real.sin (2 * θ))]
  have hv : V ^ 2 ≤ 4 * Q ^ 2 := by rw [hV]; nlinarith [hc2, sq_nonneg Q]
  have hu : U ^ 2 ≤ 2 * (U + V) ^ 2 + 2 * V ^ 2 := by nlinarith [sq_nonneg (U + 2 * V)]
  rw [hmain]; linarith

/-- **The pointwise domination, everywhere on `Iz × Iθ`.**  At the angular endpoints and at
`z = 0` both sides are nonnegative with `s20F4` vanishing; in the interior
`s20F4_le_of_int` applies with the differentiability of the `∂_θ²`-slice supplied by the
smoothness of `Ψ` on the open quadrant. -/
theorem s20F4_le_HkIntegrand (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
      ≤ 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  have hnn : (0 : ℝ) ≤ 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
    mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 2 _ z θ)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · have h0 : Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ = 0 := by
      rw [← hz0]; exact s20F4_eq_zero_z α Ψ θ
    rw [h0]; exact hnn
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · have h0 : Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ = 0 := by
        rw [← hθ0]; exact s20F4_eq_zero_theta_zero α hα4 Ψ z
      rw [h0]; exact hnn
    · rcases eq_or_lt_of_le hθ.2 with hθ2 | hθlt
      · have h0 : Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ = 0 := by
          rw [hθ2]; exact s20F4_eq_zero_theta_pi α hα4 Ψ z
        rw [h0]; exact hnn
      · exact s20F4_le_of_int α hα hα4 Ψ ⟨le_of_lt hθpos, le_of_lt hθlt⟩
          (Work.FTS.EllipticEst.H2W.slice_diff2 hsm hzpos θ ⟨hθpos, hθlt⟩)

/-- `F₃ ≤ 8 · HkIntegrand α 2 (∂_θθΨ)`: the `(1,0)`-summand of the level-`2` integrand of
`∂_θθΨ` is exactly `w²sin(2θ)^{2-γ}(∂_θ³Ψ)²`, which is `F₃/8`. -/
theorem s20F3_le_HkIntegrand (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ)
    (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ
      ≤ 8 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  rw [Work.FTS.EllipticEst.H2W.s20F3_eq α hα hα4 Ψ hθ z]
  exact mul_le_mul_of_nonneg_left
    (Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.Spaces.pthIter 2 Ψ) z θ 1 0
      (by norm_num) (by norm_num)) (by norm_num)

/-- Nonnegativity of the step-5 piece. -/
theorem s20F4_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ := by
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.Mine.sig4]
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.bt_sin_nonneg hθ) _))

/-- Nonnegativity of the step-4 piece. -/
theorem s20F3_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ := by
  rw [Work.FTS.EllipticEst.H2W.s20F3, Work.FTS.EllipticEst.Mine.sig2]
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.bt_sin_nonneg hθ) _))

theorem s20_honesty : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.Integrable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.Integrable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  intro α F Ψ hα hα4 h
  have hsm := h.smooth
  have hmem := h.memB
  obtain ⟨haesm4, haesm3, haesm4z, haesm3z⟩ := s20Aesm α Ψ hsm
  -- the two pointwise dominations of the level-`2` integrand of `∂_θθΨ`
  have hle4 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
        ≤ 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
    fun z hz θ hθ => s20F4_le_HkIntegrand α hα hα4 hsm hz hθ
  have hle3 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ
        ≤ 8 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
    fun z hz θ hθ => s20F3_le_HkIntegrand α hα hα4 Ψ z hθ
  have hnn4 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ :=
    fun z _ θ hθ => s20F4_nonneg α Ψ z hθ
  have hnn3 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ :=
    fun z _ θ hθ => s20F3_nonneg α Ψ z hθ
  -- the majorants are honest, being constant multiples of the level-`2` integrand
  have hMsl20 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      Work.Spaces.Iθ :=
    fun z hz => (hmem.1 z hz).const_mul 20
  have hMsl8 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => 8 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      Work.Spaces.Iθ :=
    fun z hz => (hmem.1 z hz).const_mul 8
  have hMz20 : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      Work.Spaces.Iz := by
    refine (show MeasureTheory.Integrable (fun z => 20 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) from hmem.2.const_mul 20).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul]
  have hMz8 : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      8 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      Work.Spaces.Iz := by
    refine (show MeasureTheory.Integrable (fun z => 8 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) from hmem.2.const_mul 8).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul]
  obtain ⟨h4θ, h4z⟩ := integrable_of_majorant haesm4 haesm4z hMsl20 hMz20 hnn4 hle4
  obtain ⟨h3θ, h3z⟩ := integrable_of_majorant haesm3 haesm3z hMsl8 hMz8 hnn3 hle3
  exact ⟨h4θ, h4z, h3θ, h3z⟩

end Work.FTS.EllipticEst.H2W.Step5
