import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS_RegExport.RXR1.SliceDiffAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS_RegExport.RXR1

/-!
# `Work.FTS_RegExport.RXR1.pthIter_le_of_weighted`

The angular analogue of `Work.FTS_RegExport.RXR1.pzIter_le_of_weighted`: the weighted slot
hypothesis `HwBnd β C` bounds the *mixed* slots `mixed b a f = D_z^b D_θ^a f` of order
`a + b ≤ 2`, and the two pure angular derivatives `∂_θ f` and `∂_θ² f` are recovered from
them by dividing by `sin(2θ)`.

* `mixed 0 1 f = sin(2θ) · ∂_θ f` is *definitional* (`D_θ f = sin(2θ) ∂_θ f`), giving the
  first slot with the loss `1/sin(2θ)`;
* `mixed 0 2 f = sin(2θ)² ∂_θ² f + 2 sin(2θ) cos(2θ) ∂_θ f` is the product rule applied to
  `θ' ↦ sin(2θ') ∂_θ f (z,θ')` (the only place where the smoothness `SmoothOpen f` is used),
  giving the second slot with the loss `1/sin(2θ)²`.

Both bounds are stated with the same constant `K = 3C` (the `2` accounting for the cross
term `2 sin(2θ) cos(2θ) ∂_θ f`, and the `1` for `|cos(2θ)| ≤ 1`).
-/

/-- The derivative of `θ ↦ sin(2θ)`. -/
lemma deriv_sin_two_slice (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
  simp [mul_comm]

/-- **The product-rule expansion of the second angular slot.**  For `f` of class `C^∞` on the
open quadrant and `(z,θ)` in it,

`D_θ² f (z,θ) = sin(2θ)² ∂_θ² f (z,θ) + 2 sin(2θ) cos(2θ) ∂_θ f (z,θ)`.

(With `mixed 0 i f = D_θ^i f`, this is the `D_θ²`-instance of
`Work.EllipticEst.RegQ.Vop.DthIter_two_eq`.) -/
lemma mixed_zero_two_expand {f : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed 0 2 f z θ
      = Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 2 f z θ
        + 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ := by
  have hP1 : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pth f z t) θ :=
    ((hS.pth.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hmain : Work.Spaces.mixed 0 2 f z θ
      = Real.sin (2 * θ) * (2 * Real.cos (2 * θ) * Work.Spaces.pth f z θ
          + Real.sin (2 * θ) * Work.Spaces.pthIter 2 f z θ) := by
    show Real.sin (2 * θ)
        * deriv (fun t : ℝ => Real.sin (2 * t) * Work.Spaces.pth f z t) θ = _
    rw [show (fun t : ℝ => Real.sin (2 * t) * Work.Spaces.pth f z t)
        = (fun t : ℝ => Real.sin (2 * t)) * (fun t : ℝ => Work.Spaces.pth f z t) from rfl,
      deriv_mul (by fun_prop) hP1, deriv_sin_two_slice]
    rw [show deriv (fun t : ℝ => Work.Spaces.pth f z t) θ
        = Work.Spaces.pthIter 2 f z θ from rfl]
  rw [hmain, show Work.Spaces.pthIter 1 f z θ = Work.Spaces.pth f z θ from rfl]
  ring

theorem pthIter_le_of_weighted {β C : ℝ} (hC : 0 ≤ C)
    (hw : Work.FTS_RegExport.RXR1.HwBnd β C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem β 4 f → Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.pthIter 1 f z θ|
            ≤ K * (Work.FTS_RegExport.RXR1.SliceW z / Real.sin (2 * θ))
              * Work.Spaces.HkNorm β 4 f ∧
        |Work.Spaces.pthIter 2 f z θ|
            ≤ K * (Work.FTS_RegExport.RXR1.SliceW z
              / (Real.sin (2 * θ) * Real.sin (2 * θ))) * Work.Spaces.HkNorm β 4 f := by
  refine ⟨3 * C, by linarith, ?_⟩
  intro f hS hH hB z θ hz hθ0 hθ1
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hW : 0 ≤ SliceW z := SliceW_nonneg hz.le
  have hN : 0 ≤ Work.Spaces.HkNorm β 4 f := Real.sqrt_nonneg _
  have hCWN : 0 ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    mul_nonneg (mul_nonneg hC hW) hN
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- ## first slot: `∂_θ f = mixed 0 1 f / sin(2θ)`
  have hb1 : |Work.Spaces.mixed 0 1 f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    hw f hS hH hB 0 1 (by norm_num) z θ hz hθ0 hθ1
  have hsx : Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|
      ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f := by
    calc Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|
        = |Work.Spaces.mixed 0 1 f z θ| := by
          rw [mixed_zero_one_eq, abs_mul, abs_of_pos hs]
      _ ≤ _ := hb1
  have hx1 : |Work.Spaces.pthIter 1 f z θ|
      ≤ 3 * C * (SliceW z / Real.sin (2 * θ)) * Work.Spaces.HkNorm β 4 f := by
    have h1 : |Work.Spaces.pthIter 1 f z θ|
        ≤ (C * SliceW z * Work.Spaces.HkNorm β 4 f) / Real.sin (2 * θ) := by
      rw [le_div_iff₀ hs]
      calc |Work.Spaces.pthIter 1 f z θ| * Real.sin (2 * θ)
          = Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ| := by ring
        _ ≤ _ := hsx
    have h2 : (C * SliceW z * Work.Spaces.HkNorm β 4 f) / Real.sin (2 * θ)
        ≤ 3 * C * (SliceW z / Real.sin (2 * θ)) * Work.Spaces.HkNorm β 4 f := by
      have h4 := div_le_div_of_nonneg_right (show C * SliceW z * Work.Spaces.HkNorm β 4 f
          ≤ 3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) by linarith [hCWN]) hs.le
      have h5 : (3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f)) / Real.sin (2 * θ)
          = 3 * C * (SliceW z / Real.sin (2 * θ)) * Work.Spaces.HkNorm β 4 f := by
        ring_nf
      rw [h5] at h4
      exact h4
    exact le_trans h1 h2
  -- ## second slot: `sin(2θ)² ∂_θ² f = mixed 0 2 f - 2 sin(2θ)cos(2θ) ∂_θ f`
  have hb2 : |Work.Spaces.mixed 0 2 f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    hw f hS hH hB 0 2 (by norm_num) z θ hz hθ0 hθ1
  have hid := mixed_zero_two_expand hS hz hθm
  have hkey : Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 2 f z θ
      = Work.Spaces.mixed 0 2 f z θ
        - 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ := by
    rw [hid]; ring
  have hsq : Real.sin (2 * θ) ^ 2 * |Work.Spaces.pthIter 2 f z θ|
      = |Work.Spaces.mixed 0 2 f z θ
        - 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ| := by
    rw [← hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hBle : |2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ|
      ≤ 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by
    have habs : |(2 : ℝ) * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ|
        = 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|) * |Real.cos (2 * θ)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hs]
      ring
    rw [habs]
    have h1 : 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|) * |Real.cos (2 * θ)|
        ≤ 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (by positivity : (0 : ℝ) ≤ 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|))
    have h2 : 2 * (Real.sin (2 * θ) * |Work.Spaces.pthIter 1 f z θ|) * 1
        ≤ 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by
      simpa using mul_le_mul_of_nonneg_left hsx (by norm_num : (0 : ℝ) ≤ 2)
    exact le_trans h1 h2
  have htri : Real.sin (2 * θ) ^ 2 * |Work.Spaces.pthIter 2 f z θ|
      ≤ 3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by
    rw [hsq]
    calc |Work.Spaces.mixed 0 2 f z θ - 2 * Real.sin (2 * θ) * Real.cos (2 * θ)
            * Work.Spaces.pthIter 1 f z θ|
        = |Work.Spaces.mixed 0 2 f z θ
            + (-(2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ))| := by
          rw [sub_eq_add_neg]
      _ ≤ |Work.Spaces.mixed 0 2 f z θ|
            + |-(2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ)| :=
          abs_add_le _ _
      _ = |Work.Spaces.mixed 0 2 f z θ|
            + |2 * Real.sin (2 * θ) * Real.cos (2 * θ) * Work.Spaces.pthIter 1 f z θ| := by
          rw [abs_neg]
      _ ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f
            + 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) :=
          add_le_add hb2 hBle
      _ = 3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by ring
  have hx2 : |Work.Spaces.pthIter 2 f z θ|
      ≤ 3 * C * (SliceW z / (Real.sin (2 * θ) * Real.sin (2 * θ)))
          * Work.Spaces.HkNorm β 4 f := by
    have hX : 3 * C * (SliceW z / (Real.sin (2 * θ) * Real.sin (2 * θ)))
          * Work.Spaces.HkNorm β 4 f
        = (3 * C * SliceW z * Work.Spaces.HkNorm β 4 f)
          / (Real.sin (2 * θ) * Real.sin (2 * θ)) := by
      ring_nf
    rw [hX, le_div_iff₀ (mul_pos hs hs)]
    calc |Work.Spaces.pthIter 2 f z θ| * (Real.sin (2 * θ) * Real.sin (2 * θ))
        = Real.sin (2 * θ) ^ 2 * |Work.Spaces.pthIter 2 f z θ| := by ring
      _ ≤ 3 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := htri
      _ = 3 * C * SliceW z * Work.Spaces.HkNorm β 4 f := by ring
  exact ⟨hx1, hx2⟩

end Work.FTS_RegExport.RXR1
