import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR1.SliceDiffAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.pzIter_bound_weighted`

Consequence of the *weighted slot bound* `HwBnd β C` (which controls the mixed slots
`D_z^b D_θ^a f` of order `a + b ≤ 2` of an honest `ℋ⁴` datum by `C · z^{3/2}/(1+z)² · |f|_{ℋ⁴}`,
cf. `Work.FTS_RegExport.RXR1.mixed_abs_le_weighted`): the plain `z`-derivatives `∂_z f` and
`∂_z² f` obey the same weighted bound with the two powers of `z` divided out,

  `|∂_z f(z,θ)| ≤ K · (W(z)/z) · |f|_{ℋ⁴}`,  `|∂_z² f(z,θ)| ≤ K · (W(z)/z²) · |f|_{ℋ⁴}`,

with `W = SliceW = z^{3/2}/(1+z)²` and `K = 2C`.

The two inputs are the definitional identities

* `mixed 1 0 f = z · ∂_z f`  (`SliceDiffAux.mixed_one_zero_eq`),
* `D_z² f = D_z f + z² · ∂_z² f`  (`dziter_two_eq_add` below, the `n = 2` case of the expansion
  of `D_z = z ∂_z` in powers of `z^k∂_z^k`, obtained from the one-variable product rule alone).

The second identity needs only that the `z`-slice of `∂_z f` be differentiable at the point,
which `SmoothOpen f` supplies through `SmoothOpen.hasDerivAt_slice_pzIter`.
-/

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS_RegExport.RXR1

set_option autoImplicit false

/-- **The bridge `D_z²F = D_zF + z²∂_z²F`.**

If the `z`-slice of `∂_zF` is differentiable at `z`, then `D_z²F = D_zF + z²∂_z²F` at `(z,θ)`.
(The `n = 2` case of the expansion of `D_z = z∂_z` in powers of `z^k∂_z^k`, with the Stirling
coefficients `S(2,1) = S(2,2) = 1`; only the product rule is used, so no higher smoothness is
required.) -/
private lemma dziter_two_eq_add (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z) :
    Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.DzIter 1 F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
  have hdmul : deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
    have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id' z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz F z' θ)
        (Work.Spaces.pz (Work.Spaces.pz F) z θ) z := hd.hasDerivAt
    have h3 : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz F z' θ)
        (1 * Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ) z :=
      (h1.mul h2).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext z'; rfl))
    simpa only [one_mul] using h3.deriv
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = z * Work.Spaces.pz F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ
  rw [hdmul]
  ring

/-- The requested lemma: from the weighted slot bound `HwBnd β C` on the mixed slots of order
`≤ 2` one gets the weighted bounds `|∂_z^j f| ≤ 2C·SliceW z / z^j · |f|_{ℋ⁴}` for `j = 1, 2`. -/
theorem pzIter_bound_weighted {β C : ℝ} (hC : 0 ≤ C)
    (hw : Work.FTS_RegExport.RXR1.HwBnd β C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem β 4 f → Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.pzIter 1 f z θ| ≤ K * (Work.FTS_RegExport.RXR1.SliceW z / z)
            * Work.Spaces.HkNorm β 4 f ∧
        |Work.Spaces.pzIter 2 f z θ| ≤ K * (Work.FTS_RegExport.RXR1.SliceW z / (z * z))
            * Work.Spaces.HkNorm β 4 f := by
  refine ⟨2 * C, by linarith, ?_⟩
  intro f hf hmem hbd z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hnorm : 0 ≤ Work.Spaces.HkNorm β 4 f := Real.sqrt_nonneg _
  have hW : 0 ≤ SliceW z := SliceW_nonneg hz.le
  have hN : 0 ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    mul_nonneg (mul_nonneg hC hW) hnorm
  -- the weighted slot bounds from `hw`
  have hb1 : z * |Work.Spaces.pzIter 1 f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f := by
    have h := hw f hf hmem hbd 1 0 (by norm_num) z θ hz hθ0 hθ1
    rw [mixed_one_zero_eq, abs_mul, abs_of_pos hz] at h
    exact h
  have hb2 : |Work.Spaces.mixed 2 0 f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f :=
    hw f hf hmem hbd 2 0 (by norm_num) z θ hz hθ0 hθ1
  have hm1eq : |Work.Spaces.mixed 1 0 f z θ| = z * |Work.Spaces.pzIter 1 f z θ| := by
    rw [mixed_one_zero_eq, abs_mul, abs_of_pos hz]
  -- the expansion `D_z²f = D_zf + z²∂_z²f`
  have hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z :=
    (hf.hasDerivAt_slice_pzIter 1 hθ hz).differentiableAt
  have hexp : Work.Spaces.DzIter 2 f z θ
      = Work.Spaces.DzIter 1 f z θ + z ^ 2 * Work.Spaces.pzIter 2 f z θ :=
    dziter_two_eq_add f hd
  have hprod : z ^ 2 * Work.Spaces.pzIter 2 f z θ
      = Work.Spaces.mixed 2 0 f z θ - Work.Spaces.mixed 1 0 f z θ := by
    show z ^ 2 * Work.Spaces.pzIter 2 f z θ
      = Work.Spaces.DzIter 2 f z θ - Work.Spaces.DzIter 1 f z θ
    linarith [hexp]
  have hB : |Work.Spaces.pzIter 2 f z θ| * z ^ 2
      ≤ 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) := by
    have h2 := abs_sub (Work.Spaces.mixed 2 0 f z θ) (Work.Spaces.mixed 1 0 f z θ)
    have h4 : |Work.Spaces.pzIter 2 f z θ| * z ^ 2 = |z ^ 2 * Work.Spaces.pzIter 2 f z θ| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg z)]; ring
    rw [h4, hprod]
    linarith [h2, hb1, hb2, hm1eq]
  -- divide the two powers of `z` out
  have hAeq : 2 * C * (SliceW z / z) * Work.Spaces.HkNorm β 4 f
      = 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) / z := by
    field_simp
  have hBeq : 2 * C * (SliceW z / (z * z)) * Work.Spaces.HkNorm β 4 f
      = 2 * (C * SliceW z * Work.Spaces.HkNorm β 4 f) / (z * z) := by
    field_simp
  constructor
  · rw [hAeq, le_div_iff₀ hz]
    nlinarith [hb1, hN]
  · rw [hBeq, le_div_iff₀ (by positivity)]
    nlinarith [hB]

end Work.FTS_RegExport.RXR1
