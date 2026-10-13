import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ASlotRoute.Auxiliary

/-- Second-order Taylor expansion with integral remainder, on a closed interval `[y, x]` lying
inside the open interval `(0, a)` on which `u` is of class `C²`:

`u x = u y + (x - y) * u' y + ∫_y^x (x - t) * u''(t) dt`.

The proof is the standard one-step integration by parts: the function
`R s = u s - (s - x) * u' s` satisfies `R' s = (x - s) * u'' s` and `R x = u x`,
so the fundamental theorem of calculus gives the claim. -/
theorem taylorSecondOrderIntegral {a y x : ℝ} {u : ℝ → ℝ} (hy : 0 < y) (hyx : y < x)
    (hx : x < a) (hC2 : ContDiffOn ℝ 2 u (Set.Ioo 0 a)) :
    u x = u y + (x - y) * deriv u y + ∫ t in y..x, (x - t) * deriv (deriv u) t := by
  -- A neighbourhood `V` of `[y, x]` contained in `(0, a)`.
  have hεpos : 0 < min (y / 2) ((a - x) / 2) := lt_min (by linarith) (by linarith)
  set V : Set ℝ := Set.Ioo (y - min (y / 2) ((a - x) / 2)) (x + min (y / 2) ((a - x) / 2))
    with hVdef
  have hVopen : IsOpen V := isOpen_Ioo
  have hVsub : V ⊆ Set.Ioo 0 a := by
    intro t ht
    have h1 : min (y / 2) ((a - x) / 2) ≤ y / 2 := min_le_left _ _
    have h2 : min (y / 2) ((a - x) / 2) ≤ (a - x) / 2 := min_le_right _ _
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hC2V : ContDiffOn ℝ 2 u V := hC2.mono hVsub
  have hC1d : ContDiffOn ℝ 1 (deriv u) V := hC2V.deriv_of_isOpen hVopen (by norm_num)
  have hcontH : ContinuousOn (deriv (deriv u)) V :=
    hC1d.continuousOn_deriv_of_isOpen hVopen (by norm_num)
  have hmem : ∀ t ∈ Set.uIcc y x, t ∈ V := by
    intro t ht
    rw [Set.uIcc_of_le hyx.le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- The auxiliary function `R s = u s - (s - x) * u' s` has the required derivative.
  have hR : ∀ t ∈ Set.uIcc y x,
      HasDerivAt (fun s => u s - (s - x) * deriv u s) ((x - t) * deriv (deriv u) t) t := by
    intro t ht
    have htV : t ∈ V := hmem t ht
    have hu1 : HasDerivAt u (deriv u t) t :=
      ((hC2V.differentiableOn (by norm_num)).differentiableAt (hVopen.mem_nhds htV)).hasDerivAt
    have hu2 : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
      ((hC1d.differentiableOn (by norm_num)).differentiableAt (hVopen.mem_nhds htV)).hasDerivAt
    have hprod : HasDerivAt (fun s => (s - x) * deriv u s)
        (1 * deriv u t + (t - x) * deriv (deriv u) t) t :=
      ((hasDerivAt_id t).sub_const x).mul hu2
    have hfin := hu1.sub hprod
    convert hfin using 1
    ring
  have hint : IntervalIntegrable (fun t => (x - t) * deriv (deriv u) t) MeasureTheory.volume y x := by
    apply ContinuousOn.intervalIntegrable
    refine (continuousOn_const.sub continuousOn_id).mul (hcontH.mono ?_)
    intro t ht
    exact hmem t ht
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hR hint
  rw [key]
  ring

end Work.FTS.EllSol.ASlotRoute.Auxiliary
