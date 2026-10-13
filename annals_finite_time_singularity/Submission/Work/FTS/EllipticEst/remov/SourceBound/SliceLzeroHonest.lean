import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Lzero_orthogonal
import Submission.Work.FTS.EllipticEst.remov.SourceBound.ftcBoundOfIntegrableDeriv
import Submission.Work.FTS.EllipticEst.remov.SourceBound.hasDerivAt_divSinCos
import Submission.Work.FTS.EllipticEst.remov.SourceBound.integral_invSinSqCosCu_left
import Submission.Work.FTS.EllipticEst.remov.SourceBound.integral_invSinSqCosCu_right

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Honesty of a slice from the honesty of its `Lzero1`-moment.**

If `u : ℝ → ℝ` is `C²` on the open interval `(0, π/2)` and the product
`θ ↦ Lzero1 u θ * sinCos2 θ` is integrable on `Iθ = [0, π/2]`, then `θ ↦ u θ * sinCos2 θ`
is integrable on `Iθ` as well.

Proof sketch.  Write `sc = sinCos2` and `G θ = -(deriv u θ) * sc θ + u θ * (cos θ * cos (2θ))`.
The already-proved `Work.Elliptic.hasDerivAt_Lzero_antideriv` (applied to `fun _ θ' => u θ'`,
using `Lzero Ψ z x = Lzero1 (fun t => Ψ z t) x` by `rfl`) gives
`HasDerivAt G (Lzero1 u θ * sc θ) θ` for every `θ ∈ (0, π/2)`.  Since `∫_{Iθ} |Lzero1 u * sc| < ∞`
and the two functions agree on `(0, π/2)` (= `Iθ` minus two points), `G'` is integrable, and the
FTC on `[θ, π/4] ⊆ (0, π/2)` gives `|G θ| ≤ M := |G (π/4)| + ∫_{Iθ} |G'|`.
Then `v θ = u θ / sc θ` satisfies `(v θ * cos θ)' = -(cos θ) * G θ / sc θ ^ 2`, so
`|v θ * cos θ| ≤ |v (π/4) * cos (π/4)| + M * ∫ 1/(sin^2 t * cos^3 t)` between `θ` and `π/4`.
The elementary bounds `sin t ≥ (2/π) t`, `cos t ≥ (2/π)(π/2 - t)` bound this integral by
`C * (1/θ + 1/(π/2-θ)^2 + 1)`, so `|u θ| ≤ C * (1/θ + 1/(π/2-θ)^2 + 1) * sin θ * cos θ`, which is
integrable against `sc` (using `sin θ ≤ θ` and `cos θ ≤ π/2 - θ`). -/
theorem SliceLzeroHonest {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  set G : ℝ → ℝ := fun θ => -(deriv u θ) * Work.Elliptic.sinCos2 θ + u θ * (Real.cos θ * Real.cos (2 * θ)) with hGdef
  set W : ℝ → ℝ := fun θ => u θ / (Real.sin θ * Real.cos θ) with hWdef
  set f' : ℝ → ℝ := fun x => -(G x) / (Real.sin x ^ 2 * Real.cos x ^ 3) with hf'def
  have hpi4 : (0:ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hderiv0 : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      HasDerivAt (fun θ => -(deriv u θ) * Work.Elliptic.sinCos2 θ + u θ * (Real.cos θ * Real.cos (2*θ)))
        (Work.FTS.EllipticEst.Lzero1 u x * Work.Elliptic.sinCos2 x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have h3 := Work.Elliptic.hasDerivAt_Lzero_antideriv (fun _ θ' => u θ') 0 x hx h2
    have hL : Work.Elliptic.Lzero (fun _ θ' => u θ') 0 x = Work.FTS.EllipticEst.Lzero1 u x := by
      simpa using (congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero u 0) x).symm
    rw [hL] at h3
    simpa using h3
  obtain ⟨M, hMnn, hM⟩ := ftcBoundOfIntegrableDeriv
    (F := fun θ => -(deriv u θ) * Work.Elliptic.sinCos2 θ + u θ * (Real.cos θ * Real.cos (2*θ)))
    (f' := fun θ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) hderiv0 h
  have hWderiv : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt W (f' x) x := by
    intro x hx
    have hh := hasDerivAt_divSinCos (G := G) hx (hu.contDiffAt (isOpen_Ioo.mem_nhds hx)) (by simp only [hGdef])
    simpa only [hWdef, hf'def] using hh
  have hGdiff : DifferentiableOn ℝ G (Set.Ioo 0 (Real.pi/2)) := by
    intro x hx
    rw [hGdef]
    exact (hderiv0 x hx).differentiableAt.differentiableWithinAt
  have hGcont : ContinuousOn G (Set.Ioo 0 (Real.pi/2)) := hGdiff.continuousOn
  have hWdiff : DifferentiableOn ℝ W (Set.Ioo 0 (Real.pi/2)) :=
    fun x hx => (hWderiv x hx).differentiableAt.differentiableWithinAt
  have hWcont : ContinuousOn W (Set.Ioo 0 (Real.pi/2)) := hWdiff.continuousOn
  have hdenom_pos : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi/2), 0 < Real.sin x ^ 2 * Real.cos x ^ 3 := by
    intro x hx
    have hs : 0 < Real.sin x := Real.sin_pos_of_mem_Ioo ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
    positivity
  have hsub_of : ∀ {a b : ℝ}, a ≤ b → 0 < a → b < Real.pi/2 →
      Set.uIcc a b ⊆ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro a b hab ha hb
    rw [Set.uIcc_of_le hab]
    exact fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hdencont : ContinuousOn (fun x : ℝ => Real.sin x ^ 2 * Real.cos x ^ 3) Set.univ :=
    ((Real.continuous_sin.pow 2).mul (Real.continuous_cos.pow 3)).continuousOn
  have hcontf' : ∀ a b : ℝ, a ≤ b → 0 < a → b < Real.pi/2 → ContinuousOn f' (Set.uIcc a b) := by
    intro a b hab ha hb
    have hsub := hsub_of hab ha hb
    rw [hf'def]
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (hGcont.mono hsub).neg
    · exact hdencont.mono (Set.subset_univ _)
    · intro x hx; exact (hdenom_pos x (hsub hx)).ne'
  have hstep : ∀ a b : ℝ, a ≤ b → 0 < a → b < Real.pi / 2 →
      |∫ t in a..b, f' t| ≤ M * ∫ t in a..b, 1/(Real.sin t^2 * Real.cos t^3) := by
    intro a b hab ha hb
    have hsub := hsub_of hab ha hb
    have hcf := hcontf' a b hab ha hb
    have hpt : ∀ x ∈ Set.Icc a b, |f' x| ≤ M / (Real.sin x^2 * Real.cos x^3) := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := hsub (by rw [Set.uIcc_of_le hab]; exact hx)
      rw [hf'def, abs_div, abs_neg, abs_of_pos (hdenom_pos x hx')]
      exact div_le_div_of_nonneg_right (hM x hx') (le_of_lt (hdenom_pos x hx'))
    have hIi1 : IntervalIntegrable (fun x => |f' x|) volume a b := hcf.abs.intervalIntegrable
    have hcden : ContinuousOn (fun x : ℝ => M / (Real.sin x^2 * Real.cos x^3)) (Set.uIcc a b) := by
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact hdencont.mono (Set.subset_univ _)
      · intro x hx; exact (hdenom_pos x (hsub hx)).ne'
    have hIi2 : IntervalIntegrable (fun x : ℝ => M / (Real.sin x^2 * Real.cos x^3)) volume a b :=
      hcden.intervalIntegrable
    have hfun : (fun x : ℝ => M / (Real.sin x^2 * Real.cos x^3))
        = fun x => M * (1/(Real.sin x^2 * Real.cos x^3)) := by
      funext x; rw [div_eq_mul_one_div]
    calc |∫ t in a..b, f' t| ≤ ∫ t in a..b, |f' t| := intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..b, M / (Real.sin t^2 * Real.cos t^3) :=
          intervalIntegral.integral_mono_on hab hIi1 hIi2 (fun x hx => hpt x hx)
      _ = M * ∫ t in a..b, 1/(Real.sin t^2 * Real.cos t^3) := by
          rw [hfun, intervalIntegral.integral_const_mul]
  have hftcW : ∀ a b : ℝ, a ≤ b → 0 < a → b < Real.pi/2 → ∫ t in a..b, f' t = W b - W a := by
    intro a b hab ha hb
    have hsub := hsub_of hab ha hb
    have hcont : ContinuousOn W (Set.uIcc a b) := hWcont.mono hsub
    rw [Set.uIcc_of_le hab] at hcont
    have hder : ∀ x ∈ Set.Ioo a b, HasDerivAt W (f' x) x := by
      intro x hx
      exact hWderiv x (hsub (by rw [Set.uIcc_of_le hab]; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hder
      (hcontf' a b hab ha hb).intervalIntegrable
  obtain ⟨K1, hK1pos, hK1⟩ := integral_invSinSqCosCu_left
  obtain ⟨K2, hK2pos, hK2⟩ := integral_invSinSqCosCu_right
  set A : ℝ := |W (Real.pi/4)| with hAdef
  set C : ℝ := A + M*K1 + M*K2 with hCdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have htri' : ∀ θ : ℝ, |W θ| ≤ |W θ - W (Real.pi/4)| + |W (Real.pi/4)| := by
    intro θ
    have hh : |W θ - W (Real.pi/4) + W (Real.pi/4)| ≤ |W θ - W (Real.pi/4)| + |W (Real.pi/4)| :=
      abs_add_le _ _
    rwa [sub_add_cancel] at hh
  have hleft : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), θ ≤ Real.pi/4 →
      |W θ| ≤ A + M * (K1/θ) := by
    intro θ hθ hθ4
    have hf := hftcW θ (Real.pi/4) hθ4 hθ.1 hpi4lt
    have hs := hstep θ (Real.pi/4) hθ4 hθ.1 hpi4lt
    rw [hf, abs_sub_comm] at hs
    have hs3 : M * (∫ t in θ..(Real.pi/4), 1/(Real.sin t^2 * Real.cos t^3)) ≤ M * (K1/θ) :=
      mul_le_mul_of_nonneg_left (hK1 θ hθ.1 hθ4) hMnn
    have htri : |W θ| ≤ |W θ - W (Real.pi/4)| + A := by rw [hAdef]; exact htri' θ
    linarith
  have hright : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), Real.pi/4 ≤ θ →
      |W θ| ≤ A + M * (K2/(Real.pi/2 - θ)^2) := by
    intro θ hθ hθ4
    have hf := hftcW (Real.pi/4) θ hθ4 hpi4 hθ.2
    have hs := hstep (Real.pi/4) θ hθ4 hpi4 hθ.2
    rw [hf] at hs
    have hs3 : M * (∫ t in (Real.pi/4)..θ, 1/(Real.sin t^2 * Real.cos t^3)) ≤ M * (K2/(Real.pi/2 - θ)^2) :=
      mul_le_mul_of_nonneg_left (hK2 θ hθ4 hθ.2) hMnn
    have htri : |W θ| ≤ |W θ - W (Real.pi/4)| + A := by rw [hAdef]; exact htri' θ
    linarith
  have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), |u θ * Work.Elliptic.sinCos2 θ| ≤ C := by
    intro θ hθ
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hdnn : 0 ≤ Real.sin θ ^ 2 * Real.cos θ ^ 3 := le_of_lt (hdenom_pos θ hθ)
    have hident : u θ * Work.Elliptic.sinCos2 θ = W θ * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
      rw [hWdef, Work.Elliptic.sinCos2]
      field_simp
    rw [hident, abs_mul, abs_of_nonneg hdnn]
    rcases le_total θ (Real.pi/4) with hle | hge
    · have hb := hleft θ hθ hle
      have htheta1 : θ ≤ 1 := by linarith [Real.pi_lt_four, hle]
      have hs2 : Real.sin θ ^ 2 ≤ θ ^ 2 := Real.sin_sq_le_sq
      have hc3 : Real.cos θ ^ 3 ≤ 1 := pow_le_one₀ (le_of_lt hcos) (Real.cos_le_one θ)
      have hdle : Real.sin θ ^ 2 * Real.cos θ ^ 3 ≤ θ := by
        have h1 : Real.sin θ ^ 2 * Real.cos θ ^ 3 ≤ θ ^ 2 * 1 :=
          mul_le_mul hs2 hc3 (pow_nonneg (le_of_lt hcos) 3) (sq_nonneg θ)
        have h2 : θ ^ 2 ≤ θ := by nlinarith [hθ.1, htheta1]
        linarith
      have hAtheta : A * θ ≤ A := by
        have hh := mul_le_of_le_one_right hA0 htheta1
        linarith [hh]
      have hnn1 : 0 ≤ A + M*(K1/θ) :=
        add_nonneg hA0 (mul_nonneg hMnn (div_nonneg (le_of_lt hK1pos) (le_of_lt hθ.1)))
      calc |W θ| * (Real.sin θ ^ 2 * Real.cos θ ^ 3)
          ≤ (A + M*(K1/θ)) * (Real.sin θ ^ 2 * Real.cos θ ^ 3) :=
            mul_le_mul_of_nonneg_right hb hdnn
        _ ≤ (A + M*(K1/θ)) * θ := mul_le_mul_of_nonneg_left hdle hnn1
        _ = A*θ + M*K1 := by
            rw [add_mul, mul_assoc, div_mul_cancel₀ K1 (ne_of_gt hθ.1)]
        _ ≤ A + M*K1 := by linarith [hAtheta]
        _ ≤ C := by rw [hCdef]; linarith [mul_nonneg hMnn (le_of_lt hK2pos)]
    · have hδpos : 0 < Real.pi/2 - θ := by linarith [hθ.2]
      have hδ1 : Real.pi/2 - θ ≤ 1 := by linarith [hge, Real.pi_lt_four]
      have hs2le1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
      have hcub : Real.cos θ ^ 3 ≤ (Real.pi/2 - θ)^3 := by
        have h1 : Real.cos θ = Real.sin (Real.pi/2 - θ) := (Real.sin_pi_div_two_sub θ).symm
        rw [h1]
        exact pow_le_pow_left₀ (Real.sin_nonneg_of_mem_Icc ⟨hδpos.le, by linarith [hge, Real.pi_pos]⟩)
          (Real.sin_le hδpos.le) 3
      have hdle : Real.sin θ ^ 2 * Real.cos θ ^ 3 ≤ (Real.pi/2 - θ)^2 := by
        have h3 : (Real.pi/2 - θ)^3 ≤ (Real.pi/2 - θ)^2 := by
          have hh : (Real.pi/2 - θ)^3 = (Real.pi/2 - θ)^2 * (Real.pi/2 - θ) := by ring
          rw [hh]
          exact mul_le_of_le_one_right (sq_nonneg _) hδ1
        calc Real.sin θ ^ 2 * Real.cos θ ^ 3 ≤ 1 * (Real.pi/2 - θ)^3 :=
              mul_le_mul hs2le1 hcub (pow_nonneg (le_of_lt hcos) 3) (by norm_num)
          _ ≤ (Real.pi/2 - θ)^2 := by rw [one_mul]; exact h3
      have hδ2le1 : (Real.pi/2 - θ)^2 ≤ 1 := by nlinarith [hδpos, hδ1]
      have hnn2 : 0 ≤ A + M*(K2/(Real.pi/2 - θ)^2) :=
        add_nonneg hA0 (mul_nonneg hMnn (div_nonneg (le_of_lt hK2pos) (sq_nonneg _)))
      have hb := hright θ hθ hge
      calc |W θ| * (Real.sin θ ^ 2 * Real.cos θ ^ 3)
          ≤ (A + M*(K2/(Real.pi/2 - θ)^2)) * (Real.sin θ ^ 2 * Real.cos θ ^ 3) :=
            mul_le_mul_of_nonneg_right hb hdnn
        _ ≤ (A + M*(K2/(Real.pi/2 - θ)^2)) * (Real.pi/2 - θ)^2 :=
            mul_le_mul_of_nonneg_left hdle hnn2
        _ = A*(Real.pi/2 - θ)^2 + M*K2 := by
            rw [add_mul, mul_assoc, div_mul_cancel₀ K2 (ne_of_gt (pow_pos hδpos 2))]
        _ ≤ A + M*K2 := by
            have hh := mul_le_of_le_one_right hA0 hδ2le1
            linarith [hh]
        _ ≤ C := by rw [hCdef]; linarith [mul_nonneg hMnn (le_of_lt hK1pos)]
  have hfin : MeasureTheory.volume (Set.Ioo (0:ℝ) (Real.pi/2)) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hasm : MeasureTheory.AEStronglyMeasurable (fun θ => u θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2))) := by
    have hsincont : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ) (Set.Ioo 0 (Real.pi/2)) := by
      unfold Work.Elliptic.sinCos2
      fun_prop
    have hc : ContinuousOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ) (Set.Ioo 0 (Real.pi/2)) :=
      hu.continuousOn.mul hsincont
    exact hc.aestronglyMeasurable measurableSet_Ioo
  have haeb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2))),
      ‖u θ * Work.Elliptic.sinCos2 θ‖ ≤ C :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => by
      rw [Real.norm_eq_abs]; exact hpt x hx)
  change MeasureTheory.Integrable (fun θ => u θ * Work.Elliptic.sinCos2 θ)
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2)) from by
        rw [Work.Spaces.Iθ]
        exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm]
  exact MeasureTheory.IntegrableOn.of_bound hfin hasm C haeb

end Work.FTS.EllipticEst.remov.SourceBound
