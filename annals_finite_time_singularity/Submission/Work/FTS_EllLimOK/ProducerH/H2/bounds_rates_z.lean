import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `∂_z`-clauses of `bounds_rates`: the operator `D_z^j (E g)` (`j ≤ 2`) obeys the rate
`min θ (π/2-θ)` of `psiDz_rate`; dividing by `z ≥ a₀` turns this into the plain partial
derivatives of the two first radial orders, with the rates `θ`, `π/2-θ` and `1`. -/
theorem bounds_rates_z {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
        |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
        |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) ∧
        |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) := by
  obtain ⟨Cψ, hCψpos, hCψ⟩ := Work.FTS_EllLimOK.ProducerH.BoxAux.psiDz_rate hα hα4 hE ha₀ hab
  set D : ℝ := Cψ + 2 * Cψ + 1 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  set C : ℝ := (1 + 1 / a₀ + 1 / a₀ ^ 2) * D with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCψD : Cψ ≤ D := by rw [hDdef]; linarith [hCψpos]
  have h2CψD : 2 * Cψ ≤ D := by rw [hDdef]; linarith [hCψpos]
  have h1a0 : (0 : ℝ) ≤ 1 / a₀ := by positivity
  have h1a02 : (0 : ℝ) ≤ 1 / a₀ ^ 2 := by positivity
  have hfacA : 1 / a₀ ≤ 1 + 1 / a₀ + 1 / a₀ ^ 2 := by linarith
  have hfacA2 : 1 / a₀ ^ 2 ≤ 1 + 1 / a₀ + 1 / a₀ ^ 2 := by linarith
  have hCA1 : Cψ / a₀ ≤ C := by
    rw [hCdef]
    calc Cψ / a₀ = Cψ * (1 / a₀) := by ring
      _ ≤ D * (1 / a₀) := mul_le_mul_of_nonneg_right hCψD h1a0
      _ ≤ D * (1 + 1 / a₀ + 1 / a₀ ^ 2) := mul_le_mul_of_nonneg_left hfacA hDpos.le
      _ = (1 + 1 / a₀ + 1 / a₀ ^ 2) * D := by ring
  have hCA3 : 2 * Cψ / a₀ ^ 2 ≤ C := by
    rw [hCdef]
    calc 2 * Cψ / a₀ ^ 2 = (2 * Cψ) * (1 / a₀ ^ 2) := by ring
      _ ≤ D * (1 / a₀ ^ 2) := mul_le_mul_of_nonneg_right h2CψD h1a02
      _ ≤ D * (1 + 1 / a₀ + 1 / a₀ ^ 2) := mul_le_mul_of_nonneg_left hfacA2 hDpos.le
      _ = (1 + 1 / a₀ + 1 / a₀ ^ 2) * D := by ring
  refine ⟨C, hCpos, ?_⟩
  intro g hg z hz θ hθ
  have hzpos : 0 < z := lt_of_lt_of_le ha₀ hz.1
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  have hm0 : 0 ≤ min θ (π / 2 - θ) := le_of_lt (mm_pos hθ)
  have hmθ : min θ (π / 2 - θ) ≤ θ := mm_le_theta θ
  have hmπ : min θ (π / 2 - θ) ≤ π / 2 - θ := mm_le_pi_sub θ
  have hm1 : min θ (π / 2 - θ) ≤ 1 := mm_le_one ⟨hθ.1.le, hθ.2.le⟩
  have hpz1 : |Work.Spaces.pz (E g) z θ| ≤ (Cψ / a₀) * Work.FTS.StrongGlobal.Xn6 α g
      * min θ (π / 2 - θ) := by
    have hDz1 := hCψ g hg 1 (by norm_num) z hz θ hθ
    have hraw : |Work.Spaces.pz (E g) z θ|
        ≤ (Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ)) / a₀ := by
      refine br_le_div_const (x := |Work.Spaces.pz (E g) z θ|)
        (A := Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ))
        (z := z) (c := a₀) hzpos (by positivity) ha₀ hz.1 ?_
      calc z * |Work.Spaces.pz (E g) z θ|
          = |Work.Spaces.DzIter 1 (E g) z θ| := by
            rw [show Work.Spaces.DzIter 1 (E g) z θ = z * Work.Spaces.pz (E g) z θ from rfl,
              abs_mul, abs_of_pos hzpos]
        _ ≤ Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := hDz1
    calc |Work.Spaces.pz (E g) z θ|
        ≤ (Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ)) / a₀ := hraw
      _ = (Cψ / a₀) * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := by ring
  have hpz2 : |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ|
      ≤ (2 * Cψ / a₀ ^ 2) * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := by
    have hslice : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        ContDiffOn ℝ 2 (fun z' => (E g) z' θ') (Set.Ioi 0) :=
      fun θ' hθ' => (hΨsm.curry_z hθ').of_le (by norm_num)
    have hsq := Work.FTS_EllLimOK.ProducerH.SecondDeriv.zsq_pzIter_two_eq
      (h := E g) hslice hzpos hθ
    simp only [Work.Spaces.mixed_zero_right] at hsq
    have hDz1 := hCψ g hg 1 (by norm_num) z hz θ hθ
    have hDz2 := hCψ g hg 2 (by norm_num) z hz θ hθ
    have hident : z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (E g)) z θ
        = Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ := by
      rw [show Work.Spaces.pz (Work.Spaces.pz (E g)) = Work.Spaces.pzIter 2 (E g) from rfl]
      exact hsq
    have htri : |Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ|
        ≤ |Work.Spaces.DzIter 2 (E g) z θ| + |Work.Spaces.DzIter 1 (E g) z θ| :=
      br_abs_sub_le_abs_add_abs _ _
    have hraw : |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ|
        ≤ (2 * Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ)) / a₀ ^ 2 := by
      refine br_le_div_const (x := |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ|)
        (A := 2 * Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ))
        (z := z ^ 2) (c := a₀ ^ 2) (by positivity) (by positivity) (by positivity)
        (by nlinarith [ha₀, hz.1]) ?_
      have hz2 : 0 < z ^ 2 := by positivity
      calc z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ|
          = |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| := by
            rw [abs_mul, abs_of_pos hz2]
        _ = |Work.Spaces.DzIter 2 (E g) z θ - Work.Spaces.DzIter 1 (E g) z θ| := by rw [hident]
        _ ≤ |Work.Spaces.DzIter 2 (E g) z θ| + |Work.Spaces.DzIter 1 (E g) z θ| := htri
        _ ≤ Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ)
              + Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := add_le_add hDz2 hDz1
        _ = 2 * Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := by ring
    calc |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ|
        ≤ (2 * Cψ * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ)) / a₀ ^ 2 := hraw
      _ = (2 * Cψ / a₀ ^ 2) * Work.FTS.StrongGlobal.Xn6 α g * min θ (π / 2 - θ) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using br_squeeze_rate hpz1 (by positivity) hCA1 hX0 hm0 hm1
  · simpa using br_squeeze_rate hpz2 (by positivity) hCA3 hX0 hm0 hm1
  · exact br_squeeze_rate hpz1 (by positivity) hCA1 hX0 hm0 hmθ
  · exact br_squeeze_rate hpz2 (by positivity) hCA3 hX0 hm0 hmθ
  · exact br_squeeze_rate hpz1 (by positivity) hCA1 hX0 hm0 hmπ
  · exact br_squeeze_rate hpz2 (by positivity) hCA3 hX0 hm0 hmπ

end Work.FTS_EllLimOK.ProducerH.H2
