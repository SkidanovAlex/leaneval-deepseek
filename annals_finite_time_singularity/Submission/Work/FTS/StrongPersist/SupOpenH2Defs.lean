import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.L3Rhs.AuxAgmon
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts -/

theorem sin_two_pos_of_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
  nlinarith [sq_nonneg (1 + z), hz.le, sq_nonneg z]

theorem w_sq_mul_self_ge {z : ℝ} (hz : 0 < z) : (256 : ℝ) / 27 ≤ (Work.Spaces.w z) ^ 2 * z := by
  have hid : 27 * (1 + z) ^ 4 - 256 * z ^ 3 = (z - 3) ^ 2 * (27 * z ^ 2 + 14 * z + 3) := by ring
  have hnn : 0 ≤ (z - 3) ^ 2 * (27 * z ^ 2 + 14 * z + 3) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hkey : 256 * z ^ 3 ≤ 27 * (1 + z) ^ 4 := by
    have : 0 ≤ 27 * (1 + z) ^ 4 - 256 * z ^ 3 := by rw [hid]; exact hnn
    linarith
  rw [Work.Spaces.w, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (z ^ 2) ^ 2)]
  nlinarith [hkey, hz]

theorem sin_two_neg_eta_one_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hpos := sin_two_pos_of_Q0 hθ
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have heta : 0 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  calc (1 : ℝ) = (Real.sin (2 * θ)) ^ (0 : ℝ) := (Real.rpow_zero _).symm
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_exponent_ge hpos hle1 (by linarith)

theorem sin_two_half_sq_neg {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [pow_two, ← Real.rpow_add (sin_two_pos_of_Q0 hθ)]
  ring_nf

theorem sin_two_half_sq_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
  rw [pow_two, ← Real.rpow_add (sin_two_pos_of_Q0 hθ)]
  ring_nf

/-! ## The derivative of `w z * √z` and its bounds -/

theorem hasDerivAt_sq (z : ℝ) : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
  have h : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℕ) * z ^ (2 - 1)) z := hasDerivAt_pow 2 z
  convert h using 1
  norm_num

theorem hasDerivAt_one_add_sq (z : ℝ) :
    HasDerivAt (fun z' : ℝ => (1 + z') ^ 2) (2 * (1 + z)) z := by
  have h0 : HasDerivAt (fun y : ℝ => 1 + y) (1 : ℝ) z := (hasDerivAt_id z).const_add 1
  have h : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℕ) * (1 + z) ^ (2 - 1)) (1 + z) :=
    hasDerivAt_pow 2 (1 + z)
  have hc := h.comp z h0
  have h1 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 2)
      ((2 : ℕ) * (1 + z) ^ (2 - 1) * 1) z := by
    refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' => ?_)
    simp only [Function.comp_def]
  convert h1 using 1
  norm_num

/-- The derivative of `w z * √z`. -/
noncomputable def dWsq (z : ℝ) : ℝ := ((Work.Spaces.w z * Real.sqrt z) * (z - 3)) / (2 * z * (1 + z))

theorem hasDerivAt_dWsq {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => Work.Spaces.w z' * Real.sqrt z') (dWsq z) z := by
  have hz2 : z ^ 2 ≠ 0 := by positivity
  have hA : HasDerivAt (fun z' : ℝ => (1 + z') ^ 2 / z' ^ 2)
      ((2 * (1 + z) * z ^ 2 - (1 + z) ^ 2 * (2 * z)) / (z ^ 2) ^ 2) z :=
    (hasDerivAt_one_add_sq z).div (hasDerivAt_sq z) hz2
  have hB : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt z)) z := Real.hasDerivAt_sqrt (ne_of_gt hz)
  have h := hA.mul hB
  have h1 : HasDerivAt (fun z' : ℝ => Work.Spaces.w z' * Real.sqrt z')
      ((2 * (1 + z) * z ^ 2 - (1 + z) ^ 2 * (2 * z)) / (z ^ 2) ^ 2 * Real.sqrt z
        + (1 + z) ^ 2 / z ^ 2 * (1 / (2 * Real.sqrt z))) z := by
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' => ?_)
    simp only [Pi.mul_apply, Work.Spaces.w]
  convert h1 using 1
  · rw [dWsq, Work.Spaces.w]
    field_simp
    nlinarith [Real.sq_sqrt hz.le]

theorem Wsq_sq {z : ℝ} (hz : 0 ≤ z) :
    (Work.Spaces.w z * Real.sqrt z) ^ 2 = (Work.Spaces.w z) ^ 2 * z := by
  rw [mul_pow, Real.sq_sqrt hz]

theorem z_mul_dWsq_sq_le {z : ℝ} (hz : 0 < z) :
    z * (dWsq z) ^ 2 ≤ (9 / 4) * (Work.Spaces.w z) ^ 2 := by
  have hs : Real.sqrt z * Real.sqrt z = z := by
    rw [← sq, Real.sq_sqrt hz.le]
  rw [dWsq, Work.Spaces.w, div_pow]
  field_simp
  nlinarith [hs, sq_nonneg (z - 3), sq_nonneg (1 + z), hz.le, sq_nonneg z]

theorem abs_div_ge_le {z : ℝ} (hz : 0 < z) :
    (z - 3) ^ 2 / (1 + z) ^ 2 ≤ 9 := by
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (z - 3), sq_nonneg (1 + z), hz.le]

/-! ## Continuity of the auxiliary factors -/

theorem continuousOn_w :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rw [Work.Spaces.w]
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Set.mem_prod.mp hp).1)

theorem continuousOn_w_mul_sqrt :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 * Real.sqrt p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  continuousOn_w.mul continuousOn_fst.sqrt

end Work.FTS.StrongPersist

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Nonnegativity of `HkIntegrand` -/

/-- Nonnegativity of `HkIntegrand`.

**Renaming note.**  The same general fact is also declared as `HkIntegrand_nonneg` in
`Submission/Work/FTS/StrongPersist/Basic.lean`.  Both would be top-level declarations in the
namespace `Work.FTS.StrongPersist`, so any module importing *both* files fails to elaborate (Lean
rejects the duplicate name).  The declaration here is **unused** outside this file, so it is kept
under the distinct name `HkIntegrand_nonneg_gen`; `Basic`'s copy is the one the chain uses. -/
theorem HkIntegrand_nonneg_gen (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  exact add_nonneg (Work.Spaces.hkZSum_nonneg α k f z θ) (Work.Spaces.hkMixedSum_nonneg α k f z θ)

/-! ## The comparison `∫ u² ≤ 2 ∫ u² σ^{-η}` -/

theorem aesm_sq_slice_of_SmoothOpen {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (h z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (fun θ => (h z θ) ^ 2)
      (volume.restrict (Set.Ioo 0 (π / 2))) :=
    (((hso.curry_θ hz).continuousOn).aestronglyMeasurable measurableSet_Ioo).pow 2
  have hmeq : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))
  rwa [hmeq] at h1

theorem int_sq_le_two_weighted {u : ℝ → ℝ}
    (haesm : AEStronglyMeasurable (fun θ => (u θ) ^ 2) (volume.restrict Work.Spaces.Iθ))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      ≤ 2 * (∫ θ in Work.Spaces.Iθ,
          (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (u θ) ^ 2 ≤ (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h1 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
        (u θ) ^ 2 ≤ (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Eventually.of_forall fun θ hθ => by
        have hle := sin_two_neg_eta_one_le hθ
        nlinarith [sq_nonneg (u θ)]
    have hmeq : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Work.Spaces.Iθ :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))
    rwa [hmeq] at h1
  have hae' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖(u θ) ^ 2‖ ≤ (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [hae] with θ hθ
    rwa [Real.norm_of_nonneg (sq_nonneg (u θ))]
  have hu2 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    Integrable.mono' hint haesm hae'
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    setIntegral_nonneg measurableSet_Icc fun θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (sin_two_nonneg_of_Iθ hθ) _)
  calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        MeasureTheory.integral_mono_ae hu2 hint hae
    _ ≤ 2 * (∫ θ in Work.Spaces.Iθ,
          (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by linarith

/-! ## Slot integrability: inner (angular) and outer (radial) -/

theorem slot_inner {α : ℝ} {k : ℕ} {h S : ℝ → ℝ → ℝ}
    (hScont : ContinuousOn (Function.uncurry S) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : Work.Spaces.HkMem α k h)
    (hSnn : ∀ z θ, 0 ≤ S z θ) (hSle : ∀ z θ, S z θ ≤ Work.Spaces.HkIntegrand α k h z θ) :
    ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => S z θ) Work.Spaces.Iθ := by
  intro z hz
  have haesm : AEStronglyMeasurable (fun θ => S z θ) (volume.restrict Work.Spaces.Iθ) := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
    · rw [← h0]
      have hzero : (fun θ => S 0 θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        have h1 := hSle 0 θ
        rw [Work.Spaces.HkIntegrand_zero_z] at h1
        exact le_antisymm h1 (hSnn 0 θ)
      rw [hzero]; exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hScont hpos
  refine Integrable.mono' (hmem.1 z hz) haesm ?_
  rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
  exact Eventually.of_forall fun θ _ => by
    rw [Real.norm_of_nonneg (hSnn z θ)]
    exact hSle z θ

theorem slot_outer {α : ℝ} {k : ℕ} {h S : ℝ → ℝ → ℝ}
    (hScont : ContinuousOn (Function.uncurry S) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : Work.Spaces.HkMem α k h)
    (hSnn : ∀ z θ, 0 ≤ S z θ) (hSle : ∀ z θ, S z θ ≤ Work.Spaces.HkIntegrand α k h z θ) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, S z θ) Work.Spaces.Iz := by
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, S z θ)
      (volume.restrict Work.Spaces.Iz) := by
    have h1 := (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry S) hScont).integral_prod_right'
    have heq : (fun z => ∫ θ, Function.uncurry S (z, θ) ∂(volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ, S z θ) := by
      funext z; rfl
    rwa [heq] at h1
  refine Integrable.mono' hmem.2 haesm ?_
  rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
  refine Eventually.of_forall fun z hz => ?_
  have h1 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, S z θ := integral_nonneg fun θ => hSnn z θ
  rw [Real.norm_of_nonneg h1]
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => hSnn z θ) (hmem.1 z hz)
    (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => hSle z θ)

end Work.FTS.StrongPersist

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The weighted-square identity -/

theorem sin_two_neg_half_sq_gen {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((Real.sin (2 * θ)) ^ (-(p / 2))) ^ 2 = (Real.sin (2 * θ)) ^ (-p) := by
  rw [pow_two, ← Real.rpow_add (sin_two_pos_of_Q0 hθ)]
  ring_nf

theorem sin_two_pos_half_sq_gen {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((Real.sin (2 * θ)) ^ (p / 2)) ^ 2 = (Real.sin (2 * θ)) ^ p := by
  rw [pow_two, ← Real.rpow_add (sin_two_pos_of_Q0 hθ)]
  ring_nf

theorem div_sin_half_sq_gen {z θ p : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (p / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-p) := by
  have hs := sin_two_nonneg_of_Iθ hθ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0]
    have h1 : (0 : ℝ) ^ (p / 2) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    have h2 : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    rw [h1, h2]
    ring
  · have hθ' : θ ∈ Set.Ioo 0 (π / 2) := by
      refine ⟨lt_of_le_of_ne hθ.1 ?_, lt_of_le_of_ne hθ.2 ?_⟩
      · intro h; rw [← h] at hspos; rw [mul_zero, Real.sin_zero] at hspos
        exact absurd hspos (lt_irrefl 0)
      · intro h; rw [h] at hspos; rw [show 2 * (π / 2) = Real.pi by ring, Real.sin_pi] at hspos
        exact absurd hspos (lt_irrefl 0)
    rw [div_pow, sin_two_pos_half_sq_gen hθ', div_eq_mul_inv, ← Real.rpow_neg hspos.le]

theorem ws_sq_eq_gen {z θ p : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    (Work.Spaces.w z * Real.sqrt z * (Real.sin (2 * θ)) ^ (-(p / 2))) ^ 2
      = z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (p / 2)) ^ 2 := by
  have hs := sin_two_nonneg_of_Iθ hθ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0]
    have h1 : (0 : ℝ) ^ (-(p / 2)) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    have h2 : (0 : ℝ) ^ (p / 2) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    rw [h1, h2]
    ring
  · have hθ' : θ ∈ Set.Ioo 0 (π / 2) := by
      refine ⟨lt_of_le_of_ne hθ.1 ?_, lt_of_le_of_ne hθ.2 ?_⟩
      · intro h; rw [← h] at hspos; rw [mul_zero, Real.sin_zero] at hspos
        exact absurd hspos (lt_irrefl 0)
      · intro h; rw [h] at hspos; rw [show 2 * (π / 2) = Real.pi by ring, Real.sin_pi] at hspos
        exact absurd hspos (lt_irrefl 0)
    rw [mul_pow, mul_pow, Real.sq_sqrt hz, sin_two_neg_half_sq_gen hθ', div_sin_half_sq_gen hθ hp]
    ring

end Work.FTS.StrongPersist

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

theorem eta_ne_zero : Work.Spaces.eta ≠ 0 := by rw [Work.Spaces.eta]; norm_num

/-- `(x · σ^{-p/2})² = x² · σ^{-p}` on `Iθ`. -/
theorem mul_sin_neg_half_sq {x θ p : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    (x * (Real.sin (2 * θ)) ^ (-(p / 2))) ^ 2
      = x ^ 2 * (Real.sin (2 * θ)) ^ (-p) := by
  have hs := sin_two_nonneg_of_Iθ hθ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0]
    have h1 : (0 : ℝ) ^ (-(p / 2)) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    have h2 : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    rw [h1, h2]; ring
  · have hθ' : θ ∈ Set.Ioo 0 (π / 2) := by
      refine ⟨lt_of_le_of_ne hθ.1 ?_, lt_of_le_of_ne hθ.2 ?_⟩
      · intro h; rw [← h] at hspos; rw [mul_zero, Real.sin_zero] at hspos
        exact absurd hspos (lt_irrefl 0)
      · intro h; rw [h] at hspos; rw [show 2 * (π / 2) = Real.pi by ring, Real.sin_pi] at hspos
        exact absurd hspos (lt_irrefl 0)
    rw [mul_pow, sin_two_neg_half_sq_gen (p := p) hθ']

theorem slot0_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter 0 h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  show (h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = _
  rw [mul_pow, div_sin_half_sq_gen hθ eta_ne_zero]
  ring

theorem slot1_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter 1 h z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * z ^ 2
          * ((Work.Spaces.pz h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  show (Work.Spaces.Dz h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = _
  rw [show Work.Spaces.Dz h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = (z * Work.Spaces.pz h z θ) * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      from rfl]
  rw [show ((z * Work.Spaces.pz h z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.pz h z θ) ^ 2
        * (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by ring]
  rw [mul_pow, div_sin_half_sq_gen hθ eta_ne_zero]
  ring

theorem dWsq_sq_id {z : ℝ} (hz : 0 < z) :
    (dWsq z) ^ 2 = (Work.Spaces.w z) ^ 2 * ((z - 3) ^ 2 / (4 * z * (1 + z) ^ 2)) := by
  rw [dWsq, Work.Spaces.w]
  field_simp
  nlinarith [Real.sq_sqrt hz.le]

theorem PhiA_sq_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (h z θ * (Work.Spaces.w z * Real.sqrt z)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * z * ((h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [mul_sin_neg_half_sq (x := h z θ * (Work.Spaces.w z * Real.sqrt z)) hθ eta_ne_zero,
      show (h z θ * (Work.Spaces.w z * Real.sqrt z)) ^ 2
        = (h z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * z from by
        rw [mul_pow, mul_pow, Real.sq_sqrt hz.le]; ring]
  ring

theorem pz_term_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * z
          * ((Work.Spaces.pz h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [mul_sin_neg_half_sq (x := Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)) hθ
        eta_ne_zero,
      show (Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)) ^ 2
        = (Work.Spaces.pz h z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * z from by
        rw [mul_pow, mul_pow, Real.sq_sqrt hz.le]; ring]
  ring

theorem d_term_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (h z θ * dWsq z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((z - 3) ^ 2 / (4 * z * (1 + z) ^ 2))
          * ((h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [mul_sin_neg_half_sq (x := h z θ * dWsq z) hθ eta_ne_zero,
      show (h z θ * dWsq z) ^ 2 = (h z θ) ^ 2 * (dWsq z) ^ 2 from by ring,
      dWsq_sq_id hz]
  ring

theorem continuousOn_sin_pow (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ q) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
  intro p hp
  exact Or.inl (ne_of_gt (sin_two_pos_of_Q0 (Set.mem_prod.mp hp).2))

theorem continuousOn_dWsq :
    ContinuousOn (fun p : ℝ × ℝ => dWsq p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hfun : (fun p : ℝ × ℝ => dWsq p.1)
      = fun p : ℝ × ℝ => ((Work.Spaces.w p.1 * Real.sqrt p.1) * (p.1 - 3)) / (2 * p.1 * (1 + p.1)) := by
    funext p; rw [dWsq]
  rw [hfun]
  refine ContinuousOn.div (continuousOn_w_mul_sqrt.mul (continuousOn_fst.sub continuousOn_const))
    ((continuousOn_const.mul continuousOn_fst).mul (continuousOn_const.add continuousOn_fst)) ?_
  intro p hp
  have hz : (0:ℝ) < p.1 := (Set.mem_prod.mp hp).1
  positivity


theorem gam_ne_zero {α : ℝ} (hα : 0 < α) : Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

theorem Wt_eq (α z θ : ℝ) :
    Work.Spaces.Wt α z θ = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]

theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  rw [show (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) from by
    funext p; rw [Wt_eq]]
  exact continuousOn_w.mul (continuousOn_sin_pow _)

theorem sqmul_unfold (X : ℝ) {z θ p : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    (X * (Work.Spaces.w z * Real.sqrt z) * (Real.sin (2 * θ)) ^ (-(p / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * z * (X ^ 2 * (Real.sin (2 * θ)) ^ (-p)) := by
  rw [mul_sin_neg_half_sq (x := X * (Work.Spaces.w z * Real.sqrt z)) hθ hp,
      show (X * (Work.Spaces.w z * Real.sqrt z)) ^ 2 = X ^ 2 * (Work.Spaces.w z) ^ 2 * z from by
        rw [mul_pow, mul_pow, Real.sq_sqrt hz.le]; ring]
  ring

theorem slot_unfold_gen (X : ℝ) {z θ p : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (p / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (X ^ 2 * (Real.sin (2 * θ)) ^ (-p)) := by
  rw [mul_pow, div_sin_half_sq_gen hθ hp]
  ring



theorem sm_unfold_gen (X : ℝ) {z θ α : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hγ : Work.Spaces.gam α ≠ 0) :
    (X * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (X ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  rw [Wt_eq]
  rw [show (X * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = ((X * Work.Spaces.w z) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      from by ring]
  rw [mul_sin_neg_half_sq (x := X * Work.Spaces.w z) hθ hγ, mul_pow]
  ring


theorem gam_lt_two {α : ℝ} (hα1 : α ≤ 1) : Work.Spaces.gam α < 2 := by
  rw [Work.Spaces.gam]; linarith

theorem gam_ne_two {α : ℝ} (hα1 : α ≤ 1) : Work.Spaces.gam α ≠ 2 :=
  ne_of_lt (gam_lt_two hα1)

/-- `(σ^{-p/2})² = σ^{-p}` on `Iθ`. -/
theorem sin_two_neg_half_sq_Iθ {θ p : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    ((Real.sin (2 * θ)) ^ (-(p / 2))) ^ 2 = (Real.sin (2 * θ)) ^ (-p) := by
  have hs := sin_two_nonneg_of_Iθ hθ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0]
    have h1 : (0 : ℝ) ^ (-(p / 2)) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    have h2 : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    rw [h1, h2]; ring
  · rw [pow_two, ← Real.rpow_add hspos]; ring_nf

/-- `σ^2 · σ^{-p} = σ^{2-p}` on `Iθ`. -/
theorem sin_two_sq_mul_neg_Iθ {θ p : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 2) :
    (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-p)
      = (Real.sin (2 * θ)) ^ (2 - p) := by
  have hs := sin_two_nonneg_of_Iθ hθ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0]
    have h2 : (0 : ℝ) ^ (2 - p) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    rw [h2]; ring
  · rw [show (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ (2 : ℝ) from
      (Real.rpow_natCast _ 2).symm]
    rw [← Real.rpow_add hspos]; ring_nf

/-- Inner (angular) integrability of a mixed slot of the `ℋ²`-integrand. -/
theorem slot_mixed_inner {α : ℝ} {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    ∀ z ∈ Work.Spaces.Iz, IntegrableOn
      (fun θ => (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i h p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (((hso.mixed j i).continuousOn).mul (continuousOn_Wt α)).pow 2
  exact slot_inner hcont hmem (fun _ _ => sq_nonneg _)
    (fun z θ => Work.Spaces.sq_le_HkIntegrand_mixed α 2 h z θ i j hi hij)

theorem slot_z_inner {α : ℝ} {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) (i : ℕ) (hi : i ≤ 2) :
    ∀ z ∈ Work.Spaces.Iz, IntegrableOn
      (fun θ => (Work.Spaces.DzIter i h z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ :=
  fun z hz => Work.FTS.EllipticEst.integrableOn_zSummand α 2 hso hmem i hi hz

/-- `∫_θ h² σ^{-η}` is finite on the angular slice. -/
theorem integrableOn_hsq_sEta {α : ℝ} {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => (h z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hslot := slot_z_inner hso hmem 0 (by norm_num) z (Set.mem_Ici.mpr hz.le)
  have hw2 : ((Work.Spaces.w z) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt (w_pos_of_pos hz))
  have heq : ∀ θ ∈ Work.Spaces.Iθ, ((Work.Spaces.w z) ^ 2)⁻¹
        * (Work.Spaces.DzIter 0 h z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    rw [show Work.Spaces.DzIter 0 h z θ = h z θ from rfl]
    rw [slot_unfold_gen (h z θ) hθ eta_ne_zero]
    exact inv_mul_cancel_left₀ hw2 _
  exact IntegrableOn.congr_fun (hslot.const_mul _) heq measurableSet_Icc

/-- `∫_θ h²` is finite on the angular slice. -/
theorem integrableOn_hsq {α : ℝ} {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => (h z θ) ^ 2) Work.Spaces.Iθ := by
  refine Integrable.mono' (integrableOn_hsq_sEta hso hmem hz)
    (aesm_sq_slice_of_SmoothOpen hso hz) ?_
  have h1 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ‖(h z θ) ^ 2‖ ≤ (h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun θ hθ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hle := sin_two_neg_eta_one_le hθ
      nlinarith [sq_nonneg (h z θ)]
  have hmeq : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))
  rwa [hmeq] at h1

/-- `∫_θ (∂_θ h)² σ^{2-γ}` is finite on the angular slice. -/
theorem integrableOn_pth_sq {α : ℝ} {h : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen h) (hmem : Work.Spaces.HkMem α 2 h) {z : ℝ}
    (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.pth h z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hγ0 : Work.Spaces.gam α ≠ 0 := gam_ne_zero hα
  have hγ2 : Work.Spaces.gam α ≠ 2 := gam_ne_two hα1
  have hslot := slot_mixed_inner hso hmem 0 1 (by norm_num) (by norm_num) z
    (Set.mem_Ici.mpr hz.le)
  have hw2 : ((Work.Spaces.w z) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt (w_pos_of_pos hz))
  have heq : ∀ θ ∈ Work.Spaces.Iθ, ((Work.Spaces.w z) ^ 2)⁻¹
        * (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.pth h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    intro θ hθ
    rw [show Work.Spaces.mixed 0 1 h z θ = Work.Spaces.Dth h z θ from rfl]
    rw [show Work.Spaces.Dth h z θ
        = Real.sin (2 * θ) * Work.Spaces.pth h z θ from rfl]
    rw [sm_unfold_gen (Real.sin (2 * θ) * Work.Spaces.pth h z θ) hθ hγ0]
    rw [inv_mul_cancel_left₀ hw2]
    rw [mul_pow]
    rw [show (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.pth h z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.pth h z θ) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        from by ring]
    rw [sin_two_sq_mul_neg_Iθ (p := Work.Spaces.gam α) hθ hγ2]
  exact IntegrableOn.congr_fun (hslot.const_mul _) heq measurableSet_Icc


end Work.FTS.StrongPersist
