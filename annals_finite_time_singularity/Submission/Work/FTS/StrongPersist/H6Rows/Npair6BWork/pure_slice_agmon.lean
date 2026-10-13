/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pure radial slice Agmon bound from the level-7 weighted integrability

For a datum `f` of class `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, a fixed *interior*
angle `θ`, and `z > 0`, the value of the `j`-th radial derivative `D_z^j f` at `z` is
controlled by the weighted `L²`-norm, over the *whole* half line `Iz = [0,∞)`, of the next
radial derivative:

  `(D_z^j f z θ)² ≤ 2 ∫_{Iz} (D_z^{j+1} f s θ)² w(s)² ds`,  `w(z) = (1+z)²/z²`,  `j ≤ 6`.

The single hypothesis is the integrability of the level-`7` weighted integrand
`Work.Spaces.HkIntegrand α 7 f · θ` on `Iz`.  Because that integrand is a finite sum of
*squares*, its integrability gives in particular the integrability of the two plain radial
slots `(D_z^i f · θ)² w²` for `i ≤ 7`, which are exactly the two integrability hypotheses of
the windowed radial Hardy inequality `Work.FTS.StrongPersist.N6Trans.SixAux.zslice6_hardy`
(the decay hypothesis that the classical radial Hardy inequality needs is replaced by the
integrability of the `L²`-weighted slot — this is what closes the window term).  The
constant is the sharp `2`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.supDz_zslice6
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option linter.unusedVariables false

/-! ## The radial restricted measure -/

/-- `volume.restrict Iz = volume.restrict (0,∞)`: the two restricted measures differ only at
the null point `0`.  (`Iz = [0,∞)`.) -/
theorem restrict_Iz_eq_Ioi :
    (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm

/-! ## Extracting a single radial slot from the level-7 integrability hypothesis -/

/-- **A single radial slot of `HkIntegrand`.**  If the level-`7` weighted integrand based at a
fixed interior angle `θ` is integrable on `Iz`, then so is every plain radial slot
`(D_z^i f · θ)² w²` with `i ≤ 7`.  (The integrand being a finite sum of squares, each
summand is dominated by the sum; the only point to be careful about is that the angular
normalisation `sin(2θ)^{η/2}` is a *nonzero* constant, and that the slot is measurable —
the total is integrable, so it is a.e. strongly measurable, but the slot itself only needs
continuity on the open half line, the difference at `z = 0` being null.) -/
theorem integrableOn_dzIter_sq_w_sq {α : ℝ} {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hInt : IntegrableOn (fun s => Work.Spaces.HkIntegrand α 7 f s θ) Work.Spaces.Iz)
    (i : ℕ) (hi : i ≤ 7) :
    IntegrableOn (fun s => (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz := by
  -- the angular normalisation `c = sin(2θ)^{η/2}` is a positive (hence nonzero) constant
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set c : ℝ := Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) with hcdef
  have hcpos : 0 < c := Real.rpow_pos_of_pos hsin _
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- the angular weight `w · c⁻¹` is continuous on the open half line
  have hwcont : ContinuousOn (fun s : ℝ => Work.Spaces.w s / c) (Set.Ioi 0) := by
    refine ContinuousOn.div_const ?_ c
    change ContinuousOn (fun s : ℝ => (1 + s) ^ 2 / s ^ 2) (Set.Ioi 0)
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))
  -- the `i`-th summand of the first (plain radial) family is a.e. strongly measurable
  have haesm : AEStronglyMeasurable
      (fun s : ℝ => (Work.Spaces.DzIter i f s θ * (Work.Spaces.w s / c)) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    rw [restrict_Iz_eq_Ioi]
    exact ((((hF.DzIter i).curry_z hθ).continuousOn).mul hwcont).pow 2 |>.aestronglyMeasurable
      measurableSet_Ioi
  -- it is dominated by the (integrable) level-7 integrand
  have hIntSlot : IntegrableOn
      (fun s : ℝ => (Work.Spaces.DzIter i f s θ * (Work.Spaces.w s / c)) ^ 2)
      Work.Spaces.Iz :=
    hInt.mono' haesm (Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_z α 7 f s θ i hi)
  -- multiply by the nonzero constant `c²` to obtain the slot with weight `w²`
  have h1 : IntegrableOn
      (fun s : ℝ => c ^ 2 * (Work.Spaces.DzIter i f s θ * (Work.Spaces.w s / c)) ^ 2)
      Work.Spaces.Iz := hIntSlot.const_mul (c ^ 2)
  exact IntegrableOn.congr_fun h1 (fun x _ => by
    show c ^ 2 * (Work.Spaces.DzIter i f x θ * (Work.Spaces.w x / c)) ^ 2
        = (Work.Spaces.DzIter i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2
    field_simp) measurableSet_Ici

/-! ## The target -/

theorem pure_slice_agmon : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (θ : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → θ ∈ Set.Ioo 0 (Real.pi / 2) →
    MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 7 f s θ) Work.Spaces.Iz →
    ∀ (j : ℕ), j ≤ 6 → ∀ z : ℝ, 0 < z →
      (Work.Spaces.DzIter j f z θ) ^ 2
        ≤ 2 * ∫ s in Work.Spaces.Iz, (Work.Spaces.DzIter (j + 1) f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
  intro α f θ hα hα1 hF hθ hInt j hj z hz
  -- the two window integrals of `zslice6_hardy` agree with the two plain radial slots
  have hid : (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter j f) x θ * Work.Spaces.w x) ^ 2)
      = fun x : ℝ => (Work.Spaces.DzIter (j + 1) f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by
    funext x
    rw [show x * Work.Spaces.pz (Work.Spaces.DzIter j f) x θ
        = Work.Spaces.DzIter (j + 1) f x θ from rfl, mul_pow]
  -- the windowed radial Hardy inequality at the fixed angle `θ`
  have hmain := Work.FTS.StrongPersist.N6Trans.SixAux.zslice6_hardy
    (h := fun x => Work.Spaces.DzIter j f x θ)
    (h' := fun x => Work.Spaces.pz (Work.Spaces.DzIter j f) x θ)
    hz (fun x hx => hF.hasDerivAt_slice_DzIter j hθ hx)
    (((hF.DzIter j).curry_z hθ).continuousOn)
    ((((hF.DzIter j).pz).curry_z hθ).continuousOn)
    (integrableOn_dzIter_sq_w_sq hF hθ hInt j (by omega))
    (by rw [hid]; exact integrableOn_dzIter_sq_w_sq hF hθ hInt (j + 1) (by omega))
  rw [hid] at hmain
  simpa using hmain

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
