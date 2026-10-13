import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise `z`-slice bound for the level-6 strong-persistence ladder

For a datum `f` of class `C^∞` on the open quadrant which lies in the weighted space
`ℋ⁶` (`Work.Spaces.HkMem α 6 f`), and for a fixed *interior* angle `θ`, the value at
`z > 0` of the `b`-th radial derivative `D_z^b f` (`b ≤ 5`) is controlled by the weighted
`L²`-norm, over the *whole* half line, of the next radial derivative `D_z^{b+1} f`:

  `(D_z^b f z θ)² ≤ C · ∫_{z' ∈ Iz} (D_z^{b+1} f z' θ)² · w(z')²`,  `w(z) = (1+z)²/z²`.

Two integrability hypotheses on the single slice `z' ↦ D_z^b f z' θ` (for the `b`-th and
the `(b+1)`-st derivative) are part of the statement; they are what replaces the *decay*
hypothesis that the classical radial Hardy inequality `Work.Spaces.HardyZ` needs.  The
proof is the window form of the radial Hardy inequality
(`Work.FTS.TransportS.half_line_window_bound`): for every `R₀ ≥ z`,

  `(h z)² ≤ 2 ∫_{z}^{2R₀} (x h'(x) w(x))² + (2/R₀) ∫_{R₀}^{2R₀} h(x)²`,

the second (window) term is dominated by `(2/R₀) ∫_{Iz} h² w²` because `w ≥ 1` on `(0,∞)`,
and the first term is monotone in `R₀`; letting `R₀ → ∞` and using that the two integrals
are finite gives the bound with the constant `2`.

-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the weight -/

/-- The radial weight `w` is nonnegative everywhere. -/
theorem zslice6_w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

/-- `1 ≤ w z²` for `z > 0`. -/
theorem zslice6_one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 :=
  one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)

/-! ## The one-dimensional radial Hardy bound on a single slice -/

/-- **Radial Hardy inequality without a decay hypothesis.**  Let `h` be of class `C¹` on
`(0,∞)`, with radial derivative `x ↦ x h'(x)`; assume `h` is square integrable against the
weight `w²` and that `x ↦ x h'(x) w(x)` is square integrable on `Iz = [0,∞)`.  Then

  `h(z₀)² ≤ 2 ∫_{Iz} (x h'(x) w(x))² dx`

for every `z₀ > 0`.  (The hypothesis `∫ h² w² < ∞` plays the role of the decay hypothesis
of `Work.Spaces.HardyZ`: it is what forces the window term of the window form of the
inequality to be small.) -/
theorem zslice6_hardy {h h' : ℝ → ℝ} {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hderiv : ∀ x, 0 < x → HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h (Set.Ioi 0)) (hcont' : ContinuousOn h' (Set.Ioi 0))
    (hint : IntegrableOn (fun x => (h x) ^ 2 * (Work.Spaces.w x) ^ 2) Work.Spaces.Iz)
    (hint2 : IntegrableOn (fun x => (x * h' x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz) :
    (h z₀) ^ 2 ≤ 2 * ∫ x in Work.Spaces.Iz, (x * h' x * Work.Spaces.w x) ^ 2 := by
  set P := ∫ x in Work.Spaces.Iz, (x * h' x * Work.Spaces.w x) ^ 2 with hP
  set K := ∫ x in Work.Spaces.Iz, (h x) ^ 2 * (Work.Spaces.w x) ^ 2 with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici
      (fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- the window inequality, for every `R₀ ≥ z₀`
  have key : ∀ R₀ : ℝ, z₀ ≤ R₀ → (h z₀) ^ 2 ≤ 2 * P + (2 / R₀) * K := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz₀ hR
    have hz2R : z₀ ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hcontR : ContinuousOn h (Set.Icc R₀ (2 * R₀)) :=
      hcont.mono fun x hx => lt_of_lt_of_le hRpos hx.1
    have hwin := Work.FTS.TransportS.half_line_window_bound (h := h) (h' := h') hz₀ hR
      (fun x hx => hderiv x (lt_of_lt_of_le hz₀ hx.1)) hcontR
      (hcont'.mono fun x hx => lt_of_lt_of_le hz₀ hx.1)
      (hcontR.pow 2).integrableOn_Icc
    -- the first window integral is at most the full radial integral
    have hAle : ∫ x in z₀..(2 * R₀), (x * h' x * Work.Spaces.w x) ^ 2 ≤ P := by
      rw [intervalIntegral.integral_of_le hz2R, hP]
      refine MeasureTheory.setIntegral_mono_set hint2
        (Eventually.of_forall fun x => sq_nonneg _) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz₀ hx.1)
    -- the window average of `h²` is dominated by `∫ h² w²`, because `w ≥ 1` on `(0,∞)`
    have hBle : ∫ x in R₀..(2 * R₀), (h x) ^ 2 ≤ K := by
      rw [intervalIntegral.integral_of_le hR2R, hK]
      have hsub : Set.Ioc R₀ (2 * R₀) ⊆ Work.Spaces.Iz :=
        fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hInt1 : IntegrableOn (fun x => (h x) ^ 2) (Set.Ioc R₀ (2 * R₀)) :=
        (hcontR.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      have hInt2 : IntegrableOn (fun x => (h x) ^ 2 * (Work.Spaces.w x) ^ 2)
          (Set.Ioc R₀ (2 * R₀)) := hint.mono_set hsub
      have step1 := MeasureTheory.setIntegral_mono_on hInt1 hInt2 measurableSet_Ioc
        (fun x hx => by
          have hw : 1 ≤ (Work.Spaces.w x) ^ 2 :=
            zslice6_one_le_w_sq (lt_trans hRpos hx.1)
          simpa using mul_le_mul_of_nonneg_left hw (sq_nonneg (h x)))
      have step2 := MeasureTheory.setIntegral_mono_set hint
        (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Eventually.of_forall hsub)
      exact le_trans step1 step2
    have hcoef1 : (0 : ℝ) ≤ 2 := by norm_num
    have hcoef2 : (0 : ℝ) ≤ 2 / R₀ := by positivity
    exact le_trans hwin (add_le_add (mul_le_mul_of_nonneg_left hAle hcoef1)
      (mul_le_mul_of_nonneg_left hBle hcoef2))
  -- let `R₀ → ∞`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set R₀ := max z₀ (2 * K / ε) + 1 with hR₀
  have hmax : max z₀ (2 * K / ε) ≤ R₀ := by
    rw [hR₀]; exact le_add_of_nonneg_right zero_le_one
  have hR₀pos : 0 < R₀ :=
    lt_of_lt_of_le (lt_of_lt_of_le hz₀ (le_max_left _ _)) hmax
  have hR₀z : z₀ ≤ R₀ := le_trans (le_max_left _ _) hmax
  have hKle : (2 / R₀) * K ≤ ε := by
    have hlt : 2 * K / ε < R₀ :=
      lt_of_le_of_lt (le_max_right z₀ (2 * K / ε)) (by
        rw [hR₀]; exact lt_add_of_pos_right _ zero_lt_one)
    have h2 : 2 * K / R₀ < ε := by
      rw [div_lt_iff₀ hR₀pos]
      have hlt' : 2 * K < R₀ * ε := (div_lt_iff₀ hε).mp hlt
      rwa [mul_comm R₀ ε] at hlt'
    calc (2 / R₀) * K = 2 * K / R₀ := by ring
      _ ≤ ε := le_of_lt h2
  exact le_trans (key R₀ hR₀z) (add_le_add le_rfl hKle)

/-! ## The target -/

theorem supDz_zslice6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ),
    0 < α → α ≤ 1 → b ≤ 5 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      MeasureTheory.IntegrableOn
        (fun z' => (Work.Spaces.DzIter b f z' θ) ^ 2 * (Work.Spaces.w z') ^ 2) Work.Spaces.Iz →
      MeasureTheory.IntegrableOn
        (fun z' => (Work.Spaces.DzIter (b + 1) f z' θ) ^ 2 * (Work.Spaces.w z') ^ 2) Work.Spaces.Iz →
      (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ C * ∫ z' in Work.Spaces.Iz,
            (Work.Spaces.DzIter (b + 1) f z' θ) ^ 2 * (Work.Spaces.w z') ^ 2 := by
  refine ⟨2, by norm_num, ?_⟩
  intro α f b hα hα1 hb hF hmem z θ hz hθ0 hθ1 hInt0 hInt1
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  -- the identity `x · ∂_z(D_z^b f)(x,θ) = D_z^{b+1} f (x,θ)`, inside the two window integrals
  have hid : (fun x => (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x θ * Work.Spaces.w x) ^ 2)
      = fun z' => (Work.Spaces.DzIter (b + 1) f z' θ) ^ 2 * (Work.Spaces.w z') ^ 2 := by
    funext x
    rw [show x * Work.Spaces.pz (Work.Spaces.DzIter b f) x θ
        = Work.Spaces.DzIter (b + 1) f x θ from rfl, mul_pow]
  have hmain := zslice6_hardy (h := fun x => Work.Spaces.DzIter b f x θ)
    (h' := fun x => Work.Spaces.pz (Work.Spaces.DzIter b f) x θ) hz
    (fun x hx => hF.hasDerivAt_slice_DzIter b hθ hx)
    (((hF.DzIter b).curry_z hθ).continuousOn)
    ((((hF.DzIter b).pz).curry_z hθ).continuousOn)
    (by simpa only [] using hInt0)
    (by rw [hid]; exact hInt1)
  rw [hid] at hmain
  simpa using hmain

end Work.FTS.StrongPersist.N6Trans.SixAux
