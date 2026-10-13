/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E4R3/Decay3Aux/SlotBound.lean` — the two pointwise slot bounds
for the low slots of an `ℋ⁴`-honest profile

The decay chapter `EpsE4Thr.E4R3.DecayChapter3` needs a **single** majorant `Maj` (independent of
the solution `g`, of `ε` and of the fake time `τ`) dominating the slots `D_z^jD_θ^i f` of order
`j + i ≤ 1` of the projected slice `f = Pz (J_ε g(τ))`, together with `IntegrableOn (Maj · / ·)`
on `(0,∞)`.

Two proved inputs give the two halves of such a majorant, uniformly in the angle:

* the **crude** bound `RXT.hkMem_pointwise_min_sq` (rate `min z 1`), with the explicit constant
  `Cpt α = √(((4/π) + 200/(γ-1))·40)`;
* the **tail** bound, proved here from the two proved modules
  `RXT.Slots.v2_theta_sup_uniform` (`(slot · w)² ≤ K ∫_σ HkIntegrand`, uniform in the angle) and
  `RXT.Slots.v2_agmonZ_noDecay` (the radial Agmon bound `(v z)² w(z)² z ≤ 4∫_z^∞(v w)² +
  ∫_z^∞ (x v' w)²`): applying the second to the `θ`-slice of the slot and dominating the two tail
  integrands by the angular-sup bound gives

    `(D_z^j D_θ^i f z θ)² ≤ 5K · |f|_{ℋ⁴}² · z³/(1+z)⁴`   (`z > 0`, `0 < θ < π/2`, `j + i ≤ 1`),

  whence `|slot z θ| ≤ √(5K)·|f|_{ℋ⁴}·√z·z/(1+z)²` — a `z^{-1/2}` decay at infinity and a `z`
  vanishing at the axis.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay
import Submission.Work.FTS_RegExport.RXT.HkMinSq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.EpsMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The crude pointwise bound with the explicit constant -/

/-- **The crude pointwise bound for the low slots, with the explicit constant**
`Cpt α = √(((4/π) + 200/(γ-1))·40)`: `|D_z^jD_θ^i f z θ| ≤ Cpt α · min z 1 · |f|_{ℋ⁴}`
for `j + i ≤ 2`.  This is the proof of `RXT.hkMem_pointwise_min` with its constant exposed. -/
theorem slot_crude {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} {j i : ℕ} (hji : j + i ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    |Work.Spaces.mixed j i f z θ|
      ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
        * min z 1 * Work.Spaces.HkNorm α 4 f := by
  have hγp : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα
    linarith
  have hC0 : (0 : ℝ) ≤ ((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40 := by
    positivity
  have hmin : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hsq := Work.FTS_RegExport.RXT.hkMem_pointwise_min_sq (α := α) hα hα1 h4 hmem
    (by omega : i + j ≤ 2) hz hθ0 hθ1
  calc |Work.Spaces.mixed j i f z θ|
      = Real.sqrt ((Work.Spaces.mixed j i f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40
          * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
          * min z 1 * Work.Spaces.HkNorm α 4 f := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC0, Real.sqrt_sq hmin]
        rfl

/-! ## The tail bound -/

/-- `Iz = [0,∞)` agrees with `(0,∞)` up to a null set. -/
private theorem Iz_ae_eq_Ioi_d3 : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- `w` is continuous on `(0,∞)`. -/
private theorem continuousOn_w_d3 :
    ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-- **The tail bound for the low slots.**  For a datum which is `C⁴` on the open quadrant and
honestly in `ℋ⁴`, every mixed slot of order `≤ 1` satisfies

  `(D_z^jD_θ^i f z θ)² ≤ C·|f|_{ℋ⁴}²·z³/(1+z)⁴`  (`z > 0`, `0 < θ < π/2`),

with `C` the constant of the angular-sup bound `RXT.Slots.v2_theta_sup_uniform`. -/
theorem slot_tail {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Fn),
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 f → ∀ j i : ℕ, j + i ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        (Work.Spaces.mixed j i f z θ) ^ 2
          ≤ C * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4) := by
  obtain ⟨K, hK0, hK⟩ := Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform (α := α) hα hα1
  refine ⟨5 * K, by positivity, ?_⟩
  intro f h4 hmem j i hji z θ hz hθ0 hθ1
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  set J : ℝ → ℝ := fun x => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ with hJdef
  have hJint : IntegrableOn J Work.Spaces.Iz := by
    rw [hJdef]; exact hmem.2
  have hJnn : ∀ x, 0 ≤ J x :=
    fun x => integral_nonneg (fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f x σ)
  -- the `θ`-slice of a slot with its weight is integrable on `Iz`, dominated by `K * J`
  have slice_int : ∀ (b a : ℕ), a + b ≤ 2 →
      IntegrableOn (fun x => (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2)
        Work.Spaces.Iz := by
    intro b a hba
    have hslice : ContDiffOn ℝ 1 (fun x => Work.Spaces.mixed b a f x θ) (Set.Ioi 0) :=
      Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
        (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b a 1 (by omega))
    refine (hJint.const_mul K).mono' ?_ ?_
    · rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi_d3]
      exact ((hslice.continuousOn.mul continuousOn_w_d3).pow 2).aestronglyMeasurable
        measurableSet_Ioi
    · rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi_d3]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact hK f h4 hmem b a (by omega) x hx θ hθ0 hθ1
  have hint1 : IntegrableOn (fun x => (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz := slice_int j i (by omega)
  have hint2 : IntegrableOn (fun x => (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
      * Work.Spaces.w x) ^ 2) Work.Spaces.Iz := by
    have := slice_int (j + 1) i (by omega)
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ici
    rw [show x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
      = Work.Spaces.mixed (j + 1) i f x θ from rfl]
  -- the pointwise dominations by `K * J`
  have hK1 : ∀ x : ℝ, 0 < x → (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2 ≤ K * J x :=
    fun x hx => hK f h4 hmem j i (by omega) x hx θ hθ0 hθ1
  have hK2 : ∀ x : ℝ, 0 < x →
      (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2 ≤ K * J x :=
    fun x hx => hK f h4 hmem (j + 1) i (by omega) x hx θ hθ0 hθ1
  -- the derivative of the slot's `z`-slice
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun x' => Work.Spaces.mixed j i f x' θ)
        (Work.Spaces.pz (Work.Spaces.mixed j i f) x θ) x := by
    intro x hx
    have hslice : ContDiffOn ℝ 1 (fun x' => Work.Spaces.mixed j i f x' θ) (Set.Ioi 0) :=
      Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
        (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 j i 1 (by omega))
    exact (hslice.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx) |>.hasDerivAt
  -- the radial Agmon bound for the `θ`-slice
  have hmain := Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay
    (v := fun x => Work.Spaces.mixed j i f x θ)
    (v' := fun x => Work.Spaces.pz (Work.Spaces.mixed j i f) x θ) hz hderiv hint1 hint2
  -- the two tail integrals are bounded by `K · HkSq`
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans hz hx)
  have hKJnn : ∀ x, 0 ≤ K * J x := fun x => mul_nonneg hK0 (hJnn x)
  have hKJi : IntegrableOn (fun x => K * J x) Work.Spaces.Iz := hJint.const_mul K
  have htail_le : (∫ x in Work.Spaces.Iz, K * J x) = K * Work.Spaces.HkSq α 4 f := by
    rw [MeasureTheory.integral_const_mul]
    rfl
  have hbd1 : (∫ x in Set.Ioi z, (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
      ≤ K * Work.Spaces.HkSq α 4 f := by
    have hFint : IntegrableOn (fun x => (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
        (Set.Ioi z) := hint1.mono_set hsub
    have hGint : IntegrableOn (fun x => K * J x) (Set.Ioi z) := hKJi.mono_set hsub
    have h1 : (∫ x in Set.Ioi z, (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
        ≤ ∫ x in Set.Ioi z, K * J x :=
      MeasureTheory.setIntegral_mono_on hFint hGint measurableSet_Ioi
        (fun x hx => hK1 x (lt_trans hz hx))
    have h2 : (∫ x in Set.Ioi z, K * J x) ≤ ∫ x in Work.Spaces.Iz, K * J x :=
      MeasureTheory.setIntegral_mono_set hKJi (Filter.Eventually.of_forall hKJnn)
        (Filter.Eventually.of_forall hsub)
    rw [htail_le] at h2
    linarith
  have hbd2 : (∫ x in Set.Ioi z, (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
      * Work.Spaces.w x) ^ 2) ≤ K * Work.Spaces.HkSq α 4 f := by
    have hFint : IntegrableOn (fun x => (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        * Work.Spaces.w x) ^ 2) (Set.Ioi z) := hint2.mono_set hsub
    have hGint : IntegrableOn (fun x => K * J x) (Set.Ioi z) := hKJi.mono_set hsub
    have h1 : (∫ x in Set.Ioi z, (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        * Work.Spaces.w x) ^ 2) ≤ ∫ x in Set.Ioi z, K * J x :=
      MeasureTheory.setIntegral_mono_on hFint hGint measurableSet_Ioi (fun x hx => by
        have hid : x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
            = Work.Spaces.mixed (j + 1) i f x θ := rfl
        rw [hid]
        exact hK2 x (lt_trans hz hx))
    have h2 : (∫ x in Set.Ioi z, K * J x) ≤ ∫ x in Work.Spaces.Iz, K * J x :=
      MeasureTheory.setIntegral_mono_set hKJi (Filter.Eventually.of_forall hKJnn)
        (Filter.Eventually.of_forall hsub)
    rw [htail_le] at h2
    linarith
  -- combine
  have hfin : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
    have h5 : (4 : ℝ) * (∫ x in Set.Ioi z, (Work.Spaces.mixed j i f x θ * Work.Spaces.w x) ^ 2)
        + (∫ x in Set.Ioi z, (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
            * Work.Spaces.w x) ^ 2) ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
      linarith [hbd1, hbd2]
    linarith [hmain, h5]
  -- divide by `w z ^ 2 * z = (1+z)^4/z^3`
  have hwz : (Work.Spaces.w z) ^ 2 * z = (1 + z) ^ 4 / z ^ 3 := by
    rw [Work.Spaces.w, div_pow]
    field_simp
  have hfin' : (Work.Spaces.mixed j i f z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * z)
      ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
    rw [← mul_assoc]; exact hfin
  rw [hwz] at hfin'
  have hpos : 0 < (1 + z) ^ 4 / z ^ 3 := by positivity
  have hgoal : (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ 5 * K * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4) := by
    rw [show z ^ 3 / (1 + z) ^ 4 = ((1 + z) ^ 4 / z ^ 3)⁻¹ by rw [inv_div]]
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hpos).mpr hfin'
  exact hgoal

end Work.FTS.StrongEps.E4R3
