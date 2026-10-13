/-
Copyright: work module for the Elgindi finite-time singularity project.

# `L6Flux/flux_prod_le`: the level-six flux term with an `L^∞` coefficient

The target is the product-measure bound

`|∫∫ canonW q · f · D_z(D_z^bD_θ^a g) · (D_z^bD_θ^a g)| ≤ 2 Mf |g|²_{ℋ⁶}`,  `a + b = 6`,

for a coefficient `f` with `|f| ≤ Mf` and `|D_z f| ≤ Mf` on the open quadrant, a datum `g`
smooth there and honestly in `ℋ⁶ ∩ ℋ⁷`, and an exponent `q` in the slot range
(`q ≤ γ(α)`, and `q ≤ η` when `a = 0`).

## Route

* at each angle `θ` the radial integration by parts of
  `Submission/Work/FTS/StrongPersist/N6Trans/L6Flux/zibp_Ioi_of_integrable.lean` turns the
  flux `∫_z canonW q · f · (z ∂_z V) · V` (`V = D_z^bD_θ^a g`) into
  `-(1/2)∫_z ∂_z(z w² f) · V²`; the two boundary terms are *derived* from the `L¹`
  hypotheses, so no decay or boundary-trace hypothesis is needed, and the angular factor
  `sin(2θ)^{-q}` is a constant of the slice (`zibp_bound`, `fluxSliceLe6` below);
* `|∂_z(z w² f)| ≤ |z ∂_z f| w² + 3 Mf w² ≤ 4 Mf w²` because `|(z-3)/(1+z)| ≤ 3`
  (`Work.FTS.H2.abs_ratio_le_three`), which produces exactly the constant `2`;
* the surviving energy `∫∫ canonW q · V²` is a level-six slot, dominated by
  `HkIntegrand α 6 g` and hence bounded by `HkSq α 6 g`: this is the *proved*
  `Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6`;
* the product-measure statement is then assembled by Fubini from the a.e. slice bound
  (`Work.FTS.TransportS.ae_integrableOn_slice`, `integral_integral`,
  `integral_integral_swap`).

All declarations here are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.L6Aux2
import Submission.Work.FTS.StrongPersist.N6Trans.L6Flux.zibp_Ioi_of_integrable
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_atTop
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.L6Flux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## The weighted radial integration by parts with a bounded derivative -/

/-- **Integration by parts on `(0,∞)` with the boundary terms derived and a bound on `φ'`.**

If `φ`, `V` are differentiable on `(0,∞)` with derivatives `φ'`, `V'`, the products `φ V V'`
and `φ' V²` are integrable, `(w V)² ∈ L¹(0,∞)` (`w z = (1+z)²/z²`), `|φ z| ≤ Mf · z · w(z)²`
on `z ≥ 0` and `|φ' z| ≤ 4 Mf w(z)²` on `(0,∞)`, then

`|∫_{(0,∞)} φ V V'| ≤ 2 Mf ∫_{(0,∞)} w² V²`.

The identity `∫ φ V V' = -(1/2)∫ φ' V²` is `zibp_Ioi_of_integrable` (same directory), whose
boundary terms are derived from the `L¹`-hypotheses; the constant `2` is the optimal one
coming from `(1/2)·4 Mf`. -/
theorem zibp_bound {Mf : ℝ} (hMf : 0 ≤ Mf) {φ φ' V V' : ℝ → ℝ}
    (hderivφ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (φ' z) z)
    (hderivV : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt V (V' z) z)
    (hint1 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)))
    (hint2 : MeasureTheory.IntegrableOn (fun z => φ' z * V z ^ 2) (Set.Ioi (0 : ℝ)))
    (hintV : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * V z ^ 2)
      (Set.Ioi (0 : ℝ)))
    (hφbnd : ∀ z ∈ Set.Ici (0 : ℝ), |φ z| ≤ Mf * (z * (Work.Spaces.w z) ^ 2))
    (hφ'bnd : ∀ z ∈ Set.Ioi (0 : ℝ), |φ' z| ≤ 4 * Mf * (Work.Spaces.w z) ^ 2) :
    |∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z|
      ≤ 2 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * V z ^ 2 := by
  have hibp := zibp_Ioi_of_integrable (Mf := Mf) hMf hderivφ hderivV hint1 hint2 hφbnd hintV
  have hnorm : |∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2|
      ≤ 4 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * V z ^ 2 := by
    calc |∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2|
        = ‖∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z in Set.Ioi (0 : ℝ), ‖φ' z * V z ^ 2‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ z in Set.Ioi (0 : ℝ), (4 * Mf) * ((Work.Spaces.w z) ^ 2 * V z ^ 2) := by
          refine MeasureTheory.integral_mono_ae hint2.norm (hintV.const_mul (4 * Mf)) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (V z))]
          calc |φ' z| * V z ^ 2 ≤ (4 * Mf * (Work.Spaces.w z) ^ 2) * V z ^ 2 :=
                mul_le_mul_of_nonneg_right (hφ'bnd z hz) (sq_nonneg _)
            _ = 4 * Mf * ((Work.Spaces.w z) ^ 2 * V z ^ 2) := by ring
      _ = 4 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * V z ^ 2 := by
          rw [MeasureTheory.integral_const_mul]
  have hhalf : |-(1 / 2) * ∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2|
      = (1 / 2) * |∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2| := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
  rw [hibp, hhalf]
  linarith [hnorm]

/-! ## The one-angle flux bound -/

/-- **The flux bound at a single angle.**  For an interior angle `θ`, the radial flux
`∫_z canonW q z θ · f z θ · (z ∂_z V) · V` with `V = D_z^bD_θ^a g` is bounded by
`2 Mf ∫_z canonW q z θ V²`, assuming only `C¹`-slices, the two coefficient bounds and the
integrability of the flux and of the weighted square.  No hypothesis on the behaviour of `V`
at `0⁺` or at `+∞` is needed: both boundary terms of the integration by parts are derived
from `hint1`/`hint2`. -/
theorem fluxSliceLe6 {Mf q θ : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} (hMf : 0 ≤ Mf) (hq0 : 0 < q)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hφcd : ContDiffOn ℝ 1 (fun z => f z θ) (Set.Ioi (0 : ℝ)))
    (hpzcd : ContinuousOn (fun z => Work.Spaces.pz f z θ) (Set.Ioi (0 : ℝ)))
    (hXcd : ContDiffOn ℝ 1 (fun z => Work.Spaces.mixed b a g z θ) (Set.Ioi (0 : ℝ)))
    (hfb : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → |f z θ| ≤ Mf)
    (hDfb : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → |Work.Spaces.Dz f z θ| ≤ Mf)
    (hint1 : MeasureTheory.IntegrableOn (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
        (Set.Ioi (0 : ℝ)))
    (hint2 : MeasureTheory.IntegrableOn (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2) (Set.Ioi (0 : ℝ))) :
    |∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
      ≤ 2 * Mf * ∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2 := by
  -- the angular factor `σ = sin(2θ)^{-q}`, constant along the slice and `≥ 1`
  set σ : ℝ := (Real.sin (2 * θ)) ^ (-q) with hσ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hσ1 : 1 ≤ σ := by
    rw [hσ]
    exact Work.FTS.TransportS.one_le_rpow_neg (le_of_lt hq0) hθ
  have hσ0 : 0 ≤ σ := le_trans zero_le_one hσ1
  have hσne : σ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hσ1)
  have hcw : ∀ z : ℝ, Work.FTS.TransportS.SlotT2.canonW q z θ = (Work.Spaces.w z) ^ 2 * σ := by
    intro z
    rw [Work.FTS.TransportS.SlotT2.canonW, hσ]
  -- the objects of the one-dimensional integration by parts
  set V : ℝ → ℝ := fun z => Work.Spaces.mixed b a g z θ with hV
  set V' : ℝ → ℝ := fun z => Work.Spaces.pz (Work.Spaces.mixed b a g) z θ with hV'
  set φ : ℝ → ℝ := fun z => f z θ * (z * (Work.Spaces.w z) ^ 2) with hφ
  set φ' : ℝ → ℝ := fun z => Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
      + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) with hφ'
  -- the two derivative hypotheses
  have hderivV : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt V (V' z) z := by
    intro z hz
    have hd := ((hXcd.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
    simpa only [hV, hV', Work.Spaces.pz] using hd
  have hderivφ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (φ' z) z := by
    intro z hz
    have hf : HasDerivAt (fun z' => f z' θ) (Work.Spaces.pz f z θ) z := by
      have hd := ((hφcd.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)).hasDerivAt
      simpa only [Work.Spaces.pz] using hd
    have h := hf.mul (Work.FTS.H2.hasDerivAt_zw2 hz)
    simp only [hφ, hφ'] at h ⊢
    convert h using 1
    ring
  -- the pointwise identities relating the flux to `φ V V'`
  have hpt1 : ∀ z : ℝ, φ z * V z * V' z
      = σ⁻¹ * (Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
        * Work.Spaces.mixed b a g z θ) := by
    intro z
    simp only [hφ, hV, hV', hcw z, Work.Spaces.Dz, Work.Spaces.pz]
    field_simp
  have hint1' : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)) :=
    (hint1.const_mul σ⁻¹).congr (Filter.Eventually.of_forall fun z => (hpt1 z).symm)
  have hptV : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 * V z ^ 2
      = σ⁻¹ * (Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2) := by
    intro z
    simp only [hV, hcw z]
    field_simp
  have hintV : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * V z ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (hint2.const_mul σ⁻¹).congr (Filter.Eventually.of_forall fun z => (hptV z).symm)
  have hpt3 : ∀ z : ℝ, Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2
      = σ * ((Work.Spaces.w z) ^ 2 * V z ^ 2) := by
    intro z
    rw [hV, hcw z]
    ring
  have hpt_flux : ∀ z : ℝ, Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ
      = σ * (φ z * V z * V' z) := by
    intro z
    simp only [hφ, hV, hV', hcw z, Work.Spaces.Dz, Work.Spaces.pz]
    ring
  -- the bound on `φ`
  have hφbnd : ∀ z ∈ Set.Ici (0 : ℝ), |φ z| ≤ Mf * (z * (Work.Spaces.w z) ^ 2) := by
    intro z hz
    have hzw : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg hz (sq_nonneg _)
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | h0
    · subst h0
      simp [hφ]
    · rw [hφ, abs_mul, abs_of_nonneg hzw]
      exact mul_le_mul_of_nonneg_right (hfb z h0) hzw
  -- the bound on `φ'`
  have hφ'bnd : ∀ z ∈ Set.Ioi (0 : ℝ), |φ' z| ≤ 4 * Mf * (Work.Spaces.w z) ^ 2 := by
    intro z hz
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hratio : |(z - 3) / (1 + z)| ≤ 3 := Work.FTS.H2.abs_ratio_le_three z hz
    have h2 : |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2|
        ≤ Mf * (Work.Spaces.w z) ^ 2 := by
      rw [show Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
            = (Work.Spaces.pz f z θ * z) * (Work.Spaces.w z) ^ 2 from by ring,
        abs_mul, abs_of_nonneg hw2,
        show |Work.Spaces.pz f z θ * z| = |Work.Spaces.Dz f z θ| from by
          rw [Work.Spaces.Dz, mul_comm]]
      exact mul_le_mul_of_nonneg_right (hDfb z hz) hw2
    have h3 : |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        ≤ 3 * Mf * (Work.Spaces.w z) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw2]
      calc |f z θ| * ((Work.Spaces.w z) ^ 2 * |(z - 3) / (1 + z)|)
          ≤ Mf * ((Work.Spaces.w z) ^ 2 * 3) :=
            mul_le_mul (hfb z hz) (mul_le_mul_of_nonneg_left hratio hw2)
              (mul_nonneg hw2 (abs_nonneg _)) hMf
        _ = 3 * Mf * (Work.Spaces.w z) ^ 2 := by ring
    rw [hφ']
    calc |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
            + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        ≤ |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2|
          + |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| := abs_add_le _ _
      _ ≤ Mf * (Work.Spaces.w z) ^ 2 + 3 * Mf * (Work.Spaces.w z) ^ 2 := add_le_add h2 h3
      _ = 4 * Mf * (Work.Spaces.w z) ^ 2 := by ring
  -- continuity of `φ'` on the slice, hence strong measurability of `φ' V²`
  have hw2cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.TransportS.continuousOn_w_sq_Qd.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun z hz => ⟨hz, hθ⟩)
  have hcontφ' : ContinuousOn φ' (Set.Ioi (0 : ℝ)) := by
    have h1 : ContinuousOn (fun z : ℝ => Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      (hpzcd.mul continuousOn_id).mul hw2cont
    have h2 : ContinuousOn
        (fun z : ℝ => f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
        (Set.Ioi (0 : ℝ)) :=
      (hφcd.continuousOn).mul (hw2cont.mul
        (ContinuousOn.div (continuousOn_id.sub continuousOn_const)
          (continuousOn_const.add continuousOn_id) (fun z hz => by
            have hz0 : (0 : ℝ) < z := hz
            linarith)))
    simp only [hφ']
    exact h1.add h2
  have hint2' : MeasureTheory.IntegrableOn (fun z => φ' z * V z ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.mono' (hintV.const_mul (4 * Mf))
      ((hcontφ'.mul ((hXcd.continuousOn).pow 2)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (V z))]
    calc |φ' z| * V z ^ 2 ≤ (4 * Mf * (Work.Spaces.w z) ^ 2) * V z ^ 2 :=
          mul_le_mul_of_nonneg_right (hφ'bnd z hz) (sq_nonneg _)
      _ = 4 * Mf * ((Work.Spaces.w z) ^ 2 * V z ^ 2) := by ring
  -- the integration by parts, and the multiplication by the constant `σ`
  have hibp := zibp_bound (Mf := Mf) hMf hderivφ hderivV hint1' hint2' hintV hφbnd hφ'bnd
  have hL : (∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
      = σ * ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z := by
    calc (∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
        = ∫ z in Set.Ioi (0 : ℝ), σ * (φ z * V z * V' z) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt_flux)
      _ = σ * ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z :=
          MeasureTheory.integral_const_mul σ _
  have hR : (∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2)
      = σ * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * V z ^ 2 := by
    calc (∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.SlotT2.canonW q z θ
          * (Work.Spaces.mixed b a g z θ) ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), σ * ((Work.Spaces.w z) ^ 2 * V z ^ 2) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt3)
      _ = σ * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * V z ^ 2 :=
          MeasureTheory.integral_const_mul σ _
  rw [hL, hR]
  calc |σ * ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z|
      = σ * |∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z| := by
        rw [abs_mul, abs_of_nonneg hσ0]
    _ ≤ σ * (2 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * V z ^ 2) :=
        mul_le_mul_of_nonneg_left hibp hσ0
    _ = 2 * Mf * (σ * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * V z ^ 2) := by ring

/-! ## The product-measure bound -/

/-- **The level-six flux term with a bounded coefficient.** -/
theorem flux_prod_le {α Mf q : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hα : 0 < α) (hMf : 0 ≤ Mf) (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b = 6)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hm6 : Work.Spaces.HkMem α 6 g) (hm7 : Work.Spaces.HkMem α 7 g)
    (hfb : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ Mf)
    (hDfb : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) :
    |∫ p, Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ 2 * Mf * Work.Spaces.HkSq α 6 g := by
  have hab6 : a + b ≤ 6 := by omega
  have hab7 : a + (b + 1) ≤ 7 := by omega
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iz with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hν
  set F : ℝ × ℝ → ℝ := fun p => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * f p.1 p.2
      * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2
    with hF
  set A : ℝ × ℝ → ℝ := fun p => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
      * (Work.Spaces.mixed b a g p.1 p.2) ^ 2 with hA
  -- the level-six slot energy (proved upstream): the weighted square is product-integrable,
  -- its `θ`-marginal is integrable, and the `θ`-outer integral is at most `HkSq α 6 g`
  obtain ⟨hAint, hmA, hAval⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6 α q g a b (le_of_lt hq0) hqγ hqη hab6 hsg hm6
  -- the pointwise domination of the flux integrand
  have hFle : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F (z, θ)| ≤ (Mf / 2) * (Work.Spaces.HkIntegrand α 7 g z θ
        + Work.Spaces.HkIntegrand α 6 g z θ) := by
    intro z θ hz hθ hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
    have hnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
      Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
    have h6 : Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      Work.FTS.StrongPersist.N6Trans.canonW_slot_le_HkGen (g := g) (q := q) hq0 hqγ
        (k := 6) (j := b) (i := a) hqη hab6 hθI
    have h7 : Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 g z θ :=
      Work.FTS.StrongPersist.N6Trans.canonW_slot_le_HkGen (g := g) (q := q) hq0 hqγ
        (k := 7) (j := b + 1) (i := a) hqη hab7 hθI
    have habs : |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        ≤ ((Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ) ^ 2
            + (Work.Spaces.mixed b a g z θ) ^ 2) / 2 :=
      Work.FTS.StrongPersist.N6Trans.abs_mul_le_half_sq_add6 _ _
    have hstep : |Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        ≤ (Mf / 2) * ((Work.FTS.TransportS.SlotT2.canonW q z θ
              * (Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ) ^ 2)
            + Work.FTS.TransportS.SlotT2.canonW q z θ
              * (Work.Spaces.mixed b a g z θ) ^ 2) := by
      have hprod : |Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
          = (Work.FTS.TransportS.SlotT2.canonW q z θ * |f z θ|)
            * |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
              * Work.Spaces.mixed b a g z θ| := by
        rw [show Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
                * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ
              = (Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ)
                * (Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
                  * Work.Spaces.mixed b a g z θ) from by ring,
          abs_mul, abs_mul, abs_of_nonneg hnn]
      rw [hprod]
      calc (Work.FTS.TransportS.SlotT2.canonW q z θ * |f z θ|)
            * |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
              * Work.Spaces.mixed b a g z θ|
          ≤ (Work.FTS.TransportS.SlotT2.canonW q z θ * Mf)
            * (((Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ) ^ 2
                + (Work.Spaces.mixed b a g z θ) ^ 2) / 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hfb z θ hz hθ hθ2) hnn) habs
              (abs_nonneg _) (mul_nonneg hnn hMf)
        _ = (Mf / 2) * ((Work.FTS.TransportS.SlotT2.canonW q z θ
              * (Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ) ^ 2)
            + Work.FTS.TransportS.SlotT2.canonW q z θ
              * (Work.Spaces.mixed b a g z θ) ^ 2) := by ring
    calc |F (z, θ)|
        = |Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
            * Work.Spaces.mixed b a g z θ| := by rw [hF]
      _ ≤ (Mf / 2) * (Work.Spaces.HkIntegrand α 7 g z θ
            + Work.Spaces.HkIntegrand α 6 g z θ) :=
          hstep.trans (mul_le_mul_of_nonneg_left (add_le_add h7 h6) (by linarith))
  -- product integrability of the flux integrand, by domination
  have hFint : MeasureTheory.Integrable F (μ.prod ν) := by
    have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Mf / 2)
        * (Work.Spaces.HkIntegrand α 7 g p.1 p.2
          + Work.Spaces.HkIntegrand α 6 g p.1 p.2)) (μ.prod ν) :=
      (((Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hsg hm7).1.add
        (Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hsg hm6).1).const_mul
          (Mf / 2))
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          (hsf.continuousOn)).mul
        (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hsg (b + 1) a)).mul
          (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hsg b a)
    refine MeasureTheory.Integrable.mono' hmaj (Work.Spaces.aesm_of_continuousOn_Qd _ hcont) ?_
    filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
      |F p| ≤ (Mf / 2) * (Work.Spaces.HkIntegrand α 7 g p.1 p.2
        + Work.Spaces.HkIntegrand α 6 g p.1 p.2))
      (fun z θ hz hθ hθ' => hFle z θ hz hθ hθ')] with p hp
    rwa [Real.norm_eq_abs]
  -- the a.e. radial slices
  have hFae : ∀ᵐ θ ∂ν, MeasureTheory.IntegrableOn (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ
      * f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
      * Work.Spaces.mixed b a g z θ) (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice (H := F) hFint
    filter_upwards [h] with θ hθ
    exact (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hθ
  have hAae : ∀ᵐ θ ∂ν, MeasureTheory.IntegrableOn (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ
      * (Work.Spaces.mixed b a g z θ) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice (H := A) hAint
    filter_upwards [h] with θ hθ
    exact (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hθ
  -- the a.e. slice bound, via the one-angle flux lemma
  have hslice : ∀ᵐ θ ∂ν,
      ‖∫ z, F (z, θ) ∂μ‖ ≤ 2 * Mf * (∫ z, A (z, θ) ∂μ) := by
    filter_upwards [Work.FTS.TransportS.ae_mem_Ioo_Iθ, hFae, hAae] with θ hθ hI1 hI2
    have hφcd : ContDiffOn ℝ 1 (fun z => f z θ) (Set.Ioi (0 : ℝ)) :=
      (hsf.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
    have hpzcd : ContinuousOn (fun z => Work.Spaces.pz f z θ) (Set.Ioi (0 : ℝ)) :=
      ((hsf.pz).continuousOn).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun z hz => ⟨hz, hθ⟩)
    have hXcd : ContDiffOn ℝ 1 (fun z => Work.Spaces.mixed b a g z θ) (Set.Ioi (0 : ℝ)) :=
      ((hsg.mixed b a).curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
    have hkey := fluxSliceLe6 (Mf := Mf) (q := q) (θ := θ) (f := f) (g := g) (a := a) (b := b)
      hMf hq0 hθ hφcd hpzcd hXcd (fun z hz => hfb z θ hz hθ.1 hθ.2)
      (fun z hz => hDfb z θ hz hθ.1 hθ.2) hI1 hI2
    rw [hμ, Work.FTS.TransportS.T3BadAux.restrict_Iz_eq_Ioi, Real.norm_eq_abs]
    simpa only [hF, hA] using hkey
  -- Fubini, and the two monotonicity steps
  have hL : (∫ p, F p ∂(μ.prod ν)) = ∫ θ, ∫ z, F (z, θ) ∂μ ∂ν :=
    (MeasureTheory.integral_integral (μ := μ) (ν := ν) (f := fun z θ => F (z, θ)) hFint).symm.trans
      (MeasureTheory.integral_integral_swap (μ := μ) (ν := ν) (f := fun z θ => F (z, θ)) hFint)
  have hmF : MeasureTheory.Integrable (fun θ => ∫ z, F (z, θ) ∂μ) ν :=
    hFint.integral_prod_right
  rw [hL, ← Real.norm_eq_abs]
  calc ‖∫ θ, ∫ z, F (z, θ) ∂μ ∂ν‖
      ≤ ∫ θ, ‖∫ z, F (z, θ) ∂μ‖ ∂ν := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ, 2 * Mf * (∫ z, A (z, θ) ∂μ) ∂ν :=
        MeasureTheory.integral_mono_ae hmF.norm (hmA.const_mul (2 * Mf)) hslice
    _ = 2 * Mf * ∫ θ, (∫ z, A (z, θ) ∂μ) ∂ν :=
        MeasureTheory.integral_const_mul (2 * Mf) _
    _ ≤ 2 * Mf * Work.Spaces.HkSq α 6 g :=
        mul_le_mul_of_nonneg_left hAval (by linarith)

end Work.FTS.StrongPersist.N6Trans.L6Flux
