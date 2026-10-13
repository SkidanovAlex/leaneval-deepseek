import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.fluxSix

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.Spaces

/-! ## Two elementary `|·|`-manipulations

These are the bookkeeping steps of the pointwise Cauchy–Schwarz (AM–GM) bound
`|ρ f X Y| ≤ |f| · (canonW q |X| |Y|) ≤ (M/2)(canonW q X² + canonW q Y²)`, where `ρ ≤ canonW q`
is the leaf weight domination and `|f| ≤ M`.  They are stated separately so that the
reassociation of the products never has to be guessed by `ring`. -/

/-- `|s u v w| ≤ |u| (t |v| |w|)` whenever `0 ≤ s ≤ t`. -/
theorem abs_four_mul_le_of_le {s t u v w : ℝ} (h0 : 0 ≤ s) (h : s ≤ t) :
    |s * u * v * w| ≤ |u| * (t * |v| * |w|) := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h0]
  have hnn : 0 ≤ |u| * |v| * |w| := by positivity
  have hkey : s * (|u| * |v| * |w|) ≤ t * (|u| * |v| * |w|) :=
    mul_le_mul_of_nonneg_right h hnn
  calc ((s * |u|) * |v|) * |w| = s * (|u| * |v| * |w|) := by ring
    _ ≤ t * (|u| * |v| * |w|) := hkey
    _ = |u| * (t * |v| * |w|) := by ring

/-- `|u (c v w)| = |u| (c |v| |w|)` for `c ≥ 0`. -/
theorem abs_mul_canonW_three {c u v w : ℝ} (hc : 0 ≤ c) :
    |u * (c * v * w)| = |u| * (c * |v| * |w|) := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc]

/-- **The family `(a₁,b₁) = (0,0)` of the level-six transport expansion.

The coefficient `f` carries *no* derivative, so the pairing
`∫∫ ρ · f · D_z(D_z^bD_θ^a g) · (D_z^bD_θ^a g)` with `a + b ≤ 5` involves only two `g`-slots of
order `≤ 6`; it is therefore a purely pointwise (Cauchy–Schwarz) estimate, with no radial
integration by parts and no `HkMem α 7 g`.  Concretely, on the open quadrant,

* `ρ ≤ canonW (qOf α a)` (`IsLeafW.le_canonW`), where `qOf α a = η` for `a = 0` and `γ` for
  `a ≥ 1` — the weight class of the slot;
* `|f| ≤ |f|_{𝒲^{6,∞}}` (`WlInf_z_bound` at `k = 0`);
* the two slots `D_z^{b+1}D_θ^a g` and `D_z^bD_θ^a g` have order `≤ 6` and the matching weight
  class, so each is dominated by `HkIntegrand α 6 g`
  (`canonW_mul_z_le_of_le` resp. `canonW_mul_mixed_le_of_le`).

Hence `|integrand| ≤ |f|_{𝒲^{6,∞}} · HkIntegrand α 6 g` a.e., and the claim follows from the
integrability of `HkIntegrand α 6 g` on the product (`HkProdOpen`), the constant being `2`
(only `1` is needed, the slack is harmless). -/
theorem fluxFamSix : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f g : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.DecayAll 6 g →
    a + b ≤ 5 → Work.FTS.TransportS.IsLeafW α a ρ →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) ∧
        |∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
          ≤ C * Work.Spaces.WlInf α 6 f * Work.Spaces.HkSq α 6 g := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα f g a b ρ hsf hfm hsg hmg hdec hab hρ
  obtain ⟨hαpos, hαle⟩ := hα
  set Mf : ℝ := WlInf α 6 f with hMfdef
  have hMfnn : 0 ≤ Mf := by
    rw [hMfdef]; exact WlInf_nonneg α 6 f hfm
  set F : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
      * Dz (mixed b a g) p.1 p.2 * mixed b a g p.1 p.2 with hFdef
  have hdz : ∀ z θ : ℝ, Dz (mixed b a g) z θ = mixed (b + 1) a g z θ := fun z θ => rfl
  -- ## The two pointwise slot dominations at order `6`
  have hslotX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ
        * (mixed (b + 1) a g z θ) ^ 2 ≤ HkIntegrand α 6 g z θ := by
    intro z θ _ hθ0 hθ2
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [Work.FTS.TransportS.T3SlotAux.qOf_zero]
      simpa only [mixed_zero_right] using
        (Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (g := g)
          (q := eta) 6 le_rfl hθ0 hθ2 (j := b + 1) (by omega))
    · rw [Work.FTS.TransportS.T3SlotAux.qOf_of_ne (by omega : a ≠ 0)]
      exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α) (g := g)
        (q := gam α) 6 le_rfl hθ0 hθ2 (j := b + 1) (i := a) (by omega) (by omega)
  have hslotY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ
        * (mixed b a g z θ) ^ 2 ≤ HkIntegrand α 6 g z θ := by
    intro z θ _ hθ0 hθ2
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [Work.FTS.TransportS.T3SlotAux.qOf_zero]
      simpa only [mixed_zero_right] using
        (Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (g := g)
          (q := eta) 6 le_rfl hθ0 hθ2 (j := b) (by omega))
    · rw [Work.FTS.TransportS.T3SlotAux.qOf_of_ne (by omega : a ≠ 0)]
      exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α) (g := g)
        (q := gam α) 6 le_rfl hθ0 hθ2 (j := b) (i := a) (by omega) (by omega)
  -- ## The pointwise Cauchy–Schwarz bound on the open quadrant
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F (z, θ)| ≤ Mf * HkIntegrand α 6 g z θ := by
    intro z θ hz hθ0 hθ2
    have hθI : θ ∈ Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hcw : 0 ≤ Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ :=
      Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
    have hρnn : 0 ≤ ρ z θ := Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hρ z hθI
    have hρle : ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW
        (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ :=
      Work.FTS.TransportS.T3SlotAux.IsLeafW.le_canonW hαpos hρ hz ⟨hθ0, hθ2⟩
    have hf : |f z θ| ≤ Mf := by
      rw [hMfdef]
      simpa using WlInf_z_bound α 6 f hfm 0 (by norm_num) z θ (le_of_lt hz) hθI
    have hX := hslotX z θ hz hθ0 hθ2
    have hY := hslotY z θ hz hθ0 hθ2
    have hFA : F (z, θ) = ρ z θ * f z θ * mixed (b + 1) a g z θ * mixed b a g z θ := by
      show ρ z θ * f z θ * Dz (mixed b a g) z θ * mixed b a g z θ
        = ρ z θ * f z θ * mixed (b + 1) a g z θ * mixed b a g z θ
      rw [hdz z θ]
    rw [hFA]
    calc |ρ z θ * f z θ * mixed (b + 1) a g z θ * mixed b a g z θ|
        ≤ |f z θ| * (Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ
            * |mixed (b + 1) a g z θ| * |mixed b a g z θ|) :=
          abs_four_mul_le_of_le hρnn hρle
      _ = |f z θ * (Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ
            * mixed (b + 1) a g z θ * mixed b a g z θ)| :=
          abs_mul_canonW_three (c := Work.FTS.TransportS.SlotT2.canonW
            (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ) (u := f z θ)
            (v := mixed (b + 1) a g z θ) (w := mixed b a g z θ) hcw |>.symm
      _ ≤ (Mf / 2) * (Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ
              * (mixed (b + 1) a g z θ) ^ 2
            + Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ
              * (mixed b a g z θ) ^ 2) :=
          Work.FTS.StrongPersist.N6Trans.SixAux.abs_mul_canonW_mul_le hcw hMfnn hf
      _ ≤ (Mf / 2) * (HkIntegrand α 6 g z θ + HkIntegrand α 6 g z θ) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = Mf * HkIntegrand α 6 g z θ := by ring
  -- ## Continuity on the open quadrant (for a.e. strong measurability)
  have hρcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rcases hρ with rfl | rfl | ⟨_, rfl⟩
    · change ContinuousOn (fun p : ℝ × ℝ =>
        Work.FTS.TransportS.SlotT2.canonW eta p.1 p.2) _
      exact Work.FTS.TransportS.SlotT2.continuousOn_canonW eta
    · refine (Work.FTS.TransportS.SlotT2.continuousOn_canonW 0).congr ?_
      intro p _
      simp [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW]
    · change ContinuousOn (fun p : ℝ × ℝ =>
        Work.FTS.TransportS.SlotT2.canonW (gam α) p.1 p.2) _
      exact Work.FTS.TransportS.SlotT2.continuousOn_canonW (gam α)
  have hcontF : ContinuousOn F (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hXc : ContinuousOn (fun p : ℝ × ℝ => Dz (mixed b a g) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := ((hsg.mixed b a).Dz).continuousOn
    have hYc : ContinuousOn (fun p : ℝ × ℝ => mixed b a g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hsg.mixed b a).continuousOn
    exact (((hρcont.mul hsf.continuousOn).mul hXc).mul hYc).congr
      (fun p _ => by rw [hFdef]; rfl)
  -- ## Integrability of `HkIntegrand α 6 g` and of the integrand
  have hHint := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsg hmg
  have haesmF : AEStronglyMeasurable F
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    aesm_of_continuousOn_Qd F hcontF
  have hdom : ∀ᵐ p ∂((volume.restrict Iz).prod (volume.restrict Iθ)),
      ‖F p‖ ≤ Mf * HkIntegrand α 6 g p.1 p.2 := by
    refine (Work.FTS.TransportS.ae_of_forall_Qd
      (fun z θ hz hθ0 hθ2 => ?_))
    rw [Real.norm_eq_abs]
    exact hpt z θ hz hθ0 hθ2
  have hdomint : Integrable (fun p : ℝ × ℝ => Mf * HkIntegrand α 6 g p.1 p.2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) := hHint.1.const_mul Mf
  have hFint : Integrable F ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    hdomint.mono' haesmF hdom
  -- ## The estimate
  have hFabsint : Integrable (fun p : ℝ × ℝ => |F p|)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) := hFint.abs
  have hmono : (∫ p, |F p| ∂((volume.restrict Iz).prod (volume.restrict Iθ)))
      ≤ ∫ p, Mf * HkIntegrand α 6 g p.1 p.2
          ∂((volume.restrict Iz).prod (volume.restrict Iθ)) := by
    refine integral_mono_ae hFabsint hdomint ?_
    filter_upwards [hdom] with p hp
    simpa only [Real.norm_eq_abs] using hp
  have hval : (∫ p, Mf * HkIntegrand α 6 g p.1 p.2
        ∂((volume.restrict Iz).prod (volume.restrict Iθ))) = Mf * HkSq α 6 g := by
    rw [integral_const_mul, hHint.2]
  constructor
  · rw [MeasureTheory.IntegrableOn, ← Work.FTS.TransportS.prod_restrict_eq]
    exact hFint
  · calc |∫ p, F p ∂((volume.restrict Iz).prod (volume.restrict Iθ))|
        ≤ ∫ p, |F p| ∂((volume.restrict Iz).prod (volume.restrict Iθ)) :=
          abs_integral_le_integral_abs
      _ ≤ Mf * HkSq α 6 g := hmono.trans (le_of_eq hval)
      _ = 1 * WlInf α 6 f * HkSq α 6 g := by rw [hMfdef]; ring

end

end Work.FTS.StrongPersist.N6Trans.SixRoute
