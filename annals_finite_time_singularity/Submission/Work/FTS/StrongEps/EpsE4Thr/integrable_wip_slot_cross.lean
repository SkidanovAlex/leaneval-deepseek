/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the *crossed* `wip`-slot pairing

`Work.FTS.StrongEps.EpsE4Thr.integrable_wip_slot_cross` is the crossed companion of
`integrable_wip_slot`: for two functions `f`, `h` which are smooth on the open quadrant and
honestly in `ℋ⁴`, and for a mixed slot `D_z^j D_θ^i` of order `j + i ≤ 4`, the pairing

  `∫∫ D_z^j D_θ^i f · D_z^j D_θ^i h · ρ`

is finite for each of the three weights `ρ = w²σ^{-η}`, `ρ = w²` and (when `i ≥ 1`)
`ρ = w²σ^{-γ}` of `StrongPersist.H1IP`, where `σ = sin(2θ)`, `w(z) = (1+z)²/z²`.

The route is the standard one for this corner of the development:

* `SmoothOpen` makes every slot **a.e. strongly measurable** for the product measure
  `(volume.restrict I_z).prod (volume.restrict I_θ)` (continuity on the open quadrant, which is
  co-null) — `SlotWt.aesm_mixed_pair_weight`;
* `HkMem α 4` makes the `ℋ⁴`-integrand **product-integrable**
  (`N6Trans.Hon.integrable_HkIntegrand_prod_open`), so the half-sum of the two integrands of `f`
  and `h` is an integrable majorant;
* each *single* weighted square is dominated by the `ℋ⁴`-integrand of the corresponding
  function: `(w²σ^c)·(D_z^jD_θ^ig)² ≤ HkIntegrand α 4 g` for `c ≥ -η` — this is the pair of
  `SlotWt.dzSlot_weight_le_HkIntegrand4` (`i = 0`, slot `D_z^j`) and
  `SlotWt.mixedSlot_weight_le_HkIntegrand4` (`i ≥ 1`, slot `D_z^jD_θ^i`, `c ≥ -γ`), combined by
  `c ≥ -η ⟹ c ≥ -γ`;
* the pointwise AM–GM `2|AB| ≤ A² + B²` then gives
  `|A_f A_h ρ| ≤ ((ρ A_f²) + (ρ A_h²))/2 ≤ (HkIntegrand α 4 f + HkIntegrand α 4 h)/2`
  on the open quadrant, and `Integrable.mono'` finishes.

Every declaration below is fully proved; the three ingredients are established in
`Submission/Work/FTS/StrongEps/EpsE4Thr/SlotWt/`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.EnergyStep
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.dzSlot_weight_le_HkIntegrand4
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The one-parameter family of weights `ρ_c = w²σ^c` (`σ = sin 2θ`) to which the three weights
of the statement belong: `ρ_{-η} = StrongPersist.rhoEta`, `ρ_0 = StrongPersist.rhoW`,
`ρ_{-γ} = StrongPersist.rhoGam α`. -/
def crossWt (c : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c

/-- **The assembly of the crossed slot pairing.**  If each of the two weighted squares
`ρ_c·(D_z^jD_θ^if)²` and `ρ_c·(D_z^jD_θ^ih)²` is pointwise dominated by the corresponding
`ℋ⁴`-integrand, then the crossed pairing against `ρ_c` is integrable.  The proof is the AM–GM
inequality on the open quadrant (co-null for the product measure), plus the product-integrability
of the two `ℋ⁴`-integrands. -/
theorem integrable_mixed_pairing {α c : ℝ} {f h : ℝ → ℝ → ℝ} {j i : ℕ}
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) (hsmh : Work.FTS.EllipticEst.SmoothOpen h)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemh : Work.Spaces.HkMem α 4 h)
    (hbF : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      crossWt c z θ * (Work.Spaces.mixed j i f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ)
    (hbH : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      crossWt c z θ * (Work.Spaces.mixed j i h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 h z θ)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i h p.1 p.2
        * crossWt c p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i h p.1 p.2
        * crossWt c p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hintf := (Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open
    (k := 4) hsmf hmemf).1
  have hinth := (Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open
    (k := 4) hsmh hmemh).1
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.HkIntegrand α 4 f p.1 p.2
        + Work.Spaces.HkIntegrand α 4 h p.1 p.2) / 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hintf.add hinth).div_const 2
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  apply Work.FTS.TransportS.ae_of_forall_Qd
  intro z θ hz hθ hθ2
  rw [Real.norm_eq_abs]
  have hσpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hρnn : 0 ≤ crossWt c z θ :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hσpos) c)
  have hA := hbF z θ hz hθ hθ2
  have hB := hbH z θ hz hθ hθ2
  have h1 : |Work.Spaces.mixed j i f z θ * Work.Spaces.mixed j i h z θ * crossWt c z θ|
      = |Work.Spaces.mixed j i f z θ| * |Work.Spaces.mixed j i h z θ|
          * crossWt c z θ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hρnn]
  have h2 : |Work.Spaces.mixed j i f z θ| * |Work.Spaces.mixed j i h z θ|
      ≤ ((Work.Spaces.mixed j i f z θ) ^ 2 + (Work.Spaces.mixed j i h z θ) ^ 2) / 2 := by
    rw [← abs_mul]
    exact Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add _ _
  have h3 := mul_le_mul_of_nonneg_right h2 hρnn
  rw [h1]
  calc |Work.Spaces.mixed j i f z θ| * |Work.Spaces.mixed j i h z θ| * crossWt c z θ
      ≤ ((Work.Spaces.mixed j i f z θ) ^ 2 + (Work.Spaces.mixed j i h z θ) ^ 2) / 2
          * crossWt c z θ := h3
    _ = (crossWt c z θ * (Work.Spaces.mixed j i f z θ) ^ 2
          + crossWt c z θ * (Work.Spaces.mixed j i h z θ) ^ 2) / 2 := by ring
    _ ≤ (Work.Spaces.HkIntegrand α 4 f z θ + Work.Spaces.HkIntegrand α 4 h z θ) / 2 := by
        linarith

theorem integrable_wip_slot_cross {α : ℝ} {f h : Work.FTS.Galerkin.Fn} {j i : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hji : j + i ≤ 4)
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) (hsmh : Work.FTS.EllipticEst.SmoothOpen h)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemh : Work.Spaces.HkMem α 4 h) :
    (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i h p.1 p.2
          * Work.FTS.StrongPersist.rhoEta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i h p.1 p.2
          * Work.FTS.StrongPersist.rhoW p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (1 ≤ i → MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i h p.1 p.2
          * Work.FTS.StrongPersist.rhoGam α p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  -- `η ≤ γ`, so the `D_z`-slot bound (`c ≥ -η`) and the mixed-slot bound (`c ≥ -γ`) are both
  -- available as soon as `c ≥ -η`.
  have heta_gam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    have h1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
    have h2 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
    linarith
  -- the pointwise domination of one weighted square by the `ℋ⁴`-integrand
  have hbound : ∀ (g : ℝ → ℝ → ℝ) (c : ℝ), -(Work.Spaces.eta) ≤ c → ∀ z θ,
      0 < z → 0 < θ → θ < π / 2 →
      crossWt c z θ * (Work.Spaces.mixed j i g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    intro g c hc z θ hz hθ hθ2
    by_cases hi : i = 0
    · subst hi
      have h4 : j ≤ 4 := by omega
      simpa only [Work.Spaces.mixed_zero_right, crossWt] using
        Work.FTS.StrongEps.EpsE4Thr.SlotWt.dzSlot_weight_le_HkIntegrand4
          (α := α) (c := c) (g := g) (m := j) hc h4 ⟨hθ, hθ2⟩
    · have hi1 : 1 ≤ i := by omega
      have hcg : -(Work.Spaces.gam α) ≤ c := by linarith [heta_gam]
      exact Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
        (α := α) (c := c) (g := g) (a := i) (b := j) hα hcg hi1 (by omega) ⟨hθ, hθ2⟩
  refine ⟨?_, ?_, ?_⟩
  · have h := integrable_mixed_pairing (α := α) (c := -(Work.Spaces.eta)) (f := f) (h := h)
      (j := j) (i := i) hsmf hsmh hmemf hmemh
      (hbound f (-(Work.Spaces.eta)) le_rfl)
      (hbound h (-(Work.Spaces.eta)) le_rfl)
      (Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight
        (c := -(Work.Spaces.eta)) hsmf hsmh)
    simpa only [Work.FTS.StrongPersist.rhoEta, crossWt] using h
  · have h := integrable_mixed_pairing (α := α) (c := 0) (f := f) (h := h)
      (j := j) (i := i) hsmf hsmh hmemf hmemh
      (hbound f 0 (by linarith [Work.Spaces.eta_pos]))
      (hbound h 0 (by linarith [Work.Spaces.eta_pos]))
      (Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight (c := 0) hsmf hsmh)
    simpa only [Work.FTS.StrongPersist.rhoW, crossWt, Real.rpow_zero, mul_one] using h
  · intro hi1
    have h := integrable_mixed_pairing (α := α) (c := -(Work.Spaces.gam α)) (f := f) (h := h)
      (j := j) (i := i) hsmf hsmh hmemf hmemh
      (fun z θ hz hθ hθ2 =>
        Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
          (α := α) (c := -(Work.Spaces.gam α)) (g := f) (a := i) (b := j)
          hα le_rfl hi1 (by omega) ⟨hθ, hθ2⟩)
      (fun z θ hz hθ hθ2 =>
        Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
          (α := α) (c := -(Work.Spaces.gam α)) (g := h) (a := i) (b := j)
          hα le_rfl hi1 (by omega) ⟨hθ, hθ2⟩)
      (Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight
        (c := -(Work.Spaces.gam α)) hsmf hsmh)
    simpa only [Work.FTS.StrongPersist.rhoGam, crossWt] using h

end Work.FTS.StrongEps.EpsE4Thr
