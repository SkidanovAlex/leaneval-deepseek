/-
# Integrability of the `wip`-slots in the strong weights `ρ_η`, `ρ_w`, `ρ_γ`

The energy identity of `Work.FTS.StrongPersist` (`hasDerivAt_wip_family`,
`EnergyStep`) consumes, at every slot `(j,i)` of the recursion, the integrability of
`D_z^j D_θ^i f · D_z^j D_θ^i f · ρ` for the three weights

* `ρ_η = w²·sin(2θ)^{-η}`, `ρ_w = w²`, `ρ_γ = w²·sin(2θ)^{-γ}`

with respect to the product of the restricted Lebesgue measures on `Iz = [0,∞)` and
`Iθ = [0,π/2]`.  This file produces those three facts from the two standard hypotheses
(`f` smooth on the open quadrant, `D_z^j D_θ^i f ∈ ℋ⁴`).

The proof is a single `Integrable.mono'` per weight:

* the majorant `HkIntegrand α 4 f` is product-integrable
  (`HkIntegrand_integrable_prod_fts`, from `HkMem` by the iterated-integral criterion
  `Work.Spaces.integrable_prod_of_iterated`);
* the domination `slot² · ρ ≤ HkIntegrand α 4 f` holds at every point of the open
  quadrant, and the product measure is carried by the open quadrant
  (`ae_mem_openQuadrant_fts`); it is supplied by the already proved general slot bounds
  `SlotWt.dzSlot_weight_le_HkIntegrand4` (for `i = 0`) and
  `SlotWt.mixedSlot_weight_le_HkIntegrand4` (for `i ≥ 1`), with the exponents
  `c = -η` resp. `c = -γ` resp. `c = 0`;
* a.e. strong measurability comes from `SlotWt.aesm_mixed_pair_weight`
  (continuity on the open quadrant plus the null boundary).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.EnergyStep
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.dzSlot_weight_le_HkIntegrand4
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4

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

/-! ## The open quadrant carries the product measure -/

/-- The product `(volume.restrict Iz).prod (volume.restrict Iθ)` of the two restricted
Lebesgue measures is carried by the open quadrant `(0,∞) × (0,π/2)`: the complement
inside `[0,∞) × [0,π/2]` is the union of the three null segments `{0} × Iθ`,
`Iz × {0}` and `Iz × {π/2}`. -/
theorem ae_mem_openQuadrant_fts :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hz : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm
  have hθ : (Work.Spaces.Iθ : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := π / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet

/-! ## Product-integrability of the `ℋ^k`-integrand -/

/-- The `ℋ^k`-integrand of a function which is `C^∞` on the open quadrant and in `ℋ^k` is
integrable for the product measure.  This is the iterated-integral criterion
`Work.Spaces.integrable_prod_of_iterated` applied to the two conjuncts of `HkMem`, the
a.e. strong measurability being continuity on the open quadrant
(`SmoothOpen.continuousOn_HkIntegrand`) plus the null boundary. -/
theorem HkIntegrand_integrable_prod_fts {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α k f z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.continuousOn_HkIntegrand α k)) ?_ hmem.2).1
  rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
  exact Eventually.of_forall fun z hz => hmem.1 z hz

/-! ## Pointwise (a.e.) domination of the three slots -/

/-- The `η`-weighted slot `(D_z^j D_θ^i f)² · w²·sin(2θ)^{-η}` is dominated, a.e. for the
product measure, by `HkIntegrand α 4 f`.  For `i = 0` this is the pure `D_z`-slot with the
exponent `c = -η` of `SlotWt.dzSlot_weight_le_HkIntegrand4`; for `i ≥ 1` it is the mixed
slot with the same exponent `c = -η`, which is legitimate because `η ≤ γ(α)`. -/
theorem ae_slot_sq_mul_rhoEta_le_HkIntegrand {α : ℝ} {j i : ℕ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hji : j + i ≤ 4) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ‖Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i f p.1 p.2
          * Work.FTS.StrongPersist.rhoEta p.1 p.2‖
        ≤ Work.Spaces.HkIntegrand α 4 f p.1 p.2 := by
  filter_upwards [ae_mem_openQuadrant_fts] with p hp
  obtain ⟨hz, hθ0, hθ1⟩ := hp
  have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  have hsin : 0 < Real.sin (2 * p.2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hρ : 0 ≤ Work.FTS.StrongPersist.rhoEta p.1 p.2 := by
    rw [Work.FTS.StrongPersist.rhoEta]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_self_nonneg _) hρ)]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    rw [Work.Spaces.mixed_zero_right, Work.FTS.StrongPersist.rhoEta]
    have hD := Work.FTS.StrongEps.EpsE4Thr.SlotWt.dzSlot_weight_le_HkIntegrand4
      (α := α) (c := -(Work.Spaces.eta)) (g := f) (m := j) (z := p.1)
      le_rfl (by omega) hθ
    have hrw : Work.Spaces.DzIter j f p.1 p.2 * Work.Spaces.DzIter j f p.1 p.2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.eta)))
        = Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter j f p.1 p.2) ^ 2 := by ring
    rw [hrw]
    exact hD
  · have hcg : -(Work.Spaces.gam α) ≤ -(Work.Spaces.eta) := by
      simp only [Work.Spaces.gam, Work.Spaces.eta]
      linarith
    have hM := Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
      (α := α) (c := -(Work.Spaces.eta)) (g := f) (a := i) (b := j) (z := p.1)
      hα hcg (by omega) (by omega) hθ
    rw [Work.FTS.StrongPersist.rhoEta]
    have hrw : Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i f p.1 p.2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.eta)))
        = Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 := by ring
    rw [hrw]
    exact hM

/-- The unweighted slot `(D_z^j D_θ^i f)² · w²` is dominated, a.e. for the product measure,
by `HkIntegrand α 4 f`.  This is the exponent `c = 0` of the two slot bounds
(`c = 0 ≥ -η` and `c = 0 ≥ -γ(α)`). -/
theorem ae_slot_sq_mul_rhoW_le_HkIntegrand {α : ℝ} {j i : ℕ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hji : j + i ≤ 4) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ‖Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i f p.1 p.2
          * Work.FTS.StrongPersist.rhoW p.1 p.2‖
        ≤ Work.Spaces.HkIntegrand α 4 f p.1 p.2 := by
  filter_upwards [ae_mem_openQuadrant_fts] with p hp
  obtain ⟨hz, hθ0, hθ1⟩ := hp
  have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  have hρ : 0 ≤ Work.FTS.StrongPersist.rhoW p.1 p.2 := by
    rw [Work.FTS.StrongPersist.rhoW]
    exact sq_nonneg _
  rw [Real.norm_of_nonneg (mul_nonneg (mul_self_nonneg _) hρ)]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    rw [Work.Spaces.mixed_zero_right, Work.FTS.StrongPersist.rhoW]
    have hD := Work.FTS.StrongEps.EpsE4Thr.SlotWt.dzSlot_weight_le_HkIntegrand4
      (α := α) (c := 0) (g := f) (m := j) (z := p.1)
      (by simp only [Work.Spaces.eta]; norm_num) (by omega) hθ
    have hrw : Work.Spaces.DzIter j f p.1 p.2 * Work.Spaces.DzIter j f p.1 p.2
        * Work.Spaces.w p.1 ^ 2
        = Work.Spaces.w p.1 ^ 2 * (Work.Spaces.DzIter j f p.1 p.2) ^ 2 := by ring
    rw [hrw]
    simpa only [Real.rpow_zero, mul_one] using hD
  · have hcg : -(Work.Spaces.gam α) ≤ (0 : ℝ) := by
      simp only [Work.Spaces.gam]
      linarith
    have hM := Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
      (α := α) (c := 0) (g := f) (a := i) (b := j) (z := p.1)
      hα hcg (by omega) (by omega) hθ
    rw [Work.FTS.StrongPersist.rhoW]
    have hrw : Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i f p.1 p.2
        * Work.Spaces.w p.1 ^ 2
        = Work.Spaces.w p.1 ^ 2 * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 := by ring
    rw [hrw]
    simpa only [Real.rpow_zero, mul_one] using hM

/-- The `γ`-weighted mixed slot `(D_z^j D_θ^i f)² · w²·sin(2θ)^{-γ}` (only defined for
`i ≥ 1`) is dominated, a.e. for the product measure, by `HkIntegrand α 4 f`: it is the
exponent `c = -γ` of `SlotWt.mixedSlot_weight_le_HkIntegrand4`. -/
theorem ae_slot_sq_mul_rhoGam_le_HkIntegrand {α : ℝ} {j i : ℕ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hji : j + i ≤ 4) (hi : 1 ≤ i) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ‖Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i f p.1 p.2
          * Work.FTS.StrongPersist.rhoGam α p.1 p.2‖
        ≤ Work.Spaces.HkIntegrand α 4 f p.1 p.2 := by
  filter_upwards [ae_mem_openQuadrant_fts] with p hp
  obtain ⟨hz, hθ0, hθ1⟩ := hp
  have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  have hsin : 0 < Real.sin (2 * p.2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hρ : 0 ≤ Work.FTS.StrongPersist.rhoGam α p.1 p.2 := by
    rw [Work.FTS.StrongPersist.rhoGam]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_self_nonneg _) hρ)]
  have hM := Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
    (α := α) (c := -(Work.Spaces.gam α)) (g := f) (a := i) (b := j) (z := p.1)
    hα le_rfl hi (by omega) hθ
  rw [Work.FTS.StrongPersist.rhoGam]
  have hrw : Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i f p.1 p.2
      * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.gam α)))
      = Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 := by ring
  rw [hrw]
  exact hM

/-! ## The target -/

theorem WipSlotIntegrable {α : ℝ} {f : Work.FTS.Galerkin.Fn} {j i : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hji : j + i ≤ 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i f p.1 p.2
          * Work.FTS.StrongPersist.rhoEta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i f p.1 p.2
          * Work.FTS.StrongPersist.rhoW p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (1 ≤ i → MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.mixed j i f p.1 p.2
          * Work.FTS.StrongPersist.rhoGam α p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  have hHk : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    HkIntegrand_integrable_prod_fts (k := 4) hsm hmem
  refine ⟨?_, ?_, ?_⟩
  · exact hHk.mono' (Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight
        (c := -(Work.Spaces.eta)) (f := f) (h := f) (j := j) (i := i) hsm hsm)
      (ae_slot_sq_mul_rhoEta_le_HkIntegrand (α := α) (j := j) (i := i) (f := f) hα hji)
  · refine hHk.mono' ?_
      (ae_slot_sq_mul_rhoW_le_HkIntegrand (α := α) (j := j) (i := i) (f := f) hα hji)
    simpa only [Work.FTS.StrongPersist.rhoW, Real.rpow_zero, mul_one] using
      (Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight
        (c := 0) (f := f) (h := f) (j := j) (i := i) hsm hsm)
  · intro hi
    exact hHk.mono' (Work.FTS.StrongEps.EpsE4Thr.SlotWt.aesm_mixed_pair_weight
        (c := -(Work.Spaces.gam α)) (f := f) (h := f) (j := j) (i := i) hsm hsm)
      (ae_slot_sq_mul_rhoGam_le_HkIntegrand (α := α) (j := j) (i := i) (f := f) hα hji hi)

end Work.FTS.StrongEps.EpsE4Thr
