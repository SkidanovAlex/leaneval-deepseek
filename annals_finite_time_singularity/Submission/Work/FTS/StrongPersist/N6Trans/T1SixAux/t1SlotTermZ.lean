import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6.Exc6
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Level-six slot energies with the `θ`-outer iteration order

`Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6` is the per-slot energy bound of the
level-six `T2` transport estimate: for a datum `g` which is `C^∞` on the open quadrant and
honestly in `ℋ⁶`, the canonical weight `canonW q z θ = w(z)^2 sin(2θ)^{-q}` times the square
of a slot `D_z^b D_θ^a g` (`a + b ≤ 6`) is product-integrable on the quadrant, its
`θ`-marginal is integrable on `Iθ`, and the `θ`-outer iterated integral is bounded by
`HkSq α 6 g`.  The exponent constraints are the natural ones: `0 ≤ q`,
`q ≤ γ = 1 + α/10` and (in the pure `D_z` case `a = 0`) `q ≤ η = 99/100`.

This is the `θ`-outer counterpart of `T1SixAux.energy_z6` / `T1SixAux.energy_mixed6`
(which are stated in the `z`-outer order and with the strict hypothesis `0 < q`); the two
extra features here are that `q = 0` is allowed and that the iteration order is the one used
by the assembly.  Both are handled by working with the *open* angular interval `(0, π/2)`:
there `sin (2θ) ∈ (0, 1]`, so `canonW` is monotone in the exponent literally from `q ≤ q'`
with no positivity assumption on `q`, and the two endpoints `θ = 0, π/2` are null for
`volume.restrict Iθ` — they are precisely the points where Lean's totalised
`sin(2θ)^{-0} = 1` would break the monotonicity.

All declarations here are complete proofs; they rest on the axioms
`[propext, Classical.choice, Quot.sound]` only.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono
  canonW_eta_eq canonW_gam_eq)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The product measure on the quadrant, and a.e. statements on the open quadrant -/

/-- The product of the two restricted Lebesgue measures on `Iz` and `Iθ`. -/
abbrev slotPm : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- A statement true on the whole open quadrant holds a.e. for the product of the two
restricted Lebesgue measures. -/
theorem ae_slotPm_of_forall_Qd {P : ℝ × ℝ → Prop}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → P (z, θ)) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), P p := by
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[(volume : MeasureTheory.Measure (ℝ × ℝ))] (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_of_forall_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet
    fun p hp => h p.1 p.2 hp.1 hp.2.1 hp.2.2

/-! ## The open-interval pointwise slot bounds -/

/-- `sin (2θ) > 0` on the open angular interval `(0, π/2)`. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- **Exponent monotonicity of `canonW` on the open angular interval.**  No positivity
assumption on `q` is needed there, because `sin (2θ) ∈ (0, 1]` gives
`sin(2θ)^{-q} ≤ sin(2θ)^{-q'}` directly from `q ≤ q'` (the boundary value
`sin(2θ)^{-0} = 1` at `θ = 0` or `θ = π/2` is what forces the restriction to the open
interval when `q = 0`). -/
theorem canonW_mono_open {q q' : ℝ} (hqq : q ≤ q') {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : canonW q z θ ≤ canonW q' z θ := by
  have hσ : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h : Real.sin (2 * θ) ^ (-q) ≤ Real.sin (2 * θ) ^ (-q') :=
    Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (by linarith)
  simp only [canonW]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- **The pointwise slot domination at level six, on the open quadrant.**  For `a + b ≤ 6`,
`q ≤ γ`, and (when `a = 0`) `q ≤ η`, the `canonW q`-weighted square of the slot
`D_z^b D_θ^a g` is dominated by the `ℋ⁶`-integrand of `g`. -/
theorem canonW_mixed_le6_open (α q : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ)
    (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- pure `D_z`-slot, priced with `q ≤ η`
    subst ha
    have hb : b ≤ 6 := by omega
    have hqb : q ≤ Work.Spaces.eta := hqη rfl
    have hmono : canonW q z θ ≤ canonW Work.Spaces.eta z θ := canonW_mono_open hqb hθ
    have hWhz : canonW Work.Spaces.eta z θ
        = (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
      rw [canonW_eta_eq z θ (Set.Ioo_subset_Icc_self hθ)]
      rfl
    rw [Work.Spaces.mixed_zero_right]
    calc canonW q z θ * (Work.Spaces.DzIter b g z θ) ^ 2
        ≤ canonW Work.Spaces.eta z θ * (Work.Spaces.DzIter b g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hmono (sq_nonneg _)
      _ = (Work.Spaces.DzIter b g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [hWhz]; ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ b hb
  · -- mixed slot, priced with `q ≤ γ`
    have hmono : canonW q z θ ≤ canonW (Work.Spaces.gam α) z θ := canonW_mono_open hqγ hθ
    have hWt : canonW (Work.Spaces.gam α) z θ = (Work.Spaces.Wt α z θ) ^ 2 :=
      canonW_gam_eq α z θ (Set.Ioo_subset_Icc_self hθ)
    calc canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ canonW (Work.Spaces.gam α) z θ * (Work.Spaces.mixed b a g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hmono (sq_nonneg _)
      _ = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hWt]; ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ a b ha hab

/-! ## The slot energy -/

/-- **The level-six slot energy, in the `θ`-outer iteration order.**  For `g` smooth on the
open quadrant and `HkMem α 6 g`, the canonical slot integrand of `D_z^b D_θ^a g`
(`a + b ≤ 6`) with exponent `q ∈ [0, γ]` (`q ≤ η` when `a = 0`) is product-integrable on
`Iz ×ˢ Iθ`, its `θ`-marginal `θ ↦ ∫_z canonW q · (D_z^bD_θ^a g)²` is integrable on `Iθ`,
and the `θ`-outer iterated integral is at most `HkSq α 6 g`. -/
theorem slotEnergy6 (α q : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ)
    (hq0 : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
          * (Work.Spaces.mixed b a g p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.IntegrableOn
        (fun θ => ∫ z in Work.Spaces.Iz,
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 g := by
  -- joint a.e. strong measurability of the slot integrand
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => canonW q p.1 p.2 * (Work.Spaces.mixed b a g p.1 p.2) ^ 2) slotPm :=
    Work.FTS.TransportS.SlotT2.mslot_joint_aesm hsm b a
  -- the pointwise domination on the open quadrant, in absolute-value shape
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2|
        ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z θ _ hθ hθ2
    have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
    rw [abs_of_nonneg (mul_nonneg (canonW_nonneg hIθ) (sq_nonneg _)), one_mul]
    exact canonW_mixed_le6_open α q g a b hqγ hqη hab ⟨hθ, hθ2⟩
  -- the `ℋ⁶`-integrand dominates, and its product integral is `HkSq α 6 g`
  obtain ⟨hHkint, hHkval⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (k := 6) hsm hmem
  have hdom : ∀ᵐ p ∂slotPm, |canonW q p.1 p.2 * (Work.Spaces.mixed b a g p.1 p.2) ^ 2|
      ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α 6 g p.1 p.2 :=
    ae_slotPm_of_forall_Qd hpt
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (1 : ℝ) * Work.Spaces.HkIntegrand α 6 g p.1 p.2) slotPm :=
    hHkint.const_mul 1
  -- product integrability of the slot integrand
  have hint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => canonW q p.1 p.2 * (Work.Spaces.mixed b a g p.1 p.2) ^ 2) slotPm := by
    refine MeasureTheory.Integrable.mono' hmaj haesm ?_
    filter_upwards [hdom] with p hp
    simpa only [Real.norm_eq_abs] using hp
  -- the product-measure bound
  have hbound : (∫ p, canonW q p.1 p.2 * (Work.Spaces.mixed b a g p.1 p.2) ^ 2 ∂slotPm)
      ≤ (1 : ℝ) * Work.Spaces.HkSq α 6 g := by
    have habs : (∫ p, canonW q p.1 p.2 * (Work.Spaces.mixed b a g p.1 p.2) ^ 2 ∂slotPm)
        ≤ ∫ p, |canonW q p.1 p.2 * (Work.Spaces.mixed b a g p.1 p.2) ^ 2| ∂slotPm :=
      MeasureTheory.integral_mono_ae hint hint.abs
        (Filter.Eventually.of_forall fun p => le_abs_self _)
    have hstep : (∫ p, |canonW q p.1 p.2 * (Work.Spaces.mixed b a g p.1 p.2) ^ 2| ∂slotPm)
        ≤ ∫ p, (1 : ℝ) * Work.Spaces.HkIntegrand α 6 g p.1 p.2 ∂slotPm :=
      MeasureTheory.integral_mono_ae hint.abs hmaj hdom
    have hfin : (∫ p, (1 : ℝ) * Work.Spaces.HkIntegrand α 6 g p.1 p.2 ∂slotPm)
        = (1 : ℝ) * Work.Spaces.HkSq α 6 g := by
      rw [MeasureTheory.integral_const_mul, hHkval]
    linarith [habs, hstep, hfin.le, hfin.ge]
  -- Fubini: the `θ`-marginal and the two iterated integrals
  have hmarg : IntegrableOn (fun θ => ∫ z in Work.Spaces.Iz,
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) Work.Spaces.Iθ :=
    hint.integral_prod_right
  have hprod := MeasureTheory.integral_integral
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) hint
  have hswap := MeasureTheory.integral_integral_swap
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) hint
  refine ⟨hint, hmarg, ?_⟩
  -- rewrite the `θ`-outer integral as the `z`-outer one and use the product bound
  rw [← hswap]
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2)
      = ∫ p, canonW q p.1 p.2 * (Work.Spaces.mixed b a g p.1 p.2) ^ 2 ∂slotPm := hprod
    _ ≤ (1 : ℝ) * Work.Spaces.HkSq α 6 g := hbound
    _ = Work.Spaces.HkSq α 6 g := by ring

end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.trace_slot_ae6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Two weight dominations

`w² = (1+z)⁴/z⁴` is dominated by both the `η`-weight and the `γ`-weight of the
`ℋ^k`-integrand, on the open angular interval where `sin(2θ) > 0`. -/

/-- `w² ≤ (w / sin(2θ)^{η/2})²` on the open angular interval. -/
theorem w_sq_le_wdivsin_sq {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
  have h2 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [sq, ← Real.rpow_add hσ]
    congr 1
    ring
  calc (Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left hone (sq_nonneg _)
    _ = (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
        rw [div_pow, h2, div_eq_mul_inv, Real.rpow_neg hσ.le]

/-- `w² ≤ (Wt α z θ)²` on the open angular interval, for `0 < α`. -/
theorem w_sq_le_Wt_sq {α : ℝ} (hα : 0 < α) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    Work.FTS.TransportS.one_le_rpow_neg hgam hθ
  have h2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hσ]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  calc (Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left hone (sq_nonneg _)
    _ = (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
        rw [mul_pow, h2]

/-! ## Weighted slots are dominated by the `ℋ^k`-integrand -/

/-- A weighted pure `D_z`-slot is dominated by the `ℋ^k`-integrand. -/
theorem wsq_dzIter_le_HkIntegrand {α : ℝ} {g : ℝ → ℝ → ℝ} {b k : ℕ} (hb : b ≤ k) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsq := Work.Spaces.sq_le_HkIntegrand_z α k g z θ b hb
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b g z θ) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (Work.Spaces.DzIter b g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right (w_sq_le_wdivsin_sq hθ) (sq_nonneg _)
    _ = (Work.Spaces.DzIter b g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ := hsq

/-- A weighted mixed slot (`a ≥ 1`) is dominated by the `ℋ^k`-integrand. -/
theorem wsq_mixed_le_HkIntegrand {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {a b k : ℕ}
    (ha : 1 ≤ a) (hab : a + b ≤ k) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsq := Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ a b ha hab
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right (w_sq_le_Wt_sq hα hθ) (sq_nonneg _)
    _ = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ := hsq

/-- **The a.e. boundary trace of an `ℋ^6`-slot.**

For almost every angle `θ`, the radial trace `z · (D_z^b D_θ^a g z θ · w z)²` vanishes both at
`0⁺` and at `+∞`, as soon as the slot is of order at most `6` and `g` is smooth on the open
quadrant with `g ∈ ℋ⁶ ∩ ℋ⁷` (the extra order is needed for the `z`-derivative of the slot).

Route: `ℋ^k`-integrability gives, for a.e. `θ`, the `z`-integrability of the `θ`-slice of
`HkIntegrand`; the two weighted slots `w²·(D_z^bD_θ^ag)²` and `w²·(D_z(D_z^bD_θ^ag))²` are
pointwise dominated by `HkIntegrand α 6 g` resp. `HkIntegrand α 7 g`; the one-dimensional
`H¹`-lemma `Hon.trace_of_weights` then yields the two limits. -/
theorem trace_slot_ae6 (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g)
    (h6 : Work.Spaces.HkMem α 6 g) (h7 : Work.Spaces.HkMem α 7 g) (hab : a + b ≤ 6) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z : ℝ => z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z : ℝ => z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0) := by
  have hI6 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 6 g z θ)
        Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsm h6).1
  have hI7 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 7 g z θ)
        Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsm h7).1
  filter_upwards [hI6, hI7, Work.FTS.TransportS.ae_mem_Ioo_Iθ] with θ hJ6 hJ7 hθ
  have hJ6' : MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 6 g z θ)
      (Set.Ioi (0 : ℝ)) := (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hJ6
  have hJ7' : MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 7 g z θ)
      (Set.Ioi (0 : ℝ)) := (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hJ7
  -- the two pointwise dominations of the weighted slots by the `ℋ^k`-integrands
  have hdom1 : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0
      simpa only [Work.Spaces.mixed_zero_right] using
        wsq_dzIter_le_HkIntegrand (α := α) (g := g) (b := b) (k := 6) (by omega) hθ
    · exact wsq_mixed_le_HkIntegrand hα (Nat.one_le_iff_ne_zero.mpr ha0) hab hθ
  have hdom2 : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 g z θ := by
    intro z
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0
      simpa only [Work.Spaces.mixed_zero_right] using
        wsq_dzIter_le_HkIntegrand (α := α) (g := g) (b := b + 1) (k := 7) (by omega) hθ
    · exact wsq_mixed_le_HkIntegrand hα (Nat.one_le_iff_ne_zero.mpr ha0) (by omega) hθ
  -- continuity of the two slots in `z` on `(0,∞)` (via the `z`-slices of the smooth extension)
  have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z; rfl
    rw [hfun]
    exact ContinuousOn.pow (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))) 2
  have hcd1 := (hsm.mixed b a).curry_z hθ
  have hcd2 := (hsm.mixed (b + 1) a).curry_z hθ
  have hv1c : ContinuousOn (fun z : ℝ => Work.Spaces.mixed b a g z θ) (Set.Ioi (0 : ℝ)) :=
    hcd1.continuousOn
  have hv2c : ContinuousOn (fun z : ℝ => Work.Spaces.mixed (b + 1) a g z θ)
      (Set.Ioi (0 : ℝ)) :=
    hcd2.continuousOn
  -- integrability of the two weighted slots over `(0,∞)`
  have hW1 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' hJ6' ((hw2.mul (hv1c.pow 2)).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact hdom1 z)
  have hW2 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' hJ7' ((hw2.mul (hv2c.pow 2)).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact hdom2 z)
  -- the `z`-derivative of the slot `D_z^bD_θ^ag` is the order-`(b+1)` slot
  have hderiv_eq : (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (z * deriv (fun z' : ℝ => Work.Spaces.mixed b a g z' θ) z) ^ 2)
      = fun z => (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2 := by
    funext z
    rfl
  have hW2' : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * (z * deriv (fun z' : ℝ => Work.Spaces.mixed b a g z' θ) z) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    rw [hderiv_eq]
    exact hW2
  -- differentiability of the slot in `z`
  have hv : ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed b a g z' θ) z := fun z hz =>
    (hcd1.differentiableOn (by simp [Work.Stability.smoothOrder])).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  exact Work.FTS.StrongPersist.N6Trans.Hon.trace_of_weights
    (v := fun z' => Work.Spaces.mixed b a g z' θ) hv
    (MeasureTheory.IntegrableOn.mono_set hW1 Set.Ioo_subset_Ioi_self)
    (MeasureTheory.IntegrableOn.mono_set hW2' Set.Ioo_subset_Ioi_self)
    (MeasureTheory.IntegrableOn.mono_set hW1 (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
    (MeasureTheory.IntegrableOn.mono_set hW2' (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))

end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_eta_eq canonW_gam_eq)
open Work.FTS.StrongPersist.N6Trans.SixAux (aesm_canonW_abs_mul)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false


end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
