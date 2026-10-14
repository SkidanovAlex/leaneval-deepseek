import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.N6Trans.HonestHardSlotLem
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorLem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The honest-class bound for the pointwise majorant `EasyMajor` of the flat `ℋ⁴` pairing.**

For the honest data class — `f`, `g` of class `C^∞` on the *open* quadrant (`SmoothOpen`),
honestly in `ℋ⁴` (`HkMem α 4`), and `g` with `DecayAll 4 g` (no decay of `f`, no smoothness at
`z = 0` or at the angular boundary) — the majorant `EasyMajor α f g` is integrable for the
product measure `pm` and

  `∫ EasyMajor α f g ≤ C/√(γ-1) · |f|_{ℋ⁴} · |g|²_{ℋ⁴}`.

Route: the two pointwise `L^∞`-bounds `Kf`, `Kg` of order `≤ 2` come from `HonestSupMixed`
(`C1/√(γ-1)·|f|_{ℋ⁴}` resp. `C1/√(γ-1)·|g|_{ℋ⁴}`), the angular-supremum device `K3` from the
open-class `Work.FTS.TransportS.SlotT2.supThetaIntOpen` (`K3 = CK/√(γ-1)²·|f|²_{ℋ⁴}`), and the
`2`-dimensional assembly is the open-class (no-decay) port `AssemblyQ_o` of
`Work.H2.T1Q.AssemblyQ` (see `HonestEasyMajorAux`), whose exceptional summand is
`OpenTwins.ExcBoundOpen`.  The three terms of `TTot α f g Kf Kg K3` are all
`(const/√(γ-1))·|f|_{ℋ⁴}·HkSq α 4 g`, with constants `C1`, `C1` and `√CK`. -/
theorem HonestEasyMajorLem : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.DecayAll 4 g →
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.H2.EasyMajor α f g p.1 p.2)
        Work.FTS.H2.pm ∧
    ∫ p, Work.FTS.H2.EasyMajor α f g p.1 p.2 ∂Work.FTS.H2.pm
      ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g := by
  obtain ⟨C1, hC1pos, hC1⟩ := HonestSupMixed
  obtain ⟨CK, hCKpos, hCK⟩ := Work.FTS.TransportS.SlotT2.supThetaIntOpen
  refine ⟨5000000 * (2 * C1 + Real.sqrt CK), by positivity, ?_⟩
  intro α f g hα hα1 hf hmf hg hmg hdecg
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hs0 : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ
  have hF0 : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hG0 : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  -- ### the two pointwise `L^∞`-bounds of order `≤ 2`
  have hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ|
        ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f :=
    fun b a hab z θ hz hθ hθ2 => hC1 α f hα hα1 hf hmf b a hab z θ hz hθ hθ2
  have hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ|
        ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g :=
    fun b a hab z θ hz hθ hθ2 => hC1 α g hα hα1 hg hmg b a hab z θ hz hθ hθ2
  -- ### the angular-supremum device `K3`
  obtain ⟨hGint0, hGle0⟩ := hCK α f 3 hα hα1 (by norm_num) hf hmf
  have hGint : MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
    simpa only [Work.FTS.H2.supAbsThO, mul_pow] using hGint0
  have hGle : (∫ z in Work.Spaces.Iz,
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2)
      ≤ CK / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
    simpa only [Work.FTS.H2.supAbsThO, mul_pow] using hGle0
  have hK30 : (0 : ℝ) ≤ CK / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f :=
    mul_nonneg (div_nonneg hCKpos.le hγ.le) (Work.Spaces.HkSq_nonneg α 4 f)
  have hK3sqrt : Real.sqrt (CK / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
      = Real.sqrt CK / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
    rw [show Work.Spaces.HkNorm α 4 f = Real.sqrt (Work.Spaces.HkSq α 4 f) from rfl]
    rw [← Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    rw [Real.sqrt_mul (div_nonneg hCKpos.le hγ.le), Real.sqrt_mul_self (Real.sqrt_nonneg _),
      Real.sqrt_div hCKpos.le]
  -- ### nonnegativity of `Kf` and `Kg`
  have hKf0 : (0 : ℝ) ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f :=
    mul_nonneg (div_nonneg hC1pos.le hs0.le) hF0
  have hKg0 : (0 : ℝ) ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g :=
    mul_nonneg (div_nonneg hC1pos.le hs0.le) hG0
  -- ### the open-class assembly
  obtain ⟨hEM_int, hEM_le⟩ :=
    HonestEasyMajorAux.AssemblyQ_o α f g
      (C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f)
      (C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g)
      (CK / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
      hα hα1 hf hg hdecg hmf hmg hKf hKg hGint hGle hKf0 hKg0 hK30
  refine ⟨hEM_int, hEM_le.trans (le_of_eq ?_)⟩
  rw [Work.FTS.H2.TTot, hK3sqrt, ← Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α 4 g),
    show Work.Spaces.HkNorm α 4 g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl]
  ring

end Work.FTS.StrongPersist.N6Trans
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.HardSlotLemGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **Angular integrability of a single `ℋ⁴`-slot, generalized.**
The slot `θ ↦ (D_z^bD_θ^a g)(z,θ)² · sin(2θ)^{-q}` is integrable on `Iθ` for `a + b ≤ 4`, for
`q ∈ {0, η}` when `a = 0` and `q ∈ {0, η, γ}` when `a ≥ 1`.

This is the statement of `Work.FTS.StrongPersist.N6Trans.T1Hon.SlotIntegrableGen`, recorded here
as a `private` helper so that this module is self-contained.  It generalizes
`HardSlotAux.SlotIntegrableHonest` (the case `a + b = 4`): the whole proof is a replay of that
one, with `b ≤ 4` in place of `b = 4` and, in the `a = 0` branch, the extra dominating step
`(D_z^b g)² ≤ (D_z^b g)² sin(2θ)^{-η}` for the exponent `q = 0` (valid since
`0 < sin(2θ) ≤ 1` on the open interval). -/
private theorem slotIntegrableGen (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Work.Spaces.Iθ := by
  have hwne : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwne
  have hHk : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    have h : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
        (volume.restrict Work.Spaces.Iθ) := hmem.1 z (le_of_lt hz)
    rwa [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo] at h
  change Integrable (fun θ : ℝ =>
      (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
    (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo]
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- ## `a = 0`: the pure `D_z`-slot with exponent `0` or `η`
    have hb4 : b ≤ 4 := by omega
    rw [ha0, Work.Spaces.mixed_zero_right]
    -- the `η`-weighted slot is exactly the `HkMem`-integrable summand of the norm
    have heta : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have hZ : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hg hmem b hb4 (le_of_lt hz)
      rw [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo] at hZ
      refine (hZ.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [mul_pow, Work.H2.T1Q.slotQ_whz_sq z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      rw [show (Work.Spaces.DzIter b g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter b g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) from by ring]
      rw [inv_mul_cancel_left₀ hw2ne]
    rcases hq0 ha0 with hq | hq
    · -- `q = 0`: dominated by the `η`-slot, since `sin(2θ) ≤ 1` on the open interval
      rw [hq]
      have haesm : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(0 : ℝ)))
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
        have hfun : (fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(0 : ℝ)))
            = fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2 := by
          funext θ
          rw [neg_zero, Real.rpow_zero, mul_one]
        rw [hfun]
        exact ContinuousOn.aestronglyMeasurable
          ((Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_slice_of_smoothOpen
            (hg.DzIter b) hz).pow 2) measurableSet_Ioo
      refine Integrable.mono' heta haesm ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos
          (Work.FTS.StrongPersist.N6Trans.HardSlotAux.sin_two_pos_of_Ioo hθ)
          (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
      rw [neg_zero, Real.rpow_zero, mul_one,
        Real.norm_of_nonneg (sq_nonneg (Work.Spaces.DzIter b g z θ))]
      simpa using mul_le_mul_of_nonneg_left h1 (sq_nonneg (Work.Spaces.DzIter b g z θ))
    · -- `q = η`: exactly the `ℋ⁴`-summand
      rw [hq]
      exact heta
  · -- ## `a ≥ 1`: every slot is a summand of the `ℋ⁴`-integrand with weight `sin(2θ)^{-γ}`
    have hcontm : ContinuousOn (fun θ : ℝ => Work.Spaces.mixed b a g z θ)
        (Set.Ioo (0 : ℝ) (π / 2)) :=
      Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_slice_of_smoothOpen
        (hg.mixed b a) hz
    have hM : Integrable (fun θ : ℝ =>
        (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have haesm : AEStronglyMeasurable (fun θ : ℝ =>
          (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2)
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
        ContinuousOn.aestronglyMeasurable
          ((hcontm.mul (Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_Wt_slice
            α z)).pow 2) measurableSet_Ioo
      refine Integrable.mono' hHk haesm ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ a b hapos hab
    have hgamma : Integrable (fun θ : ℝ => (Work.Spaces.mixed b a g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      refine (hM.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [mul_pow, Work.H2.T1Q.slotQ_wt_sq α z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      rw [show (Work.Spaces.mixed b a g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed b a g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) from by ring]
      rw [inv_mul_cancel_left₀ hw2ne]
    -- a smaller exponent gives a smaller weight, so every `q ≤ γ` is integrable as well
    have hred : ∀ p : ℝ, p ≤ Work.Spaces.gam α → Integrable
        (fun θ : ℝ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-p))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      intro p hp
      have haesm : AEStronglyMeasurable (fun θ : ℝ =>
          (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-p))
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
        ContinuousOn.aestronglyMeasurable
          ((hcontm.pow 2).mul
            (Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_sin_two_rpow (-p)))
          measurableSet_Ioo
      refine Integrable.mono' hgamma haesm ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg
          (Work.Spaces.sin_two_nonneg_of_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _))]
      exact mul_le_mul_of_nonneg_left
        (Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le hp hθ)
        (sq_nonneg _)
    obtain hq | hq | hq := hqa hapos
    · rw [hq]
      exact hred 0 (le_of_lt (Work.Spaces.gam_pos hα))
    · rw [hq]
      exact hred Work.Spaces.eta (le_trans (le_of_lt Work.Spaces.eta_lt_one)
        (le_of_lt (Work.Spaces.one_lt_gam hα)))
    · rw [hq]
      exact hred (Work.Spaces.gam α) le_rfl

/-- The honest-class angular integration-by-parts bound for a single `g`-block, generalized from
the proved `Work.FTS.StrongPersist.N6Trans.HonestHardSlotLem`
(`Submission/Work/FTS/StrongPersist/N6Trans/HonestHardSlotLem.lean`) in exactly two respects:

* the slot constraint is relaxed from `a + b = 4` to `a + b ≤ 4` (the order is used *only* to
  invoke the slot integrability, so the generalization is immediate);
* for `a = 0` the exponent `q = 0` is allowed as well as `q = eta` (needed for the `w²` leaf
  weight of the slot `(0,4)`).

Everything else is verbatim: `Kf = C₁/√(γ-1)·|f|_{ℋ⁴}` is the `L^∞`-bound of `f` and of
`sin(2θ)∂_θf` from `Work.FTS.StrongPersist.N6Trans.HonestSupMixed`, and the bound itself is
`HardSlotAux.IbpSliceBound` (cut-off IBP + shrinking-endpoint limit).  The only two uses of the
slot exponent `q` in the proof are `|1 - q| ≤ 1` (true for `q ∈ {0, eta, gam α}` since
`eta = 99/100` and `gam α = 1 + α/10 ≤ 11/10`) and the slot-integrability input.

**Self-containment.**  The slot-integrability input needed here is the statement of
`Work.FTS.StrongPersist.N6Trans.T1Hon.SlotIntegrableGen` (`a + b ≤ 4`; `q ∈ {0, eta}` for
`a = 0`; `q ∈ {0, eta, gam α}` for `a ≥ 1`), which is being proved in parallel in
`Submission/Work/FTS/StrongPersist/N6Trans/T1Hon/SlotIntegrableGen.lean`; do **not** import that
module (it may still carry a `sorry`).  Instead, prove that slot-integrability statement as a
`private` helper declaration inside this file: it is the generalization of
`HardSlotAux.SlotIntegrableHonest` (whose proof already isolates `hb4 : a + b ≤ 4`; the only new
work is the `a = 0`, `q = 0` branch, and for `a = 0` the existing proof reduces to
`mixed b 0 g = DzIter b g` with `b ≤ 4`, dominated by `integrableOn_zSummand`). -/
theorem HardSlotLemGen : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (q : ℝ),
    0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.DecayAll 4 g →
    ∀ (a b : ℕ), a + b ≤ 4 →
      (a = 0 → q = 0 ∨ q = Work.Spaces.eta) →
      (1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
    ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.N6Trans.HonestSupMixed
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpSliceBound
  refine ⟨C₁ * (3 / 2 + B / 2), by positivity, ?_⟩
  intro α f g q hα hα1 hfsm hfmem hgsm hgmem hgdec a b hab hq0 hqa z hz
  set Kf : ℝ := C₁ / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f with hKf
  have hKf0 : 0 ≤ Kf := by
    rw [hKf]
    exact mul_nonneg (div_nonneg hC₁pos.le (Real.sqrt_nonneg _))
      (Work.Spaces.HkNorm_nonneg α 4 f)
  -- the only two facts about `q` used below
  have hqabs : |1 - q| ≤ 1 := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rcases hq0 ha0 with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num [Work.Spaces.eta]
    · rcases hqa hapos with h | h | h
      · rw [h]; norm_num
      · rw [h]; norm_num [Work.Spaces.eta]
      · rw [h]
        rw [Work.Spaces.gam]
        have h2 : (1 : ℝ) - (1 + α / 10) = -(α / 10) := by ring
        rw [h2, abs_neg, abs_of_nonneg (by linarith)]
        linarith
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate slice `z = 0`: the radial weight vanishes, so both sides are `0`
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    have h0 : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f 0 θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a g) 0 θ * Work.Spaces.mixed b a g 0 θ)
        = fun _ => (0 : ℝ) := by
      funext θ
      rw [hw0]
      ring
    rw [h0, MeasureTheory.integral_zero, abs_zero, hw0]
    simp
  · -- the genuine slice `z > 0`: strip the (constant) radial factor `w(z)²`, reduce to the
    -- angular slices `F`, `V` and apply the integration-by-parts bound
    set F : ℝ → ℝ := fun θ => f z θ with hF
    set V : ℝ → ℝ := fun θ => Work.Spaces.mixed b a g z θ with hV
    have hF1 : ContDiffOn ℝ 1 F (Set.Ioo 0 (π / 2)) := by
      rw [hF]
      exact (hfsm.curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
    have hV1 : ContDiffOn ℝ 1 V (Set.Ioo 0 (π / 2)) := by
      rw [hV]
      exact ((hgsm.mixed b a).curry_θ hzpos).of_le
        (by simp [Work.Stability.smoothOrder])
    have hFb : ∀ θ ∈ Set.Ioo 0 (π / 2), |F θ| ≤ Kf := by
      intro θ hθ
      have h := hC₁ α f hα hα1 hfsm hfmem 0 0 (by norm_num) z θ hzpos hθ.1 hθ.2
      have h' : |f z θ| ≤ C₁ / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := h
      simpa only [hF, hKf] using h'
    have hFd : ∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv F θ| ≤ Kf := by
      intro θ hθ
      have h := hC₁ α f hα hα1 hfsm hfmem 0 1 (by norm_num) z θ hzpos hθ.1 hθ.2
      have h' : |Work.Spaces.Dth f z θ| ≤ C₁ / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 f := h
      simpa only [hF, hKf, Work.Spaces.Dth, Work.Spaces.pth] using h'
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ := by
      have h := slotIntegrableGen α g a b q hα hgsm hgmem hab hq0 hqa hzpos
      simpa only [hV] using h
    have hslice := hB q Kf F V hKf0 hqabs hF1 hV1 hFb hFd hint
    have hcongr : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
        = fun θ : ℝ => (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-q) * F θ
            * (Real.sin (2 * θ) * deriv V θ) * V θ) := by
      funext θ
      simp only [hF, hV, Work.Spaces.Dth, Work.Spaces.pth]
      ring
    calc |∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        = (Work.Spaces.w z) ^ 2 * |∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * F θ
            * (Real.sin (2 * θ) * deriv V θ) * V θ| := by
          rw [hcongr, MeasureTheory.integral_const_mul, abs_mul,
            abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
      _ ≤ (Work.Spaces.w z) ^ 2 * ((3 / 2 + B / 2) * Kf
            * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
          mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
      _ = C₁ * (3 / 2 + B / 2) / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          rw [hKf]; ring
      _ = C₁ * (3 / 2 + B / 2) / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          simp only [hV]

end Work.FTS.StrongPersist.N6Trans.T1Hon
end
