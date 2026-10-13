import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.coefFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pureGamFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSixTop
import Submission.Work.FTS.StrongPersist.N6Trans.HardPair.mixedTerm_le_six
import Submission.Work.FTS.StrongPersist.N6Trans.L6Remainder
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.L6Aux2
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 3200000
set_option autoImplicit false

set_option quotPrecheck false in
/-- The product of the two restricted Lebesgue measures, as in the statement. -/
local notation "IPM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

noncomputable section

/-! ## Elementary bookkeeping -/

/-- `|ρ · A · B · C| = ρ · |A · B| · |C|` for a nonnegative leaf weight `ρ`. -/
theorem abs_four_leafW {ρ A B C : ℝ} (hρ : 0 ≤ ρ) :
    |ρ * A * B * C| = ρ * |A * B| * |C| := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρ, abs_mul]
  ring

/-- A bound with constant `K ≤ C` upgrades to the statement's right-hand side. -/
theorem const_mul_le_of_le {C K Mf Mth S : ℝ} (hK : K ≤ C) (hC : 0 ≤ C)
    (hMf : 0 ≤ Mf) (hMth : 0 ≤ Mth) (hS : 0 ≤ S) :
    K * Mf * S ≤ C * (Mf + Mth) * S := by
  have h1 : K * Mf ≤ C * Mf := mul_le_mul_of_nonneg_right hK hMf
  have h2 : C * Mf ≤ C * (Mf + Mth) := mul_le_mul_of_nonneg_left (by linarith) hC
  exact mul_le_mul_of_nonneg_right (h1.trans h2) hS

/-- Every leaf weight is nonnegative on the closed angular interval. -/
theorem leafW_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ ρ z θ := by
  rcases hρ with h | h | ⟨_, h⟩
  · rw [h]
    exact Work.FTS.TransportS.leafEta_nonneg
      (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)
  · rw [h]; exact Work.FTS.TransportS.leafOne_nonneg z θ
  · rw [h]
    exact Work.FTS.TransportS.leafGam_nonneg α
      (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)

/-- **Pointwise domination gives integrability and the value bound.**  A function which is
a.e. dominated by `M · HkIntegrand α 6 g` is product-integrable and its integral is bounded
by `M · HkSq α 6 g`. -/
theorem integrable_and_bound_of_pointwise {α M : ℝ} {g : ℝ → ℝ → ℝ} {I : ℝ × ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) (hM : 0 ≤ M)
    (haesm : MeasureTheory.AEStronglyMeasurable I IPM)
    (hpt : ∀ᵐ p ∂IPM, ‖I p‖ ≤ M * Work.Spaces.HkIntegrand α 6 g p.1 p.2) :
    MeasureTheory.Integrable I IPM ∧ |∫ p, I p ∂IPM| ≤ M * Work.Spaces.HkSq α 6 g := by
  obtain ⟨hHk, hHkval⟩ :=
    Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hsg hmem
  have hdom : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => M * Work.Spaces.HkIntegrand α 6 g p.1 p.2) IPM := hHk.const_mul M
  have hInt : MeasureTheory.Integrable I IPM := MeasureTheory.Integrable.mono' hdom haesm hpt
  refine ⟨hInt, ?_⟩
  have h1 : ‖∫ p, I p ∂IPM‖ ≤ ∫ p, ‖I p‖ ∂IPM :=
    MeasureTheory.norm_integral_le_integral_norm _
  rw [Real.norm_eq_abs] at h1
  have h2 : ∫ p, ‖I p‖ ∂IPM ≤ ∫ p, M * Work.Spaces.HkIntegrand α 6 g p.1 p.2 ∂IPM :=
    MeasureTheory.integral_mono_ae hInt.norm hdom hpt
  have h3 : ∫ p, M * Work.Spaces.HkIntegrand α 6 g p.1 p.2 ∂IPM
      = M * Work.Spaces.HkSq α 6 g := by
    rw [MeasureTheory.integral_const_mul, hHkval]
  linarith

/-- A.e. strong measurability of the summand integrand (the leaf weight is one of the three
continuous canonical weights). -/
theorem leafW_aesm_summand {α : ℝ} {f g : ℝ → ℝ → ℝ} {a b a₁ b₁ : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ f p.1 p.2
        * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) IPM := by
  rcases hρ with h | h | ⟨_, h⟩
  · rw [h]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta).mul
          ((hsf.mixed b₁ a₁).continuousOn)).mul
          ((hsg.mixed (b - b₁ + 1) (a - a₁)).continuousOn)).mul
          ((hsg.mixed b a).continuousOn))
  · rw [h]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      ((((Work.FTS.TransportS.continuousOn_w_sq_Qd).mul
          ((hsf.mixed b₁ a₁).continuousOn)).mul
          ((hsg.mixed (b - b₁ + 1) (a - a₁)).continuousOn)).mul
          ((hsg.mixed b a).continuousOn))
  · rw [h]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)).mul
          ((hsf.mixed b₁ a₁).continuousOn)).mul
          ((hsg.mixed (b - b₁ + 1) (a - a₁)).continuousOn)).mul
          ((hsg.mixed b a).continuousOn))

/-! ## The two pointwise case lemmas -/

/-- **The `a₁ = 0`, `b₁ ≥ 1` summand** (pointwise form): the single angular derivative of
`f` is absent, so `f` is bounded by `|f|_{𝒲^{6,∞}}` and the two `g`-slots are absorbed by
`HkIntegrand α 6 g`. -/
theorem summand_zeroAngular_pointwise {α : ℝ} {f g : ℝ → ℝ → ℝ} {a b b₁ : ℕ}
    {ρ : ℝ → ℝ → ℝ} (hα : 0 < α) (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hfw : Work.Spaces.WlInfMem α 6 f) (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hab : a + b ≤ 6) (hb₁ : 1 ≤ b₁) (hb₁b : b₁ ≤ b) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |ρ z θ * Work.Spaces.mixed b₁ 0 f z θ * Work.Spaces.mixed (b - b₁ + 1) a g z θ
          * Work.Spaces.mixed b a g z θ|
        ≤ 1000 * Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hW0 : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfw
  have hMf0 : 0 ≤ 1000 * Work.Spaces.WlInf α 6 f := by linarith
  have h := Work.FTS.StrongPersist.N6Trans.l6_summand_le_zero (α := α)
    (Mf := 1000 * Work.Spaces.WlInf α 6 f) (f := f) (g := g) (a := a) (b := b) (b1 := b₁)
    (ρ := ρ) hα hMf0 le_rfl hsf hfw hρ hab hb₁ hb₁b z θ hz hθ0 hθ1
  calc |ρ z θ * Work.Spaces.mixed b₁ 0 f z θ * Work.Spaces.mixed (b - b₁ + 1) a g z θ
          * Work.Spaces.mixed b a g z θ|
      = ρ z θ * |Work.Spaces.mixed b₁ 0 f z θ * Work.Spaces.mixed (b - b₁ + 1) a g z θ|
          * |Work.Spaces.mixed b a g z θ| :=
        abs_four_leafW (leafW_nonneg hρ hθI)
    _ ≤ 1000 * Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ := h

/-- **The `a₁ = a ≥ 1` summand with the `η`-leaf weight** (pointwise form): the `f`-factor
carries `a ≥ 1` angular derivatives, hence the fractional gain
`|D_z^{b₁}D_θ^af| ≤ 1000|f|(α+σ)σ^{α/5} ≤ 2000|f|`, and both `g`-slots are priced at the
`η`-slot weight (compatible with the pure and the mixed slot alike). -/
theorem summand_pureEta_pointwise {α : ℝ} {f g : ℝ → ℝ → ℝ} {a b b₁ : ℕ}
    {ρ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hfw : Work.Spaces.WlInfMem α 6 f)
    (hρ : ρ = Work.FTS.TransportS.leafEta ∨ ρ = Work.FTS.TransportS.leafOne)
    (ha : 1 ≤ a) (hab : a + b ≤ 6) (hb₁ : b₁ ≤ b) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |ρ z θ * Work.Spaces.mixed b₁ a f z θ * Work.Spaces.mixed (b - b₁ + 1) 0 g z θ
          * Work.Spaces.mixed b a g z θ|
        ≤ 2000 * Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hθ1])
  have hW0 : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfw
  -- the `f`-factor
  have hfac : |Work.Spaces.mixed b₁ a f z θ| ≤ 2000 * Work.Spaces.WlInf α 6 f := by
    have h := Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 (a := a) (b := b₁)
      hα hsf hfw ha (by omega) hz hθ
    have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hr : Real.sin (2 * θ) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs.le hle1 (by positivity)
    have hr0 : 0 ≤ Real.sin (2 * θ) ^ (α / 5) := Real.rpow_nonneg hs.le _
    have h2 : (α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5) ≤ 2 := by
      simpa using mul_le_mul (by linarith [hα, hα1] : α + Real.sin (2 * θ) ≤ 2) hr hr0
        (by norm_num : (0 : ℝ) ≤ 2)
    calc |Work.Spaces.mixed b₁ a f z θ|
        ≤ 1000 * (Work.Spaces.WlInf α 6 f
            * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5))) := h
      _ ≤ 1000 * (Work.Spaces.WlInf α 6 f * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hW0) (by norm_num)
      _ = 2000 * Work.Spaces.WlInf α 6 f := by ring
  -- the two `g`-slots against the `η`-weight
  have hpair : Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
      * |Work.Spaces.mixed (b - b₁ + 1) 0 g z θ| * |Work.Spaces.mixed b a g z θ|
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
    have h := Work.FTS.StrongPersist.N6Trans.canonW_pair_le6 (α := α) (g := g)
      (q := Work.Spaces.eta) Work.Spaces.eta_pos
      (Work.FTS.TransportS.T2Sup.eta_le_gam hα) (fun _ => le_rfl) (fun _ => le_rfl)
      (j := b - b₁ + 1) (i := 0) (b := b) (a := a) (by omega) hab hzI hθI
    simpa only [Work.Spaces.mixed_zero_right] using h
  -- the leaf weight is dominated by `canonW η`
  have hρle : ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ := by
    rcases hρ with h | h
    · rw [h]
      exact le_of_eq rfl
    · rw [h]
      have h1 : (1 : ℝ) ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
        Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
      have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc Work.FTS.TransportS.leafOne z θ = (Work.Spaces.w z) ^ 2 := rfl
        _ = (Work.Spaces.w z) ^ 2 * 1 := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left h1 hw
        _ = Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ := rfl
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hρnn : 0 ≤ ρ z θ := by
    rcases hρ with h | h
    · rw [h]
      exact Work.FTS.TransportS.leafEta_nonneg
        (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI)
    · rw [h]; exact Work.FTS.TransportS.leafOne_nonneg z θ
  calc |ρ z θ * Work.Spaces.mixed b₁ a f z θ * Work.Spaces.mixed (b - b₁ + 1) 0 g z θ
          * Work.Spaces.mixed b a g z θ|
      = ρ z θ * |Work.Spaces.mixed b₁ a f z θ|
          * (|Work.Spaces.mixed (b - b₁ + 1) 0 g z θ| * |Work.Spaces.mixed b a g z θ|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
        ring
    _ ≤ Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * |Work.Spaces.mixed b₁ a f z θ|
          * (|Work.Spaces.mixed (b - b₁ + 1) 0 g z θ| * |Work.Spaces.mixed b a g z θ|) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hρle (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = |Work.Spaces.mixed b₁ a f z θ|
          * (Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
              * |Work.Spaces.mixed (b - b₁ + 1) 0 g z θ| * |Work.Spaces.mixed b a g z θ|) := by
        ring
    _ ≤ |Work.Spaces.mixed b₁ a f z θ| * Work.Spaces.HkIntegrand α 6 g z θ :=
        mul_le_mul_of_nonneg_left hpair (abs_nonneg _)
    _ ≤ (2000 * Work.Spaces.WlInf α 6 f) * Work.Spaces.HkIntegrand α 6 g z θ :=
        mul_le_mul_of_nonneg_right hfac hHnn

/-- The summand integrand of the level-six transport expansion, as a reducible abbreviation. -/
abbrev summandFun (ρ : ℝ → ℝ → ℝ) (f g : ℝ → ℝ → ℝ) (a b a₁ b₁ : ℕ) : ℝ × ℝ → ℝ :=
  fun p => ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
    * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2

/-- **The pointwise assembly of a summand.**  A pointwise bound on the open quadrant, together
with a.e. strong measurability, gives integrability and the value bound for the summand. -/
theorem summandFun_aesm_and_bound {α M : ℝ} {f g : ℝ → ℝ → ℝ} {a b a₁ b₁ : ℕ}
    {ρ : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hmem : Work.Spaces.HkMem α 6 g) (hM : 0 ≤ M)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |ρ z θ * Work.Spaces.mixed b₁ a₁ f z θ
          * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ * Work.Spaces.mixed b a g z θ|
        ≤ M * Work.Spaces.HkIntegrand α 6 g z θ) :
    MeasureTheory.Integrable (summandFun ρ f g a b a₁ b₁) IPM ∧
      |∫ p, summandFun ρ f g a b a₁ b₁ p ∂IPM| ≤ M * Work.Spaces.HkSq α 6 g := by
  have haesm : MeasureTheory.AEStronglyMeasurable (summandFun ρ f g a b a₁ b₁) IPM :=
    leafW_aesm_summand (α := α) (f := f) (g := g) (a := a) (b := b) (a₁ := a₁)
      (b₁ := b₁) (ρ := ρ) hsf hsg hρ
  have hptae : ∀ᵐ p ∂IPM, ‖summandFun ρ f g a b a₁ b₁ p‖
      ≤ M * Work.Spaces.HkIntegrand α 6 g p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
      ‖summandFun ρ f g a b a₁ b₁ p‖ ≤ M * Work.Spaces.HkIntegrand α 6 g p.1 p.2) ?_
    intro z θ hz hθ0 hθ1
    rw [Real.norm_eq_abs]
    exact hpt z θ hz hθ0 hθ1
  exact integrable_and_bound_of_pointwise hsg hmem hM haesm hptae

/-- The per-summand bound of the level-six `D_z`-transport expansion: for every Leibniz index
`(a₁,b₁)` with `a₁ ≤ a`, `b₁ ≤ b` (`a + b ≤ 6`) the product-measure integral of
`ρ · D_z^{b₁}D_θ^{a₁}f · D_z^{b-b₁+1}D_θ^{a-a₁}g · D_z^bD_θ^ag` is integrable and bounded by
`C·(WlInf α 6 f + CoefTh 3 f)·HkSq α 6 g`.  Branch structure, all pieces proved in the
workspace: `(a₁,b₁) = (0,0)` with `a+b ≤ 5` → `fluxFamSix`;  with `a+b = 6` → `fluxFamSixTop`;
`a₁ = 0`, `b₁ ≥ 1` → `L6Remainder.l6_summand_le_zero` (pointwise) integrated against
`HkIntegrand α 6 g` via `Hon.integrable_HkIntegrand_prod_open`;  `1 ≤ a₁ < a` →
`HardPair.mixedTerm_le_six` (same pointwise route);  `a₁ = a`, `a + b₁ ≤ 4` → `coefFamSix`;
`a₁ = a`, `5 ≤ a + b₁` → `pureGamFamSix` when `ρ = leafGam α` (it needs `b-b₁+1 ≤ 2`, which
follows from `5 ≤ a+b₁`, `a+b ≤ 6`), and the pointwise `canonW η`-route otherwise
(`ρ ≤ canonW η = leafEta` in both other cases, `canonW η·(D_z^m g)² ≤ HkIntegrand α 6 g` for
the pure slot by `canonW_slot_le_HkGen`, and `canonW η·(mixed b a g)² ≤ canonW γ·(mixed b a g)²
≤ HkIntegrand α 6 g` since `η ≤ γ`). -/
theorem sixSummandBound : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f g : ℝ → ℝ → ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.VocabO.CoefThMem 3 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
    a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ → a₁ ≤ a → b₁ ≤ b →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b₁ a₁ f p.1 p.2
          * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
        |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
              * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
          ≤ C * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
              * Work.Spaces.HkSq α 6 g := by
  obtain ⟨Cf, hCf0, hCf⟩ := fluxFamSix
  obtain ⟨Ct, hCt0, hCt⟩ := fluxFamSixTop
  obtain ⟨Cc, hCc0, hCc⟩ := coefFamSix
  obtain ⟨Cp, hCp0, hCp⟩ := pureGamFamSix
  obtain ⟨Cm, hCm0, hCm⟩ := Work.FTS.StrongPersist.N6Trans.HardPair.mixedTerm_le_six
  set C : ℝ := Cf + Ct + Cc + Cp + Cm + 3001 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro α hα f g a b a₁ b₁ ρ hsf hfw hc3 hsg hg6 hg7 hdec hab hρ ha₁ hb₁
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hMf0 : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfw
  have hMth0 : 0 ≤ Work.FTS.VocabO.CoefTh 3 f := Work.FTS.TransportS.coefTh_nonneg 3 f
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  have hC0 : 0 ≤ C := le_of_lt hCpos
  have hCfC : Cf ≤ C := by rw [hCdef]; linarith
  have hCtC : Ct ≤ C := by rw [hCdef]; linarith
  have hCcC : Cc ≤ C := by rw [hCdef]; linarith
  have hCpC : Cp ≤ C := by rw [hCdef]; linarith
  have hCmC : Cm ≤ C := by rw [hCdef]; linarith
  have h1000C : (1000 : ℝ) ≤ C := by rw [hCdef]; linarith
  have h2000C : (2000 : ℝ) ≤ C := by rw [hCdef]; linarith
  change MeasureTheory.Integrable (summandFun ρ f g a b a₁ b₁) IPM ∧
      |∫ p, summandFun ρ f g a b a₁ b₁ p ∂IPM|
        ≤ C * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f) * Work.Spaces.HkSq α 6 g
  have hfin : ∀ (V : ℝ × ℝ → ℝ) (K : ℝ), K ≤ C →
      |∫ p, V p ∂IPM| ≤ K * Work.Spaces.WlInf α 6 f * Work.Spaces.HkSq α 6 g →
      |∫ p, V p ∂IPM|
        ≤ C * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f) * Work.Spaces.HkSq α 6 g :=
    fun V K hK hb => hb.trans (const_mul_le_of_le hK hC0 hMf0 hMth0 hS0)
  have hfin' : ∀ (V : ℝ × ℝ → ℝ) (K : ℝ), K ≤ C →
      |∫ p, V p ∂IPM|
          ≤ K * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f) * Work.Spaces.HkSq α 6 g →
      |∫ p, V p ∂IPM|
        ≤ C * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f) * Work.Spaces.HkSq α 6 g :=
    fun V K hK hb => hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (by linarith)) hS0)
  by_cases hA : a₁ = 0
  · subst hA
    by_cases hb₁0 : b₁ = 0
    · subst hb₁0
      have hV : summandFun ρ f g a b 0 0 = (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2) := by
        funext p
        simp only [summandFun, Nat.sub_zero, Work.Spaces.mixed_zero_right,
          Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
        rfl
      by_cases hab5 : a + b ≤ 5
      · obtain ⟨hint, hbound⟩ := hCf α hα f g a b ρ hsf hfw hsg hg6 hdec hab5 hρ
        exact ⟨by rw [hV, Work.FTS.TransportS.prod_restrict_eq]; exact hint,
          hfin _ Cf hCfC (by rw [hV]; exact hbound)⟩
      · have hab6 : a + b = 6 := by omega
        obtain ⟨hint, hbound⟩ := hCt α hα f g a b ρ hsf hfw hsg hg6 hg7 hdec hab6 hρ
        exact ⟨by rw [hV, Work.FTS.TransportS.prod_restrict_eq]; exact hint,
          hfin _ Ct hCtC (by rw [hV]; exact hbound)⟩
    · have hb1 : 1 ≤ b₁ := Nat.one_le_iff_ne_zero.mpr hb₁0
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |ρ z θ * Work.Spaces.mixed b₁ 0 f z θ
              * Work.Spaces.mixed (b - b₁ + 1) (a - 0) g z θ * Work.Spaces.mixed b a g z θ|
            ≤ 1000 * Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ :=
        fun z θ hz hθ0 hθ1 =>
          summand_zeroAngular_pointwise (α := α) (f := f) (g := g) (a := a) (b := b)
            (b₁ := b₁) (ρ := ρ) hα0 hsf hfw hρ hab hb1 hb₁ z θ hz hθ0 hθ1
      obtain ⟨hint, hbound⟩ := summandFun_aesm_and_bound (a := a) (b := b) (a₁ := 0)
        (b₁ := b₁) (M := 1000 * Work.Spaces.WlInf α 6 f) hsf hsg hρ hg6
        (mul_nonneg (by norm_num) hMf0) hpt
      exact ⟨hint, hfin _ 1000 h1000C hbound⟩
  · have ha1 : 1 ≤ a₁ := Nat.one_le_iff_ne_zero.mpr hA
    by_cases hlt : a₁ < a
    · have ha₁b₁ : a₁ + b₁ ≤ 6 := by omega
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |ρ z θ * Work.Spaces.mixed b₁ a₁ f z θ
              * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ * Work.Spaces.mixed b a g z θ|
            ≤ Cm * Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ :=
        fun z θ hz hθ0 hθ1 => by
          rw [abs_four_leafW (leafW_nonneg hρ ⟨le_of_lt hθ0, le_of_lt hθ1⟩)]
          exact hCm α hα0 hα1 f g a b a₁ b₁ ρ hsf hfw hsg hg6 hab hρ ha1 hlt ha₁b₁ hb₁
            z θ hz hθ0 hθ1
      obtain ⟨hint, hbound⟩ := summandFun_aesm_and_bound (a := a) (b := b) (a₁ := a₁)
        (b₁ := b₁) (M := Cm * Work.Spaces.WlInf α 6 f) hsf hsg hρ hg6
        (mul_nonneg (le_of_lt hCm0) hMf0) hpt
      exact ⟨hint, hfin _ Cm hCmC hbound⟩
    · have ha₁eq : a₁ = a := le_antisymm ha₁ (not_lt.mp hlt)
      have ha : 1 ≤ a := ha₁eq ▸ ha1
      rw [ha₁eq]
      by_cases hab₁ : a + b₁ ≤ 4
      · have hV : summandFun ρ f g a b a b₁ = (fun p : ℝ × ℝ => ρ p.1 p.2
            * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2) := by
          funext p
          simp only [summandFun, Nat.sub_self, Work.Spaces.mixed_zero_right]
        obtain ⟨hint, hbound⟩ := hCc α hα f g a b b₁ ρ hsf hfw hc3 hsg hg6 hab hρ ha hab₁ hb₁
        exact ⟨by rw [hV, Work.FTS.TransportS.prod_restrict_eq]; exact hint,
          hfin' _ Cc hCcC (by rw [hV]; exact hbound)⟩
      · have h5 : 5 ≤ a + b₁ := by omega
        have hρs : Work.FTS.TransportS.IsLeafW α a ρ := hρ
        rcases hρ with hEta | hOne | ⟨_, hGam⟩
        · have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
              |ρ z θ * Work.Spaces.mixed b₁ a f z θ
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a) g z θ
                  * Work.Spaces.mixed b a g z θ|
                ≤ 2000 * Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ :=
            fun z θ hz hθ0 hθ1 => by
              rw [show a - a = 0 from Nat.sub_self a]
              exact summand_pureEta_pointwise (α := α) (f := f) (g := g) (a := a) (b := b)
                (b₁ := b₁) (ρ := ρ) hα0 hα1 hsf hfw (Or.inl hEta) ha hab hb₁ z θ hz hθ0 hθ1
          obtain ⟨hint, hbound⟩ := summandFun_aesm_and_bound (a := a) (b := b) (a₁ := a)
            (b₁ := b₁) (M := 2000 * Work.Spaces.WlInf α 6 f) hsf hsg hρs hg6
            (mul_nonneg (by norm_num) hMf0) hpt
          exact ⟨hint, hfin _ 2000 h2000C hbound⟩
        · have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
              |ρ z θ * Work.Spaces.mixed b₁ a f z θ
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a) g z θ
                  * Work.Spaces.mixed b a g z θ|
                ≤ 2000 * Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ :=
            fun z θ hz hθ0 hθ1 => by
              rw [show a - a = 0 from Nat.sub_self a]
              exact summand_pureEta_pointwise (α := α) (f := f) (g := g) (a := a) (b := b)
                (b₁ := b₁) (ρ := ρ) hα0 hα1 hsf hfw (Or.inr hOne) ha hab hb₁ z θ hz hθ0 hθ1
          obtain ⟨hint, hbound⟩ := summandFun_aesm_and_bound (a := a) (b := b) (a₁ := a)
            (b₁ := b₁) (M := 2000 * Work.Spaces.WlInf α 6 f) hsf hsg hρs hg6
            (mul_nonneg (by norm_num) hMf0) hpt
          exact ⟨hint, hfin _ 2000 h2000C hbound⟩
        · have hbm : b - b₁ + 1 ≤ 2 := by omega
          have hV : summandFun ρ f g a b a b₁ = (fun p : ℝ × ℝ =>
              Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2) := by
            funext p
            rw [hGam]
            simp only [summandFun, Nat.sub_self, Work.Spaces.mixed_zero_right]
          obtain ⟨hint, hbound⟩ := hCp α hα f g a b b₁ hsf hfw hsg hg6 ha hab hb₁ h5 hbm
          exact ⟨by rw [hV, Work.FTS.TransportS.prod_restrict_eq]; exact hint,
            hfin _ Cp hCpC (by rw [hV]; exact hbound)⟩


end
