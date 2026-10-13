/-
# `RowDthW/PerTerm/perTermWlInf` — a Leibniz-remainder summand of the `D_θ`-row with a
`𝒲^{6,∞}`-priced coefficient

Every summand of the Leibniz expansion of `mixed b a (A · D_θ f)` other than the transport term
`A · D_θ(mixed b a f)` has the shape

`∫_z ∫_θ ρ · (D_z^j D_θ^i A) · (D_z^{b-j} D_θ^{a-i+1} f) · (D_z^b D_θ^a f)`

with `i ≤ a`, `j ≤ b`, `¬(i = 0 ∧ j = 0)`.  Both `f`-slots are *mixed* slots of order `≤ 6`
(`a - i + 1 ≥ 1` always, and `(b-j) + (a-i+1) ≤ 6` because `i + j ≥ 1`), so their weighted
squares are dominated by `HkIntegrand α 6 f` on the open quadrant.  The coefficient slot is
priced pointwise by `2000 K` (`WlInf α 6 A ≤ K` via the `C⁶` pointwise bounds
`Cd6.mixed_le_WlInf6_cd6` / `Cd6.dzIter_le_WlInf6_cd6`), and AM–GM turns the product of the
three slots into `(4000 K) · HkIntegrand α 6 f`.  Integrating over the quadrant gives
`4000 K · HkSq α 6 f ≤ 4000 (1+K)(1 + HkSq α 6 f)`.

The measure-theoretic bookkeeping (the two `IntegrableOn` conjuncts, with the `z = 0` slice
handled by the vanishing of the weight) is done by a local copy of `integrableConjunctsAux`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixed_le_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_le_WlInf6_cd6
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW.PerTerm

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_mono canonW_zero_z)

/-! ## Measure-theoretic bookkeeping on `Iθ` and `Iz` -/

private theorem restrict_Iθ_eq_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
      (b := Real.pi / 2))).symm

private theorem restrict_Iz_eq_Ioi :
    MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  have h : Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Set.Ici (0 : ℝ) :=
    MeasureTheory.Ioi_ae_eq_Ici
  simpa [Work.Spaces.Iz] using (MeasureTheory.Measure.restrict_congr_set h).symm

private theorem integral_Iθ_mono_ae {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ ≤ g θ)
    (h0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ f θ)
    (hg : MeasureTheory.IntegrableOn g Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ) ≤ ∫ θ in Work.Spaces.Iθ, g θ := by
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
  · rw [restrict_Iθ_eq_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h0
  · rw [restrict_Iθ_eq_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

private theorem integral_Iz_mono_ae {f g : ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), f z ≤ g z)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ f z)
    (hg : MeasureTheory.IntegrableOn g Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, g z := by
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
  · rw [restrict_Iz_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h0
  · rw [restrict_Iz_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h

/-- If `F` is continuous on the open quadrant, vanishes at `z = 0`, and is dominated on the
open quadrant by `H` whose angular slices and marginal are integrable, then the angular slices
and the marginal of `F` are integrable. -/
private theorem integrableConjuncts {F H : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hH : MeasureTheory.AEStronglyMeasurable (Function.uncurry H)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hzero : ∀ θ : ℝ, F 0 θ = 0)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => H z θ) Work.Spaces.Iθ)
    (hmarg : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, H z θ) Work.Spaces.Iz)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |F z θ| ≤ H z θ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz := by
  have hslF : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      rw [show (fun θ : ℝ => F 0 θ) = fun _ => (0 : ℝ) from funext fun θ => hzero θ]
      exact integrableOn_zero
    · refine Integrable.mono' (hsl z hz)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hF hzpos) ?_
      rw [restrict_Iθ_eq_Ioo]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs]
      exact hpt z θ hzpos hθ.1 hθ.2
  refine ⟨hslF, ?_⟩
  refine Integrable.mono' hmarg
    (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd _ hF)) ?_
  rw [restrict_Iz_eq_Ioi]
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  rw [Real.norm_eq_abs]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  refine integral_mono_ae ((hslF z (Set.mem_Ici.mpr hz.le)).abs)
    (hsl z (Set.mem_Ici.mpr hz.le)) ?_
  rw [restrict_Iθ_eq_Ioo]
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  exact hpt z θ hz hθ.1 hθ.2

/-! ## Continuity of the canonical weight on the open quadrant -/

private theorem continuousOn_canonW (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
    have h2 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
    have h0 : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)), p.1 ^ 2 ≠ 0 :=
      fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)
    have h3 := ContinuousOn.div₀ (f := fun p : ℝ × ℝ => (1 + p.1) ^ 2)
      (g := fun p : ℝ × ℝ => p.1 ^ 2)
      (s := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) h1 h2 h0
    simpa only [Work.Spaces.w] using h3
  have hs : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
  have hspos : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      0 < Real.sin (2 * p.2) :=
    fun p hp => Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  have hs' := ContinuousOn.rpow_const (f := fun p : ℝ × ℝ => Real.sin (2 * p.2)) (p := -q) hs
    (fun p hp => Or.inl (ne_of_gt (hspos p hp)))
  have hmain : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * Real.sin (2 * p.2) ^ (-q))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hw.pow 2).mul hs'
  simpa only [canonW] using hmain

/-! ## Pointwise bounds for the leaf weights -/

/-- `leafOne = w²` is dominated by the canonical `η`-weight on the open quadrant. -/
private theorem leafOne_le_canonW_eta {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.TransportS.leafOne z θ ≤ canonW Work.Spaces.eta z θ := by
  have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
  calc Work.FTS.TransportS.leafOne z θ = (Work.Spaces.w z) ^ 2 * 1 := by
        simp only [Work.FTS.TransportS.leafOne, mul_one]
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = canonW Work.Spaces.eta z θ := rfl

/-- For `α > 0` one has `η ≤ γ`. -/
private theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have := Work.Spaces.eta_lt_one
  linarith

/-! ## The lemma -/

theorem perTermWlInf : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K M : ℝ) (a b i j : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ → i ≤ a → j ≤ b →
      ¬(i = 0 ∧ j = 0) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ C * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by
  refine ⟨4000, by norm_num, ?_⟩
  intro α hαmem A f K M a b i j ρ hsmA hWmem hWK hdat hab hleaf hia hjb hne
  obtain ⟨hα, hα1⟩ := hαmem
  -- ## basic facts
  have hA6 : ContDiffOn ℝ 6 (Function.uncurry A) Work.FTS.EllipticEst.Q0 := hsmA.forall 6
  have hsmf : Work.FTS.EllipticEst.SmoothOpen f := hdat.sm
  have hf6 : Work.Spaces.HkMem α 6 f := hdat.h6
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 A := Work.Spaces.WlInf_nonneg α 6 A hWmem
  have hK0 : 0 ≤ K := le_trans hWnn hWK
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- ## the pointwise bound of the coefficient slot `mixed j i A`
  have hXle : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |Work.Spaces.mixed j i A z θ| ≤ 2000 * K := by
    intro z θ hz hθ
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])).le
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [Work.Spaces.mixed_zero_right]
      have hj6 : j ≤ 6 := by omega
      have h1 := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_le_WlInf6_cd6
        (α := α) (f := A) hA6 hWmem hj6 hz hθ
      have h2 : (1000 : ℝ) * Work.Spaces.WlInf α 6 A ≤ 2000 * K := by linarith
      linarith
    · have hi1 : 1 ≤ i := hipos
      have hij : i + j ≤ 6 := by omega
      have h1 := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixed_le_WlInf6_cd6
        (α := α) hα hA6 hWmem hi1 hij hz hθ
      have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hrpow1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
        Real.rpow_le_one hsin0 hσ1 (by linarith)
      have hrpow0 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hsin0 _
      have hfac : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
        have h1' : α + Real.sin (2 * θ) ≤ 2 := by linarith
        nlinarith
      have h2 : Work.Spaces.WlInf α 6 A
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ≤ K * 2 :=
        mul_le_mul hWK hfac (mul_nonneg (by linarith) hrpow0) hK0
      linarith [hrpow1]
  -- ## the main argument, for a generic canonical exponent `q`
  have key : ∀ (q : ℝ), 0 < q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      (∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → ρ z θ ≤ canonW q z θ) →
      (∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ) →
      ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      (∀ θ : ℝ, ρ 0 θ = 0) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ 4000 * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by
    intro q hq0 hqγ hqη hρle hρnonneg hρcont hρzero
    -- the two `f`-slot bounds
    have hYle : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
        canonW q z θ * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      intro z θ _ hθ
      exact Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_mixed_le6 α f hq0 hqγ
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ (b - j) (a - i + 1) (by omega) (by omega)
    have hZle : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
        canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      intro z θ _ hθ
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        rw [Work.Spaces.mixed_zero_right]
        exact Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_z_le6 α f hq0 (hqη rfl)
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ b (by omega)
      · exact Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_mixed_le6 α f hq0 hqγ
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ b a (by omega) (by omega)
    -- the pointwise bound of the integrand
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |ρ z θ * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
            * Work.Spaces.mixed b a f z θ|
          ≤ (4000 * K) * Work.Spaces.HkIntegrand α 6 f z θ := by
      intro z θ hz hθ0 hθ2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ2⟩
      have hρnn : 0 ≤ ρ z θ :=
        hρnonneg z θ ⟨le_of_lt hθ0, le_of_lt hθ2⟩
      have hY2 : ρ z θ * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        le_trans (mul_le_mul_of_nonneg_right (hρle z θ hz hθ) (sq_nonneg _))
          (hYle z θ hz hθ)
      have hZ2 : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        le_trans (mul_le_mul_of_nonneg_right (hρle z θ hz hθ) (sq_nonneg _))
          (hZle z θ hz hθ)
      have hX := hXle z θ hz hθ
      have hamgm : ρ z θ * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ|
          ≤ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
        have h := two_mul_le_add_sq |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
          |Work.Spaces.mixed b a f z θ|
        rw [sq_abs, sq_abs] at h
        nlinarith [h, hρnn, hY2, hZ2]
      calc |ρ z θ * Work.Spaces.mixed j i A z θ
              * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
              * Work.Spaces.mixed b a f z θ|
          = |Work.Spaces.mixed j i A z θ| * (ρ z θ
              * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]; ring
        _ ≤ (2000 * K) * (2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
            mul_le_mul hX hamgm
              (mul_nonneg (mul_nonneg hρnn (abs_nonneg _)) (abs_nonneg _))
              (by linarith)
        _ = (4000 * K) * Work.Spaces.HkIntegrand α 6 f z θ := by ring
    -- the integrability conjuncts
    have hcontF : ContinuousOn (Function.uncurry (fun z θ => ρ z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (((hρcont.mul (hsmA.mixed j i).continuousOn).mul
        (hsmf.mixed (b - j) (a - i + 1)).continuousOn).mul
          (hsmf.mixed b a).continuousOn)
    have hHcont : ContinuousOn (fun p : ℝ × ℝ =>
        (4000 * K) * Work.Spaces.HkIntegrand α 6 f p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      continuousOn_const.mul (hsmf.continuousOn_HkIntegrand α 6)
    have hzero : ∀ θ : ℝ, ρ 0 θ * Work.Spaces.mixed j i A 0 θ
        * Work.Spaces.mixed (b - j) (a - i + 1) f 0 θ
        * Work.Spaces.mixed b a f 0 θ = 0 := by
      intro θ
      rw [hρzero θ]; ring
    have hslH : ∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ : ℝ =>
          (4000 * K) * Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iθ :=
      fun z hz => (hf6.1 z hz).const_mul (4000 * K)
    have hmargH : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (4000 * K) * Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iz := by
      rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (4000 * K) * Work.Spaces.HkIntegrand α 6 f z θ)
          = fun z : ℝ => (4000 * K) * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 6 f z θ from by
        funext z
        rw [MeasureTheory.integral_const_mul]]
      exact hf6.2.const_mul (4000 * K)
    obtain ⟨h1, h2⟩ := integrableConjuncts (F := fun z θ => ρ z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ)
      (H := fun z θ => (4000 * K) * Work.Spaces.HkIntegrand α 6 f z θ)
      hcontF (Work.Spaces.aesm_of_continuousOn_Qd _ hHcont) hzero hslH hmargH hpt
    refine ⟨h1, h2, ?_⟩
    calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
            * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
            * Work.Spaces.mixed b a f z θ|
        ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
            * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
            * Work.Spaces.mixed b a f z θ| := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (4000 * K) * Work.Spaces.HkIntegrand α 6 f z θ := by
          refine integral_Iz_mono_ae (fun z hz => ?_) (fun z _ => abs_nonneg _) hmargH
          refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
          exact integral_Iθ_mono_ae (fun θ hθ => hpt z θ (Set.mem_Ioi.mp hz) hθ.1 hθ.2)
            (fun θ _ => abs_nonneg _) (hslH z (Set.mem_Ici.mpr (Set.mem_Ioi.mp hz).le))
      _ = (4000 * K) * Work.Spaces.HkSq α 6 f := by
          simp only [Work.Spaces.HkSq, MeasureTheory.integral_const_mul]
      _ ≤ 4000 * (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by
          have h1 : K * Work.Spaces.HkSq α 6 f
              ≤ (1 + K) * (1 + Work.Spaces.HkSq α 6 f) := by nlinarith [hK0, hSq0]
          nlinarith [h1]
  -- ## the three leaf cases
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · subst hρ
    exact key Work.Spaces.eta Work.Spaces.eta_pos (eta_le_gam hα) (fun _ => le_rfl)
      (fun z θ _ hθ => le_of_eq rfl)
      (fun z θ hθ => Work.FTS.TransportS.leafEta_nonneg
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
          by linarith [hθ.2, Real.pi_pos]⟩))
      (by simpa only [Work.FTS.TransportS.leafEta, canonW] using
        continuousOn_canonW Work.Spaces.eta)
      (fun θ => canonW_zero_z Work.Spaces.eta θ)
  · subst hρ
    exact key Work.Spaces.eta Work.Spaces.eta_pos (eta_le_gam hα) (fun _ => le_rfl)
      (fun z θ _ hθ => leafOne_le_canonW_eta hθ)
      (fun z θ _ => Work.FTS.TransportS.leafOne_nonneg z θ)
      (by simpa only [Work.FTS.TransportS.leafOne, canonW, neg_zero, Real.rpow_zero, mul_one]
        using continuousOn_canonW (0 : ℝ))
      (fun θ => by simp [Work.FTS.TransportS.leafOne, Work.Spaces.w])
  · subst hρ
    exact key (Work.Spaces.gam α) (Work.Spaces.gam_pos hα) le_rfl
      (fun h0 => absurd h0 (by omega))
      (fun z θ _ _ => le_of_eq rfl)
      (fun z θ hθ => Work.FTS.TransportS.leafGam_nonneg α
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
          by linarith [hθ.2, Real.pi_pos]⟩))
      (by simpa only [Work.FTS.TransportS.leafGam, canonW] using
        continuousOn_canonW (Work.Spaces.gam α))
      (fun θ => canonW_zero_z (Work.Spaces.gam α) θ)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW.PerTerm
