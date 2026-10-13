import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.L6Flux.flux_prod_le
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.L6Aux2
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.fluxSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix

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
set_option maxHeartbeats 1600000

/-! ## The canonical-weight form of the level-six top flux bound

The target `fluxFamSixTop` is the top family (`a + b = 6`) of the level-six transport
expansion with the three *leaf* weights of `TransportS.IsLeafW` as the weight `ρ`.  Each of
the three leaf weights is literally one of the canonical weights `canonW q = w² sin(2θ)^{-q}`
with `q ∈ {η, 0, γ(α)}`, so the whole statement is the `canonW`-form below, and the reduction
to it is a case split plus the (definitional) identification of the weight.

The `canonW`-form for `a + b = 6` is *not* a purely pointwise statement (the two `g`-slots are
of order `7` and `6`, and only `HkIntegrand α 7` dominates the former, which would give the
wrong right-hand side): the value bound is the honest level-six radial integration by parts of
`SixAux.fluxSix`, which prices the flux by the surviving slot `mixed b a g` of order `6` (the
`HkMem α 7 g` hypothesis is used only for the boundary identity).  That flux bound enters the
lemma below as a *hypothesis* (with an explicit constant `C`), so that the constant produced by
`fluxSix` is the one the main theorem exports.

* the pointwise domination of the *integrand* by `(Mf/2)(HkIntegrand α 7 + HkIntegrand α 6)`
  (`ℋ⁷`-slot for `D_z(mixed b a g)`, `ℋ⁶`-slot for `mixed b a g`, AM–GM) gives the
  `IntegrableOn` conjunct, through `Hon.integrable_HkIntegrand_prod_open` (at order `7`);
* the two slot dominations are `T2Sup.canonW_z_slot_le_gen` (the pure `D_z`-slot, `q ≤ η`) and
  `T2Sup.canonW_mixed_slot_le_gen` (the mixed slots, `q ≤ γ`), both with the *non-strict*
  hypothesis `0 ≤ q`, which is what makes the `q = 0` leaf weight `w²` fall out as well;
* the value bound (stated on the iterated integral) is moved to the product measure by Fubini
  (`MeasureTheory.integral_integral`), the integrability hypothesis being exactly the one
  produced above. -/

/-- **The canonical-weight level-six top flux bound.**  For `0 ≤ q ≤ γ(α)`, `q ≤ η` whenever
the surviving angular index vanishes, and `a + b = 6`, if the iterated-integral flux bound
holds with constant `C`, then the product-measure form holds with the same constant:

`|∫∫ canonW q · f · D_z(D_z^bD_θ^ag) · (D_z^bD_θ^ag)| ≤ C |f|_{𝒲^{6,∞}} |g|²_{ℋ⁶}`,

with the integrand product-integrable on `Iz ×ˢ Iθ`. -/
theorem fluxTop_of_flux {α : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q C : ℝ}
    (hαpos : 0 < α) (hq0 : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α)
    (hqη : a = 0 → q ≤ Work.Spaces.eta) (hab : a + b = 6)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 6 f)
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hm6 : Work.Spaces.HkMem α 6 g)
    (hm7 : Work.Spaces.HkMem α 7 g)
    (hflux : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
      ≤ C * Work.Spaces.WlInf α 6 f * Work.Spaces.HkSq α 6 g) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) ∧
      |∫ p, Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * f p.1 p.2
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * Work.Spaces.WlInf α 6 f * Work.Spaces.HkSq α 6 g := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iz with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hν
  set Mf : ℝ := Work.Spaces.WlInf α 6 f with hMfdef
  have hMfnn : 0 ≤ Mf := by rw [hMfdef]; exact Work.Spaces.WlInf_nonneg α 6 f hfm
  set F : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
      * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2 with hFdef
  have hab6 : a + b ≤ 6 := by omega
  have hdz : ∀ z θ : ℝ, Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
      = Work.Spaces.mixed (b + 1) a g z θ := fun z θ => rfl
  -- ## The two pointwise slot dominations
  have hslotX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 g z θ := by
    intro z θ _ hθ0 hθ2
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have h := Work.FTS.TransportS.T2Sup.canonW_z_slot_le_gen (α := α) (z := z) (θ := θ) 7
        hq0 (hqη rfl) g (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hθ0, hθ2⟩) (b + 1)
        (by omega)
      simpa only [Work.Spaces.mixed_zero_right] using h
    · exact Work.FTS.TransportS.T2Sup.canonW_mixed_slot_le_gen (α := α) (z := z)
        hαpos 7 hq0 hqγ g (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hθ0, hθ2⟩) (b + 1) a
        ha (by omega)
  have hslotY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z θ _ hθ0 hθ2
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have h := Work.FTS.TransportS.T2Sup.canonW_z_slot_le_gen (α := α) (z := z) (θ := θ) 6
        hq0 (hqη rfl) g (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hθ0, hθ2⟩) b
        (by omega)
      simpa only [Work.Spaces.mixed_zero_right] using h
    · exact Work.FTS.TransportS.T2Sup.canonW_mixed_slot_le_gen (α := α) (z := z)
        hαpos 6 hq0 hqγ g (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hθ0, hθ2⟩) b a
        ha (by omega)
  -- ## The pointwise bound on the integrand
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F (z, θ)| ≤ (Mf / 2) * (Work.Spaces.HkIntegrand α 7 g z θ
        + Work.Spaces.HkIntegrand α 6 g z θ) := by
    intro z θ hz hθ0 hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hcw : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
      Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
    have hX := hslotX z θ hz hθ0 hθ2
    have hY := hslotY z θ hz hθ0 hθ2
    have hf : |f z θ| ≤ Mf := by
      have h := Work.Spaces.WlInf_z_bound α 6 f hfm 0 (by norm_num) z θ (le_of_lt hz) hθI
      rw [hMfdef]
      simpa using h
    have hFA : F (z, θ) = Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ := by
      simp only [hFdef, hdz]
    rw [hFA]
    calc |Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
            * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ|
        ≤ |f z θ| * (Work.FTS.TransportS.SlotT2.canonW q z θ
            * |Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|) :=
          abs_four_mul_le_of_le hcw le_rfl
      _ = |f z θ * (Work.FTS.TransportS.SlotT2.canonW q z θ
            * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)| :=
          (abs_mul_canonW_three hcw).symm
      _ ≤ (Mf / 2) * (Work.FTS.TransportS.SlotT2.canonW q z θ
              * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
            + Work.FTS.TransportS.SlotT2.canonW q z θ
              * (Work.Spaces.mixed b a g z θ) ^ 2) :=
          Work.FTS.StrongPersist.N6Trans.SixAux.abs_mul_canonW_mul_le hcw hMfnn hf
      _ ≤ (Mf / 2) * (Work.Spaces.HkIntegrand α 7 g z θ
            + Work.Spaces.HkIntegrand α 6 g z θ) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  -- ## Continuity on the open quadrant
  have hcontF : ContinuousOn F (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Work.FTS.TransportS.SlotT2.continuousOn_canonW q
    have h2 : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := hsf.continuousOn
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hsg (b + 1) a
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a g p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hsg b a
    exact (((h1.mul h2).mul h3).mul h4).congr
      (fun p _ => by simp only [hFdef, Pi.mul_apply])
  -- ## Integrability of the integrand
  have hdomint : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Mf / 2) *
      (Work.Spaces.HkIntegrand α 7 g p.1 p.2 + Work.Spaces.HkIntegrand α 6 g p.1 p.2))
      (μ.prod ν) :=
    (((Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hsg hm7).1.add
      (Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hsg hm6).1).const_mul
        (Mf / 2))
  have haesmF : MeasureTheory.AEStronglyMeasurable F (μ.prod ν) :=
    Work.Spaces.aesm_of_continuousOn_Qd F hcontF
  have hdom : ∀ᵐ p ∂(μ.prod ν), ‖F p‖ ≤ (Mf / 2) * (Work.Spaces.HkIntegrand α 7 g p.1 p.2
      + Work.Spaces.HkIntegrand α 6 g p.1 p.2) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ => ‖F p‖ ≤ (Mf / 2) *
      (Work.Spaces.HkIntegrand α 7 g p.1 p.2 + Work.Spaces.HkIntegrand α 6 g p.1 p.2)) ?_
    intro z θ hz hθ hθ2
    rw [Real.norm_eq_abs]
    exact hpt z θ hz hθ hθ2
  have hFint : MeasureTheory.Integrable F (μ.prod ν) := hdomint.mono' haesmF hdom
  -- ## Fubini: the product-measure integral is the iterated one
  have hFub : (∫ p, F p ∂(μ.prod ν))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ := by
    have h := MeasureTheory.integral_integral (μ := μ) (ν := ν)
      (f := fun z θ => Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
      (show MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q
          p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2) (μ.prod ν) from hFint)
    exact h.symm
  constructor
  · rw [MeasureTheory.IntegrableOn, ← Work.FTS.TransportS.prod_restrict_eq]
    exact hFint
  · rw [hFub]
    simpa only [hMfdef] using hflux

/-- **The top family `a + b = 6` of the level-six transport expansion.**  For every leaf weight
`ρ` of the slot with `a` angular derivatives (`ρ ∈ {w²sin(2θ)^{-η}, w², w²sin(2θ)^{-γ(α)}}`),

```
IntegrableOn (fun p => ρ p.1 p.2 * f p.1 p.2 * D_z(D_z^bD_θ^ag) p.1 p.2 * (D_z^bD_θ^ag) p.1 p.2)
  (Iz ×ˢ Iθ)
∧ |∫∫ ρ · f · D_z(D_z^bD_θ^ag) · (D_z^bD_θ^ag)| ≤ 2 |f|_{𝒲^{6,∞}} |g|²_{ℋ⁶}.
```

Each leaf weight is a canonical weight (`canonW η`, `canonW 0`, `canonW γ(α)`), so the claim is
`fluxTop_of_flux` in the three cases `q = η`, `q = 0`, `q = γ(α)`; the guards
`q ≤ γ(α)` and `a = 0 → q ≤ η` hold in each case (`η ≤ γ(α)`, `0 ≤ η`, and, for the `γ`-weight,
`1 ≤ a` by the definition of `IsLeafW`), and the flux bound is `SixAux.fluxSix`. -/
theorem fluxFamSixTop : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f g : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
    a + b = 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) ∧
        |∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
          ≤ C * Work.Spaces.WlInf α 6 f * Work.Spaces.HkSq α 6 g := by
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FTS.StrongPersist.N6Trans.SixAux.fluxSix
  refine ⟨C6, hC6pos, ?_⟩
  intro α hα f g a b ρ hsf hfm hsg hmg hm7 hdec hab hρ
  obtain ⟨hαpos, hαle⟩ := hα
  have hab6 : a + b ≤ 6 := by omega
  have hηγ : Work.Spaces.eta ≤ Work.Spaces.gam α :=
    Work.FTS.TransportS.T2Sup.eta_le_gam hαpos
  have hfb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |f z θ| ≤ Work.Spaces.WlInf α 6 f := by
    intro z θ hz hθ0 hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have h := Work.Spaces.WlInf_z_bound α 6 f hfm 0 (by norm_num) z θ (le_of_lt hz) hθI
    simpa using h
  have hDfb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dz f z θ| ≤ Work.Spaces.WlInf α 6 f := by
    intro z θ hz hθ0 hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have h := Work.FTS.StrongPersist.N6Trans.zpz_le_WlInf6 hfm (j := 1) (by norm_num)
      (le_of_lt hz) hθI
    simpa only [Work.Spaces.Dz, Work.Spaces.pzIter, pow_one] using h
  rcases hρ with hρ | hρ | ⟨ha1, hρ⟩
  · -- `ρ = leafEta = canonW η`
    subst hρ
    have hq : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafEta p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
        = (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
          * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2) := by
      funext p
      simp only [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.SlotT2.canonW]
    rw [hq]
    exact fluxTop_of_flux (C := C6) (q := Work.Spaces.eta) hαpos Work.Spaces.eta_nonneg hηγ
      (fun _ => le_rfl) hab hsf hfm hsg hmg hm7
      (hC6 α f g a b Work.Spaces.eta (Work.Spaces.WlInf α 6 f) hαpos hαle
        Work.Spaces.eta_nonneg hηγ (fun _ => le_rfl) hab6 hsf hsg hmg hm7 hdec hfb hDfb)
  · -- `ρ = leafOne = canonW 0`
    subst hρ
    have hq : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafOne p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
        = (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW 0 p.1 p.2
          * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2) := by
      funext p
      simp only [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW, neg_zero,
        Real.rpow_zero, mul_one]
    rw [hq]
    exact fluxTop_of_flux (C := C6) (q := 0) hαpos le_rfl (Work.Spaces.gam_pos hαpos).le
      (fun _ => Work.Spaces.eta_nonneg) hab hsf hfm hsg hmg hm7
      (hC6 α f g a b 0 (Work.Spaces.WlInf α 6 f) hαpos hαle le_rfl
        (Work.Spaces.gam_pos hαpos).le (fun _ => Work.Spaces.eta_nonneg) hab6 hsf hsg hmg hm7
        hdec hfb hDfb)
  · -- `ρ = leafGam α = canonW (γ α)`; here `1 ≤ a`, so the `q ≤ η` guard is vacuous
    subst hρ
    exact fluxTop_of_flux (C := C6) (q := Work.Spaces.gam α) hαpos
      (Work.Spaces.gam_pos hαpos).le le_rfl (fun h0 => absurd h0 (Nat.one_le_iff_ne_zero.mp ha1))
      hab hsf hfm hsg hmg hm7
      (hC6 α f g a b (Work.Spaces.gam α) (Work.Spaces.WlInf α 6 f) hαpos hαle
        (Work.Spaces.gam_pos hαpos).le le_rfl
        (fun h0 => absurd h0 (Nat.one_le_iff_ne_zero.mp ha1)) hab6 hsf hsg hmg hm7 hdec hfb hDfb)

end

end Work.FTS.StrongPersist.N6Trans.SixRoute
