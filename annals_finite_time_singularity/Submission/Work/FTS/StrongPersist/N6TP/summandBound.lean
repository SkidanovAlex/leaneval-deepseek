import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSixTop
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.StrongPersist.N6TP.coefThGain
import Submission.Work.FTS.StrongPersist.N6TP.termBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6TP

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/- Per-summand bound of the level-six `D_z`-transport Leibniz expansion with a flat coefficient of order 5.

Context: I am assembling `N6Trans (IP6 1 … 1) α₂ Ct`, whose third clause is T3Clause6: for
`SmoothOpen f`, `WlInfMem α 6 f`, `CoefThMem 5 f`, `HQo α 6 g`, `HkMem α 7 g`, `DecayAll 6 g`,
  `|IP6 1…1 α (fun z θ => f z θ * Dz g z θ) g| ≤ Ct * α^{-1/2} * (WlInf α 6 f + CoefTh 5 f) * Xn6 α g ^ 2`.
`IP6 1…1` unfolds via `ip4_unfold_bound` into leaf slot pairings, so I need the per-slot
`D_z`-transport bound at level six, which I reduce (via `SixRoute.sixExpansion`, the exact Leibniz
expansion `mixed b a (f · D_z g) = Σ_{a₁≤a} Σ_{b₁≤b} C(a,a₁)C(b,b₁) · mixed b₁ a₁ f · mixed (b-b₁+1)(a-a₁) g`)
to this per-summand statement for every Leibniz index `(a₁,b₁)` with `a₁ ≤ a`, `b₁ ≤ b`, `a + b ≤ 6`.

It is true; the pieces are all in the workspace. Hints for the prover (branch on `(a₁,b₁)` and on
`a = 0` vs `1 ≤ a`):
* `(a₁,b₁) = (0,0)`: the integrand is `ρ·f·D_z(mixed b a g)·mixed b a g`; use `fluxFamSix`
  (`a+b ≤ 5`) resp. `fluxFamSixTop` (`a+b = 6`), both in `…N6Trans.SixRoute`, stated as
  `IntegrableOn … (Iz ×ˢ Iθ)` (convert with `Work.FTS.TransportS.prod_restrict_eq`).
* `a₁ = 0`, `b₁ ≥ 1`: `|D_z^{b₁} f| ≤ 1000·WlInf α 6 f` (`L6Core.dzIter_le_WlInf6`, `b₁ ≤ b ≤ 6`);
  then dominate the two `g`-factors by `HkIntegrand α 6 g` either with the weight `canonW eta`
  (when `a = 0`, `T2Sup.canonW_z_slot_le_gen`) or with `canonW (gam α)`
  (`T2Sup.canonW_mixed_slot_le_gen`, `a ≥ 1`), after `|G|·|Y| ≤ (G²+Y²)/2`.
* `1 ≤ a₁ ≤ a`: the σ-gain `Work.FTS.TransportS.flat_mixed_le 5` applied with
  `K := CoefTh 5 f` gives `|mixed b₁ a₁ f| ≤ C·sin(2θ)·CoefTh 5 f` (grades of `CoefTh` by
  `Work.FTS.H2.le_supAbsO`); with `ρ ≤ canonW (gam α)` one has
  `sin(2θ)·ρ ≤ canonW (gam α - 1) = canonW (α/10)`, and `α/10 ≤ eta`, `α/10 ≤ gam α` make both
  `g`-slots compatible with `HkIntegrand α 6 g` (`T2Sup.canonW_z_slot_le_gen` when `a₁ = a`, the
  second factor being the pure slot `D_z^{b-b₁+1} g`; `T2Sup.canonW_mixed_slot_le_gen` when `a₁ < a`),
  again after `|G|·|Y| ≤ (G²+Y²)/2` and `ρ ≤ canonW (gam α)` from `T3SlotAux.IsLeafW.le_canonW`.
* Integrability: `|integrand| ≤ const·HkIntegrand α 6 g` pointwise on the open quadrant and
  `Hon.integrable_HkIntegrand_prod_open` (product-integrability of `HkIntegrand`), plus a.e. strong
  measurability from continuity on the open quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`,
  `Hon.continuousOn_mixed_Qd_open`); the integral bound is then `|∫| ≤ ∫|·| ≤ const·HkSq α 6 g`
  (`HkSq` is the product integral of `HkIntegrand`).
Each `canonW`-slot comparison is stated on the open quadrant (0 < z, 0 < θ < π/2), which is enough
(a null set). -/

/-- **The a.e.-pointwise domination package.**  If `F` is continuous on the open quadrant and
dominated pointwise there by `M · HkIntegrand α 6 g`, then `F` is product-integrable on
`Iz ×ˢ Iθ` (with respect to the product of the two restricted Lebesgue measures) and its
integral is bounded by `M · HkSq α 6 g`.

This is the common bookkeeping step of every non-exceptional Leibniz summand of
`summandBound`: the domination only holds on the open quadrant (`z > 0`), which is conull
inside `Iz ×ˢ Iθ`, and the a.e. strong measurability follows from continuity there. -/
theorem summand_ae_package {α : ℝ} {g : ℝ → ℝ → ℝ} {F : ℝ × ℝ → ℝ} {M : ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α 6 g)
    (hcont : ContinuousOn F (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ‖F (z, θ)‖ ≤ M * Work.Spaces.HkIntegrand α 6 g z θ) :
    MeasureTheory.Integrable F ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, F p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))| ≤ M * Work.Spaces.HkSq α 6 g := by
  obtain ⟨hHint, hHkval⟩ := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (k := 6) hsg hmg
  have haesm : MeasureTheory.AEStronglyMeasurable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd F hcont
  have hdom : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ‖F p‖ ≤ M * Work.Spaces.HkIntegrand α 6 g p.1 p.2 :=
    Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ hθ2 => hpt z θ hz hθ hθ2)
  have hdomint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      M * Work.Spaces.HkIntegrand α 6 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hHint.const_mul M
  have hFint : MeasureTheory.Integrable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hdomint.mono' haesm hdom
  refine ⟨hFint, ?_⟩
  calc |∫ p, F p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ ∫ p, |F p| ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := abs_integral_le_integral_abs
    _ ≤ ∫ p, M * Work.Spaces.HkIntegrand α 6 g p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        refine integral_mono_ae hFint.abs hdomint ?_
        filter_upwards [hdom] with p hp
        simpa only [Real.norm_eq_abs] using hp
    _ = M * Work.Spaces.HkSq α 6 g := by rw [integral_const_mul, hHkval]

theorem summandBound : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f g : ℝ → ℝ → ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.VocabO.CoefThMem 5 f →
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
          ≤ C * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
              * Work.Spaces.HkSq α 6 g := by
  obtain ⟨C1, hC1pos, hflux5⟩ := Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix
  obtain ⟨C2, hC2pos, hflux6⟩ := Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSixTop
  obtain ⟨Cf, hCfpos, hcoef⟩ := Work.FTS.StrongPersist.N6TP.coefThGain
  refine ⟨max (max C1 C2) (max 1000 Cf) + 1, by positivity, ?_⟩
  intro α hα f g a b a₁ b₁ ρ hsf hfm hcfm hsg hmg6 hmg7 hdec hab hρ ha₁ hb₁
  obtain ⟨hαpos, hαle⟩ := hα
  have hαmem : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hαpos, hαle⟩
  set D : ℝ := max (max C1 C2) (max 1000 Cf) with hDdef
  have hC1 : C1 ≤ D := by
    rw [hDdef]; exact le_trans (le_max_left C1 C2) (le_max_left _ _)
  have hC2 : C2 ≤ D := by
    rw [hDdef]; exact le_trans (le_max_right C1 C2) (le_max_left _ _)
  have h1000 : (1000 : ℝ) ≤ D := by
    rw [hDdef]; exact le_trans (le_max_left 1000 Cf) (le_max_right _ _)
  have hCfle : Cf ≤ D := by
    rw [hDdef]; exact le_trans (le_max_right 1000 Cf) (le_max_right _ _)
  have hDnn : 0 ≤ D := by linarith [h1000]
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  have hCnn : 0 ≤ Work.FTS.VocabO.CoefTh 5 f := Work.FTS.TransportS.coefTh_nonneg 5 f
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  have hWl_le : C1 * Work.Spaces.WlInf α 6 f
      ≤ (D + 1) * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f) :=
    mul_le_mul (by linarith) (by linarith) hWnn (by linarith)
  have hWl2_le : C2 * Work.Spaces.WlInf α 6 f
      ≤ (D + 1) * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f) :=
    mul_le_mul (by linarith) (by linarith) hWnn (by linarith)
  have hcoef_le : 1000 * Work.Spaces.WlInf α 6 f + Cf * Work.FTS.VocabO.CoefTh 5 f
      ≤ (D + 1) * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f) := by
    have h1 : 1000 * Work.Spaces.WlInf α 6 f ≤ D * Work.Spaces.WlInf α 6 f :=
      mul_le_mul_of_nonneg_right h1000 hWnn
    have h2 : Cf * Work.FTS.VocabO.CoefTh 5 f ≤ D * Work.FTS.VocabO.CoefTh 5 f :=
      mul_le_mul_of_nonneg_right hCfle hCnn
    nlinarith [h1, h2, hWnn, hCnn, hDnn]
  by_cases h00 : a₁ = 0 ∧ b₁ = 0
  · -- the exceptional summand `(a₁,b₁) = (0,0)`: the radial flux of `g` alone
    obtain ⟨ha0, hb0⟩ := h00
    subst ha0
    subst hb0
    have heq : (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed 0 0 f p.1 p.2
          * Work.Spaces.mixed (b - 0 + 1) (a - 0) g p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2)
        = (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2) := by
      funext p
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero, Nat.sub_zero]
      rfl
    rw [heq]
    rcases lt_or_eq_of_le hab with h5 | h6
    · have h5' : a + b ≤ 5 := by omega
      have h := hflux5 α hαmem f g a b ρ hsf hfm hsg hmg6 hdec h5' hρ
      rw [MeasureTheory.IntegrableOn, ← Work.FTS.TransportS.prod_restrict_eq] at h
      refine ⟨h.1, ?_⟩
      refine h.2.trans ?_
      have := mul_le_mul_of_nonneg_right hWl_le hSnn
      linarith [this]
    · have h6' : a + b = 6 := by omega
      have h := hflux6 α hαmem f g a b ρ hsf hfm hsg hmg6 hmg7 hdec h6' hρ
      rw [MeasureTheory.IntegrableOn, ← Work.FTS.TransportS.prod_restrict_eq] at h
      refine ⟨h.1, ?_⟩
      refine h.2.trans ?_
      have := mul_le_mul_of_nonneg_right hWl2_le hSnn
      linarith [this]
  · -- every other Leibniz summand: pointwise AM–GM against the `ℋ⁶`-slots of `g`
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |ρ z θ * Work.Spaces.mixed b₁ a₁ f z θ
            * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ
            * Work.Spaces.mixed b a g z θ|
        ≤ (1000 * Work.Spaces.WlInf α 6 f + Cf * Work.FTS.VocabO.CoefTh 5 f)
            * Work.Spaces.HkIntegrand α 6 g z θ := by
      intro z θ hz hθ0 hθ2
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ2.le⟩
      have hρnn : 0 ≤ ρ z θ := Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hρ z hθI
      have h := Work.FTS.StrongPersist.N6TP.termBound α Cf hαpos hαle hCfpos.le f g a b a₁ b₁ ρ
        hsf hfm hab hρ ha₁ hb₁ h00 (hcoef f hsf hcfm) z θ hz hθ0 hθ2
      rw [abs_mul] at h
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
      ring_nf at h ⊢
      linarith [h]
    have hρcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      rcases hρ with rfl | rfl | ⟨_, rfl⟩
      · exact Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta
      · refine (Work.FTS.TransportS.SlotT2.continuousOn_canonW 0).congr ?_
        intro p _
        simp [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW]
      · exact Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ f p.1 p.2
        * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (((hρcont.mul
        (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hsf b₁ a₁)).mul
        (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hsg (b - b₁ + 1)
          (a - a₁))).mul
        (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hsg b a))
    obtain ⟨hint, hbound⟩ := summand_ae_package (α := α) (g := g)
      (F := fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
        * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
      (M := 1000 * Work.Spaces.WlInf α 6 f + Cf * Work.FTS.VocabO.CoefTh 5 f)
      hsg hmg6 hcont (fun z θ hz hθ0 hθ2 => by
        rw [Real.norm_eq_abs]; exact hpt z θ hz hθ0 hθ2)
    refine ⟨hint, ?_⟩
    refine hbound.trans ?_
    have := mul_le_mul_of_nonneg_right hcoef_le hSnn
    linarith [this]

end

end Work.FTS.StrongPersist.N6TP
