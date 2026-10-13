import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.H2.OpenPort.coefTh3_mixed_gain
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.integrable_prod_ae

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

/-! ## The weight algebra of the `γ`-slot

A leaf weight `ρ` of the slot with `a ≥ 1` angular derivatives is dominated by the canonical
weight `canonW γ = w² sin(2θ)^{-γ}` (`IsLeafW.le_canonW` and `qOf α a = γ` for `a ≠ 0`), and
the `sin(2θ)`-gain of `CoefTh 3 f` (`H2.OpenPort.coefTh3_mixed_gain`) converts one factor
`sin(2θ)` into the shift `γ ↦ γ - 1 = α/10` of the exponent.  The next lemma is that shift. -/

/-- **The weight shift of the `γ`-slot**: on the open angular interval,
`canonW γ · sin(2θ) = canonW (γ - 1)`. -/
theorem canonW_gam_mul_sin (α z θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ * Real.sin (2 * θ)
      = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (show (0 : ℝ) < 2 * θ by linarith [hθ.1])
      (show 2 * θ < Real.pi by linarith [hθ.2, Real.pi_pos])
  rw [Work.FTS.TransportS.SlotT2.canonW, Work.FTS.TransportS.SlotT2.canonW]
  have h1 : Real.sin (2 * θ) ^ (-(Work.Spaces.gam α - 1))
      = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α) + 1) := by
    congr 1; ring
  rw [h1, Real.rpow_add hs, Real.rpow_one]
  ring

/-- The open interval `(0,π/2)` is co-null in `Iθ`: `volume.restrict (0,π/2) = volume.restrict Iθ`. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- The open half-line `(0,∞)` is co-null in `Iz`: `volume.restrict (0,∞) = volume.restrict Iz`. -/
theorem restrict_Ioi_eq_restrict_Iz :
    MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iz]; exact MeasureTheory.Ioi_ae_eq_Ici)

/-- **The `a₁ = a`, `a + b₁ ≤ 4` family of the level-six `D_z`-transport pairing.**

All angular derivatives `D_θ^a` (`a ≥ 1`) of the coefficient `f` sit on the *single* factor
`D_z^{b₁}D_θ^a f`, whose total order is `a + b₁ ≤ 4`, so `H2.OpenPort.coefTh3_mixed_gain`
gives the pointwise gain `|D_z^{b₁}D_θ^a f| ≤ Cg · sin(2θ) · CoefTh 3 f`.  With the leaf weight
`ρ` of the slot (`IsLeafW α a ρ`, `a ≥ 1`) this yields the pointwise domination

  `|ρ · D_z^{b₁}D_θ^a f · D_z^{b-b₁+1} g · D_z^bD_θ^a g| ≤ Cg · CoefTh 3 f · HkIntegrand α 6 g`

on the open quadrant: the weight identity `canonW_gam_mul_sin` converts `ρ ≤ canonW γ` and the
extra `sin(2θ)` into `canonW (γ-1)`, and `L6Core.canonW_pair_le6` (the two-factor `ℋ⁶` AM–GM,
with the slots `D_z^{b-b₁+1} g` of order `≤ 6` and `D_z^bD_θ^a g` of order `a + b ≤ 6`) absorbs
the two `g`-factors into `HkIntegrand`.  The factor is `γ - 1 = α/10 ≤ η, γ`, which is what makes
the canonical weight compatible with *both* slots. -/
theorem coefFamSix : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f g : ℝ → ℝ → ℝ) (a b b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.VocabO.CoefThMem 3 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ → 1 ≤ a → a + b₁ ≤ 4 → b₁ ≤ b →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2)
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) ∧
        |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a f p.1 p.2
              * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
          ≤ C * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
              * Work.Spaces.HkSq α 6 g := by
  obtain ⟨Cg, hCgpos, hCgmix⟩ := Work.FTS.H2.OpenPort.coefTh3_mixed_gain
  refine ⟨Cg + 1, by linarith, ?_⟩
  intro α hα f g a b b₁ ρ hsf hfmem hcf hsg hgmem hab hleaf ha hab₁ hb₁
  have hα0 : 0 < α := hα.1
  have hCg0 : 0 ≤ Cg := le_of_lt hCgpos
  have hCth : 0 ≤ Work.FTS.VocabO.CoefTh 3 f := Work.FTS.TransportS.coefTh_nonneg 3 f
  have hMfnn : 0 ≤ Cg * Work.FTS.VocabO.CoefTh 3 f := mul_nonneg hCg0 hCth
  have hqpos : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
  have hqeta : Work.Spaces.gam α - 1 ≤ Work.Spaces.eta := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith [hα.2]
  have hqgam : Work.Spaces.gam α - 1 ≤ Work.Spaces.gam α := by linarith
  -- ## the pointwise bound on the open quadrant
  have hpt : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |ρ z θ * Work.Spaces.mixed b₁ a f z θ * Work.Spaces.DzIter (b - b₁ + 1) g z θ
          * Work.Spaces.mixed b a g z θ|
        ≤ (Cg * Work.FTS.VocabO.CoefTh 3 f) * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z θ hz hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hzI : z ∈ Work.Spaces.Iz := hz.le
    have hρnn : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz hθ.1 hθ.2
    -- the coefficient factor: `ρ · |D_z^{b₁}D_θ^a f| ≤ Cg·CoefTh · canonW (γ-1)`
    have hC1 : ρ z θ * |Work.Spaces.mixed b₁ a f z θ|
        ≤ (Cg * Work.FTS.VocabO.CoefTh 3 f)
          * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := by
      have hρle : ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
        have h := Work.FTS.TransportS.T3SlotAux.IsLeafW.le_canonW hα0 hleaf hz hθ
        rwa [Work.FTS.TransportS.T3SlotAux.qOf_of_ne (Nat.one_le_iff_ne_zero.mp ha)] at h
      have hmx : |Work.Spaces.mixed b₁ a f z θ|
          ≤ Cg * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f :=
        hCgmix f hsf hcf a b₁ ha hab₁ z θ hz hθ.1 hθ.2
      have hcnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ :=
        Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
      calc ρ z θ * |Work.Spaces.mixed b₁ a f z θ|
          ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
              * (Cg * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f) :=
            mul_le_mul hρle hmx (abs_nonneg _) hcnn
        _ = (Cg * Work.FTS.VocabO.CoefTh 3 f)
              * (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
                * Real.sin (2 * θ)) := by ring
        _ = (Cg * Work.FTS.VocabO.CoefTh 3 f)
              * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := by
            rw [canonW_gam_mul_sin α z θ hθ]
    -- the two `g`-factors: `canonW (γ-1) · |D_z^{b-b₁+1}g| · |D_z^bD_θ^a g| ≤ HkIntegrand`
    have hC2 : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ
        * |Work.Spaces.DzIter (b - b₁ + 1) g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
      have h := Work.FTS.StrongPersist.N6Trans.canonW_pair_le6 (α := α) (g := g)
        (q := Work.Spaces.gam α - 1) hqpos hqgam
        (j := b - b₁ + 1) (i := 0) (b := b) (a := a)
        (fun _ => hqeta) (fun h0 => absurd h0 (Nat.one_le_iff_ne_zero.mp ha))
        (by omega) hab hzI hθI
      simpa only [Work.Spaces.mixed_zero_right, Nat.zero_add] using h
    have habsρ : |ρ z θ * Work.Spaces.mixed b₁ a f z θ|
        = ρ z θ * |Work.Spaces.mixed b₁ a f z θ| := by
      rw [abs_mul, abs_of_nonneg hρnn]
    calc |ρ z θ * Work.Spaces.mixed b₁ a f z θ * Work.Spaces.DzIter (b - b₁ + 1) g z θ
            * Work.Spaces.mixed b a g z θ|
        = |ρ z θ * Work.Spaces.mixed b₁ a f z θ| * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ| := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ ((Cg * Work.FTS.VocabO.CoefTh 3 f)
              * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ)
            * |Work.Spaces.DzIter (b - b₁ + 1) g z θ| * |Work.Spaces.mixed b a g z θ| := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) (abs_nonneg _)
          rw [habsρ]; exact hC1
      _ = (Cg * Work.FTS.VocabO.CoefTh 3 f)
            * (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ
              * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by ring
      _ ≤ (Cg * Work.FTS.VocabO.CoefTh 3 f) * Work.Spaces.HkIntegrand α 6 g z θ :=
          mul_le_mul_of_nonneg_left hC2 hMfnn
  -- ## the product measure is the planar measure restricted to the open quadrant
  have hquad : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)).symm
  have hmeas : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hquad]
  -- ## integrability of the dominating function `Cg·CoefTh · HkIntegrand α 6 g`
  have hKint : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α 6 g z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.integrable_prod_ae
      (Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
      (Work.Spaces.aesm_of_continuousOn_Qd _ (hsg.continuousOn_HkIntegrand α 6))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hgmem.1 z hz)
      hgmem.2
  have hmaj : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => (Cg * Work.FTS.VocabO.CoefTh 3 f)
        * Work.Spaces.HkIntegrand α 6 g z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hKint.const_mul (Cg * Work.FTS.VocabO.CoefTh 3 f)
  -- ## a.e. strong measurability of the integrand (the leaf weights are canonical weights)
  have hFaesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => ρ z θ * Work.Spaces.mixed b₁ a f z θ
        * Work.Spaces.DzIter (b - b₁ + 1) g z θ * Work.Spaces.mixed b a g z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      rcases hleaf with h1 | h1 | ⟨h1, h2⟩
      · rw [h1]; exact Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta
      · rw [h1]
        have heq : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafOne p.1 p.2)
            = fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW 0 p.1 p.2 := by
          funext p
          simp [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW]
        rw [heq]
        exact Work.FTS.TransportS.SlotT2.continuousOn_canonW 0
      · rw [h2]; exact Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)
    exact ((hρc.mul (hsf.mixed b₁ a).continuousOn).mul
      (hsg.mixed (b - b₁ + 1) 0).continuousOn).mul (hsg.mixed b a).continuousOn
  -- ## integrability of the integrand, by a.e. domination
  have hFint : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => ρ z θ * Work.Spaces.mixed b₁ a f z θ
        * Work.Spaces.DzIter (b - b₁ + 1) g z θ * Work.Spaces.mixed b a g z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.Integrable.mono' hmaj hFaesm ?_
    rw [hmeas]
    refine MeasureTheory.ae_restrict_of_forall_mem
      ((isOpen_Ioi.prod isOpen_Ioo).measurableSet) (fun p hp => ?_)
    simp only [Real.norm_eq_abs]
    exact hpt p.1 p.2 hp.1 hp.2
  -- ## the angular slice bound (`z > 0`, i.e. a.e. in `z`)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b₁ a f z θ
          * Work.Spaces.DzIter (b - b₁ + 1) g z θ * Work.Spaces.mixed b a g z θ|
        ≤ (Cg * Work.FTS.VocabO.CoefTh 3 f)
          * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
    rw [← restrict_Ioi_eq_restrict_Iz]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz0 => ?_)
    have hz : z ∈ Work.Spaces.Iz := by
      simp only [Work.Spaces.Iz, Set.mem_Ici]; exact hz0.le
    calc |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b₁ a f z θ
          * Work.Spaces.DzIter (b - b₁ + 1) g z θ * Work.Spaces.mixed b a g z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, (Cg * Work.FTS.VocabO.CoefTh 3 f)
            * Work.Spaces.HkIntegrand α 6 g z θ := by
          rw [← Real.norm_eq_abs]
          refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => norm_nonneg _)
            ((hgmem.1 z hz).const_mul _) ?_
          rw [← restrict_Ioo_eq_restrict_Iθ]
          refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
          simp only [Real.norm_eq_abs]
          exact hpt z θ hz0 hθ
      _ = (Cg * Work.FTS.VocabO.CoefTh 3 f)
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
          rw [MeasureTheory.integral_const_mul]
  refine ⟨?_, ?_⟩
  · -- ## the integrability clause
    show MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b₁ a f p.1 p.2
        * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    have hvol : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
        = MeasureTheory.volume.prod MeasureTheory.volume := rfl
    rw [hvol, ← MeasureTheory.Measure.prod_restrict
      (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      Work.Spaces.Iz Work.Spaces.Iθ]
    exact hFint
  · -- ## the integral bound: Fubini, then the slice bound in `θ` and in `z`
    rw [(MeasureTheory.integral_integral hFint).symm]
    calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b₁ a f z θ
            * Work.Spaces.DzIter (b - b₁ + 1) g z θ * Work.Spaces.mixed b a g z θ|
        ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b₁ a f z θ
            * Work.Spaces.DzIter (b - b₁ + 1) g z θ * Work.Spaces.mixed b a g z θ| := by
          rw [← Real.norm_eq_abs]
          exact MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ z in Work.Spaces.Iz, (Cg * Work.FTS.VocabO.CoefTh 3 f)
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
          exact MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => abs_nonneg _)
            (hgmem.2.const_mul _) hslice
      _ = (Cg * Work.FTS.VocabO.CoefTh 3 f) * Work.Spaces.HkSq α 6 g := by
          rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
      _ ≤ (Cg + 1) * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
            * Work.Spaces.HkSq α 6 g := by
          have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfmem
          have hH : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
          refine mul_le_mul_of_nonneg_right ?_ hH
          have ha1 : Cg * Work.FTS.VocabO.CoefTh 3 f
              ≤ Cg * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hW) hCg0
          have ha2 : Cg * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
              ≤ (Cg + 1) * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f) :=
            mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hW hCth)
          linarith

end Work.FTS.StrongPersist.N6Trans.SixRoute
