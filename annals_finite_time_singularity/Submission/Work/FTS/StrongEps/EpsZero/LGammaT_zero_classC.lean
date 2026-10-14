import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_LocDatum3a.Basic
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L₁₂` zero-mode identity of `𝓛_Γ^T` on the class `C`

The paper's `L₁₂(𝓛_Γ^T f)(0) = -L₁₂(f)(0)` for a profile `f` which is `ClassC α` (open-quadrant
`C^∞`, `ℋ⁷`-honesty, the `BdryTraces` vanishing, the axis condition and `L₁₂(f)(0) = 0`) and
vanishes off the open quadrant — the class of the projected, mollified slices of the
`ε`-scheme (`Submission/Work/FTS/StrongEps/EpsZero/NOTES.md`).

## Route

`𝓛_Γ^T = 𝓛_Γ - 𝕡 ∘ Transport` definitionally, so the claim splits into

* `L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)`: the paper's computation, on disk as
  `Work.FTS.Apriori.ZeroMode.L12_LGamma_zero`, whose hypothesis bundle `L12Hyp` (the pointwise
  slice data, the joint integrability of `K·∂_z f`, and the two density integrabilities) is
  produced from `ClassC α f + hzero` by the bridge lemmas of `EpsZero/Bridge/`:
  `BdryClassC`, `pz_prod_integrable_of_smoothOpen`, `HintL`, `L12densLGamma` and `LGammaSlice`
  (the last two via `Work.FTS.GalBasis.cc` and `Work.Coercivity.CommutZ`);
* `L₁₂(𝕡 (Transport f))(0) = 0`: `Work.Coercivity.Proj_L12f_zero`, its integrability inputs being
  `Transport_L12_integrable` (for `Transport f`) and the bridge `ProjTransport` (for its
  projection).

The two are combined by the linearity `Work.FTS.FinalClock.L12LinearSub`; on the negative
half-line the two densities take the explicit elementary forms recorded in the proof (this is
what supplies that lemma's `∀ s`-slice hypotheses).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero

set_option maxHeartbeats 800000

theorem LGammaT_zero_classC {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : Work.FTS.Galerkin.Fn}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0) :
    Work.Construction.L12 (Work.Coercivity.LGammaT α f) 0 = - Work.Construction.L12 f 0 := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ### the `ClassC`-data at levels `4` and `1`
  have h4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.IPGen.HkMem_mono_le hC.reg 4 (by norm_num) hC.mem
  have h1 : Work.Spaces.HkMem α 1 f :=
    Work.FTS.IPGen.HkMem_mono_le hC.reg 1 (by norm_num) hC.mem
  -- ### the pointwise data of the `L₁₂` zero-mode identity
  have hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 := fun θ _ => hzero 0 θ (by simp)
  obtain ⟨hcont, hdec, hdiff⟩ :=
    Work.FTS.StrongEps.EpsZero.Bridge.BdryClassC hC hzero
  -- ### the joint integrability of `K·∂_z f`
  have hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.StrongEps.EpsZero.pz_prod_integrable_of_smoothOpen hC.reg h1
  -- ### `L12dens f ∈ L¹`
  have hintL2 : MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi 0) :=
    Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hC.reg h4
  -- ### `∂_z f` vanishes on the negative half-line
  have hpzneg : ∀ s : ℝ, s < 0 → ∀ θ : ℝ, Work.Spaces.pz f s θ = 0 := by
    intro s hs θ
    have hev : (fun z : ℝ => f z θ) =ᶠ[nhds s] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with z hz
      exact hzero z θ (fun hc' => absurd hc'.1 (not_lt.mpr (le_of_lt hz)))
    show deriv (fun z : ℝ => f z θ) s = 0
    rw [hev.deriv_eq]
    exact deriv_const s 0
  have hfneg : ∀ s : ℝ, s < 0 → ∀ θ : ℝ, f s θ = 0 :=
    fun s hs θ => hzero s θ (fun hc' => absurd hc'.1 (not_lt.mpr (le_of_lt hs)))
  -- ### `Transport f` vanishes for `s ≤ 0`
  have hTransport_nonpos : ∀ s : ℝ, s ≤ 0 → ∀ θ : ℝ, Work.Coercivity.Transport f s θ = 0 := by
    intro s hs θ
    have hf0 : (fun θ' : ℝ => f s θ') = fun _ => (0 : ℝ) := by
      funext θ'
      exact hzero s θ' (fun hc' => absurd hc'.1 (not_lt.mpr hs))
    simp only [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Spaces.pth]
    rw [hf0, deriv_const]
    ring
  -- ### `LGamma f` and `Proj (Transport f)` on the negative half-line
  have hLG_neg : ∀ s : ℝ, s < 0 → ∀ θ : ℝ, Work.Coercivity.LGamma α f s θ
      = -(2 * s * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + s) ^ 2))
          * Work.Coercivity.L12f f s := by
    intro s hs θ
    have hf : f s θ = 0 := hfneg s hs θ
    have hpz : Work.Spaces.pz f s θ = 0 := hpzneg s hs θ
    simp only [Work.Coercivity.LGamma, Work.Coercivity.L, Work.Spaces.Dz]
    rw [hf, hpz]
    ring
  have hPT_neg : ∀ s : ℝ, s < 0 → ∀ θ : ℝ,
      Work.Coercivity.Proj α (Work.Coercivity.Transport f) s θ
        = -(Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * s ^ 2 / (1 + s) ^ 3)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
    intro s hs θ
    have hT : Work.Coercivity.Transport f s θ = 0 := hTransport_nonpos s (le_of_lt hs) θ
    simp only [Work.Coercivity.Proj]
    rw [hT]
    ring
  -- ### `SmoothOpen`/`ℋ⁴` of `D_z f`, and the angular `∂_z f`-slices
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f) := hC.reg.Dz
  have hDzmem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le hC.reg
      (Work.FTS.IPGen.HkMem_mono_le hC.reg 5 (by norm_num) hC.mem)
  have hpz : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.pz f s θ) Work.Spaces.Iθ := by
    intro s hs
    have h := Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hDzsm hDzmem hs
    refine h.congr_fun ?_ (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
    intro θ _
    have hsne : s ≠ 0 := ne_of_gt hs
    simp only [Work.Spaces.Dz]
    field_simp
  -- ### the `L₁₂`-density of `D_z f` is `Kav (∂_z f)`, hence `Kav (∂_z f) ∈ L¹`
  have hmd : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ)
      (Set.Ioi 0) := by
    have hInt : MeasureTheory.IntegrableOn
        (Work.Construction.L12dens (Work.Spaces.Dz f)) (Set.Ioi 0) :=
      Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hDzsm hDzmem
    refine hInt.congr_fun ?_ measurableSet_Ioi
    intro s hs
    exact Work.Coercivity.CommutZ.L12dens_Dz_eq f s hs
  -- ### `K·Γ·(L₁₂ f/(1+z)²) ∈ L¹`
  have hintL : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
        * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2)) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.StrongEps.EpsZero.Bridge.HintL hα0 hintL2
  -- ### the density of `𝓛_Γ f` is in `L¹`
  have hint3 : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Coercivity.LGamma α f)) (Set.Ioi 0) :=
    Work.FTS.StrongEps.EpsZero.Bridge.L12densLGamma hα0 hα1 hC.reg h4 hint hintL2 hmd
  -- ### the paper's zero-mode identity for `𝓛_Γ`
  have hLG : Work.Construction.L12 (Work.Coercivity.LGamma α f) 0
      = - Work.Construction.L12 f 0 :=
    Work.FTS.Apriori.ZeroMode.L12_LGamma_zero hα0 hα1 hdiff hcont hdec hvan
      hint hintL hintL2 hint3
  -- ### the projector kills the transport term
  have hTr := Work.FTS.GalFields.RHS.Transport_L12_integrable hα0 hα1 hC.reg h4
  have hPT := Work.FTS.StrongEps.EpsZero.Bridge.ProjTransport hα0 hα1 hC.reg hTr.1 hTr.2
  have hP : Work.Construction.L12 (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) 0 = 0 :=
    Work.Coercivity.Proj_L12f_zero α hα0 hα1 (Work.Coercivity.Transport f) hTr.2 hTr.1 hPT.2
  -- ### the slice integrability for *all* `s` (the negative half-line is elementary)
  have hLGslice : ∀ s : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.LGamma α f s θ / s) Work.Spaces.Iθ := by
    intro s
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have hconst : ∀ θ : ℝ, Work.Spaces.K θ * Work.Coercivity.LGamma α f s θ / s
          = (-(2 / (Work.Spaces.c α * (1 + s) ^ 2)) * Work.Coercivity.L12f f s)
              * (Work.Spaces.K θ * Work.Spaces.Gam α θ) := by
        intro θ
        rw [hLG_neg s hs θ]
        by_cases h1s : (1 : ℝ) + s = 0
        · rw [h1s]
          simp
        · have hsne : s ≠ 0 := ne_of_lt hs
          field_simp
      rw [show (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.LGamma α f s θ / s)
          = fun θ : ℝ => (-(2 / (Work.Spaces.c α * (1 + s) ^ 2)) * Work.Coercivity.L12f f s)
              * (Work.Spaces.K θ * Work.Spaces.Gam α θ) from funext hconst]
      rw [show (fun θ : ℝ => (-(2 / (Work.Spaces.c α * (1 + s) ^ 2))
                * Work.Coercivity.L12f f s) * (Work.Spaces.K θ * Work.Spaces.Gam α θ))
          = fun θ : ℝ => (-(2 / (Work.Spaces.c α * (1 + s) ^ 2))
                * Work.Coercivity.L12f f s) * (Work.Spaces.Gam α θ * Work.Spaces.K θ) from by
        funext θ; ring]
      exact (Work.Spaces.CAux.integrableOn_GamK α hα0).const_mul _
    · subst hs
      simpa only [div_zero] using
        (MeasureTheory.integrableOn_zero (s := Work.Spaces.Iθ) (μ := volume))
    · exact Work.FTS.StrongEps.EpsZero.Bridge.LGammaSlice hα0 hα1 hC.reg h4 hpz s hs
  have hPTslice : ∀ s : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.Proj α (Work.Coercivity.Transport f) s θ / s)
      Work.Spaces.Iθ := by
    intro s
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have hconst : ∀ θ : ℝ,
          Work.Spaces.K θ * Work.Coercivity.Proj α (Work.Coercivity.Transport f) s θ / s
            = (-(Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                  * (2 * s / (Work.Spaces.c α * (1 + s) ^ 3))))
                * (Work.Spaces.K θ * Work.Spaces.Gam α θ) := by
        intro θ
        rw [hPT_neg s hs θ]
        by_cases h1s : (1 : ℝ) + s = 0
        · rw [h1s]
          simp
        · have hsne : s ≠ 0 := ne_of_lt hs
          field_simp
      rw [show (fun θ : ℝ =>
            Work.Spaces.K θ * Work.Coercivity.Proj α (Work.Coercivity.Transport f) s θ / s)
          = fun θ : ℝ => (-(Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                  * (2 * s / (Work.Spaces.c α * (1 + s) ^ 3))))
                * (Work.Spaces.K θ * Work.Spaces.Gam α θ) from funext hconst]
      rw [show (fun θ : ℝ => (-(Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                * (2 * s / (Work.Spaces.c α * (1 + s) ^ 3))))
                * (Work.Spaces.K θ * Work.Spaces.Gam α θ))
          = fun θ : ℝ => (-(Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                * (2 * s / (Work.Spaces.c α * (1 + s) ^ 3))))
                * (Work.Spaces.Gam α θ * Work.Spaces.K θ) from by
        funext θ; ring]
      exact (Work.Spaces.CAux.integrableOn_GamK α hα0).const_mul _
    · subst hs
      simpa only [div_zero] using
        (MeasureTheory.integrableOn_zero (s := Work.Spaces.Iθ) (μ := volume))
    · exact hPT.1 s hs
  -- ### the split and the conclusion
  have hsplit := Work.FTS.FinalClock.L12LinearSub hLGslice hPTslice hint3 hPT.2
  rw [show Work.Coercivity.LGammaT α f
      = fun z θ => Work.Coercivity.LGamma α f z θ
          - Work.Coercivity.Proj α (Work.Coercivity.Transport f) z θ from rfl, ← hsplit, hLG, hP]
  ring

end Work.FTS.StrongEps.EpsZero
