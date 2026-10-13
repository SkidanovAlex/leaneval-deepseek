import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllExist.ClassCInputs
import Submission.Work.FTS.EllExist.hkMem_orthSource_of_Fstar_smooth
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.EllipticEst.Cert.GbarLayer.Target
import Submission.Work.FTS.EllipticEst.Cert.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_norm
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VthAuxC

/-- **The `ℋ⁴`-certificate of the orthogonalised source and of the layer `Ḡ·sin 2θ`.**

For every profile `g` of the linear class `C` (`Work.FTS.EllSol.ClassC α g`) and every
`α ∈ (0,1]` the two objects feeding the `V^{th}` slot of the elliptic package,
`orthSource g = g - (15/4)·sin 2θ·F_*(g)` and `Ḡ(α,g)·sin 2θ`, are `C^∞` on the open quadrant and
honestly in `ℋ⁴`, with `ℋ⁴`-norms bounded by a universal constant times `|g|_{ℋ⁴}`; the constant
is *independent of `α ∈ (0,1]`*.

Route (verbatim from `Work.FTS.EllSol.orthSource_HkNorm_le` and
`Work.FTS.EllipticEst.Cert.GbarSin_layer`, with `EllClassO` replaced by the class fields):

* `orthSource g = g + (-(15/4))·Φ` with `Φ = F_*(g)·sin 2θ`, so the `C^∞`-part is the sum of
  `h.reg` and the separated product `SmoothOpen.sep_mul h.fsm (fun_prop)` (via
  `EllExist.smoothOpen_orthSource_of_Fstar_smooth`), and the `ℋ⁴`-norm bound is the triangle
  inequality `HkNorm_add_le` plus `HkNorm_const_mul` together with the certificate
  `Cert.Fstar_Hk_le_open 4` for `Φ`;
* the same triangle inequality gives the membership
  (`EllExist.hkMem_orthSource_of_Fstar_smooth` at level `7`, descended to level `4` by
  `HkMem_mono_open`);
* `Ḡ(α,g) ∈ C^∞(0,∞)` is `Cert.Gbar_contDiffOn_Ioi` (it uses `F_*(g) ∈ C^∞(0,∞)`, i.e. `h.fsm`,
  and the integrability of `F_*(g)(r)/r`), so `Ḡ·sin 2θ` is `SmoothOpen.sep_mul` of the two;
  membership and norm bound are the layer certificate
  `GbarLayer.layer_{HkMem_target_of_smoothOpen, Gbar_HkNorm_le_SmoothOpen}`. -/
theorem certC : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllSol.ClassC α g →
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkMem α 4 (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g) ≤ C * Work.Spaces.HkNorm α 4 g ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ∧
    Work.Spaces.HkMem α 4 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ∧
    Work.Spaces.HkNorm α 4 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
      ≤ C * Work.Spaces.HkNorm α 4 g := by
  -- the two `α`-uniform certificates
  obtain ⟨Cf, hCfpos, hFle⟩ := Work.FTS.EllipticEst.Cert.Fstar_Hk_le_open 4
  obtain ⟨Cg, hCgpos, hGle⟩ :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_Gbar_HkNorm_le_SmoothOpen 4
  refine ⟨max (Real.sqrt 2 * (1 + (15 / 4) * Cf)) Cg, ?_, ?_⟩
  · have hpos : (0 : ℝ) < Real.sqrt 2 * (1 + (15 / 4) * Cf) := by positivity
    exact lt_of_lt_of_le hpos (le_max_left _ _)
  · intro α g hα hα1 h
    -- ## the standing facts about the class-`C` profile
    have hreg : Work.FTS.EllipticEst.SmoothOpen g := h.reg
    have hfsm : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0) :=
      h.fsm
    have hmem7 : Work.Spaces.HkMem α 7 g := h.mem
    have hmem4 : Work.Spaces.HkMem α 4 g :=
      Work.FTS.OpenPkg.HkMem_mono_open hreg 4 (by norm_num) hmem7
    have hgram : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry g)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hreg
    -- ## `orthSource g`: smoothness
    have hOrthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) :=
      Work.FTS.EllExist.smoothOpen_orthSource_of_Fstar_smooth hreg h.fsm
    -- ## `orthSource g`: membership (level `7`, descended to level `4`)
    have hOrthMem : Work.Spaces.HkMem α 4 (Work.Elliptic.orthSource g) :=
      Work.FTS.OpenPkg.HkMem_mono_open hOrthSm 4 (by norm_num)
        (Work.FTS.EllExist.hkMem_orthSource_of_Fstar_smooth hα hα1 hreg hmem7 h.fsm)
    -- ## the angular-moment term `Φ = F_*(g)·sin 2θ`
    have hΦsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.SmoothOpen.sep_mul hfsm (by fun_prop)
    have hΦraw : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hΦsm
    have hΦmem : Work.Spaces.HkMem α 4
        (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
      have h := Work.FTS.EllipticEst.Cert.HkMem_bmom_sin_of_smoothOpen α 4 g hα hα1 hreg hmem4
      simpa only [Work.FTS.EllipticEst.Bmom_zero] using h
    -- ## the scaled term `-(15/4)·Φ`
    have hSsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
      hΦsm.const_mul' (-(15 / 4))
    have hSraw : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry
          (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSsm
    have hSmem : Work.Spaces.HkMem α 4
        (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
      Work.FTS.LocData.HkMem_const_mul α 4 (-(15 / 4)) hΦmem
    -- ## `orthSource g` as the sum of the two summands
    have horth : Work.Elliptic.orthSource g
        = fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
      funext z θ
      simp only [Work.Elliptic.orthSource]
      ring
    -- ## the norm bound for `orthSource g` (triangle inequality + `Cert.Fstar_Hk_le_open 4`)
    have hsum := Work.FTS.EllipticEst.HkNorm_add_le α 4 hgram hSraw hmem4 hSmem
    have hcm := Work.FTS.EllipticEst.HkNorm_const_mul α 4 (-(15 / 4)) hΦraw
    have hPhi := hFle α g hα hα1 hgram hmem4
    have hOrthLe : Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g)
        ≤ (Real.sqrt 2 * (1 + (15 / 4) * Cf)) * Work.Spaces.HkNorm α 4 g := by
      rw [horth]
      calc Work.Spaces.HkNorm α 4
            (fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
          ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 g
              + Work.Spaces.HkNorm α 4 (fun z θ => (-(15 / 4))
                  * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))) := hsum
        _ = Real.sqrt 2 * (Work.Spaces.HkNorm α 4 g
              + (15 / 4) * Work.Spaces.HkNorm α 4
                  (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))) := by
            rw [hcm, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 15 / 4)]
        _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 g
              + (15 / 4) * (Cf * Work.Spaces.HkNorm α 4 g)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
            have h1 : (15 / 4) * Work.Spaces.HkNorm α 4
                  (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))
                ≤ (15 / 4) * (Cf * Work.Spaces.HkNorm α 4 g) :=
              mul_le_mul_of_nonneg_left hPhi (by norm_num)
            linarith
        _ = (Real.sqrt 2 * (1 + (15 / 4) * Cf)) * Work.Spaces.HkNorm α 4 g := by ring
    -- ## the layer `Ḡ(α,g)·sin 2θ`
    have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
        (Set.Ioi 0) :=
      Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hreg hmem7
    have hGbsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α g hα hfsm hFint
    have hGbsinSm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.SmoothOpen.sep_mul hGbsm (by fun_prop)
    have hGbsinMem : Work.Spaces.HkMem α 4
        (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.Cert.GbarLayer.layer_HkMem_target_of_smoothOpen α hα hα1 4 g hreg
        hmem4
    have hGbsinLe : Work.Spaces.HkNorm α 4
        (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
        ≤ Cg * Work.Spaces.HkNorm α 4 g :=
      hGle α g hα hα1 hreg hmem4
    -- ## assembling the two bounds into the common constant
    refine ⟨hOrthSm, hOrthMem, ?_, hGbsinSm, hGbsinMem, ?_⟩
    · exact le_trans hOrthLe
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Work.Spaces.HkNorm_nonneg α 4 g))
    · exact le_trans hGbsinLe
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Work.Spaces.HkNorm_nonneg α 4 g))

end Work.FTS.EllSol.VthAuxC
