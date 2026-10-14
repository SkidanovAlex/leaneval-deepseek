import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cores.aSlotsTwo
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## The two level-`0` slots of `A = z²∂_z²Ψ` -/

/-- **The level-`0` `A`-slot of the weak class**, from the level-`0` estimate `h0`: this is the
`A`-half of `TT.EllWeak0`, with the class descended from level `2` to level `0`. -/
theorem aSlotsTwoT1_l0A (h0 : ∃ C : ℝ, 0 < C ∧ TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := h0
  refine ⟨C₀, hC₀pos, ?_⟩
  intro α F Ψ hα hα4 h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.H2W.SmoothOpen_F_weak α 2 F Ψ h
  have hAso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul (hΨso.pzIter 2)
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_pthIter hΨso 2
  have hdesc : TT.EllWeakPos α 0 F Ψ :=
    ⟨h.eq, h.zero, h.pi_half, h.orthF, h.orthPsi, h.smooth,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 2) (by norm_num)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hFso) h.memF,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 2) (by norm_num)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hAso) h.memA,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 2) (by norm_num)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hBso) h.memB,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 2) (by norm_num)
        (Work.FTS.EllipticEst.TT.smoothOpen_diagHon
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hBso)) h.memZPth2⟩
  have hmain := hC₀ α F Ψ hα hα4 hdesc
  have hBnn : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) :=
    Work.Spaces.HkSq_nonneg α 0 _
  have hFmono : Work.Spaces.HkSq α 0 F ≤ Work.Spaces.HkSq α 2 F := by
    have hpt : ∀ z θ, Work.Spaces.HkIntegrand α 0 F z θ
        ≤ 1 * Work.Spaces.HkIntegrand α 2 F z θ := by
      intro z θ
      rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq]
      simpa using Work.Spaces.sq_le_HkIntegrand_z α 2 F z θ 0 (by norm_num)
    have := Work.FTS.EllipticEst.H2W.eslHkSqZero_le_of_pointwise α 1 (by norm_num)
      (g := F) h.memF hpt
    simpa using this
  have hstep : α ^ 4 * Work.Spaces.HkSq α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      ≤ C₀ * Work.Spaces.HkSq α 0 F := by linarith
  exact hstep.trans (mul_le_mul_of_nonneg_left hFmono (le_of_lt hC₀pos))

/-- **The angular `(0,2)`-slot of `A` at level `0`**, from the shifted level-`0` estimates. -/
theorem aSlotsTwoT1_l0pA (h0 : ∃ C : ℝ, 0 < C ∧ TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.Spaces.HkSq α 0
          (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := HkSq_zero_pthIter_two_DzIter_two_le h0
  obtain ⟨C₁, hC₁pos, hC₁⟩ := HkSq_zero_pthIter_two_DzIter_one_le h0
  refine ⟨2 * C₂ + 2 * C₁, by linarith, ?_⟩
  intro α F Ψ hα hα4 h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_pthIter hΨso 2
  -- (1) `∂_θ²(z²∂_z²Ψ) = z²∂_z²(∂_θ²Ψ)`
  have e1 : Work.Spaces.HkSq α 0
        (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      = Work.Spaces.HkSq α 0
          (Work.FTS.EllipticEst.H2W.Ae.rad2 (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
      Work.FTS.EllipticEst.H2W.pthIter_two_zsq_eq_rad2 Ψ hΨso hz ⟨hθ0, hθ1⟩)
  -- (2) `z²∂_z² = D_z² - D_z`
  have e2 : Work.Spaces.HkSq α 0
        (Work.FTS.EllipticEst.H2W.Ae.rad2 (Work.Spaces.pthIter 2 Ψ))
      = Work.Spaces.HkSq α 0
          (fun z θ => Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
            - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
      Work.FTS.EllipticEst.H2W.AeDataAofAux.zsq_pzIter2_eq_open hBso hz ⟨hθ0, hθ1⟩)
  -- (3) honesty of the two summands
  have hm2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
      ((hBso.DzIter 2).continuousOn)
      (fun z θ hz hθ0 hθ1 =>
        (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 2 hΨso
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)).symm)
      ((Work.FTS.EllipticEst.H2W.HkMem_zero_slices α F Ψ h 2 (by norm_num)).2.2)
  have hm1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
      ((hBso.DzIter 1).continuousOn)
      (fun z θ hz hθ0 hθ1 =>
        (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 1 hΨso
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)).symm)
      ((Work.FTS.EllipticEst.H2W.HkMem_zero_slices α F Ψ h 1 (by norm_num)).2.2)
  have hsub := Work.FTS.EllipticEst.H2W.HkSq_zero_sub_le α
    (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
    (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) hm2 hm1
  -- (4) the Clairaut transfers of the two `ℋ⁰`-norms
  have f2 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
      = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
      (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 2 hΨso
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)).symm)
  have f1 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
      = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
      (Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 1 hΨso
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)).symm)
  have hb2 := hC₂ α F Ψ hα hα4 h
  have hb1 := hC₁ α F Ψ hα hα4 h
  have hkey : Work.Spaces.HkSq α 0
        (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ≤ (2 * C₂ + 2 * C₁) * Work.Spaces.HkSq α 2 F := by
    rw [e1, e2]
    calc Work.Spaces.HkSq α 0
          (fun z θ => Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
            - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ)
        ≤ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
          + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) := hsub
      _ = 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
          + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := by
          rw [f2, f1]
      _ ≤ 2 * (C₂ * Work.Spaces.HkSq α 2 F) + 2 * (C₁ * Work.Spaces.HkSq α 2 F) := by
          linarith
      _ = (2 * C₂ + 2 * C₁) * Work.Spaces.HkSq α 2 F := by ring
  have hα4le : α ^ 4 ≤ 1 := pow_le_one₀ (le_of_lt hα) (by linarith)
  calc α ^ 4 * Work.Spaces.HkSq α 0
        (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ≤ 1 * Work.Spaces.HkSq α 0
          (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
        mul_le_mul_of_nonneg_right hα4le (Work.Spaces.HkSq_nonneg α 0 _)
    _ ≤ (2 * C₂ + 2 * C₁) * Work.Spaces.HkSq α 2 F := by simpa using hkey

/-! ## The target -/

/-- **The level-`1` `A`-slot**: `α⁴ Tk α 1 (z²∂_z²Ψ) ≤ C |F|²_{ℋ²}` on the level-`2` weak
class. -/
theorem aSlotsTwoT1 (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨Cag, hCagpos, hag⟩ := Work.FTS.EllipticEst.H2W.angularAgmon
  obtain ⟨Cp, hCppos, hpiv⟩ := Work.FTS.EllipticEst.H2W.pivotBound
  have hCis : (0 : ℝ) ≤ 20000 * Cp + 10000 * Real.pi + 1 := by positivity
  obtain ⟨Cl, hClpos, hlh⟩ := Work.FTS.EllipticEst.H2W.esl_lhs_bound Cag
    (20000 * Cp + 10000 * Real.pi + 1) (le_of_lt hCagpos) hCis hag
    (Work.FTS.EllipticEst.H2W.deriv_sq_mul_sEta_le Cp hCppos hpiv)
    (fun α u hα hα4 hu => Work.FTS.EllipticEst.H2W.eslDth2Bound α hα hα4 u hu)
    (fun α F Ψ hh => Work.FTS.EllipticEst.H2W.eslHkMemPthTwoZsq α hh)
  obtain ⟨CA, hCApos, hA⟩ := aSlotsTwoT1_l0A h0
  obtain ⟨CB, hCBpos, hB⟩ := aSlotsTwoT1_l0pA h0
  refine ⟨Cl * (CA + CB) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hα4nn : (0 : ℝ) ≤ α ^ 4 := by positivity
  have hClnn : 0 ≤ Cl := le_of_lt hClpos
  have h2nn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hS2nn : 0 ≤ Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.mixed 0 2 (Work.FTS.EllipticEst.H2W.eslA Ψ) z θ
        * Work.Spaces.Wt α z θ) :=
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have h1 := hlh α F Ψ hα hα4 h
  have hA' := hA α F Ψ hα hα4 h
  have hB' := hB α F Ψ hα hα4 h
  have h2 : α ^ 4 * (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.eslA Ψ)
        + Work.Spaces.HkSq α 0
            (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.eslA Ψ)))
      ≤ (CA + CB) * Work.Spaces.HkSq α 2 F := by
    have hx : 0 ≤ Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.eslA Ψ) :=
      Work.Spaces.HkSq_nonneg α 0 _
    have hy : 0 ≤ Work.Spaces.HkSq α 0
        (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.eslA Ψ)) :=
      Work.Spaces.HkSq_nonneg α 0 _
    have hAx : α ^ 4 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.eslA Ψ)
        ≤ CA * Work.Spaces.HkSq α 2 F := hA'
    have hBy : α ^ 4 * Work.Spaces.HkSq α 0
          (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.eslA Ψ))
        ≤ CB * Work.Spaces.HkSq α 2 F := hB'
    nlinarith [hAx, hBy, h2nn, hx, hy]
  calc α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 1 (Work.FTS.EllipticEst.H2W.eslA Ψ) z θ
            * Work.Spaces.Wt α z θ) := rfl
    _ ≤ α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 0 1 (Work.FTS.EllipticEst.H2W.eslA Ψ) z θ
              * Work.Spaces.Wt α z θ)
          + Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 0 2 (Work.FTS.EllipticEst.H2W.eslA Ψ) z θ
              * Work.Spaces.Wt α z θ)) := by
        nlinarith [hα4nn, hS2nn]
    _ ≤ α ^ 4 * (Cl * (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.eslA Ψ)
          + Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.eslA Ψ)))) :=
        mul_le_mul_of_nonneg_left h1 hα4nn
    _ = Cl * (α ^ 4 * (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.eslA Ψ)
          + Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.eslA Ψ)))) := by ring
    _ ≤ Cl * ((CA + CB) * Work.Spaces.HkSq α 2 F) :=
        mul_le_mul_of_nonneg_left h2 hClnn
    _ ≤ (Cl * (CA + CB) + 1) * Work.Spaces.HkSq α 2 F := by nlinarith [h2nn]

end

end Work.FTS.EllipticEst.Cores
