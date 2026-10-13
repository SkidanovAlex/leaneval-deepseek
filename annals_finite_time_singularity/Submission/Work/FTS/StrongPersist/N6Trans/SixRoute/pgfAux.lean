import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePt6
import Submission.Work.Blocks.DivSinHalfCore
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.H2.Transport3Aux.sin_weight_hardy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `pureGamFamSix` — auxiliary lemmas

Helpers for `Work.FTS.StrongPersist.N6Trans.SixRoute.pureGamFamSix`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The open quadrant. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The product measure on the quadrant. -/
abbrev pm : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-! ## Continuity on the open quadrant -/

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) := by
  have h3 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
  have h4 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi h3 h4

theorem continuousOn_sin_two_rpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd := by
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
  intro p hp
  exact Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo ⟨hp.2.1, hp.2.2⟩))

theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := rfl
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

theorem continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [hfun]
  exact continuousOn_w_Qd.mul (continuousOn_sin_two_rpow_Qd _)

theorem continuousOn_w2_sig_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ c) Qd :=
  (continuousOn_w_Qd.pow 2).mul (continuousOn_sin_two_rpow_Qd c)

theorem continuousOn_w_div_sig_Qd :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd := by
  refine continuousOn_w_Qd.div (continuousOn_sin_two_rpow_Qd _) (fun p hp => ?_)
  exact ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo ⟨hp.2.1, hp.2.2⟩) _)

theorem aesm_of_continuousOn_Qd' {F : ℝ → ℝ → ℝ}
    (h : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Qd) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) pm :=
  Work.Spaces.aesm_of_continuousOn_Qd _ h

theorem continuousOn_sin_two_rpow_Ioo (c : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun _ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))

/-! ## Fubini for nonnegative functions on the quadrant -/

theorem integrable_prod_of_iterated_ae {G : ℝ → ℝ → ℝ}
    (hnn : ∀ᵐ p ∂pm, 0 ≤ G p.1 p.2)
    (hAE : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2) pm)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => G z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, G z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => G p.1 p.2) pm ∧
      (∫ p : ℝ × ℝ, G p.1 p.2 ∂pm)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, G z θ := by
  have hae := MeasureTheory.Measure.ae_ae_of_ae_prod hnn
  have hkey : (fun z => ∫ θ in Work.Spaces.Iθ, ‖G z θ‖)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, G z θ) := by
    filter_upwards [hae] with z hz
    exact MeasureTheory.integral_congr_ae (hz.mono fun θ hθ => Real.norm_of_nonneg hθ)
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => G p.1 p.2) pm := by
    rw [MeasureTheory.integrable_prod_iff hAE]
    exact ⟨hslice, houter.congr hkey.symm⟩
  exact ⟨hInt, (MeasureTheory.integral_integral hInt).symm⟩

/-! ## The weight identities and comparisons -/

theorem Wt_sq_eq {α z θ : ℝ} (hγ : Work.Spaces.gam α ≠ 0) (hσ : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rcases eq_or_lt_of_le hσ with h | h
  · rw [← h, Real.zero_rpow (by simpa using hγ),
      Real.zero_rpow (by simpa using (div_ne_zero hγ (by norm_num : (2:ℝ) ≠ 0)))]
    ring
  · have h1 : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      rw [sq, ← Real.rpow_add h]
      congr 1
      ring
    rw [h1]

theorem Wt_sq_Iθ {α z θ : ℝ} (hγ : Work.Spaces.gam α ≠ 0) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  Wt_sq_eq hγ (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)

theorem gam_ne_zero {α : ℝ} (hα : 0 < α) : Work.Spaces.gam α ≠ 0 :=
  ne_of_gt (by rw [Work.Spaces.gam]; linarith)

theorem rpow_le_rpow_neg_pos {σ c q : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : -q ≤ c) :
    σ ^ c ≤ σ ^ (-q) :=
  Real.rpow_le_rpow_of_exponent_ge hσ hσ1 hc

theorem gam_mul_split {α σ : ℝ} (hσ : 0 < σ) :
    σ ^ (-(Work.Spaces.gam α)) * (α + σ) * σ ^ (α / 5)
      = α * σ ^ (-(1 - α / 10)) + σ ^ (α / 10) := by
  have h2 : σ ^ (-(Work.Spaces.gam α)) * σ ^ (α / 5) = σ ^ (-(1 - α / 10)) := by
    rw [← Real.rpow_add hσ, Work.Spaces.gam]
    congr 1
    ring
  have h3 : σ ^ (-(1 - α / 10)) * σ = σ ^ (α / 10) := by
    have h1 : σ ^ (-(1 - α / 10)) * σ ^ (1 : ℝ) = σ ^ (α / 10) := by
      rw [← Real.rpow_add hσ]
      congr 1
      ring
    rwa [Real.rpow_one] at h1
  calc σ ^ (-(Work.Spaces.gam α)) * (α + σ) * σ ^ (α / 5)
      = α * (σ ^ (-(Work.Spaces.gam α)) * σ ^ (α / 5))
        + (σ ^ (-(Work.Spaces.gam α)) * σ ^ (α / 5)) * σ := by ring
    _ = α * σ ^ (-(1 - α / 10)) + σ ^ (α / 10) := by rw [h2, h3]

theorem amgm_sqrt (c K G Y : ℝ) (hK : 0 < K) (hc : 0 ≤ c) :
    c * |G| * |Y| ≤ c ^ 2 * G ^ 2 / (2 * Real.sqrt K) + Real.sqrt K * Y ^ 2 / 2 := by
  have hK' : Real.sqrt K * Real.sqrt K = K := by rw [← sq, Real.sq_sqrt hK.le]
  have hs := sq_nonneg (c * |G| - Real.sqrt K * |Y|)
  have h1 : |G| ^ 2 = G ^ 2 := sq_abs G
  have h2 : |Y| ^ 2 = Y ^ 2 := sq_abs Y
  have hkey : 2 * Real.sqrt K * (c * |G| * |Y|) ≤ c ^ 2 * G ^ 2 + K * Y ^ 2 := by
    have h := hs
    rw [sub_sq, mul_pow, mul_pow, h1, h2, Real.sq_sqrt hK.le] at h
    nlinarith [h]
  have hpos : 0 < 2 * Real.sqrt K := by positivity
  have h3 : (c ^ 2 * G ^ 2 + K * Y ^ 2) / (2 * Real.sqrt K)
      = c ^ 2 * G ^ 2 / (2 * Real.sqrt K) + Real.sqrt K * Y ^ 2 / 2 := by
    have h4 : K * Y ^ 2 / (2 * Real.sqrt K) = Real.sqrt K * Y ^ 2 / 2 := by
      rw [div_eq_iff (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.sqrt K))]
      rw [show Real.sqrt K * Y ^ 2 / 2 * (2 * Real.sqrt K)
          = (Real.sqrt K * Real.sqrt K) * Y ^ 2 by ring]
      rw [hK']
    rw [add_div, h4]
  rw [← h3, le_div_iff₀ hpos]
  linarith [hkey]

theorem pm_eq_restrict :
    pm = MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  show (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    = MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]

/-! ## The `σ`-weight of the angular derivative of a pure `D_z`-slot -/

theorem sigma_pth_dzIter {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (m : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DzIter m g z θ') θ
      = Work.Spaces.mixed m 1 g z θ := by
  rw [Work.Blocks.DivSinHalf.deriv_DzIter_slice_Q0 hg m hz hθ]
  have h := Work.FTS.TransportS.DzIter_const_mul m (fun θ' => Real.sin (2 * θ'))
    (Work.Spaces.pth g) z θ
  rw [← h]
  rfl

/-! ## Product integrability from a pointwise domination by the `ℋ⁶`-integrand -/

theorem integrable_of_le_HkIntegrand {α : ℝ} {F g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) pm)
    (hpt : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 ≤ F z θ ∧ F z θ ≤ Work.Spaces.HkIntegrand α 6 g z θ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2) pm ∧
      (∫ p : ℝ × ℝ, F p.1 p.2 ∂pm) ≤ Work.Spaces.HkSq α 6 g := by
  have h := Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise (α := α) (M := 1)
    (F := F) (g := g) hgs hgm (by norm_num) haesm
    (fun z θ hz hθ hθ2 => by
      rw [abs_of_nonneg (hpt z θ hz hθ hθ2).1]
      simpa using (hpt z θ hz hθ hθ2).2)
  simpa using h

/-- The `γ`-weighted mixed slot of `g`, squared. -/
theorem mixedSlot_sq_le_HkSq {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 6) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed b a g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2) pm ∧
      (∫ p : ℝ × ℝ, (Work.Spaces.mixed b a g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 ∂pm)
        ≤ Work.Spaces.HkSq α 6 g := by
  refine integrable_of_le_HkIntegrand (F := fun z θ =>
      (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2) hgs hgm ?_ ?_
  · refine aesm_of_continuousOn_Qd' (F := fun z θ =>
        (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2) ?_
    exact ((hgs.mixed b a).continuousOn.mul (continuousOn_Wt_Qd α)).pow 2
  · intro z θ hz hθ hθ2
    exact ⟨sq_nonneg _, Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ a b ha hab⟩

/-- The `η`-weighted pure `D_z`-slot of `g`, squared. -/
theorem dzSlot_sq_le_HkSq {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (m : ℕ) (hm : m ≤ 6) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter m g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) pm ∧
      (∫ p : ℝ × ℝ, (Work.Spaces.DzIter m g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 ∂pm)
        ≤ Work.Spaces.HkSq α 6 g := by
  refine integrable_of_le_HkIntegrand (F := fun z θ =>
      (Work.Spaces.DzIter m g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) hgs hgm ?_ ?_
  · refine aesm_of_continuousOn_Qd' (F := fun z θ =>
        (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) ?_
    exact ((hgs.DzIter m).continuousOn.mul continuousOn_w_div_sig_Qd).pow 2
  · intro z θ hz hθ hθ2
    exact ⟨sq_nonneg _, Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ m hm⟩

/-- A `σ^{c}`-weighted mixed slot of `g`, squared, for `c ≥ -γ`. -/
theorem mixedSlot_weight_le_HkSq {α c : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (hc : -(Work.Spaces.gam α) ≤ c) {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 6) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ c
          * (Work.Spaces.mixed b a g p.1 p.2) ^ 2) pm ∧
      (∫ p : ℝ × ℝ, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ c
          * (Work.Spaces.mixed b a g p.1 p.2) ^ 2 ∂pm) ≤ Work.Spaces.HkSq α 6 g := by
  refine integrable_of_le_HkIntegrand (F := fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c
        * (Work.Spaces.mixed b a g z θ) ^ 2) hgs hgm ?_ ?_
  · refine aesm_of_continuousOn_Qd' (F := fun z θ =>
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c
          * (Work.Spaces.mixed b a g z θ) ^ 2) ?_
    exact (continuousOn_w2_sig_Qd c).mul ((hgs.mixed b a).continuousOn.pow 2)
  · intro z θ hz hθ hθ2
    have hσ : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo ⟨hθ, hθ2⟩
    have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hY0 : 0 ≤ (Work.Spaces.mixed b a g z θ) ^ 2 := sq_nonneg _
    refine ⟨by positivity, ?_⟩
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (rpow_le_rpow_neg_pos hσ hσ1 hc) (sq_nonneg _)) hY0
      _ = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          rw [mul_pow, Wt_sq_eq (gam_ne_zero hα) hσ.le]
          ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ a b ha hab

/-- A `σ^{c}`-weighted pure `D_z`-slot of `g`, squared, for `c ≥ -η`. -/
theorem dzSlot_weight_le_HkSq {α c : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (hc : -(Work.Spaces.eta) ≤ c) (m : ℕ) (hm : m ≤ 6) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ c
          * (Work.Spaces.DzIter m g p.1 p.2) ^ 2) pm ∧
      (∫ p : ℝ × ℝ, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ c
          * (Work.Spaces.DzIter m g p.1 p.2) ^ 2 ∂pm) ≤ Work.Spaces.HkSq α 6 g := by
  refine integrable_of_le_HkIntegrand (F := fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c
        * (Work.Spaces.DzIter m g z θ) ^ 2) hgs hgm ?_ ?_
  · refine aesm_of_continuousOn_Qd' (F := fun z θ =>
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c
          * (Work.Spaces.DzIter m g z θ) ^ 2) ?_
    exact (continuousOn_w2_sig_Qd c).mul ((hgs.DzIter m).continuousOn.pow 2)
  · intro z θ hz hθ hθ2
    have hσ : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo ⟨hθ, hθ2⟩
    have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hY0 : 0 ≤ (Work.Spaces.DzIter m g z θ) ^ 2 := sq_nonneg _
    refine ⟨by positivity, ?_⟩
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.DzIter m g z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter m g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (rpow_le_rpow_neg_pos hσ hσ1 hc) (sq_nonneg _)) hY0
      _ = (Work.Spaces.DzIter m g z θ
            * (Work.FTS.H2.Whz z θ)) ^ 2 := by
          rw [mul_pow, Work.FTS.H2.hbi_Whz_sq z θ hσ.le]
          ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ m hm

end Work.FTS.StrongPersist.N6Trans.SixRoute
