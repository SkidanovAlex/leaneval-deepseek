import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.EllipticEst.Cores.PPureShiftRad.Basic
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.Basic
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.MajEst
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.pzIterSliceIntegrable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.Physical.Ident.vorticity_psiField_scaled
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The diagonal second-order honesty of the second difference-quotient datum

`EllWeakPos α k F Ψ` has, besides the three `HkMem`-clauses for `F`, `z²∂_z²Ψ`, `∂_θ²Ψ`, a
fourth ("diagonal") one: the honesty of `D_z(∂_θ²Ψ) = z ∂_z∂_θ²Ψ`.  That clause is not implied
by the other three, but it *is* stable under the second difference quotient: writing
`B = ∂_θ²Ψ` and `Y = D_zB`, the identity `D_z(dqq c B) = dqq c (D_zB)` (two applications of
`pPureShiftAux.Dz_dq_eqOn`) identifies the diagonal slot of the quotient with `dqq c Y`, whose
honesty follows from the honesty of `D_z²Y` — and `D_z²Y` is honest precisely because the
*level-`2`* diagonal clause of the hypothesis says that `Y` itself is in `ℋ²`. -/
theorem HkMem_diag_dqq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {c : ℝ} (hc : 1 < c) :
    Work.Spaces.HkMem α 0 (fun z θ =>
      z * Work.Spaces.pz (Work.Spaces.pthIter 2
        (Work.FTS.EllipticEst.Cores.Dil.dq c
          (Work.FTS.EllipticEst.Cores.Dil.dq c Ψ))) z θ) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hSΨ.pth.pth
  have hY : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
    hSB.Dz
  have hYmem : Work.Spaces.HkMem α 2 (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
    h.memZPth2
  have hYY : Work.Spaces.HkMem α 0
      (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)))) :=
    Work.FTS.EllipticEst.Cores.Dil.HkMem_DzDz hY hYmem
  have hbase : Work.Spaces.HkMem α 0
      (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))) :=
    Work.FTS.EllipticEst.Cores.pPureShiftAux.HkMem_dqq hY hY.Dz hYY hc
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hbase ?_
  intro z hz θ hθ
  have hev : (fun z' : ℝ => Work.Spaces.pthIter 2
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c Ψ) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c
        (Work.Spaces.pthIter 2 Ψ) z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.FTS.EllipticEst.Cores.pPureShiftAux.pthIter_two_dqq_eqOn hSΨ hc z' θ hz' hθ
  have hpz : Work.Spaces.pz (Work.Spaces.pthIter 2
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c Ψ)) z θ
      = Work.Spaces.pz (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c
        (Work.Spaces.pthIter 2 Ψ)) z θ := hev.deriv_eq
  have hstep : Work.Spaces.Dz (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c
        (Work.Spaces.pthIter 2 Ψ)) z θ
      = Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) z θ := by
    have h1 := Work.FTS.EllipticEst.Cores.pPureShiftAux.Dz_dq_eqOn
      (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hSB hcpos) hc z θ hz hθ
    have h2 : Work.FTS.EllipticEst.Cores.Dil.dq c
          (Work.Spaces.Dz (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.Spaces.pthIter 2 Ψ))) z θ
        = Work.FTS.EllipticEst.Cores.Dil.dq c
          (Work.FTS.EllipticEst.Cores.Dil.dq c
            (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))) z θ :=
      Work.FTS.EllipticEst.Cores.Dil.dq_congr_of_pos hcpos
        (fun y hy => Work.FTS.EllipticEst.Cores.pPureShiftAux.Dz_dq_eqOn hSB hc y θ hy hθ) hz
    simpa only [Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq] using h1.trans h2
  calc Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) z θ
      = Work.Spaces.Dz (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c
          (Work.Spaces.pthIter 2 Ψ)) z θ := hstep.symm
    _ = z * Work.Spaces.pz (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c
          (Work.Spaces.pthIter 2 Ψ)) z θ := rfl
    _ = z * Work.Spaces.pz (Work.Spaces.pthIter 2
          (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq c Ψ)) z θ := by rw [hpz]

/-! ## The target -/

theorem ShiftedTwoL2Clean (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.Spaces.HkSq α 0
          (Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 F) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := h0
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro α F Ψ hα hα4 h
  set A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hAdef
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hBdef
  set X : ℝ := Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 F) with hXdef
  have hXnn : 0 ≤ X := Work.Spaces.HkSq_nonneg α 0 _
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cores.Dil.smoothOpen_of_bslOp_eq hSΨ
      (fun z θ hz hθ hlt => h.eq z hz θ hθ hlt)
  have hSA : Work.FTS.EllipticEst.SmoothOpen A :=
    Work.FTS.EllipticEst.Cores.Dil.smoothOpen_zsq_mul (hSΨ.pzIter 2)
  have hSB : Work.FTS.EllipticEst.SmoothOpen B := hSΨ.pth.pth
  have hFmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz F)) :=
    Work.FTS.EllipticEst.Cores.Dil.HkMem_DzDz hSF h.memF
  have hAmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz A)) :=
    Work.FTS.EllipticEst.Cores.Dil.HkMem_DzDz hSA h.memA
  have hBmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz B)) :=
    Work.FTS.EllipticEst.Cores.Dil.HkMem_DzDz hSB h.memB
  -- the dilation parameters
  set c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1) with hcdef
  have hcpos : ∀ n : ℕ, 0 < c n := fun n => by
    rw [hcdef]; positivity
  have hc1 : ∀ n : ℕ, 1 < c n := fun n => by
    rw [hcdef]
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hctend : Filter.Tendsto c Filter.atTop (nhds 1) := by
    rw [hcdef]
    have h1 : Filter.Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1
  have hctend' : Filter.Tendsto c Filter.atTop (nhdsWithin 1 (Set.Ioi 1)) := by
    rw [nhdsWithin]
    refine Filter.tendsto_inf.mpr ⟨hctend, ?_⟩
    rw [Filter.tendsto_principal]
    exact Filter.Eventually.of_forall hc1
  have hpow : Filter.Tendsto (fun n : ℕ => (c n) ^ 6) Filter.atTop (nhds 1) := by
    simpa using hctend.pow 6
  -- the slot identities for the difference-quotient datum
  have hslotA : ∀ n : ℕ, Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.FTS.EllipticEst.Cores.Dil.dq (c n)
          (Work.FTS.EllipticEst.Cores.Dil.dq (c n) Ψ)) z θ)
      = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) A) := fun n =>
    Work.FTS.EllipticEst.HkSq_congr_open α 0
      (fun z θ hz hθ hlt =>
        Work.FTS.EllipticEst.Cores.pPureShiftAux.zsq_pzIter_two_dqq_eqOn hSΨ (hc1 n) z θ hz
          ⟨hθ, hlt⟩)
  have hslotB : ∀ n : ℕ, Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) Ψ))
      = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) B) := fun n =>
    Work.FTS.EllipticEst.HkSq_congr_open α 0
      (fun z θ hz hθ hlt =>
        Work.FTS.EllipticEst.Cores.pPureShiftAux.pthIter_two_dqq_eqOn hSΨ (hc1 n) z θ hz
          ⟨hθ, hlt⟩)
  -- the estimate for the difference-quotient datum
  have hest : ∀ n : ℕ, α ^ 4 * Work.Spaces.HkSq α 0
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) A)
      + Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) B)
      ≤ C₀ * (c n) ^ 6 * X := by
    intro n
    have hcls : Work.FTS.EllipticEst.TT.EllWeakPos α 0
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) F)
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) Ψ) :=
      Work.FTS.EllipticEst.Cores.pPureShiftAux.EllWeakPos_dqq h hFmem hAmem hBmem (hc1 n)
        (HkMem_diag_dqq h (hc1 n))
    have hE := hC₀ α (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) F)
      (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) Ψ) hα hα4 hcls
    rw [hslotA n, hslotB n] at hE
    have hsrc : Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) F)
        ≤ (c n) ^ 6 * X := by
      rw [hXdef]
      exact Work.FTS.EllipticEst.Cores.pPureShiftAux.HkSq_dqq_le hSF hSF.Dz hFmem (hc1 n)
    calc α ^ 4 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) A)
          + Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) B)
        ≤ C₀ * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) F) := hE
      _ ≤ C₀ * ((c n) ^ 6 * X) := mul_le_mul_of_nonneg_left hsrc (le_of_lt hC₀pos)
      _ = C₀ * (c n) ^ 6 * X := by ring
  -- the tail bound on the dilation constants
  have htail : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in Filter.atTop, C₀ * (c n) ^ 6 * X ≤ C₀ * X + δ := fun δ hδ => by
    have hev := hpow.eventually (isOpen_Iio.mem_nhds
      (show (1 : ℝ) ∈ Set.Iio (1 + δ / (C₀ * X + 1)) from by
        rw [Set.mem_Iio]
        have : 0 < δ / (C₀ * X + 1) := by positivity
        linarith))
    filter_upwards [hev] with n hn
    have h1 : (c n) ^ 6 ≤ 1 + δ / (C₀ * X + 1) := le_of_lt hn
    have hden : 0 < C₀ * X + 1 := by nlinarith [hC₀pos, hXnn]
    have h2 : C₀ * X * (δ / (C₀ * X + 1)) ≤ δ := by
      have hle : (C₀ * X) / (C₀ * X + 1) ≤ 1 := by
        rw [div_le_iff₀ hden]
        linarith
      calc C₀ * X * (δ / (C₀ * X + 1)) = ((C₀ * X) / (C₀ * X + 1)) * δ := by ring
        _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hle (le_of_lt hδ)
        _ = δ := by ring
    have h3 : C₀ * (c n) ^ 6 * X ≤ C₀ * X * (1 + δ / (C₀ * X + 1)) := by
      have h1' : C₀ * X * (c n) ^ 6 ≤ C₀ * X * (1 + δ / (C₀ * X + 1)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hC₀pos.le hXnn)
      calc C₀ * (c n) ^ 6 * X = C₀ * X * (c n) ^ 6 := by ring
        _ ≤ C₀ * X * (1 + δ / (C₀ * X + 1)) := h1'
    have h4 : C₀ * X * (1 + δ / (C₀ * X + 1))
        = C₀ * X + C₀ * X * (δ / (C₀ * X + 1)) := by ring
    linarith [h2, h3, h4]
  -- Fatou along `c → 1⁺`: the `A`-slot
  have hFatouA : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz A)) ≤ C₀ * X := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hα4pos : 0 < α ^ 4 := by positivity
    have hbound := htail δ hδ
    have hmeasn : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) A)
          p.1 p.2))
        (Work.FTS.EllipticEst.Cores.Dil.quadMeasure) := fun n =>
      Work.FTS.EllipticEst.Cores.Dil.aemeasurable_ofReal_HkIntegrand_of_continuousOn
        ((Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq
          (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hSA (hcpos n)) (hcpos n))
          |>.continuousOn_HkIntegrand α 0)
    have hmeasv : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz A)) p.1 p.2))
        (Work.FTS.EllipticEst.Cores.Dil.quadMeasure) :=
      Work.FTS.EllipticEst.Cores.Dil.aemeasurable_ofReal_HkIntegrand_of_continuousOn
        ((hSA.Dz.Dz).continuousOn_HkIntegrand α 0)
    have hmemn : ∀ n : ℕ, Work.Spaces.HkMem α 0
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) A) := fun n =>
      Work.FTS.EllipticEst.Cores.pPureShiftAux.HkMem_dqq hSA hSA.Dz hAmem (hc1 n)
    have hmemv : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz A)) := hAmem
    have hae : ∀ᵐ p ∂(Work.FTS.EllipticEst.Cores.Dil.quadMeasure),
        Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) A p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.Dz (Work.Spaces.Dz A) p.1 p.2)) := by
      refine Work.FTS.EllipticEst.Cores.pPureShiftAux.ae_mem_Q0.mono fun p hp => ?_
      simpa only [Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq, Function.comp_def] using
        (Work.FTS.EllipticEst.Cores.Dil.tendsto_dqq_DzDz hSA hp.1 ⟨hp.2.1, hp.2.2⟩).comp hctend'
    have hy : ∀ᶠ n : ℕ in Filter.atTop, Work.Spaces.HkSq α 0
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) A) ≤ (C₀ * X + δ) / α ^ 4 := by
      filter_upwards [hbound] with n hn
      have h2 : (0 : ℝ) ≤ Work.Spaces.HkSq α 0
          (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) B) :=
        Work.Spaces.HkSq_nonneg α 0 _
      have h3 : α ^ 4 * Work.Spaces.HkSq α 0
          (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) A) ≤ C₀ * (c n) ^ 6 * X := by
        linarith [hest n]
      rw [le_div_iff₀ hα4pos]
      nlinarith [h3, hn]
    have hfat := Work.FTS.EllipticEst.Cores.Dil.HkSq_zero_le_of_eventually_le
      hmeasn hmeasv hmemn hmemv hae hy
    calc α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz A))
        ≤ α ^ 4 * ((C₀ * X + δ) / α ^ 4) := mul_le_mul_of_nonneg_left hfat (by positivity)
      _ = C₀ * X + δ := by
          rw [mul_div_assoc']
          exact mul_div_cancel_left₀ _ (ne_of_gt hα4pos)
  -- Fatou along `c → 1⁺`: the `B`-slot
  have hFatouB : Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz B)) ≤ C₀ * X := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hbound := htail δ hδ
    have hmeasn : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) B)
          p.1 p.2))
        (Work.FTS.EllipticEst.Cores.Dil.quadMeasure) := fun n =>
      Work.FTS.EllipticEst.Cores.Dil.aemeasurable_ofReal_HkIntegrand_of_continuousOn
        ((Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq
          (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hSB (hcpos n)) (hcpos n))
          |>.continuousOn_HkIntegrand α 0)
    have hmeasv : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz B)) p.1 p.2))
        (Work.FTS.EllipticEst.Cores.Dil.quadMeasure) :=
      Work.FTS.EllipticEst.Cores.Dil.aemeasurable_ofReal_HkIntegrand_of_continuousOn
        ((hSB.Dz.Dz).continuousOn_HkIntegrand α 0)
    have hmemn : ∀ n : ℕ, Work.Spaces.HkMem α 0
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) B) := fun n =>
      Work.FTS.EllipticEst.Cores.pPureShiftAux.HkMem_dqq hSB hSB.Dz hBmem (hc1 n)
    have hmemv : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz B)) := hBmem
    have hae : ∀ᵐ p ∂(Work.FTS.EllipticEst.Cores.Dil.quadMeasure),
        Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) B p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.Dz (Work.Spaces.Dz B) p.1 p.2)) := by
      refine Work.FTS.EllipticEst.Cores.pPureShiftAux.ae_mem_Q0.mono fun p hp => ?_
      simpa only [Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq, Function.comp_def] using
        (Work.FTS.EllipticEst.Cores.Dil.tendsto_dqq_DzDz hSB hp.1 ⟨hp.2.1, hp.2.2⟩).comp hctend'
    have hy : ∀ᶠ n : ℕ in Filter.atTop, Work.Spaces.HkSq α 0
        (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) B) ≤ C₀ * X + δ := by
      filter_upwards [hbound] with n hn
      have h2 : (0 : ℝ) ≤ α ^ 4 * Work.Spaces.HkSq α 0
          (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) A) :=
        mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
      have h3 : Work.Spaces.HkSq α 0
          (Work.FTS.EllipticEst.Cores.pPureShiftAux.dqq (c n) B) ≤ C₀ * (c n) ^ 6 * X := by
        linarith [hest n]
      linarith [h3, hn]
    exact Work.FTS.EllipticEst.Cores.Dil.HkSq_zero_le_of_eventually_le
      hmeasn hmeasv hmemn hmemv hae hy
  -- assembly
  have hDzIter : ∀ u : ℝ → ℝ → ℝ, Work.Spaces.DzIter 2 u = Work.Spaces.Dz (Work.Spaces.Dz u) :=
    fun u => rfl
  calc α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 A)
      + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 B)
      = α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz A))
        + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz B)) := by
        rw [hDzIter A, hDzIter B]
    _ ≤ C₀ * X + C₀ * X := add_le_add hFatouA hFatouB
    _ = 2 * C₀ * X := by ring

end

end Work.FTS.EllipticEst.Cores
