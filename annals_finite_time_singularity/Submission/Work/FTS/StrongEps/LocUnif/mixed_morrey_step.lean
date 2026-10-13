import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongLWP.Sobolev.holder_half_of_W22
import Submission.Work.FTS.StrongLWP.Sobolev.EqcProduct
import Submission.Work.FTS.StrongLWP.Sobolev.EqcBasis
import Submission.Work.FTS.StrongLWP.Sobolev.EqcBasic
import Submission.Work.FTS.StrongEps.LocUnif.basis_apply_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem mixed_morrey_step {χ : ℝ × ℝ → ℝ} {F : ℝ → ℝ → ℝ} {α C C₀ M Km : ℝ}
    {a b c d a' b' c' d' : ℝ}
    (hmor : ∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      ∀ p q : ℝ × ℝ, |v p - v q| ≤ Km * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
        + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * dist p q ^ (1 / 2 : ℝ))
    (hKmnn : 0 ≤ Km) (hα : 0 < α) (hC₀nn : 0 ≤ C₀) (hCpos : 0 < C)
    (hχC2 : ContDiff ℝ 2 χ) (hχcs : HasCompactSupport χ) (hχnn : ∀ x, 0 ≤ χ x)
    (hχle1 : ∀ x, χ x ≤ 1)
    (hχone : ∀ z, z ∈ Set.Icc a b → ∀ θ, θ ∈ Set.Icc c d → χ (z, θ) = 1)
    (hχzero : ∀ x, x ∉ Set.Icc a' b' ×ˢ Set.Icc c' d' → χ x = 0)
    (hMfd1 : ∀ x, ‖fderiv ℝ χ x‖ ≤ M) (hMfd2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M)
    (hsub : Set.Icc a' b' ×ˢ Set.Icc c' d' ⊆ Work.FTS.EllipticEst.Q0)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F) (hFmem : Work.Spaces.HkMem α 6 F)
    (hFbd : Work.Spaces.HkNorm α 6 F ≤ C₀)
    (hrect : ∀ (j i : ℕ), j + i ≤ 4 →
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.mixed j i F z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F)) :
    ∀ (j i : ℕ), j + i ≤ 4 → ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c d,
        |Work.Spaces.mixed j i F p.1 p.2 - Work.Spaces.mixed j i F q.1 q.2|
          ≤ (Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀)) * dist p q ^ (1 / 2 : ℝ) := by
  intro j i hji p hp q hq
  have hisOpen : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  -- the uncurried slot and the rectangle
  set G : ℝ × ℝ → ℝ := Function.uncurry (Work.Spaces.mixed j i F) with hGdef
  set s : Set (ℝ × ℝ) := Set.Icc a' b' ×ˢ Set.Icc c' d' with hsdef
  have hsc : IsClosed s := isClosed_Icc.prod isClosed_Icc
  have hscm : MeasurableSet s := hsc.measurableSet
  have hkomp : IsCompact s := isCompact_Icc.prod isCompact_Icc
  -- `G` is `C²` on the open quadrant
  have hG2 : ContDiffOn ℝ 2 G Work.FTS.EllipticEst.Q0 := by
    have h := (hFsm.mixed j i).of_le two_le_smoothOrder
    simpa only [hGdef] using h
  have hG1 : ContDiffOn ℝ 1 G Work.FTS.EllipticEst.Q0 := hG2.of_le (by norm_num)
  have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ G) Work.FTS.EllipticEst.Q0 :=
    hG2.fderiv_of_isOpen hisOpen (by norm_num)
  -- integrability on the rectangle, from continuity
  have hI0 : IntegrableOn (fun x : ℝ × ℝ => (G x) ^ 2) s :=
    ((hG2.continuousOn.mono hsub).pow 2).integrableOn_compact hkomp
  have hI1 : IntegrableOn (fun x : ℝ × ℝ => ‖fderiv ℝ G x‖ ^ 2) s := by
    have hcont := (hfd1.continuousOn.mono hsub).norm.pow 2
    exact hcont.integrableOn_compact hkomp
  -- the four basis entries of `D²G`, as functions of the point, and their sum `E`
  set A : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pzIter 2 (Work.Spaces.mixed j i F) x.1 x.2 with hAdef
  set B : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) x.1 x.2 with hBdef
  set Cc : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) x.1 x.2 with hCcdef
  set D : ℝ × ℝ → ℝ :=
    fun x => Work.Spaces.pthIter 2 (Work.Spaces.mixed j i F) x.1 x.2 with hDdef
  set E : ℝ × ℝ → ℝ := fun x => ‖A x‖ + ‖B x‖ + ‖Cc x‖ + ‖D x‖ with hEdef
  have hI2 : IntegrableOn (fun x : ℝ × ℝ => E x ^ 2) s := by
    have hAc := (((hFsm.mixed j i).pz).pz).continuousOn
    have hBc := (((hFsm.mixed j i).pth).pz).continuousOn
    have hCc' := (((hFsm.mixed j i).pz).pth).continuousOn
    have hDc := (((hFsm.mixed j i).pth).pth).continuousOn
    have hE := ((((hAc.norm.add hBc.norm).add hCc'.norm).add hDc.norm)).mono hsub
    exact (hE.pow 2).integrableOn_compact hkomp
  have hIA : IntegrableOn (fun x : ℝ × ℝ => (A x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pz).pz).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  have hIB : IntegrableOn (fun x : ℝ × ℝ => (B x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pth).pz).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  have hIC : IntegrableOn (fun x : ℝ × ℝ => (Cc x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pz).pth).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  have hID : IntegrableOn (fun x : ℝ × ℝ => (D x) ^ 2) s := by
    have hcont := (((hFsm.mixed j i).pth).pth).continuousOn.mono hsub
    exact (hcont.pow 2).integrableOn_compact hkomp
  -- `E` dominates the operator norm of the second derivative
  have hEbd : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ E x := by
    intro x hx
    have hxQ : x ∈ Work.FTS.EllipticEst.Q0 := hsub hx
    have h := norm_fderiv_fderiv_le_basis (G := Work.Spaces.mixed j i F) hisOpen hG2 hxQ
    simpa only [hEdef, hAdef, hBdef, hCcdef, hDdef, Real.norm_eq_abs,
      Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h
  -- the rectangle bounds of the hypothesis
  obtain ⟨hmix, hpz1, hpth1, hpz2, hpzpth, hpthpz, hpth2⟩ := hrect j i hji
  -- the `L²`-bound of the slot itself on the rectangle
  have hAg : ∫ x in s, (G x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have hr : ∫ x in s, (G x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d', (Work.Spaces.mixed j i F z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := G)
        (a := a') (b := b') (c := c') (d := d') hI0
      simpa only [hGdef, Function.uncurry] using h
    rw [hr]; exact hmix
  -- the `L²`-bound of the four second basis entries
  have hA2 : ∫ x in s, (A x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have heq : ∫ x in s, (A x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pzIter 2 (Work.Spaces.mixed j i F) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := A)
        (a := a') (b := b') (c := c') (d := d') hIA
      simpa only [hAdef] using h
    rw [heq]
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hpz2
  have hB2 : ∫ x in s, (B x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have heq : ∫ x in s, (B x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := B)
        (a := a') (b := b') (c := c') (d := d') hIB
      simpa only [hBdef] using h
    rw [heq]; exact hpzpth
  have hC2 : ∫ x in s, (Cc x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have heq : ∫ x in s, (Cc x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := Cc)
        (a := a') (b := b') (c := c') (d := d') hIC
      simpa only [hCcdef] using h
    rw [heq]; exact hpthpz
  have hD2 : ∫ x in s, (D x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F := by
    have heq : ∫ x in s, (D x) ^ 2
        = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
            (Work.Spaces.pthIter 2 (Work.Spaces.mixed j i F) z θ) ^ 2 := by
      have h := Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq (f := D)
        (a := a') (b := b') (c := c') (d := d') hID
      simpa only [hDdef] using h
    rw [heq]
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hpth2
  -- hence `∫_s E² ≤ 16 C |F|²`
  have hE2 : ∫ x in s, E x ^ 2 ≤ 16 * C * Work.Spaces.HkSq α 6 F := by
    have hpt : ∀ x ∈ s, E x ^ 2
        ≤ 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) := by
      intro x hx
      have h := Work.FTS.StrongLWP.Sobolev.eqc_sq_add4_le ‖A x‖ ‖B x‖ ‖Cc x‖ ‖D x‖
      simpa only [hEdef, Real.norm_eq_abs, sq_abs] using h
    have h12 : IntegrableOn (fun x : ℝ × ℝ => (A x) ^ 2 + (B x) ^ 2) s := hIA.add hIB
    have h123 : IntegrableOn (fun x : ℝ × ℝ => (A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2) s :=
      h12.add hIC
    have h1234 : IntegrableOn (fun x : ℝ × ℝ =>
        (A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) s := h123.add hID
    have hInt : IntegrableOn (fun x : ℝ × ℝ =>
        4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)) s := h1234.const_mul 4
    have hmono : ∫ x in s, E x ^ 2
        ≤ ∫ x in s, 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hInt
        (ae_restrict_of_forall_mem hscm hpt)
    have sA : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2) = (∫ x in s, (A x) ^ 2) + ∫ x in s, (B x) ^ 2 :=
      integral_add hIA hIB
    have sB : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2)
        = (∫ x in s, ((A x) ^ 2 + (B x) ^ 2)) + ∫ x in s, (Cc x) ^ 2 :=
      integral_add h12 hIC
    have sC : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)
        = (∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2)) + ∫ x in s, (D x) ^ 2 :=
      integral_add h123 hID
    have sD : ∫ x in s, 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)
        = 4 * ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) :=
      integral_const_mul 4 _
    have hsum4 : ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2)
        ≤ (((C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F)
            + C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F := by
      rw [sC, sB, sA]
      linarith [hA2, hB2, hC2, hD2]
    calc ∫ x in s, E x ^ 2
        ≤ ∫ x in s, 4 * ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) := hmono
      _ = 4 * ∫ x in s, ((A x) ^ 2 + (B x) ^ 2 + (Cc x) ^ 2 + (D x) ^ 2) := sD
      _ ≤ 4 * ((((C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F)
            + C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F) :=
          mul_le_mul_of_nonneg_left hsum4 (by norm_num)
      _ = 16 * C * Work.Spaces.HkSq α 6 F := by ring
  -- the `L²`-bound of the first derivative
  have hD1 : ∫ x in s, ‖fderiv ℝ G x‖ ^ 2 ≤ 4 * C * Work.Spaces.HkSq α 6 F := by
    have hpt : ∀ x ∈ s, ‖fderiv ℝ G x‖ ^ 2
        ≤ 2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
            + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) := by
      intro x hx
      have hxQ : x ∈ Work.FTS.EllipticEst.Q0 := hsub hx
      have hdiff : DifferentiableAt ℝ G x :=
        (hG2.contDiffAt (hisOpen.mem_nhds hxQ)).differentiableAt (by norm_num)
      have e1 : (fderiv ℝ G x) (1, 0)
          = Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2 :=
        (Work.Spaces.pz_eq_fderiv (G := Work.Spaces.mixed j i F) hdiff).symm
      have e2 : (fderiv ℝ G x) (0, 1)
          = Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2 :=
        (Work.Spaces.pth_eq_fderiv (G := Work.Spaces.mixed j i F) hdiff).symm
      have hop := Work.FTS.StrongLWP.Sobolev.eqc_opNorm_le_basis_sum (fderiv ℝ G x)
      rw [e1, e2, Real.norm_eq_abs, Real.norm_eq_abs] at hop
      have h1 : ‖fderiv ℝ G x‖ ^ 2
          ≤ (|Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2|
              + |Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hop 2
      have h2 := Work.FTS.StrongLWP.Sobolev.eqc_sq_add2_le
        |Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2|
        |Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2|
      rw [sq_abs, sq_abs] at h2
      exact h1.trans h2
    have hIpz : IntegrableOn (fun x : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) s := by
      have hcont := ((hFsm.mixed j i).pz).continuousOn.mono hsub
      exact (hcont.pow 2).integrableOn_compact hkomp
    have hIpth : IntegrableOn (fun x : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) s := by
      have hcont := ((hFsm.mixed j i).pth).continuousOn.mono hsub
      exact (hcont.pow 2).integrableOn_compact hkomp
    have hInt : IntegrableOn (fun x : ℝ × ℝ =>
        2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)) s :=
      (hIpz.add hIpth).const_mul 2
    have hzp : ∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F := by
      have heq : ∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
              (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 :=
        Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq
          (f := Function.uncurry (Work.Spaces.pz (Work.Spaces.mixed j i F)))
          (a := a') (b := b') (c := c') (d := d') hIpz
      rw [heq]; exact hpz1
    have hthp : ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F := by
      have heq : ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          = ∫ z in Set.Icc a' b', ∫ θ in Set.Icc c' d',
              (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 :=
        Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq
          (f := Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed j i F)))
          (a := a') (b := b') (c := c') (d := d') hIpth
      rw [heq]; exact hpth1
    have hIpzth : IntegrableOn (fun x : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) s := hIpz.add hIpth
    have sA : ∫ x in s, ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
        = (∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
          + ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2 :=
      integral_add hIpz hIpth
    have sB : ∫ x in s, 2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
        = 2 * ∫ x in s, ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
          + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) :=
      integral_const_mul 2 _
    calc ∫ x in s, ‖fderiv ℝ G x‖ ^ 2
        ≤ ∫ x in s, 2 * ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
            + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hInt
            (ae_restrict_of_forall_mem hscm hpt)
      _ = 2 * ∫ x in s, ((Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2
            + (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) := sB
      _ = 2 * ((∫ x in s, (Work.Spaces.pz (Work.Spaces.mixed j i F) x.1 x.2) ^ 2)
            + ∫ x in s, (Work.Spaces.pth (Work.Spaces.mixed j i F) x.1 x.2) ^ 2) := by rw [sA]
      _ ≤ 2 * ((C * Work.Spaces.HkSq α 6 F) + C * Work.Spaces.HkSq α 6 F) := by
          linarith [hzp, hthp]
      _ = 4 * C * Work.Spaces.HkSq α 6 F := by ring
  -- the cutoff product
  have hv2 : ContDiff ℝ 2 (fun x : ℝ × ℝ => χ x * G x) :=
    contDiff_two_mul_of_contDiffOn_two hsc hsub hisOpen hχC2 hχzero hG2
  have hvcs : HasCompactSupport (fun x : ℝ × ℝ => χ x * G x) :=
    Work.FTS.StrongLWP.Sobolev.eqc_hasCompactSupport_mul (χ := χ) (g := G) hχcs
  -- Morrey's inequality for `χ · G`
  have hm := hmor (fun x : ℝ × ℝ => χ x * G x) hv2 hvcs p q
  -- the two `L²`-norms appearing in Morrey's inequality
  have hA : ∫ x : ℝ × ℝ, (χ x * G x) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F :=
    (Work.FTS.StrongLWP.Sobolev.eqc_integral_mul_sq_le hχzero hχle1 hχnn hscm hI0).trans hAg
  have hB : ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2
      ≤ 3 * C * (16 + 17 * M ^ 2) * Work.Spaces.HkSq α 6 F := by
    have hM0 : ∀ x : ℝ × ℝ, ‖χ x‖ ≤ 1 := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχnn x)]; exact hχle1 x
    have hgd : ∀ y ∈ Work.FTS.EllipticEst.Q0, DifferentiableAt ℝ G y := fun y hy =>
      (hG2.contDiffAt (hisOpen.mem_nhds hy)).differentiableAt (by norm_num)
    have hgd2 : ∀ y ∈ Work.FTS.EllipticEst.Q0, DifferentiableAt ℝ (fderiv ℝ G) y := fun y hy =>
      (hfd1.contDiffAt (hisOpen.mem_nhds hy)).differentiableAt (by norm_num)
    have hbd := Work.FTS.StrongLWP.Sobolev.eqc_integral_fderiv_fderiv_mul_sq_le
      (χ := χ) (g := G) (s := s) (U := Work.FTS.EllipticEst.Q0)
      (M0 := 1) (M1 := M) (M2 := M) (E := E)
      hχC2 hsc hχzero hM0 hMfd1 hMfd2 hisOpen hsub hgd hgd2 hEbd hI0 hI1 hI2
    have hstep : 3 * (1 ^ 2 * (∫ x in s, E x ^ 2)
          + (2 * M) ^ 2 * (∫ x in s, ‖fderiv ℝ G x‖ ^ 2)
          + M ^ 2 * (∫ x in s, (G x) ^ 2))
        ≤ 3 * (1 ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F)
          + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F)
          + M ^ 2 * (C * Work.Spaces.HkSq α 6 F)) := by
      have a1 := mul_le_mul_of_nonneg_left hE2 (by norm_num : (0 : ℝ) ≤ 1 ^ 2)
      have a2 := mul_le_mul_of_nonneg_left hD1 (sq_nonneg (2 * M))
      have a3 := mul_le_mul_of_nonneg_left hAg (sq_nonneg M)
      linarith
    calc ∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2
        ≤ 3 * (1 ^ 2 * (∫ x in s, E x ^ 2)
            + (2 * M) ^ 2 * (∫ x in s, ‖fderiv ℝ G x‖ ^ 2)
            + M ^ 2 * (∫ x in s, (G x) ^ 2)) := hbd
      _ ≤ 3 * (1 ^ 2 * (16 * C * Work.Spaces.HkSq α 6 F)
            + (2 * M) ^ 2 * (4 * C * Work.Spaces.HkSq α 6 F)
            + M ^ 2 * (C * Work.Spaces.HkSq α 6 F)) := hstep
      _ = 3 * C * (16 + 17 * M ^ 2) * Work.Spaces.HkSq α 6 F := by ring
  -- the square-root comparison
  have hCnn : 0 ≤ C := le_of_lt hCpos
  have hQnn : 0 ≤ 3 * C * (16 + 17 * M ^ 2) := by positivity
  have hsum : Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
        + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2)
      ≤ 2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ := by
    have hs1 : Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
        ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ := by
      calc Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
          ≤ Real.sqrt (C * Work.Spaces.HkSq α 6 F) := Real.sqrt_le_sqrt hA
        _ = Real.sqrt C * Real.sqrt (Work.Spaces.HkSq α 6 F) := Real.sqrt_mul hCnn _
        _ ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ :=
            mul_le_mul (Real.sqrt_le_sqrt (by linarith [hQnn])) hFbd
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hs2 : Real.sqrt (∫ x : ℝ × ℝ,
          ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2)
        ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ := by
      calc Real.sqrt (∫ x : ℝ × ℝ,
            ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2)
          ≤ Real.sqrt (3 * C * (16 + 17 * M ^ 2) * Work.Spaces.HkSq α 6 F) :=
            Real.sqrt_le_sqrt hB
        _ = Real.sqrt (3 * C * (16 + 17 * M ^ 2)) * Real.sqrt (Work.Spaces.HkSq α 6 F) :=
            Real.sqrt_mul hQnn _
        _ ≤ Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀ :=
            mul_le_mul (Real.sqrt_le_sqrt (by linarith [hCnn])) hFbd
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  -- the values at `p` and `q` inside the inner rectangle
  have hGp : G p = Work.Spaces.mixed j i F p.1 p.2 := rfl
  have hGq : G q = Work.Spaces.mixed j i F q.1 q.2 := rfl
  have hχp : χ p = 1 := hχone p.1 hp.1 p.2 hp.2
  have hχq : χ q = 1 := hχone q.1 hq.1 q.2 hq.2
  have hvp : (fun x : ℝ × ℝ => χ x * G x) p = Work.Spaces.mixed j i F p.1 p.2 := by
    simp only [hχp, hGp, one_mul]
  have hvq : (fun x : ℝ × ℝ => χ x * G x) q = Work.Spaces.mixed j i F q.1 q.2 := by
    simp only [hχq, hGq, one_mul]
  -- assemble
  have hd0 : 0 ≤ dist p q ^ (1 / 2 : ℝ) := Real.rpow_nonneg dist_nonneg _
  have hfin : |(fun x : ℝ × ℝ => χ x * G x) p - (fun x : ℝ × ℝ => χ x * G x) q|
      ≤ (Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀)) * dist p q ^ (1 / 2 : ℝ) := by
    calc |(fun x : ℝ × ℝ => χ x * G x) p - (fun x : ℝ × ℝ => χ x * G x) q|
        ≤ Km * (Real.sqrt (∫ x : ℝ × ℝ, (χ x * G x) ^ 2)
            + Real.sqrt (∫ x : ℝ × ℝ,
                ‖fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => χ x * G x)) x‖ ^ 2))
          * dist p q ^ (1 / 2 : ℝ) := hm
      _ ≤ Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀)
            * dist p q ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hKmnn) hd0
  rw [hvp, hvq] at hfin
  exact hfin

end Work.FTS.StrongEps.LocUnif
