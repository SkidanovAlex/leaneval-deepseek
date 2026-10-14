import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeI1_fts
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_bnd
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

open Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The quadratic solve -/

/-- `X² ≤ K(NX + N²)` with `K, N ≥ 0` gives `X ≤ (K+1)N`. -/
private theorem quad_solve {K X N : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
    (h : X ^ 2 ≤ K * (N * X + N ^ 2)) : X ≤ (K + 1) * N := by
  by_cases hX : X ≤ 0
  · nlinarith
  · push_neg at hX
    by_cases hN0 : N = 0
    · subst hN0
      have h2 : X ^ 2 ≤ 0 := by simpa using h
      have h3 : X = 0 := sq_eq_zero_iff.mp (le_antisymm h2 (sq_nonneg X))
      rw [h3]; simp
    · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hN0)
      by_contra hcon
      push_neg at hcon
      have h1 : 0 < (X - (K + 1) * N) * N := mul_pos (by linarith) hNpos
      nlinarith [hcon, hK, h1, h]

/-! ## The assembly of Step 2 from the four inputs -/

/-- **Step 2 of `prop:H2` in the class `AeData`, from the four inputs.**

The inputs are, in order: the honesty of `u`; the honesty of `z∂_zu` (from the honesty of `u` and
the radial Agmon–Nirenberg interpolation); the `u`-half of Step 1, i.e. `‖u‖_ρ ≤ C‖G‖_ρ`; the `I₁`
lower bound; and the `I₄` bound `IP (∂_θ(tan θ·u)) B ≤ IP u B + C IP u u`. -/
theorem step2Ae_core
    (hmem : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → Work.Spaces.HkMem α 0 u)
    (hgrad : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → Work.Spaces.HkMem α 0 u →
      Work.Spaces.HkMem α 0 (grad u))
    (hbnd : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      Work.Spaces.HkMem α 0 u → nrm α u ≤ C * nrm α G)
    (hI1 : Work.FTS.EllipticEst.AngAWeak.AeI1)
    (hI4 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      Work.Spaces.HkMem α 0 u → Work.Spaces.HkMem α 0 (grad u) →
      Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
          (Work.Spaces.pthIter 2 u)
        ≤ Work.FTS.EllipticEst.AngSecond.IP u (Work.Spaces.pthIter 2 u)
          + C * Work.FTS.EllipticEst.AngSecond.IP u u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      nrm α (ang2 u) ≤ C * (nrm α G + α * nrm α (grad u)) := by
  obtain ⟨Cb, hCb, hbb⟩ := hbnd
  obtain ⟨C4, hC4, h4b⟩ := hI4
  obtain ⟨C1, hC1, h1b⟩ := hI1
  have hK0 : (0 : ℝ) ≤ C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1) := by
    nlinarith [hC1, hC4, hCb]
  refine ⟨C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1) + 1, by linarith, ?_⟩
  intro α u G hA
  have hα : 0 < α := hA.hα
  have hα4 : α ≤ 1 / 4 := hA.hα4
  have hmu : Work.Spaces.HkMem α 0 u := hmem α u G hA
  have hmuU : Work.Spaces.HkMem α 0 (grad u) := hgrad α u G hA hmu
  have hmems := (Work.FTS.EllipticEst.remov.aeIPMemsSlim :
    Work.FTS.EllipticEst.AngAWeak.AeIPMems) α u G hA hmu hmuU
  obtain ⟨hFmem, hQmem, hUmem, hG1mem, humem, hBmem⟩ := hmems
  have huumem : Work.FTS.EllipticEst.AngSecond.IPMem u u :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmu
  have hUUmem : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => z * Work.Spaces.pz u z θ) (fun z θ => z * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmuU
  have hGGmem : Work.FTS.EllipticEst.AngSecond.IPMem G G :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hA.memG
  -- abbreviations
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u with hBdef
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ with hQdef
  set U : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ with hUdef
  set G₁ : ℝ → ℝ → ℝ :=
    fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ with hG₁def
  set f : ℝ := nrm α G with hfdef
  set b : ℝ := nrm α U with hbdef
  set X : ℝ := nrm α B with hXdef
  set m : ℝ := nrm α u with hmdef
  set N : ℝ := f + α * b with hNdef
  have hf0 : 0 ≤ f := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  -- ## `HkSq` versus the honest `IP`-pairing
  have hb2 : b ^ 2 = Work.FTS.EllipticEst.AngSecond.IP U U := by
    rw [hbdef, hUdef, nrm, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hX2 : X ^ 2 = Work.FTS.EllipticEst.AngSecond.IP B B := by
    rw [hXdef, hBdef, nrm, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hf2 : f ^ 2 = Work.FTS.EllipticEst.AngSecond.IP G G := by
    rw [hfdef, nrm, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hm2 : m ^ 2 = Work.FTS.EllipticEst.AngSecond.IP u u := by
    rw [hmdef, nrm, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hXeq : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) = X := by
    rw [← hX2]; exact Real.sqrt_sq hX0
  have hbeq : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U) = b := by
    rw [← hb2]; exact Real.sqrt_sq hb0
  have hfeq : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP G G) = f := by
    rw [← hf2]; exact Real.sqrt_sq hf0
  have hmeq : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP u u) = m := by
    rw [← hm2]; exact Real.sqrt_sq hm0
  -- ## the identity, and Cauchy–Schwarz
  have hid := Work.FTS.EllipticEst.AngAWeak.I_identity_weak α G u hA.eq
    hFmem hQmem hUmem hG1mem humem hBmem
  have hcsG := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz hGGmem hBmem hFmem
  have hcsU := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz hUUmem hBmem hUmem
  have hcsu := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz huumem hBmem humem
  -- ## the five bounds
  have e1 : -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
      ≤ C1 * (α ^ 2 * b ^ 2) + C1 * ((α ^ 2 * b) * X) := by
    have h := h1b α u G hA hmuU
    rw [hbeq, hXeq, ← hb2] at h
    linarith [h]
  have e2 : -α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
      ≤ (5 + α) * ((α * b) * X) := by
    have h := (abs_le.mp hcsU).1
    rw [hbeq, hXeq] at h
    have h5 : 0 ≤ α * (5 + α) := by nlinarith [hα]
    nlinarith [h, h5, hb0, hX0]
  have e4 : Work.FTS.EllipticEst.AngSecond.IP G₁ B ≤ m * X + C4 * m ^ 2 := by
    have h := h4b α u G hA hmu hmuU
    have hcs : Work.FTS.EllipticEst.AngSecond.IP u B ≤ m * X := by
      have h2 := (abs_le.mp hcsu).2
      rw [hmeq, hXeq] at h2
      linarith [h2]
    rw [← hm2] at h
    linarith [h, hcs]
  have e5 : -6 * Work.FTS.EllipticEst.AngSecond.IP u B ≤ 6 * (m * X) := by
    have h := (abs_le.mp hcsu).1
    rw [hmeq, hXeq] at h
    linarith [h]
  have e6 : -Work.FTS.EllipticEst.AngSecond.IP G B ≤ f * X := by
    have h := (abs_le.mp hcsG).1
    rw [hfeq, hXeq] at h
    linarith [h]
  -- ## the identity, solved for the pairing of `∂_θθu` with itself
  have hid' : Work.FTS.EllipticEst.AngSecond.IP B B
      = -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
        - α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
        + Work.FTS.EllipticEst.AngSecond.IP G₁ B
        - 6 * Work.FTS.EllipticEst.AngSecond.IP u B
        - Work.FTS.EllipticEst.AngSecond.IP G B := by
    rw [← hBdef, ← hQdef, ← hUdef, ← hG₁def] at hid
    linarith [hid]
  -- ## the Step-1 bound on `u`
  have hmb : m ≤ Cb * f := by
    have h := hbb α u G hA hmu
    rw [hmdef, hfdef]
    exact h
  -- ## the elementary consequences of the abbreviations
  have hNf : f ≤ N := by rw [hNdef]; nlinarith [hb0, hα.le]
  have hNb : α * b ≤ N := by rw [hNdef]; nlinarith [hf0]
  have hαb2 : α ^ 2 * b ^ 2 ≤ N ^ 2 := by nlinarith [hNb, hα, hb0, hN0]
  have hαbX : (α ^ 2 * b) * X ≤ N * X := by
    have h1 : α ^ 2 * b ≤ N := by
      have h2 : α ^ 2 * b = α * (α * b) := by ring
      rw [h2]
      calc α * (α * b) ≤ α * N := mul_le_mul_of_nonneg_left hNb hα.le
        _ ≤ 1 * N := by
            have h3 : α ≤ 1 := by linarith
            exact mul_le_mul_of_nonneg_right h3 hN0
        _ = N := by ring
    exact mul_le_mul_of_nonneg_right h1 hX0
  have h5bb : (5 + α) * ((α * b) * X) ≤ (21 / 4) * (N * X) := by
    have h1 : 5 + α ≤ 21 / 4 := by linarith
    have h2 : 0 ≤ (α * b) * X := by positivity
    have h3 : (α * b) * X ≤ N * X := mul_le_mul_of_nonneg_right hNb hX0
    calc (5 + α) * ((α * b) * X) ≤ (21 / 4) * ((α * b) * X) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ (21 / 4) * (N * X) := mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hmX : m * X ≤ (Cb * N) * X := by
    have h2 : Cb * f ≤ Cb * N := mul_le_mul_of_nonneg_left hNf hCb.le
    exact mul_le_mul_of_nonneg_right (le_trans hmb h2) hX0
  have hm2N : m ^ 2 ≤ (Cb * N) ^ 2 := by
    have h1 : m ≤ Cb * N := le_trans hmb (mul_le_mul_of_nonneg_left hNf hCb.le)
    nlinarith [h1, hm0, hCb, hN0]
  have hfX : f * X ≤ N * X := mul_le_mul_of_nonneg_right hNf hX0
  -- ## the collection
  have hkey : X ^ 2 ≤ (C1 + C4 * Cb ^ 2) * N ^ 2
      + (C1 + 21 / 4 + Cb + 6 * Cb + 1) * (N * X) := by
    have hsum : X ^ 2 ≤ C1 * (α ^ 2 * b ^ 2) + C1 * ((α ^ 2 * b) * X)
        + (5 + α) * ((α * b) * X) + (m * X + C4 * m ^ 2) + 6 * (m * X) + f * X := by
      rw [hX2, hid']
      linarith [e1, e2, e4, e5, e6]
    have t1 : C1 * (α ^ 2 * b ^ 2) ≤ C1 * N ^ 2 := mul_le_mul_of_nonneg_left hαb2 hC1.le
    have t2 : C1 * ((α ^ 2 * b) * X) ≤ C1 * (N * X) := mul_le_mul_of_nonneg_left hαbX hC1.le
    have t4 : C4 * m ^ 2 ≤ C4 * (Cb * N) ^ 2 := mul_le_mul_of_nonneg_left hm2N hC4.le
    have t5 : 6 * (m * X) ≤ 6 * ((Cb * N) * X) :=
      mul_le_mul_of_nonneg_left hmX (by norm_num)
    have hcollect : C1 * (α ^ 2 * b ^ 2) + C1 * ((α ^ 2 * b) * X)
        + (5 + α) * ((α * b) * X) + (m * X + C4 * m ^ 2) + 6 * (m * X) + f * X
        ≤ C1 * N ^ 2 + C1 * (N * X) + (21 / 4) * (N * X)
          + ((Cb * N) * X + C4 * (Cb * N) ^ 2) + 6 * ((Cb * N) * X) + N * X :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add t1 t2) h5bb)
        (add_le_add hmX t4)) t5) hfX
    calc X ^ 2 ≤ C1 * N ^ 2 + C1 * (N * X) + (21 / 4) * (N * X)
          + ((Cb * N) * X + C4 * (Cb * N) ^ 2) + 6 * ((Cb * N) * X) + N * X :=
          le_trans hsum hcollect
      _ = (C1 + C4 * Cb ^ 2) * N ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1) * (N * X) := by ring
  have hmain : X ^ 2 ≤ (C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1))
      * (N * X + N ^ 2) := by
    have h1 : (C1 + C4 * Cb ^ 2) * N ^ 2
        ≤ (C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1)) * N ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith [hC1, hCb]) (sq_nonneg N)
    have h2 : (C1 + 21 / 4 + Cb + 6 * Cb + 1) * (N * X)
        ≤ (C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1)) * (N * X) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hC1, hCb, hC4, sq_nonneg Cb])
        (mul_nonneg hN0 hX0)
    have h3 : (C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1)) * (N * X + N ^ 2)
        = (C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1)) * (N * X)
          + (C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1)) * N ^ 2 := by ring
    rw [h3]; linarith [hkey, h1, h2]
  have hfinal := quad_solve hK0 hN0 hmain
  calc nrm α (ang2 u) = X := by rw [hXdef, hBdef]; rfl
    _ ≤ (C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1) + 1) * N := hfinal
    _ = (C1 + C4 * Cb ^ 2 + (C1 + 21 / 4 + Cb + 6 * Cb + 1) + 1)
        * (nrm α G + α * nrm α (grad u)) := by rw [hNdef, hfdef, hbdef, hUdef]; rfl


end Work.FTS.EllipticEst.Cores
