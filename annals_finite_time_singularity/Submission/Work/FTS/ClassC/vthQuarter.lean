/-
# `Work.FTS.EllSol.VthAuxC.assembleC` — the assembly of the `V^{th}` slot on `ClassC`

`ellVth_transferC_of_pieces` proves the `V^{th}` slot

```
CoefThMem 1 (Vop (PhiTil α g Φg)) ∧ CoefTh 1 (Vop (PhiTil α g Φg)) ≤ Ce · α^{-1/2} · |g|_{ℋ⁴}
```

for a datum of the class `ClassC` from three analytic inputs:

* `hE` — the level-`4` elliptic estimate `∃ C, EllEstUnif 4 C` (the chapter's `prop:Hk`);
* `hCert` — the certificate for `orthSource g` and `Ḡ(α,g)·sin 2θ` on `ClassC`;
* `hPoin` — the angular Poincaré estimate for the straightened unknown `ellShift α g Φg`.

The `ℋ⁴`-bound of `∂_θ(Vop Ξ)` (where `Ξ = PhiTil α g Φg`) comes from the pointwise identity
`pth_Vop_PhiTil_eq` and the five summand bounds; the final step is Elgindi's Corollary
`SecondDerivativesBounded` (`VthAux.mixedSlot_sup_le_hk_open`) and `1/√(γ-1) = √10 α^{-1/2}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.ropBasic
import Submission.Work.FTS.EllSol.VthAux.mixedSlot_sup_le_hk_open
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.EllSol.VthAuxC.helpersC
import Submission.Work.FTS.EllSol.ropPoincareAe
import Submission.Work.FTS.EllSol.VthAuxC.poinC
import Submission.Work.FTS.EllSol.VthAuxC.identC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The angular Poincaré estimate for the straightened unknown with the range `α ≤ 1/4`
explicit** (the `∀`-form of `VthAuxC.poinC`, whose statement returns an existential `α₀`; the
witness there is `1/4`, but Lean cannot see that through the opaque `∃`). -/
theorem poinC_quarter : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      ClassC α g → Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
        (ellShift α g Φg) →
      Work.Spaces.HkMem α 4 (ellShift α g Φg) ∧
      Work.Spaces.HkMem α 4 (Work.Spaces.pth (ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (ellShift α g Φg)
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (Work.Spaces.pth (ellShift α g Φg))
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (ellShift α g Φg)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllSol.ropPoincareAe
  refine ⟨C, hCpos, ?_⟩
  intro α g Φg hα hα4 _hcls _hsol _hsm hW
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨htr3, htr4⟩ := VthAuxC.pc_traces (α := α) (F := Work.Elliptic.orthSource g)
    (Ψ := ellShift α g Φg) hα hα4 hW
  have hvan : Work.Spaces.VanishTheta (ellShift α g Φg) := ⟨hW.zero, hW.pi_half⟩
  exact hC α (ellShift α g Φg) hα hα1 hW.smooth htr3 htr4
    (fun j _hj z _hz => ⟨VthAuxC.pc_dzIter_value_zero hvan j z,
      VthAuxC.pc_dzIter_value_pi_half hvan j z⟩) hW.memB

/-- **The `V^{th}` slot from its three analytic inputs, with the `α`-range `1/4` explicit.**

A copy of `Work.FTS.EllSol.VthAuxC.ellVth_transferC_of_pieces` in which the angular Poincaré
input is taken in its `∀`-form for `α ≤ 1/4` (so that the returned constant needs no existential
`α₀`), so that the slot is obtained for the whole range `α ∈ (0, 1/4]` demanded by
`Work.FTS.ClassC.VthSlot`.  Everything else is verbatim. -/
theorem ellVth_transferC_of_pieces_quarter
    (hE : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C)
    (hCert : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 → ClassC α g →
      Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
      Work.Spaces.HkMem α 4 (Work.Elliptic.orthSource g) ∧
      Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g) ≤ C * Work.Spaces.HkNorm α 4 g ∧
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ∧
      Work.Spaces.HkMem α 4 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ∧
      Work.Spaces.HkNorm α 4 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α 4 g)
    (hPoin : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g Φg : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 / 4 → ClassC α g → Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
        (ellShift α g Φg) →
      Work.Spaces.HkMem α 4 (ellShift α g Φg) ∧
      Work.Spaces.HkMem α 4 (Work.Spaces.pth (ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (ellShift α g Φg)
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (Work.Spaces.pth (ellShift α g Φg))
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (ellShift α g Φg))) :
    ∃ Ce : ℝ, 0 < Ce ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg → Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g) (ellShift α g Φg) →
    Work.FTS.VocabO.CoefThMem 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
    Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
      ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨C1, hC1pos, hE'⟩ := hE
  obtain ⟨C2, hC2pos, hCert'⟩ := hCert
  obtain ⟨C3, hC3pos, hPoin'⟩ := hPoin
  obtain ⟨CS, hCSpos, hS'⟩ := VthAux.mixedSlot_sup_le_hk_open
  obtain ⟨C4, hC4pos, hDz'⟩ := Work.FTS.EllipticEst.HkNorm_Dz_le_open 4
  refine ⟨4 * (CS * Real.sqrt 10
      * (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
          + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2))))),
    by positivity, ?_⟩
  intro α g Φg hα hαm hg hsol hsmΦ hweak
  have hα4 : α ≤ 1 / 4 := hαm
  have hα1 : α ≤ 1 := by linarith
  have hαnn : 0 ≤ α := le_of_lt hα
  let F : ℝ → ℝ → ℝ := Work.Elliptic.orthSource g
  let W : ℝ → ℝ → ℝ := ellShift α g Φg
  let GB : ℝ → ℝ → ℝ := fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)
  let GBm : ℝ → ℝ → ℝ := fun z θ => -(Work.Elliptic.Gbar α g z) * Real.sin (2 * θ)
  let A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 W z θ
  let DZ : ℝ → ℝ → ℝ := Work.Spaces.Dz W
  let V : ℝ → ℝ → ℝ := Work.Construction.Vop (Work.Construction.PhiTil α g Φg)
  let K : ℝ := Work.Spaces.HkNorm α 4 g
  have hKnn : 0 ≤ K := Work.Spaces.HkNorm_nonneg α 4 g
  obtain ⟨hFsm, hFmem, hFle, hGBsm, hGBmem, hGBle⟩ := hCert' α g hα hα1 hg
  have hEll := hE' α F W hα hα4 hweak
  have hAle : α ^ 2 * Work.Spaces.HkNorm α 4 A ≤ C1 * (C2 * K) := by
    have h1 : α ^ 2 * Work.Spaces.HkNorm α 4 A ≤ C1 * Work.Spaces.HkNorm α 4 F := by
      linarith [hEll, Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.pthIter 2 W)]
    calc α ^ 2 * Work.Spaces.HkNorm α 4 A ≤ C1 * Work.Spaces.HkNorm α 4 F := h1
      _ ≤ C1 * (C2 * K) := mul_le_mul_of_nonneg_left hFle (le_of_lt hC1pos)
  have hBle : Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W) ≤ C1 * (C2 * K) := by
    have h1 : Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W)
        ≤ C1 * Work.Spaces.HkNorm α 4 F := by
      linarith [hEll, mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α 4 A)]
    calc Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W) ≤ C1 * Work.Spaces.HkNorm α 4 F := h1
      _ ≤ C1 * (C2 * K) := mul_le_mul_of_nonneg_left hFle (le_of_lt hC1pos)
  obtain ⟨hWmem, hWpmem, hWle, hWple⟩ := hPoin' α g Φg hα hα4 hg hsol hsmΦ hweak
  have hWle' : Work.Spaces.HkNorm α 4 W ≤ C3 * (C1 * (C2 * K)) :=
    le_trans hWle (mul_le_mul_of_nonneg_left hBle (le_of_lt hC3pos))
  have hSmW : Work.FTS.EllipticEst.SmoothOpen W :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hweak.smooth
  have hSmA : Work.FTS.EllipticEst.SmoothOpen A :=
    Work.FTS.EllipticEst.SmoothOpen.zsq_mul (hSmW.pz.pz)
  have hSmGBm : Work.FTS.EllipticEst.SmoothOpen GBm := by
    have h1 := Work.FTS.EllipticEst.SmoothOpen.const_mul' (-1) hGBsm
    exact Work.FTS.EllipticEst.SmoothOpen.congr h1 (fun z θ _ _ _ => by
      simp only [GBm, GB]; ring)
  have hGBmmem : Work.Spaces.HkMem α 4 GBm := by
    have h1 : Work.Spaces.HkMem α 4 ((-1 : ℝ) • GB) :=
      Work.FTS.EllipticEst.HkMem_smul (by norm_num) α 4 hGBmem
    refine Work.FTS.EllipticEst.HkMem_agreeOnQ hSmGBm (fun z θ _ _ _ => ?_) h1
    simp only [GBm, GB, Pi.smul_apply, smul_eq_mul]
    ring
  have hGBm_norm : Work.Spaces.HkNorm α 4 GBm = Work.Spaces.HkNorm α 4 GB := by
    have h1 : GBm = - GB := by
      funext z θ
      simp only [GBm, GB, Pi.neg_apply]
      ring
    rw [h1, Work.FTS.EllipticEst.HkNorm_neg]
  have hDZ := hDz' α W hα hα1 hSmW.forall hWmem (Work.FTS.EllipticEst.TT.EllWeakPos.memA hweak)
  obtain ⟨hDZmem, hDZbnd⟩ := hDZ
  have hDZle : (α * (5 + α)) * Work.Spaces.HkNorm α 4 DZ
      ≤ 6 * (C4 * (C3 * (C1 * (C2 * K)) + C1 * (C2 * K))) := by
    have h1 : α * Work.Spaces.HkNorm α 4 DZ
        ≤ C4 * (Work.Spaces.HkNorm α 4 W + α ^ 2 * Work.Spaces.HkNorm α 4 A) := hDZbnd
    have h2 : Work.Spaces.HkNorm α 4 W + α ^ 2 * Work.Spaces.HkNorm α 4 A
        ≤ C3 * (C1 * (C2 * K)) + C1 * (C2 * K) := add_le_add hWle' hAle
    have h3 : α * Work.Spaces.HkNorm α 4 DZ
        ≤ C4 * (C3 * (C1 * (C2 * K)) + C1 * (C2 * K)) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt hC4pos))
    calc (α * (5 + α)) * Work.Spaces.HkNorm α 4 DZ
        = (5 + α) * (α * Work.Spaces.HkNorm α 4 DZ) := by ring
      _ ≤ 6 * (α * Work.Spaces.HkNorm α 4 DZ) := by
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg hαnn (Work.Spaces.HkNorm_nonneg α 4 DZ))
          linarith
      _ ≤ 6 * (C4 * (C3 * (C1 * (C2 * K)) + C1 * (C2 * K))) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hSm6W : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 6 * W z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' 6 hSmW
  have hSm6GBm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 6 * GBm z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' 6 hSmGBm
  have hSmA2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α ^ 2 * A z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' (α ^ 2) hSmA
  have hSmDZ2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (α * (5 + α)) * DZ z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' (α * (5 + α)) hSmW.Dz
  have hSmF6W : Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ + 6 * W z θ) :=
    vthC_smoothOpen_add hFsm hSm6W
  have hSmF6WGB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ) :=
    vthC_smoothOpen_add (vthC_smoothOpen_add hFsm hSm6W) hSm6GBm
  have hSmF6WGBA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ) :=
    vthC_smoothOpen_add (vthC_smoothOpen_add (vthC_smoothOpen_add hFsm hSm6W) hSm6GBm) hSmA2
  have hMem6W : Work.Spaces.HkMem α 4 (fun z θ => 6 * W z θ) :=
    Work.FTS.EllipticEst.HkMem_smul (by norm_num) α 4 hWmem
  have hMem6GBm : Work.Spaces.HkMem α 4 (fun z θ => 6 * GBm z θ) :=
    Work.FTS.EllipticEst.HkMem_smul (by norm_num) α 4 hGBmmem
  have hMemA2 : Work.Spaces.HkMem α 4 (fun z θ => α ^ 2 * A z θ) :=
    Work.FTS.EllipticEst.HkMem_smul (pow_ne_zero 2 (ne_of_gt hα)) α 4
      (Work.FTS.EllipticEst.TT.EllWeakPos.memA hweak)
  have hMemDZ2 : Work.Spaces.HkMem α 4 (fun z θ => (α * (5 + α)) * DZ z θ) :=
    Work.FTS.EllipticEst.HkMem_smul (ne_of_gt (by positivity : (0 : ℝ) < α * (5 + α))) α 4 hDZmem
  have hMemF6W : Work.Spaces.HkMem α 4 (fun z θ => F z θ + 6 * W z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hFsm hSm6W hFmem hMem6W
  have hMemF6WGB : Work.Spaces.HkMem α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open (vthC_smoothOpen_add hFsm hSm6W) hSm6GBm hMemF6W hMem6GBm
  have hMemF6WGBA : Work.Spaces.HkMem α 4
      (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open (vthC_smoothOpen_add (vthC_smoothOpen_add hFsm hSm6W)
      hSm6GBm) hSmA2 hMemF6WGB hMemA2
  have hn1 : Work.Spaces.HkNorm α 4 F ≤ C2 * K := hFle
  have hn2 : Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ) ≤ 6 * (C3 * (C1 * (C2 * K))) := by
    have h1 : Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)
        = |(6 : ℝ)| * Work.Spaces.HkNorm α 4 W :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 6 hSmW.forall
    rw [h1, show |(6 : ℝ)| = 6 by norm_num]
    exact mul_le_mul_of_nonneg_left hWle' (by norm_num)
  have hn3 : Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ) ≤ 6 * (C2 * K) := by
    have h1 : Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)
        = |(6 : ℝ)| * Work.Spaces.HkNorm α 4 GBm :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 6 hSmGBm.forall
    rw [h1, show |(6 : ℝ)| = 6 by norm_num, hGBm_norm]
    exact mul_le_mul_of_nonneg_left hGBle (by norm_num)
  have hn4 : Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ) ≤ C1 * (C2 * K) := by
    have h1 : Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)
        = |α ^ 2| * Work.Spaces.HkNorm α 4 A :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 (α ^ 2) hSmA.forall
    rw [h1, abs_of_nonneg (sq_nonneg α)]
    exact hAle
  have hn5 : Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)
      ≤ 6 * (C4 * (C3 * (C1 * (C2 * K)) + C1 * (C2 * K))) := by
    have h1 : Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)
        = |α * (5 + α)| * Work.Spaces.HkNorm α 4 DZ :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 (α * (5 + α)) hSmW.Dz.forall
    rw [h1, abs_of_nonneg (by positivity)]
    exact hDZle
  have hpoint : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      -(F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ + (α * (5 + α)) * DZ z θ)
        = Work.Spaces.pth V z θ := by
    intro z θ hz hθ0 hθ1
    exact (pth_Vop_PhiTil_eq α g Φg hweak hGBsm hz ⟨hθ0, hθ1⟩).symm
  let S5 : ℝ → ℝ → ℝ := fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ
    + (α * (5 + α)) * DZ z θ
  have hSmS5 : Work.FTS.EllipticEst.SmoothOpen S5 :=
    Work.FTS.EllipticEst.SmoothOpen.congr (vthC_smoothOpen_add hSmF6WGBA hSmDZ2)
      (fun z θ _ _ _ => by simp only [S5])
  have hMemS5 : Work.Spaces.HkMem α 4 S5 :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hSmS5 (fun z θ _ _ _ => by
      simp only [S5])
      (Work.FTS.EllipticEst.HkMem_add_open hSmF6WGBA hSmDZ2 hMemF6WGBA hMemDZ2)
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have htri1 : Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
      ≤ 2 * (Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)) := by
    have h := Work.FTS.EllipticEst.HkNorm_add_le α 4 hFsm.forall hSm6W.forall hFmem hMem6W
    calc Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 F
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)) := h
      _ ≤ 2 * (Work.Spaces.HkNorm α 4 F
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)) := by
          refine mul_le_mul_of_nonneg_right hsqrt2 ?_
          exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 F)
            (Work.Spaces.HkNorm_nonneg α 4 _)
  have htri2 : Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
      ≤ 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)) := by
    have h := Work.FTS.EllipticEst.HkNorm_add_le α 4 hSmF6W.forall hSm6GBm.forall
      hMemF6W hMem6GBm
    calc Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)) := h
      _ ≤ 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)) := by
          refine mul_le_mul_of_nonneg_right hsqrt2 ?_
          exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 _) (Work.Spaces.HkNorm_nonneg α 4 _)
  have htri3 : Work.Spaces.HkNorm α 4
        (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
      ≤ 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)) := by
    have h := Work.FTS.EllipticEst.HkNorm_add_le α 4 hSmF6WGB.forall hSmA2.forall
      hMemF6WGB hMemA2
    calc Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)) := h
      _ ≤ 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)) := by
          refine mul_le_mul_of_nonneg_right hsqrt2 ?_
          exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 _) (Work.Spaces.HkNorm_nonneg α 4 _)
  have htri4 : Work.Spaces.HkNorm α 4 S5
      ≤ 2 * (Work.Spaces.HkNorm α 4
            (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := by
    have h := Work.FTS.EllipticEst.HkNorm_add_le α 4 hSmF6WGBA.forall hSmDZ2.forall
      hMemF6WGBA hMemDZ2
    have heq : S5 = fun z θ => (F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
        + (α * (5 + α)) * DZ z θ := rfl
    rw [heq]
    calc Work.Spaces.HkNorm α 4 (fun z θ => (F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
          + (α * (5 + α)) * DZ z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4
              (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := h
      _ ≤ 2 * (Work.Spaces.HkNorm α 4
              (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := by
          refine mul_le_mul_of_nonneg_right hsqrt2 ?_
          exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 _) (Work.Spaces.HkNorm_nonneg α 4 _)
  have hVhd : Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)
      ≤ 32 * (Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := by
    have hsq : Work.Spaces.HkSq α 4 (Work.Spaces.pth V)
        = Work.Spaces.HkSq α 4 (fun z θ => -(S5 z θ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ0 hθ1 => by
        rw [hpoint z θ hz hθ0 hθ1])
    have hnorm : Work.Spaces.HkNorm α 4 (Work.Spaces.pth V) = Work.Spaces.HkNorm α 4 S5 := by
      have h2 : Work.Spaces.HkNorm α 4 (fun z θ => -(S5 z θ)) = Work.Spaces.HkNorm α 4 S5 := by
        have hneg : (fun z θ => -(S5 z θ)) = -S5 := by
          funext z θ; simp only [Pi.neg_apply]
        rw [hneg, Work.FTS.EllipticEst.HkNorm_neg]
      have h3 : Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)
          = Work.Spaces.HkNorm α 4 (fun z θ => -(S5 z θ)) := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsq]
      rw [h3, h2]
    rw [hnorm]
    have hnn1 : 0 ≤ Work.Spaces.HkNorm α 4 F := Work.Spaces.HkNorm_nonneg α 4 F
    have hnn2 : 0 ≤ Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have hnn3 : 0 ≤ Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have hnn4 : 0 ≤ Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have hnn5 : 0 ≤ Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    linarith [htri1, htri2, htri3, htri4]
  have hVle : Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)
      ≤ (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
          + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K := by
    have hsum : Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)
        ≤ (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2))) * K := by
      nlinarith [hn1, hn2, hn3, hn4, hn5, hKnn, le_of_lt hC1pos, le_of_lt hC2pos,
        le_of_lt hC3pos, le_of_lt hC4pos]
    calc Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)
        ≤ 32 * (Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := hVhd
      _ ≤ 32 * ((C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2))) * K) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K := by ring
  have hSmΞ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Φg) := by
    have hdec : (fun z θ => ellShift α g Φg z θ
        + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ))
        = Work.Construction.PhiTil α g Φg := by
      rw [Work.FTS.EllipticEst.PhiTil_eq_EllResid]
      exact (vthC_EllResid_eq_ellShift α g Φg).symm
    exact Work.FTS.EllipticEst.SmoothOpen.congr (vthC_smoothOpen_add hSmW hSmGBm)
      (fun z θ _ _ _ => by rw [← hdec])
  have hSmV : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth V) := by
    have hVeq : V = fun z θ => Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ
        - Real.tan θ * Work.Construction.PhiTil α g Φg z θ := by
      funext z θ; simp only [V, Work.Construction.Vop]
    rw [hVeq]
    exact (vthC_smoothOpen_sub hSmΞ.pth (vthC_smoothOpen_tan_mul hSmΞ)).pth
  have hMemV : Work.Spaces.HkMem α 4 (Work.Spaces.pth V) := by
    have h2 : Work.Spaces.HkMem α 4 ((-1 : ℝ) • S5) :=
      Work.FTS.EllipticEst.HkMem_smul (c := (-1 : ℝ)) (by norm_num) α 4 hMemS5
    refine Work.FTS.EllipticEst.HkMem_agreeOnQ (f := (-1 : ℝ) • S5) hSmV ?_ h2
    intro z θ hz hθ0 hθ1
    simpa only [Pi.smul_apply, smul_eq_mul, neg_one_mul, S5]
      using hpoint z θ hz hθ0 hθ1
  have hratio : 0 ≤ CS / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (le_of_lt hCSpos) (Real.sqrt_nonneg _)
  refine ⟨fun b i hbi => ⟨CS / Real.sqrt (Work.Spaces.gam α - 1)
      * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V),
      fun z θ hz hθ0 hθ1 => hS' α (Work.Spaces.pth V) b i hα hα1 (by omega) hSmV hMemV
        z θ hz hθ0 hθ1⟩, ?_⟩
  have hcoef : Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
      ≤ 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)) := by
    have h := Work.FTS.TransportS.coefTh_le_of_supAbsO_le (l := 1)
      (f := Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
      (K := CS / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V))
      (fun b i hbi => Work.FTS.H2.supAbsO_le
        (fun z θ hz hθ0 hθ1 => hS' α (Work.Spaces.pth V) b i hα hα1 (by omega) hSmV hMemV
          z θ hz hθ0 hθ1))
    have h4 : (((1 : ℕ) : ℝ) + 1) * (((1 : ℕ) : ℝ) + 1) = 4 := by norm_num
    calc _ ≤ (((1 : ℕ) : ℝ) + 1) * (((1 : ℕ) : ℝ) + 1)
          * (CS / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)) := h
      _ = 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)) := by rw [h4]
  have hstep : 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V))
      ≤ 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
        * ((32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVle hratio) (by norm_num)
  have hfin : 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
        * ((32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K))
      = (4 * (CS * Real.sqrt 10 * (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))))) * α ^ (-(1 / 2 : ℝ)) * K := by
    rw [show CS / Real.sqrt (Work.Spaces.gam α - 1)
          = CS * (1 / Real.sqrt (Work.Spaces.gam α - 1)) from by ring,
      vthC_inv_sqrt_gam_sub_one hα]
    ring
  calc Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
      ≤ 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)) := hcoef
    _ ≤ 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
          * ((32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
              + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K)) := hstep
    _ = (4 * (CS * Real.sqrt 10 * (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))))) * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.HkNorm α 4 g := by
        rw [hfin]

end Work.FTS.EllSol
