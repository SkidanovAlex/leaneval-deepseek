import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev12
import Submission.Work.FTS_BSIdentP.RegPkgPrime.HidPointwise
import Submission.Work.FTS_BSIdentP.Slim.MerPsiCorrectedBundle
import Submission.Work.FTS_BSIdentP.Slim.PsiFieldCorrCocompact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_BSIdentP

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS
open Work.FTS.Physical (PhysClock)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-! ## P2 — the slim variant (the gate) -/

/-- **BSIdent-P2 (gate)**: the slim variant — `C²` only on `w > 0`, and only the three first-order
rates. -/
theorem hid_of_corrected'_slim_proved {α : ℝ≥0} {A B : ℝ → ℝ} {g : Fam} {C : PhysClock}
    {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hlaw : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (pExp (α : ℝ)) (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (pExp (α : ℝ)) w θ + g w θ (Physical.clockInv C t))
    (hΦsm : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
        (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hΦplane : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hΦaxis : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w →
      Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    (hrate : ∀ t ∈ Set.Ioo 0 C.T, ∃ lam C₀ : ℝ, 0 < lam ∧ 0 < C₀ ∧
      2 ≤ pExp (α : ℝ) * lam ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
      Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) x := by
  classical
  -- the clock data, and the choice of the axis level `L t` for every `t`
  have hclock : ∀ t ∈ Set.Ioo 0 C.T,
      0 < (α : ℝ) ∧ A (Physical.clockInv C t) ≠ 0 ∧ 0 < B (Physical.clockInv C t) := by
    intro t ht
    have htIco : t ∈ Set.Ico (0 : ℝ) C.T := ⟨ht.1.le, ht.2⟩
    have hτnn : 0 ≤ Physical.clockInv C t := Physical.clockInv_nonneg C htIco
    have hτmem : Physical.clockInv C t ∈ Set.Icc (0 : ℝ) (Physical.clockInv C t + 1) :=
      ⟨hτnn, by linarith⟩
    have hP := hreg (Physical.clockInv C t + 1) (by linarith)
    exact ⟨hP.hα, ne_of_gt (hP.hA _ hτmem), hP.hB _ hτmem⟩
  -- the slim bundle, with the constants chosen per `t`
  have hbundle : ∀ t ∈ Set.Ioo 0 C.T, ∃ Lz : ℝ → ℝ, Continuous Lz ∧
      Continuous (Work.FTS.BSIdent.psiFieldCorr
        (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) Lz) ∧
      Filter.Tendsto (Work.FTS.BSIdent.psiFieldCorr
          (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) Lz)
        (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
    intro t ht
    obtain ⟨lam, C₀, hlam, hC₀, hexp, hr⟩ := hrate t ht
    exact Work.FTS.BSIdentP.Weyl.merPsi_corrected_bundle (hclock t ht).1 (hclock t ht).2.1
      (hclock t ht).2.2 (fun w θ hw hθ hθ' => hΦsm t ht w θ hw hθ hθ')
      (fun w hw => hΦplane t ht w hw) (fun w hw => hΦaxis t ht w hw) hlam hC₀ hexp hr
  let L : ℝ → ℝ → ℝ := fun t =>
    if ht : t ∈ Set.Ioo 0 C.T then Classical.choose (hbundle t ht) else fun _ => 0
  have hLspec : ∀ t ∈ Set.Ioo 0 C.T,
      Continuous (L t) ∧
      Continuous (Work.FTS.BSIdent.psiFieldCorr
        (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) (L t)) ∧
      Filter.Tendsto (Work.FTS.BSIdent.psiFieldCorr
          (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) (L t))
        (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
    intro t ht
    have h := Classical.choose_spec (hbundle t ht)
    simpa only [L, dif_pos ht] using h
  -- the off-axis `C²`-regularity of `merPsi` is *derived* from the slim `C²` of `Φ`
  have hΨ : ∀ t ∈ Set.Ioo 0 C.T, ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C p.1 p.2 t) (r, z) :=
    fun t ht r z hr hz =>
      Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice (α : ℝ) A B Φ C t (hclock t ht).2.2
        (fun w θ hw hθ hθ2 => hΦsm t ht w θ hw (by linarith) (by linarith)) hr hz
  refine Work.FTS.BSIdentP.hid_of_pointwise' hreg hlaw hΨ
    (v := fun t => Work.FTS.BSIdent.psiFieldCorr
      (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) (L t))
    (fun t ht x hx => Work.FTS.BSIdent.psiFieldCorr_eq_psiField_of_mem_Uax hx)
    (fun t ht => (hLspec t ht).2.1) (fun t ht => (hLspec t ht).2.2)

/-! ## `continuous_axisLevel_slim` -/


/-! ## P1 — the per-`t` decay constants -/


/-! ## The law in the `IsBslSol` form (the shape in which `Sol` delivers it) -/


end Work.FTS_BSIdentP
