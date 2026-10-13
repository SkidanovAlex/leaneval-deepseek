/-
# `Work.FTS_BSIdentP.Producers` — the BSIdent port: `hid_of_corrected'`, `hid_of_corrected'_slim`,
`continuous_axisLevel_slim`

The three theorems requested for `StreamBdryIface/Producers.lean`, with the *identical* types:

* `hid_of_corrected'_proved` (P1): `BSIdent.hid_of_corrected` with the corrected package
  `Work.FTS.RegPkgGal.RegPkg'` and the decay constants chosen per `t`
  (`∀ t, ∃ lam C₀, …`).
* `hid_of_corrected'_slim_proved` (P2, the gate): the same with `C²` of `Φ` assumed only on
  `w > 0` and only the three first-order rate clauses.
* `continuous_axisLevel_slim_proved`: the `w = 0` patch of P2 — the `z = 0` case of
  `Weyl.Levels.continuous_axisLevel` under the slim hypotheses.

P1 is **derived from P2** (its hypotheses are strictly stronger: `-1 < w` implies `0 < w`, and the
six-clause rate implies its first three clauses).  P2 is proved through
`Work.FTS.BSIdentP.hid_of_pointwise'` (route C for `RegPkg'`) and the slim bundle
`Work.FTS.BSIdentP.Weyl.merPsi_corrected_bundle` (the port of `Weyl.merPsi_corrected_bundle`);
`continuous_axisLevel_slim_proved` is
`Work.FTS.BSIdentP.Levels.continuous_axisLevel`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev12
import Submission.Work.FTS_BSIdentP.RegPkgPrime.HidPointwise
import Submission.Work.FTS_BSIdentP.Slim.MerPsiCorrectedBundle
import Submission.Work.FTS_BSIdentP.Slim.ContinuousAxisLevel

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

/-- **BSIdent-P2, the `z = 0` patch**: `continuous_axisLevel` under the slim hypotheses. -/
theorem continuous_axisLevel_slim_proved {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Work.FTS.Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Work.FTS.Physical.clockInv C t) ≠ 0)
    (hB : 0 < B (Work.FTS.Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Work.FTS.Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Work.FTS.Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Work.FTS.Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Work.FTS.Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Work.FTS.Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Work.FTS.Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    Continuous (Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Work.FTS.Physical.clockInv C t)) :=
  Work.FTS.BSIdentP.Levels.continuous_axisLevel hα hA hB hsm hzeroPlane hzeroAxis hlam hC₀ hexp
    hrate

/-! ## P1 — the per-`t` decay constants -/

/-- **BSIdent-P1**: `hid_of_corrected` with `RegPkg'` (physVort facts from `FireFix.Prime.*`;
clock positivity from `hreg.hA/hB`) and the decay constants chosen per `t`. -/
theorem hid_of_corrected'_proved {α : ℝ≥0} {A B : ℝ → ℝ} {g : Fam} {C : PhysClock} {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hlaw : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (pExp (α : ℝ)) (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (pExp (α : ℝ)) w θ + g w θ (Physical.clockInv C t))
    (hΦsm : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ →
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
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
      Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) x := by
  refine hid_of_corrected'_slim_proved hreg hlaw ?_ hΦplane hΦaxis ?_
  · intro t ht w θ hw hθ hθ'
    exact hΦsm t ht w θ (by linarith) hθ hθ'
  · intro t ht
    obtain ⟨lam, C₀, hlam, hC₀, hexp, hr⟩ := hrate t ht
    exact ⟨lam, C₀, hlam, hC₀, hexp, fun w θ hw hθ hθ' =>
      ⟨(hr w θ hw hθ hθ').1, (hr w θ hw hθ hθ').2.1, (hr w θ hw hθ hθ').2.2.1⟩⟩

/-! ## The law in the `IsBslSol` form (the shape in which `Sol` delivers it) -/

/-- **P2 with the elliptic law in the paper's `IsBslSol` form**, exactly as the reconstruction's
`Sol` conjunct delivers it.  This is the form `StreamBdry` consumes: the pointwise law `hlaw` is
the first conjunct of `IsBslSol`. -/
theorem hid_of_corrected'_slim_of_IsBslSol {α : ℝ≥0} {A B : ℝ → ℝ} {g : Fam} {C : PhysClock}
    {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hsol : ∀ t ∈ Set.Ioo 0 C.T, Work.Elliptic.IsBslSol (pExp (α : ℝ))
      (Work.Construction.Ftau (pExp (α : ℝ)) g (Physical.clockInv C t))
      (fun z θ => Φ z θ (Physical.clockInv C t)))
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
        = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi (α : ℝ) A B Φ C r z t) x :=
  hid_of_corrected'_slim_proved hreg
    (fun t ht w θ hw hθ hθ2 => (hsol t ht).1 w hw θ hθ hθ2)
    hΦsm hΦplane hΦaxis hrate

end Work.FTS_BSIdentP
