/-
# `Work.FTS.BSIdent.hid_of_corrected` — route C with the corrected field exhibited

This module combines

* `Work.FTS.BSIdent.hid_of_pointwise` (route C: Weyl on the difference, with the weak divergence and
  curl equations derived from pointwise identities off the two coordinate planes), and
* `Work.FTS.BSIdent.Weyl.merPsi_corrected_bundle` (the geometric bundle of the *corrected* ansatz
  field `psiFieldCorr (merPsi … · t) L`, where `L z = lim_{r→0⁺} merPsi(r,z,t)/r` is the axis level),

into the identification `hid` of `blowupAtTop_of_regPkg'`,

  `physVel (−physOmega α A B g C) x t = Cyl.psiField (merPsi α A B Φ C · · t) x`,  `t ∈ (0,T)`,
  `x ∈ Uax`,

with **no** `Work.LWP.BiotSavartInverse`, **no** `Physical.DivCurlLiouville` and **no**
`C¹`-regularity hypothesis on `Cyl.psiField` (which is false at the axis, see
`Weyl/Corrected.lean`).

The hypotheses are the elliptic law `hlaw` and the analytic data of `Φ` near the two boundary
endpoints `θ = 0, π/2` of the quadrant and at `w → ∞`: `hΦsm` (interior `C²` of `Φ` on a
neighbourhood of the closed quadrant), `hΦplane`/`hΦaxis` (the Dirichlet values `Φ(·,0) = Φ(·,π/2)
= 0`), `hexp`/`hrate` (the true vanishing/decay rates `|Φ| ≲ (π/2−θ)(1+w)^{−λ}` etc.).  The
off-axis `C²`-regularity `hΨ` of `merPsi` that `hid_of_pointwise` needs is **derived** here from
`hΦsm` via `Defs.contDiffAt_merPsi_slice`, so it is not a hypothesis of this theorem.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.hid_of_pointwise
import Submission.Work.FTS.BSIdent.Weyl.Corrected
import Submission.Work.FTS.BSIdent.Weyl.merPsi_corrected_bundle
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice
import Submission.Work.FTS.FireFix.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology Real NNReal

namespace Work.FTS.BSIdent

set_option autoImplicit false

/-- **THE IDENTIFICATION `hid` BY ROUTE C, WITH THE CORRECTED FIELD.**  For every `t ∈ (0,T)` the
reconstructed physical velocity `physVel (−physOmega α A B g C) · t` coincides with the ansatz field
`Cyl.psiField (merPsi α A B Φ C · · t)` on `Uax = {x₃ ≠ 0, r ≠ 0}`. -/
theorem hid_of_corrected {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {C : Physical.PhysClock} {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.Regularity.RegPkg (α : ℝ) S A B g)
    (hlaw : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp (α : ℝ))
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp (α : ℝ)) w θ
          + g w θ (Physical.clockInv C t))
    (hΦsm : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
        (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hΦplane : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w →
      Φ w 0 (Physical.clockInv C t) = 0)
    (hΦaxis : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w →
      Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp (α : ℝ) * lam)
    (hrate : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)|
          ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x := by
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
  let L : ℝ → ℝ → ℝ := fun t =>
    if ht : t ∈ Set.Ioo 0 C.T then
      Classical.choose (Weyl.merPsi_corrected_bundle (α := (α : ℝ)) (A := A) (B := B) (Φ := Φ)
        (C := C) (t := t) (hclock t ht).1 (hclock t ht).2.1 (hclock t ht).2.2
        (fun w θ hw hθ hθ' => hΦsm t ht w θ hw hθ hθ') (fun w hw => hΦplane t ht w hw)
        (fun w hw => hΦaxis t ht w hw) hlam hC₀ hexp (fun w θ hw hθ hθ' => hrate t ht w θ hw hθ hθ'))
    else fun _ => 0
  have hLspec : ∀ t ∈ Set.Ioo 0 C.T,
      Continuous (L t) ∧
      Continuous (psiFieldCorr (fun r z => merPsi (α : ℝ) A B Φ C r z t) (L t)) ∧
      Filter.Tendsto (psiFieldCorr (fun r z => merPsi (α : ℝ) A B Φ C r z t) (L t))
        (Filter.cocompact R3) (nhds 0) := by
    intro t ht
    have h := Classical.choose_spec (Weyl.merPsi_corrected_bundle (α := (α : ℝ)) (A := A) (B := B)
      (Φ := Φ) (C := C) (t := t) (hclock t ht).1 (hclock t ht).2.1 (hclock t ht).2.2
      (fun w θ hw hθ hθ' => hΦsm t ht w θ hw hθ hθ') (fun w hw => hΦplane t ht w hw)
      (fun w hw => hΦaxis t ht w hw) hlam hC₀ hexp (fun w θ hw hθ hθ' => hrate t ht w θ hw hθ hθ'))
    simpa only [L, dif_pos ht] using h
  -- the off-axis `C²`-regularity of `merPsi` is *derived* from `hΦsm` (interior `C²` of `Φ`)
  have hΨ : ∀ t ∈ Set.Ioo 0 C.T, ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => merPsi (α : ℝ) A B Φ C p.1 p.2 t) (r, z) :=
    fun t ht r z hr hz =>
      Defs.contDiffAt_merPsi_slice (α : ℝ) A B Φ C t (hclock t ht).2.2
        (fun w θ hw hθ hθ2 => hΦsm t ht w θ (by linarith) (by linarith) (by linarith)) hr hz
  refine hid_of_pointwise hreg hlaw hΨ
    (v := fun t => psiFieldCorr (fun r z => merPsi (α : ℝ) A B Φ C r z t) (L t))
    (fun t ht x hx => psiFieldCorr_eq_psiField_of_mem_Uax hx)
    (fun t ht => (hLspec t ht).2.1) (fun t ht => (hLspec t ht).2.2)

/-- **THE IDENTIFICATION BY ROUTE C, FROM THE `IsBslSol` INTERFACE.**  The same as
`hid_of_corrected` with the elliptic law in the paper's (PolarBSL) form, exactly as node N1/Open2
delivers it (the first conjunct of `IsDynGSolWith (IsBslSol p) p Φ g`). -/
theorem hid_of_corrected_of_IsBslSol {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {C : Physical.PhysClock} {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.Regularity.RegPkg (α : ℝ) S A B g)
    (hsol : ∀ t ∈ Set.Ioo 0 C.T, Work.Elliptic.IsBslSol (Work.FTS.Regularity.pExp (α : ℝ))
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp (α : ℝ)) g (Physical.clockInv C t))
      (fun z θ => Φ z θ (Physical.clockInv C t)))
    (hΦsm : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
        (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hΦplane : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w →
      Φ w 0 (Physical.clockInv C t) = 0)
    (hΦaxis : ∀ t ∈ Set.Ioo 0 C.T, ∀ w : ℝ, 0 < w →
      Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp (α : ℝ) * lam)
    (hrate : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)|
          ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x :=
  hid_of_corrected hreg
    (fun t ht w θ hw hθ hθ2 => (hsol t ht).1 w hw θ hθ hθ2)
    hΦsm hΦplane hΦaxis hlam hC₀ hexp hrate

/-- **The stream-function dictionary with the firing theorem.**  `Work.FTS.BSIdent.merPsi` is the
firing theorem's `Work.FTS.FireFix.merPsi` at the *odd-extended* family:

  `BSIdent.merPsi α A B Φ C = FireFix.merPsi α A B (PhiOdd Φ) C`.

This is the instantiation `Work.FTS.FireFix.blowupAtTop_of_regPkg'` uses for its `hid` slot (its
docstring records that "the natural instantiation passes the odd extension in `θ`"), and it is
`rfl`-level because both sides are `ρP² · (A (clockInv C t))⁻¹ · ·(ρP^{3α}/B, θP, clockInv C t)`.
A caller holding only the *non-extended* `Φ₀` (with `Φ₀ w 0 τ = 0`) can replace `PhiOdd Φ₀` by `Φ₀`
on `θ ≥ 0` via `PhiOdd_of_nonneg`. -/
theorem merPsi_eq_fireFix (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Physical.PhysClock) :
    merPsi α A B Φ C = Work.FTS.FireFix.merPsi α A B (PhiOdd Φ) C := rfl

end Work.FTS.BSIdent
