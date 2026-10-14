import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.Vop_far
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb2_dthDV_proved
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_StreamBdry.SB0.sb0_psiField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SB0` — the gauge summand and the jump sheet are invisible to `Cyl.psiField`

**Target (`Work.FTS_StreamBdry.SB0.sb0_psiField`, statement unchanged).**  For the firing pair
`(psiFire Φs E g, psiHatP (pExp a) Φs E g)` of the StreamBdry reduction, the meridian field
`psiField` of the physical stream function and of the `U`-slot (BSIdent) stream function agree on
`Uax`:

`psiField (merPsi (psiFire)) = psiField (BSIdent.merPsi (psiHatP))`  on `Uax`, for `t ∈ (0,T)`.

## Route (all inputs from the frozen hypotheses)

Write `σ := clockInv C t ≥ 0`, `αG := pExp a = 3a`, `ρ := ρP r z`, `θ := θP r z`,
`χ := ρ^{3a}/B σ`.

1. **Pointwise value difference.**  By `hdec` (SB1′) there is `κ` with
   `slice PsiCan τ = psiP + κ·gaugeMode` on `Qd`.  For `θ > 0` this gives
   `psiFire (χ,θ) − psiHatP (χ,θ) = κ·gaugeMode (χ,θ)`; both families are odd in `θ`
   (`psiFire_odd`; `oddPerS`-oddness from `SB25.oddPerS_pieces`) and `gaugeMode` is even in `θ`,
   so for `θ < 0` the difference is `−κ·gaugeMode (χ,θ)`.  Hence
   `psiFire − psiHatP = sgn(θ)·κ·gaugeMode (χ,θ)`.  (`psiFire_sub_psiHatP`.)
2. **Gauge algebra.**  `gaugeMode (χ,θ) = χ^{−1/a}/cos θ` and
   `χ^{−1/a} = ρ^{−3}·B^{1/a}` (`sb0_gauge_alg`), while `ρ·cos θ = r` (`Cyl.cos_thetaP`); so the
   difference of the *stream functions* is `(if 0 < z then c/r else −c/r)` with
   `c = κ·A(σ)^{-1}·B(σ)^{1/a}` — a "jump sheet" with `sgn z`.
3. **`psiField` of the jump sheet vanishes** (`sb0_psiFieldJump`): at `z ≠ 0` the `z`-slice of
   `c·sgn(z)/r` is locally constant, so `∂_zψ = 0`, and `∂_rψ = −ψ/r`, so the axial component
   `−ψ/r − ∂_rψ` vanishes too.
4. **`psiField` is additive in the stream function** (`sb0_psiFieldAdd`) when both summands are
   differentiable at the point.  The BSIdent stream function is `C²` there
   (`BSIdent.Defs.contDiffAt_merPsi_slice` with `hsm` for `psiHatP`, which is `sb0_hsm_psiHatP`
   from `hPsm`), and the jump sheet is differentiable off the axis.
5. The two stream functions need only agree **on the cross** (radial line and axial line) through
   `x` for `psiField` to agree at `x` (`psiField_congr_of_cross`, which uses only `deriv`
   congruence along the two lines) — so no differentiability of the `psiFire`-side is needed
   (whence `hC3` is not consumed by the proof).

-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open scoped Topology
open Filter

namespace Work.FTS_StreamBdry.SB0

open Work.FTS.Galerkin (Fn Fam slice slice_apply)
open Work.FTS.StreamBdryIface (psiP psiHatP gaugeMode Uprime oddPerS)

/-! ## §1 Value facts for `psiP`, `psiHatP`, `psiFire` -/

/-- `psiP` vanishes at `θ = π/2` (the factor `sin 2θ`). -/
theorem psiP_at_pi_div_two (αG z : ℝ) (Ψ : Fn) : psiP αG Ψ z (Real.pi / 2) = 0 := by
  have h : Work.Construction.s2 (Real.pi / 2) = 0 := by
    rw [Work.Construction.s2_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  simp only [psiP, h]; norm_num

/-- On `0 < θ ≤ π/2` the family `psiHatP` is the `U`-slot part of the canonical slice. -/
theorem psiHatP_pos (αG : ℝ) {Φs : Fn} {E : Fn → Fn} {g : Fam} {w θ τ : ℝ} (hw : 0 < w)
    (hθ : 0 < θ) (hθ' : θ ≤ Real.pi / 2) :
    psiHatP αG Φs E g w θ τ = psiP αG (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) w θ := by
  rw [psiHatP, ite_eq_left hw]
  exact (Work.FTS_StreamBdry.SB25.oddPerS_pieces
    (psiP αG (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
    (fun z => psiP_at_pi_div_two αG z _)).2.1 w θ hθ hθ'

/-- On `−π/2 ≤ θ < 0` the family `psiHatP` is the odd reflection of the `U`-slot part. -/
theorem psiHatP_neg (αG : ℝ) {Φs : Fn} {E : Fn → Fn} {g : Fam} {w θ τ : ℝ} (hw : 0 < w)
    (hθ : -(Real.pi / 2) ≤ θ) (hθ' : θ < 0) :
    psiHatP αG Φs E g w θ τ = -psiP αG (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) w (-θ) := by
  rw [psiHatP, ite_eq_left hw]
  exact (Work.FTS_StreamBdry.SB25.oddPerS_pieces
    (psiP αG (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
    (fun z => psiP_at_pi_div_two αG z _)).2.2.1 w θ hθ hθ'

/-- The firing family below the equatorial plane: the odd reflection of `PsiCan`. -/
theorem psiFire_neg {Φs : Fn} {E : Fn → Fn} {g : Fam} {z θ τ : ℝ} (hθ : θ < 0) :
    Work.FTS.FinalV2.psiFire Φs E g z θ τ = -Work.FTS.Nonlin.PsiCan Φs E g z (-θ) τ := by
  rw [Work.FTS.FinalV2.psiFire, Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ),
    Work.FTS.FinalV2.psiCut, ite_eq_left (by linarith : (0 : ℝ) < -θ)]

/-! ## §2 The pointwise difference of the two families -/

/-- **The value difference of the firing family and the `U`-slot family**: for `χ > 0` and
`θ ∈ (−π/2, π/2) \ {0}`, the decomposition `PsiCan = psiP + κ·gaugeMode` on `Qd` (extended to
negative `θ` by oddness) gives
`psiFire (χ,θ,τ) − psiHatP (χ,θ,τ) = sgn(θ)·κ·gaugeMode (χ,θ)`. -/
theorem psiFire_sub_psiHatP {αG : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam} {κ : ℝ} {τ χ θ : ℝ}
    (hχ : 0 < χ) (hθlo : -(Real.pi / 2) < θ) (hθhi : θ < Real.pi / 2) (hθne : θ ≠ 0)
    (hdecκ : ∀ z θ', (z, θ') ∈ Work.Construction.Qd →
      slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ'
        = psiP αG (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ'
          + κ * gaugeMode αG z θ') :
    Work.FTS.FinalV2.psiFire Φs E g χ θ τ - psiHatP αG Φs E g χ θ τ
      = (if 0 < θ then (1 : ℝ) else -1) * (κ * gaugeMode αG χ θ) := by
  rcases lt_trichotomy θ 0 with h | h | h
  · have hpos : 0 < -θ := by linarith
    have hmem : (χ, -θ) ∈ Work.Construction.Qd := ⟨hχ, hpos, by linarith⟩
    have hdec := hdecκ χ (-θ) hmem
    simp only [slice_apply] at hdec
    rw [psiFire_neg h, psiHatP_neg αG hχ (by linarith) h,
      ite_eq_right (not_lt.mpr (le_of_lt h)), hdec]
    have hg : gaugeMode αG χ (-θ) = gaugeMode αG χ θ := by
      simp only [gaugeMode, Real.cos_neg]
    rw [hg]; ring
  · subst h; exact absurd rfl hθne
  · have hmem : (χ, θ) ∈ Work.Construction.Qd := ⟨hχ, h, hθhi⟩
    have hdec := hdecκ χ θ hmem
    simp only [slice_apply] at hdec
    rw [Work.FTS.FinalV2.psiFire_of_pos h, psiHatP_pos αG hχ h (le_of_lt hθhi),
      ite_eq_left h, hdec]
    ring

/-- On the strip `(−π/2, π/2)` the odd extension `PhiOdd` of `psiHatP` is `psiHatP` itself. -/
theorem PhiOdd_psiHatP {αG : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam} {τ χ θ : ℝ} (hχ : 0 < χ)
    (hθlo : -(Real.pi / 2) < θ) (hθhi : θ < Real.pi / 2) :
    Work.FTS.BSIdent.PhiOdd (psiHatP αG Φs E g) χ θ τ = psiHatP αG Φs E g χ θ τ := by
  rcases lt_trichotomy θ 0 with h | h | h
  · have hpos : 0 < -θ := by linarith
    rw [Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr h),
      psiHatP_pos αG hχ hpos (by linarith), psiHatP_neg αG hχ (by linarith) h]
  · subst h; rw [Work.FTS.BSIdent.PhiOdd_of_nonneg le_rfl]
  · exact Work.FTS.BSIdent.PhiOdd_of_nonneg (le_of_lt h)

/-! ## §3 The sign of `θ = arctan(z/r)` -/

theorem thetaP_pos_iff {r z : ℝ} (hr : 0 < r) : 0 < Work.Cyl.thetaP r z ↔ 0 < z := by
  rw [Work.Cyl.thetaP, Real.arctan_pos, div_pos_iff_of_pos_right hr]

theorem thetaP_neg_iff {r z : ℝ} (hr : 0 < r) : Work.Cyl.thetaP r z < 0 ↔ z < 0 := by
  have h := Real.arctan_lt_zero (x := z / r)
  rw [Work.Cyl.thetaP]
  constructor
  · intro h1
    have h2 := h.mp h1
    have h3 := mul_neg_of_neg_of_pos h2 hr
    rwa [div_mul_cancel₀ z hr.ne'] at h3
  · intro h1
    apply h.mpr
    rw [div_eq_mul_inv]
    exact mul_neg_of_neg_of_pos h1 (inv_pos.mpr hr)

/-! ## §4 The value difference of the two meridian stream functions -/

/-- **The jump-sheet identity**: with `χ := ρ^p / B(σ)`, `θ := θP r z` (`r > 0`, `z ≠ 0`) and
`κ` the gauge constant of `hdec` at `σ = clockInv C t`, the physical (`MeridianDyn`) stream
function of the firing family differs from the `U`-slot (`BSIdent`) stream function by the jump
sheet `z ↦ ±c/r`, `c = κ·A(σ)^{-1}·B(σ)^{1/a}`. -/
theorem merPsi_diff {a : ℝ} (ha : 0 < a) {Φs : Fn} {E : Fn → Fn} {g : Fam} {A B : ℝ → ℝ}
    {C : Work.FTS.Physical.PhysClock} {κ t r z : ℝ}
    (hdecκ : ∀ z θ', (z, θ') ∈ Work.Construction.Qd →
      slice (Work.FTS.Nonlin.PsiCan Φs E g) (Work.FTS.Physical.clockInv C t) z θ'
        = psiP (Work.FTS.Regularity.pExp a)
            (slice (Work.FTS.Nonlin.PsiCan Φs E g) (Work.FTS.Physical.clockInv C t)) z θ'
          + κ * gaugeMode (Work.FTS.Regularity.pExp a) z θ')
    (hr : 0 < r) (hz : z ≠ 0) (hB : 0 < B (Work.FTS.Physical.clockInv C t)) :
    Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp a) A B
        (Work.FTS.FinalV2.psiFire Φs E g) C r z t
      = Work.FTS.BSIdent.merPsi a A B (psiHatP (Work.FTS.Regularity.pExp a) Φs E g) C r z t
        + (if 0 < z then (κ * (A (Work.FTS.Physical.clockInv C t))⁻¹
              * B (Work.FTS.Physical.clockInv C t) ^ (1 / a)) / r
           else -((κ * (A (Work.FTS.Physical.clockInv C t))⁻¹
              * B (Work.FTS.Physical.clockInv C t) ^ (1 / a)) / r)) := by
  rw [Work.FTS.MeridianDyn.merPsi, Work.FTS.MeridianDyn.dynPsi_apply,
    Work.FTS.BSIdent.merPsi_apply]
  set σ := Work.FTS.Physical.clockInv C t with hσ
  set Ainv := (A σ)⁻¹ with hAinv
  set ρ := Work.Cyl.rhoP r z with hρdef
  set θ := Work.Cyl.thetaP r z with hθdef
  set χ := ρ ^ Work.FTS.Regularity.pExp a / B σ with hχdef
  have hρ : 0 < ρ := by rw [hρdef]; exact Work.Cyl.rhoP_pos hr z
  have hBσ : 0 < B σ := by rw [hσ]; exact hB
  have hχ : 0 < χ := by
    rw [hχdef]; exact div_pos (Real.rpow_pos_of_pos hρ _) hBσ
  have hθlo : -(Real.pi / 2) < θ := by rw [hθdef]; exact Real.neg_pi_div_two_lt_arctan _
  have hθhi : θ < Real.pi / 2 := by rw [hθdef]; exact Real.arctan_lt_pi_div_two _
  have hθne : θ ≠ 0 := by
    intro h0
    have h2 : Work.Cyl.thetaP r z = 0 := by rw [← hθdef]; exact h0
    rw [Work.Cyl.thetaP] at h2
    have h3 := (Real.arctan_eq_zero_iff (x := z / r)).mp h2
    rw [div_eq_zero_iff] at h3
    rcases h3 with h3 | h3
    · exact hz h3
    · exact hr.ne' h3
  rw [PhiOdd_psiHatP (αG := Work.FTS.Regularity.pExp a) hχ hθlo hθhi]
  have hA := psiFire_sub_psiHatP (αG := Work.FTS.Regularity.pExp a) (κ := κ) (τ := σ)
    hχ hθlo hθhi hθne hdecκ
  have hcos : ρ * Real.cos θ = r := by
    rw [hθdef, Work.Cyl.cos_thetaP hr z, hρdef]
    exact mul_div_cancel₀ r (Work.Cyl.rhoP_ne_zero hr z)
  have h1 : gaugeMode (Work.FTS.Regularity.pExp a) χ θ
      = (ρ ^ (3 * a) / B σ) ^ (-(3 / (3 * a))) / Real.cos θ := by
    simp only [gaugeMode, hχdef, Work.FTS.Regularity.pExp_eq]
  have hkey : ρ ^ 2 * Ainv * ((if 0 < θ then (1 : ℝ) else -1)
        * (κ * gaugeMode (Work.FTS.Regularity.pExp a) χ θ))
      = (if 0 < z then (κ * Ainv * B σ ^ (1 / a)) / r
          else -((κ * Ainv * B σ ^ (1 / a)) / r)) := by
    rcases lt_trichotomy θ 0 with h | h | h
    · have hzneg : z < 0 := (thetaP_neg_iff (z := z) hr).mp (by rw [← hθdef]; exact h)
      rw [ite_eq_right (not_lt.mpr (le_of_lt h)), ite_eq_right (not_lt.mpr (le_of_lt hzneg)), h1,
        show ρ ^ 2 * Ainv * (-1 * (κ * ((ρ ^ (3 * a) / B σ) ^ (-(3 / (3 * a)))
            / Real.cos θ)))
          = -(ρ ^ 2 * Ainv * (κ * ((ρ ^ (3 * a) / B σ) ^ (-(3 / (3 * a)))
              / Real.cos θ))) by ring,
        sb0_gauge_alg ha hρ hBσ, hcos]
    · exfalso; exact hθne h
    · have hzpos : 0 < z := (thetaP_pos_iff (z := z) hr).mp (by rw [← hθdef]; exact h)
      rw [ite_eq_left h, ite_eq_left hzpos, h1,
        show ρ ^ 2 * Ainv * (1 * (κ * ((ρ ^ (3 * a) / B σ) ^ (-(3 / (3 * a)))
            / Real.cos θ)))
          = ρ ^ 2 * Ainv * (κ * ((ρ ^ (3 * a) / B σ) ^ (-(3 / (3 * a)))
              / Real.cos θ)) by ring,
        sb0_gauge_alg ha hρ hBσ, hcos]
  have hmain : ρ ^ 2 * Ainv * (Work.FTS.FinalV2.psiFire Φs E g χ θ σ
        - psiHatP (Work.FTS.Regularity.pExp a) Φs E g χ θ σ)
      = (if 0 < z then (κ * Ainv * B σ ^ (1 / a)) / r
          else -((κ * Ainv * B σ ^ (1 / a)) / r)) := by
    rw [hA]; exact hkey
  have step : ρ ^ 2 * Ainv * (Work.FTS.FinalV2.psiFire Φs E g χ θ σ)
      = ρ ^ 2 * Ainv * (psiHatP (Work.FTS.Regularity.pExp a) Φs E g χ θ σ)
        + (if 0 < z then (κ * Ainv * B σ ^ (1 / a)) / r
            else -((κ * Ainv * B σ ^ (1 / a)) / r)) := by
    have h := hmain
    rw [mul_sub] at h
    linarith
  rw [step]

/-! ## §5 `psiField` bookkeeping -/

/-- `psiField` depends on `ψ` only through its values on the cross (the radial and the axial line)
through `x`, plus the value at `x` itself.  Only `deriv` congruence along the two lines is used,
so no differentiability is required. -/
theorem psiField_congr_of_cross {f g : ℝ → ℝ → ℝ} {x : Work.Cyl.R3}
    (hZ : (fun z' => f (Work.Cyl.radial x) z') =ᶠ[𝓝 (Work.Cyl.axial x)]
      (fun z' => g (Work.Cyl.radial x) z'))
    (hR : (fun r' => f r' (Work.Cyl.axial x)) =ᶠ[𝓝 (Work.Cyl.radial x)]
      (fun r' => g r' (Work.Cyl.axial x)))
    (h0 : f (Work.Cyl.radial x) (Work.Cyl.axial x)
      = g (Work.Cyl.radial x) (Work.Cyl.axial x)) :
    Work.Cyl.psiField f x = Work.Cyl.psiField g x := by
  have hz := hZ.deriv_eq
  have hr := hR.deriv_eq
  simp only [Work.Cyl.psiField, Work.Cyl.cylField, Work.Cyl.pdZ, Work.Cyl.pdR, h0]
  rw [hz, hr]

/-- The complement of `{0}` is a neighbourhood of any nonzero real. -/
theorem ne_mem_nhds {r : ℝ} (hr : r ≠ 0) : ({r' : ℝ | r' ≠ 0} : Set ℝ) ∈ 𝓝 r :=
  isOpen_ne.mem_nhds hr

/-- The jump sheet `(r,z) ↦ ±c/r` is differentiable off the axis. -/
theorem differentiableAt_jump (c r z : ℝ) (hr : r ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => (if 0 < p.2 then c / p.1 else -(c / p.1)))
      (r, z) := by
  have hconst : (fun p : ℝ × ℝ => (if 0 < p.2 then c / p.1 else -(c / p.1)))
      =ᶠ[𝓝 (r, z)] (fun p : ℝ × ℝ => (if 0 < z then c else -c) / p.1) := by
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hlt] with p hp
      rw [ite_eq_right (not_lt.mpr hp.le), ite_eq_right (not_lt.mpr hlt.le), neg_div]
    · filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hgt] with p hp
      rw [ite_eq_left hp, ite_eq_left hgt]
  have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => (if 0 < z then c else -c) / p.1) (r, z) := by
    have hc : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (if 0 < z then c else -c) / p.1) (r, z) :=
      ContDiffAt.div contDiffAt_const (by fun_prop) (by simpa using hr)
    exact hc.differentiableAt (by norm_num)
  exact hd.congr_of_eventuallyEq hconst

/-! ## §6 The target -/

theorem sb0_psiField {a : ℝ} (ha : 0 < a) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {A B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hC3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3
      (fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd)
    (hdec : ∀ τ : ℝ, 0 ≤ τ → ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ
        = Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ
          + κ * Work.FTS.StreamBdryIface.gaugeMode (Work.FTS.Regularity.pExp a) z θ)
    (hPsm : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.oddPerS
        (Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)))
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
      Work.Cyl.psiField (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp a) A B
          (Work.FTS.FinalV2.psiFire Φs E g) C r z t) x
        = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi a A B
          (Work.FTS.StreamBdryIface.psiHatP (Work.FTS.Regularity.pExp a) Φs E g) C r z t) x := by
  intro t ht x hx
  set σ := Work.FTS.Physical.clockInv C t with hσ
  have hτ : 0 ≤ σ := by rw [hσ]; exact Work.FTS.Physical.clockInv_nonneg C ⟨ht.1.le, ht.2⟩
  obtain ⟨κ, hκ⟩ := hdec σ hτ
  have hBσ : 0 < B σ := by rw [hσ]; exact hB σ hτ
  have hr : 0 < Work.Cyl.radial x := Work.FTS.BSIdent.radial_pos_of_mem_Uax hx
  have hz : Work.Cyl.axial x ≠ 0 := Work.FTS.BSIdent.axial_ne_zero_of_mem_Uax hx
  set ψF : ℝ → ℝ → ℝ := fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp a) A B
      (Work.FTS.FinalV2.psiFire Φs E g) C r z t with hψF
  set ψB : ℝ → ℝ → ℝ := fun r z => Work.FTS.BSIdent.merPsi a A B
      (psiHatP (Work.FTS.Regularity.pExp a) Φs E g) C r z t with hψB
  set c0 : ℝ := κ * (A σ)⁻¹ * B σ ^ (1 / a) with hc0
  set Δ : ℝ → ℝ → ℝ := fun r z => if 0 < z then c0 / r else -(c0 / r) with hΔ
  -- §6.1 the two stream functions differ by the jump sheet, off the equatorial plane
  have hpoint : ∀ r z : ℝ, 0 < r → z ≠ 0 → ψF r z = ψB r z + Δ r z := by
    intro r z hr hz
    rw [hψF, hψB, hΔ, hc0]
    exact merPsi_diff ha (hdecκ := fun z θ hzθ => hκ z θ hzθ) hr hz (by rw [← hσ]; exact hBσ)
  -- §6.2 they agree with `ψB + Δ` on the cross through `x`
  have hnbZ : ({z' : ℝ | z' ≠ 0} : Set ℝ) ∈ 𝓝 (Work.Cyl.axial x) := ne_mem_nhds hz
  have hZ : (fun z' => ψF (Work.Cyl.radial x) z')
      =ᶠ[𝓝 (Work.Cyl.axial x)]
        (fun z' => ψB (Work.Cyl.radial x) z' + Δ (Work.Cyl.radial x) z') := by
    filter_upwards [hnbZ] with z' hz'
    exact hpoint _ _ hr hz'
  have hnbR : Set.Ioi (0 : ℝ) ∈ 𝓝 (Work.Cyl.radial x) := isOpen_Ioi.mem_nhds hr
  have hR : (fun r' => ψF r' (Work.Cyl.axial x))
      =ᶠ[𝓝 (Work.Cyl.radial x)]
        (fun r' => ψB r' (Work.Cyl.axial x) + Δ r' (Work.Cyl.axial x)) := by
    filter_upwards [hnbR] with r' hr'
    exact hpoint r' _ hr' hz
  have h0 : ψF (Work.Cyl.radial x) (Work.Cyl.axial x)
      = ψB (Work.Cyl.radial x) (Work.Cyl.axial x) + Δ (Work.Cyl.radial x) (Work.Cyl.axial x) :=
    hpoint _ _ hr hz
  have h1 : Work.Cyl.psiField ψF x
      = Work.Cyl.psiField (fun r z => ψB r z + Δ r z) x :=
    psiField_congr_of_cross hZ hR h0
  -- §6.3 differentiability of the two summands at `x`
  have hdiffB : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψB p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    have hsm := sb0_hsm_psiHatP ha hPsm (τ := σ) hτ
    have hCd := Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice a A B
      (psiHatP (Work.FTS.Regularity.pExp a) Φs E g) C t (by rw [← hσ]; exact hBσ) hsm hr hz
    exact hCd.differentiableAt (by norm_num)
  have hdiffΔ : DifferentiableAt ℝ (fun p : ℝ × ℝ => Δ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    rw [hΔ]
    exact differentiableAt_jump c0 _ _ (ne_of_gt hr) hz
  -- §6.4 additivity and the vanishing of the jump sheet
  have h2 := sb0_psiFieldAdd (f := ψB) (g := Δ) (x := x) hdiffB hdiffΔ
  have h3 := sb0_psiFieldJump c0 (x := x) hr hz
  rw [h1, h2, hΔ, h3, add_zero]

end Work.FTS_StreamBdry.SB0
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB2.sb2_c2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

open scoped Real Topology
open Set Filter
open Work.FTS.StreamBdryIface (oddPerS psiP)

set_option autoImplicit false

noncomputable section

/-! ## §6 The main assembly

For a `C²` function `P` on the open quadrant whose two edge traces at `θ = 0` and `θ = π/2` are
those of `psiP` (`Edge0`, `EdgePi`), the odd/`π`-reflection `oddPerS P` is `C²` on the strip
`(0,∞) × (-(π/2)-1, π/2+1)`.

The two seams `θ = 0` and `θ = π/2` are glued with `SB25.glue_line_C2` (radius `π/2`): the two
branches are `-P(-·)` resp. `-P(π-·)`, whose partials are known by `BrNegFacts`/`BrMirFacts`; the
one-sided limits at the seam are the `Edge0`/`EdgePi` data.  The remaining strip is obtained from
the `C²`-ness on `(0,π)` by the odd reflection `OddReflectC2`. -/

private theorem oddPerS_strip_c2 {P : ℝ → ℝ → ℝ}
    (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    (hPmid : ∀ w, P w (Real.pi / 2) = 0)
    (hBrNeg : ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (-θ)))
        (Strip (-(Real.pi / 2)) 0) ∧
      (∀ w θ, 0 < w → -(Real.pi / 2) < θ → θ < 0 →
        Work.Spaces.pz (fun w θ => -P w (-θ)) w θ = -Work.Spaces.pz P w (-θ) ∧
        Work.Spaces.pth (fun w θ => -P w (-θ)) w θ = Work.Spaces.pth P w (-θ) ∧
        Work.Spaces.pz (Work.Spaces.pz (fun w θ => -P w (-θ))) w θ
          = -Work.Spaces.pz (Work.Spaces.pz P) w (-θ) ∧
        Work.Spaces.pth (Work.Spaces.pz (fun w θ => -P w (-θ))) w θ
          = Work.Spaces.pth (Work.Spaces.pz P) w (-θ) ∧
        Work.Spaces.pz (Work.Spaces.pth (fun w θ => -P w (-θ))) w θ
          = Work.Spaces.pz (Work.Spaces.pth P) w (-θ) ∧
        Work.Spaces.pth (Work.Spaces.pth (fun w θ => -P w (-θ))) w θ
          = -Work.Spaces.pth (Work.Spaces.pth P) w (-θ)))
    (hBrMir : ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (Real.pi - θ)))
        (Strip (Real.pi / 2) Real.pi) ∧
      (∀ w θ, 0 < w → Real.pi / 2 < θ → θ < Real.pi →
        Work.Spaces.pz (fun w θ => -P w (Real.pi - θ)) w θ
            = -Work.Spaces.pz P w (Real.pi - θ) ∧
        Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) w θ
            = Work.Spaces.pth P w (Real.pi - θ) ∧
        Work.Spaces.pz (Work.Spaces.pz (fun w θ => -P w (Real.pi - θ))) w θ
          = -Work.Spaces.pz (Work.Spaces.pz P) w (Real.pi - θ) ∧
        Work.Spaces.pth (Work.Spaces.pz (fun w θ => -P w (Real.pi - θ))) w θ
          = Work.Spaces.pth (Work.Spaces.pz P) w (Real.pi - θ) ∧
        Work.Spaces.pz (Work.Spaces.pth (fun w θ => -P w (Real.pi - θ))) w θ
          = Work.Spaces.pz (Work.Spaces.pth P) w (Real.pi - θ) ∧
        Work.Spaces.pth (Work.Spaces.pth (fun w θ => -P w (Real.pi - θ))) w θ
          = -Work.Spaces.pth (Work.Spaces.pth P) w (Real.pi - θ)))
    (hE0 : Edge0 P) (hEP : EdgePi P) :
    ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) := by
  obtain ⟨hodd, hpos, hneg, hgt, hzero⟩ :=
    Work.FTS_StreamBdry.SB25.oddPerS_pieces P hPmid
  -- the agreement of the six partials with those of the two branches
  have hAgA := partials_eqOn_of_eqOn (U := Strip 0 (Real.pi / 2)) (f := oddPerS P) (g := P)
    (isOpen_Ioi.prod isOpen_Ioo)
    (fun p hp => hpos p.1 p.2 hp.2.1 hp.2.2.le)
  have hAgB := partials_eqOn_of_eqOn (U := Strip (-(Real.pi / 2)) 0) (f := oddPerS P)
    (g := fun w θ => -P w (-θ))
    (isOpen_Ioi.prod isOpen_Ioo)
    (fun p hp => hneg p.1 p.2 hp.2.1.le hp.2.2)
  have hAgC := partials_eqOn_of_eqOn (U := Strip (Real.pi / 2) Real.pi) (f := oddPerS P)
    (g := fun w θ => -P w (Real.pi - θ))
    (isOpen_Ioi.prod isOpen_Ioo)
    (fun p hp => hgt p.1 p.2 hp.2.1 hp.2.2)
  -- smoothness on the three open pieces
  have hA_h : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P)) (Strip 0 (Real.pi / 2)) :=
    (hP2.mono strip_le_Qd).congr
      (fun p hp => hpos p.1 p.2 hp.2.1 hp.2.2.le)
  have hB_h : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P)) (Strip (-(Real.pi / 2)) 0) :=
    hBrNeg.1.congr (fun p hp => hneg p.1 p.2 hp.2.1.le hp.2.2)
  have hC_h : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P)) (Strip (Real.pi / 2) Real.pi) :=
    hBrMir.1.congr (fun p hp => hgt p.1 p.2 hp.2.1 hp.2.2)
  -- the punctured strips of the two gluings
  have hsetS0 : Work.FTS_StreamBdry.SB25.glueS 0 (Real.pi / 2)
      = Strip (-(Real.pi / 2)) 0 ∪ Strip 0 (Real.pi / 2) := by
    simp only [Work.FTS_StreamBdry.SB25.glueS, Strip, Set.prod_union]
    rw [show (0 : ℝ) - Real.pi / 2 = -(Real.pi / 2) from by ring,
      show (0 : ℝ) + Real.pi / 2 = Real.pi / 2 from by ring]
  have hsetS1 : Work.FTS_StreamBdry.SB25.glueS (Real.pi / 2) (Real.pi / 2)
      = Strip 0 (Real.pi / 2) ∪ Strip (Real.pi / 2) Real.pi := by
    simp only [Work.FTS_StreamBdry.SB25.glueS, Strip, Set.prod_union]
    rw [show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) from by ring,
      show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]
  have hglueS0 : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueS 0 (Real.pi / 2)) := by
    rw [hsetS0]
    exact contDiffOn_union_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
      (isOpen_Ioi.prod isOpen_Ioo) hB_h hA_h
  have hglueS1 : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueS (Real.pi / 2) (Real.pi / 2)) := by
    rw [hsetS1]
    exact contDiffOn_union_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
      (isOpen_Ioi.prod isOpen_Ioo) hA_h hC_h
  -- continuity on the two full strips
  have hglueU0 : ContinuousOn (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueU 0 (Real.pi / 2)) := by
    rintro ⟨w, θ⟩ hp
    rw [Work.FTS_StreamBdry.SB25.mem_glueU] at hp
    obtain ⟨hw, h1, h2⟩ := hp
    rcases lt_trichotomy θ 0 with h | h | h
    · exact (hB_h.continuousOn.continuousAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (w, θ) ∈ Strip (-(Real.pi / 2)) 0 from ⟨hw, by linarith, h⟩))).continuousWithinAt
    · subst h
      have hval : Function.uncurry (oddPerS P) (w, 0) = 0 := by
        simpa only [Function.uncurry] using hzero w
      refine (continuousAt_seam0 hw hval ?_ ?_ ?_).continuousWithinAt
      · refine Tendsto.congr' (f₁ := Function.uncurry P)
          (f₂ := Function.uncurry (oddPerS P)) ?_
          ((hE0 w hw).1.mono_left (nhdsWithin_mono _ strip_le_Qd))
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hpos q.1 q.2 hq.2.1 hq.2.2.le).symm
      · have hmain : Tendsto (fun q : ℝ × ℝ => -(P q.1 (-q.2)))
            (𝓝[Strip (-(Real.pi / 2)) 0] (w, 0)) (𝓝 0) := by
          have h1' : Tendsto (fun q : ℝ × ℝ => P q.1 (-q.2))
              (𝓝[Strip (-(Real.pi / 2)) 0] (w, 0)) (𝓝 0) :=
            tendsto_neg_comp (hE0 w hw).1
          simpa using h1'.neg
        refine Tendsto.congr' (f₁ := fun q : ℝ × ℝ => -(P q.1 (-q.2)))
          (f₂ := Function.uncurry (oddPerS P)) ?_ hmain
        filter_upwards [self_mem_nhdsWithin] with q hq
        show -(P q.1 (-q.2)) = oddPerS P q.1 q.2
        exact (hneg q.1 q.2 hq.2.1.le hq.2.2).symm
      · refine Tendsto.congr' (f₁ := fun _ : ℝ × ℝ => (0 : ℝ))
          (f₂ := Function.uncurry (oddPerS P)) ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with q hq
        rw [Set.mem_prod, Set.mem_singleton_iff] at hq
        show (0 : ℝ) = oddPerS P q.1 q.2
        rw [hq.2]
        exact (hzero q.1).symm
    · exact (hA_h.continuousOn.continuousAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (w, θ) ∈ Strip 0 (Real.pi / 2) from ⟨hw, h, by linarith⟩))).continuousWithinAt
  have hglueU1 : ContinuousOn (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueU (Real.pi / 2) (Real.pi / 2)) := by
    rintro ⟨w, θ⟩ hp
    rw [Work.FTS_StreamBdry.SB25.mem_glueU] at hp
    obtain ⟨hw, h1, h2⟩ := hp
    rcases lt_trichotomy θ (Real.pi / 2) with h | h | h
    · exact (hA_h.continuousOn.continuousAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (w, θ) ∈ Strip 0 (Real.pi / 2) from ⟨hw, by linarith, h⟩))).continuousWithinAt
    · subst h
      refine (continuousAt_seamPi hw ?_ ?_ ?_ ?_).continuousWithinAt
      · show oddPerS P w (Real.pi / 2) = 0
        rw [hpos w (Real.pi / 2) (by linarith [Real.pi_pos]) le_rfl]
        exact hPmid w
      · have hmain : Tendsto (fun q : ℝ × ℝ => -(P q.1 (Real.pi - q.2)))
            (𝓝[Strip (Real.pi / 2) Real.pi] (w, Real.pi / 2)) (𝓝 0) := by
          have h1' : Tendsto (fun q : ℝ × ℝ => P q.1 (Real.pi - q.2))
              (𝓝[Strip (Real.pi / 2) Real.pi] (w, Real.pi / 2)) (𝓝 0) :=
            tendsto_sub_comp (hEP w hw).1
          simpa using h1'.neg
        refine Tendsto.congr' (f₁ := fun q : ℝ × ℝ => -(P q.1 (Real.pi - q.2)))
          (f₂ := Function.uncurry (oddPerS P)) ?_ hmain
        filter_upwards [self_mem_nhdsWithin] with q hq
        show -(P q.1 (Real.pi - q.2)) = oddPerS P q.1 q.2
        exact (hgt q.1 q.2 hq.2.1 hq.2.2).symm
      · refine Tendsto.congr' (f₁ := Function.uncurry P)
          (f₂ := Function.uncurry (oddPerS P)) ?_
          ((hEP w hw).1.mono_left (nhdsWithin_mono _ strip_le_Qd))
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hpos q.1 q.2 hq.2.1 hq.2.2.le).symm
      · refine Tendsto.congr' (f₁ := fun _ : ℝ × ℝ => (0 : ℝ))
          (f₂ := Function.uncurry (oddPerS P)) ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with q hq
        rw [Set.mem_prod, Set.mem_singleton_iff] at hq
        show (0 : ℝ) = oddPerS P q.1 q.2
        rw [hq.2, hpos q.1 (Real.pi / 2) (by linarith [Real.pi_pos]) le_rfl]
        exact (hPmid q.1).symm
    · exact (hC_h.continuousOn.continuousAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (w, θ) ∈ Strip (Real.pi / 2) Real.pi from ⟨hw, h, by linarith⟩))).continuousWithinAt
  -- the six limits at the two seams
  have hlim0 : ∀ D ∈ ({Work.Spaces.pz (oddPerS P), Work.Spaces.pth (oddPerS P),
      Work.Spaces.pz (Work.Spaces.pz (oddPerS P)),
      Work.Spaces.pth (Work.Spaces.pz (oddPerS P)),
      Work.Spaces.pz (Work.Spaces.pth (oddPerS P)),
      Work.Spaces.pth (Work.Spaces.pth (oddPerS P))} : Set (ℝ → ℝ → ℝ)),
      ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry D)
        (𝓝[Work.FTS_StreamBdry.SB25.glueS 0 (Real.pi / 2)] (z0, 0)) (𝓝 l) := by
    intro D hD z0 hz0
    obtain ⟨h0P, h0pz, h0pzpz, h0pthpth, ⟨l0pth, h0pth⟩, ⟨l0mix, h0mix1, h0mix2⟩⟩ :=
      hE0 z0 hz0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, tendsto_seam0 (D := Work.Spaces.pz (oddPerS P)) (DP := Work.Spaces.pz P) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).1]; ring)
        h0pz (by ring)⟩
    · exact ⟨l0pth, tendsto_seam0 (D := Work.Spaces.pth (oddPerS P)) (DP := Work.Spaces.pth P) (σ := 1) (l := l0pth)
        (fun w θ hq => hAgA.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.1]; ring)
        h0pth (by ring)⟩
    · exact ⟨0, tendsto_seam0 (D := Work.Spaces.pz (Work.Spaces.pz (oddPerS P))) (DP := Work.Spaces.pz (Work.Spaces.pz P)) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.2.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.2.1]; ring)
        h0pzpz (by ring)⟩
    · exact ⟨l0mix, tendsto_seam0 (D := Work.Spaces.pth (Work.Spaces.pz (oddPerS P))) (DP := Work.Spaces.pth (Work.Spaces.pz P)) (σ := 1) (l := l0mix)
        (fun w θ hq => hAgA.2.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.2.2.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.1]; ring)
        h0mix2 (by ring)⟩
    · exact ⟨l0mix, tendsto_seam0 (D := Work.Spaces.pz (Work.Spaces.pth (oddPerS P))) (DP := Work.Spaces.pz (Work.Spaces.pth P)) (σ := 1) (l := l0mix)
        (fun w θ hq => hAgA.2.2.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.2.2.2.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.2.1]; ring)
        h0mix1 (by ring)⟩
    · exact ⟨0, tendsto_seam0 (D := Work.Spaces.pth (Work.Spaces.pth (oddPerS P))) (DP := Work.Spaces.pth (Work.Spaces.pth P)) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.2.2.2.2.2 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.2.2.2.2 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.2.2]; ring)
        h0pthpth (by ring)⟩
  have hlim1 : ∀ D ∈ ({Work.Spaces.pz (oddPerS P), Work.Spaces.pth (oddPerS P),
      Work.Spaces.pz (Work.Spaces.pz (oddPerS P)),
      Work.Spaces.pth (Work.Spaces.pz (oddPerS P)),
      Work.Spaces.pz (Work.Spaces.pth (oddPerS P)),
      Work.Spaces.pth (Work.Spaces.pth (oddPerS P))} : Set (ℝ → ℝ → ℝ)),
      ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry D)
        (𝓝[Work.FTS_StreamBdry.SB25.glueS (Real.pi / 2) (Real.pi / 2)] (z0, Real.pi / 2))
        (𝓝 l) := by
    intro D hD z0 hz0
    obtain ⟨h0P, h0pz, h0pzpz, h0pthpth, ⟨l0pth, h0pth⟩, ⟨l0mix, h0mix1, h0mix2⟩⟩ :=
      hEP z0 hz0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, tendsto_seamPi (D := Work.Spaces.pz (oddPerS P)) (DP := Work.Spaces.pz P) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).1]; ring)
        h0pz (by ring)⟩
    · exact ⟨l0pth, tendsto_seamPi (D := Work.Spaces.pth (oddPerS P)) (DP := Work.Spaces.pth P) (σ := 1) (l := l0pth)
        (fun w θ hq => hAgA.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.1]; ring)
        h0pth (by ring)⟩
    · exact ⟨0, tendsto_seamPi (D := Work.Spaces.pz (Work.Spaces.pz (oddPerS P))) (DP := Work.Spaces.pz (Work.Spaces.pz P)) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.2.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.2.1]; ring)
        h0pzpz (by ring)⟩
    · exact ⟨l0mix, tendsto_seamPi (D := Work.Spaces.pth (Work.Spaces.pz (oddPerS P))) (DP := Work.Spaces.pth (Work.Spaces.pz P)) (σ := 1) (l := l0mix)
        (fun w θ hq => hAgA.2.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.2.2.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.1]; ring)
        h0mix2 (by ring)⟩
    · exact ⟨l0mix, tendsto_seamPi (D := Work.Spaces.pz (Work.Spaces.pth (oddPerS P))) (DP := Work.Spaces.pz (Work.Spaces.pth P)) (σ := 1) (l := l0mix)
        (fun w θ hq => hAgA.2.2.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.2.2.2.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.2.1]; ring)
        h0mix1 (by ring)⟩
    · exact ⟨0, tendsto_seamPi (D := Work.Spaces.pth (Work.Spaces.pth (oddPerS P))) (DP := Work.Spaces.pth (Work.Spaces.pth P)) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.2.2.2.2.2 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.2.2.2.2 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.2.2]; ring)
        h0pthpth (by ring)⟩
  -- the two gluings
  have hC2_0 : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueU 0 (Real.pi / 2)) :=
    Work.FTS_StreamBdry.SB25.glue_line_C2 (oddPerS P) 0 (Real.pi / 2)
      (by linarith [Real.pi_pos]) hglueS0 hglueU0 hlim0
  have hC2_1 : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueU (Real.pi / 2) (Real.pi / 2)) :=
    Work.FTS_StreamBdry.SB25.glue_line_C2 (oddPerS P) (Real.pi / 2) (Real.pi / 2)
      (by linarith [Real.pi_pos]) hglueS1 hglueU1 hlim1
  -- the odd reflection of the `(0,π)` strip
  have hC2_1' : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 Real.pi) := by
    have hset : Work.FTS_StreamBdry.SB25.glueU (Real.pi / 2) (Real.pi / 2)
        = Set.Ioi 0 ×ˢ Set.Ioo 0 Real.pi := by
      simp only [Work.FTS_StreamBdry.SB25.glueU]
      rw [show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) from by ring,
        show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]
    rw [← hset]
    exact hC2_1
  have hC2_neg : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P)) (Strip (-Real.pi) 0) :=
    OddReflectC2 hodd hC2_1'
  -- the cover
  have hpi : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  rintro ⟨w, θ⟩ hp
  rw [Set.mem_prod] at hp
  obtain ⟨hw, h1, h2⟩ := hp
  rcases lt_trichotomy θ 0 with h | h | h
  · exact (hC2_neg.contDiffAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
        (show (w, θ) ∈ Strip (-Real.pi) 0 from ⟨hw, by linarith, h⟩))).contDiffWithinAt
  · subst h
    refine (hC2_0.contDiffAt ?_).contDiffWithinAt
    exact (Work.FTS_StreamBdry.SB25.isOpen_glueU 0 (Real.pi / 2)).mem_nhds (by
      rw [Work.FTS_StreamBdry.SB25.mem_glueU]
      exact ⟨hw, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  · refine (hC2_1.contDiffAt ?_).contDiffWithinAt
    exact (Work.FTS_StreamBdry.SB25.isOpen_glueU (Real.pi / 2) (Real.pi / 2)).mem_nhds (by
      rw [Work.FTS_StreamBdry.SB25.mem_glueU]
      exact ⟨hw, by linarith [hpi], by linarith [h2, Real.pi_pos, hpi]⟩)

theorem sb2_c2 {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hdthDV : ∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))) z θ| ≤ K') :
    ContDiffOn ℝ 2 (Function.uncurry
      (Work.FTS.StreamBdryIface.oddPerS (Work.FTS.StreamBdryIface.psiP αG Ψ)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) := by
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hPmid : ∀ w, psiP αG Ψ w (Real.pi / 2) = 0 := by
    intro w
    rw [Work.FTS_StreamBdry.psiP_eq_Iint]
    have hs2 : Work.Construction.s2 (Real.pi / 2) = 0 := by
      rw [Work.Construction.s2_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    rw [hs2]
    ring
  have hE0 : Edge0 (psiP αG Ψ) := fun z0 hz0 =>
    Work.FTS_StreamBdry.SB25.psiP_edge_zero (αG := αG) (M := M) (L := L) (Mf := Mf)
      hαG hsol h3 hslot hF hdthDV z0 hz0
  have hEP : EdgePi (psiP αG Ψ) := fun z0 hz0 =>
    Work.FTS_StreamBdry.SB25.psiP_edge_axis (αG := αG) (M := M) (L := L) (Mf := Mf)
      hαG hsol h3 hslot hF hdthDV z0 hz0
  exact oddPerS_strip_c2 hP2 hPmid
    (BrNegFacts hP2) (BrMirFacts hP2) hE0 hEP

end

end Work.FTS_StreamBdry.SB2
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB5.Core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB5.Core` — the core decay lemma `sb5_decay_core` and the `psiP` `θ`-bounds.
-/

namespace Work.FTS_StreamBdry.SB5

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## §9 The core decay lemma -/

/-- **Core decay.**  If `P` is the `U`-slot part with source `F` supported in `z < L`, with the
`D_z`-bounds `|D_z^j P| ≤ M sin 2θ` (`j ≤ 2`), the `θ`-bounds `|∂_θP|, |∂_θ²P| ≤ K` and the
pointwise decay `P z θ → 0` (`z → ∞`) at every fixed `θ ∈ (0,π/2)`, then
`|D_z^j P z θ| ≤ M sin 2θ (L/z)^{4/α}` for `z ≥ L`, `j ≤ 2`. -/
theorem sb5_decay_core {α M L K : ℝ} (hα : 0 < α) (hL : 0 < L) {P F : ℝ → ℝ → ℝ}
    (hP3 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd)
    (hbsl : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Elliptic.bslOp α P z θ = F z θ)
    (hF0 : ∀ z θ, L ≤ z → θ ∈ Work.Spaces.Iθ → F z θ = 0)
    (hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j P z θ| ≤ M * Work.Construction.s2 θ)
    (hK1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pth P z θ| ≤ K)
    (hK2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pthIter 2 P z θ| ≤ K)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => P z θ) atTop (𝓝 0))
    (hbar : Work.FTS.StreamBdryIface.SB5Barrier) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j P z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hαk_eq : α * (4 / α) = 4 := by field_simp
  have hαk : 0 < α * (4 / α) := by rw [hαk_eq]; norm_num
  have hαk5 : α * (4 / α) < 5 := by rw [hαk_eq]; norm_num
  have hV : IsOpen Work.Construction.Qd := isOpen_Qd
  have hPd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z, θ) := fun z θ hzθ =>
    (hP3.contDiffAt (hV.mem_nhds hzθ)).differentiableAt (by norm_num)
  have hPth : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth P)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd (n := 2)
      (show ContDiffOn ℝ ((2 : WithTop ℕ∞) + 1) (Function.uncurry P)
        Work.Construction.Qd from hP3)
  have hPd2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) (z, θ) := fun z θ hzθ =>
    (hPth.contDiffAt (hV.mem_nhds hzθ)).differentiableAt (by norm_num)
  have hsquare : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun θ' => P z θ') θ ∧
        DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P z θ') θ := fun z θ hzθ =>
    ⟨Work.Spaces.differentiableAt_curry_right (hPd z θ hzθ),
      Work.Spaces.differentiableAt_curry_right (hPd2 z θ hzθ)⟩
  -- the `sb5_compare` mechanism, with the four variable hypotheses supplied per function
  have hcompare : ∀ (Q : ℝ → ℝ → ℝ) (Mb : ℝ),
      ContDiffOn ℝ 2 (Function.uncurry Q) Work.Construction.Qd →
      (∀ z θ, L < z → θ ∈ Ioo (0 : ℝ) (π / 2) → Work.Elliptic.bslOp α Q z θ = 0) →
      (∀ z θ, L ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) → |Q z θ| ≤ Mb * Work.Construction.s2 θ) →
      (∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
        |Q z θ| ≤ ε * Work.Construction.s2 θ) →
      ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
        |Q z θ| ≤ Mb * Work.Construction.s2 θ * (L / z) ^ (4 / α) :=
    fun Q Mb hC2 hbslQ hbdQ hdecQ z θ hzθ hLz =>
      Work.FTS_StreamBdry.SB25.sb5_compare α (4 / α) L Mb Q hα hL hαk hαk5 hbar hC2 hbslQ
        hbdQ hdecQ z θ hLz (Work.FTS_StreamBdry.mem_Qd.mp hzθ).2
  -- ## j = 0
  have hj0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |P z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
    intro z θ hzθ hLz
    obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
    exact hcompare P M (hP3.of_le (by norm_num))
      (fun z θ hz hθ => by
        have hmem : (z, θ) ∈ Work.Construction.Qd :=
          Work.FTS_StreamBdry.mem_Qd.mpr ⟨lt_trans hL hz, hθ.1, hθ.2⟩
        rw [hbsl z θ hmem]
        exact hF0 z θ (le_of_lt hz) (Work.FTS_StreamBdry.Qd_theta_Iθ hmem))
      (fun z θ hz hθ =>
        hDz z θ (Work.FTS_StreamBdry.mem_Qd.mpr ⟨lt_of_lt_of_le hL hz, hθ.1, hθ.2⟩)
          0 (by norm_num))
      (fun ε hε => uniform_decay_of_data hsquare hK1 hK2
        (fun z hz => tendsto_zero_endpoints_of_abs_le_s2
          (fun z θ hzθ => hDz z θ hzθ 0 (by norm_num)) hz)
        (fun θ hθ => hdec θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) ε hε)
      z θ hzθ hLz
  -- ## j = 1
  have hj1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |Work.Spaces.DzIter 1 P z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
    intro z θ hzθ hLz
    obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
    have hdecθ : Tendsto (fun z => P z θ) atTop (𝓝 0) := hdec θ ⟨le_of_lt hθ1, le_of_lt hθ2⟩
    rcases eq_or_lt_of_le hLz with hzL | hzLt
    · rw [hzL, div_self (ne_of_gt hz0), Real.one_rpow, mul_one]
      exact hDz z θ hzθ 1 (by norm_num)
    · have hconv : Tendsto (fun h' : ℝ => dilDiff P h' z θ) (𝓝[>] (0 : ℝ))
          (𝓝 (Work.Spaces.DzIter 1 P z θ)) := by
        have hdq := Work.FTS_StreamBdry.SB25.dq1_facts (fun z' => P z' θ) L
          (M * Work.Construction.s2 θ) hL
          (fun z' hz' => Work.Spaces.differentiableAt_curry_left
            (hPd z' θ (Work.FTS_StreamBdry.mem_Qd.mpr
              ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩)))
          (fun z' hz' => by
            have h := hDz z' θ (Work.FTS_StreamBdry.mem_Qd.mpr
              ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩) 1 (by norm_num)
            simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
              Work.Spaces.pz] using h)
        simpa only [dilDiff, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
          Work.Spaces.pz] using hdq.2 z hzLt
      have hbound : ∀ᶠ h' in 𝓝[>] (0 : ℝ),
          |dilDiff P h' z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
        filter_upwards [self_mem_nhdsWithin] with h' hh'
        exact hcompare (dilDiff P h') M (contDiffOn_dilDiff_three (h := h') hP3)
          (fun z' θ' hz' hθ' => bslOp_dilDiff_eq_zero hL hP3 hbsl hF0 hh' hz' hθ')
          (fun z' θ' hz' hθ' => by
            have h := (Work.FTS_StreamBdry.SB25.dq1_facts (fun z'' => P z'' θ') L
              (M * Work.Construction.s2 θ') hL
              (fun z'' hz'' => Work.Spaces.differentiableAt_curry_left
                (hPd z'' θ' (Work.FTS_StreamBdry.mem_Qd.mpr
                  ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩)))
              (fun z'' hz'' => by
                have h2 := hDz z'' θ' (Work.FTS_StreamBdry.mem_Qd.mpr
                  ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩) 1 (by norm_num)
                simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
                  Work.Spaces.pz] using h2)).1 h' hh' z' hz'
            simpa only [dilDiff] using h)
          (fun ε hε => uniform_decay_of_data
            (fun z' θ' hzθ' => ⟨
              Work.Spaces.differentiableAt_curry_right
                (((contDiffOn_dilDiff_three (h := h') hP3).contDiffAt
                  (hV.mem_nhds hzθ')).differentiableAt (by norm_num)),
              differentiableAt_pth_dilDiff (Work.FTS_StreamBdry.mem_Qd.mp hzθ').1
                ⟨(Work.FTS_StreamBdry.mem_Qd.mp hzθ').2.1,
                  (Work.FTS_StreamBdry.mem_Qd.mp hzθ').2.2⟩ hPd hPd2⟩)
            (fun z' θ' hzθ' => abs_pth_dilDiff_le hh' hK1 hPd hzθ')
            (fun z' θ' hzθ' => abs_pthIter2_dilDiff_le hh' hK2 hPd hPd2 hzθ')
            (fun z' hz' => tendsto_zero_endpoints_of_abs_le_s2
              (fun a b hab => abs_dilDiff_le_s2 hh'
                (fun w θ hw => hDz w θ hw 0 (by norm_num)) hab) hz')
            (fun θ' hθ' => tendsto_dilDiff_atTop hh'
              (hdec θ' ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩))
            ε hε)
          z θ hzθ hLz
      exact le_of_tendsto hconv.abs hbound
  -- ## j = 2
  have hj2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |Work.Spaces.DzIter 2 P z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
    intro z θ hzθ hLz
    obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
    rcases eq_or_lt_of_le hLz with hzL | hzLt
    · rw [hzL, div_self (ne_of_gt hz0), Real.one_rpow, mul_one]
      exact hDz z θ hzθ 2 (by norm_num)
    · have h1sm : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DzIter 1 P))
          Work.Construction.Qd := contDiffOn_DzIter_one (n := 2) hP3
      have h2sm : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter 2 P))
          Work.Construction.Qd := contDiffOn_DzIter_two (n := 1) hP3
      have hcont2 : ∀ θ' ∈ Ioo (0 : ℝ) (π / 2),
          ContinuousOn (fun z'' => Work.Spaces.DzIter 2 P z'' θ') (Ici L) :=
        fun θ' hθ' => continuousOn_slice_of_contDiffOn hL hθ' h2sm
      have hconv : Tendsto (fun h' : ℝ => dilDiff2 P h' z θ) (𝓝[>] (0 : ℝ))
          (𝓝 (Work.Spaces.DzIter 2 P z θ)) := by
        have hdq := Work.FTS_StreamBdry.SB25.dq2_facts (fun z' => P z' θ) L
          (M * Work.Construction.s2 θ) hL
          (fun z' hz' => by
            refine ⟨Work.Spaces.differentiableAt_curry_left
              (hPd z' θ (Work.FTS_StreamBdry.mem_Qd.mpr
                ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩)), ?_⟩
            exact Work.Spaces.differentiableAt_curry_left
              ((h1sm.contDiffAt (hV.mem_nhds (Work.FTS_StreamBdry.mem_Qd.mpr
                ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩))).differentiableAt (by norm_num)))
          (fun z' hz' => hcont2 θ ⟨hθ1, hθ2⟩ z' hz')
          (fun z' hz' => by
            have h := hDz z' θ (Work.FTS_StreamBdry.mem_Qd.mpr
              ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩) 2 (by norm_num)
            simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
              Work.Spaces.pz] using h)
        simpa only [dilDiff2, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
          Work.Spaces.pz] using hdq.2 z hzLt
      have hbound : ∀ᶠ h' in 𝓝[>] (0 : ℝ),
          |dilDiff2 P h' z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
        filter_upwards [self_mem_nhdsWithin] with h' hh'
        refine hcompare (dilDiff2 P h') M (contDiffOn_dilDiff2_three (h := h') hP3)
          (fun z' θ' hz' hθ' => bslOp_dilDiff2_eq_zero hL hP3 hbsl hF0 hh' hz' hθ')
          (fun z' θ' hz' hθ' => by
            have h := (Work.FTS_StreamBdry.SB25.dq2_facts (fun z'' => P z'' θ') L
              (M * Work.Construction.s2 θ') hL
              (fun z'' hz'' => by
                refine ⟨Work.Spaces.differentiableAt_curry_left
                  (hPd z'' θ' (Work.FTS_StreamBdry.mem_Qd.mpr
                    ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩)), ?_⟩
                exact Work.Spaces.differentiableAt_curry_left
                  ((h1sm.contDiffAt (hV.mem_nhds (Work.FTS_StreamBdry.mem_Qd.mpr
                    ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩))).differentiableAt (by norm_num)))
              (fun z'' hz'' => hcont2 θ' hθ' z'' hz'')
              (fun z'' hz'' => by
                have h2 := hDz z'' θ' (Work.FTS_StreamBdry.mem_Qd.mpr
                  ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩) 2 (by norm_num)
                simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
                  Work.Spaces.pz] using h2)).1 h' hh' z' hz'
            simpa only [dilDiff2] using h)
          (fun ε hε => uniform_decay_of_data
            (fun z' θ' hzθ' => ⟨
              Work.Spaces.differentiableAt_curry_right
                (((contDiffOn_dilDiff2_three (h := h') hP3).contDiffAt
                  (hV.mem_nhds hzθ')).differentiableAt (by norm_num)),
              differentiableAt_pth_dilDiff2 (Work.FTS_StreamBdry.mem_Qd.mp hzθ').1
                ⟨(Work.FTS_StreamBdry.mem_Qd.mp hzθ').2.1,
                  (Work.FTS_StreamBdry.mem_Qd.mp hzθ').2.2⟩ hPd hPd2⟩)
            (fun z' θ' hzθ' => abs_pth_dilDiff2_le hh' hK1 hPd hzθ')
            (fun z' θ' hzθ' => abs_pthIter2_dilDiff2_le hh' hK2 hPd hPd2 hzθ')
            (fun z' hz' => tendsto_zero_endpoints_of_abs_le_s2
              (fun a b hab => abs_dilDiff2_le_s2 hh'
                (fun w θ hw => hDz w θ hw 0 (by norm_num)) hab) hz')
            (fun θ' hθ' => tendsto_dilDiff2_atTop hh'
              (hdec θ' ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩))
            ε hε)
          z θ hzθ hLz
      exact le_of_tendsto hconv.abs hbound
  -- ## assembly
  intro z θ hzθ hLz j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact hj0 z θ hzθ hLz
  · exact hj1 z θ hzθ hLz
  · exact hj2 z θ hzθ hLz

/-! ## §10 The `θ`-bounds and the pointwise decay for `psiP` -/

/-- `|∂_θ psiP| ≤ 3M`: `∂_θP = V(Ψ) + tan θ·P` and `V` cannot see the gauge mode. -/
theorem abs_pth_psiP_le {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| ≤ 3 * M := by
  intro z θ hzθ
  have hV := Work.FTS_StreamBdry.SB3.Vop_psiP_eq hαG h3 hslot z θ hzθ
  have hpth : Work.Spaces.pth (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
      = Work.Construction.Vop Ψ z θ
        + Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ := by
    rw [Work.Construction.Vop] at hV
    linarith
  have h1 : |Work.Construction.Vop Ψ z θ| ≤ M :=
    Work.FTS_StreamBdry.SlotBd.V_le hslot hzθ (j := 0) (by norm_num)
  have h2 : |Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ| ≤ 2 * M := by
    have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hzθ)
    have hs2 : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hzθ
    have hkey : Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ
        = (Real.tan θ * Work.Construction.s2 θ)
          * (Work.FTS.StreamBdryIface.psiP αG Ψ z θ / Work.Construction.s2 θ) := by
      field_simp
    have hsin : |2 * Real.sin θ ^ 2| ≤ 2 := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sin θ ^ 2)]
      nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
    have hdiv : |Work.FTS.StreamBdryIface.psiP αG Ψ z θ / Work.Construction.s2 θ| ≤ M := by
      rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
      exact Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot z θ hzθ 0 (by norm_num)
    rw [hkey, abs_mul, Work.FTS_StreamBdry.tan_mul_s2 hcos]
    exact mul_le_mul hsin hdiv (abs_nonneg _) (by norm_num)
  rw [hpth]
  calc |Work.Construction.Vop Ψ z θ
        + Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ|
      ≤ |Work.Construction.Vop Ψ z θ|
        + |Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ| := abs_add_le _ _
    _ ≤ M + 2 * M := add_le_add h1 h2
    _ ≤ 3 * M := by linarith

/-- The `U`-slot part of a solution decays pointwise in `z` at every fixed `θ`. -/
theorem tendsto_psiP_atTop {αG M : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Tendsto (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z θ) atTop (𝓝 0) := by
  intro θ hθ
  by_cases hθ0 : θ = 0
  · subst hθ0
    have hone : (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z 0) = fun _ => (0 : ℝ) := by
      funext z
      rw [Work.FTS_StreamBdry.psiP_eq_Iint, s2_zero]
      ring
    rw [hone]
    exact tendsto_const_nhds
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
    by_cases hθπ : θ = π / 2
    · subst hθπ
      have hone : (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z (π / 2)) = fun _ => (0 : ℝ) := by
        funext z
        rw [Work.FTS_StreamBdry.psiP_eq_Iint, s2_pi_div_two]
        ring
      rw [hone]
      exact tendsto_const_nhds
    · have hθlt : θ < π / 2 := lt_of_le_of_ne hθ.2 hθπ
      obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M) hαG h3
        hslot (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
        (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
        (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
      have heq : (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z θ)
          =ᶠ[atTop] (fun z => Ψ z θ
            - κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        have h := hκ z θ (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθpos, hθlt⟩)
        linarith
      have h1 : Tendsto (fun z => Ψ z θ) atTop (𝓝 0) := hsol.2.2.2 θ ⟨hθ.1, hθ.2⟩
      have h2 : Tendsto (fun z => κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) atTop
          (𝓝 0) := by
        have hg : Tendsto (fun z : ℝ => z ^ (-(3 / αG))) atTop (𝓝 0) :=
          tendsto_rpow_neg_atTop (by positivity)
        have h3' := hg.const_mul (κ / Real.cos θ)
        simpa only [Work.FTS.StreamBdryIface.gaugeMode, div_eq_mul_inv, mul_comm, mul_left_comm,
          mul_assoc, zero_mul, mul_zero] using h3'
      have h0 : Tendsto (fun z => Ψ z θ
          - κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) atTop (𝓝 (0 - 0)) := h1.sub h2
      refine Tendsto.congr' heq.symm ?_
      simpa using h0


end

end Work.FTS_StreamBdry.SB5
end
