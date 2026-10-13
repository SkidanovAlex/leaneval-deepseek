import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.sb1_gauge_proved
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB25.psiP_edge_zero
import Submission.Work.FTS_StreamBdry.SB25.psiP_edge_axis
import Submission.Work.FTS_StreamBdry.SB25.oddPerS_pieces
import Submission.Work.FTS_StreamBdry.SB0.sb0_psiFieldAdd
import Submission.Work.FTS_StreamBdry.SB0.sb0_psiFieldJump
import Submission.Work.FTS_StreamBdry.SB0.sb0_hsm_psiHatP
import Submission.Work.FTS_StreamBdry.SB0.sb0_gauge_alg
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice

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
