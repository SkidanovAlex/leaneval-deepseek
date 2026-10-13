/-
# `Work.FTS.FinalClock.PhysClock` — manufacturing the clock from the modulation `μ`

Design §2 (`FTS_PHYS_BRIDGE.md`, item 8).  The main theorem is

  `physClock_of_dyn`: from `|muDyn α Φ g τ| ≤ 1/2` for `τ ≥ 0` and the continuity of `muDyn` on
  `[0,∞)`, there is a `PhysClock` whose modulation is `m = fun s ↦ muDyn α Φ g (max s 0)` and
  whose amplitude is `C.A τ = 2 · exp (-∫₀^τ (1 + m s) ds)`.

The factor `2` is correction 2 of the design: the meridian-residual computation of §3 forces
`C.A = 2·A_v`, where `A_v = Avort m` is the vorticity amplitude used in `merProfile`/`physVort`.
The `max`-extension replaces `μ` by its (continuous) extension to `ℝ`, which is what makes the
amplitude differentiable at `τ = 0` two-sidedly as `PhysClock.hAderiv` demands.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.FinalClock.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace Work.FTS.FinalClock

open Work.FTS.Physical (PhysClock)
open Work.FTS.Galerkin (Fam slice muDyn)

/-! ## The clock of a bounded, continuous modulation -/

/-- **The clock of a modulation `m` bounded by `1/2`.**  Its amplitude is the vorticity amplitude
of the design scaled by `2`: `A = 2 · Avort m`, i.e. `A(τ) = 2 e^{-∫₀^τ (1+m)}`; its modulation
is `m` itself.  `A` solves `A' = -(1+m)A` (so `PhysClock.hAderiv` holds), it is positive and
continuous, and `1/2 ≤ 1+m ≤ 3/2` gives `PhysClock.hmu_lo`/`hmu_hi`. -/
noncomputable def physClockOf (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) : PhysClock where
  A := fun τ => 2 * Avort m τ
  mu := m
  hApos := fun τ _ => by
    have := Avort_pos m τ
    linarith
  hAcont := (Avort_continuous hc).const_mul 2 |>.continuousOn
  hAderiv := fun τ _ => by
    have h := (Avort_hasDerivAt hc τ).const_mul 2
    have hval : 2 * (-(1 + m τ) * Avort m τ) = -(1 + m τ) * (2 * Avort m τ) := by ring
    rwa [hval] at h
  hmu_lo := fun τ _ => by linarith [hm.ge τ]
  hmu_hi := fun τ _ => by linarith [hm.le τ]

@[simp] theorem physClockOf_mu (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) :
    (physClockOf m hc hm).mu = m := rfl

@[simp] theorem physClockOf_A (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) :
    (physClockOf m hc hm).A = fun τ : ℝ => 2 * Avort m τ := rfl

theorem physClockOf_A_apply (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) (τ : ℝ) :
    (physClockOf m hc hm).A τ = 2 * Avort m τ := rfl

theorem physClockOf_A_pos (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) (τ : ℝ) :
    0 < (physClockOf m hc hm).A τ := by
  have := Avort_pos m τ
  rw [physClockOf_A_apply]
  linarith

theorem physClockOf_hasDerivAt (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) (τ : ℝ) :
    HasDerivAt (physClockOf m hc hm).A (-(1 + m τ) * (physClockOf m hc hm).A τ) τ := by
  have h := (Avort_hasDerivAt hc τ).const_mul 2
  have hval : 2 * (-(1 + m τ) * Avort m τ) = -(1 + m τ) * (2 * Avort m τ) := by ring
  rw [hval] at h
  simpa only [physClockOf_A] using h

theorem physClockOf_continuous (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) :
    Continuous (physClockOf m hc hm).A :=
  (Avort_continuous hc).const_mul 2

/-! ## The quantitative consequences of the modulation bound -/

/-- The clock of a bounded modulation decays at least like `e^{-τ/2}`. -/
theorem physClockOf_A_le_exp (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    (physClockOf m hc hm).A τ ≤ 2 * Real.exp ((-(1 / 2 : ℝ)) * τ) := by
  rw [physClockOf_A_apply]
  have := Avort_le_exp hm hc hτ
  linarith

/-- The clock of a bounded modulation decays at most like `e^{-3τ/2}`. -/
theorem physClockOf_exp_le_A (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    2 * Real.exp ((-(3 / 2 : ℝ)) * τ) ≤ (physClockOf m hc hm).A τ := by
  rw [physClockOf_A_apply]
  have := exp_le_Avort hm hc hτ
  linarith

/-- The amplitude of the clock is integrable on `[0,∞)`: the blow-up time is finite. -/
theorem physClockOf_integrableOn_A (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) :
    IntegrableOn (physClockOf m hc hm).A (Set.Ioi 0) := by
  have h2 : (physClockOf m hc hm).A = fun τ : ℝ => 2 * Avort m τ := rfl
  rw [h2]
  exact (Avort_integrableOn hm hc).const_mul 2

/-! ## The companion amplitude `B` (design §3) -/

/-- The companion amplitude `B(τ) = c · Bdyn m τ` of the clock: it solves `B' = -(1-m)B`, which
is exactly the `hBd` hypothesis of `meridianEq_of_dynEq` (§3) with `C.mu = m`. -/
theorem hasDerivAt_Bdyn_const_mul (m : ℝ → ℝ) (hc : Continuous m) (c τ : ℝ) :
    HasDerivAt (fun s : ℝ => c * Bdyn m s) (-(1 - m τ) * (c * Bdyn m τ)) τ := by
  have h := (Bdyn_hasDerivAt hc τ).const_mul c
  have hval : c * (-(1 - m τ) * Bdyn m τ) = -(1 - m τ) * (c * Bdyn m τ) := by ring
  rwa [hval] at h

/-- The same, with the modulation read off the clock produced by `physClockOf`: this is the form
in which `meridianEq_of_dynEq` consumes `hAdh`/`hBdh`. -/
theorem hasDerivAt_Bdyn_of_clock (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) (c τ : ℝ) :
    HasDerivAt (fun s : ℝ => c * Bdyn m s)
      (-(1 - (physClockOf m hc hm).mu τ) * (c * Bdyn m τ)) τ := by
  simpa only [physClockOf_mu] using hasDerivAt_Bdyn_const_mul m hc c τ

/-- The companion version of `Avort_hasDerivAt`, scaled by `2` so that it matches the clock's
amplitude `C.A = 2 Avort`: `(C.A)' = -(1 + C.mu) C.A`. -/
theorem hasDerivAt_clock_A (m : ℝ → ℝ) (hc : Continuous m) (hm : MuBound m) (τ : ℝ) :
    HasDerivAt (physClockOf m hc hm).A
      (-(1 + (physClockOf m hc hm).mu τ) * (physClockOf m hc hm).A τ) τ :=
  physClockOf_hasDerivAt m hc hm τ

/-! ## The main theorem: the clock of the dynamic modulation `muDyn` -/

/-- **`physClock_of_dyn` (design §2, item 8).**  If the modulation constant `muDyn α Φ g` of the
dynamic rescaling is bounded by `1/2` on the fake-time half-line and continuous there, then it is
the modulation of a clock: a `PhysClock` whose modulation is the `max`-extension
`m = fun s ↦ muDyn α Φ g (max s 0)` of `muDyn` and whose amplitude is
`C.A τ = 2 e^{-∫₀^τ (1 + m s) ds}`.

The extension is what makes `C.A` differentiable at `τ = 0` two-sidedly; on `[0,∞)` it agrees
with `muDyn`, so the clock realises exactly the modulation of the fake-time equation. -/
theorem physClock_of_dyn {αG : ℝ} {Φ g : Fam}
    (hμ : ∀ τ : ℝ, 0 ≤ τ → |muDyn αG Φ g τ| ≤ 1 / 2)
    (hc : ContinuousOn (muDyn αG Φ g) (Set.Ici 0)) :
    ∃ C : PhysClock, C.mu = (fun s : ℝ => muDyn αG Φ g (max s 0)) ∧
      ∀ τ : ℝ,
        C.A τ = 2 * Real.exp (-∫ s in (0 : ℝ)..τ, (1 + muDyn αG Φ g (max s 0))) :=
  ⟨physClockOf (fun s : ℝ => muDyn αG Φ g (max s 0)) (continuous_maxExt hc)
      (maxExt_bound hμ),
    rfl, fun _ => rfl⟩

/-- The same statement with the modulation bound and the continuity hypothesis combined into the
`MuBound`/`ContinuousOn` pair used by the interface (`maxExt_bound`/`continuous_maxExt` are the
two bridges). -/
theorem physClock_of_dyn' {αG : ℝ} {Φ g : Fam}
    (hμ : ∀ τ : ℝ, 0 ≤ τ → |muDyn αG Φ g τ| ≤ 1 / 2)
    (hc : ContinuousOn (muDyn αG Φ g) (Set.Ici 0)) :
    (physClockOf (fun s : ℝ => muDyn αG Φ g (max s 0)) (continuous_maxExt hc)
        (maxExt_bound hμ)).mu = (fun s : ℝ => muDyn αG Φ g (max s 0)) :=
  rfl

/-- The amplitude of the clock of `physClock_of_dyn` is positive. -/
theorem physClock_of_dyn_A_pos {αG : ℝ} {Φ g : Fam}
    (hμ : ∀ τ : ℝ, 0 ≤ τ → |muDyn αG Φ g τ| ≤ 1 / 2)
    (hc : ContinuousOn (muDyn αG Φ g) (Set.Ici 0)) (τ : ℝ) :
    0 < (physClockOf (fun s : ℝ => muDyn αG Φ g (max s 0)) (continuous_maxExt hc)
        (maxExt_bound hμ)).A τ :=
  physClockOf_A_pos _ _ _ τ

/-- The amplitude of the clock of `physClock_of_dyn` decays like `e^{-τ/2}`, which is what makes
the blow-up time finite (`PhysClock.integrableOn_A`) and the vorticity blow up like `1/(T-t)`. -/
theorem physClock_of_dyn_A_le_exp {αG : ℝ} {Φ g : Fam}
    (hμ : ∀ τ : ℝ, 0 ≤ τ → |muDyn αG Φ g τ| ≤ 1 / 2)
    (hc : ContinuousOn (muDyn αG Φ g) (Set.Ici 0)) {τ : ℝ} (hτ : 0 ≤ τ) :
    (physClockOf (fun s : ℝ => muDyn αG Φ g (max s 0)) (continuous_maxExt hc)
        (maxExt_bound hμ)).A τ ≤ 2 * Real.exp ((-(1 / 2 : ℝ)) * τ) :=
  physClockOf_A_le_exp _ _ _ hτ

end Work.FTS.FinalClock
