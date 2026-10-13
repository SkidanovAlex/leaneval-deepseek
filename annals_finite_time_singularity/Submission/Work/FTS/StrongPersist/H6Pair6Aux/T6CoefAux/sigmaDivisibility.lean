import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# σ-divisibility: the identity `leafGam α · D_θ = w²·sin(2θ)^{1-γ}·∂_θ`

`D_θ = sin(2θ)·∂_θ` and `leafGam α = w²·sin(2θ)^{-γ}` with `γ = 1 + α/10`, so the `sin(2θ)`
carried by the operator **cancels one power** of the `γ`-weight: for `σ = sin 2θ > 0`

  `leafGam α · D_θ A · Y · D_θ Y = w² · σ^{2-γ} · ∂_θA · Y · ∂_θY`,

and on `[0,π/2]` the new weight `σ^{2-γ} = σ^{1-α/10}` is **bounded** by `1`, whereas
`σ^{-γ}` is not even integrable near `θ = 0, π/2`.

This module records the identity and the three `L²`-bounds it buys at the *bounded* weight
`σ^{2-γ}`, for the three factors of the `b = 5` pairing
`leafGam α · D_θA · D_z^5 f · D_θ(D_z^5 f)`:

* `canon_A_slot` — the A-factor `∂_θA` (equivalently the `(0,1)`-slot of `A`, level 4);
* `canon_Z_slot` — the `θ`-derivative `∂_θ(D_z^b f)` (equivalently the `(b,1)`-slot, `b ≤ 5`);
* `canon_mid_slot` — the pure-`z` factor `D_z^b f` (`b ≤ 5`) with the **critical** weight
  `σ^{-(1-α/10)}` dominating `σ^{2-γ}` (`qDzLe` / `thetaHardyApp`).

Together with `pairing_Dth_eq_canon` this reduces the `b = 5` case to the trilinear form
`∫∫ w²σ^{2-γ} ∂_θA · D_z^5f · ∂_θ(D_z^5f)` with all three factors `L²` at the same *bounded*
weight — the form on which the alignment-penalty argument of the next layer has to work.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

/-- `Wt α z θ = w z · sin(2θ)^{-γ/2}`, so its square is the γ-weight `w²σ^{-γ}`. -/
theorem Wt_sq_eq_Iθ {α z θ : ℝ} {hσ : 0 < Real.sin (2 * θ)} :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul (le_of_lt hσ)]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-! ## § 1. The pointwise σ-divisibility identities -/

/-- **The σ-divisibility identity (two factors).**  For `σ = sin 2θ > 0`,
`leafGam α · D_θ A = w²·σ^{1-γ}·∂_θA`. -/
theorem leafGam_mul_Dth_eq {α z θ : ℝ} (hσ : 0 < Real.sin (2 * θ)) (A : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.leafGam α z θ * Work.Spaces.Dth A z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
        * Work.Spaces.pth A z θ := by
  set s := Real.sin (2 * θ) with hs
  have h1 : s ^ (-(Work.Spaces.gam α)) * s = s ^ (1 - Work.Spaces.gam α) := by
    have h := Real.rpow_add hσ (-(Work.Spaces.gam α)) (1 : ℝ)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hfun : Work.Spaces.Dth A z θ = s * Work.Spaces.pth A z θ := rfl
  have hlf : Work.FTS.TransportS.leafGam α z θ
      = (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.gam α)) := rfl
  rw [hfun, hlf, hs]
  calc (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        * (Real.sin (2 * θ) * Work.Spaces.pth A z θ)
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
          * Real.sin (2 * θ)) * Work.Spaces.pth A z θ := by ring
    _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
          * Work.Spaces.pth A z θ := by rw [h1]

/-- **The σ-divisibility identity (four factors).**  For `σ = sin 2θ > 0`,
`leafGam α · D_θ A · Y · D_θ Y = w²·σ^{2-γ}·∂_θA · Y · ∂_θY`, the weight `σ^{2-γ}` being
bounded by `1` on the angular interval. -/
theorem leafGam_four_eq {α z θ : ℝ} (hσ : 0 < Real.sin (2 * θ)) (A Y : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.leafGam α z θ * Work.Spaces.Dth A z θ * Y z θ * Work.Spaces.Dth Y z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * Work.Spaces.pth A z θ * Y z θ * Work.Spaces.pth Y z θ := by
  have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sin (2 * θ)
      = (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) := by
    have h := Real.rpow_add hσ (-(Work.Spaces.gam α)) (1 : ℝ)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have h2 : (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * Real.sin (2 * θ)
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    have h := Real.rpow_add hσ (1 - Work.Spaces.gam α) (1 : ℝ)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hfun : Work.Spaces.Dth A z θ = Real.sin (2 * θ) * Work.Spaces.pth A z θ := rfl
  have hfunY : Work.Spaces.Dth Y z θ = Real.sin (2 * θ) * Work.Spaces.pth Y z θ := rfl
  have hlf : Work.FTS.TransportS.leafGam α z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl
  rw [hfun, hfunY, hlf]
  calc (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        * (Real.sin (2 * θ) * Work.Spaces.pth A z θ) * Y z θ
        * (Real.sin (2 * θ) * Work.Spaces.pth Y z θ)
      = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
          * Real.sin (2 * θ)) * Real.sin (2 * θ)) * Work.Spaces.pth A z θ * Y z θ
        * Work.Spaces.pth Y z θ := by ring
    _ = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
          * Real.sin (2 * θ)) * Work.Spaces.pth A z θ * Y z θ
        * Work.Spaces.pth Y z θ := by rw [h1]
    _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * Work.Spaces.pth A z θ * Y z θ * Work.Spaces.pth Y z θ := by rw [h2]

/-- `leafGam α` is a.e. nonnegative for the product measure. -/
theorem leafGam_nonneg_ae (α : ℝ) :
    ∀ᵐ p ∂pm, 0 ≤ Work.FTS.TransportS.leafGam α p.1 p.2 := by
  refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
  exact Work.FTS.TransportS.leafGam_nonneg α
    (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])))

/-- The a.e. form of the four-factor identity on the product measure. -/
theorem pairing_Dth_eq_canon (α : ℝ) (A Y : ℝ → ℝ → ℝ) :
    (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.Dth A p.1 p.2
        * Y p.1 p.2 * Work.Spaces.Dth Y p.1 p.2)
      =ᵐ[pm] (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * Work.Spaces.pth A p.1 p.2 * Y p.1 p.2 * Work.Spaces.pth Y p.1 p.2) := by
  refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
  exact leafGam_four_eq (Real.sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith [Real.pi_pos])) A Y

/-! ## § 2. The bounded weight `σ^{2-γ}` -/

theorem canonW_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
  Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _

theorem canonW_le_one {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hα : α ≤ 1) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ 1 := by
  refine Real.rpow_le_one (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) (Real.sin_le_one _) ?_
  rw [Work.Spaces.gam]
  linarith

/-- On the **open** interval `σ^{2-γ} ≤ σ^{-(1-α/10)}`: the bounded weight is dominated by the
critical weight (which is what `qDzLe` prices). -/
theorem canonW_le_crit {α θ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ (Real.sin (2 * θ)) ^ (-(1 - α / 10)) := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  refine Real.rpow_le_rpow_of_exponent_ge hσ hσ1 ?_
  rw [Work.Spaces.gam]
  linarith

/-! ## § 3. The three `L²`-bounds at the bounded weight -/

/-- **The `A`-factor.**  `∫∫ w²σ^{2-γ}(∂_θA)² ≤ |A|²_{ℋ⁴} ≤ K4²` — the `(0,1)`-slot of `A`. -/
theorem canon_A_slot {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {A : ℝ → ℝ → ℝ}
    (hAsm : Work.FTS.EllipticEst.SmoothOpen A) (hA4 : Work.Spaces.HkMem α 4 A) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth A p.1 p.2) ^ 2) pm ∧
      (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth A p.1 p.2) ^ 2 ∂pm) ≤ Work.Spaces.HkSq α 4 A := by
  have hslot := mixed_slot_le (α := α) 4 hAsm hA4 (i := 1) (j := 0) le_rfl (by norm_num)
  have hae : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth A p.1 p.2) ^ 2)
      =ᵐ[pm] (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 0 1 A p.1 p.2) ^ 2) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hAC : Work.Spaces.mixed 0 1 A z θ
        = Real.sin (2 * θ) * Work.Spaces.pth A z θ := by
      have h := Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth hAsm 0 hz ⟨hθ0, hθ1⟩
      simpa only [Work.Spaces.DzIter_zero] using h
    have hkey := Work.Spaces.bt_mixed_weight_gen α z θ hα hα1 hθI
      (Work.Spaces.pth A z θ) (Work.Spaces.mixed 0 1 A z θ) hAC
    have hσpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hWt := Wt_sq_eq_Iθ (α := α) (z := z) (θ := θ) (hσ := hσpos)
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth A z θ) ^ 2
        = (Work.Spaces.pth A z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by ring
      _ = (Work.Spaces.mixed 0 1 A z θ * Work.Spaces.Wt α z θ) ^ 2 := hkey
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 0 1 A z θ) ^ 2 := by
          rw [mul_pow, hWt]; ring
  refine ⟨hslot.1.congr hae.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hae]
  exact hslot.2

/-- **The `Z`-factor.**  `∫∫ w²σ^{2-γ}(∂_θ(D_z^bf))² ≤ |f|²_{ℋ⁶}` for `b ≤ 5` — the
`(b,1)`-slot of `f`. -/
theorem canon_Z_slot {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hfsm : Work.FTS.EllipticEst.SmoothOpen f) (hf6 : Work.Spaces.HkMem α 6 f) (hb : b ≤ 5) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter b f) p.1 p.2) ^ 2) pm ∧
      (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth (Work.Spaces.DzIter b f) p.1 p.2) ^ 2 ∂pm)
        ≤ Work.Spaces.HkSq α 6 f := by
  have hslot := mixed_slot_le (α := α) 6 hfsm hf6 (i := 1) (j := b) le_rfl (by omega)
  have hae : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter b f) p.1 p.2) ^ 2)
      =ᵐ[pm] (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b 1 f p.1 p.2) ^ 2) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hkey := Work.FTS.TransportS.SlotT2.supOpen_pth_weight hfsm hα hα1 b hz ⟨hθ0, hθ1⟩
    have hσpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hWt := Wt_sq_eq_Iθ (α := α) (z := z) (θ := θ) (hσ := hσpos)
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        = (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by ring
      _ = (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := hkey
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b 1 f z θ) ^ 2 := by
          rw [mul_pow, hWt]; ring
  refine ⟨hslot.1.congr hae.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hae]
  exact hslot.2

/-- **The middle factor.**  `∫∫ w²σ^{2-γ}(D_z^bf)² ≤ Cα^{-2}(1+|f|²_{ℋ⁶})` for `b ≤ 5`: the
bounded weight `σ^{2-γ}` is dominated by the critical weight `σ^{-(1-α/10)}`, which is exactly
what `thetaHardyApp`/`qDzLe` prices for pure `D_z`-slots up to order `5`. -/
theorem canon_mid_slot : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (f : ℝ → ℝ → ℝ) (b : ℕ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → b ≤ 5 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.DzIter b f p.1 p.2) ^ 2) pm ∧
        (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.DzIter b f p.1 p.2) ^ 2 ∂pm)
          ≤ C * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
  refine ⟨Cd, hCdpos, ?_⟩
  intro α hα f b hfsm hf6 hb
  have hcrit := hCd α hα f b hfsm hf6 hb
  obtain ⟨hα0, hα1⟩ := hα
  have hle : ∀ᵐ p ∂pm, (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.DzIter b f p.1 p.2) ^ 2
      ≤ (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(1 - α / 10))
        * (Work.Spaces.DzIter b f p.1 p.2) ^ 2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hsq : 0 ≤ (Work.Spaces.DzIter b f z θ) ^ 2 := sq_nonneg _
    have h2 := canonW_le_crit hα0 hα1 ⟨hθ0, hθ1⟩
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.DzIter b f z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.DzIter b f z θ) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(1 - α / 10))
            * (Work.Spaces.DzIter b f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hsq) hw
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
            * (Work.Spaces.DzIter b f z θ) ^ 2 := by ring
  have hnn : ∀ᵐ p ∂pm, 0 ≤ (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.DzIter b f p.1 p.2) ^ 2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (canonW_nonneg ⟨le_of_lt hθ0, le_of_lt hθ1⟩)) (sq_nonneg _)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.DzIter b f p.1 p.2) ^ 2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 := contOn_w
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
        Work.FTS.EllipticEst.Q0 := by
      have hs : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
          Work.FTS.EllipticEst.Q0 := by fun_prop
      refine hs.rpow_const (fun p hp => Or.inl (ne_of_gt ?_))
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])
    exact (h1.mul h2).mul ((hfsm.DzIter b).continuousOn.pow 2)
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)
      * (Work.Spaces.DzIter b f p.1 p.2) ^ 2) pm := by
    refine hcrit.1.mono' haesm ?_
    filter_upwards [hle, hnn] with p hp hn
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hp
  exact ⟨hint, le_trans (MeasureTheory.integral_mono_ae hint hcrit.1 hle) hcrit.2⟩

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
