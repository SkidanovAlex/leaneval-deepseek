import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceL1Ae
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sup_mixed_le_H4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


/-! ## The three factors of row 15 -/

/-- The angular factor `A15 α = 2·C15 α` of row 15: `A15 α θ = -4(α/c(α))·D_θΓ(θ)`. -/
def A15 (α : ℝ) : ℝ → ℝ := fun θ => 2 * Work.FTS.NonlinRows.C15 α θ

/-- `A·G`, the `(z,θ)`-product of the angular factor and the weighted star coefficient. -/
def AG15 (α : ℝ) (Φs : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => A15 α θ * Work.FTS.NonlinRows.G15 α Φs z θ

/-- The open-quadrant representative `ψ·A·G` of `N₂^{**} = -2U(Φ̃_*)∂_θF_*`. -/
def N2ssO (α : ℝ) (Φs : Fn) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.NonlinRows.psi15 z * AG15 α Φs z θ

/-! ## The identity on the open quadrant -/

/-- `N₂^{**} = ψ·(A·G)` on the open quadrant (the weighted identity of `NRow15T2Aux.Defs`
divided by its fibre `(z+1)³/z²`). -/
theorem N2ss_open_eq {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hv : Work.Spaces.VanishTheta (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N2ss α Φs z θ = N2ssO α Φs z θ := by
  intro z hz θ hθ0 hθ1
  have hw := Work.FTS.NonlinRows.N2ss_weighted_eq hα hα1 hv z (le_of_lt hz) θ
    ⟨hθ0.le, hθ1.le⟩
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  have hz3 : (1 + z) ^ 3 ≠ 0 := pow_ne_zero 3 hz1
  rw [N2ssO, AG15, A15, Work.FTS.NonlinRows.psi15_eq, ← hw]
  field_simp
  ring

/-- The same identity as a `Set.EqOn` statement on the open quadrant `Q0`. -/
theorem N2ss_eqOn_Q0 {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hv : Work.Spaces.VanishTheta (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) :
    Set.EqOn (Function.uncurry (Work.FTS.Nonlin.N2ss α Φs))
      (Function.uncurry (N2ssO α Φs)) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact N2ss_open_eq hα hα1 hv p.1 hz p.2 hθ0 hθ1

/-! ## Smoothness -/

theorem smoothOpen_A15 (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => A15 α θ) := by
  have h := Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (2 : ℝ)
    (Work.FTS.NonlinRows.smoothOpen_C15_bsl α)
  simpa only [A15] using h

theorem smoothOpen_AG15 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (AG15 α Φs) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl (smoothOpen_A15 α)
    (Work.FTS.NonlinRows.smoothOpen_G15 hα hα1 hs)

theorem smoothOpen_N2ssO {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (N2ssO α Φs) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
    (Work.FTS.NonlinRows.smoothOpen_psi15) (smoothOpen_AG15 hα hα1 hs)

/-! ## Functorial evaluations on one-variable functions -/

theorem pzIter_thetaFn (A : ℝ → ℝ) (d : ℕ) :
    Work.Spaces.pzIter d (fun _ (θ : ℝ) => A θ) = fun _ θ => if d = 0 then A θ else 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      show deriv (fun z' : ℝ => (if d = 0 then A θ else (0 : ℝ))) z
        = (if d + 1 = 0 then A θ else 0)
      rw [show (fun z' : ℝ => (if d = 0 then A θ else (0 : ℝ)))
            = fun _ : ℝ => (if d = 0 then A θ else 0) from rfl, deriv_const]
      simp

theorem pzIter_DthIter_thetaFn (A : ℝ → ℝ) (e d : ℕ) :
    Work.Spaces.pzIter d (Work.Spaces.DthIter e (fun _ (θ : ℝ) => A θ))
      = fun _ θ => if d = 0 then Work.Spaces.dthU^[e] A θ else 0 := by
  rw [Work.FTS.NonlinRows.DthIter_theta_only, pzIter_thetaFn]

theorem pzIter_DthIter_thetaFn_apply (A : ℝ → ℝ) (e d : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter d (Work.Spaces.DthIter e (fun _ (θ' : ℝ) => A θ')) z θ
      = if d = 0 then Work.Spaces.dthU^[e] A θ else 0 := by
  rw [pzIter_DthIter_thetaFn]

theorem dthIter_zFn (r : ℝ → ℝ) (a : ℕ) (ha : 1 ≤ a) :
    Work.Spaces.DthIter a (fun z _ => r z) = fun _ _ => (0 : ℝ) := by
  have h1 : Work.Spaces.Dth (fun z _ => r z) = fun _ _ => (0 : ℝ) := by
    funext z θ
    simp [Work.Spaces.Dth, Work.Spaces.pth]
  have key : ∀ b : ℕ, Work.Spaces.DthIter (b + 1) (fun z _ => r z)
      = fun _ _ => (0 : ℝ) := by
    intro b
    induction b with
    | zero => simpa using h1
    | succ b ih =>
        rw [show b + 1 + 1 = (b + 1) + 1 from by ring, Work.Spaces.DthIter_succ, ih]
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  exact key b

theorem pzIter_dthIter_zFn (r : ℝ → ℝ) (a c : ℕ) (ha : 1 ≤ a) :
    Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z _ => r z)) = fun _ _ => (0 : ℝ) := by
  rw [dthIter_zFn r a ha]
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.pz]


theorem sum_range_range_const (n m : ℕ) (C : ℝ) :
    (∑ _c ∈ Finset.range (n + 1), ∑ _a ∈ Finset.range (m + 1), C)
      = (((n + 1 : ℕ)) : ℝ) * (((m + 1 : ℕ)) : ℝ) * C := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-! ## The angular jet bounds of `A15 = 2·C15` -/

/-- `|D_θ^a (A15 α)(θ)| ≤ K·α²` for `a ≤ 4`, `0 < α ≤ 1`, `θ ∈ Iθ`. -/
theorem dthU_iter_A15_flat_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[a] (A15 α) θ| ≤ K * α ^ 2 := by
  obtain ⟨K, hKpos, hKb⟩ := Work.FTS.NonlinRows.dthU_iter_C15_le
  refine ⟨2 * K, by positivity, ?_⟩
  intro α hα hα1 a ha θ hθ
  have h := hKb α hα hα1 a ha θ hθ
  have hGam : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hfun : A15 α = fun θ => 2 * Work.FTS.NonlinRows.C15 α θ := rfl
  rw [hfun, Work.Spaces.dthU_iter_const_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hKa2 : 0 ≤ K * α ^ 2 := mul_nonneg hKpos.le (sq_nonneg α)
  calc 2 * |Work.Spaces.dthU^[a] (Work.FTS.NonlinRows.C15 α) θ|
      ≤ 2 * (K * α ^ 2 * Work.Spaces.Gam α θ) := by linarith [h]
    _ ≤ 2 * K * α ^ 2 := by nlinarith [hGam, hGam0, hKa2]
    _ = 2 * K * α ^ 2 := by ring

/-- `α·Γ(θ) ≤ (α + sin 2θ)·sin(2θ)^{α/5}` on `Iθ` (`Gam_mul_weight_le`, multiplied out). -/
theorem alpha_Gam_le_weight {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    α * Work.Spaces.Gam α θ
      ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rcases eq_or_lt_of_le hs with h | h
  · have hsc : Real.sin θ * Real.cos θ = 0 := by
      have h2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
      rw [h2] at h
      linarith
    have hGam : Work.Spaces.Gam α θ = 0 := by
      rw [Work.Spaces.Gam]
      have hz : Real.sin θ * Real.cos θ ^ 2 = 0 := by
        rw [show Real.sin θ * Real.cos θ ^ 2 = (Real.sin θ * Real.cos θ) * Real.cos θ by ring,
          hsc, zero_mul]
      rw [hz]
      exact Real.zero_rpow (by linarith : α / 3 ≠ 0)
    rw [hGam, mul_zero, ← h, Real.zero_rpow (by linarith : α / 5 ≠ 0), mul_zero]
  · have hw := Work.Spaces.Gam_mul_weight_le α θ hα hθ
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hkey : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        ≤ α + Real.sin (2 * θ) := by
      rw [div_le_iff₀ hden] at hw
      simpa using hw
    have hinv : ((Real.sin (2 * θ)) ^ (-(α / 5)))⁻¹ = (Real.sin (2 * θ)) ^ (α / 5) := by
      rw [Real.rpow_neg h.le, inv_inv]
    have hs' : 0 < (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_pos_of_pos h _
    calc α * Work.Spaces.Gam α θ
        = α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            * ((Real.sin (2 * θ)) ^ (-(α / 5)))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos h _)), mul_one]
      _ = α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            * (Real.sin (2 * θ)) ^ (α / 5) := by rw [hinv]
      _ ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
          mul_le_mul_of_nonneg_right hkey hs'.le

/-- `|D_θ^a (A15 α)(θ)| ≤ K·α·(α+sin 2θ)sin(2θ)^{α/5}` for `a ≤ 4`, `0 < α ≤ 1`, `θ ∈ Iθ`. -/
theorem dthU_iter_A15_weight_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[a] (A15 α) θ|
          ≤ K * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  obtain ⟨K, hKpos, hKb⟩ := Work.FTS.NonlinRows.dthU_iter_C15_le
  refine ⟨2 * K, by positivity, ?_⟩
  intro α hα hα1 a ha θ hθ
  have h := hKb α hα hα1 a ha θ hθ
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hw := alpha_Gam_le_weight (α := α) (θ := θ) hα hθ
  have hfun : A15 α = fun θ => 2 * Work.FTS.NonlinRows.C15 α θ := rfl
  rw [hfun, Work.Spaces.dthU_iter_const_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * |Work.Spaces.dthU^[a] (Work.FTS.NonlinRows.C15 α) θ|
      ≤ 2 * (K * α ^ 2 * Work.Spaces.Gam α θ) := by linarith [h]
    _ = 2 * K * α * (α * Work.Spaces.Gam α θ) := by ring
    _ ≤ 2 * K * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)


end Work.FTS.Nonlinear.Open
