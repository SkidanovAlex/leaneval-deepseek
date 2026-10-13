import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Quadrant
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Wrapper
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.abs_PhiOdd_le
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.rhoP_sq_mul_cos_rpow_div_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The decay of the ansatz field: the bounds at the level of `merPsiT`

The analytic core of the decay estimate, specialised from `psiCore` to the meridian stream
function `merPsiT` of the reconstruction: the bounds on `∂_z ψ`, `∂_r ψ` and `ψ/r`, the
differentiability of the two slices (needed to reach the degenerate points `z = 0`, `r = 0`) and
the vanishing of `ψ` on the plane `z = 0` and on the axis `r = 0`.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Cyl

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The three bounds at the point -/

/-- The odd extension `Φ̂(·,·,τ)` inherits the first three conjuncts of `PhiRate` on the open
quadrant. -/
theorem phiOdd_rate {Φ : Work.FTS.BSIdent.Fam} {τ C₀ q lam : ℝ}
    (h0 : ∀ w, 0 < w → Φ w 0 τ = 0) (hrate : PhiRate Φ τ C₀ q lam)
    {w θ : ℝ} (hw : 0 < w) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.FTS.BSIdent.PhiOdd Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam) ∧
    |Work.Cyl.pdR (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ|
      ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam - 1) ∧
    |Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ|
      ≤ C₀ * (Real.pi / 2 - θ) ^ (q - 1) * (1 + w) ^ (-lam) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Work.FTS.BSIdent.PhiOdd_of_nonneg hθ0.le]
    exact (hrate w θ hw hθ0 hθ1).1
  · have hev : (fun w' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w' θ τ) =ᶠ[𝓝 w] fun w' => Φ w' θ τ :=
      Filter.Eventually.of_forall (fun w' => Work.FTS.BSIdent.PhiOdd_of_nonneg hθ0.le)
    rw [Work.Cyl.pdR, Filter.EventuallyEq.deriv_eq hev]
    exact (hrate w θ hw hθ0 hθ1).2.1
  · have hev : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) =ᶠ[𝓝 θ] fun θ' => Φ w θ' τ := by
      filter_upwards [isOpen_Ioi.mem_nhds hθ0] with θ' hθ'
      exact Work.FTS.BSIdent.PhiOdd_of_nonneg hθ'.le
    rw [Work.Cyl.pdZ, Filter.EventuallyEq.deriv_eq hev]
    exact (hrate w θ hw hθ0 hθ1).2.2.1

/-- **The bound on `∂_z ψ` on the open quadrant.** -/
theorem abs_pdZ_merPsiT_le_pos {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 → ContDiffAt ℝ 3
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {q lam C₀ : ℝ} (hq : 2 < q) (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 3 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : PhiRate Φ (Physical.clockInv C t) C₀ q lam) :
    ∀ r z, 0 < r → 0 < z →
      |Work.Cyl.pdZ (merPsiT α A B Φ C t) r z|
        ≤ decayKzr (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹) C₀ q lam
            (B (Physical.clockInv C t)) / (1 + Work.Cyl.rhoP r z) := by
  intro r z hr hz
  rw [merPsiT_eq_psiCore]
  have hθ0 : 0 < Work.Cyl.thetaP r z := thetaP_pos_of_pos hr hz
  have hθ1 : Work.Cyl.thetaP r z < Real.pi / 2 := thetaP_lt_pi_div_two r z
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hB
  obtain ⟨hb1, hb2, hb3⟩ := phiOdd_rate h0 hrate hw hθ0 hθ1
  refine abs_pdZ_psiCore_le hC₀.le hq hlam ?_ hB hr hz hexp
    (diffAt2_PhiOdd hsm hw hθ0 hθ1) hb1 hb2 hb3
  rw [Work.FTS.Regularity.pExp]; linarith

/-- **The bound on `∂_r ψ` on the open quadrant.** -/
theorem abs_pdR_merPsiT_le_pos {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 → ContDiffAt ℝ 3
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {q lam C₀ : ℝ} (hq : 2 < q) (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 3 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : PhiRate Φ (Physical.clockInv C t) C₀ q lam) :
    ∀ r z, 0 < r → 0 < z →
      |Work.Cyl.pdR (merPsiT α A B Φ C t) r z|
        ≤ decayKzr (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹) C₀ q lam
            (B (Physical.clockInv C t)) / (1 + Work.Cyl.rhoP r z) := by
  intro r z hr hz
  rw [merPsiT_eq_psiCore]
  have hθ0 : 0 < Work.Cyl.thetaP r z := thetaP_pos_of_pos hr hz
  have hθ1 : Work.Cyl.thetaP r z < Real.pi / 2 := thetaP_lt_pi_div_two r z
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hB
  obtain ⟨hb1, hb2, hb3⟩ := phiOdd_rate h0 hrate hw hθ0 hθ1
  refine abs_pdR_psiCore_le hC₀.le hq hlam ?_ hB hr hz hexp
    (diffAt2_PhiOdd hsm hw hθ0 hθ1) hb1 hb2 hb3
  rw [Work.FTS.Regularity.pExp]; linarith

/-! ## Differentiability of the two slices on the open quadrant -/

theorem differentiableAt_merPsiT_snd {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 → ContDiffAt ℝ 3
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hB : 0 < B (Physical.clockInv C t)) {r z : ℝ} (hr : 0 < r) (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => merPsiT α A B Φ C t r z') z := by
  rw [merPsiT_eq_psiCore]
  simp only [psiCore]
  have hθ0 : 0 < Work.Cyl.thetaP r z := thetaP_pos_of_pos hr hz
  have hθ1 : Work.Cyl.thetaP r z < Real.pi / 2 := thetaP_lt_pi_div_two r z
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hB
  have hG := diffAt2_PhiOdd hsm hw hθ0 hθ1
  have hρ2 : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) (2 * z) z := by
    have hfun : (fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) = fun z' : ℝ => z' ^ 2 + r ^ 2 := by
      funext z'; rw [Work.Cyl.rhoP_sq]; ring
    rw [hfun]
    have h : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    simpa using h.add_const (r ^ 2)
  have h2 : HasDerivAt
      (fun z' : ℝ => (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z' ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z')) _ z :=
    Work.Cyl.hasDerivAt_comp_two _ _ _ _ _ z hG
      (Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r _ z _ hr) (Work.Cyl.hasDerivAt_thetaP_snd r z hr)
  exact ((hρ2.mul_const _).mul h2).differentiableAt

theorem differentiableAt_merPsiT_fst {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 → ContDiffAt ℝ 3
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hB : 0 < B (Physical.clockInv C t)) {r z : ℝ} (hr : 0 < r) (hz : 0 < z) :
    DifferentiableAt ℝ (fun r' => merPsiT α A B Φ C t r' z) r := by
  rw [merPsiT_eq_psiCore]
  simp only [psiCore]
  have hθ0 : 0 < Work.Cyl.thetaP r z := thetaP_pos_of_pos hr hz
  have hθ1 : Work.Cyl.thetaP r z < Real.pi / 2 := thetaP_lt_pi_div_two r z
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hB
  have hG := diffAt2_PhiOdd hsm hw hθ0 hθ1
  have hρ2 : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ 2) (2 * r) r := by
    have hfun : (fun r' : ℝ => Work.Cyl.rhoP r' z ^ 2) = fun r' : ℝ => r' ^ 2 + z ^ 2 := by
      funext r'; rw [Work.Cyl.rhoP_sq]
    rw [hfun]
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.add_const (z ^ 2)
  have h2 : HasDerivAt
      (fun r' : ℝ => (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ (Physical.clockInv C t))
        (Work.Cyl.rhoP r' z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r' z)) _ r :=
    Work.Cyl.hasDerivAt_comp_two _ _ _ _ _ r hG
      (DecayAux.hasDerivAt_rhoP_rpow_div_fst r _ z _ hr) (DecayAux.hasDerivAt_thetaP_fst r z hr)
  exact ((hρ2.mul_const _).mul h2).differentiableAt

/-! ## The bound on `ψ/r` -/

/-- **The bound on `ψ/r`** (all `z`, `r > 0`). -/
theorem abs_div_merPsiT_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {q lam C₀ : ℝ} (hq : 2 < q) (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 3 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : PhiRate Φ (Physical.clockInv C t) C₀ q lam) :
    ∀ r z, 0 < r →
      |merPsiT α A B Φ C t r z / r|
        ≤ decayKq ((A (Physical.clockInv C t))⁻¹) C₀ q lam (B (Physical.clockInv C t))
            / (1 + Work.Cyl.rhoP r z) := by
  intro r z hr
  rw [merPsiT_eq_psiCore]
  simp only [psiCore]
  set ρ := Work.Cyl.rhoP r z with hρ
  set θ := Work.Cyl.thetaP r z with hθ
  set w := ρ ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) with hw
  set R := (1 + w) ^ (-lam) with hR
  have hρpos : 0 < ρ := by rw [hρ]; exact Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ ρ := hρpos.le
  have hwpos : 0 < w := by
    rw [hw]; exact div_pos (Real.rpow_pos_of_pos hρpos _) hB
  have hRnn : 0 ≤ R := by rw [hR]; exact (Real.rpow_pos_of_pos (by linarith) _).le
  have hcos : Real.cos θ = r / ρ := by
    rw [hθ, hρ]; exact Work.Cyl.cos_thetaP hr z
  have hθabs : |θ| < Real.pi / 2 := by rw [hθ]; exact abs_thetaP_lt r z
  have hG : |Work.FTS.BSIdent.PhiOdd Φ w θ (Physical.clockInv C t)|
      ≤ C₀ * (Real.pi / 2) ^ q * (Real.cos θ) ^ q * R := by
    have h := abs_PhiOdd_le_cos hC₀.le (by linarith) h0
      (fun w' θ' hw' hθ' hθ'' => (hrate w' θ' hw' hθ' hθ'').1) hwpos hθabs
    simpa [hR] using h
  have hrc : r ≤ ρ := by rw [hρ]; exact le_rhoP r z hr.le
  have hkey : ρ ^ 2 * (Real.cos θ) ^ q / r ≤ ρ := by
    rw [hcos]
    exact DecayAux.rhoP_sq_mul_cos_rpow_div_le (by linarith) hr hrc
  have hρR : ρ * R ≤ 2 * max 1 ((B (Physical.clockInv C t)) ^ lam) / (1 + ρ) := by
    have hp : (0 : ℝ) < Work.FTS.Regularity.pExp α := by
      rw [Work.FTS.Regularity.pExp]; linarith
    have h := DecayAux.rho_mul_rpow_weight_le (p := Work.FTS.Regularity.pExp α) (lam := lam)
      (b := B (Physical.clockInv C t)) (ρ := ρ) hp hlam hB hρnn hexp
    rw [← hw, ← hR] at h
    exact h
  have hbase : |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q
      * (ρ ^ 2 * (Real.cos θ) ^ q / r) * R
      ≤ |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q * ρ * R := by
    have h1 : (0 : ℝ) ≤ |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q :=
      mul_nonneg (mul_nonneg (abs_nonneg _) hC₀.le) (Real.rpow_nonneg (by linarith [Real.pi_pos]) _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey h1) hRnn
  have htoKq : |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q
      * (2 * max 1 ((B (Physical.clockInv C t)) ^ lam) / (1 + ρ))
      = decayKq ((A (Physical.clockInv C t))⁻¹) C₀ q lam (B (Physical.clockInv C t)) / (1 + ρ) := by
    rw [decayKq]; ring
  have hlast : |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q * ρ * R
      ≤ |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q
        * (2 * max 1 ((B (Physical.clockInv C t)) ^ lam) / (1 + ρ)) := by
    have h1 : (0 : ℝ) ≤ |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q :=
      mul_nonneg (mul_nonneg (abs_nonneg _) hC₀.le) (Real.rpow_nonneg (by linarith [Real.pi_pos]) _)
    calc |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q * ρ * R
        = (|(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q) * (ρ * R) := by ring
      _ ≤ (|(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q)
            * (2 * max 1 ((B (Physical.clockInv C t)) ^ lam) / (1 + ρ)) :=
          mul_le_mul_of_nonneg_left hρR h1
      _ = |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q
            * (2 * max 1 ((B (Physical.clockInv C t)) ^ lam) / (1 + ρ)) := by ring
  calc |ρ ^ 2 * (A (Physical.clockInv C t))⁻¹
          * Work.FTS.BSIdent.PhiOdd Φ w θ (Physical.clockInv C t) / r|
      = ρ ^ 2 * |(A (Physical.clockInv C t))⁻¹|
          * |Work.FTS.BSIdent.PhiOdd Φ w θ (Physical.clockInv C t)| / r := by
        rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ρ), abs_of_nonneg hr.le]
    _ ≤ ρ ^ 2 * |(A (Physical.clockInv C t))⁻¹|
          * (C₀ * (Real.pi / 2) ^ q * (Real.cos θ) ^ q * R) / r := by
        have h1 : (0 : ℝ) ≤ ρ ^ 2 * |(A (Physical.clockInv C t))⁻¹| :=
          mul_nonneg (sq_nonneg ρ) (abs_nonneg _)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG h1) hr.le
    _ = |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q
          * (ρ ^ 2 * (Real.cos θ) ^ q / r) * R := by ring
    _ ≤ |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q * ρ * R := hbase
    _ ≤ |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) ^ q
          * (2 * max 1 ((B (Physical.clockInv C t)) ^ lam) / (1 + ρ)) := hlast
    _ = decayKq ((A (Physical.clockInv C t))⁻¹) C₀ q lam (B (Physical.clockInv C t))
          / (1 + ρ) := htoKq

/-! ## Vanishing on the plane `z = 0` and on the axis `r = 0` -/

/-- `ψ(r, 0) = 0`: on the plane `θ = 0` the profile vanishes by hypothesis. -/
theorem merPsiT_zero_snd {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0) (r : ℝ) :
    merPsiT α A B Φ C t r 0 = 0 := by
  rw [merPsiT_eq_psiCore]
  simp only [psiCore, Work.Cyl.thetaP, zero_div, div_zero, Real.arctan_zero]
  by_cases hr : r = 0
  · subst hr
    have hρ0 : Work.Cyl.rhoP 0 0 = 0 := by rw [Work.Cyl.rhoP]; norm_num
    rw [hρ0]; ring
  · have hρ : 0 < Work.Cyl.rhoP r 0 := by
      rw [Work.Cyl.rhoP]
      exact Real.sqrt_pos.mpr (by linarith [sq_pos_of_ne_zero hr, sq_nonneg (0 : ℝ)])
    have hw : 0 < Work.Cyl.rhoP r 0 ^ Work.FTS.Regularity.pExp α
        / B (Physical.clockInv C t) :=
      div_pos (Real.rpow_pos_of_pos hρ _) hB
    rw [Work.FTS.BSIdent.PhiOdd_of_nonneg le_rfl, h0 _ hw]; ring

/-- `ψ(0, z) = 0`: on the axis the factor `ρ²` vanishes. -/
theorem merPsiT_zero_fst {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0) (z : ℝ) :
    merPsiT α A B Φ C t 0 z = 0 := by
  rw [merPsiT_eq_psiCore]
  simp only [psiCore, Work.Cyl.thetaP, zero_div, div_zero, Real.arctan_zero]
  by_cases hz : z = 0
  · subst hz
    have hρ0 : Work.Cyl.rhoP 0 0 = 0 := by rw [Work.Cyl.rhoP]; norm_num
    rw [hρ0]; ring
  · have hρ : 0 < Work.Cyl.rhoP 0 z := by
      rw [Work.Cyl.rhoP]
      exact Real.sqrt_pos.mpr (by linarith [sq_pos_of_ne_zero hz, sq_nonneg (0 : ℝ)])
    have hw : 0 < Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α
        / B (Physical.clockInv C t) :=
      div_pos (Real.rpow_pos_of_pos hρ _) hB
    rw [Work.FTS.BSIdent.PhiOdd_of_nonneg le_rfl, h0 _ hw]; ring

end Work.FTS.BSIdent.Cyl
