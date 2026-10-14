import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.FireFix.Prime.PhysVortBundle
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Physical.Meridian
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddNegPi
import Submission.Work.FTS_BSIdentP.Slim.TendstoSliceQuotient
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.DecayAux.PosQuadrant =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels.abs_pdZ_pdR_psiCore_le_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sharp (`q = 1`) pointwise decay of `∂_z ψ`, `∂_r ψ`

This is the `q = 1` counterpart of `Work.FTS.BSIdent.Cyl.abs_combination_bound`: the profile
bounds lose the *whole* rate `(π/2 - θ)` (for `∂_θG`) resp. one power of `(π/2 - θ)` (for
`∂_wG`), no `(π/2-θ)^{q-2}` slack is available, and the exponent hypothesis is only
`2 ≤ p·λ`.  The combination bound is therefore reproved from scratch (`q = 1` makes the
`(π/2 - θ)`-bookkeeping trivial: the only thing used is `π/2 - θ ≤ π/2`), and the weight
estimate `ρ (1+ρ^p/b)^{-λ} ≤ 2 max 1 (b^λ)/(1+ρ)` is the sharp one
`rho_mul_rpow_weight_le_two`.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Weyl.Levels

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise bound in the sharp regime -/

/-- The two terms `c (X ∂_wG + Y ∂_θG)` of the chain rule are bounded by
`decayKzrOne p c C₀ lam b / (1+ρ)` as soon as `|X| ≤ p ρ w`, `|Y| ≤ ρ` and the profile
satisfies the three *sharp* (`q = 1`) bounds at the point. -/
theorem abs_combination_bound_one {G : ℝ → ℝ → ℝ} {p c b C₀ lam r z zc X Y : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 2 ≤ p * lam) (hzc : |zc| ≤ Work.Cyl.rhoP r z)
    (hX : |X| ≤ p * Work.Cyl.rhoP r z * (Work.Cyl.rhoP r z ^ p / b))
    (hY : |Y| ≤ Work.Cyl.rhoP r z)
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |2 * zc * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + c * (X * Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              + Y * Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))|
      ≤ decayKzrOne p c C₀ lam b / (1 + Work.Cyl.rhoP r z) := by
  set ρ := Work.Cyl.rhoP r z with hρ
  set θ := Work.Cyl.thetaP r z with hθ
  set w := ρ ^ p / b with hw
  set S := Real.pi / 2 - θ with hS
  set R := (1 + w) ^ (-lam) with hR
  have hρpos : 0 < ρ := by rw [hρ]; exact Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ ρ := hρpos.le
  have hθlt : θ < Real.pi / 2 := by rw [hθ]; exact Work.FTS.BSIdent.Cyl.thetaP_lt_pi_div_two r z
  have hθpos : 0 < θ := by rw [hθ]; exact Work.FTS.BSIdent.Cyl.thetaP_pos_of_pos hr hz
  have hSnn : 0 ≤ S := by rw [hS]; linarith
  have hSle : S ≤ Real.pi / 2 := by rw [hS]; linarith
  have hwpos : 0 < w := by
    rw [hw]; exact div_pos (Real.rpow_pos_of_pos hρpos p) hb
  have hwnn : 0 ≤ w := hwpos.le
  have h1w : (0 : ℝ) < 1 + w := by linarith
  have hRpos : 0 < R := by rw [hR]; exact Real.rpow_pos_of_pos h1w _
  have hRnn : 0 ≤ R := hRpos.le
  have h2pi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hval' : |G w θ| ≤ C₀ * S * R := hval
  have hwd' : |Work.Cyl.pdR G w θ| ≤ C₀ * S * (1 + w) ^ (-lam - 1) := hwd
  have hth' : |Work.Cyl.pdZ G w θ| ≤ C₀ * R := hth
  have hX' : |X| ≤ p * ρ * w := hX
  have hY' : |Y| ≤ ρ := hY
  have hzcb : |zc| ≤ ρ := by rw [hρ]; exact hzc
  -- the elementary comparisons
  have hwR2 : w * (1 + w) ^ (-lam - 1) ≤ R := by
    have e1 : (1 + w) ^ (-lam - 1) = R * (1 + w)⁻¹ := by
      have e2 : (1 + w) ^ (-lam - 1) = (1 + w) ^ (-lam) * (1 + w) ^ (-1 : ℝ) := by
        rw [show -lam - 1 = -lam + (-1) by ring, Real.rpow_add h1w]
      rw [e2, ← hR, Real.rpow_neg_one]
    have hw1 : w * (1 + w)⁻¹ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (show w ≤ 1 + w by linarith)
        (inv_nonneg.mpr h1w.le)
      rwa [mul_inv_cancel₀ (ne_of_gt h1w)] at h
    calc w * (1 + w) ^ (-lam - 1) = (w * (1 + w)⁻¹) * R := by rw [e1]; ring
      _ ≤ 1 * R := mul_le_mul_of_nonneg_right hw1 hRnn
      _ = R := one_mul R
  have hρR : ρ * R ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
    have h := rho_mul_rpow_weight_le_two hp hlam hb hρnn hpl
    rw [← hw, ← hR] at h
    exact h
  -- the three term bounds
  have hT1 : 2 * |zc| * |c| * (C₀ * S * R)
      ≤ (2 * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) := by
    have hCS : C₀ * S * R ≤ C₀ * (Real.pi / 2) * R := by
      have h1 : C₀ * S ≤ C₀ * (Real.pi / 2) := mul_le_mul_of_nonneg_left hSle hC₀
      calc C₀ * S * R ≤ (C₀ * (Real.pi / 2)) * R := mul_le_mul_of_nonneg_right h1 hRnn
        _ = C₀ * (Real.pi / 2) * R := by ring
    have hz2 : 2 * |zc| ≤ 2 * ρ := by linarith [hzcb]
    have hz2c : 2 * |zc| * |c| ≤ 2 * ρ * |c| := mul_le_mul_of_nonneg_right hz2 (abs_nonneg c)
    calc 2 * |zc| * |c| * (C₀ * S * R)
        ≤ 2 * ρ * |c| * (C₀ * (Real.pi / 2) * R) :=
          mul_le_mul hz2c hCS (mul_nonneg (mul_nonneg hC₀ hSnn) hRnn)
            (mul_nonneg (mul_nonneg (by norm_num) hρnn) (abs_nonneg c))
      _ = (2 * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) := by ring
  have hT2 : |c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
      ≤ (p * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) := by
    have hCS : C₀ * S * (1 + w) ^ (-lam - 1)
        ≤ C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1) := by
      have h1 : C₀ * S ≤ C₀ * (Real.pi / 2) := mul_le_mul_of_nonneg_left hSle hC₀
      calc C₀ * S * (1 + w) ^ (-lam - 1)
          ≤ (C₀ * (Real.pi / 2)) * (1 + w) ^ (-lam - 1) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg h1w.le _)
        _ = C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1) := by ring
    have h1 : |c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
        ≤ |c| * ((p * ρ * w) * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hCS (mul_nonneg (mul_nonneg hp.le hρnn) hwnn))
        (abs_nonneg c)
    have h2 : |c| * ((p * ρ * w) * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1)))
        = (p * (Real.pi / 2))
          * (|c| * C₀ * (ρ * (w * (1 + w) ^ (-lam - 1)))) := by ring
    have h3 : (p * (Real.pi / 2))
          * (|c| * C₀ * (ρ * (w * (1 + w) ^ (-lam - 1))))
        ≤ (p * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwR2 hρnn)
          (mul_nonneg (abs_nonneg c) hC₀))
        (mul_nonneg hp.le h2pi.le)
    exact h1.trans (h2.trans_le h3)
  have hT3 : |c| * (ρ * (C₀ * R)) ≤ 1 * (|c| * C₀ * (ρ * R)) := by
    have h : |c| * (ρ * (C₀ * R)) = 1 * (|c| * C₀ * (ρ * R)) := by ring
    rw [h]
  have hsum : 2 * |zc| * |c| * (C₀ * S * R)
        + (|c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
          + |c| * (ρ * (C₀ * R)))
      ≤ (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
        * (|c| * C₀ * (ρ * R)) := by
    have h := add_le_add hT1 (add_le_add hT2 hT3)
    calc 2 * |zc| * |c| * (C₀ * S * R)
          + (|c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
            + |c| * (ρ * (C₀ * R)))
        ≤ (2 * (Real.pi / 2)) * (|c| * C₀ * (ρ * R))
          + ((p * (Real.pi / 2)) * (|c| * C₀ * (ρ * R))
            + 1 * (|c| * C₀ * (ρ * R))) := h
      _ = (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
          * (|c| * C₀ * (ρ * R)) := by ring
  have hfin : (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
        * (|c| * C₀ * (ρ * R))
      ≤ decayKzrOne p c C₀ lam b / (1 + ρ) := by
    have hA : (0 : ℝ) ≤ |c| * C₀ := mul_nonneg (abs_nonneg c) hC₀
    have hb1 : |c| * C₀ * (ρ * R) ≤ |c| * C₀ * (2 * max 1 (b ^ lam) / (1 + ρ)) :=
      mul_le_mul_of_nonneg_left hρR hA
    have hcoef : (0 : ℝ) ≤ 2 * (Real.pi / 2) + p * (Real.pi / 2) + 1 := by
      have := mul_nonneg hp.le h2pi.le; linarith [Real.pi_pos]
    calc (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
          * (|c| * C₀ * (ρ * R))
        ≤ (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
            * (|c| * C₀ * (2 * max 1 (b ^ lam) / (1 + ρ))) :=
          mul_le_mul_of_nonneg_left hb1 hcoef
      _ = decayKzrOne p c C₀ lam b / (1 + ρ) := by rw [decayKzrOne]; ring
  -- assembling
  have h1a : |2 * zc * c * G w θ| = 2 * |zc| * |c| * |G w θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h1b : |c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)|
      = |c| * |X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ| := abs_mul c _
  have h1c : |X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ|
      ≤ |X| * |Work.Cyl.pdR G w θ| + |Y| * |Work.Cyl.pdZ G w θ| :=
    (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_mul]))
  have h1 : |2 * zc * c * G w θ + c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)|
      ≤ 2 * |zc| * |c| * |G w θ|
        + (|c| * (|X| * |Work.Cyl.pdR G w θ|) + |c| * (|Y| * |Work.Cyl.pdZ G w θ|)) := by
    calc |2 * zc * c * G w θ + c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)|
        ≤ |2 * zc * c * G w θ| + |c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)| :=
          abs_add_le _ _
      _ = 2 * |zc| * |c| * |G w θ|
            + |c| * |X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ| := by rw [h1a, h1b]
      _ ≤ 2 * |zc| * |c| * |G w θ|
            + |c| * (|X| * |Work.Cyl.pdR G w θ| + |Y| * |Work.Cyl.pdZ G w θ|) := by
          have hc := mul_le_mul_of_nonneg_left h1c (abs_nonneg c)
          linarith
      _ = 2 * |zc| * |c| * |G w θ|
            + (|c| * (|X| * |Work.Cyl.pdR G w θ|)
              + |c| * (|Y| * |Work.Cyl.pdZ G w θ|)) := by rw [mul_add]
  have h2 : 2 * |zc| * |c| * |G w θ|
        + (|c| * (|X| * |Work.Cyl.pdR G w θ|) + |c| * (|Y| * |Work.Cyl.pdZ G w θ|))
      ≤ 2 * |zc| * |c| * (C₀ * S * R)
        + (|c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
          + |c| * (ρ * (C₀ * R))) := by
    have hA : 2 * |zc| * |c| * |G w θ| ≤ 2 * |zc| * |c| * (C₀ * S * R) :=
      mul_le_mul_of_nonneg_left hval'
        (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg zc)) (abs_nonneg c))
    have hB : |X| * |Work.Cyl.pdR G w θ| ≤ (p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)) :=
      mul_le_mul hX' hwd' (abs_nonneg _) (mul_nonneg (mul_nonneg hp.le hρnn) hwnn)
    have hD : |Y| * |Work.Cyl.pdZ G w θ| ≤ ρ * (C₀ * R) :=
      mul_le_mul hY' hth' (abs_nonneg _) hρnn
    exact add_le_add hA (add_le_add (mul_le_mul_of_nonneg_left hB (abs_nonneg c))
      (mul_le_mul_of_nonneg_left hD (abs_nonneg c)))
  exact h1.trans (h2.trans (hsum.trans hfin))

/-! ## The theorem -/

theorem abs_pdZ_pdR_psiCore_le_one {G : ℝ → ℝ → ℝ} {p c b C₀ lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 2 ≤ p * lam)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.psiCore p c b G) r z|
        ≤ Work.FTS.BSIdent.Weyl.Levels.decayKzrOne p c C₀ lam b / (1 + Work.Cyl.rhoP r z) ∧
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.psiCore p c b G) r z|
        ≤ Work.FTS.BSIdent.Weyl.Levels.decayKzrOne p c C₀ lam b / (1 + Work.Cyl.rhoP r z) := by
  have hρnn : 0 ≤ Work.Cyl.rhoP r z := (Work.Cyl.rhoP_pos hr z).le
  have hwp : (0 : ℝ) ≤ Work.Cyl.rhoP r z ^ p / b :=
    div_nonneg (Real.rpow_nonneg hρnn p) hb.le
  constructor
  · rw [Work.FTS.BSIdent.Cyl.pdZ_psiCore_eq hG hr]
    refine abs_combination_bound_one (zc := z)
      (X := p * z * (Work.Cyl.rhoP r z ^ p / b)) (Y := r)
      hC₀ hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
    · exact Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z
    · rw [abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hwp]
      have h2 : p * |z| ≤ p * Work.Cyl.rhoP r z :=
        mul_le_mul_of_nonneg_left (Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z) hp.le
      exact mul_le_mul_of_nonneg_right h2 hwp
    · rw [abs_of_nonneg hr.le]
      exact Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le
  · rw [Work.FTS.BSIdent.Cyl.pdR_psiCore_eq hG hr]
    refine abs_combination_bound_one (zc := r)
      (X := p * r * (Work.Cyl.rhoP r z ^ p / b)) (Y := -z)
      hC₀ hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
    · rw [abs_of_nonneg hr.le]
      exact Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le
    · rw [abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hr.le, abs_of_nonneg hwp]
      have h2 : p * r ≤ p * Work.Cyl.rhoP r z :=
        mul_le_mul_of_nonneg_left (Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le) hp.le
      exact mul_le_mul_of_nonneg_right h2 hwp
    · rw [abs_neg]
      exact Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z

end Work.FTS.BSIdent.Weyl.Levels
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PhysVortAeAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Clauses

/-! ## 1. The product rule for a scalar function times `e_θ` -/

lemma norm_fderiv_smul_eTheta_le {H : R3 → ℝ} {x : R3} (hr : 0 < Work.Cyl.radial x)
    (hH : DifferentiableAt ℝ H x) :
    ‖fderiv ℝ (fun y : R3 => H y • Work.Cyl.eTheta y) x‖
      ≤ |H x| * (2 / Work.Cyl.radial x) + ‖fderiv ℝ H x‖ := by
  have hE : DifferentiableAt ℝ Work.Cyl.eTheta x := (eTheta_deriv_bound x hr).1
  have hEb := (eTheta_deriv_bound x hr).2
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hkey : fderiv ℝ ((fun y : R3 => H y) • Work.Cyl.eTheta) x
      = H x • fderiv ℝ Work.Cyl.eTheta x + (fderiv ℝ H x).smulRight (Work.Cyl.eTheta x) :=
    fderiv_smul hH hE
  change ‖fderiv ℝ ((fun y : R3 => H y) • Work.Cyl.eTheta) x‖ ≤ _
  rw [hkey]
  calc ‖H x • fderiv ℝ Work.Cyl.eTheta x + (fderiv ℝ H x).smulRight (Work.Cyl.eTheta x)‖
      ≤ ‖H x • fderiv ℝ Work.Cyl.eTheta x‖
        + ‖(fderiv ℝ H x).smulRight (Work.Cyl.eTheta x)‖ := norm_add_le _ _
    _ = |H x| * ‖fderiv ℝ Work.Cyl.eTheta x‖ + ‖fderiv ℝ H x‖ * ‖Work.Cyl.eTheta x‖ := by
        rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
    _ = |H x| * ‖fderiv ℝ Work.Cyl.eTheta x‖ + ‖fderiv ℝ H x‖ := by
        rw [Work.Cyl.norm_eTheta x hrne, mul_one]
    _ ≤ |H x| * (2 / Work.Cyl.radial x) + ‖fderiv ℝ H x‖ := by
        have := mul_le_mul_of_nonneg_left hEb (abs_nonneg (H x))
        linarith

/-! ## 2. Recovering the two-variable differentiability of the profile -/

lemma diffAt2_of_differentiableAt_smul_eTheta {α B : ℝ} (hα : 0 < α) (hB : 0 < B)
    {Ψ : ℝ → ℝ → ℝ} {x : R3} (hr : 0 < Work.Cyl.radial x)
    (hd : DifferentiableAt ℝ (fun y : R3 =>
      Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y) • Work.Cyl.eTheta y) x) :
    Work.Cyl.DiffAt2 Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x) := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hE : DifferentiableAt ℝ Work.Cyl.eTheta x := (eTheta_deriv_bound x hr).1
  have hinner := DifferentiableAt.inner ℝ hd hE
  have hmem : {y : R3 | 0 < Work.Cyl.radial y} ∈ 𝓝 x :=
    (Work.Cyl.differentiableAt_radial x hrne).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hr)
  have hH : DifferentiableAt ℝ
      (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y)) x := by
    refine hinner.congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    have hnorm : ‖Work.Cyl.eTheta y‖ = 1 := Work.Cyl.norm_eTheta y (ne_of_gt hy)
    show Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y)
      = inner ℝ (Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y) • Work.Cyl.eTheta y)
          (Work.Cyl.eTheta y)
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
    ring
  exact diffAt2_of_comp_sect hα hB x hr hH

/-! ## 3. The profile vanishes beyond the support radius -/

lemma profile_eq_zero_of_supp {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ L : ℝ}
    (hsupp : ∀ z θ : ℝ, L ≤ z → Work.FTS.Regularity.profFull α g z θ τ = 0)
    {z θ : ℝ} (hz : L ≤ z) :
    Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ = 0 := by
  by_cases hθ : 0 ≤ θ
  · rw [profile_eq_Ppos hθ, Ppos]
    have h := hsupp z θ hz
    rw [Work.FTS.Regularity.profFull_apply] at h
    simpa [Work.FTS.Regularity.pExp] using h
  · rw [profile_eq_neg_Ppos hθ, Ppos]
    have h := hsupp z (-θ) hz
    rw [Work.FTS.Regularity.profFull_apply] at h
    have h' : Work.Construction.Fstar (3 * α) z (-θ) + g z (-θ) τ = 0 := by
      simpa [Work.FTS.Regularity.pExp] using h
    rw [h', neg_zero]

/-! ## 4. The pointwise bounds on the profile slice -/

lemma profile_abs_le_N {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : ℝ → ℝ → ℝ → ℝ} {τ N : ℝ}
    (hN : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ τ| ≤ N)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : |θ| ≤ Real.pi / 2) :
    |Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ|
      ≤ 20 * (3 * α) + N := by
  have hF := (Fstar_bounds hα hα13).1
  have hθup : θ ≤ Real.pi / 2 := by linarith [abs_le.mp hθ]
  by_cases hθ0 : 0 ≤ θ
  · have hmem : θ ∈ Work.Spaces.Iθ := ⟨hθ0, hθup⟩
    rw [profile_eq_Ppos hθ0, Ppos]
    calc |Work.Construction.Fstar (3 * α) z θ + g z θ τ|
        ≤ |Work.Construction.Fstar (3 * α) z θ| + |g z θ τ| := abs_add_le _ _
      _ ≤ 20 * (3 * α) + N := by
          have h1 := hF z θ hz hmem
          have h2 := hN z θ hz hmem
          nlinarith
  · have hmem : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith, by linarith [abs_le.mp hθ]⟩
    rw [show Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ
        = -Ppos α g τ z (-θ) from profile_eq_neg_Ppos hθ0, Ppos, abs_neg]
    calc |Work.Construction.Fstar (3 * α) z (-θ) + g z (-θ) τ|
        ≤ |Work.Construction.Fstar (3 * α) z (-θ)| + |g z (-θ) τ| := abs_add_le _ _
      _ ≤ 20 * (3 * α) + N := by
          have h1 := hF z (-θ) hz hmem
          have h2 := hN z (-θ) hz hmem
          nlinarith

lemma profile_pz_le {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {Npz : ℝ}
    {g : ℝ → ℝ → ℝ → ℝ} (hNpz : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Npz)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : |θ| ≤ Real.pi / 2) :
    |Work.Spaces.pz (fun z θ => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ) z θ| ≤ 60 * α + Npz := by
  have hθup : θ ≤ Real.pi / 2 := by linarith [abs_le.mp hθ]
  by_cases hθ0 : 0 ≤ θ
  · exact abs_pz_profile_le hα hα13 hNpz hcont hτ hz (⟨hθ0, hθup⟩ : θ ∈ Work.Spaces.Iθ)
  · have hpos : (0:ℝ) ≤ -θ := by linarith
    have hmem : -θ ∈ Work.Spaces.Iθ := ⟨hpos, by linarith [abs_le.mp hθ]⟩
    have hfun : (fun z' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z' θ)
        = fun z' => - Work.ConstructionInstance.profile (3 * α)
            (Work.FTS.Regularity.gSlice g τ) z' (-θ) := by
      funext z'
      rw [profile_eq_neg_Ppos hθ0, profile_eq_Ppos hpos]
    have hd : deriv (fun z' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z' θ) z
        = - deriv (fun z' => Work.ConstructionInstance.profile (3 * α)
            (Work.FTS.Regularity.gSlice g τ) z' (-θ)) z := by
      rw [hfun, Work.FTS.EllipticEst.deriv_neg_apply]
    show |deriv (fun z' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z' θ) z| ≤ 60 * α + Npz
    rw [hd, abs_neg]
    exact abs_pz_profile_le hα hα13 hNpz hcont hτ hz hmem

lemma profile_pth_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ}
    (hz : 0 ≤ z) (hθ1 : 0 < |θ|) (hθ2 : |θ| < Real.pi / 2)
    (hd : DifferentiableAt ℝ (fun θ' => Work.ConstructionInstance.profile (3 * α)
      (Work.FTS.Regularity.gSlice g τ) z θ') θ) :
    |deriv (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') θ|
      ≤ 200 * α ^ 2 * (Real.sin (|θ|)) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z (|θ|)| := by
  have habs := abs_lt.mp hθ2
  by_cases hpos : 0 ≤ θ
  · have hθpos : 0 < θ := lt_of_le_of_ne hpos (by rintro rfl; simp at hθ1)
    have hmem : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hθpos, habs.2⟩
    have heq : (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') =ᶠ[𝓝 θ]
        (fun θ' => Ppos α g τ z θ') := by
      filter_upwards [isOpen_Ioi.mem_nhds hθpos] with θ' hθ'
      exact profile_eq_Ppos hθ'.le
    have hPn : DifferentiableAt ℝ (fun θ' => Ppos α g τ z θ') θ :=
      hd.congr_of_eventuallyEq heq.symm
    rw [Filter.EventuallyEq.deriv_eq heq, abs_of_pos hθpos]
    exact abs_pdz_posbranch_le hα hα13 hz hmem hPn
  · have hneg : θ < 0 := not_le.mp hpos
    have hmem : -θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) :=
      ⟨by linarith, by linarith [habs.1]⟩
    have heq : (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') =ᶠ[𝓝 θ]
        (fun θ' => - Ppos α g τ z (-θ')) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hneg] with θ' hθ'
      show Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ'
        = - Ppos α g τ z (-θ')
      rw [profile_eq_neg_Ppos (not_le.mpr hθ')]
    have hd' : DifferentiableAt ℝ (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') (-(-θ)) := by simpa using hd
    have hcomp : DifferentiableAt ℝ (fun w : ℝ => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z (-w)) (-θ) :=
      hd'.comp (-θ) (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => -w) (-θ))
    have hev : (fun w : ℝ => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z (-w)) =ᶠ[𝓝 (-θ)]
        (fun w : ℝ => - Ppos α g τ z w) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi (by linarith : (0:ℝ) < -θ)] with w hw
      have hw' : (0:ℝ) < w := hw
      show Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z (-w)
        = - Ppos α g τ z w
      rw [profile_eq_neg_Ppos (not_le.mpr (by linarith : -w < 0))]
      simp only [neg_neg]
    have hPn : DifferentiableAt ℝ (fun w : ℝ => Ppos α g τ z w) (-θ) := by
      have h1 : DifferentiableAt ℝ (fun w : ℝ => - Ppos α g τ z w) (-θ) :=
        hcomp.congr_of_eventuallyEq hev.symm
      refine (h1.neg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp
    have hb := abs_pdz_posbranch_le hα hα13 hz hmem hPn
    rw [Real.cos_neg] at hb
    have hder : deriv (fun θ' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z θ') θ
        = deriv (fun w : ℝ => Ppos α g τ z w) (-θ) := by
      rw [Filter.EventuallyEq.deriv_eq heq]
      rw [Work.FTS.EllipticEst.deriv_neg_apply, deriv_comp_neg]
      ring
    rw [hder, abs_of_neg hneg]
    exact hb

/-! ## 5. The frame bound for scalar-valued linear maps -/

lemma norm_le_frame_scalar (L : R3 →L[ℝ] ℝ) (x : R3) (hr : 0 < Work.Cyl.radial x) :
    ‖L‖ ≤ ‖L (Work.Cyl.eR x)‖ + ‖L (Work.Cyl.eTheta x)‖ + ‖L Work.Cyl.eZ‖ := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have heZ : ‖(Work.Cyl.eZ : R3)‖ = 1 := by simp [Work.Cyl.eZ, FiniteTimeSingularity.e]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  have hdecE : inner ℝ u (Work.Cyl.eR x) • Work.Cyl.eR x
      + inner ℝ u (Work.Cyl.eTheta x) • Work.Cyl.eTheta x
      + inner ℝ u Work.Cyl.eZ • Work.Cyl.eZ = u := by
    have h := Work.Cyl.decomposition (fun _ : R3 => u) x hrne
    simpa [Work.Cyl.compR, Work.Cyl.compT, Work.Cyl.compZ] using h.symm
  have hLu : L u = inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)
      + inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)
      + inner ℝ u (Work.Cyl.eZ : R3) • L Work.Cyl.eZ := by
    conv_lhs => rw [← hdecE]
    simp only [map_add, map_smul]
  have hcS : |inner ℝ u (Work.Cyl.eR x)| ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u (Work.Cyl.eR x)
    rwa [Work.Cyl.norm_eR x hrne, mul_one] at h
  have hcT : |inner ℝ u (Work.Cyl.eTheta x)| ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u (Work.Cyl.eTheta x)
    rwa [Work.Cyl.norm_eTheta x hrne, mul_one] at h
  have hcZ : |inner ℝ u (Work.Cyl.eZ : R3)| ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u (Work.Cyl.eZ : R3)
    rwa [heZ, mul_one] at h
  calc ‖L u‖
      = ‖inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)
          + inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)
          + inner ℝ u (Work.Cyl.eZ : R3) • L Work.Cyl.eZ‖ := by rw [hLu]
    _ ≤ ‖inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)
          + inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)‖
        + ‖inner ℝ u (Work.Cyl.eZ : R3) • L Work.Cyl.eZ‖ := norm_add_le _ _
    _ ≤ (‖inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)‖
          + ‖inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)‖)
        + ‖inner ℝ u (Work.Cyl.eZ : R3) • L Work.Cyl.eZ‖ := by
        gcongr
        exact norm_add_le _ _
    _ = |inner ℝ u (Work.Cyl.eR x)| * ‖L (Work.Cyl.eR x)‖
        + |inner ℝ u (Work.Cyl.eTheta x)| * ‖L (Work.Cyl.eTheta x)‖
        + |inner ℝ u (Work.Cyl.eZ : R3)| * ‖L Work.Cyl.eZ‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖u‖ * ‖L (Work.Cyl.eR x)‖ + ‖u‖ * ‖L (Work.Cyl.eTheta x)‖
        + ‖u‖ * ‖L Work.Cyl.eZ‖ := by
        have h1 := mul_le_mul_of_nonneg_right hcS (norm_nonneg (L (Work.Cyl.eR x)))
        have h2 := mul_le_mul_of_nonneg_right hcT (norm_nonneg (L (Work.Cyl.eTheta x)))
        have h3 := mul_le_mul_of_nonneg_right hcZ (norm_nonneg (L Work.Cyl.eZ))
        linarith
    _ = (‖L (Work.Cyl.eR x)‖ + ‖L (Work.Cyl.eTheta x)‖ + ‖L Work.Cyl.eZ‖) * ‖u‖ := by
        ring

/-! ## 6. The chain-rule bound for `x ↦ Ψ(ρ(x)^{3α}/B, θ(x))` -/

lemma norm_fderiv_profile_comp_le {α B : ℝ} (hα : 0 < α) (hB : 0 < B)
    {Ψ : ℝ → ℝ → ℝ} {x : R3} (hr : 0 < Work.Cyl.radial x)
    (hD : Work.Cyl.DiffAt2 Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)) :
    ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y)) x‖
      ≤ 2 * (|Work.Spaces.pz Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
              * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B))
        + 2 * |Work.Spaces.pth Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
            / Work.Cyl.rho x := by
  set P : ℝ := Work.Spaces.pz Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x) with hP
  set Q : ℝ := Work.Spaces.pth Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x) with hQ
  set A : ℝ := (3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B with hA
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hρpos.le _)) hB.le
  -- the two-variable function `(r,θ) ↦ Ψ(r^{3α}/B, θ)`
  set Ψt : ℝ → ℝ → ℝ := fun r θ' => Ψ (r ^ (3 * α) / B) θ' with hΨt
  have hDt : Work.Cyl.DiffAt2 Ψt (Work.Cyl.rho x) (Work.Cyl.theta x) := by
    have hφ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.1 ^ (3 * α) / B, p.2))
        (Work.Cyl.rho x, Work.Cyl.theta x) := by
      have h0 : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ (3 * α))
          (Work.Cyl.rho x, Work.Cyl.theta x) :=
        differentiableAt_fst.rpow_const (Or.inl (ne_of_gt hρpos))
      have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ (3 * α) / B)
          (Work.Cyl.rho x, Work.Cyl.theta x) := by
        have h := h0.mul_const B⁻¹
        convert h using 1
        funext p
        rw [div_eq_mul_inv]
      exact h1.prodMk differentiableAt_snd
    have h := hD.comp (Work.Cyl.rho x, Work.Cyl.theta x) hφ
    simpa [Work.Cyl.DiffAt2, hΨt, Function.comp_def] using h
  -- the derivative in the first slot of `Ψt`
  have hpdR : Work.Cyl.pdR Ψt (Work.Cyl.rho x) (Work.Cyl.theta x) = P * A := by
    have hslice : DifferentiableAt ℝ (fun s : ℝ => Ψ s (Work.Cyl.theta x))
        (Work.Cyl.rho x ^ (3 * α) / B) :=
      Work.Cyl.differentiableAt_slice_fst Ψ _ _ hD
    have hder : HasDerivAt (fun s : ℝ => Ψ s (Work.Cyl.theta x)) P
        (Work.Cyl.rho x ^ (3 * α) / B) := by
      rw [hP]
      simpa [Work.Spaces.pz] using hslice.hasDerivAt
    have hbase : HasDerivAt (fun r : ℝ => r ^ (3 * α))
        ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1)) (Work.Cyl.rho x) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hρpos))
    have hbase2 : HasDerivAt (fun r : ℝ => r ^ (3 * α) / B)
        ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B) (Work.Cyl.rho x) :=
      hbase.div_const B
    have hcomp := hder.comp (Work.Cyl.rho x) hbase2
    rw [Work.Cyl.pdR, hA]
    simpa [hΨt, Function.comp_def] using hcomp.deriv
  -- the derivative in the second slot of `Ψt`
  have hpdZ : Work.Cyl.pdZ Ψt (Work.Cyl.rho x) (Work.Cyl.theta x) = Q := by
    rw [hQ]
    rfl
  set H : R3 → ℝ := fun y => Ψ (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y) with hH
  have hHdiff : DifferentiableAt ℝ H x :=
    Work.Cyl.differentiableAt_rho_theta_comp Ψt x hDt hr
  have hER : (fderiv ℝ H x) (Work.Cyl.eR x)
      = Real.cos (Work.Cyl.theta x) * (P * A) - Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q := by
    rw [hH]
    change (fderiv ℝ (fun y : R3 => Ψt (Work.Cyl.rho y) (Work.Cyl.theta y)) x)
        (Work.Cyl.eR x) = _
    rw [Work.Cyl.fderiv_rho_theta_eR Ψt x hDt hr, hpdR, hpdZ]
  have hEZ : (fderiv ℝ H x) Work.Cyl.eZ
      = Real.sin (Work.Cyl.theta x) * (P * A) + Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x * Q := by
    rw [hH]
    change (fderiv ℝ (fun y : R3 => Ψt (Work.Cyl.rho y) (Work.Cyl.theta y)) x)
        Work.Cyl.eZ = _
    rw [Work.Cyl.fderiv_rho_theta_eZ Ψt x hDt hr, hpdR, hpdZ]
  have hETh : (fderiv ℝ H x) (Work.Cyl.eTheta x) = 0 := by
    rw [hH]
    change (fderiv ℝ (fun y : R3 => Ψt (Work.Cyl.rho y) (Work.Cyl.theta y)) x)
        (Work.Cyl.eTheta x) = _
    exact fderiv_rho_theta_eTheta Ψt x hDt hr
  -- the two directional bounds
  have hERb : ‖(fderiv ℝ H x) (Work.Cyl.eR x)‖ ≤ |P| * A + |Q| / Work.Cyl.rho x := by
    rw [hER, Real.norm_eq_abs]
    have h1 : |Real.cos (Work.Cyl.theta x) * (P * A)
        - Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q|
        ≤ |Real.cos (Work.Cyl.theta x) * (P * A)|
          + |Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q| := by
      simpa using abs_sub_le (Real.cos (Work.Cyl.theta x) * (P * A)) 0
        (Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q)
    have h2 : |Real.cos (Work.Cyl.theta x) * (P * A)| ≤ |P| * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA0]
      have hc := Real.abs_cos_le_one (Work.Cyl.theta x)
      calc |Real.cos (Work.Cyl.theta x)| * (|P| * A) ≤ 1 * (|P| * A) := by
            gcongr
        _ = |P| * A := by ring
    have h3 : |Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x * Q| ≤ |Q| / Work.Cyl.rho x := by
      rw [abs_mul, abs_div]
      have hs := Real.abs_sin_le_one (Work.Cyl.theta x)
      have hρ : |Work.Cyl.rho x| = Work.Cyl.rho x := abs_of_pos hρpos
      rw [hρ]
      calc |Real.sin (Work.Cyl.theta x)| / Work.Cyl.rho x * |Q| ≤ 1 / Work.Cyl.rho x * |Q| := by
            gcongr
        _ = |Q| / Work.Cyl.rho x := by ring
    linarith
  have hEZb : ‖(fderiv ℝ H x) Work.Cyl.eZ‖ ≤ |P| * A + |Q| / Work.Cyl.rho x := by
    rw [hEZ, Real.norm_eq_abs]
    have h1 : |Real.sin (Work.Cyl.theta x) * (P * A)
        + Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x * Q|
        ≤ |Real.sin (Work.Cyl.theta x) * (P * A)|
          + |Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x * Q| := abs_add_le _ _
    have h2 : |Real.sin (Work.Cyl.theta x) * (P * A)| ≤ |P| * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA0]
      have hc := Real.abs_sin_le_one (Work.Cyl.theta x)
      calc |Real.sin (Work.Cyl.theta x)| * (|P| * A) ≤ 1 * (|P| * A) := by gcongr
        _ = |P| * A := by ring
    have h3 : |Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x * Q| ≤ |Q| / Work.Cyl.rho x := by
      rw [abs_mul, abs_div]
      have hs := Real.abs_cos_le_one (Work.Cyl.theta x)
      have hρ : |Work.Cyl.rho x| = Work.Cyl.rho x := abs_of_pos hρpos
      rw [hρ]
      calc |Real.cos (Work.Cyl.theta x)| / Work.Cyl.rho x * |Q| ≤ 1 / Work.Cyl.rho x * |Q| := by
            gcongr
        _ = |Q| / Work.Cyl.rho x := by ring
    linarith
  calc ‖fderiv ℝ H x‖
      ≤ ‖(fderiv ℝ H x) (Work.Cyl.eR x)‖ + ‖(fderiv ℝ H x) (Work.Cyl.eTheta x)‖
        + ‖(fderiv ℝ H x) Work.Cyl.eZ‖ := norm_le_frame_scalar _ x hr
    _ ≤ 2 * (|P| * A) + 2 * |Q| / Work.Cyl.rho x := by
        rw [hETh, norm_zero, mul_div_assoc]
        linarith
    _ = 2 * (|Work.Spaces.pz Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)| * A)
        + 2 * |Work.Spaces.pth Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
            / Work.Cyl.rho x := by rw [hP, hQ]
    _ = 2 * (|Work.Spaces.pz Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
              * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B))
        + 2 * |Work.Spaces.pth Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)|
            / Work.Cyl.rho x := by rw [hA]

/-! ## 7. Differentiability of the rescaled two-variable function -/

lemma diffAt2_comp_rpow {α B : ℝ} (hB : 0 < B) {Ψ : ℝ → ℝ → ℝ} {x : R3}
    (hr : 0 < Work.Cyl.radial x)
    (hD : Work.Cyl.DiffAt2 Ψ (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)) :
    Work.Cyl.DiffAt2 (fun r θ => Ψ (r ^ (3 * α) / B) θ) (Work.Cyl.rho x) (Work.Cyl.theta x) := by
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  have hφ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.1 ^ (3 * α) / B, p.2))
      (Work.Cyl.rho x, Work.Cyl.theta x) := by
    have h0 : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ (3 * α))
        (Work.Cyl.rho x, Work.Cyl.theta x) :=
      differentiableAt_fst.rpow_const (Or.inl (ne_of_gt hρpos))
    have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ (3 * α) / B)
        (Work.Cyl.rho x, Work.Cyl.theta x) := by
      have h := h0.mul_const B⁻¹
      convert h using 1
      funext p
      rw [div_eq_mul_inv]
    exact h1.prodMk differentiableAt_snd
  have h := hD.comp (Work.Cyl.rho x, Work.Cyl.theta x) hφ
  simpa [Work.Cyl.DiffAt2, Function.comp_def] using h

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.physOmega_timeDeriv_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology

namespace Work.FTS.FireFix.Clauses

/-! ## The amplitude factor `t ↦ (C.A (τ(t)))⁻¹` -/

/-- **The amplitude factor of the chain rule is continuous on the physical window.**  The extended
inverse clock `clockInv C` is continuous on `[0, C.T)` (it is differentiable there, with the
tangent extension at `0`), it takes values in `[0,∞)` on that window, and `C.A` is continuous and
positive on `[0,∞)`; hence the composite `t ↦ C.A (clockInv C t)` is continuous on `[0, C.T)` and
nowhere zero there, so its inverse is too. -/
theorem clockInv_amplitude_inv_continuousOn {C : Work.FTS.Physical.PhysClock} :
    ContinuousOn (fun t : ℝ => (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
      (Set.Ico (0 : ℝ) C.T) := by
  have hclock : ContinuousOn (fun t : ℝ => Work.FTS.Physical.clockInv C t)
      (Set.Ico (0 : ℝ) C.T) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      exact (Work.FTS.Physical.clockInv_hasDerivAt_zero C).continuousAt.continuousWithinAt
    · exact (Work.FTS.Physical.clockInv_hasDerivAt C ⟨h, ht.2⟩).continuousAt.continuousWithinAt
  have hA : ContinuousOn (fun t : ℝ => C.A (Work.FTS.Physical.clockInv C t))
      (Set.Ico (0 : ℝ) C.T) := by
    have h := C.hAcont.comp hclock
      (fun t ht => Work.FTS.Physical.clockInv_nonneg C ht)
    simpa only [Function.comp_def] using h
  exact hA.inv₀
    (fun t ht => ne_of_gt (C.hApos _ (Work.FTS.Physical.clockInv_nonneg C ht)))

/-! ## Joint continuity of `∂_τ physVort` through the clock -/

/-- **The fake-time derivative of the physical vorticity, read through the extended inverse clock,
is continuous on the physical window `ℝ³ × [0, C.T)`.**

At every point `q₀` of the window we choose the fake-time strip `[0, τ(q₀.2) + 1]`, which carries
the full bundle of `physVort α A B g` (`Prime.physVort_bundle`); its two Hölder clauses (in `x`,
uniformly in `τ`, from the space derivative bound; and in `τ`, uniformly in `x`, from the bundle)
give the continuity of `(x,τ) ↦ ∂_τ physVort … x τ` within `ℝ³ × [0,∞)` at `(q₀.1, τ(q₀.2))`, and
the clock map `q ↦ (q.1, τ(q.2))` is continuous with image in `ℝ³ × [0,∞)`. -/
theorem timeDeriv_physVort_clock_continuousOn {α : ℝ} (hα : 0 < α)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) q.1
          (Work.FTS.Physical.clockInv C q.2))
      (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) := by
  intro q₀ hq₀
  set Φ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3) × ℝ :=
    fun q => (q.1, Work.FTS.Physical.clockInv C q.2)
  have hτ₀ : 0 ≤ Work.FTS.Physical.clockInv C q₀.2 :=
    Work.FTS.Physical.clockInv_nonneg C hq₀.2
  have hSpos : 0 < Work.FTS.Physical.clockInv C q₀.2 + 1 := by linarith
  -- the fake-time bundle and its two Hölder clauses
  obtain ⟨_R, _hR, hbun⟩ := Work.FTS.FireFix.Prime.physVort_bundle
    (hreg (Work.FTS.Physical.clockInv C q₀.2 + 1) hSpos)
  obtain ⟨c, hc, Cx, _hCx, hx⟩ := Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_general
    (α := (⟨α, hα.le⟩ : NNReal)) hα hSpos hbun
  obtain ⟨N, hN⟩ := hbun.2.2
  -- joint continuity of `∂_τ physVort` within `ℝ³ × [0,∞)`
  have hΨ : ContinuousWithinAt
      (fun p : EuclideanSpace ℝ (Fin 3) × ℝ =>
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) p.1 p.2)
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) (Φ q₀) := by
    refine Support.holder_pair_continuousWithinAt
      (C := Cx) (N := N) (c := c) (a := α)
      (S := Work.FTS.Physical.clockInv C q₀.2 + 1)
      (t₀ := Work.FTS.Physical.clockInv C q₀.2) (x₀ := q₀.1)
      hc hα hτ₀ (by linarith) (fun x x' t ht => ?_) (fun x t t' ht ht' => ?_)
    · have h := hx x x' t ht
      calc dist (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t)
              (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x' t)
          = ‖FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t -
              FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x' t‖ := by
            rw [dist_eq_norm]
        _ ≤ Cx * ‖x - x'‖ ^ c := h
    · have h := hN x t ht t' ht'
      calc dist (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t)
              (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t')
          = ‖FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t -
              FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t'‖ := by
            rw [dist_eq_norm]
        _ ≤ N * |t - t'| ^ α := h
  -- the clock map and the composition
  have hclockAt : ContinuousAt (Work.FTS.Physical.clockInv C) q₀.2 := by
    rcases eq_or_lt_of_le hq₀.2.1 with h | h
    · rw [← h]
      exact (Work.FTS.Physical.clockInv_hasDerivAt_zero C).continuousAt
    · exact (Work.FTS.Physical.clockInv_hasDerivAt C ⟨h, hq₀.2.2⟩).continuousAt
  have hclockWithin : ContinuousWithinAt (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      Work.FTS.Physical.clockInv C q.2) (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) q₀ := by
    have h := hclockAt.comp (continuous_snd.continuousAt (x := q₀))
    simpa only [Function.comp_def] using h.continuousWithinAt
  have hΦ : ContinuousWithinAt Φ (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) q₀ :=
    continuous_fst.continuousWithinAt.prodMk hclockWithin
  have hmap : Set.MapsTo Φ (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T)
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
    fun q hq => ⟨trivial, Work.FTS.Physical.clockInv_nonneg C hq.2⟩
  have hcomp := ContinuousWithinAt.comp (x := q₀) (f := Φ) hΨ hΦ hmap
  simpa only [Φ, Function.comp_def] using hcomp

/-! ## The target -/

theorem physOmega_timeDeriv_continuous {α : ℝ} (hα : 0 < α)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        FiniteTimeSingularity.timeDeriv
          (fun y s => - Work.FTS.Physical.physOmega α A B g C y s) q.1 q.2)
      (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) := by
  have hB : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) q.1
          (Work.FTS.Physical.clockInv C q.2))
      (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) :=
    timeDeriv_physVort_clock_continuousOn hα hreg
  have hAinv := clockInv_amplitude_inv_continuousOn (C := C)
  have h1 : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      (C.A (Work.FTS.Physical.clockInv C q.2))⁻¹) (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) := by
    have h : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        (C.A (Work.FTS.Physical.clockInv C q.2))⁻¹) (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) :=
      hAinv.comp
        (g := fun t : ℝ => (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
        (f := fun q : EuclideanSpace ℝ (Fin 3) × ℝ => q.2)
        (continuous_snd : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × ℝ => q.2)).continuousOn
        (fun _ hq => hq.2)
    simpa only [Function.comp_def] using h
  have hH : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      - ((C.A (Work.FTS.Physical.clockInv C q.2))⁻¹ •
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) q.1
          (Work.FTS.Physical.clockInv C q.2)))
      (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) :=
    (h1.smul hB).neg
  refine hH.congr (fun q hq => ?_)
  exact Support.timeDeriv_physOmega_eq hα hreg q.1 hq.2

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.VortEqLocal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.FireFix

/-- **The pointwise `(u·∇)ω` identity** for a swirl vorticity and a no-swirl velocity field.  This
is `Work.CoreResiduals.VorticityEquation.directionalDeriv_swirl_cylField` with the `DiffAt2`
hypothesis required only at the point `(radial x, axial x)` (its proof only uses it there). -/
theorem directionalDeriv_swirl_cylField_at {ur uz W : ℝ → ℝ → ℝ → ℝ} {x : R3} {t : ℝ}
    (hW : Work.Cyl.DiffAt2 (fun r z => W r z t) (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    directionalDeriv
        (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
        (fun x t => Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) x t
      = (ur (Work.Cyl.radial x) (Work.Cyl.axial x) t
            * Work.Cyl.pdR (fun r' z' => W r' z' t) (Work.Cyl.radial x) (Work.Cyl.axial x)
          + uz (Work.Cyl.radial x) (Work.Cyl.axial x) t
            * Work.Cyl.pdZ (fun r' z' => W r' z' t) (Work.Cyl.radial x) (Work.Cyl.axial x))
        • Work.Cyl.eTheta x := by
  rw [directionalDeriv]
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hG : Work.Cyl.DiffAt2 (fun r z => W r z t) (Work.Cyl.radial x) (Work.Cyl.axial x) := hW
  have hrad : DifferentiableAt ℝ Work.Cyl.radial x := Work.Cyl.differentiableAt_radial x hrne
  have hax : DifferentiableAt ℝ Work.Cyl.axial x := Work.Cyl.differentiableAt_axial x
  have hΦ : DifferentiableAt ℝ (fun y : R3 => (Work.Cyl.radial y, Work.Cyl.axial y)) x :=
    hrad.prodMk hax
  have hc : DifferentiableAt ℝ (fun y : R3 => W (Work.Cyl.radial y) (Work.Cyl.axial y) t) x :=
    DifferentiableAt.comp (g := fun p : ℝ × ℝ => W p.1 p.2 t) x hG hΦ
  have hf : DifferentiableAt ℝ (fun y : R3 => Work.Cyl.eTheta y) x := by
    have h1 : DifferentiableAt ℝ (fun y : R3 => (Work.Cyl.radial y)⁻¹) x := hrad.inv hrne
    have h2 : DifferentiableAt ℝ (fun y : R3 => Work.Cyl.angularVec y) x :=
      Work.CoreResiduals.VorticityEquation.differentiableAt_angularVec x
    have h := h1.smul h2
    convert h using 1
    funext y
    simp [Work.Cyl.eTheta, one_div]
  rw [fderiv_fun_smul hc hf]
  rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [Work.CoreResiduals.VorticityEquation.fderiv_eTheta_cylField_eq_zero
    (fun r z => ur r z t) (fun r z => uz r z t) x hr]
  rw [Work.CoreResiduals.VorticityEquation.fderiv_comp_radial_axial (fun r z => W r z t) x
        (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) hG hr]
  have hsq : x 0 ^ 2 + x 1 ^ 2 = Work.Cyl.radial x ^ 2 := (Work.Cyl.radial_sq x).symm
  have hv0 : (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 0
      = ur (Work.Cyl.radial x) (Work.Cyl.axial x) t * x 0 / Work.Cyl.radial x :=
    Work.Cyl.cylField_zero _ _ x
  have hv1 : (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 1
      = ur (Work.Cyl.radial x) (Work.Cyl.axial x) t * x 1 / Work.Cyl.radial x :=
    Work.Cyl.cylField_one _ _ x
  have hdot' : x 0 * (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 0
      + x 1 * (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 1
      = ur (Work.Cyl.radial x) (Work.Cyl.axial x) t * Work.Cyl.radial x := by
    rw [hv0, hv1]; field_simp; rw [hsq]
  have hdot : (x 0 * (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 0
      + x 1 * (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 1) / Work.Cyl.radial x
      = ur (Work.Cyl.radial x) (Work.Cyl.axial x) t := by
    rw [hdot']; field_simp
  rw [hdot, Work.Cyl.cylField_two]
  simp only [smul_zero, zero_add]
  congr 1
  ring

/-- **The pointwise `(ω·∇)u` identity**; pointwise version of
`Work.CoreResiduals.VorticityEquation.directionalDeriv_cylField_swirl`. -/
theorem directionalDeriv_cylField_swirl_at {ur uz W : ℝ → ℝ → ℝ → ℝ} {x : R3} {t : ℝ}
    (hu : Work.Cyl.DiffAt2 (fun r z => ur r z t) (Work.Cyl.radial x) (Work.Cyl.axial x) ∧
      Work.Cyl.DiffAt2 (fun r z => uz r z t) (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    directionalDeriv
        (fun x t => Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x)
        (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
      = (W (Work.Cyl.radial x) (Work.Cyl.axial x) t
          * (ur (Work.Cyl.radial x) (Work.Cyl.axial x) t / Work.Cyl.radial x)) • Work.Cyl.eTheta x := by
  rw [directionalDeriv]
  rw [map_smul, Work.CoreResiduals.VorticityEquation.fderiv_cylField_eTheta
        (fun r z => ur r z t) (fun r z => uz r z t) x hu.1 hu.2 hr]
  simp only [smul_smul, Work.Cyl.redR]

/-- **The pointwise scalar reduction of the `ℝ³` vorticity equation.**  If the meridian residual of
`(W, ψ)` vanishes at `(radial x, axial x, t)` and the meridian pair is differentiable there, then
the `ℝ³` vorticity equation holds at `(x,t)` for the stream-function velocity
`psiField (ψ · t)` and the swirl vorticity `W(radial x, axial x, t) • e_θ(x)`. -/
theorem vorticityEquation_at {W ψ : ℝ → ℝ → ℝ → ℝ} {x : R3} {t : ℝ}
    (hr : 0 < Work.Cyl.radial x)
    (hW : Work.Cyl.DiffAt2 (fun r z => W r z t) (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hψC : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2 t)
      (Work.Cyl.radial x, Work.Cyl.axial x))
    (hres : Work.CoreResiduals.meridianResid W ψ (Work.Cyl.radial x) (Work.Cyl.axial x) t = 0) :
    timeDeriv (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
      + directionalDeriv (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
          (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x) x t
      = directionalDeriv (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x)
          (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t := by
  have hψd : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2 t)
      (Work.Cyl.radial x, Work.Cyl.axial x) := hψC.differentiableAt (by norm_num)
  have hu1 : Work.Cyl.DiffAt2 (fun r z => Work.Cyl.pdZ (fun r' z' => ψ r' z' t) r z)
      (Work.Cyl.radial x) (Work.Cyl.axial x) :=
    Work.Cyl.differentiableAt_pdZ (fun r' z' => ψ r' z' t) _ _ hψC
  have hu2 : Work.Cyl.DiffAt2
      (fun r z => -(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z)
      (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
    have h1 : Work.Cyl.DiffAt2 (fun r z => Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z)
        (Work.Cyl.radial x) (Work.Cyl.axial x) :=
      Work.Cyl.differentiableAt_pdR (fun r' z' => ψ r' z' t) _ _ hψC
    have h2 : DifferentiableAt ℝ
        (fun p : ℝ × ℝ => ψ p.1 p.2 t * (p.1)⁻¹) (Work.Cyl.radial x, Work.Cyl.axial x) :=
      hψd.mul (differentiableAt_fst.inv (by simpa using hrne))
    exact h2.neg.sub h1
  have hpsi : (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x)
      = fun x t => Work.Cyl.cylField (fun r z => Work.Cyl.pdZ (fun r' z' => ψ r' z' t) r z)
          (fun r z => -(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z) x := by
    funext y s
    simp only [Work.Cyl.psiField]
  rw [hpsi]
  rw [Work.CoreResiduals.VorticityEquation.timeDeriv_swirl (W := W) x t,
    directionalDeriv_swirl_cylField_at (W := W) (ur := fun r z t => Work.Cyl.pdZ
      (fun r' z' => ψ r' z' t) r z)
      (uz := fun r z t => -(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z) hW hr,
    directionalDeriv_cylField_swirl_at (W := W) (ur := fun r z t => Work.Cyl.pdZ
      (fun r' z' => ψ r' z' t) r z)
      (uz := fun r z t => -(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z)
      ⟨hu1, hu2⟩ hr, ← add_smul]
  congr 1
  rw [← add_assoc]
  simp only [Work.CoreResiduals.meridianResid] at hres
  linarith

/-- **Transport of the pointwise vorticity equation along a change of the pair `(u,ω)`.**  If the
velocity fields agree near `x` and the vorticity fields agree identically, the equation transfers
(both `timeDeriv` and `directionalDeriv` only see the pointwise values). -/
theorem vorticityEquation_transfer {u v ω η : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (huv : (fun y => u y t) =ᶠ[𝓝 x] (fun y => v y t)) (hωη : ω = η)
    (h : timeDeriv η x t + directionalDeriv η v x t = directionalDeriv v η x t) :
    timeDeriv ω x t + directionalDeriv ω u x t = directionalDeriv u ω x t := by
  have h1 : timeDeriv ω x t = timeDeriv η x t := by rw [hωη]
  have h2 : directionalDeriv ω u x t = directionalDeriv η v x t := by
    show fderiv ℝ (fun y => ω y t) x (u x t) = fderiv ℝ (fun y => η y t) x (v x t)
    rw [show (fun y => ω y t) = (fun y => η y t) from by funext y; rw [hωη],
      huv.eq_of_nhds]
  have h3 : directionalDeriv u ω x t = directionalDeriv v η x t := by
    show fderiv ℝ (fun y => u y t) x (ω x t) = fderiv ℝ (fun y => v y t) x (η x t)
    rw [huv.fderiv_eq, show ω x t = η x t from by rw [hωη]]
  rw [h1, h2, h3]
  exact h

/-- **The pointwise vorticity equation of the reconstruction.**  From the meridian equation on the
window `(0,T)` (`Work.FTS.MeridianDyn.MeridianEqOn`) and the two differentiability clauses of the
design (`hW`, `hΨ`), the `ℝ³` vorticity equation holds at every `x ∈ Uax` and every `t ∈ (0,T)`. -/
theorem vorticityEquationOn_of_meridianEqOn {W ψ : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hmer : Work.FTS.MeridianDyn.MeridianEqOn W ψ T)
    (hW : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      Work.Cyl.DiffAt2 (fun r z => W r z t) r z)
    (hΨ : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2 t) (r, z)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Work.FTS.PressureOn.Uax,
      timeDeriv (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
        + directionalDeriv
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
            (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x) x t
        = directionalDeriv (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x)
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t := by
  intro t ht x hx
  have hr : 0 < Work.Cyl.radial x := by
    rcases eq_or_lt_of_le (Work.Cyl.radial_nonneg x) with h | h
    · exfalso
      have h01 : x 0 = 0 ∧ x 1 = 0 := (Work.Cyl.radial_eq_zero_iff x).mp h.symm
      exact hx.2 (by rw [h01.1, h01.2]; norm_num)
    · exact h
  exact vorticityEquation_at (hr := hr) (hW := hW t ht _ _ hr hx.1)
    (hψC := hΨ t ht _ _ hr hx.1) (hres := hmer _ _ t hr hx.1 ht)

end Work.FTS.FireFix
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.AbsPdZPdRPsiCoreLeOne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sharp (`q = 1`) pointwise decay of `∂_z ψ`, `∂_r ψ`

This is the `q = 1` counterpart of `Work.FTS.BSIdent.Cyl.abs_combination_bound`: the profile
bounds lose the *whole* rate `(π/2 - θ)` (for `∂_θG`) resp. one power of `(π/2 - θ)` (for
`∂_wG`), no `(π/2-θ)^{q-2}` slack is available, and the exponent hypothesis is only
`2 ≤ p·λ`.  The combination bound is therefore reproved from scratch (`q = 1` makes the
`(π/2 - θ)`-bookkeeping trivial: the only thing used is `π/2 - θ ≤ π/2`), and the weight
estimate `ρ (1+ρ^p/b)^{-λ} ≤ 2 max 1 (b^λ)/(1+ρ)` is the sharp one
`rho_mul_rpow_weight_le_two`.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise bound in the sharp regime -/

/-- The two terms `c (X ∂_wG + Y ∂_θG)` of the chain rule are bounded by
`decayKzrOne p c C₀ lam b / (1+ρ)` as soon as `|X| ≤ p ρ w`, `|Y| ≤ ρ` and the profile
satisfies the three *sharp* (`q = 1`) bounds at the point. -/
theorem abs_combination_bound_one {G : ℝ → ℝ → ℝ} {p c b C₀ lam r z zc X Y : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 2 ≤ p * lam) (hzc : |zc| ≤ Work.Cyl.rhoP r z)
    (hX : |X| ≤ p * Work.Cyl.rhoP r z * (Work.Cyl.rhoP r z ^ p / b))
    (hY : |Y| ≤ Work.Cyl.rhoP r z)
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |2 * zc * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + c * (X * Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              + Y * Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))|
      ≤ decayKzrOne p c C₀ lam b / (1 + Work.Cyl.rhoP r z) := by
  set ρ := Work.Cyl.rhoP r z with hρ
  set θ := Work.Cyl.thetaP r z with hθ
  set w := ρ ^ p / b with hw
  set S := Real.pi / 2 - θ with hS
  set R := (1 + w) ^ (-lam) with hR
  have hρpos : 0 < ρ := by rw [hρ]; exact Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ ρ := hρpos.le
  have hθlt : θ < Real.pi / 2 := by rw [hθ]; exact Work.FTS.BSIdent.Cyl.thetaP_lt_pi_div_two r z
  have hθpos : 0 < θ := by rw [hθ]; exact Work.FTS.BSIdent.Cyl.thetaP_pos_of_pos hr hz
  have hSnn : 0 ≤ S := by rw [hS]; linarith
  have hSle : S ≤ Real.pi / 2 := by rw [hS]; linarith
  have hwpos : 0 < w := by
    rw [hw]; exact div_pos (Real.rpow_pos_of_pos hρpos p) hb
  have hwnn : 0 ≤ w := hwpos.le
  have h1w : (0 : ℝ) < 1 + w := by linarith
  have hRpos : 0 < R := by rw [hR]; exact Real.rpow_pos_of_pos h1w _
  have hRnn : 0 ≤ R := hRpos.le
  have h2pi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hval' : |G w θ| ≤ C₀ * S * R := hval
  have hwd' : |Work.Cyl.pdR G w θ| ≤ C₀ * S * (1 + w) ^ (-lam - 1) := hwd
  have hth' : |Work.Cyl.pdZ G w θ| ≤ C₀ * R := hth
  have hX' : |X| ≤ p * ρ * w := hX
  have hY' : |Y| ≤ ρ := hY
  have hzcb : |zc| ≤ ρ := by rw [hρ]; exact hzc
  -- the elementary comparisons
  have hwR2 : w * (1 + w) ^ (-lam - 1) ≤ R := by
    have e1 : (1 + w) ^ (-lam - 1) = R * (1 + w)⁻¹ := by
      have e2 : (1 + w) ^ (-lam - 1) = (1 + w) ^ (-lam) * (1 + w) ^ (-1 : ℝ) := by
        rw [show -lam - 1 = -lam + (-1) by ring, Real.rpow_add h1w]
      rw [e2, ← hR, Real.rpow_neg_one]
    have hw1 : w * (1 + w)⁻¹ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (show w ≤ 1 + w by linarith)
        (inv_nonneg.mpr h1w.le)
      rwa [mul_inv_cancel₀ (ne_of_gt h1w)] at h
    calc w * (1 + w) ^ (-lam - 1) = (w * (1 + w)⁻¹) * R := by rw [e1]; ring
      _ ≤ 1 * R := mul_le_mul_of_nonneg_right hw1 hRnn
      _ = R := one_mul R
  have hρR : ρ * R ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
    have h := rho_mul_rpow_weight_le_two hp hlam hb hρnn hpl
    rw [← hw, ← hR] at h
    exact h
  -- the three term bounds
  have hT1 : 2 * |zc| * |c| * (C₀ * S * R)
      ≤ (2 * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) := by
    have hCS : C₀ * S * R ≤ C₀ * (Real.pi / 2) * R := by
      have h1 : C₀ * S ≤ C₀ * (Real.pi / 2) := mul_le_mul_of_nonneg_left hSle hC₀
      calc C₀ * S * R ≤ (C₀ * (Real.pi / 2)) * R := mul_le_mul_of_nonneg_right h1 hRnn
        _ = C₀ * (Real.pi / 2) * R := by ring
    have hz2 : 2 * |zc| ≤ 2 * ρ := by linarith [hzcb]
    have hz2c : 2 * |zc| * |c| ≤ 2 * ρ * |c| := mul_le_mul_of_nonneg_right hz2 (abs_nonneg c)
    calc 2 * |zc| * |c| * (C₀ * S * R)
        ≤ 2 * ρ * |c| * (C₀ * (Real.pi / 2) * R) :=
          mul_le_mul hz2c hCS (mul_nonneg (mul_nonneg hC₀ hSnn) hRnn)
            (mul_nonneg (mul_nonneg (by norm_num) hρnn) (abs_nonneg c))
      _ = (2 * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) := by ring
  have hT2 : |c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
      ≤ (p * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) := by
    have hCS : C₀ * S * (1 + w) ^ (-lam - 1)
        ≤ C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1) := by
      have h1 : C₀ * S ≤ C₀ * (Real.pi / 2) := mul_le_mul_of_nonneg_left hSle hC₀
      calc C₀ * S * (1 + w) ^ (-lam - 1)
          ≤ (C₀ * (Real.pi / 2)) * (1 + w) ^ (-lam - 1) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg h1w.le _)
        _ = C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1) := by ring
    have h1 : |c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
        ≤ |c| * ((p * ρ * w) * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hCS (mul_nonneg (mul_nonneg hp.le hρnn) hwnn))
        (abs_nonneg c)
    have h2 : |c| * ((p * ρ * w) * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1)))
        = (p * (Real.pi / 2))
          * (|c| * C₀ * (ρ * (w * (1 + w) ^ (-lam - 1)))) := by ring
    have h3 : (p * (Real.pi / 2))
          * (|c| * C₀ * (ρ * (w * (1 + w) ^ (-lam - 1))))
        ≤ (p * (Real.pi / 2)) * (|c| * C₀ * (ρ * R)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwR2 hρnn)
          (mul_nonneg (abs_nonneg c) hC₀))
        (mul_nonneg hp.le h2pi.le)
    exact h1.trans (h2.trans_le h3)
  have hT3 : |c| * (ρ * (C₀ * R)) ≤ 1 * (|c| * C₀ * (ρ * R)) := by
    have h : |c| * (ρ * (C₀ * R)) = 1 * (|c| * C₀ * (ρ * R)) := by ring
    rw [h]
  have hsum : 2 * |zc| * |c| * (C₀ * S * R)
        + (|c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
          + |c| * (ρ * (C₀ * R)))
      ≤ (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
        * (|c| * C₀ * (ρ * R)) := by
    have h := add_le_add hT1 (add_le_add hT2 hT3)
    calc 2 * |zc| * |c| * (C₀ * S * R)
          + (|c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
            + |c| * (ρ * (C₀ * R)))
        ≤ (2 * (Real.pi / 2)) * (|c| * C₀ * (ρ * R))
          + ((p * (Real.pi / 2)) * (|c| * C₀ * (ρ * R))
            + 1 * (|c| * C₀ * (ρ * R))) := h
      _ = (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
          * (|c| * C₀ * (ρ * R)) := by ring
  have hfin : (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
        * (|c| * C₀ * (ρ * R))
      ≤ decayKzrOne p c C₀ lam b / (1 + ρ) := by
    have hA : (0 : ℝ) ≤ |c| * C₀ := mul_nonneg (abs_nonneg c) hC₀
    have hb1 : |c| * C₀ * (ρ * R) ≤ |c| * C₀ * (2 * max 1 (b ^ lam) / (1 + ρ)) :=
      mul_le_mul_of_nonneg_left hρR hA
    have hcoef : (0 : ℝ) ≤ 2 * (Real.pi / 2) + p * (Real.pi / 2) + 1 := by
      have := mul_nonneg hp.le h2pi.le; linarith [Real.pi_pos]
    calc (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
          * (|c| * C₀ * (ρ * R))
        ≤ (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
            * (|c| * C₀ * (2 * max 1 (b ^ lam) / (1 + ρ))) :=
          mul_le_mul_of_nonneg_left hb1 hcoef
      _ = decayKzrOne p c C₀ lam b / (1 + ρ) := by rw [decayKzrOne]; ring
  -- assembling
  have h1a : |2 * zc * c * G w θ| = 2 * |zc| * |c| * |G w θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h1b : |c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)|
      = |c| * |X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ| := abs_mul c _
  have h1c : |X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ|
      ≤ |X| * |Work.Cyl.pdR G w θ| + |Y| * |Work.Cyl.pdZ G w θ| :=
    (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_mul]))
  have h1 : |2 * zc * c * G w θ + c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)|
      ≤ 2 * |zc| * |c| * |G w θ|
        + (|c| * (|X| * |Work.Cyl.pdR G w θ|) + |c| * (|Y| * |Work.Cyl.pdZ G w θ|)) := by
    calc |2 * zc * c * G w θ + c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)|
        ≤ |2 * zc * c * G w θ| + |c * (X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ)| :=
          abs_add_le _ _
      _ = 2 * |zc| * |c| * |G w θ|
            + |c| * |X * Work.Cyl.pdR G w θ + Y * Work.Cyl.pdZ G w θ| := by rw [h1a, h1b]
      _ ≤ 2 * |zc| * |c| * |G w θ|
            + |c| * (|X| * |Work.Cyl.pdR G w θ| + |Y| * |Work.Cyl.pdZ G w θ|) := by
          have hc := mul_le_mul_of_nonneg_left h1c (abs_nonneg c)
          linarith
      _ = 2 * |zc| * |c| * |G w θ|
            + (|c| * (|X| * |Work.Cyl.pdR G w θ|)
              + |c| * (|Y| * |Work.Cyl.pdZ G w θ|)) := by rw [mul_add]
  have h2 : 2 * |zc| * |c| * |G w θ|
        + (|c| * (|X| * |Work.Cyl.pdR G w θ|) + |c| * (|Y| * |Work.Cyl.pdZ G w θ|))
      ≤ 2 * |zc| * |c| * (C₀ * S * R)
        + (|c| * ((p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)))
          + |c| * (ρ * (C₀ * R))) := by
    have hA : 2 * |zc| * |c| * |G w θ| ≤ 2 * |zc| * |c| * (C₀ * S * R) :=
      mul_le_mul_of_nonneg_left hval'
        (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg zc)) (abs_nonneg c))
    have hB : |X| * |Work.Cyl.pdR G w θ| ≤ (p * ρ * w) * (C₀ * S * (1 + w) ^ (-lam - 1)) :=
      mul_le_mul hX' hwd' (abs_nonneg _) (mul_nonneg (mul_nonneg hp.le hρnn) hwnn)
    have hD : |Y| * |Work.Cyl.pdZ G w θ| ≤ ρ * (C₀ * R) :=
      mul_le_mul hY' hth' (abs_nonneg _) hρnn
    exact add_le_add hA (add_le_add (mul_le_mul_of_nonneg_left hB (abs_nonneg c))
      (mul_le_mul_of_nonneg_left hD (abs_nonneg c)))
  exact h1.trans (h2.trans (hsum.trans hfin))

/-! ## The theorem -/

theorem abs_pdZ_pdR_psiCore_le_one {G : ℝ → ℝ → ℝ} {p c b C₀ lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 2 ≤ p * lam)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam))
    (hwd : |Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam - 1))
    (hth : |Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.psiCore p c b G) r z|
        ≤ Work.FTS.BSIdentP.Levels.decayKzrOne p c C₀ lam b / (1 + Work.Cyl.rhoP r z) ∧
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.psiCore p c b G) r z|
        ≤ Work.FTS.BSIdentP.Levels.decayKzrOne p c C₀ lam b / (1 + Work.Cyl.rhoP r z) := by
  have hρnn : 0 ≤ Work.Cyl.rhoP r z := (Work.Cyl.rhoP_pos hr z).le
  have hwp : (0 : ℝ) ≤ Work.Cyl.rhoP r z ^ p / b :=
    div_nonneg (Real.rpow_nonneg hρnn p) hb.le
  constructor
  · rw [Work.FTS.BSIdent.Cyl.pdZ_psiCore_eq hG hr]
    refine abs_combination_bound_one (zc := z)
      (X := p * z * (Work.Cyl.rhoP r z ^ p / b)) (Y := r)
      hC₀ hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
    · exact Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z
    · rw [abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hwp]
      have h2 : p * |z| ≤ p * Work.Cyl.rhoP r z :=
        mul_le_mul_of_nonneg_left (Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z) hp.le
      exact mul_le_mul_of_nonneg_right h2 hwp
    · rw [abs_of_nonneg hr.le]
      exact Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le
  · rw [Work.FTS.BSIdent.Cyl.pdR_psiCore_eq hG hr]
    refine abs_combination_bound_one (zc := r)
      (X := p * r * (Work.Cyl.rhoP r z ^ p / b)) (Y := -z)
      hC₀ hlam hp hb hr hz hpl ?_ ?_ ?_ hval hwd hth
    · rw [abs_of_nonneg hr.le]
      exact Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le
    · rw [abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hr.le, abs_of_nonneg hwp]
      have h2 : p * r ≤ p * Work.Cyl.rhoP r z :=
        mul_le_mul_of_nonneg_left (Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le) hp.le
      exact mul_le_mul_of_nonneg_right h2 hwp
    · rw [abs_neg]
      exact Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z

end Work.FTS.BSIdentP.Levels
end
end
