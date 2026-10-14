import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Series.BslOp.Setup
import Submission.Work.FTS.PhiStar.Series.Deleg.lzero1_pair_eFam
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.L12Add
-- ===== merged: Submission.Work.FTS.ClassC.HonestCut.integrableOn_slice_psiSeries_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "w" => Work.Spaces.w
local notation "eFam" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "acoeff" => Work.FTS.PhiStar.Series.acoeff
local notation "psiSeries" => Work.FTS.PhiStar.Series.psiSeries

/-- **The pointwise sup bound for the mode series on `Iθ`.**  Under the weighted summability
`Σ_m (m+1)|a_m(z)| < ∞` of the radial coefficients, the series `Σ_m a_m(z)·e_m(θ)` is absolutely
convergent for every `θ ∈ Iθ` and

  `|psiSeries α F z θ| ≤ 3 · Σ_m (m+1)·|a_m(z)|`.

The bound is the Weierstrass majorant `|a_m e_m θ| ≤ 3(m+1)|a_m|` coming from the sharp linear
sup bound on the eigenfamily. -/
lemma abs_psiSeries_slice_le {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hcoef : Summable (fun m : ℕ => ((m : ℝ) + 1) * |acoeff α m F z|)) {θ : ℝ}
    (hθ : θ ∈ Iθ) :
    |psiSeries α F z θ| ≤ 3 * ∑' m : ℕ, ((m : ℝ) + 1) * |acoeff α m F z| := by
  have hmode : ∀ m : ℕ, ‖acoeff α m F z * eFam m θ‖ ≤ 3 * (((m : ℝ) + 1) * |acoeff α m F z|) := by
    intro m
    rw [Real.norm_eq_abs, abs_mul]
    calc |acoeff α m F z| * |eFam m θ| ≤ |acoeff α m F z| * (3 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (Work.FTS.ClassC.abs_eFam_le m hθ) (abs_nonneg _)
      _ = 3 * (((m : ℝ) + 1) * |acoeff α m F z|) := by ring
  have hu : Summable (fun m : ℕ => 3 * (((m : ℝ) + 1) * |acoeff α m F z|)) := hcoef.mul_left 3
  have hs : Summable (fun m : ℕ => acoeff α m F z * eFam m θ) :=
    Summable.of_norm_bounded hu hmode
  have h1 : ‖∑' m : ℕ, acoeff α m F z * eFam m θ‖
      ≤ ∑' m : ℕ, ‖acoeff α m F z * eFam m θ‖ :=
    norm_tsum_le_tsum_norm hs.norm
  have h2 : (∑' m : ℕ, ‖acoeff α m F z * eFam m θ‖)
      ≤ ∑' m : ℕ, 3 * (((m : ℝ) + 1) * |acoeff α m F z|) :=
    Summable.tsum_le_tsum hmode hs.norm hu
  have h3 : (∑' m : ℕ, 3 * (((m : ℝ) + 1) * |acoeff α m F z|))
      = 3 * ∑' m : ℕ, ((m : ℝ) + 1) * |acoeff α m F z| := tsum_mul_left
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (h2.trans (le_of_eq h3))

/-- **The level-`0` `θ`-slice of the modal solution is integrable.** -/
theorem integrableOn_slice_psiSeries_zero {α : ℝ} {F : ℝ → ℝ → ℝ} (z : ℝ) (hz : 0 < z)
    (hcoef : Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|)) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0
        (Work.FTS.PhiStar.Series.psiSeries α F) z θ) Work.Spaces.Iθ := by
  set S : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) * |acoeff α m F z| with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact tsum_nonneg fun m => by positivity
  -- the uniform sup bound on the slice
  have hψ : ∀ θ ∈ Iθ, |psiSeries α F z θ| ≤ 3 * S := by
    intro θ hθ
    simpa only [hS] using abs_psiSeries_slice_le hcoef hθ
  -- measurability: the slice is a series of continuous functions
  have hψaesm : AEStronglyMeasurable (fun θ : ℝ => psiSeries α F z θ)
      (volume.restrict Iθ) := by
    show AEStronglyMeasurable
      (fun θ : ℝ => ∑' m : ℕ, acoeff α m F z * eFam m θ) _
    exact AEStronglyMeasurable.tsum
      (fun m => (continuous_const.mul (Work.FTS.PhiStar.Series.continuous_eFam m)).aestronglyMeasurable)
  have hsEta_aesm : AEStronglyMeasurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.Honest.sEta_integrableOn.aestronglyMeasurable
  have hasm2 : AEStronglyMeasurable
      (fun θ : ℝ => (w z) ^ 2 * ((psiSeries α F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (volume.restrict Iθ) :=
    ((hψaesm.pow 2).mul hsEta_aesm).const_mul ((w z) ^ 2)
  have hasm : AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ) (volume.restrict Iθ) :=
    hasm2.congr (Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq_ae α (psiSeries α F) z).symm
  -- the integrable dominating slice
  have hdom : IntegrableOn
      (fun θ : ℝ => (w z) ^ 2 * (9 * S ^ 2) * Work.FTS.EllipticEst.sEta θ) Iθ :=
    (Work.FTS.EllipticEst.Honest.sEta_integrableOn).const_mul ((w z) ^ 2 * (9 * S ^ 2))
  refine hdom.mono' hasm ?_
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 _ z θ),
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq' hθ (psiSeries α F) z]
  have hb := hψ θ hθ
  have hsq : (psiSeries α F z θ) ^ 2 ≤ (3 * S) ^ 2 := by
    rcases abs_le.mp hb with ⟨h1, h2⟩
    exact sq_le_sq' h1 h2
  have h3 : (3 * S) ^ 2 = 9 * S ^ 2 := by ring
  rw [h3] at hsq
  have hse := Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
  have hw := sq_nonneg (w z)
  calc (w z) ^ 2 * ((psiSeries α F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ (w z) ^ 2 * ((9 * S ^ 2) * Work.FTS.EllipticEst.sEta θ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hse) hw
    _ = (w z) ^ 2 * (9 * S ^ 2) * Work.FTS.EllipticEst.sEta θ := by ring

end Work.FTS.ClassC.HonestCut
end
end
-- ===== merged: Submission.Work.FTS.ClassC.ModeSumMain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "eFam" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "sEta" => Work.FTS.EllipticEst.sEta


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.CmodeIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.FTS.ClassCHon

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`. -/
theorem setIntegral_Iθ_eq_intervalIntegral (F : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, F θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), F θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- **The self-adjointness pairing of `Lzero1` with the Gegenbauer modes.**
If `u` is `C^∞` and supported in `[a,b] ⊂ (0, π/2)` (so that `u` and all its derivatives vanish
near `0` and near `π/2`, killing the boundary terms of the integration by parts), and if
`Lzero1 u` is continuous, then

  `∫_{0}^{π/2} (Lzero1 u)(θ) · eFam m θ · cos θ dθ = lam m · ∫_{0}^{π/2} u(θ) · eFam m θ · cos θ dθ`.

This is the instance `ψ = Lzero1 u`, `v = u` of the fundamental pairing identity
`Work.FTS.PhiStar.Series.Deleg.lzero1_pair_eFam`, transported from the set integral over `Iθ`
to the interval integral. -/
theorem pair_Lzero1_eFam {u : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2)
    (hu : Good a b u) (hLu : Good a b (Work.FTS.EllipticEst.Lzero1 u)) (m : ℕ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllipticEst.Lzero1 u θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam m
        * ∫ θ in (0 : ℝ)..(Real.pi / 2),
            u θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
  have h0 : (0 : ℝ) ∉ Set.Icc a b := fun h => absurd h.1 (not_le.mpr ha)
  have hpi : (Real.pi / 2) ∉ Set.Icc a b := fun h => absurd h.2 (not_le.mpr hb)
  have hkey := Work.FTS.PhiStar.Series.Deleg.lzero1_pair_eFam
    (Work.FTS.EllipticEst.Lzero1 u) u m hu.contDiff.contDiffOn
    hu.contDiff.continuous.continuousOn (hu.eq_zero 0 h0) (hu.eq_zero (Real.pi / 2) hpi)
    hLu.contDiff.continuous.continuousOn (fun θ _ => rfl)
  calc (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllipticEst.Lzero1 u θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 u θ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) :=
        (setIntegral_Iθ_eq_intervalIntegral _).symm
    _ = Work.FTS.PhiStar.Gegenbauer.lam m
          * (∫ θ in Work.Spaces.Iθ, u θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Real.cos θ) := hkey
    _ = Work.FTS.PhiStar.Gegenbauer.lam m
          * ∫ θ in (0 : ℝ)..(Real.pi / 2),
              u θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
        rw [setIntegral_Iθ_eq_intervalIntegral]

/-- **The iteration of the pairing.**  Assuming the iterates `Lop g k` are again `C^∞` and
supported in `[a,b]` (this is `Lop_good`), the mode coefficient of `g` is obtained from that of
the `k`-th iterate at the cost of the factor `(lam m)^{-k}`:

  `∫ g · e_m · cos = (lam m)^{-k} · ∫ (Lop g k) · e_m · cos`. -/
theorem cmode_iter {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2)
    (hLop : ∀ k : ℕ, Good a b (Lop g k)) {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2),
        g θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = (1 / Work.FTS.PhiStar.Gegenbauer.lam m) ^ k
        * ∫ θ in (0 : ℝ)..(Real.pi / 2),
            Lop g k θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
  have hlam : Work.FTS.PhiStar.Gegenbauer.lam m ≠ 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  induction k with
  | zero => simp
  | succ k ih =>
      have hp := pair_Lzero1_eFam ha hb (hLop k) (hLop (k + 1)) m
      rw [← Lop_succ] at hp
      have hstep : (∫ θ in (0 : ℝ)..(Real.pi / 2),
            Lop g k θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
          = (1 / Work.FTS.PhiStar.Gegenbauer.lam m)
            * ∫ θ in (0 : ℝ)..(Real.pi / 2),
                Lop g (k + 1) θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
        rw [hp]
        field_simp
      rw [ih, hstep, pow_succ]
      ring

end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.Deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false
set_option maxHeartbeats 800000


end Work.FTS.ClassCHon.Zpz
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.abs_cmode_le_lzero_iter_fix =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.BslOp.Bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The six pointwise bounds on the mode terms.**  From the angular bounds `hAng`, the coefficient
decay `hDec`, the radial bounds `hGamma` and the arithmetic of `hterm`, every differentiated mode
term is dominated by a fixed multiple of the majorant `majPow`. -/
theorem mode_bounds (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hAng : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |Gegenbauer.eFam m θ| ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ∧
      |deriv (Gegenbauer.eFam m) θ|
        ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 2 ∧
      |iteratedDeriv 2 (Gegenbauer.eFam m) θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 4 ∧
      |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 3)
    (hDec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hGamma : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ z : ℝ, 0 < z →
      |iteratedDeriv k (gammaFun α m) z| ≤ C / Gegenbauer.lam m)
    (hInt : (∀ m : ℕ, ContinuousOn (fun t => cmode m (RemSource α ψ) t) (Set.Ioi 0)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ (-(2 * (m : ℝ) / α) - 1))
        (Set.Ioi 1)) ∧
      ContinuousOn (VocabO.phiA α) (Set.Ioi 0) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)))
    (hterm : ∀ (Cdec CBz Kφ : ℝ), 0 < Cdec → 0 < CBz → 0 < Kφ → ∀ cθ : ℝ, 0 < cθ →
      ∃ D : ℝ, 0 < D ∧ ∀ m : ℕ, 1 ≤ m →
        let L := (Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
        (α ^ 2 * Cdec * CBz * Kφ / L * (3 * ((m : ℝ) + 1)) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4)
            ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3)
            ≤ D * majPow m)) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → ∃ D : ℝ, 0 < D ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y →
        |acoeff α m (RemSource α ψ) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y →
        |deriv (acoeff α m (RemSource α ψ)) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y →
        |deriv (deriv (acoeff α m (RemSource α ψ))) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + π / 2) / 2 →
        |acoeff α m (RemSource α ψ) z| * |deriv (Gegenbauer.eFam m) y| ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + π / 2) / 2 →
        |acoeff α m (RemSource α ψ) z| * |iteratedDeriv 2 (Gegenbauer.eFam m) y|
          ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + π / 2) / 2 →
        |acoeff α m (RemSource α ψ) z|
          * |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y| ≤ D * majPow m) := by
  intro z hz θ hθ hθ2
  have hcosθ : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  set θu : ℝ := (θ + π / 2) / 2 with hθu
  -- the `m = 0` mode coefficient vanishes
  have hb0 : bmode 0 ψ = 0 := by
    have hF : Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
      simpa only [Elliptic.Fstar] using hmom
    rw [bmode_eq_cmode 0 ψ 0]
    exact eFam_zero_moment (fun _ θ => ψ θ) hF
  have hac0 : ∀ y : ℝ, acoeff α 0 (RemSource α ψ) y = 0 := by
    intro y
    rw [acoeff_RemSource, hb0]
    ring
  obtain ⟨Cdec, hCdecpos, hDec'⟩ := hDec
  obtain ⟨CBz, hCBzpos, hGamma'⟩ := hGamma
  have hθu_lt : θu < Real.pi / 2 := by rw [hθu]; linarith [hθ2]
  have hcθ : 0 < Real.cos θu :=
    Real.cos_pos_of_mem_Ioo ⟨by rw [hθu]; linarith [Real.pi_pos], hθu_lt⟩
  obtain ⟨D, hDpos, hDsh⟩ :=
    hterm Cdec CBz 1 hCdecpos hCBzpos one_pos (Real.cos θu) hcθ
  -- differentiability of the mode solutions and of their derivatives
  have hdiffA : ∀ m : ℕ,
      (∀ y, 0 < y → HasDerivAt (gammaFun α m) (rgiD1 α m (VocabO.phiA α) y) y) ∧
      (∀ y, 0 < y →
        HasDerivAt (deriv (gammaFun α m)) (deriv (rgiD1 α m (VocabO.phiA α)) y) y) :=
    fun m => hasDerivAt_gammaFun hα m hInt.2.2.2.1 (hInt.2.2.2.2.1 m) (hInt.2.2.2.2.2 m)
  have hderA : ∀ m : ℕ,
      (∀ y, 0 < y → HasDerivAt (acoeff α m (RemSource α ψ))
        (α ^ 2 * bmode m ψ * rgiD1 α m (VocabO.phiA α) y) y) ∧
      (∀ y, 0 < y → HasDerivAt (deriv (acoeff α m (RemSource α ψ)))
        (α ^ 2 * bmode m ψ * deriv (rgiD1 α m (VocabO.phiA α)) y) y) :=
    fun m => hasDerivAt_acoeff m (hdiffA m).1 (hdiffA m).2
  -- the two basic product bounds
  have hbase : ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ y : ℝ, 0 < y →
      |bmode m ψ| * |iteratedDeriv k (gammaFun α m) y|
        ≤ Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
    intro m hm k hk y hy
    exact bound_mul (le_of_lt hCdecpos) (le_of_lt hCBzpos) (lam_pos hm) (sqrt_two_m_pos m)
      (hDec' m hm) (hGamma' m hm k hk y hy)
  have hacc : ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ y : ℝ, 0 < y →
      |iteratedDeriv k (acoeff α m (RemSource α ψ)) y|
        ≤ α ^ 2 * Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
    intro m hm k hk y hy
    have hbase0 := hbase m hm
    interval_cases k
    · have h := hbase0 0 (by norm_num) y hy
      rw [iteratedDeriv_zero] at h
      have habs : |acoeff α m (RemSource α ψ) y|
          = α ^ 2 * (|bmode m ψ| * |gammaFun α m y|) := by
        rw [acoeff_RemSource,
          show ((α ^ 2 * bmode m ψ) * Radial.radGreen α m (VocabO.phiA α) y)
            = α ^ 2 * bmode m ψ * gammaFun α m y from rfl,
          abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        ring
      rw [iteratedDeriv_zero, habs]
      calc α ^ 2 * (|bmode m ψ| * |gammaFun α m y|)
          ≤ α ^ 2 * (Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = α ^ 2 * Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
            ring
    · have h := hbase0 1 (by norm_num) y hy
      rw [iteratedDeriv_one, (hdiffA m).1 y hy |>.deriv] at h
      have habs : |iteratedDeriv 1 (acoeff α m (RemSource α ψ)) y|
          = α ^ 2 * (|bmode m ψ| * |rgiD1 α m (VocabO.phiA α) y|) := by
        rw [iteratedDeriv_one, deriv_acoeff m (hdiffA m).1 y hy, abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        ring
      rw [habs]
      calc α ^ 2 * (|bmode m ψ| * |rgiD1 α m (VocabO.phiA α) y|)
          ≤ α ^ 2 * (Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = α ^ 2 * Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
            ring
    · have h := hbase0 2 (by norm_num) y hy
      rw [iteratedDeriv_two_apply, (hdiffA m).2 y hy |>.deriv] at h
      have habs : |iteratedDeriv 2 (acoeff α m (RemSource α ψ)) y|
          = α ^ 2 * (|bmode m ψ| * |deriv (rgiD1 α m (VocabO.phiA α)) y|) := by
        rw [iteratedDeriv_two_apply, deriv_deriv_acoeff m (hdiffA m).1 (hdiffA m).2 y hy,
          abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        ring
      rw [habs]
      calc α ^ 2 * (|bmode m ψ| * |deriv (rgiD1 α m (VocabO.phiA α)) y|)
          ≤ α ^ 2 * (Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = α ^ 2 * Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
            ring
  -- the four arithmetic shapes of `termEstimates`
  have hshape1 : ∀ m : ℕ, 1 ≤ m →
      α ^ 2 * Cdec * CBz * 1
          / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) * (3 * ((m : ℝ) + 1))
        ≤ D * majPow m := by
    intro m hm
    have h := (hDsh m hm).1
    simpa only [mul_one] using h
  have hshape2 : ∀ m : ℕ, 1 ≤ m →
      α ^ 2 * Cdec * CBz * 1
          / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
          * (900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2) ≤ D * majPow m := by
    intro m hm
    have h := (hDsh m hm).2.1
    simpa only [mul_one] using h
  have hshape3 : ∀ m : ℕ, 1 ≤ m →
      α ^ 2 * Cdec * CBz * 1
          / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
          * (27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4) ≤ D * majPow m := by
    intro m hm
    have h := (hDsh m hm).2.2.1
    simpa only [mul_one] using h
  have hshape4 : ∀ m : ℕ, 1 ≤ m →
      α ^ 2 * Cdec * CBz * 1
          / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
          * (9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3) ≤ D * majPow m := by
    intro m hm
    have h := (hDsh m hm).2.2.2
    simpa only [mul_one] using h
  -- the five pointwise bounds
  have hB0 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |acoeff α m (RemSource α ψ) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hac0 y, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 0 (by norm_num) y hy
      rw [iteratedDeriv_zero] at h1
      calc |acoeff α m (RemSource α ψ) y| * |Gegenbauer.eFam m θ|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (3 * ((m : ℝ) + 1)) := by
            have h2 : |Gegenbauer.eFam m θ|
                ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := (hAng m θ ⟨hθ, hθ2⟩).1
            have h3 := sqrt_mu_le hm
            calc |acoeff α m (RemSource α ψ) y| * |Gegenbauer.eFam m θ|
                ≤ (α ^ 2 * Cdec * CBz
                    / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                    * (3 * ((m : ℝ) + 1)) :=
                  mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
              _ = _ := rfl
        _ ≤ D * majPow m := by
            have h4 := hshape1 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (3 * ((m : ℝ) + 1))
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (3 * ((m : ℝ) + 1)) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB1 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (acoeff α m (RemSource α ψ)) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : deriv (acoeff α 0 (RemSource α ψ)) y = 0 := by
        rw [show acoeff α 0 (RemSource α ψ) = fun _ => (0 : ℝ) from funext hac0]
        simp
      rw [this, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 1 (by norm_num) y hy
      rw [iteratedDeriv_one] at h1
      have h2 : |Gegenbauer.eFam m θ|
          ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := (hAng m θ ⟨hθ, hθ2⟩).1
      have h3 := sqrt_mu_le hm
      calc |deriv (acoeff α m (RemSource α ψ)) y| * |Gegenbauer.eFam m θ|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape1 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (3 * ((m : ℝ) + 1))
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (3 * ((m : ℝ) + 1)) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB2 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (deriv (acoeff α m (RemSource α ψ))) y| * |Gegenbauer.eFam m θ|
        ≤ D * majPow m := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hd : deriv (acoeff α 0 (RemSource α ψ)) = fun _ => (0 : ℝ) := by
        rw [show acoeff α 0 (RemSource α ψ) = fun _ => (0 : ℝ) from funext hac0]
        simp
      have : deriv (deriv (acoeff α 0 (RemSource α ψ))) y = 0 := by rw [hd]; simp
      rw [this, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 2 (by norm_num) y hy
      rw [iteratedDeriv_two_apply] at h1
      have h2 : |Gegenbauer.eFam m θ|
          ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := (hAng m θ ⟨hθ, hθ2⟩).1
      have h3 := sqrt_mu_le hm
      calc |deriv (deriv (acoeff α m (RemSource α ψ))) y| * |Gegenbauer.eFam m θ|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape1 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (3 * ((m : ℝ) + 1))
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (3 * ((m : ℝ) + 1)) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB3 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ θu →
      |acoeff α m (RemSource α ψ) z| * |deriv (Gegenbauer.eFam m) y| ≤ D * majPow m := by
    intro m y hy hyu
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hac0 z, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 0 (by norm_num) z hz
      rw [iteratedDeriv_zero] at h1
      have hcosy : Real.cos θu ≤ Real.cos y := by
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) ?_ hyu
        linarith [Real.pi_pos, hθ2]
      have hcvy : 0 < Real.cos y := lt_of_lt_of_le hcθ hcosy
      have h2 : |deriv (Gegenbauer.eFam m) y|
          ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 2 :=
        (hAng m y ⟨hy, by linarith [hyu, hθu_lt]⟩).2.1
      have h3 : 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 2
          ≤ 900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2 := by
        have hmu := mu_le hm
        have hsq : (Real.cos θu) ^ 2 ≤ (Real.cos y) ^ 2 := by
          exact pow_le_pow_left₀ (le_of_lt hcθ) hcosy 2
        calc 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 2
            ≤ 100 * (9 * ((m : ℝ) + 1) ^ 2) / (Real.cos y) ^ 2 := by
              exact div_le_div_of_nonneg_right (by linarith [hmu]) (by positivity)
          _ = 900 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2 := by ring
          _ ≤ 900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2 := by
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      calc |acoeff α m (RemSource α ψ) z| * |deriv (Gegenbauer.eFam m) y|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape2 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2)
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB4 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ θu →
      |acoeff α m (RemSource α ψ) z| * |iteratedDeriv 2 (Gegenbauer.eFam m) y|
        ≤ D * majPow m := by
    intro m y hy hyu
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hac0 z, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 0 (by norm_num) z hz
      rw [iteratedDeriv_zero] at h1
      have hcosy : Real.cos θu ≤ Real.cos y := by
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) ?_ hyu
        linarith [Real.pi_pos, hθ2]
      have hcvy : 0 < Real.cos y := lt_of_lt_of_le hcθ hcosy
      have h2 : |iteratedDeriv 2 (Gegenbauer.eFam m) y|
          ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
              * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 4 :=
        (hAng m y ⟨hy, by linarith [hyu, hθu_lt]⟩).2.2.1
      have h3 : 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
              * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 4
          ≤ 27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4 := by
        have hmu := mu_mul_sqrt_mu_le hm
        have hsq : (Real.cos θu) ^ 4 ≤ (Real.cos y) ^ 4 := by
          exact pow_le_pow_left₀ (le_of_lt hcθ) hcosy 4
        calc 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
                * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 4
            ≤ 1000 * (27 * ((m : ℝ) + 1) ^ 3) / (Real.cos y) ^ 4 := by
              exact div_le_div_of_nonneg_right (by linarith [hmu]) (by positivity)
          _ = 27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos y) ^ 4 := by ring
          _ ≤ 27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4 := by
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      calc |acoeff α m (RemSource α ψ) z| * |iteratedDeriv 2 (Gegenbauer.eFam m) y|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape3 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4)
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB5 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ θu →
      |acoeff α m (RemSource α ψ) z|
        * |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y| ≤ D * majPow m := by
    intro m y hy hyu
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hac0 z, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 0 (by norm_num) z hz
      rw [iteratedDeriv_zero] at h1
      have hcosy : Real.cos θu ≤ Real.cos y := by
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) ?_ hyu
        linarith [Real.pi_pos, hθ2]
      have hcvy : 0 < Real.cos y := lt_of_lt_of_le hcθ hcosy
      have h2 : |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y|
          ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 3 :=
        (hAng m y ⟨hy, by linarith [hyu, hθu_lt]⟩).2.2.2
      have h3 : 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 3
          ≤ 9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3 := by
        have hmu := mu_le hm
        have hsq : (Real.cos θu) ^ 3 ≤ (Real.cos y) ^ 3 := by
          exact pow_le_pow_left₀ (le_of_lt hcθ) hcosy 3
        calc 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 3
            ≤ 1000 * (9 * ((m : ℝ) + 1) ^ 2) / (Real.cos y) ^ 3 := by
              exact div_le_div_of_nonneg_right (by linarith [hmu]) (by positivity)
          _ = 9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 3 := by ring
          _ ≤ 9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3 := by
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      calc |acoeff α m (RemSource α ψ) z|
            * |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape4 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3)
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  exact ⟨D, hDpos, hB0, hB1, hB2, hB3, hB4, hB5⟩

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.EnergyStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice)
open Work.Coercivity (HkIPStep H1IP wip LGammaT)
open Work.Spaces (Dz Dth mixed)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The energy-derivative predicate -/



/-! ## The base case: the four `wip`-level facts of `H1IP` -/







end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.NZaux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Linearity of `L₁₂` over `F_* + f` at level `ℋ⁴`.**

`Work.Construction.L12 g z = ∫_z^∞ ∫_0^{π/2} K(θ) g(s,θ)/s dθ ds` is an integral, so it is
additive in the profile; unconditionally the Bochner integral is additive only on integrable
functions, so the proof spends the honesty of the datum (`SmoothOpen f`, `HkMem α 4 f`) to
produce the four integrability certificates required by `Work.FTS.LocData.L12_add_mul`:

* the angular slice of the reference profile, `θ ↦ K θ F_*(s,θ)/s`, continuous on the compact
  `Iθ` (`Work.Stability.integrableOn_slice_Fstar`);
* the angular slice of `f`, `θ ↦ K θ f(s,θ)/s`, for `s > z > 0`
  (`Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`);
* the two densities on `(z,∞)`: that of `F_*` is the elementary `α·2/(1+s)²`
  (`Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn`), and that of `f`
  (`Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem`), restricted from `(0,∞)`
  to `(z,∞)`.

No boundary behaviour of `f` is used: the statement is a purely measure-theoretic consequence
of `SmoothOpen` and `HkMem α 4`. -/
theorem L12AddFstar {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z : ℝ, 0 < z → Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z := by
  intro z hz
  have hslice_f : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
    fun s hs =>
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hso hmem
        (lt_of_lt_of_le hz hs.le)
  have hdens_f : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hso hmem).mono_set
      (fun s hs => lt_of_lt_of_le hz hs.le)
  exact (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
    (a := Work.Construction.Fstar α) (b := f)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s)
    hslice_f
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz.le)
    hdens_f).1

end Work.FTS.StrongPersist.H6Rows.NZaux
end
