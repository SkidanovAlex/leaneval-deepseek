/-
# `FTS/ClassCHon/CmodeIter` — the iteration of the `θ`-pairing and its assembly

This module contains the *non-delegated* half of the rapid-decay argument:

* `setIntegral_Iθ_eq_intervalIntegral` — the set integral over `Iθ = [0, π/2]` is the interval
  integral over `0..π/2`;
* `pair_Lzero1_eFam` — the self-adjointness pairing
  `∫ (Lzero1 u) e_m cos = lam m · ∫ u e_m cos`, deduced from the existing
  `Work.FTS.PhiStar.Series.Deleg.lzero1_pair_eFam`;
* `cmode_iter` — the iteration `∫ g e_m cos = (lam m)^{-k} ∫ (Lzero1^k g) e_m cos`.

The remaining ingredients — that the iterates `Lop g k` are again `C^∞` and supported in
`[a,b]` (`Lop_good`), and that the moment of a `C^∞` function supported in `[a,b]` against
`eFam m · cos` is `O(m)` (`mode_moment_bound`) — are the sibling modules.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.PhiStar.Series.Deleg.lzero1_pair_eFam

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
