import Mathlib
import Submission.Work.FIArea6T.Defs
import Submission.Work.FIArea6T.CleanMoll
import Submission.Work.FIArea7.deltaTau_mass_le

namespace Work.FIArea6T

/-- **T4 — the mass of the (5.9)-complement of a clean coefficient (Rankin, area 7's A3).**

For `Pa.τ = tauOf Pa.x Asave = (log x)^{201048576}` (the round-6 pin, recorded for every far piece
in `FIRed6Axis/Statement.lean`), the (5.9)-complement `β − tauCut Pa β = tauCompl Pa β` of a clean
coefficient has `L²`-mass at most `N (log N)^{-4·10^9}` over the inner box.

Route (the only arithmetic input is *FI* (10.4) done by Rankin's trick, area 7's A3):
* `Work.FIArea6T.clean_eq_betaTilde` gives `q, p` with `Work.FIArea7.IsMollPair Pa q p` such that
  the clean coefficient is `1[(5.14) ∧ (5.8) ∧ (5.7)] · Work.FIArea7.betaTilde Pa q p φ z0`, the
  area-7 coefficient of (17.15);
* `Work.FIArea7.deltaTau_mass_le` bounds `Σ_{gBox (radN Pa)} ‖betaTilde Pa q p φ z0 z · 1[τ>τ]‖²`
  by `Pa.N * (log Pa.N)^{-(4*10^9)}` for large `x` — take the maximum of its threshold with the
  threshold needed to identify the two boxes;
* pointwise, `Work.FIArea6T.tauCompl_eq_mul` gives
  `β z − tauCut Pa β z = β z · 1[τ(gnorm z) > Pa.τ]`, and `‖β z · 1[τ>τ]‖ ≤
  ‖betaTilde Pa q p φ z0 z · 1[τ>τ]‖`: on the support `(5.14) ∧ (5.8) ∧ (5.7)` the two coefficient
  formulas agree (`InPolarBox` carries the primarity that `radBeta` requires), and off the support
  `β z = 0`.

Suggested namespace: `Work.FIArea6T`. -/
theorem cleanTau_mass_le :
    ∃ x0 : ℝ, ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      x0 ≤ (Pa.x : ℝ) → Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave →
      Work.FITop4.IsCleanCoeff6 Pa φ z0 β →
      ∑ z ∈ Work.FITop.boxN Pa, ‖β z - Work.FITop4.tauCut Pa β z‖ ^ 2
        ≤ Pa.N * (Real.log Pa.N) ^ (-(4 * 10 ^ 9 : ℝ)) := by
  -- The Rankin mass bound of area 7 (`FI` (10.4) at power `25`), for the inner box.
  obtain ⟨x0, hx0⟩ := Work.FIArea7.deltaTau_mass_le
  refine ⟨x0, ?_⟩
  intro Pa φ z0 β hx htau hβ
  -- The clean coefficient is `1[(5.14) ∧ (5.8) ∧ (5.7)] · betaTilde` (area 7's (17.15) coefficient).
  obtain ⟨q, p, hmoll, hform⟩ := Work.FIArea6T.clean_eq_betaTilde hβ
  -- Pointwise: the (5.9)-complement of `β` is dominated by the area-7 complement of `betaTilde`.
  have hpt : ∀ z : GaussianInt,
      ‖β z - Work.FITop4.tauCut Pa β z‖
        ≤ ‖Work.FIArea7.betaTilde Pa q p φ z0 z
            * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1)‖ := by
    intro z
    have hdelta : β z - Work.FITop4.tauCut Pa β z
        = β z * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1) :=
      Work.FIArea6T.tauCompl_eq_mul Pa β z
    rw [hdelta, hform z]
    by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
        ∧ Work.FITop4.SameClass8 z z0
    · simp [if_pos hc]
    · simp [if_neg hc]
  -- Sum comparison over the identical inner box `boxN Pa = gBox (radN Pa)`.
  refine le_trans ?_ (hx0 Pa q p φ z0 hx htau hmoll)
  have hbox : Work.FITop.boxN Pa = Work.FIPlan.gBox (Work.FITop.radN Pa) := rfl
  rw [hbox]
  exact Finset.sum_le_sum (fun z _ => pow_le_pow_left₀ (norm_nonneg _) (hpt z) 2)

end Work.FIArea6T
