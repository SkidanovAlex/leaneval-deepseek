import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.mom2Summable
import Submission.Work.BoseBoxFock.tauDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauC0Facts` — the `c₀`-bound and the `c₀`-free envelope of the profile

The target `Work.BoseBoxFock.tauLattice_le_tauContinuumChi` involves the *opaque* profile
`tauProf = tauProf`, so every proof may use only the six recorded
properties

(P1) `ContDiff ℝ ⊤`;  (P2) `Monotone`;  (P3) `(max 0 (r−2))² ≤ φ r`;
(P4) `φ r ≤ (max 0 (r−1))²`;  (P5) `φ r = 0` for `r ≤ 1`;
(P6) `∃ c₀ ≥ 0, ∀ r ≥ 2, φ r = (r−3/2)² + c₀`.

This module records the two *sharp* consequences of (P1)–(P6) that the deficit reduction needs:

* `tauC0_le_three_quarters` — the recorded constant satisfies `c₀ ≤ 3/4`
  (apply (P4) at `r = 2` to (P6): `1/4 + c₀ ≤ 1`).  This is the *only* upper bound on `c₀`
  available: the admissible set of constants is exactly `[0, 3/4)` (for every `c₀ < 3/4` there is
  a `C^∞` monotone profile with those six properties — glue the quadratic tail `(r−3/2)²+c₀`
  to `0` below `r = 1` with a flat contact at `1.25+c₀` and a flat contact at `2`), so a proof of
  the target must work with `c₀` arbitrarily close to `3/4`.

* `tauProf_le_tauEnvWorst` — the pointwise envelope
  `tauEnvWorst s = 0` (`s ≤ 1`), `min ((s−1)²) 1` (`1 < s < 2`), `(s−3/2)² + 3/4` (`2 ≤ s`),
  valid for *every* admissible profile.  It is the pointwise-optimal envelope compatible with
  (P2), (P4), (P5), (P6) and `c₀ ≤ 3/4`, whence the `c₀`-free form of the deficit
  `tauDeltaWorst` used by the reduction in the target file.

`tauLatZero_le_tauLatPow_zero` (`a₀ ≤ S₀`) is the elementary comparison used to pass from the
`c₀ = 3/4` deficit to the deficit of the actual (unknown) `c₀`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The `c₀`-free upper envelope of every admissible profile**:
`0` on `(−∞,1]`, `min ((s−1)²) 1` on `(1,2)`, `(s−3/2)²+3/4` on `[2,∞)`. -/
noncomputable def tauEnvWorst (s : ℝ) : ℝ :=
  if s ≤ 1 then 0 else if s < 2 then min ((s - 1) ^ 2) 1 else (s - 3 / 2) ^ 2 + 3 / 4

/-- (P4) for the chosen profile `tauProf`. -/
lemma tauProf_le_max_sq (s : ℝ) : tauProf s ≤ (max 0 (s - 1)) ^ 2 :=
  tauProf_spec.2.2.2.1 s

/-- (P5) for the chosen profile. -/
lemma tauProf_eq_zero_of_le_one {s : ℝ} (hs : s ≤ 1) : tauProf s = 0 :=
  tauProf_spec.2.2.2.2.1 s hs

/-- (P2) for the chosen profile. -/
lemma tauProf_mono : Monotone tauProf :=
  tauProf_spec.2.1

/-- **The constant of the chosen profile satisfies `c₀ ≤ 3/4`.**  (P4) at `r = 2` together with
(P6) gives `1/4 + c₀ ≤ 1`. -/
theorem tauC0_le_three_quarters : tauC0 ≤ 3 / 4 := by
  have h4 := tauProf_le_max_sq 2
  have h6 : tauProf 2 = (2 - 3 / 2) ^ 2 + tauC0 := tauProf_quad le_rfl
  rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 2 - 1)] at h4
  rw [h6] at h4
  linarith

/-- **The envelope**: the chosen profile is pointwise below `tauEnvWorst`. -/
theorem tauProf_le_tauEnvWorst (s : ℝ) : tauProf s ≤ tauEnvWorst s := by
  by_cases h1 : s ≤ 1
  · rw [tauEnvWorst, if_pos h1, tauProf_eq_zero_of_le_one h1]
  · rw [tauEnvWorst, if_neg h1]
    by_cases h2 : s < 2
    · rw [if_pos h2]
      refine le_min ?_ ?_
      · have h := tauProf_le_max_sq s
        rwa [max_eq_right (by linarith : (0 : ℝ) ≤ s - 1)] at h
      · have h := tauProf_mono (le_of_lt h2)
        rw [tauProf_quad le_rfl] at h
        linarith [tauC0_le_three_quarters]
    · rw [if_neg h2]
      rw [tauProf_quad (not_lt.mp h2)]
      linarith [tauC0_le_three_quarters]

/-- **`a₀ ≤ S₀`**: the `n = 0` term of the lattice moment `S₀` is dominated by the whole sum
(summability is `mom2Summable`, the frame identity for the box). -/
theorem tauLatZero_le_tauLatPow_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hsupp : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    tauLatZero ℓ g ≤ tauLatPow ℓ 0 g := by
  have hsum := mom2Summable hℓ hg hgc hsupp
  rw [tauLatPow_zero, tauLatZero]
  have hm : kmomInt ℓ (0 : Fin 3 → ℤ) = 0 := by
    show ℓ⁻¹ • Work.BoseB4.vec 0 = 0
    rw [show Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 by ext i; simp [Work.BoseB4.vec],
      smul_zero]
  have hle := hsum.sum_le_tsum ({0} : Finset (Fin 3 → ℤ)) (fun i _ => by positivity)
  rw [Finset.sum_singleton] at hle
  simpa only [hm] using hle

/-! ## The extra structure of the *explicit* profile `tauPhi`

The following two facts hold for the explicit smoothing `tauPhi : ℝ → ℝ` of `TauProf.lean` — but
**not** for the opaque `tauProf`: they are *not* consequences of (P1)–(P6), they need the kernel
representation `tauPhi s = ∫ (max 0 (s − 3/2 − t))² K(t) dt` with `K ≥ 0`, `∫K = 1`, `∫tK = 0`.
They are the two facts that make the *intended* (restated, `tauPhi`-based) form of the target
strictly easier than the opaque one: `τ̃` stays below its quadratic tail, so the deficit `δ_c` of
`tauDefs` is a *credit* (`δ_c ≥ 0`). -/

/-- **The explicit profile is below its quadratic tail**: `tauPhi r ≤ (r−3/2)² + ∫t² tauKer`. -/
theorem tauPhi_le_quad (r : ℝ) :
    tauPhi r ≤ (r - 3 / 2) ^ 2 + ∫ t, t ^ 2 * tauKer t := by
  rw [tauPhi_eq_integral]
  have hpt : ∀ t : ℝ, tauH (r - 3 / 2 - t) * tauKer t ≤ (r - 3 / 2 - t) ^ 2 * tauKer t := by
    intro t
    rcases eq_or_ne (tauKer t) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    · refine mul_le_mul_of_nonneg_right ?_ (tauKer_nonneg t)
      have h1 : (0 : ℝ) ≤ max 0 (r - 3 / 2 - t) := le_max_left _ _
      have h2 : max 0 (r - 3 / 2 - t) ≤ |r - 3 / 2 - t| :=
        max_le (abs_nonneg _) (le_abs_self _)
      have h3 := pow_le_pow_left₀ h1 h2 2
      simpa [tauH, sq_abs] using h3
  have hInt1 : Integrable (fun t => tauH (r - 3 / 2 - t) * tauKer t) volume :=
    tauKer_mul_integrable _ (tauH_continuous.comp (by fun_prop))
  have hInt2 : Integrable (fun t => (r - 3 / 2 - t) ^ 2 * tauKer t) volume :=
    tauKer_mul_integrable _ (by fun_prop)
  calc ∫ t, tauH (r - 3 / 2 - t) * tauKer t
      ≤ ∫ t, (r - 3 / 2 - t) ^ 2 * tauKer t := integral_mono hInt1 hInt2 hpt
    _ = (r - 3 / 2) ^ 2 + ∫ t, t ^ 2 * tauKer t := by
        rw [integral_sq_sub_mul, tauKer_integral, tauKer_moment1]
        ring

/-- **For the explicit profile the deficit `δ_c` is a credit** (`δ_c ≥ 0`). -/
theorem tauDelta_phi_nonneg {c r : ℝ} (hc : 0 < c) :
    0 ≤ r ^ 2 - 3 * c * r + (9 / 4 + ∫ t, t ^ 2 * tauKer t) * c ^ 2
      - c ^ 2 * tauPhi (r / c) := by
  have h := tauPhi_le_quad (r / c)
  have hmul : c ^ 2 * tauPhi (r / c)
      ≤ c ^ 2 * ((r / c - 3 / 2) ^ 2 + ∫ t, t ^ 2 * tauKer t) :=
    mul_le_mul_of_nonneg_left h (sq_nonneg c)
  have hexp : c ^ 2 * ((r / c - 3 / 2) ^ 2 + ∫ t, t ^ 2 * tauKer t)
      = (r - 3 * c / 2) ^ 2 + c ^ 2 * ∫ t, t ^ 2 * tauKer t := by
    field_simp
  rw [hexp] at hmul
  nlinarith [hmul, sq_nonneg (r - 3 * c / 2)]

end Work.BoseBoxFock
