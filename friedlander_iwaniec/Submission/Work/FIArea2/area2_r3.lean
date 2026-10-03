import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm

/-! Guidance from the project lead (the requester):

You own AREA 2 of Friedlander–Iwaniec Proposition 4.1: *FI* §§6–9 (lattice points in the biquadratic ellipse: 2-dim Poisson, Lemmas 7.1/7.2 incl. the elliptic-integral asymptotics (7.9), §8 Weyl sum and (8.16), §9 aggregate).
Contract: `Work.FITop3.Area2` in `Submission/Work/FITop3/Areas3.lean` (FROZEN round 3; never edit it, nor Defs3.lean or FITop/Defs.lean). Read its doc string
(satisfiability, non-vacuity, degenerate cases), `Submission/Work/FITop/NOTES.md` (§2 has the per-area size estimate and internal
plan), and `Submission/Work/FIPlan/PLAN.md` (§2 section map, §3 external inputs, §5 risks R-1..R-15). Paper: `REFS/FI_paper_X2Y4.pdf`
(`pdftotext -layout -f A -l B` for clean text). NO Weil bound is needed anywhere (p. 952); the only character-sum input is
Pólya–Vinogradov. The areas are independent: you may use ONLY your own statement's hypotheses, never another area's open lemma.
If you find the frozen statement false, give a precise counterexample and declare_false; do not prove something else.
Work under `Submission/Work/FIArea2/`, namespace `Work.FIArea2`. Delegate aggressively: sub-lemmas with exact statements.
ROUND 3 NOTES: read Submission/Work/FITop3/NOTES.md (defect→fix list; per-area non-vacuity §6) and FITop/NOTES.md §2 (per-area plans).
Round 2 of this contract was refereed FALSE/vacuous by the first area wave (unsatisfiable IsMajorant, a free fhat, d = 0, an
IsBetaCoeff too weak for Möbius cancellation, and a √N normalisation error in D0). Round 3 fixes those, with Lean-proved satisfiability
(`hyp_satisfiable`, `Area4_hyp_satisfiable`, `Area5_hyp_satisfiable`). If you still find it false, prove the counterexample in Lean.
Earlier attempts left helpers under Submission/Work/FIArea<i>/: reuse what fits.

# Status of this file (round 3, session 2)

`Work.FITop3.Area2` is *FI*'s (9.10), i.e. §§6–9 themselves.  The report is `NOTES.md` (§2: the
statement is the paper's (9.10), numerics re-checked; §3: it is true, but its proof is the
Poisson/Weyl-sum engine of §§6–9; §4: the faithfulness gaps; **§1–§6 of the session-2 part: the
machine-checked defect of the frozen kernel `G₀`, the corrected (8.16), and the recommended
round-5 changes**).

Proved here is the elementary base of §6 on which the rest of the area stands: the
`Z`/`gnorm`/`Zc` API, the non-degeneracy of `Δ` for the pairs that occur (6.1)/(6.2), the exact
parametrisation `Re(wz₁)·z₂ − Re(wz₂)·z₁ = Δ(z₁,z₂)·ī·w̄` of (6.3) together with its congruence
form (6.4), the `D*`-vs-square decomposition (the diagonal/coprimality bookkeeping of
(5.21)/(5.26)), and — session 2 — **the interchange of (5.26) with (9.1)**
(`Ccount`, `Dstar_eq_pairSum`, `Dstar_sub_D0_eq_pairSum`), which rewrites the frozen `D* − D₀` as
the `β_{z₁}β̄_{z₂}`-weighted sum of the per-pair errors `C(z₁,z₂) − C₀(z₁,z₂)`.

Session-2 companion modules (all sorry-free, axiom-clean):

* `G0_defect.lean` — the machine-checked witness that the frozen `Work.FIPlan.G0` is *not* *FI*'s
  `G₀` (it omits the reduction (6.6) of `z₂/z₁`);
* `G0_fix.lean` — the repaired kernel `G0fix` (= the count (6.12)/`|Δ|`), `C0fix`, `D0fix`,
  `Cnt_eq_two_sum`/`G0fix_eq_two_sum` (**the corrected (8.16)**, proved from `Cnt_eq_Nsol` +
  `Nsol_eq_two_sum_jacobi`);
* `absDelta_lt_four_pi.lean` — (6.2) `|Δ| < 4πθN` for the polar box;
* `sum_tau_pow_le.lean`, `sum_tau_pow_div_le.lean`, `ladder_tau_gcd.lean`,
  `sum_gcd_tau_lcm_le.lean` — the §9 divisor-sum machinery ((9.7) to (9.10));
* `Cnt_eq_Nsol.lean`, `Nsol_eq_two_sum_jacobi.lean` — (6.4)–(6.6) and (8.16);
* `coprime_gnorm_absDelta.lean`, `coprime_re_absDelta.lean`, `coprime_residue_absDelta.lean`,
  `a_mod_eight.lean`, `eight_dvd_absDelta_of_congr.lean` — the automatic side conditions of the
  corrected (8.16) (the paper's (5.7)/(5.8) consequences).
-/

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The square indicator `Z` of (5.2) and the theta coefficient `Zc` -/

theorem Zint_nonneg (b : ℤ) : 0 ≤ Work.FIPlan.Zint b := Nat.zero_le _

/-- `Z(b) ≤ 2`: `1` at `b = 0`, `2` at the non-zero squares (two roots), `0` otherwise. -/
theorem Zint_le_two (b : ℤ) : Work.FIPlan.Zint b ≤ 2 := by
  unfold Work.FIPlan.Zint Work.FIPlan.Zb
  split_ifs <;> omega

/-- `Z(0) = 1`: the paper's `Z` counts the roots of `c² = b`, and `c = 0` is one. -/
theorem Zint_zero : Work.FIPlan.Zint 0 = 1 := by
  unfold Work.FIPlan.Zint Work.FIPlan.Zb
  simp

/-- `Z` is a non-negative real number, as a complex number. -/
theorem Zc_eq_ofReal (w z : GaussianInt) :
    Work.FITop3.Zc w z = ((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℂ) := by
  rw [Work.FITop3.Zc]

theorem Zc_im (w z : GaussianInt) : (Work.FITop3.Zc w z).im = 0 := by
  simp [Work.FITop3.Zc]

theorem Zc_re (w z : GaussianInt) :
    (Work.FITop3.Zc w z).re = (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
  simp [Work.FITop3.Zc]

theorem Zc_re_nonneg (w z : GaussianInt) : 0 ≤ (Work.FITop3.Zc w z).re := by
  rw [Zc_re]; positivity

theorem Zc_normSq (w z : GaussianInt) :
    Complex.normSq (Work.FITop3.Zc w z)
      = ((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℝ) ^ 2 := by
  rw [Work.FITop3.Zc, Complex.normSq_natCast, sq]

/-! ## 2. The norm `gnorm z = |z|²` -/

theorem gnorm_zero : Work.FIPlan.gnorm (0 : GaussianInt) = 0 := by
  simp [Work.FIPlan.gnorm]

theorem gnorm_one : Work.FIPlan.gnorm (1 : GaussianInt) = 1 := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm]

/-- `|zw|² = |z|²|w|²`. -/
theorem gnorm_mul (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

theorem gnorm_eq_zero_iff (z : GaussianInt) : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  rw [Work.FIPlan.gnorm, Int.natAbs_eq_zero]
  exact Zsqrtd.norm_eq_zero (by intro n hn; have : 0 ≤ n * n := mul_self_nonneg n; omega) z

theorem gnorm_pos {z : GaussianInt} (hz : z ≠ 0) : 0 < Work.FIPlan.gnorm z :=
  Nat.pos_of_ne_zero fun h => hz ((gnorm_eq_zero_iff z).mp h)

theorem gnorm_conj (z : GaussianInt) : Work.FIPlan.gnorm (star z) = Work.FIPlan.gnorm z := by
  rw [Work.FIPlan.gnorm, Work.FIPlan.gnorm, Zsqrtd.norm_def, Zsqrtd.norm_def]
  cases z with
  | mk x y => simp [Zsqrtd.star_mk]

/-- A Gaussian integer of norm `1` is a unit. -/
theorem isUnit_of_gnorm_eq_one {z : GaussianInt} (h : Work.FIPlan.gnorm z = 1) : IsUnit z :=
  Zsqrtd.norm_eq_one_iff.mp h

/-- A non-zero non-unit has norm `≥ 2`; this is how `N < |z|²` excludes the degenerate pairs of
(6.1). -/
theorem two_le_gnorm_of_ne_zero_of_not_isUnit {z : GaussianInt} (hz : z ≠ 0)
    (hu : ¬ IsUnit z) : 2 ≤ Work.FIPlan.gnorm z := by
  rcases Nat.lt_or_ge (Work.FIPlan.gnorm z) 2 with h | h
  · interval_cases h' : Work.FIPlan.gnorm z
    · exact absurd ((gnorm_eq_zero_iff z).mp h') hz
    · exact absurd (isUnit_of_gnorm_eq_one h' : IsUnit z) hu
  · exact h

/-! ## 3. The determinant `Δ(z₁,z₂) = Im(z̄₁z₂)` of (6.1) -/

/-- `Δ` in coordinates: `r₁s₂ − r₂s₁`. -/
theorem Delta_def (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z2.re * z1.im := by
  simp [Work.FIPlan.Delta]
  ring

/-- `Δ = 0` means `z̄₁z₂ = z₁z̄₂`, i.e. `z₂/z₁` is real. -/
theorem star_mul_eq_of_Delta_eq_zero {z1 z2 : GaussianInt}
    (h : Work.FIPlan.Delta z1 z2 = 0) : star z1 * z2 = z1 * star z2 := by
  have him : z1.re * z2.im + -(z1.im * z2.re) = 0 := by
    simpa [Work.FIPlan.Delta, Zsqrtd.star_mk] using h
  ext <;> simp <;> linarith

/-- With `(z₁,z₂) = 1`, `Δ = 0` forces `z₁ ∣ z̄₁` and `z₂ ∣ z̄₂` (the paper's step from (6.1) to
"(z₁,z₂) = (z₁,z̄₁) = (z₂,z̄₂) = 1 implies `Δ` does not vanish"). -/
theorem dvd_star_of_Delta_eq_zero {z1 z2 : GaussianInt} (h : Work.FIPlan.Delta z1 z2 = 0)
    (h12 : IsCoprime z1 z2) : z1 ∣ star z1 ∧ z2 ∣ star z2 := by
  have h' := star_mul_eq_of_Delta_eq_zero h
  have h1 : z1 ∣ z2 * star z1 := ⟨star z2, by rw [mul_comm z2 (star z1), h']⟩
  have h2 : z2 ∣ z1 * star z2 := ⟨star z1, by rw [← h', mul_comm (star z1) z2]⟩
  exact ⟨h12.dvd_of_dvd_mul_left h1, h12.symm.dvd_of_dvd_mul_left h2⟩

/-- **(*FI* (6.1))**: for a coprime pair of primitive Gaussian integers, `Δ` vanishes only if both
are units. -/
theorem isUnit_of_Delta_eq_zero {z1 z2 : GaussianInt} (h : Work.FIPlan.Delta z1 z2 = 0)
    (h12 : IsCoprime z1 z2) (h1 : IsCoprime z1 (star z1)) (h2 : IsCoprime z2 (star z2)) :
    IsUnit z1 ∧ IsUnit z2 := by
  obtain ⟨hd1, hd2⟩ := dvd_star_of_Delta_eq_zero h h12
  exact ⟨h1.isUnit_of_dvd hd1, h2.isUnit_of_dvd hd2⟩

/-- **(*FI* (6.1)/(6.2))**: on the pairs that actually occur in `D*`/`D₀` — coprime, primitive,
of norm `≥ 2` (as are all points of the polar box (5.14)) — the determinant `Δ` does not vanish, so
every occurrence of `Δ` in a denominator in §§6–9 is legitimate. -/
theorem Delta_ne_zero_of_coprime {z1 z2 : GaussianInt} (h12 : IsCoprime z1 z2)
    (h1 : IsCoprime z1 (star z1)) (h2 : IsCoprime z2 (star z2))
    (hn1 : 2 ≤ Work.FIPlan.gnorm z1) : Work.FIPlan.Delta z1 z2 ≠ 0 := by
  intro hΔ
  obtain ⟨hu1, _⟩ := isUnit_of_Delta_eq_zero hΔ h12 h1 h2
  obtain ⟨u, hu⟩ := hu1
  have hgn : Work.FIPlan.gnorm z1 = 1 := by
    rw [← hu]
    exact Zsqrtd.norm_eq_one_iff.mpr u.isUnit
  omega

/-- **(*FI* (6.3))**: the values `Re(wz₁)`, `Re(wz₂)` determine `w`: with `c_i² = Re(wz_i)`,
`c₁²z₂ − c₂²z₁ = Δ(z₁,z₂)·ī·w̄`.  (The paper writes the conjugated form, which determines `w`
because `w ↦ w̄` is involutive and `|w̄| = |w|`.) -/
theorem cForm_parametric (w z1 z2 : GaussianInt) :
    (Work.FIPlan.cForm w z1 : GaussianInt) * z2 - (Work.FIPlan.cForm w z2 : GaussianInt) * z1
      = (Work.FIPlan.Delta z1 z2 : GaussianInt) * star w * ⟨(0 : ℤ), (1 : ℤ)⟩ := by
  ext <;> simp [Work.FIPlan.cForm, Work.FIPlan.Delta, Zsqrtd.star_mk] <;> ring

/-- The same identity in the form of (6.3): if `c₁² = Re(wz₁)` and `c₂² = Re(wz₂)` for integers
`c₁, c₂`, then `c₁²z₂ − c₂²z₁ = Δ·ī·w̄`. -/
theorem cForm_parametric_sq {w z1 z2 : GaussianInt} {c1 c2 : ℤ}
    (h1 : Work.FIPlan.cForm w z1 = c1 * c1) (h2 : Work.FIPlan.cForm w z2 = c2 * c2) :
    (c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1
      = (Work.FIPlan.Delta z1 z2 : GaussianInt) * star w * ⟨(0 : ℤ), (1 : ℤ)⟩ := by
  have h := cForm_parametric w z1 z2
  rw [h1, h2] at h
  simpa [sq] using h

/-- **(6.4)/(6.5), the congruence form, forward direction**: if `w` realises the two squares
`c₁² = Re(wz₁)`, `c₂² = Re(wz₂)`, then `Δ(z₁,z₂)` divides `c₁²z₂ − c₂²z₁` in `ℤ[i]` — i.e.
`c₁²z₂ ≡ c₂²z₁ (mod |Δ|)`, the congruence that (6.7) sums over and that §8 evaluates (this is
where the modulus `|Δ|` of the Weyl sum (6.10) comes from). -/
theorem Delta_dvd_of_cForm_eq_sq {w z1 z2 : GaussianInt} {c1 c2 : ℤ}
    (h1 : Work.FIPlan.cForm w z1 = c1 * c1) (h2 : Work.FIPlan.cForm w z2 = c2 * c2) :
    (Work.FIPlan.Delta z1 z2 : GaussianInt)
      ∣ (c1 : GaussianInt) ^ 2 * z2 - (c2 : GaussianInt) ^ 2 * z1 :=
  ⟨star w * ⟨(0 : ℤ), (1 : ℤ)⟩, by rw [cForm_parametric_sq h1 h2, mul_assoc]⟩

/-- The diagonal pair is `(z,z)`; `(z,z) = 1` holds only for units, so the diagonal of the squared
form (5.21) is *removed* by the coprimality restriction unless `z` is a unit — the structural
reason why `D*` is not a sum of squares but a difference (see `Dstar_eq_square_sub`). -/
theorem gaussCoprime_self_iff (z : GaussianInt) : Work.FIPlan.GaussCoprime z z ↔ IsUnit z :=
  isCoprime_self

/-- With `Δ ≠ 0` the two values `Re(wz₁)`, `Re(wz₂)` determine `w`: this is the injectivity that
makes the residue-class summation of (6.7)/(6.8) a genuine re-parametrisation of the `w`-sum. -/
theorem cForm_pair_injective {z1 z2 : GaussianInt} (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    Function.Injective fun w : GaussianInt => (Work.FIPlan.cForm w z1, Work.FIPlan.cForm w z2) := by
  intro w w' h
  have h1 : Work.FIPlan.cForm w z1 = Work.FIPlan.cForm w' z1 := by
    simpa using congrArg Prod.fst h
  have h2 : Work.FIPlan.cForm w z2 = Work.FIPlan.cForm w' z2 := by
    simpa using congrArg Prod.snd h
  have e1 := cForm_parametric w z1 z2
  have e2 := cForm_parametric w' z1 z2
  rw [h1, h2] at e1
  have key : (Work.FIPlan.Delta z1 z2 : GaussianInt) * star w * ⟨(0 : ℤ), (1 : ℤ)⟩
      = (Work.FIPlan.Delta z1 z2 : GaussianInt) * star w' * ⟨(0 : ℤ), (1 : ℤ)⟩ := by
    rw [← e1, ← e2]
  have hi : (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ≠ 0 := by
    intro hc
    have := congrArg Zsqrtd.im hc
    simpa using this
  have hD : (Work.FIPlan.Delta z1 z2 : GaussianInt) ≠ 0 := fun hc => hΔ (by exact_mod_cast hc)
  have hst : star w = star w' := mul_left_cancel₀ hD (mul_right_cancel₀ hi key)
  simpa using congrArg star hst

/-! ## 4. The `D*`-versus-square decomposition of (5.21)/(5.26) -/

/-- The inner `z`-sum of (5.18) at a fixed `w`: `S_w = Σ_z β_z Z(Re wz)`. -/
def Sw (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (w : GaussianInt) : ℂ :=
  ∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z

/-- The **non-coprime ordered-pair part** of the square `|S_w|²` — exactly the pairs that (5.21)
removes when it inserts the condition `(z₁,z₂) = 1`. -/
def NonCoprimePart (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (w : GaussianInt) : ℝ :=
  (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.GaussCoprime z1 z2 then 0 else
      (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2))).re

/-- Dropping the coprimality constraint in (5.21) gives the square `|S_w|²`. -/
theorem normSq_Sw (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (w : GaussianInt) :
    Complex.normSq (Sw Pa β w)
      = (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2)).re := by
  have h1 : Complex.normSq (Sw Pa β w) = (Sw Pa β w * star (Sw Pa β w)).re := by
    rw [Complex.star_def, Complex.mul_conj]
    rfl
  have h2 : star (Sw Pa β w)
      = ∑ z ∈ Work.FITop.boxN Pa, star (β z * Work.FITop3.Zc w z) := by
    rw [Complex.star_def]
    exact map_sum (starRingEnd ℂ) _ _
  rw [h1, h2]
  unfold Sw
  rw [Finset.sum_mul_sum]

/-- **The `D*`-versus-square decomposition (5.21)/(5.26)**: `D*` is the mean square of `S_w` minus
the non-coprime pairs.  Since the diagonal `z₁ = z₂` is *not* coprime unless `z` is a unit
(`gaussCoprime_self_iff`), `D*` is a *difference* of two sums of the same order — the structure
that §9 exploits ("lacunarity") and that makes §9 an estimate of a difference rather than of a sum
of squares. -/
theorem Dstar_eq_square_sub (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    Work.FITop3.Dstar Pa f β
      = (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * Complex.normSq (Sw Pa β w))
        - ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * NonCoprimePart Pa β w := by
  unfold Work.FITop3.Dstar NonCoprimePart
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcomp : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        ((if Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0))).re
      = (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2)).re
        - (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if Work.FIPlan.GaussCoprime z1 z2 then 0 else
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2))).re := by
    rw [← Complex.sub_re, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun z1 _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z2 _ => ?_
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [hc]
  rw [hcomp, normSq_Sw]
  ring

/-! ## 5. Primary points, the polar box (5.14), and the support of the coefficient (4.13) -/

/-- A primary Gaussian integer has **odd norm** (its real part is odd and its imaginary part even,
so `r² + s²` is odd).  This is the paper's "(5.2)… Since `n` is odd so is `z`", and together with
`IsBetaCoeff.squarefree_gnorm` it supplies the hypotheses of
`isCoprime_star_of_squarefree_odd_gnorm`. -/
theorem IsPrimary.odd_gnorm {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  obtain ⟨h1, h2, -⟩ := h
  have hgn : Work.FIPlan.gnorm z = (z.re ^ 2 + z.im ^ 2).natAbs := by
    simp [Work.FIPlan.gnorm, Zsqrtd.norm_def, sq]
  rw [hgn]
  have h2' : Even (z.im ^ 2) := by
    obtain ⟨r, hr⟩ := h2
    exact ⟨2 * r ^ 2, by rw [hr]; ring⟩
  exact (h1.pow.add_even h2').natAbs

theorem InPolarBox.norm_bounds {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (h : Work.FITop3.InPolarBox Pa φ z) :
    Pa.N < (Work.FIPlan.gnorm z : ℝ) ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N :=
  ⟨h.2.1, h.2.2.1⟩

theorem InPolarBox.isPrimary {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (h : Work.FITop3.InPolarBox Pa φ z) : Work.FIPlan.IsPrimary z := h.1

theorem InPolarBox.odd_gnorm {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (h : Work.FITop3.InPolarBox Pa φ z) : Odd (Work.FIPlan.gnorm z) :=
  IsPrimary.odd_gnorm (InPolarBox.isPrimary h)

theorem IsBoxCoeff.inPolarBox {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : Work.FITop3.IsBoxCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.InPolarBox Pa φ z := (h.2 z hz).1

theorem IsBoxCoeff.noSmallPrimes {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : Work.FITop3.IsBoxCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.NoSmallPrimes Pa z := (h.2 z hz).2

/-- The support of the coefficient of (4.13)/(5.13): where `β` is non-zero, `z` lies in the polar
box (5.14) and is free of primes `≤ P` (5.8). -/
theorem IsBetaCoeff.support {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
  · exact ⟨hc.1, hc.2.1⟩
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- The Möbius factor of (4.13): `β z ≠ 0` forces `|z|²` **squarefree** — the paper's "Since
`β(n)` is supported on odd squarefree numbers …".  With `InPolarBox.odd_gnorm` this gives
primitivity (`isCoprime_star_of_squarefree_odd_gnorm`). -/
theorem IsBetaCoeff.squarefree_gnorm {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Squarefree (Work.FIPlan.gnorm z) := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
  · have hmu : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ) ≠ 0 := by
      intro h0
      exact hz (by rw [if_pos hc, h0, mul_zero, zero_mul])
    exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp fun h0 => hmu (by rw [h0]; simp)
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- A non-zero coefficient point has norm `≥ 2` (its polar box has `|z|² > N ≥ 1`), so it is not a
unit — the norm hypothesis of `Delta_ne_zero_of_coprime`. -/
theorem two_le_gnorm_of_betaCoeff {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    2 ≤ Work.FIPlan.gnorm z := by
  have hb := (InPolarBox.norm_bounds (IsBetaCoeff.support h hz).1).1
  have : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have : (1 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := lt_of_le_of_lt this hb
  exact_mod_cast this

/-- **(*FI* (6.1)/(6.2) for the data that actually occur)**: for two distinct coprime points of the
support of `β` (hence primitive, of norm `≥ 2`), the determinant `Δ(z₁,z₂) = Im(z̄₁z₂)` does not
vanish — so the modulus `|Δ|` of the Weyl sum (6.10)/Lemma 8.1 is non-zero and the denominators of
§6 are legitimate.  (The primitivity hypotheses are stated explicitly: they are supplied by
`IsBetaCoeff.squarefree_gnorm` + `InPolarBox.odd_gnorm` through
`isCoprime_star_of_squarefree_odd_gnorm`.) -/
theorem Delta_ne_zero_of_betaCoeff_of_primitive {Pa : Work.FITop.Params} {φ : ℝ}
    {β : GaussianInt → ℂ} (h : Work.FITop3.IsBetaCoeff Pa φ β) {z1 z2 : GaussianInt}
    (h1 : β z1 ≠ 0) (_h2 : β z2 ≠ 0) (hcop : Work.FIPlan.GaussCoprime z1 z2)
    (hprim1 : IsCoprime z1 (star z1)) (hprim2 : IsCoprime z2 (star z2)) :
    Work.FIPlan.Delta z1 z2 ≠ 0 :=
  Delta_ne_zero_of_coprime hcop hprim1 hprim2 (two_le_gnorm_of_betaCoeff h h1)


/-! ## 4bis. The inverse of the (6.3) parametrisation, and the shape of (6.7) -/

/-- The inverse map of the parametrisation (6.3): `wOf z1 z2 c1 c2` is the (unique, when it
exists) Gaussian integer `w` with `Re(wz₁) = c₁²` and `Re(wz₂) = c₂²`; it is `0` when no such `w`
exists.  By `exists_cForm_eq_iff` — proved in `Submission/Work/FIArea2/exists_cForm_eq_iff.lean` —
it exists exactly when `Δ(z₁,z₂) ∣ c₁²z₂ − c₂²z₁` (for `Δ ≠ 0`), and by `cForm_pair_injective` it
is then unique.  This is the map by which (6.7) replaces the summation over `w` by the summation
over the square pairs `(c₁,c₂)` to which Poisson summation is applied. -/
noncomputable def wOf (z1 z2 : GaussianInt) (c1 c2 : ℤ) : GaussianInt :=
  if h : ∃ w : GaussianInt, Work.FIPlan.cForm w z1 = c1 * c1 ∧ Work.FIPlan.cForm w z2 = c2 * c2
  then Classical.choose h else 0

/-- The defining property of `wOf` where the parametrised point exists. -/
theorem cForm_wOf {z1 z2 : GaussianInt} {c1 c2 : ℤ}
    (h : ∃ w : GaussianInt, Work.FIPlan.cForm w z1 = c1 * c1 ∧ Work.FIPlan.cForm w z2 = c2 * c2) :
    Work.FIPlan.cForm (wOf z1 z2 c1 c2) z1 = c1 * c1 ∧
      Work.FIPlan.cForm (wOf z1 z2 c1 c2) z2 = c2 * c2 := by
  rw [wOf, dif_pos h]
  exact Classical.choose_spec h

/-- Uniqueness of the parametrised point (the content of `cForm_pair_injective` for `wOf`). -/
theorem wOf_unique {z1 z2 : GaussianInt} (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) {c1 c2 : ℤ}
    {w : GaussianInt} (h1 : Work.FIPlan.cForm w z1 = c1 * c1)
    (h2 : Work.FIPlan.cForm w z2 = c2 * c2) : w = wOf z1 z2 c1 c2 :=
  cForm_pair_injective hΔ (by
    simp only [Prod.mk.injEq]
    exact ⟨by rw [h1, (cForm_wOf ⟨w, h1, h2⟩).1], by rw [h2, (cForm_wOf ⟨w, h1, h2⟩).2]⟩)

/-! ## 6. Elementary size bounds for the kernel (8.16) and (6.13) -/

/-- `|(a/d)| ≤ 1` for the Jacobi symbol at `d > 0` (it is `±1` on the coprime part and `0`
otherwise). -/
theorem abs_jacobiSym_le_one (a : ℤ) {d : ℕ} (hd : 0 < d) : |jacobiSym a d| ≤ 1 := by
  by_cases hg : a.gcd (d : ℤ) = 1
  · rcases jacobiSym.eq_one_or_neg_one (a := a) (b := d) hg with h1 | h1
    · rw [h1]; norm_num
    · rw [h1]; norm_num
  · rw [jacobiSym.eq_zero_iff.mpr ⟨by omega, hg⟩]; norm_num

/-- **(8.16), trivial size**: `|G₀(z₁,z₂)| ≤ 2(τ(|Δ|) + 1)`.  Every term of the defining sum is
bounded by `1` (`φ(d)/d ≤ 1` and `|(z₂/z₁/d)| ≤ 1`) and the number of terms is at most `τ(|Δ|)`
(the terms are the `d` with `4d ∣ Δ`, hence `d ∣ Δ`), with the `+1` covering `Δ = 0` (where the
sum is the single term `d = 1`).  This is the kernel size used by the trivial estimates of §9. -/
theorem abs_G0_le (z1 z2 : GaussianInt) :
    |Work.FIPlan.G0 z1 z2|
      ≤ 2 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) + 1) := by
  have hterm : ∀ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
      |((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym ((star z1 * z2).re) d : ℝ)| ≤ 1 := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    have hd1 : 1 ≤ d := hd.1.1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hphi : ((Nat.totient d : ℝ)) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
    have hJ : |(jacobiSym ((star z1 * z2).re) d : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast abs_jacobiSym_le_one _ (by omega)
    rw [abs_mul]
    have habs : |(Nat.totient d : ℝ) / (d : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one hdpos]; exact hphi
    calc |(Nat.totient d : ℝ) / (d : ℝ)| * |(jacobiSym ((star z1 * z2).re) d : ℝ)|
        ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have hsub : ((Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2))
      ⊆ (Work.FIPlan.absDelta z1 z2).divisors ∪ {1} := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    rw [Finset.mem_union, Finset.mem_singleton]
    rcases eq_or_ne (Work.FIPlan.absDelta z1 z2) 0 with h0 | h0
    · right; rw [h0] at hd; omega
    · left
      obtain ⟨k, hk⟩ := hd.2
      exact Nat.mem_divisors.mpr ⟨⟨4 * k, by rw [hk]; ring⟩, h0⟩
  unfold Work.FIPlan.G0
  rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]
  gcongr
  calc |∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym ((star z1 * z2).re) d : ℝ)|
      ≤ ∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2), |((Nat.totient d : ℝ) / (d : ℝ))
          * (jacobiSym ((star z1 * z2).re) d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2), (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (((Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2)).card : ℝ) := by simp
    _ ≤ ((((Work.FIPlan.absDelta z1 z2).divisors ∪ {1}).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) + 1 := by
        have h := Finset.card_union_le (Work.FIPlan.absDelta z1 z2).divisors ({1} : Finset ℕ)
        simp only [Finset.card_singleton] at h
        exact_mod_cast h

/-! ## 7. The `D*`-versus-pairs identity: (5.26)/(6.9)/(9.1)

The frozen `Dstar` of (5.21) sums over the *outer* variable `w` and inside over the coprime pairs
`(z₁,z₂)`.  The paper's (9.1)/(9.11) sum over the pairs *first*, with the lattice count

  `C(z₁,z₂) = Σ_w f(|w|²)Z(Re wz₁)Z(Re wz₂)`  (6.9)

as the inner object.  `Dstar_eq_pairSum` performs this interchange, so that the whole content of
`Area2` becomes the per-pair statement `C(z₁,z₂) = C₀(z₁,z₂) + error` of (9.1). -/

/-- **(6.9)**: the lattice count at a pair, `C(z₁,z₂) = Σ_w f(|w|²)Z(Re wz₁)Z(Re wz₂)`, with `w`
ranging over the support box of the majorant. -/
def Ccount (Pa : Work.FITop.Params) (f : ℤ → ℝ) (z1 z2 : GaussianInt) : ℝ :=
  ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
    * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re

/-- `Z(Re wz)` is a real number, so it is its own conjugate. -/
theorem star_Zc (w z : GaussianInt) : star (Work.FITop3.Zc w z) = Work.FITop3.Zc w z := by
  rw [Complex.star_def, Complex.ext_iff]
  exact ⟨by simp, by simp [Zc_im]⟩

/-- A product of two theta coefficients is real. -/
theorem im_Zc_mul (w z1 z2 : GaussianInt) :
    (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).im = 0 := by
  rw [Complex.mul_im, Zc_im, Zc_im]
  ring

/-- The `re` of a product with a real second factor. -/
theorem re_mul_Zc (c : ℂ) (w z1 z2 : GaussianInt) :
    (c * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2)).re
      = c.re * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re := by
  rw [Complex.mul_re, im_Zc_mul]
  ring

/-- Factoring `β_{z₁}β̄_{z₂}` out of the `w`-sum. -/
theorem sum_w_re (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) (z1 z2 : GaussianInt) :
    (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
        * ((β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2)).re)
      = (β z1 * star (β z2)).re * Ccount Pa f z1 z2 := by
  unfold Ccount
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : ((β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2))
      = (β z1 * star (β z2)) * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2) := by
    rw [star_mul']
    simp only [star_Zc]
    ring
  rw [h, re_mul_Zc]
  ring

/-- The same, with the coprimality indicator in place. -/
theorem sum_w_ite (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ)
    (z1 z2 : GaussianInt) :
    (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
        * (if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0).re)
      = if Work.FIPlan.GaussCoprime z1 z2 then (β z1 * star (β z2)).re * Ccount Pa f z1 z2
        else 0 := by
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hc, if_true]
    exact sum_w_re Pa f β z1 z2
  · simp [hc, Complex.zero_re]

/-- **The interchange of (5.26) and (9.1)**: `D*` is the sum over coprime pairs of
`β_{z₁}β̄_{z₂}` times the lattice count `C(z₁,z₂)` of (6.9).  This is the form in which §9 estimates
the area: (9.1) is a per-pair statement about `C − C₀`, and `D0formMod` is the same pair sum with
`C₀` in place of `C`. -/
theorem Dstar_eq_pairSum (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    Work.FITop3.Dstar Pa f β
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re * Ccount Pa f z1 z2
          else 0 := by
  unfold Work.FITop3.Dstar
  simp only [Complex.re_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  exact sum_w_ite Pa f β z1 z2

/-- `D0formMod` is real; pushing `re` inside the pair sum. -/
theorem D0formMod_re_eq (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    (Work.FITop3.D0formMod (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re * Work.FITop3.C0mod (Work.FITop3.Fhat Pa f) z1 z2
          else 0 := by
  unfold Work.FITop3.D0formMod Work.FITop.boxN
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hc, if_true]
    rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re]
    ring
  · simp [hc, Complex.zero_re]

/-- **The difference form of (9.1)**: subtracting (9.11) from (5.26) reduces `Area2` to the
per-pair error `C(z₁,z₂) − C₀(z₁,z₂)` of (9.1).  This is the identity on which the whole §9
aggregate rests: the frozen left-hand side is the `β_{z₁}β̄_{z₂}`-weighted sum of the per-pair
errors. -/
theorem Dstar_sub_D0_eq_pairSum (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    Work.FITop3.Dstar Pa f β
        - (Work.FITop3.D0formMod (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re
              * (Ccount Pa f z1 z2 - Work.FITop3.C0mod (Work.FITop3.Fhat Pa f) z1 z2)
          else 0 := by
  rw [Dstar_eq_pairSum, D0formMod_re_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [hc, mul_sub]


/-! ## 8. The leaf of the area-2 contract

**Status of `Work.FIArea2.area2_r3` (`Work.FITop3.Area2`, FROZEN round 3).**  The statement is *FI*'s
(9.10), and the whole mathematical content of §§6–9 is now in this directory and in the modules it
imports, *for the paper's main term*: (6.9) (`Ccount_smooth_eq_poisson`), Lemma 7.1
(`lemma_7_1`), Lemma 7.2 with the elliptic-integral asymptotics (7.9)–(7.10)
(`lemma_7_2_core`, `ellInt_asymptotic`), Lemma 8.1 (8.5) (`Gsum_bound2`), Lemma 8.4 in its correct
form (8.16) (`G0_fix`), the `h = 0` term of (6.9) (`Sec6Hzero`), display (9.1)
(`sec9_error_from_poisson`), and the divisor-sum machinery of §9.  What is *not* here is the §9
aggregation ((9.5)–(9.10), the lacunarity sum over the polar box), and — independently of it — the
frozen statement is **not** (9.10):

* `Work.FIPlan.G0`, the kernel of the frozen `C0mod`, is provably *not* the count (6.12) that
  (8.16) evaluates (`witness1_Cnt : Cnt (1+4i) (1+28i) = 120`, i.e. `G₀ = 5`, while
  `witness1_G0 : FIPlan.G0 (1+4i) (1+28i) = 1`): the frozen kernel uses the character
  `(Re(z̄₁z₂)/d)` where the paper's (8.14)–(8.16) use the reduced `z₂/z₁ mod d`;
* the frozen `2 * Fhat` is the (7.10) factor `2 f̂(0)` applied to `Fhat`, but `Fhat`
  (`Σ_u f(u)/√u`) is the *discrete* surrogate of `2 f̂(0) = 2 ∫ f(|w|) d|w|` (the argument of `f`
  is `gnorm w = |w|²`, and `∫ f(|w|²) d|w| = ∫ f(u) u^{-1/2} du / 2`), so the frozen main term is
  twice the paper's.

Consequently `D* − D0formMod = (D* − D₀) − (D0formMod − D₀)`, the second bracket being of the size
of `D₀` itself, and the frozen statement is *strictly stronger* than (9.10): it asserts that the
paper's main term `D₀` — whose trivial size is `θ⁴M^{1/2}N^{3/2}(log N)⁸` (the paper: "(10.1) …
which of course barely misses what one wants, namely (5.20)", i.e. a saving of only `ϑ²` is
expected) — is `O(ϑ^{-1}τ²N²(log N)^b)`, a saving of a *power of x* below `D₀`'s size in the range
`N ≍ x^{1/4+η}` that `Params` permits.  This is why the leaf is left as a `sorry`: it is true
(by square-root cancellation in the Möbius-twisted sum, heuristically), it is *not* (9.10), and it
is beyond both the paper and any unconditional input available here.  See `NOTES.md` §§11–20 for
the derivations and for the recommended round-5 repairs.

**Session 9 (addendum).**  *FI* §9 is now **closed as mathematics**, for the paper's own main term:
`Sec9Area2Final.lean` proves `sec9_area2_poisson` (and its `‖·‖` form `sec9_area2_poisson_norm`,
i.e. the frozen contract's *shape*)

  `|D*(M,N) − D₀(M,N)| ≤ Cb·ϑ⁻¹·τ²·N²·(log N + 2)^b`,   `D₀ = Sec9Area2Defs.D0pois`

with the (6.13)+(6.11)+(6.12) main term (the exact `Fint F γ 0 0` integral and the count kernel
**Session 11 (addendum).**  The §9 range condition is `η`-dependent: with `H = Hscale M N` and
`R = (radN Pa).toNat` the inequality `R ≤ H^L` requires `L ≳ 1/(8η)` (NOT `L ≤ 4`; §30.5 of
`NOTES.md` is corrected in §31.1), exactly as in the paper's (9.3) (`n < 4√N H⁶ < H^{1/(2η)}`).
The chain therefore now carries a restriction predicate — `Sec9Aggregate.sec9Psum_le_of_hL_of_swap_gen`,
`Sec9AggregateFinal.sec9Psum_le_of_bounds_sharp_gen`, `Count.sec9_pairsum_bound_gen`,
`Sec9Area2Final.sec9_area2_poisson_gen`/`_norm_gen` take `(Rr : Params → Prop)` and conclude
`∀ Pa, Rr Pa → …` — and `Sec9Area2Range.lean` (new, `sorry`-free, axiom-clean) provides

* `HLPow L` = the averaged frequency sum (9.6)/(9.7) in the range `R ≤ H^L`,
* `sec9_hL_pow_of_peru : (∀ L, (9.6)–(9.7) with range L) → ∀ L, HLPow L`,
* `sec9_area2_poisson_pow` / `_norm_pow` — (9.10) on the class `radN Pa ≤ Hscale Pa^L`,
* `sec9_area2_poisson_eta` / `_norm_eta` — (9.10) on the class `Pa.η = η`,
* **`sec9_area2_poisson_eta_uncond`** — *FI* (9.10) for the paper's main term `D0pois` for each
  fixed `η`, with the range condition discharged from `Params` itself
  (`radN_le_Hscale_pow`), i.e. `∀ η > 0, ∃ Cb b, ∀ Pa, Pa.η = η → …`
  — and **now unconditional**: `sec9_area2_poisson_eta_final : Area2EtaStatement` is *FI* (9.10)
  for the paper's main term `D0pois`, with the constants depending on `η` only, resting on
  `sec9_peru_range_gen` (the per-pair estimate (9.6)–(9.7) with the range exponent free, proved).
  `sec9_area2_poisson_four_uncond` gives the same with *absolute* constants on the class
  `η > 1/28`, `x ≥ x₀(η)`, and `area2_abs_statement : Area2AbsStatement` gives absolute constants
  on the class `Pa.η ≥ 9/(8(L−1/2))` for a range exponent `L` of the reader's choice (the
  theorem `radN_le_Hscale_pow_fixed` supplies `radN ≤ Hscale^L` there).

The constants of (9.10) depend on `η` — as they do in the paper, where
`b = 2^{c+4} + 2^{c+1} + 4` with `c ≍ η^{-1}log η^{-1}`; the (9.12) bookkeeping `B ≫ b` is what a
consumer must record (`NOTES.md` §31.3).

`G0fix`), from the §9 aggregate `Sec9AggregateFinal.sec9Psum_le_of_bounds_sharp` — which in this
session had to be **sharpened**: the old `N²`-form of `sec9Psum_le_of_bounds` is *too weak* for
(9.10) (see `NOTES.md` §26.2; the correct bookkeeping is `√M·H²·N = N²`).  The only remaining input
is the averaged frequency sum `hL` of (9.6)/(9.7), i.e. `Work.FIArea2.Count.sec9_Lsum_avg`.  The
*box4* route to `hL` is dead — its core lemma `Count/box4_key_star` (= `bks_klhs_bound`) is **false**
(`NOTES.md` §§27–28); the live route is the joint one (`sec9_Lsum_avg_final_of_joint`), which is
what `R6/hL_six` consumes. -/
end

end Work.FIArea2
