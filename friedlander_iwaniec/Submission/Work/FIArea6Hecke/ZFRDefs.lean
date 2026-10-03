/-
# `Submission.Work.FIArea6Hecke.ZFRDefs` — vocabulary for the Hecke zero-free region

This file collects the *elementary* vocabulary that the zero-free region
`Work.FIArea6Hecke.heckeStripZFR` (the non-vanishing half of *FI* (16.20)+(16.24)) needs, together
with the elementary lemmas about it.  Everything here is proved outright (no `sorry`), so the file
is safe to import from anywhere in the Hecke chapter.

## What the target needs, and where this file sits in it

`heckeStripZFR` asks for `c > 0` with `Lval d m Lam s ≠ 0` in
`1 - c/(d^ε·log(|m|+|s.im|+3)) ≤ s.re ≤ 2`, for every *strict* character `χ` mod `4d` and every
entire `Lam` agreeing with `heckeArch d m s * heckeLSeries chi m s` on `1 + |m|/2 < s.re`.
Writing `G` for the honest completion of `L(s,ψ)`, the classical chain is

1. **existence of the completion** `G` (entire, agreeing with `heckeArch·heckeLSeries` on
   `1 < s.re`) — Hecke's functional equation, i.e. the theta law `thetaHol_poisson` fed into
   `heckeFE_of_theta` together with the Mellin identity `mellin_thetaHol_clean`;
2. **identification**: `Lam = G` (both entire, agreeing on the nonempty open set `1+|m|/2 < s.re`);
   here `Lam - G` is entire and vanishes on an open set, so it vanishes identically.  This is
   `eq_of_agrees_right` below;
3. **non-vanishing of `G`** in the region, i.e. `G s ≠ 0`; since
   `Lval d m Lam s = Lam s / heckeArch d m s` and `heckeArch d m s ≠ 0` for `0 < s.re`
   (`Lval_ne_zero_iff`), steps 2+3 give `Lval d m Lam s ≠ 0`.  Step 3 is the deep part: the
   de la Vallée Poussin region off the real axis (the `(3,4,1)` inequality
   `heckeThreeFourOneZFR`, plus convexity bounds for the completion) and the Landau–Siegel bound
   on the real axis.

`principalStrict d` below is the *principal* strict character (`1` on the units modulo `4d`, `0`
elsewhere): its Hecke `L`-series is the "`ζ_K` of the `(3,4,1)` inequality" (the first and third
factors), and it is the trivial-conductor datum of the chapter.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. Units modulo `4d` and the principal strict character -/

/-- `4d` as a Gaussian integer (the modulus of the chapter). -/
abbrev fourDZFR (d : ℕ) : GaussianInt := ((((4 * d : ℕ) : ℤ)) : GaussianInt)

lemma isUnitMod4d_one (d : ℕ) : Work.FIArea5.S16Hecke.IsUnitMod4d d (1 : GaussianInt) :=
  ⟨1, by ring_nf; exact dvd_zero _⟩

/-- `z·w` is a unit modulo `4d` iff `z` and `w` both are: the units of the quotient
`ℤ[i]/(4d)` form a submonoid, and `z·w` invertible forces both factors invertible. -/
lemma isUnitMod4d_mul_iff {d : ℕ} {z w : GaussianInt} :
    Work.FIArea5.S16Hecke.IsUnitMod4d d (z * w) ↔
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d w := by
  constructor
  · intro ⟨c, hc⟩
    refine ⟨⟨w * c, ?_⟩, ⟨z * c, ?_⟩⟩
    · simpa [mul_assoc] using hc
    · have h2 : z * w * c = w * (z * c) := by ring
      rwa [h2] at hc
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a * b, ?_⟩
    have h : z * w * (a * b) - 1 = (z * a - 1) * (w * b) + (w * b - 1) := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb

/-- The units modulo `4d` depend only on the class modulo `4d`. -/
lemma isUnitMod4d_congr' {d : ℕ} {z w : GaussianInt} (h : fourDZFR d ∣ (z - w)) :
    Work.FIArea5.S16Hecke.IsUnitMod4d d z ↔ Work.FIArea5.S16Hecke.IsUnitMod4d d w := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have : w * a - 1 = (z * a - 1) - (z - w) * a := by ring
    rw [this]
    exact dvd_sub ha (dvd_mul_of_dvd_left h a)
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have : z * a - 1 = (w * a - 1) + (z - w) * a := by ring
    rw [this]
    exact dvd_add ha (dvd_mul_of_dvd_left h a)

/-- **The principal strict character modulo `4d`**: the indicator of the units of `ℤ[i]/(4d)`. -/
def principalStrict (d : ℕ) : GaussianInt → ℂ := fun z =>
  if Work.FIArea5.S16Hecke.IsUnitMod4d d z then 1 else 0

lemma principalStrict_of_unit {d : ℕ} {z : GaussianInt}
    (h : Work.FIArea5.S16Hecke.IsUnitMod4d d z) : principalStrict d z = 1 := if_pos h

lemma principalStrict_of_not_unit {d : ℕ} {z : GaussianInt}
    (h : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d z) : principalStrict d z = 0 := if_neg h

lemma principalStrict_one (d : ℕ) : principalStrict d (1 : GaussianInt) = 1 :=
  principalStrict_of_unit (isUnitMod4d_one d)

lemma principalStrict_mul (d : ℕ) (z w : GaussianInt) :
    principalStrict d (z * w) = principalStrict d z * principalStrict d w := by
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z <;>
    by_cases hw : Work.FIArea5.S16Hecke.IsUnitMod4d d w
  · rw [principalStrict_of_unit (isUnitMod4d_mul_iff.mpr ⟨hz, hw⟩), principalStrict_of_unit hz,
      principalStrict_of_unit hw, mul_one]
  · rw [principalStrict_of_not_unit (fun h => hw (isUnitMod4d_mul_iff.mp h).2),
      principalStrict_of_unit hz, principalStrict_of_not_unit hw, mul_zero]
  · rw [principalStrict_of_not_unit (fun h => hz (isUnitMod4d_mul_iff.mp h).1),
      principalStrict_of_not_unit hz, principalStrict_of_unit hw, zero_mul]
  · rw [principalStrict_of_not_unit (fun h => hz (isUnitMod4d_mul_iff.mp h).1),
      principalStrict_of_not_unit hz, principalStrict_of_not_unit hw, zero_mul]

lemma norm_principalStrict_le_one (d : ℕ) (z : GaussianInt) : ‖principalStrict d z‖ ≤ 1 := by
  by_cases h : Work.FIArea5.S16Hecke.IsUnitMod4d d z <;>
    simp [principalStrict, h]

lemma principalStrict_eq_of_dvd_sub {d : ℕ} {z w : GaussianInt} (h : fourDZFR d ∣ (z - w)) :
    principalStrict d z = principalStrict d w := by
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · rw [principalStrict_of_unit hz, principalStrict_of_unit ((isUnitMod4d_congr' h).mp hz)]
  · rw [principalStrict_of_not_unit hz,
      principalStrict_of_not_unit (fun hw => hz ((isUnitMod4d_congr' h).mpr hw))]

/-- A multiple of `4d` is not a unit modulo `4d` (for `d ≥ 1`): `4d ∣ 1` would force
`gnorm (4d) = 16d² ≤ 1`. -/
lemma not_isUnitMod4d_of_dvd {d : ℕ} (hd : 1 ≤ d) {z : GaussianInt} (h : fourDZFR d ∣ z) :
    ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d z := by
  rintro ⟨a, ha⟩
  have hza : fourDZFR d ∣ z * a := dvd_mul_of_dvd_left h a
  have h1 : fourDZFR d ∣ (1 : GaussianInt) := by
    have hz : (1 : GaussianInt) = z * a - (z * a - 1) := by ring
    rw [hz]
    exact dvd_sub hza ha
  obtain ⟨b, hb⟩ := h1
  have hgn : Work.FIPlan.gnorm (1 : GaussianInt) = Work.FIPlan.gnorm (fourDZFR d * b) := by
    rw [hb]
  rw [Work.FIArea5.S16Hecke.gnorm_mul, Work.FIArea5.S16Hecke.gnorm_one] at hgn
  have h4 : Work.FIPlan.gnorm (fourDZFR d) = (4 * d) ^ 2 := by
    simp [Work.FIPlan.gnorm, Zsqrtd.norm_def, Int.natAbs_mul, Int.natAbs_natCast, pow_two,
      fourDZFR]
  rw [h4] at hgn
  have hpos : 1 ≤ Work.FIPlan.gnorm b := by
    rcases Nat.eq_zero_or_pos (Work.FIPlan.gnorm b) with h0 | h0
    · rw [h0, mul_zero] at hgn
      exact absurd hgn (by norm_num)
    · exact h0
  have hgn' : (1 : ℝ) = ((4 * d) ^ 2 : ℝ) * (Work.FIPlan.gnorm b : ℝ) := by exact_mod_cast hgn
  have hb1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm b : ℝ) := by exact_mod_cast hpos
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith [sq_nonneg (4 * (d : ℝ))]

lemma principalStrict_eq_zero_of_dvd {d : ℕ} (hd : 1 ≤ d) {z : GaussianInt}
    (h : fourDZFR d ∣ z) : principalStrict d z = 0 :=
  principalStrict_of_not_unit (not_isUnitMod4d_of_dvd hd h)

/-- **The principal strict character is a strict character modulo `4d`.** -/
theorem isCharMod4dStrict_principalStrict (d : ℕ) (hd : 1 ≤ d) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d (principalStrict d) := by
  refine ⟨⟨principalStrict_one d, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro z w; exact principalStrict_mul d z w
  · intro z; exact norm_principalStrict_le_one d z
  · intro z w h; exact principalStrict_eq_of_dvd_sub h
  · intro z hz; exact principalStrict_eq_zero_of_dvd hd hz
  · intro z hz; exact principalStrict_of_not_unit hz

/-! ## 2. The archimedean factor on the right half-plane -/

/-- `heckeArch d m s = (4d/π)^s·Γ(s + |m|/2)` does not vanish when `re s > 0`, so on the right
half-plane `Lval d m Lam s = 0 ↔ Lam s = 0`. -/
lemma heckeArch_ne_zero_of_pos_re {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Work.FITop4.Bridge.heckeArch d m s ≠ 0 := by
  unfold Work.FITop4.Bridge.heckeArch
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_def_of_ne_zero ?_]
    · exact Complex.exp_ne_zero _
    · have h1 : ((4 : ℂ) * ((d : ℝ) : ℂ)) ≠ 0 := by
        refine mul_ne_zero (by norm_num) ?_
        exact_mod_cast (ne_of_gt (by exact_mod_cast hd : (0 : ℝ) < (d : ℝ)))
      have h2 : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simpa using div_ne_zero h1 h2
  · refine Complex.Gamma_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.ofReal_re]
    have := abs_nonneg (m : ℝ)
    linarith

lemma Lval_ne_zero_iff {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {Lam : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) :
    Lval d m Lam s ≠ 0 ↔ Lam s ≠ 0 := by
  rw [Lval, div_ne_zero_iff]
  simp [heckeArch_ne_zero_of_pos_re hd m hs]

/-! ## 3. Uniqueness of the completion on an open half-plane -/

/-- **Two entire functions agreeing on an open half-plane are equal.**  This is the step that
turns `heckeStripZFR` into a statement about the honest completion `G` of the Hecke `L`-function:
the entire function `Lam` of the hypothesis agrees with `G` on `1 + |m|/2 < s.re`, hence on a
nonempty open set, and both are entire. -/
lemma eq_of_agrees_right (G Lam : ℂ → ℂ) (hG : AnalyticOn ℂ G Set.univ)
    (hL : AnalyticOn ℂ Lam Set.univ) (h : ∀ s : ℂ, 1 < s.re → Lam s = G s) : Lam = G := by
  have hG' : AnalyticOnNhd ℂ G Set.univ := analyticOn_univ.mp hG
  have hL' : AnalyticOnNhd ℂ Lam Set.univ := analyticOn_univ.mp hL
  have hev : (fun s : ℂ => Lam s - G s) =ᶠ[nhds (2 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (2 : ℂ) (by norm_num : (0 : ℝ) < 1)] with s hs
    have h1 : ‖s - 2‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
    have h2 : |s.re - 2| ≤ ‖s - 2‖ := by
      simpa using Complex.abs_re_le_norm (s - 2)
    have h3 : 1 < s.re := by
      have := lt_of_le_of_lt h2 h1
      rw [abs_lt] at this
      linarith [this.1]
    simp [h s h3]
  have hzero : (fun s : ℂ => Lam s - G s) = 0 :=
    AnalyticOnNhd.eq_of_eventuallyEq (hL'.sub hG') (fun z _ => analyticAt_const) hev
  funext s
  exact sub_eq_zero.mp (congrFun hzero s)

end

end Work.FIArea6Hecke
