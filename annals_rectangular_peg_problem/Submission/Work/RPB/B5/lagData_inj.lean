import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B2.chordSurf_injective
import Submission.Work.RPB.B2.chordSurf_period_swap
import Submission.Work.RPV.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPB.Defs
import Submission.Work.RPV.V
import Submission.Work.RPB.B5.collar_noSpurious_restricted
import Submission.Work.RPB.B5.K0_chordSurf_level
import Submission.Work.RPB.B5.chartW_eq_chordSurf_sqrt
import Submission.Work.RPB.B5.lagData_rho_inj
import Submission.Work.RPB.B5.lagData_K0_lagPt
import Submission.Work.RPB.B5.lagData_chord_form_left
import Submission.Work.RPB.B5.lagData_chord_form_right
import Submission.Work.RPB.B5.collar_levelPt_inj

/-!
# B5: injectivity of the assembled Lagrangian family modulo `2π`

`Work.RPB.B5.lagData_inj`: the assembled family `ℓ τ (x,t) = lagPt D.W D.Γc D.Ac D.rho τ x t`
satisfies the `inj` field of `Work.RPV.LagFamily`: if two of its points agree up to the
`2π`-shift `Tk k` of the angle coordinate, then they have the same `x` and the same `t` mod `2π`.

## Plan (see `B5_PLAN.lean` for the global picture)

The family is made of two kinds of pieces:

* the **collar** `|x| ≥ √2` (`σ = sig x ≥ 0`): for `x ≤ -√2` the point is
  `collarPt τ (sig x) t = levelPt (Γc τ (sig x) t) (sig x) (Ac τ (sig x) t)`, and for `x ≥ √2`
  it is the `τ_π`-image of the reflected point (`τ_π` preserves `K₀` and `uproj`);
* the **chord chart** `|x| < √2`: for `-√2 < x ≤ 0` the point is
  `W τ t (rho τ x t) = chordSurf CI.c a τ t (√(rho τ x t))`, and for `0 < x < √2` it is the
  `τ_π`-image of the chord at `(t-π, √(rho τ (-x) (t-π)))`, which the chord swap rewrites as
  `chordSurf CI.c a τ t (π - √(rho τ (-x) (t-π)))`.

`K₀` is invariant under `Tk`, equals `-x²/2 ≤ -1` on the collar and is `> -1` on the chart, so
the level of `K₀` decides on which of the two kinds both points lie (and separates the collar
from the chart).  Inside each kind the collision is resolved by the injectivity of the collar
parametrisation (`collar_levelPt_inj`, resp. `collar_noSpurious_restricted` for the mixed-sign
case where the two collar halves are glued by `τ_π`) or by the injectivity of the chord annulus
(`Work.RPB.B2.chordSurf_injective`) together with the injectivity of `x ↦ rho τ x t` on
`[-√2, 0]` (`lagData_rho_inj`).
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

open Complex

/-! ## Elementary facts about the two branches of `lagPt` -/

/-- `rho` is `2π`-periodic in `t`, hence invariant under all integer shifts of the parameter. -/
private lemma rho_add_two_pi_mul {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    (D : Work.RPB.B5.LagData CI a) (τ x t : ℝ) (l : ℤ) :
    D.rho τ x (t + 2 * Real.pi * l) = D.rho τ x t :=
  Int.induction_on l (by simp)
    (fun n ih => by
      have ih' : D.rho τ x (t + 2 * Real.pi * (n : ℝ)) = D.rho τ x t := by simpa using ih
      rw [show (((n : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
        show t + 2 * Real.pi * ((n : ℝ) + 1) = (t + 2 * Real.pi * (n : ℝ)) + 2 * Real.pi
          by ring,
        D.hrhoper τ x (t + 2 * Real.pi * (n : ℝ)), ih'])
    (fun n ih => by
      have ih' : D.rho τ x (t + 2 * Real.pi * (-(n : ℝ))) = D.rho τ x t := by simpa using ih
      have key := D.hrhoper τ x ((t + 2 * Real.pi * (-(n : ℝ))) - 2 * Real.pi)
      have h2 : (t + 2 * Real.pi * (-(n : ℝ)) - 2 * Real.pi) + 2 * Real.pi
          = t + 2 * Real.pi * (-(n : ℝ)) := by ring
      rw [h2] at key
      rw [show ((-(n : ℤ) - 1 : ℤ) : ℝ) = -(n : ℝ) - 1 by push_cast; ring,
        show t + 2 * Real.pi * (-(n : ℝ) - 1)
            = (t + 2 * Real.pi * (-(n : ℝ))) - 2 * Real.pi by ring, key.symm, ih'])

/-- Two points `≤ -√2` with the same `sig` are equal. -/
private lemma sig_inj_on {x x' : ℝ} (hx : x ≤ -Real.sqrt 2) (hx' : x' ≤ -Real.sqrt 2)
    (h : sig x = sig x') : x = x' := by
  have h2 : x ^ 2 = x' ^ 2 := by simp only [sig] at h; linarith
  have hx0 : x ≤ 0 := by linarith [Real.sqrt_nonneg 2]
  have hsq : (x - x') * (x + x') = 0 := by nlinarith [h2]
  rcases mul_eq_zero.mp hsq with h1 | h1
  · linarith
  · have := Real.sqrt_pos_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith

/-- Two points `≥ √2` with the same `sig` are equal. -/
private lemma sig_inj_on_pos {x x' : ℝ} (hx : Real.sqrt 2 ≤ x) (hx' : Real.sqrt 2 ≤ x')
    (h : sig x = sig x') : x = x' := by
  have h2 : x ^ 2 = x' ^ 2 := by simp only [sig] at h; linarith
  have hsq : (x - x') * (x + x') = 0 := by nlinarith [h2]
  rcases mul_eq_zero.mp hsq with h1 | h1
  · linarith
  · have := Real.sqrt_pos_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith

/-- `sig x ≥ 0` on the collar side. -/
private lemma sig_nonneg_of_le {x : ℝ} (hx : x ≤ -Real.sqrt 2) : 0 ≤ sig x := by
  have h : Real.sqrt 2 ≤ -x := by linarith [Real.sqrt_nonneg 2]
  have h2 : (Real.sqrt 2) ^ 2 ≤ (-x) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg 2) h 2
  rw [Real.sq_sqrt (by norm_num)] at h2
  have h3 : (2 : ℝ) ≤ x ^ 2 := by rw [show (-x) ^ 2 = x ^ 2 by ring] at h2; exact h2
  simp only [sig]; linarith

/-- `sig x ≥ 0` on the right collar side as well. -/
private lemma sig_nonneg_of_ge {x : ℝ} (hx : Real.sqrt 2 ≤ x) : 0 ≤ sig x := by
  have h := sig_nonneg_of_le (x := -x) (by linarith : -x ≤ -Real.sqrt 2)
  rwa [show sig (-x) = sig x by simp only [sig]; ring] at h

/-- `√2 ≤ |x|` forces `x² ≥ 2`. -/
private lemma two_le_sq_of_sqrt_two_le_abs {x : ℝ} (h : Real.sqrt 2 ≤ |x|) : 2 ≤ x ^ 2 := by
  have h1 : (Real.sqrt 2) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg 2) h 2
  rwa [Real.sq_sqrt (by norm_num), sq_abs] at h1

/-- The left collar branch of `lagPt`. -/
private lemma lagPt_collar_neg {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    (D : Work.RPB.B5.LagData CI a) (τ x t : ℝ) (hx : x ≤ -Real.sqrt 2) :
    lagPt D.W D.Γc D.Ac D.rho τ x t = collarPt D.Γc D.Ac τ (sig x) t := by
  rw [lagPt, if_pos (by linarith [Real.sqrt_nonneg 2]), basePt, if_pos hx, collarPt]

/-- The right collar branch of `lagPt`. -/
private lemma lagPt_collar_pos {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    (D : Work.RPB.B5.LagData CI a) (τ x t : ℝ) (hx : Real.sqrt 2 ≤ x) :
    lagPt D.W D.Γc D.Ac D.rho τ x t
      = Work.RPV.tau Real.pi (collarPt D.Γc D.Ac τ (sig x) (t - Real.pi)) := by
  have hx0 : 0 < x := by linarith [Real.sqrt_pos_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hnx : -x ≤ -Real.sqrt 2 := by linarith
  rw [lagPt, if_neg (not_le.mpr hx0), basePt, if_pos hnx, collarPt, collarPt,
    show sig (-x) = sig x by simp only [sig]; ring]

/-- `√(rho τ x t) ∈ (0, π/2]` for `x ∈ (-√2, 0]`. -/
private lemma sqrt_rho_mem {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    (D : Work.RPB.B5.LagData CI a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) {x t : ℝ}
    (hx : x ∈ Set.Ioc (-Real.sqrt 2) 0) :
    0 < Real.sqrt (D.rho τ x t) ∧ Real.sqrt (D.rho τ x t) ≤ Real.pi / 2 := by
  obtain ⟨h0, hle⟩ := D.hrhoval τ hτ x hx t
  refine ⟨Real.sqrt_pos_of_pos h0, ?_⟩
  calc Real.sqrt (D.rho τ x t) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hle
    _ = Real.pi / 2 := by
        rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)

/-- `π` is not an integral multiple of `2π`. -/
private lemma ne_two_pi_mul_pi : ∀ m : ℤ, Real.pi ≠ 2 * Real.pi * (m : ℝ) := by
  intro m hm
  have h' : 2 * (m : ℝ) = 1 := by nlinarith [hm, Real.pi_pos]
  have h3 : (2 * m : ℤ) = 1 := by
    have : ((2 * m : ℤ) : ℝ) = (1 : ℝ) := by push_cast; linarith [h']
    exact_mod_cast this
  omega

/-- `-π` is not an integral multiple of `2π`. -/
private lemma ne_two_pi_mul_neg_pi : ∀ m : ℤ, -Real.pi ≠ 2 * Real.pi * (m : ℝ) := by
  intro m hm
  have h' : 2 * (m : ℝ) = -1 := by nlinarith [hm, Real.pi_pos]
  have h3 : (2 * m : ℤ) = -1 := by
    have : ((2 * m : ℤ) : ℝ) = (-1 : ℝ) := by push_cast; linarith [h']
    exact_mod_cast this
  omega

/-- On `|x| < √2` the family is a chord of the curve, with the radius of the corresponding chart
branch. -/
private lemma lagPt_chord_rep {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    {τ x t : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hx : |x| < Real.sqrt 2) :
    ∃ r ∈ Set.Ioo (0 : ℝ) Real.pi,
      lagPt D.W D.Γc D.Ac D.rho τ x t = Work.RPB.chordSurf CI.c a τ t r ∧
      ((x ≤ 0 ∧ r = Real.sqrt (D.rho τ x t)) ∨
       (0 < x ∧ r = Real.pi - Real.sqrt (D.rho τ (-x) (t - Real.pi)))) := by
  have hx1 : -Real.sqrt 2 < x := (abs_lt.mp hx).1
  have hx2 : x < Real.sqrt 2 := (abs_lt.mp hx).2
  by_cases hxs : x ≤ 0
  · obtain ⟨h1, h2⟩ := lagData_chord_form_left CI a D τ hτ x t hx1 hxs
    exact ⟨Real.sqrt (D.rho τ x t), ⟨h2.1, by linarith [h2.2, Real.pi_pos]⟩, h1,
      Or.inl ⟨hxs, rfl⟩⟩
  · have hxpos : 0 < x := lt_of_not_ge hxs
    obtain ⟨h1, h2⟩ := lagData_chord_form_right CI a ha D τ hτ x t hxpos hx2
    exact ⟨Real.pi - Real.sqrt (D.rho τ (-x) (t - Real.pi)), h2, h1, Or.inr ⟨hxpos, rfl⟩⟩

theorem lagData_inj (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t x' t' (k : ℤ),
      lagPt D.W D.Γc D.Ac D.rho τ x' t'
        = Work.RPV.Tk k (lagPt D.W D.Γc D.Ac D.rho τ x t) →
      x' = x ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * m := by
  intro τ hτ x t x' t' k h
  -- `K₀` is invariant under the `2π`-shift `Tk k`
  have hK0 : Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ x' t')
      = Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ x t) := by
    rw [h, Work.RPV.K0_Tk]
  obtain ⟨hKcol, hKch⟩ := lagData_K0_lagPt CI a ha D
  by_cases hxc : |x| < Real.sqrt 2
  · -- ## the chord chart: `|x| < √2`, and then `|x'| < √2` too (`K₀ > -1`)
    have hxc' : |x'| < Real.sqrt 2 := by
      by_contra hcon
      have hge : Real.sqrt 2 ≤ |x'| := le_of_not_gt hcon
      have h1 := hKch τ hτ x t hxc
      have h2 := hKcol τ hτ x' t' hge
      have h3 : (2 : ℝ) ≤ x' ^ 2 := two_le_sq_of_sqrt_two_le_abs hge
      rw [hK0] at h2
      linarith
    have hx1 : -Real.sqrt 2 < x := (abs_lt.mp hxc).1
    have hx2 : x < Real.sqrt 2 := (abs_lt.mp hxc).2
    have hx1' : -Real.sqrt 2 < x' := (abs_lt.mp hxc').1
    have hx2' : x' < Real.sqrt 2 := (abs_lt.mp hxc').2
    obtain ⟨r, hr, hrep, hbr⟩ := lagPt_chord_rep ha D hτ hxc
    obtain ⟨r', hr', hrep', hbr'⟩ := lagPt_chord_rep ha D hτ hxc'
    -- both points are chords of the curve at time `τ`: injectivity mod `2π`
    have hkey : Work.RPB.chordSurf CI.c a τ t' r'
        = Work.RPV.Tk k (Work.RPB.chordSurf CI.c a τ t r) := by
      rw [← hrep', ← hrep]; exact h
    obtain ⟨hrr, m, hm⟩ :=
      Work.RPB.B2.chordSurf_injective CI a ha τ hτ t r hr r' hr' t' k hkey
    refine ⟨?_, ⟨m, hm⟩⟩
    rcases hbr with ⟨hxs, hrv⟩ | ⟨hxpos, hrv⟩
    · rcases hbr' with ⟨hxs', hrv'⟩ | ⟨hxpos', hrv'⟩
      · -- ## both on the left chart piece: the radii `√rho` agree, so `x = x'`
        have hmem : x ∈ Set.Icc (-Real.sqrt 2) 0 := ⟨hx1.le, hxs⟩
        have hmem' : x' ∈ Set.Icc (-Real.sqrt 2) 0 := ⟨hx1'.le, hxs'⟩
        have hp : D.rho τ x t = D.rho τ x' t := by
          have hA : Real.sqrt (D.rho τ x t) = Real.sqrt (D.rho τ x' t') := by
            rw [← hrv, ← hrv']; exact hrr.symm
          have h0 : 0 < D.rho τ x t := (D.hrhoval τ hτ x ⟨hx1, hxs⟩ t).1
          have h0' : 0 < D.rho τ x' t' := (D.hrhoval τ hτ x' ⟨hx1', hxs'⟩ t').1
          have hsq := congrArg (fun y : ℝ => y ^ 2) hA
          rw [Real.sq_sqrt h0.le, Real.sq_sqrt h0'.le] at hsq
          rwa [show D.rho τ x' t' = D.rho τ x' t by
            rw [hm, rho_add_two_pi_mul D τ x' t m]] at hsq
        exact (lagData_rho_inj CI a D τ hτ t x hmem x' hmem' hp).symm
      · -- ## left chart piece against the reflected right piece: the two radii add up to `π`
        have hle' : -x' ≤ 0 := by linarith
        have hgt' : -Real.sqrt 2 < -x' := by linarith
        have hA : Real.sqrt (D.rho τ x t)
            = Real.pi - Real.sqrt (D.rho τ (-x') (t' - Real.pi)) := by
          rw [← hrv, ← hrv']; exact hrr.symm
        obtain ⟨hb1, hb2⟩ := sqrt_rho_mem D hτ (x := x) (t := t) ⟨hx1, hxs⟩
        obtain ⟨hb1', hb2'⟩ := sqrt_rho_mem D hτ (x := -x') (t := t' - Real.pi) ⟨hgt', hle'⟩
        have heq1 : Real.sqrt (D.rho τ x t) = Real.pi / 2 := by linarith
        have heq2 : Real.sqrt (D.rho τ (-x') (t' - Real.pi)) = Real.pi / 2 := by linarith
        have hv1 : D.rho τ x t = Real.pi ^ 2 / 4 := by
          have hh := congrArg (fun y : ℝ => y ^ 2) heq1
          rw [Real.sq_sqrt (x := D.rho τ x t) (D.hrhoval τ hτ x ⟨hx1, hxs⟩ t).1.le] at hh
          rw [hh]; ring
        have hv2 : D.rho τ (-x') (t' - Real.pi) = Real.pi ^ 2 / 4 := by
          have hh := congrArg (fun y : ℝ => y ^ 2) heq2
          rw [Real.sq_sqrt (x := D.rho τ (-x') (t' - Real.pi))
            (D.hrhoval τ hτ (-x') ⟨hgt', hle'⟩ (t' - Real.pi)).1.le] at hh
          rw [hh]; ring
        have hx0 : x = 0 := lagData_rho_inj CI a D τ hτ t x ⟨hx1.le, hxs⟩ 0
          ⟨by linarith [Real.sqrt_nonneg 2], le_refl 0⟩ (by rw [hv1, D.hrho0 τ hτ t])
        have hx'0 : -x' = 0 := lagData_rho_inj CI a D τ hτ (t' - Real.pi) (-x')
          ⟨hgt'.le, hle'⟩ 0 ⟨by linarith [Real.sqrt_nonneg 2], le_refl 0⟩
          (by rw [hv2, D.hrho0 τ hτ (t' - Real.pi)])
        linarith
    · rcases hbr' with ⟨hxs', hrv'⟩ | ⟨hxpos', hrv'⟩
      · -- ## reflected right piece against the left chart piece (the mirror image)
        have hle : -x ≤ 0 := by linarith
        have hgt : -Real.sqrt 2 < -x := by linarith
        have hA : Real.pi - Real.sqrt (D.rho τ (-x) (t - Real.pi))
            = Real.sqrt (D.rho τ x' t') := by
          rw [← hrv, ← hrv']; exact hrr.symm
        obtain ⟨hb1, hb2⟩ := sqrt_rho_mem D hτ (x := -x) (t := t - Real.pi) ⟨hgt, hle⟩
        obtain ⟨hb1', hb2'⟩ := sqrt_rho_mem D hτ (x := x') (t := t') ⟨hx1', hxs'⟩
        have heq1 : Real.sqrt (D.rho τ (-x) (t - Real.pi)) = Real.pi / 2 := by linarith
        have heq2 : Real.sqrt (D.rho τ x' t') = Real.pi / 2 := by linarith
        have hv1 : D.rho τ (-x) (t - Real.pi) = Real.pi ^ 2 / 4 := by
          have hh := congrArg (fun y : ℝ => y ^ 2) heq1
          rw [Real.sq_sqrt (x := D.rho τ (-x) (t - Real.pi))
            (D.hrhoval τ hτ (-x) ⟨hgt, hle⟩ (t - Real.pi)).1.le] at hh
          rw [hh]; ring
        have hv2 : D.rho τ x' t' = Real.pi ^ 2 / 4 := by
          have hh := congrArg (fun y : ℝ => y ^ 2) heq2
          rw [Real.sq_sqrt (x := D.rho τ x' t') (D.hrhoval τ hτ x' ⟨hx1', hxs'⟩ t').1.le] at hh
          rw [hh]; ring
        have hx0 : -x = 0 := lagData_rho_inj CI a D τ hτ (t - Real.pi) (-x)
          ⟨hgt.le, hle⟩ 0 ⟨by linarith [Real.sqrt_nonneg 2], le_refl 0⟩
          (by rw [hv1, D.hrho0 τ hτ (t - Real.pi)])
        have hx'0 : x' = 0 := lagData_rho_inj CI a D τ hτ t' x' ⟨hx1'.le, hxs'⟩ 0
          ⟨by linarith [Real.sqrt_nonneg 2], le_refl 0⟩ (by rw [hv2, D.hrho0 τ hτ t'])
        linarith
      · -- ## both on the reflected right piece: the radii `π - √rho` agree
        have hmem : -x ∈ Set.Icc (-Real.sqrt 2) 0 := ⟨by linarith, by linarith⟩
        have hmem' : -x' ∈ Set.Icc (-Real.sqrt 2) 0 := ⟨by linarith, by linarith⟩
        have hp : D.rho τ (-x) (t - Real.pi) = D.rho τ (-x') (t - Real.pi) := by
          have hA : Real.pi - Real.sqrt (D.rho τ (-x) (t - Real.pi))
              = Real.pi - Real.sqrt (D.rho τ (-x') (t' - Real.pi)) := by
            rw [← hrv, ← hrv']; exact hrr.symm
          have hpp : Real.sqrt (D.rho τ (-x) (t - Real.pi))
              = Real.sqrt (D.rho τ (-x') (t' - Real.pi)) := by linarith
          have h0 : 0 < D.rho τ (-x) (t - Real.pi) :=
            (D.hrhoval τ hτ (-x) ⟨by linarith, by linarith⟩ (t - Real.pi)).1
          have h0' : 0 < D.rho τ (-x') (t' - Real.pi) :=
            (D.hrhoval τ hτ (-x') ⟨by linarith, by linarith⟩ (t' - Real.pi)).1
          have hsq := congrArg (fun y : ℝ => y ^ 2) hpp
          rw [Real.sq_sqrt h0.le, Real.sq_sqrt h0'.le] at hsq
          rwa [show D.rho τ (-x') (t' - Real.pi) = D.rho τ (-x') (t - Real.pi) by
            rw [show t' - Real.pi = (t - Real.pi) + 2 * Real.pi * m by linarith,
              rho_add_two_pi_mul D τ (-x') (t - Real.pi) m]] at hsq
        have hxx : -x = -x' :=
          lagData_rho_inj CI a D τ hτ (t - Real.pi) (-x) hmem (-x') hmem' hp
        linarith
  · -- ## the collar: `|x| ≥ √2`, and then `|x'| ≥ √2` too (`K₀ ≤ -1`)
    have hge : Real.sqrt 2 ≤ |x| := le_of_not_gt hxc
    have hge' : Real.sqrt 2 ≤ |x'| := by
      by_contra hcon
      have h1 := hKch τ hτ x' t' (lt_of_not_ge hcon)
      have h2 := hKcol τ hτ x t hge
      have h3 : (2 : ℝ) ≤ x ^ 2 := two_le_sq_of_sqrt_two_le_abs hge
      have h2' : Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ x' t') = -x ^ 2 / 2 := by
        rw [hK0, h2]
      linarith
    by_cases hxs : x ≤ 0
    · by_cases hxs' : x' ≤ 0
      · -- ## both on the left collar
        have hxle : x ≤ -Real.sqrt 2 := by
          have h := hge; rw [abs_of_nonpos hxs] at h; linarith
        have hxle' : x' ≤ -Real.sqrt 2 := by
          have h := hge'; rw [abs_of_nonpos hxs'] at h; linarith
        have heq : collarPt D.Γc D.Ac τ (sig x') t'
            = Work.RPV.Tk k (collarPt D.Γc D.Ac τ (sig x) t) := by
          have h0 := h
          rw [lagPt_collar_neg D τ x' t' hxle', lagPt_collar_neg D τ x t hxle] at h0
          exact h0
        obtain ⟨hsig, m, hm⟩ := collar_levelPt_inj CI a D τ hτ (sig x) (sig x') t t'
          (sig_nonneg_of_le hxle) (sig_nonneg_of_le hxle') k heq
        exact ⟨sig_inj_on hxle' hxle hsig.symm, ⟨m, hm⟩⟩
      · -- ## left collar against the right collar: impossible (`τ_π` would need `π ∈ 2πℤ`)
        exfalso
        have hxle : x ≤ -Real.sqrt 2 := by
          have h := hge; rw [abs_of_nonpos hxs] at h; linarith
        have hxpos' : 0 < x' := lt_of_not_ge hxs'
        have hxge' : Real.sqrt 2 ≤ x' := by
          have h := hge'; rw [abs_of_pos hxpos'] at h; exact h
        have hh : Work.RPV.tau Real.pi (collarPt D.Γc D.Ac τ (sig x') (t' - Real.pi))
            = Work.RPV.Tk k (collarPt D.Γc D.Ac τ (sig x) t) := by
          have h0 := h
          rw [lagPt_collar_pos D τ x' t' hxge', lagPt_collar_neg D τ x t hxle] at h0
          exact h0
        have h2 := congrArg (Work.RPV.tau (-Real.pi)) hh
        rw [Work.RPV.tau_neg, ← Work.RPV.Tk_tau] at h2
        exact collar_noSpurious_restricted D.Γc D.Ac D.hΓper D.hAper D.hemb τ hτ (sig x')
          (sig x) (t' - Real.pi) t k (-Real.pi) (sig_nonneg_of_ge hxge')
          (sig_nonneg_of_le hxle) ne_two_pi_mul_neg_pi h2
    · by_cases hxs' : x' ≤ 0
      · -- ## right collar against the left collar: impossible as well
        exfalso
        have hxpos : 0 < x := lt_of_not_ge hxs
        have hxge : Real.sqrt 2 ≤ x := by
          have h := hge; rw [abs_of_pos hxpos] at h; exact h
        have hxle' : x' ≤ -Real.sqrt 2 := by
          have h := hge'; rw [abs_of_nonpos hxs'] at h; linarith
        have hh : collarPt D.Γc D.Ac τ (sig x') t'
            = Work.RPV.Tk k
                (Work.RPV.tau Real.pi (collarPt D.Γc D.Ac τ (sig x) (t - Real.pi))) := by
          have h0 := h
          rw [lagPt_collar_neg D τ x' t' hxle', lagPt_collar_pos D τ x t hxge] at h0
          exact h0
        exact collar_noSpurious_restricted D.Γc D.Ac D.hΓper D.hAper D.hemb τ hτ (sig x')
          (sig x) t' (t - Real.pi) k Real.pi (sig_nonneg_of_le hxle')
          (sig_nonneg_of_ge hxge) ne_two_pi_mul_pi hh
      · -- ## both on the right collar: conjugate by `τ_π` and apply the left-collar statement
        have hxpos : 0 < x := lt_of_not_ge hxs
        have hxpos' : 0 < x' := lt_of_not_ge hxs'
        have hxge : Real.sqrt 2 ≤ x := by
          have h := hge; rw [abs_of_pos hxpos] at h; exact h
        have hxge' : Real.sqrt 2 ≤ x' := by
          have h := hge'; rw [abs_of_pos hxpos'] at h; exact h
        have heq : collarPt D.Γc D.Ac τ (sig x') (t' - Real.pi)
            = Work.RPV.Tk k (collarPt D.Γc D.Ac τ (sig x) (t - Real.pi)) := by
          have hh : Work.RPV.tau Real.pi (collarPt D.Γc D.Ac τ (sig x') (t' - Real.pi))
              = Work.RPV.Tk k
                  (Work.RPV.tau Real.pi (collarPt D.Γc D.Ac τ (sig x) (t - Real.pi))) := by
            have h0 := h
            rw [lagPt_collar_pos D τ x' t' hxge', lagPt_collar_pos D τ x t hxge] at h0
            exact h0
          have h2 := congrArg (Work.RPV.tau (-Real.pi)) hh
          rwa [Work.RPV.tau_neg, ← Work.RPV.Tk_tau, Work.RPV.tau_neg] at h2
        obtain ⟨hsig, m, hm⟩ := collar_levelPt_inj CI a D τ hτ (sig x) (sig x') (t - Real.pi)
          (t' - Real.pi) (sig_nonneg_of_ge hxge) (sig_nonneg_of_ge hxge') k heq
        refine ⟨(sig_inj_on_pos hxge hxge' hsig).symm, ⟨m, ?_⟩⟩
        linarith

end Work.RPB.B5
