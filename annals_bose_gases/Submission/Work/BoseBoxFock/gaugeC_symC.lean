import Mathlib.Tactic.IntervalCases
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.GaugeWt
import Submission.Work.BoseBoxFock.gaugeCoeff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.gaugeC_symC` — the gauge turns the complex symbol into the real one

FS's reduction of `thm:Kafz` to a nonnegative coherent parameter: on the operator level
the substitution `z = r u` with `u` of unit modulus replaces the complex symbol `symC z`
(the anti-Wick symbol `Σ_i z^{p_i} z̄^{q_i} KvecF i`) by the real one
`symR r = Σ_i r^{p_i+q_i} KvecF i`, *intertwining* the gauge `gaugeC u`:

  `gaugeC u (symC (r*u) w) = symR r (gaugeC u w)`.

The proof expands both symbols over `Finset.range 25` and uses that the dictionary slot
`KvecF i` is gauge-homogeneous of weight `qvecF i - pvecF i` (`gaugeWt_KvecF_slots`
below, from the weight lemmas of `Work.BoseBoxFock.GaugeWt`), i.e.
`gaugeC u (KvecF i w) = u^(q_i - p_i) • KvecF i (gaugeC u w)`; the remaining scalar
identity `(r u)^{p} (r ū)^{q} u^{q-p} = r^{p+q}` for `u ū = 1` is
`Work.BoseBoxFock.gaugeCoeff`.
-/

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

section Slots

variable {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {f g : Mode → Fin m → ℝ} {BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)}
variable {PHs : Finset Mode} {E : Work.BoseB7.Q3Env Mode} {gHat0 : ℝ} {u : ℂ}
variable {hBNH : ∀ w : cfock (Excited m),
  gaugeC (Excited m) u (BNH w) = BNH (gaugeC (Excited m) u w)}

/-- **The gauge weight of the dictionary slots.**  Each of the 25 anti-normal slots
`KvecF i` of `KafzDict` has gauge weight `qvecF i - pvecF i`, the weight that makes the
monomial `a₀^(pvecF i) (a₀†)^(qvecF i) KvecF i` gauge invariant; the slot
`i = 2` is the high-momentum operator, whose gauge invariance is the hypothesis `hBNH`.
The proof is a 25-case split on the pattern match defining `KvecF`, each case one of the
weight lemmas of `GaugeWt.lean` (possibly multiplied by a scalar). -/
theorem gaugeWt_KvecF_slots (hu : u ≠ 0) (hBNH : ∀ w : cfock (Excited m),
      gaugeC (Excited m) u (BNH w) = BNH (gaugeC (Excited m) u w))
    (i : ℕ) (hi : i < 25) :
    GaugeWt u (KvecF f g BNH PHs E gHat0 i) ((qvecF i : ℤ) - (pvecF i : ℤ)) := by
  interval_cases i
  · rw [KvecF_0,
      show ((qvecF 0 : ℤ) - (pvecF 0 : ℤ)) = 0 by simp only [qvecF_0, pvecF_0]; norm_num]
    exact gaugeWt_Bkin (m := m) hu f E
  · rw [KvecF_1,
      show ((qvecF 1 : ℤ) - (pvecF 1 : ℤ)) = 0 by simp only [qvecF_1, pvecF_1]; norm_num]
    exact gaugeWt_smul (gaugeWt_Bgap (m := m) hu) ((E.b / (2 * E.ell ^ 2) : ℝ) : ℂ)
  · rw [KvecF_2,
      show ((qvecF 2 : ℤ) - (pvecF 2 : ℤ)) = 0 by simp only [qvecF_2, pvecF_2]; norm_num]
    exact gaugeWt_smul (gaugeWt_of_comm (Mode := Mode) hBNH)
      ((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) : ℝ) : ℂ)
  · rw [KvecF_3,
      show ((qvecF 3 : ℤ) - (pvecF 3 : ℤ)) = 0 by simp only [qvecF_3, pvecF_3]; norm_num]
    exact gaugeWt_smul (gaugeWt_one (X := Excited m) u) (cHCF E gHat0 : ℂ)
  · rw [KvecF_4,
      show ((qvecF 4 : ℤ) - (pvecF 4 : ℤ)) = 0 by simp only [qvecF_4, pvecF_4]; norm_num]
    exact gaugeWt_smul (gaugeWt_smul (gaugeWt_one (X := Excited m) u) (4 : ℂ))
      (-(cHCF E gHat0 : ℂ))
  · rw [KvecF_5,
      show ((qvecF 5 : ℤ) - (pvecF 5 : ℤ)) = 0 by simp only [qvecF_5, pvecF_5]; norm_num]
    exact gaugeWt_smul (gaugeWt_smul (gaugeWt_one (X := Excited m) u) (2 : ℂ))
      (cHCF E gHat0 : ℂ)
  · rw [KvecF_6,
      show ((qvecF 6 : ℤ) - (pvecF 6 : ℤ)) = 0 by simp only [qvecF_6, pvecF_6]; norm_num]
    exact gaugeWt_smul (gaugeWt_one (X := Excited m) u) (cMuF E gHat0 : ℂ)
  · rw [KvecF_7,
      show ((qvecF 7 : ℤ) - (pvecF 7 : ℤ)) = 0 by simp only [qvecF_7, pvecF_7]; norm_num]
    exact gaugeWt_smul (gaugeWt_one (X := Excited m) u) ((cMuF E gHat0 : ℂ) * (-1 : ℂ))
  · rw [KvecF_8,
      show ((qvecF 8 : ℤ) - (pvecF 8 : ℤ)) = 0 by simp only [qvecF_8, pvecF_8]; norm_num]
    exact gaugeWt_smul (gaugeWt_BW (m := m) hu (Finset.univ : Finset Mode)
      (fun k => E.W1 k + E.W1omega k) f) (i3F E : ℂ)
  · rw [KvecF_9,
      show ((qvecF 9 : ℤ) - (pvecF 9 : ℤ)) = 0 by simp only [qvecF_9, pvecF_9]; norm_num]
    exact gaugeWt_smul (gaugeWt_BW (m := m) hu (Finset.univ : Finset Mode)
      (fun k => E.W1 k + E.W1omega k) f) (((-(i3F E) : ℝ)) : ℂ)
  · rw [KvecF_10,
      show ((qvecF 10 : ℤ) - (pvecF 10 : ℤ)) = 2 by simp only [qvecF_10, pvecF_10]; norm_num]
    exact gaugeWt_smul (gaugeWt_Bbog1 (m := m) hu (Finset.univ : Finset Mode)
      (fun k => E.W1 k) f) (((1 / 2 : ℝ) * i3F E : ℝ) : ℂ)
  · rw [KvecF_11,
      show ((qvecF 11 : ℤ) - (pvecF 11 : ℤ)) = -2 by simp only [qvecF_11, pvecF_11]; norm_num]
    exact gaugeWt_smul (gaugeWt_Bbog2 (m := m) hu (Finset.univ : Finset Mode)
      (fun k => E.W1 k) f) (((1 / 2 : ℝ) * i3F E : ℝ) : ℂ)
  · rw [KvecF_12, Bc8,
      show ((qvecF 12 : ℤ) - (pvecF 12 : ℤ)) = -1 by simp only [qvecF_12, pvecF_12]; norm_num]
    exact gaugeWt_BchiC (m := m) hu (Finset.univ : Finset Mode) E.hatChi (i3F E * E.W1 0) f
  · rw [KvecF_13, Bc8',
      show ((qvecF 13 : ℤ) - (pvecF 13 : ℤ)) = -1 by simp only [qvecF_13, pvecF_13]; norm_num]
    exact gaugeWt_neg (gaugeWt_BchiC (m := m) hu (Finset.univ : Finset Mode) E.hatChi
      (2 * (i3F E * E.W1 0) + E.mu * E.W1 0) f)
  · rw [KvecF_14, Ba8,
      show ((qvecF 14 : ℤ) - (pvecF 14 : ℤ)) = 1 by simp only [qvecF_14, pvecF_14]; norm_num]
    exact gaugeWt_BchiA (m := m) hu (Finset.univ : Finset Mode) E.hatChi (i3F E * E.W1 0) f
  · rw [KvecF_15, Ba8',
      show ((qvecF 15 : ℤ) - (pvecF 15 : ℤ)) = 1 by simp only [qvecF_15, pvecF_15]; norm_num]
    exact gaugeWt_neg (gaugeWt_BchiA (m := m) hu (Finset.univ : Finset Mode) E.hatChi
      (2 * (i3F E * E.W1 0) + E.mu * E.W1 0) f)
  · rw [KvecF_16, Bc9,
      show ((qvecF 16 : ℤ) - (pvecF 16 : ℤ)) = -1 by simp only [qvecF_16, pvecF_16]; norm_num]
    exact gaugeWt_BchiC (m := m) hu (Work.BoseB7.excited Mode) E.hatChiSq
      (i3F E * E.W1omega0) g
  · rw [KvecF_17, Bc9',
      show ((qvecF 17 : ℤ) - (pvecF 17 : ℤ)) = -1 by simp only [qvecF_17, pvecF_17]; norm_num]
    exact gaugeWt_neg (gaugeWt_BchiC (m := m) hu (Work.BoseB7.excited Mode) E.hatChiSq
      (2 * (i3F E * E.W1omega0) + 0) g)
  · rw [KvecF_18, Ba9,
      show ((qvecF 18 : ℤ) - (pvecF 18 : ℤ)) = 1 by simp only [qvecF_18, pvecF_18]; norm_num]
    exact gaugeWt_BchiA (m := m) hu (Work.BoseB7.excited Mode) E.hatChiSq
      (i3F E * E.W1omega0) g
  · rw [KvecF_19, Ba9',
      show ((qvecF 19 : ℤ) - (pvecF 19 : ℤ)) = 1 by simp only [qvecF_19, pvecF_19]; norm_num]
    exact gaugeWt_neg (gaugeWt_BchiA (m := m) hu (Work.BoseB7.excited Mode) E.hatChiSq
      (2 * (i3F E * E.W1omega0) + 0) g)
  · rw [KvecF_20,
      show ((qvecF 20 : ℤ) - (pvecF 20 : ℤ)) = 0 by simp only [qvecF_20, pvecF_20]; norm_num]
    exact gaugeWt_smul (gaugeWt_BW (m := m) hu (Finset.univ : Finset Mode)
      (fun _ => (1 : ℝ)) f) (((i3F E * (E.W1 0 + E.W1omega0) : ℝ)) : ℂ)
  · rw [KvecF_21,
      show ((qvecF 21 : ℤ) - (pvecF 21 : ℤ)) = 0 by simp only [qvecF_21, pvecF_21]; norm_num]
    exact gaugeWt_smul (gaugeWt_BW (m := m) hu (Finset.univ : Finset Mode)
      (fun _ => (1 : ℝ)) f) (((-(i3F E * (E.W1 0 + E.W1omega0)) : ℝ)) : ℂ)
  · rw [KvecF_22,
      show ((qvecF 22 : ℤ) - (pvecF 22 : ℤ)) = 0 by simp only [qvecF_22, pvecF_22]; norm_num]
    exact gaugeWt_smul (gaugeWt_BW (m := m) hu (Finset.univ : Finset Mode)
      (fun _ => (1 : ℝ)) f) (((-(E.mu * E.W1 0) : ℝ)) : ℂ)
  · rw [KvecF_23,
      show ((qvecF 23 : ℤ) - (pvecF 23 : ℤ)) = 1 by simp only [qvecF_23, pvecF_23]; norm_num]
    exact gaugeWt_BQ3a (m := m) hu (Work.BoseB7.excited Mode) PHs
      (fun s k => i3F E * (E.fL s * E.W1 k)) g f
  · rw [KvecF_24,
      show ((qvecF 24 : ℤ) - (pvecF 24 : ℤ)) = -1 by simp only [qvecF_24, pvecF_24]; norm_num]
    exact gaugeWt_BQ3b (m := m) hu (Work.BoseB7.excited Mode) PHs
      (fun s k => i3F E * (E.fL s * E.W1 k)) g f

end Slots

theorem gaugeC_symC {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f g : Mode → Fin m → ℝ)
    (BNH : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 r : ℝ) (u : ℂ)
    (hu : u * starRingEnd ℂ u = 1)
    (hBNH : ∀ w : Work.BoseB4.cfock (Work.BoseB4.Excited m),
      Work.BoseBoxFock.gaugeC (Work.BoseB4.Excited m) u (BNH w)
        = BNH (Work.BoseBoxFock.gaugeC (Work.BoseB4.Excited m) u w)) :
    ∀ w : Work.BoseB4.cfock (Work.BoseB4.Excited m),
      Work.BoseBoxFock.gaugeC (Work.BoseB4.Excited m) u
          (Work.BoseBoxFock.symC f g BNH PHs E gHat0 ((r : ℂ) * u) w)
        = Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
            (Work.BoseBoxFock.gaugeC (Work.BoseB4.Excited m) u w) := by
  intro w
  -- `u` has unit modulus, hence is nonzero
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  -- the gauge weight of the `i`-th dictionary slot
  have hw : ∀ i ∈ Finset.range 25,
      GaugeWt u (KvecF f g BNH PHs E gHat0 i) ((qvecF i : ℤ) - (pvecF i : ℤ)) :=
    fun i hi => gaugeWt_KvecF_slots (m := m) (f := f) (g := g) (BNH := BNH) (PHs := PHs)
      (E := E) (gHat0 := gHat0) hu0 hBNH i (Finset.mem_range.mp hi)
  rw [symC, symR]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, hw i hi, smul_smul, gaugeCoeff u hu r (pvecF i) (qvecF i)]

end Work.BoseBoxFock
