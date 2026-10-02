/-
# GATE2 — the integrality of the phase gap along the critical orbit

The `α`-relative Böttcher deviation `Work.GATE.deviation φ α z`
(`Submission/Work/GATE/Gate/Defs.lean`) is the representative of the shifted Böttcher argument
`bAngle φ z - α` in the window `(-1/2, 1/2]`.  The gate transport of `Submission/Work/GATE2/`
(`Submission/Work/GATE2/Window.lean`, field `hdev`) drives the *base window* of the gate backwards
along the critical orbit: the `m`-th iterate of the parameter `e` under the second return map
`F_e = (T_e)^{10}` has its Böttcher argument within `windowEps` of the direction `α`.  That
backwards iteration divides the deviation by `1024` at each step — and for this to be *consistent*
with the fact that the deviation always lies in `(-1/2, 1/2]`, the two normalisations must differ
by an **integer** at every step.  This module proves exactly that:

```
deviation α ((F_e)^[m] e) = 1024^m * deviation α e + j,      j ∈ ℤ,
```

for the root direction `α = 371/1023` of the proof of `mandelbar_not_path_connected`.

## The mathematics

`Work.GATE2.varphiCrit_F_iterate` is the functional equation of the critical Böttcher coordinate
along the high return map,

```
(φ_c e)^(1024^m) = φ_c ((F_c)^[m] e),
```

so the arguments are related by `arg φ_c ((F_c)^[m] e) ≡ 1024^m · arg φ_c e` modulo `2π`
(`Complex.arg_pow_coe_angle`), i.e. the *normalised* Böttcher arguments `bAngle` are congruent
modulo `1` after multiplication by `1024^m`.  Writing `rep` for the representative of a real in
`(-1/2, 1/2]` (`repPhase`), the deviation is `rep (bAngle - α)`, and

```
rep (1024^m · b - α)  vs  1024^m · rep (b - α)
```

differ by an integer exactly when `(1024^m - 1) α ∈ ℤ` — because `rep x - x ∈ ℤ` and `rep` is
invariant under integer translations.  That integrality is *the* arithmetic coincidence of the
root angle: `1023 α = 371` and `1023 ∣ 1024^m - 1` (as `1024 ≡ 1` modulo `1023`), so
`(1024^m - 1) α = 371 · ((1024^m - 1)/1023) ∈ ℤ` (`exists_int_pow_sub_one_mul`).

Everything is purely elementary: no dynamics beyond the functional equation above is used.

## Main results

* `Work.GATE2.PhaseGap.deviation_eq_repPhase`, `…repPhase_add_int`, `…exists_int_repPhase_sub`;
* `Work.GATE2.PhaseGap.exists_int_repPhase_comb` — the phase-gap step;
* `Work.GATE2.PhaseGap.exists_int_pow_sub_one_mul` — the integrality `(1024^m - 1) α ∈ ℤ`;
* `Work.GATE2.phase_gap_integrality` — the requested lemma.
-/
import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.varphiCrit_F_iterate
import Submission.Work.GATE2.deviation_continuousAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

/-! ## The vocabulary of the phase gap

The representative of a real number in the window `(-1/2, 1/2]`, of which the `α`-relative
deviation is an instance, and the arithmetic of that representative. -/

namespace PhaseGap

/-- The representative of a real number in the window `(-1/2, 1/2]`: `toIocMod` at period `1`
and left end `-1/2`. -/
def repPhase (x : ℝ) : ℝ := toIocMod (p := (1 : ℝ)) one_pos (-1 / 2) x

/-- **The deviation is the representative of the shifted Böttcher argument**:
`deviation φ α z = repPhase (bAngle φ z - α)`. -/
theorem deviation_eq_repPhase (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    Work.GATE.deviation φ α z = repPhase (Work.GATE.bAngle φ z - α) := by
  symm
  refine (toIocMod_eq_iff (p := (1 : ℝ)) one_pos (a := -1 / 2)
    (b := Work.GATE.bAngle φ z - α)).mpr ⟨?_, ?_⟩
  · obtain ⟨hlo, hhi⟩ := Work.GATE.deviation_mem φ α z
    refine ⟨by linarith, ?_⟩
    rw [show (-1 / 2 + 1 : ℝ) = 1 / 2 by norm_num]
    exact hhi
  · refine ⟨-⌊α - Work.GATE.bAngle φ z + 1 / 2⌋, ?_⟩
    rw [zsmul_eq_mul, mul_one, Work.GATE.deviation_def, Work.GATE.liftAngle]
    push_cast
    ring

/-- **The representative is invariant under integer translation** (period `1`). -/
theorem repPhase_add_int (x : ℝ) (m : ℤ) : repPhase (x + (m : ℝ)) = repPhase x := by
  show toIocMod (p := (1 : ℝ)) one_pos (-1 / 2) (x + (m : ℝ))
      = toIocMod (p := (1 : ℝ)) one_pos (-1 / 2) x
  simpa only [zsmul_eq_mul, mul_one] using
    (toIocMod_add_zsmul (p := (1 : ℝ)) one_pos (-1 / 2) x m)

/-- **The representative differs from the number by an integer.** -/
theorem exists_int_repPhase_sub (x : ℝ) : ∃ m : ℤ, repPhase x = x + (m : ℝ) := by
  refine ⟨-toIocDiv (p := (1 : ℝ)) one_pos (-1 / 2) x, ?_⟩
  have h := toIocMod_sub_self (p := (1 : ℝ)) one_pos (-1 / 2) x
  rw [zsmul_eq_mul, mul_one] at h
  show toIocMod (p := (1 : ℝ)) one_pos (-1 / 2) x
      = x + ((-toIocDiv (p := (1 : ℝ)) one_pos (-1 / 2) x : ℤ) : ℝ)
  linarith

/-- **The phase-gap step.**  If the Böttcher arguments `bz`, `bw` of two points are congruent
modulo the period `1` up to the factor `n` (`hb`), and if `(n - 1) α` is an integer (`hα`), then
the `α`-deviations of the two points differ by the factor `n` up to an integer. -/
theorem exists_int_repPhase_comb {α bw bz : ℝ} (n : ℕ)
    (hb : ∃ k : ℤ, bw = (n : ℝ) * bz + (k : ℝ))
    (hα : ∃ t : ℤ, ((n : ℝ) - 1) * α = (t : ℝ)) :
    ∃ j : ℤ, repPhase (bw - α) = (n : ℝ) * repPhase (bz - α) + (j : ℝ) := by
  obtain ⟨k, hk⟩ := hb
  obtain ⟨t, ht⟩ := hα
  obtain ⟨m₁, hm₁⟩ := exists_int_repPhase_sub (n * (bz - α))
  obtain ⟨m₂, hm₂⟩ := exists_int_repPhase_sub (bz - α)
  refine ⟨m₁ - (n : ℤ) * m₂, ?_⟩
  have h1 : repPhase (bw - α) = repPhase (n * bz - α) := by
    rw [hk, show n * bz + (k : ℝ) - α = (n * bz - α) + (k : ℝ) by ring]
    exact repPhase_add_int _ k
  have h2 : n * bz - α = n * (bz - α) + ((n : ℝ) - 1) * α := by ring
  have h3 : repPhase (n * bz - α) = repPhase (n * (bz - α)) := by
    rw [h2, ht]
    exact repPhase_add_int _ t
  rw [h1, h3, hm₁, hm₂]
  push_cast
  ring

/-- **The integrality of the phase gap.**  `1023 ∣ 1024^m - 1` (since `1024 ≡ 1` modulo `1023`)
and `1023 α = 371`, hence `(1024^m - 1) α = 371 · ((1024^m - 1)/1023)` is an integer. -/
theorem exists_int_pow_sub_one_mul {α : ℝ} (hα : 1023 * α = 371) (m : ℕ) :
    ∃ t : ℤ, ((((1024 ^ m : ℕ) : ℝ)) - 1) * α = (t : ℝ) := by
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (1024 : ℤ) 1 m
  have hq' : (1024 : ℤ) ^ m - 1 = 1023 * q := by simpa using hq
  have hqR : (1024 : ℝ) ^ m - 1 = 1023 * (q : ℝ) := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) hq'
    push_cast at h
    simpa using h
  have hcast : (((1024 ^ m : ℕ) : ℝ)) = (1024 : ℝ) ^ m := by push_cast; ring
  refine ⟨371 * q, ?_⟩
  rw [hcast, hqR]
  rw [show (1023 : ℝ) * (q : ℝ) * α = (q : ℝ) * (1023 * α) by ring, hα]
  push_cast
  ring

/-- The representative of `y` in `(-π, π]` expressed through `toIocDiv`: the form of
`toIocMod_sub_self` in which it is consumed to produce the integer of `arg (w^n) - n arg w`. -/
theorem toIocMod_two_pi_eq (y : ℝ) :
    toIocMod Real.two_pi_pos (-Real.pi) y
      = y + 2 * Real.pi * ((-toIocDiv Real.two_pi_pos (-Real.pi) y : ℤ) : ℝ) := by
  have h : toIocMod Real.two_pi_pos (-Real.pi) y
      = y + ((-toIocDiv Real.two_pi_pos (-Real.pi) y : ℤ) : ℝ) * (2 * Real.pi) := by
    have hh := toIocMod_sub_self (p := 2 * Real.pi) Real.two_pi_pos (-Real.pi) y
    rw [zsmul_eq_mul] at hh
    linarith
  rw [h]
  ring

end PhaseGap

/-- **The phase gap along the critical orbit is integral.**

The `m`-th iterate of the parameter `e` under the second return map `F_c = (T_c)^{10}` has
`α`-relative Böttcher deviation `1024^m` times that of `e`, up to an integer `j`.  This is the
consistency of the `1024`-fold refinement of the gate window with the normalisation of the
deviation, and it uses the arithmetic of the root angle `α = 371/1023`: `1023 α = 371` is an
integer while `1024^m ≡ 1` modulo `1023`, so `(1024^m - 1) α ∈ ℤ`. -/
theorem phase_gap_integrality {c : ℂ} {e : ℂ} (he : e ∈ Work.ParamRays.critDomain c) {α : ℝ}
    (hα : 1023 * α = 371) (m : ℕ) :
    ∃ j : ℤ, Work.GATE.deviation (Work.Bottcher.varphiCrit c) α ((Work.EL.F c)^[m] e) =
      (1024 : ℝ) ^ m * Work.GATE.deviation (Work.Bottcher.varphiCrit c) α e + j := by
  -- the functional equation of the critical Böttcher coordinate along the high return map
  have hpow : (Work.Bottcher.varphiCrit c e) ^ (1024 ^ m)
      = Work.Bottcher.varphiCrit c ((Work.EL.F c)^[m] e) := varphiCrit_F_iterate he m
  -- hence the arguments agree modulo `2π` after multiplication by `1024^m`
  have hang : (Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[m] e)) : Real.Angle)
      = (1024 ^ m) • (Complex.arg (Work.Bottcher.varphiCrit c e) : Real.Angle) := by
    rw [← hpow]
    exact Complex.arg_pow_coe_angle _ _
  -- in the window `(-π, π]`
  have hmain : Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[m] e))
      = toIocMod Real.two_pi_pos (-Real.pi)
          ((1024 : ℝ) ^ m * Complex.arg (Work.Bottcher.varphiCrit c e)) := by
    calc Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[m] e))
        = ((Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[m] e)) : Real.Angle)).toReal := by
            simp
      _ = (((1024 ^ m) • (Complex.arg (Work.Bottcher.varphiCrit c e) : Real.Angle))).toReal := by
            rw [hang]
      _ = (((((1024 ^ m : ℕ) : ℝ) * Complex.arg (Work.Bottcher.varphiCrit c e) : ℝ) :
              Real.Angle)).toReal := by
            rw [Real.Angle.natCast_mul_eq_nsmul]
      _ = toIocMod Real.two_pi_pos (-Real.pi)
            (((1024 ^ m : ℕ) : ℝ) * Complex.arg (Work.Bottcher.varphiCrit c e)) := by
            rw [Real.Angle.toReal_coe]
      _ = toIocMod Real.two_pi_pos (-Real.pi)
            ((1024 : ℝ) ^ m * Complex.arg (Work.Bottcher.varphiCrit c e)) := by
            rw [Nat.cast_pow, Nat.cast_ofNat]
  -- the integer in the argument equation
  have hargmod : ∃ k : ℤ, Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[m] e))
      = (1024 : ℝ) ^ m * Complex.arg (Work.Bottcher.varphiCrit c e) + 2 * Real.pi * (k : ℝ) := by
    refine ⟨-toIocDiv Real.two_pi_pos (-Real.pi)
      ((1024 : ℝ) ^ m * Complex.arg (Work.Bottcher.varphiCrit c e)), ?_⟩
    rw [hmain, PhaseGap.toIocMod_two_pi_eq]
  -- the same congruence for the normalised Böttcher arguments
  have hb : ∃ k : ℤ, Work.GATE.bAngle (Work.Bottcher.varphiCrit c) ((Work.EL.F c)^[m] e)
      = (((1024 ^ m : ℕ) : ℝ)) * Work.GATE.bAngle (Work.Bottcher.varphiCrit c) e + (k : ℝ) := by
    obtain ⟨k, hk⟩ := hargmod
    refine ⟨k, ?_⟩
    rw [Work.GATE.bAngle, Work.GATE.bAngle]
    push_cast
    rw [hk]
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt Real.two_pi_pos
    field_simp
  -- the arithmetic of the root angle
  have hintR := PhaseGap.exists_int_pow_sub_one_mul hα m
  have hint : ∃ t : ℤ, ((((1024 ^ m : ℕ) : ℝ)) - 1) * α = (t : ℝ) := by
    simpa [Nat.cast_pow, Nat.cast_ofNat] using hintR
  -- the phase-gap step
  obtain ⟨j, hj⟩ := PhaseGap.exists_int_repPhase_comb (α := α)
    (bw := Work.GATE.bAngle (Work.Bottcher.varphiCrit c) ((Work.EL.F c)^[m] e))
    (bz := Work.GATE.bAngle (Work.Bottcher.varphiCrit c) e) (n := 1024 ^ m) hb hint
  refine ⟨j, ?_⟩
  rw [PhaseGap.deviation_eq_repPhase (Work.Bottcher.varphiCrit c) α ((Work.EL.F c)^[m] e),
    PhaseGap.deviation_eq_repPhase (Work.Bottcher.varphiCrit c) α e]
  simpa [Nat.cast_pow, Nat.cast_ofNat] using hj

end Work.GATE2
