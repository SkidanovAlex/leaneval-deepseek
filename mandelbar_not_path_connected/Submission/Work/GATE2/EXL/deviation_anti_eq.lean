/-
# GATE2 / EXL — the anti-symmetry of the `α`-Böttcher deviation along the square root

The parabolic flower `fl` of the root `z₁` carries an antiholomorphic *square root* `g` of the
second return map `F c = (T_c)^{10}`; for the mandelbar the root is `g = (T_c)^5`, and the flower
records the functional equation

```
fl.Ψ (star w + 1/2) = g (fl.Ψ w)          (fl.Ψ_anti)
```

(`star` is complex conjugation).  This module proves that under this anti-involution the
`α`-Böttcher deviation at the direction `α₁ = 371/1023` is *minus `32` times* the deviation at the
direction `α₂ = 404/1023`, at the level of the dynamical point `z = fl.Ψ w`:

```
deviation α₂ (g z) = −32 · deviation α₁ z.
```

## The mathematics

The critical Böttcher coordinate satisfies `φ (T_c z) = conj (φ z)^2` on the critical domain, so
along the odd iterate `g = (T_c)^5` the equation conjugates five times and

```
φ (g z) = conj (φ z)^{32}.
```

Writing `b := bAngle φ z = arg (φ z) / 2π`, this is the congruence `bAngle φ (g z) ≡ −32 b (mod 1)`.
The deviation is the representative `deviation φ α z = repPhase (bAngle φ z − α)` of the shifted
Böttcher argument.  Hence, with `δ := deviation φ α₁ z` (so `b = α₁ + δ + m`, `m ∈ ℤ`),

```
deviation φ α₂ (g z) = repPhase (−32 b − α₂)
                     = repPhase (−32 δ − (32 α₁ + α₂) − 32 m)
                     = repPhase (−32 δ),
```

because `32 α₁ + α₂ = 32·371/1023 + 404/1023 = 12276/1023 = 12` is an integer — the arithmetic
coincidence of the two root angles.  The hypothesis `|δ| < 1/64` puts `−32 δ` inside the window
`(−1/2, 1/2)`, so `repPhase (−32 δ) = −32 δ`, which is the claim.

## Main results

* `varphiCrit_Tantibar_five` — the five-fold Böttcher equation `φ (T_c^5 z) = conj (φ z)^32`;
* `bAngle_Tantibar_five` — the induced congruence of the Böttcher arguments;
* `repPhase_neg_mul_of_small`, `deviation_congr` — the elementary phase arithmetic;
* `deviation_anti_step` — the dynamical form;
* `deviation_anti_eq` — the requested statement.
-/
import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.GATE2.PathTransport.angle_F_iterate
import Submission.Work.GATE2.EXL.MinCrossing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## The five-fold Böttcher equation of the square root `g = (T_c)^5` -/

/-- **The Böttcher equation along the odd iterate `(T_c)^5`.**  Iterating the antiholomorphic
Böttcher equation `φ (T_c z) = conj (φ z)^2` an odd number (`5`) of times leaves one conjugation
and raises the exponent to `2^5 = 32`:
`φ ((T_c)^5 z) = conj (φ z)^32`.  (The two-step relation is `conj (conj w ^ 2) ^ 2 = w ^ 4`,
so the even part doubles the exponent to `4^m` and the last step adds the single conjugation.) -/
theorem varphiCrit_Tantibar_five {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    Work.Bottcher.varphiCrit c ((Tantibar c)^[5] z)
      = (starRingEnd ℂ) (Work.Bottcher.varphiCrit c z) ^ 32 := by
  -- the critical domain is `T_c`-invariant, so every iterate of `z` lies in it
  have hmem : ∀ k : ℕ, (Tantibar c)^[k] z ∈ Work.ParamRays.critDomain c := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact Work.ParamRays.Tantibar_mem_critDomain ih
  -- the even iterates: the exponent `4^m`
  have hEven : ∀ m : ℕ, Work.Bottcher.varphiCrit c ((Tantibar c)^[2*m] z)
      = (Work.Bottcher.varphiCrit c z)^(4^m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hmem2m : (Tantibar c)^[2*m] z ∈ Work.ParamRays.critDomain c := hmem (2*m)
      have hTmem : Tantibar c ((Tantibar c)^[2*m] z) ∈ Work.ParamRays.critDomain c :=
        Work.ParamRays.Tantibar_mem_critDomain hmem2m
      have hiter : (Tantibar c)^[2*(m+1)] z
          = Tantibar c (Tantibar c ((Tantibar c)^[2*m] z)) := by
        rw [show 2*(m+1) = 2 + 2*m from by ring, Function.iterate_add_apply,
          show (2:ℕ) = 1+1 from rfl, Function.iterate_add_apply, Function.iterate_one]
      rw [hiter, Work.Bottcher.varphiCrit_comm_Tantibar hTmem,
        Work.Bottcher.varphiCrit_comm_Tantibar hmem2m, ih]
      simp only [map_pow, starRingEnd_apply, star_star]
      rw [← pow_mul, ← pow_mul]
      rw [show (4:ℕ)^m * (2*2) = 4^(m+1) from by rw [pow_succ]]
  -- the odd iterates: one leftover conjugation, exponent `2 · 4^m`
  have hOdd : ∀ m : ℕ, Work.Bottcher.varphiCrit c ((Tantibar c)^[2*m+1] z)
      = (starRingEnd ℂ) (Work.Bottcher.varphiCrit c z)^(2 * 4^m) := by
    intro m
    have hmem2m : (Tantibar c)^[2*m] z ∈ Work.ParamRays.critDomain c := hmem (2*m)
    have hiter : (Tantibar c)^[2*m+1] z = Tantibar c ((Tantibar c)^[2*m] z) := by
      rw [Function.iterate_succ_apply']
    rw [hiter, Work.Bottcher.varphiCrit_comm_Tantibar hmem2m, hEven m]
    rw [map_pow, ← pow_mul]
    congr 1
    ring
  -- `5 = 2·2 + 1`
  exact hOdd 2

/-! ## The congruence of the Böttcher arguments -/

/-- **The congruence of the Böttcher argument under `g = (T_c)^5`.**  On the critical domain the
normalised Böttcher argument `bAngle φ z = arg (φ z) / 2π` satisfies

```
bAngle φ ((T_c)^5 z) = −32 · bAngle φ z + k,        k ∈ ℤ,
```

because `arg (conj w) = −arg w` and `arg (w^n) = n · arg w` modulo `2π`. -/
theorem bAngle_Tantibar_five {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    ∃ k : ℤ, Work.GATE.bAngle (Work.Bottcher.varphiCrit c) ((Tantibar c)^[5] z)
      = -(32:ℝ) * Work.GATE.bAngle (Work.Bottcher.varphiCrit c) z + (k:ℝ) := by
  have hfun := varphiCrit_Tantibar_five hz
  -- `(32 : ℕ) • (−(arg φ z : Angle)) = ((−32 · arg φ z) : Angle)`
  have hstep : (32 : ℕ) • (-(Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle))
      = ((-(32 : ℝ) * Complex.arg (Work.Bottcher.varphiCrit c z)) : Real.Angle) := by
    rw [← Real.Angle.coe_neg, ← Real.Angle.natCast_mul_eq_nsmul]
    congr 1
    ring
  -- the angle equation
  have hArg : (Complex.arg (Work.Bottcher.varphiCrit c ((Tantibar c)^[5] z)) : Real.Angle)
      = ((-(32 : ℝ) * Complex.arg (Work.Bottcher.varphiCrit c z)) : Real.Angle) := by
    rw [hfun, Complex.arg_pow_coe_angle, Complex.arg_conj_coe_angle, hstep]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hArg
  refine ⟨k, ?_⟩
  simp only [Work.GATE.bAngle]
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt Real.two_pi_pos
  field_simp
  linarith [hk]

/-! ## The elementary phase arithmetic -/

/-- **`repPhase` fixes `−32 d` when `|d| < 1/64`.**  Then `−32 d ∈ (−1/2, 1/2)`, which is
contained in the window `(−1/2, 1/2]` of the representative. -/
theorem repPhase_neg_mul_of_small {d : ℝ} (h : |d| < 1/64) :
    Work.GATE2.PhaseGap.repPhase (-(32:ℝ) * d) = -(32:ℝ) * d := by
  have h32 : |(-(32:ℝ)) * d| < 1 / 2 := by
    rw [abs_mul, show |(-(32:ℝ))| = 32 by norm_num]
    nlinarith [h, abs_nonneg d]
  rw [Work.GATE2.PhaseGap.repPhase, toIocMod_eq_self]
  have hh := abs_lt.mp h32
  constructor <;> linarith [hh.1, hh.2]

/-- **The phase-gap step for the anti-involution.**  If the Böttcher arguments satisfy
`bAngle φ w ≡ −32 · bAngle φ z (mod 1)` and `32 α + β = 12` is an integer, then the `β`-deviation
of `w` is `−32` times the `α`-deviation of `z`, provided the latter is small enough that
`−32 δ` fits in the fundamental window. -/
theorem deviation_congr {φ : ℂ → ℂ} {α β : ℝ} {z w : ℂ}
    (hb : ∃ k : ℤ, Work.GATE.bAngle φ w = -(32:ℝ) * Work.GATE.bAngle φ z + (k:ℝ))
    (hα : (32:ℝ) * α + β = 12)
    (hsmall : |Work.GATE.deviation φ α z| < 1/64) :
    Work.GATE.deviation φ β w = -(32:ℝ) * Work.GATE.deviation φ α z := by
  obtain ⟨k, hk⟩ := hb
  obtain ⟨m, hm⟩ := Work.GATE2.PhaseGap.exists_int_repPhase_sub (Work.GATE.bAngle φ z - α)
  -- `δ = (b − α) + m`, so `b = α + δ − m`
  have hd : Work.GATE.deviation φ α z = (Work.GATE.bAngle φ z - α) + (m : ℝ) := by
    rw [Work.GATE2.PhaseGap.deviation_eq_repPhase]; exact hm
  have hbz : Work.GATE.bAngle φ z = α + Work.GATE.deviation φ α z - (m:ℝ) := by linarith
  rw [Work.GATE2.PhaseGap.deviation_eq_repPhase φ β w, hk]
  rw [show (-(32:ℝ) * Work.GATE.bAngle φ z + (k:ℝ) - β)
      = (-(32:ℝ) * Work.GATE.bAngle φ z - β) + (k:ℝ) by ring,
    Work.GATE2.PhaseGap.repPhase_add_int]
  rw [hbz]
  -- `−32(α + δ − m) − β = (−32 δ) + (32 m − 12)`
  have hshift : (-(32:ℝ) * (α + Work.GATE.deviation φ α z - (m:ℝ)) - β)
      = (-(32:ℝ) * Work.GATE.deviation φ α z) + (((32:ℤ)*m - 12 : ℤ) : ℝ) := by
    push_cast
    linarith [hα]
  rw [hshift, Work.GATE2.PhaseGap.repPhase_add_int]
  exact repPhase_neg_mul_of_small hsmall

/-- **The anti-symmetry of the deviation along the square root `g = (T_c)^5`.**  For a point `z` of
the critical domain whose `α₁`-deviation is smaller than `1/64`,

```
deviation α₂ ((T_c)^5 z) = −32 · deviation α₁ z.
```

The arithmetic of the root angles is `32 α₁ + α₂ = 12`. -/
theorem deviation_anti_step {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c)
    (hsmall : |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 z| < 1 / 64) :
    Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2 ((Tantibar c)^[5] z)
      = -(32:ℝ) * Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 z := by
  have hb := bAngle_Tantibar_five hz
  have hα : (32:ℝ) * Work.EL.alpha1 + Work.EL.alpha2 = 12 := by
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  exact deviation_congr hb hα hsmall

/-! ## The requested statement -/

theorem deviation_anti_eq {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    {w : ℂ}
    (hcrit : fl.Ψ w ∈ Work.ParamRays.critDomain c)
    (hsmall : |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ w)| < 1 / 64) :
    Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2 (fl.Ψ (star w + 1 / 2)) =
      -(32 : ℝ) * Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ w) := by
  rw [fl.Ψ_anti w]
  exact deviation_anti_step hcrit hsmall

end Work.GATE2.EXL
