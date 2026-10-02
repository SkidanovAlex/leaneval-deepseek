/-
# ELAssembly — the level-`0` inputs of the arm chains, from the root-parabolic bundle

`Work.ELAssembly.armChainInputs_of` discharges, from the root-parabolic bundle
`d : Work.EL.RootParabolic c` alone, the six "level-`0`" fields that `ChainInputs` leaves as
inputs:

* the three co-landings of the level-`0` arm pairs
  `(armA1 0, armA2 0)`, `(armB1 0, armB2 0)`, `(armC1 0, armC2 0)`, and
* the non-degeneracy `arcLen (armX1 n) (armX2 n) ≠ 0` of the arm angles at every level.

## The mathematics

The level-`0` arm angles are exactly the first five iterates of the two root angles
`α₁ = 371/1023`, `α₂ = 404/1023` under the angle-doubling map `T θ = Int.fract (-2θ)`:

| arm | `armX1 0` | `armX2 0` |
|-----|-----------|-----------|
| `A` | `α₁`      | `α₂`      |
| `B` | `T²α₁`    | `T²α₂`    |
| `C` | `T⁴α₁`    | `T⁴α₂`    |

(using only the even iterates; the odd ones `T α₁ = 281/1023`, `T α₂ = 215/1023` lie in the other
half of the tripod).  The two root rays land at `d.z₁` (`d.rays`), and landing is equivariant
under `T_c` (`Work.ELNest.landsN_iterate`), so the rays of angles `T^{2k} α₁`, `T^{2k} α₂` land at
`(Tantibar c)^[2k] z₁`.  The non-degeneracy is a rational computation from the closed forms
`armA1_closed`, …, `armC2_closed`.

The bridge from the root-parabolic bundle to the `ELPull`-flavoured landing relation is
`Work.PortraitCount.landsN_elDynB` (the canonical `ELPull.DynB c` is `Work.PortraitCount.elDynB d`
by definition) composed with `Work.ELTop.landsN_iff_landsAt`.
-/
import Mathlib
import Submission.Work.ELAssembly.ELPullChains
import Submission.Work.ELAssembly.Instantiate
import Submission.Work.ELNest.Qp_shift
import Submission.Work.SeedDyn.Portrait
import Submission.Work.FSeed.RootParabolic
import Submission.Work.ELNest.armChain_nest
import Submission.Work.Landing.Angle.rootOrbit_pairs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.ELAssembly

/-! ## The bridge from `Work.EL.RootParabolic` to `Work.ELPull.LandsN` -/

/-- The canonical `ELPull`-flavoured landing relation at the root-parabolic bundle `d` agrees
with `Work.Landing.landsAt`: `hNcanOf d` is `Work.PortraitCount.elDynB d` by definition. -/
theorem landsN_can_iff_landsAt {c : ℂ} (d : Work.EL.RootParabolic c) (θ : ℝ) (y : ℂ) :
    Work.ELPull.LandsN (hNcanOf d) θ y ↔ Work.Landing.landsAt c θ y :=
  (Work.PortraitCount.landsN_elDynB d θ y).trans
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher θ y)

/-- Landing of the iterated ray: from `Work.EL.LandsN d.hN θ y` the ray of angle `T^[k] θ` lands
at `(Tantibar c)^[k] y`, transported to the `ELPull`-flavoured relation of `hNcanOf d`. -/
theorem landsN_can_iterate {c : ℂ} (d : Work.EL.RootParabolic c) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN d.hN θ y) (k : ℕ) :
    Work.ELPull.LandsN (hNcanOf d) (Work.EL.T^[k] θ) ((Tantibar c)^[k] y) :=
  (Work.PortraitCount.landsN_elDynB d _ _).mpr
    (Work.ELNest.landsN_iterate d.hN d.bottcher k h)

/-! ## The level-`0` arm angles

The level-`0` angles are the exact rationals of the certificate; the closed forms of
`Submission/Work/ELNest/armChain_nest.lean` reduce them at `n = 0` to the displayed values. -/

theorem armA1_zero_angle : Work.ELNest.armA1 0 = Work.EL.alpha1 := by
  rw [Work.ELNest.armA1_closed 0]; norm_num [Work.EL.alpha1]

theorem armA2_zero_angle : Work.ELNest.armA2 0 = Work.EL.alpha2 := by
  rw [Work.ELNest.armA2_closed 0]; norm_num [Work.EL.alpha2]

theorem armB1_zero_angle : Work.ELNest.armB1 0 = 461 / 1023 := by
  rw [Work.ELNest.armB1_closed 0]; norm_num

theorem armB2_zero_angle : Work.ELNest.armB2 0 = 593 / 1023 := by
  rw [Work.ELNest.armB2_closed 0]; norm_num

theorem armC1_zero_angle : Work.ELNest.armC1 0 = 821 / 1023 := by
  rw [Work.ELNest.armC1_closed 0]; norm_num

theorem armC2_zero_angle : Work.ELNest.armC2 0 = 326 / 1023 := by
  rw [Work.ELNest.armC2_closed 0]; norm_num

/-! ## The angle orbit of the root angles

The first five iterates of the doubling map on the two root angles
(`Work.Landing.Angle.rootOrbit_pairs`), read off against `Work.EL.alpha1 = 371/1023`,
`Work.EL.alpha2 = 404/1023`. -/

theorem alpha_T2_first : Work.EL.T^[2] Work.EL.alpha1 = 461 / 1023 :=
  (Prod.ext_iff.mp Work.Landing.Angle.rootOrbit_pairs.2.1).1

theorem alpha_T2_second : Work.EL.T^[2] Work.EL.alpha2 = 593 / 1023 :=
  (Prod.ext_iff.mp Work.Landing.Angle.rootOrbit_pairs.2.1).2

theorem alpha_T4_first : Work.EL.T^[4] Work.EL.alpha1 = 821 / 1023 :=
  (Prod.ext_iff.mp Work.Landing.Angle.rootOrbit_pairs.2.2.2.1).1

theorem alpha_T4_second : Work.EL.T^[4] Work.EL.alpha2 = 326 / 1023 :=
  (Prod.ext_iff.mp Work.Landing.Angle.rootOrbit_pairs.2.2.2.1).2

/-! ## Non-degeneracy of the arm angles

`Work.EL.arcLen a b = Int.fract (b - a)`, and the closed forms give, with `t = (64ⁿ)⁻¹ ∈ (0,1]`,

* `armA2 n - armA1 n = 1/21 - (330/21483) t ∈ (0,1)`,
* `armB2 n - armB1 n = 4/21 - (1320/21483) t ∈ (0,1)`,
* `armC2 n - armC1 n = -(5/21 + (5280/21483) t) ∈ (-1,0)`,

so that the fractional part is the difference in the first two cases and the difference plus one
in the third; in each case it is strictly positive. -/

theorem arcLen_armA_ne_zero (n : ℕ) :
    Work.EL.arcLen (Work.ELNest.armA1 n) (Work.ELNest.armA2 n) ≠ 0 := by
  rw [Work.EL.arcLen, Work.ELNest.armA1_closed n, Work.ELNest.armA2_closed n]
  have ht1 : ((64 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hle : (330 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ ≤ (330 : ℝ) / 21483 :=
    mul_le_of_le_one_right (by norm_num) ht1
  have hpos : 0 < 1 / 21 - (330 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ := by linarith
  have hlt : 1 / 21 - (330 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ < 1 := by
    have hnn : 0 ≤ (330 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ :=
      mul_nonneg (by norm_num) (by positivity)
    linarith
  rw [show (25 : ℝ) / 63 - 41 / 21483 * ((64 : ℝ) ^ n)⁻¹
        - (22 / 63 + 289 / 21483 * ((64 : ℝ) ^ n)⁻¹)
      = 1 / 21 - 330 / 21483 * ((64 : ℝ) ^ n)⁻¹ by ring]
  rw [Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt⟩]
  linarith

theorem arcLen_armB_ne_zero (n : ℕ) :
    Work.EL.arcLen (Work.ELNest.armB1 n) (Work.ELNest.armB2 n) ≠ 0 := by
  rw [Work.EL.arcLen, Work.ELNest.armB1_closed n, Work.ELNest.armB2_closed n]
  have ht1 : ((64 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hle : (1320 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ ≤ (1320 : ℝ) / 21483 :=
    mul_le_of_le_one_right (by norm_num) ht1
  have hpos : 0 < 4 / 21 - (1320 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ := by linarith
  have hlt : 4 / 21 - (1320 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ < 1 := by
    have hnn : 0 ≤ (1320 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ :=
      mul_nonneg (by norm_num) (by positivity)
    linarith
  rw [show (37 : ℝ) / 63 - 164 / 21483 * ((64 : ℝ) ^ n)⁻¹
        - (25 / 63 + 1156 / 21483 * ((64 : ℝ) ^ n)⁻¹)
      = 4 / 21 - 1320 / 21483 * ((64 : ℝ) ^ n)⁻¹ by ring]
  rw [Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt⟩]
  linarith

theorem arcLen_armC_ne_zero (n : ℕ) :
    Work.EL.arcLen (Work.ELNest.armC1 n) (Work.ELNest.armC2 n) ≠ 0 := by
  rw [Work.EL.arcLen, Work.ELNest.armC1_closed n, Work.ELNest.armC2_closed n]
  have hle : (5280 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ ≤ (5280 : ℝ) / 21483 :=
    mul_le_of_le_one_right (by norm_num) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hgt : -1 < (22 : ℝ) / 63 - 656 / 21483 * ((64 : ℝ) ^ n)⁻¹
      - (37 / 63 + 4624 / 21483 * ((64 : ℝ) ^ n)⁻¹) := by
    rw [show (22 : ℝ) / 63 - 656 / 21483 * ((64 : ℝ) ^ n)⁻¹
          - (37 / 63 + 4624 / 21483 * ((64 : ℝ) ^ n)⁻¹)
        = -(5 / 21 + 5280 / 21483 * ((64 : ℝ) ^ n)⁻¹) by ring]
    linarith
  have hlt : (22 : ℝ) / 63 - 656 / 21483 * ((64 : ℝ) ^ n)⁻¹
      - (37 / 63 + 4624 / 21483 * ((64 : ℝ) ^ n)⁻¹) < 0 := by
    have hnn : 0 ≤ (5280 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ :=
      mul_nonneg (by norm_num) (by positivity)
    rw [show (22 : ℝ) / 63 - 656 / 21483 * ((64 : ℝ) ^ n)⁻¹
          - (37 / 63 + 4624 / 21483 * ((64 : ℝ) ^ n)⁻¹)
        = -(5 / 21 + 5280 / 21483 * ((64 : ℝ) ^ n)⁻¹) by ring]
    linarith
  have hf : Int.fract ((22 : ℝ) / 63 - 656 / 21483 * ((64 : ℝ) ^ n)⁻¹
        - (37 / 63 + 4624 / 21483 * ((64 : ℝ) ^ n)⁻¹))
      = ((22 : ℝ) / 63 - 656 / 21483 * ((64 : ℝ) ^ n)⁻¹
        - (37 / 63 + 4624 / 21483 * ((64 : ℝ) ^ n)⁻¹)) + 1 :=
    Int.fract_eq_iff.mpr ⟨by linarith, by linarith, -1, by ring⟩
  rw [hf]
  linarith

/-! ## The statement -/

theorem armChainInputs_of {c : ℂ} (d : Work.EL.RootParabolic c) : ((∃ y : ℂ, Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (Work.ELNest.armA1 0) y ∧ Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (Work.ELNest.armA2 0) y) ∧ (∃ y : ℂ, Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (Work.ELNest.armB1 0) y ∧ Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (Work.ELNest.armB2 0) y) ∧ (∃ y : ℂ, Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (Work.ELNest.armC1 0) y ∧ Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (Work.ELNest.armC2 0) y)) ∧ ((∀ n : ℕ, Work.EL.arcLen (Work.ELNest.armA1 n) (Work.ELNest.armA2 n) ≠ 0) ∧ (∀ n : ℕ, Work.EL.arcLen (Work.ELNest.armB1 n) (Work.ELNest.armB2 n) ≠ 0) ∧ (∀ n : ℕ, Work.EL.arcLen (Work.ELNest.armC1 n) (Work.ELNest.armC2 n) ≠ 0)) := by
  have hP0 : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 d.z₁).mpr d.rays.1
  have hP0b : Work.EL.LandsN d.hN Work.EL.alpha2 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha2 d.z₁).mpr d.rays.2
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- arm `A`: the root rays themselves
    refine ⟨d.z₁, ?_, ?_⟩
    · rw [armA1_zero_angle]
      exact (landsN_can_iff_landsAt d Work.EL.alpha1 d.z₁).mpr d.rays.1
    · rw [armA2_zero_angle]
      exact (landsN_can_iff_landsAt d Work.EL.alpha2 d.z₁).mpr d.rays.2
  · -- arm `B`: the two-step images of the root rays
    have hs1 := landsN_can_iterate d hP0 2
    have hs2 := landsN_can_iterate d hP0b 2
    rw [alpha_T2_first] at hs1
    rw [alpha_T2_second] at hs2
    refine ⟨(Tantibar c)^[2] d.z₁, ?_, ?_⟩
    · rw [armB1_zero_angle]; exact hs1
    · rw [armB2_zero_angle]; exact hs2
  · -- arm `C`: the four-step images of the root rays
    have hs1 := landsN_can_iterate d hP0 4
    have hs2 := landsN_can_iterate d hP0b 4
    rw [alpha_T4_first] at hs1
    rw [alpha_T4_second] at hs2
    refine ⟨(Tantibar c)^[4] d.z₁, ?_, ?_⟩
    · rw [armC1_zero_angle]; exact hs1
    · rw [armC2_zero_angle]; exact hs2
  · intro n; exact arcLen_armA_ne_zero n
  · intro n; exact arcLen_armB_ne_zero n
  · intro n; exact arcLen_armC_ne_zero n

end Work.ELAssembly
