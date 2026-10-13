import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.c_bounds
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.rhs_jet_aux` — the analytic and `Jet`-closure helpers of
`rhs_jet_of_parts`

This is the auxiliary module of `Submission/Work/FTS/RegPkgGal/Der/rhs_jet_of_parts.lean`.

It contains

* the elementary analytic facts about `θ ↦ Γ(θ)/c(3α) = (sin θ cos²θ)^α/c(3α)` and
  `z ↦ 2z²/(1+z)³` that give the bound and the `α`-Hölder modulus of the coercivity correction
  `AK α z θ = (Γ(θ)/c)·2z²/(1+z)³` (`rhsJet_ak_bounds`);
* the `Jet`-closure API used by the assembly: `rhsJet_add` (sum), `rhsJet_neg` (negation),
  `rhsJet_congr` (transport along a pointwise equality) and `rhsJet_mul` (multiplication by a
  bounded `α`-Hölder scalar depending on `τ` only).

All declarations are prefixed `rhsJet_` so as not to collide with the delegations
`Work.FTS.RegPkgGal.Der.{gam_div_c_holder,zsqCube_holder}` that prove the two `θ`- and
`z`-estimates independently.
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

/-! ## Elementary analytic helpers -/

/-- `|u^α - v^α| ≤ |u - v|^α` for `u, v ≥ 0` and `0 < α ≤ 1` (concavity of `t ↦ t^α`). -/
theorem rhsJet_rpow_abs_sub_le {α x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : |x ^ α - y ^ α| ≤ |x - y| ^ α := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → |a ^ α - b ^ α| ≤ |a - b| ^ α := by
    intro a b ha hb
    wlog h : b ≤ a generalizing a b with H
    · rw [abs_sub_comm, abs_sub_comm a b]
      exact H b a hb ha (not_le.mp h).le
    · have h1 : a ^ α ≤ (a - b) ^ α + b ^ α := by
        have := Real.rpow_add_le_add_rpow (sub_nonneg.mpr h) hb hα0.le hα1
        rwa [sub_add_cancel] at this
      have h2 : b ^ α ≤ a ^ α := Real.rpow_le_rpow hb h hα0.le
      have h3 : 0 ≤ a - b := sub_nonneg.mpr h
      rw [abs_of_nonneg (sub_nonneg.mpr h2), abs_of_nonneg h3]
      linarith
  exact key x y hx hy

/-- `θ ↦ sin θ cos²θ` is `3`-Lipschitz on `ℝ` (product rule, with the `1`-Lipschitz continuity of
`sin` and `cos`). -/
theorem rhsJet_sin_cos_sq_lipschitz (θ θ' : ℝ) :
    |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ≤ 3 * |θ - θ'| := by
  have hs : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := by
    have h := Real.lipschitzWith_sin.dist_le_mul θ θ'
    simpa [Real.dist_eq] using h
  have hc : |Real.cos θ - Real.cos θ'| ≤ |θ - θ'| := by
    have h := Real.lipschitzWith_cos.dist_le_mul θ θ'
    simpa [Real.dist_eq] using h
  have hc1 : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hc2 : |Real.cos θ'| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ', Real.cos_le_one θ'⟩
  have hcos2 : |Real.cos θ ^ 2 - Real.cos θ' ^ 2| ≤ 2 * |θ - θ'| := by
    have h : Real.cos θ ^ 2 - Real.cos θ' ^ 2
        = (Real.cos θ - Real.cos θ') * (Real.cos θ + Real.cos θ') := by ring
    rw [h, abs_mul]
    have h1 : |Real.cos θ + Real.cos θ'| ≤ 2 := by
      calc |Real.cos θ + Real.cos θ'| ≤ |Real.cos θ| + |Real.cos θ'| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add hc1 hc2
        _ = 2 := by norm_num
    calc |Real.cos θ - Real.cos θ'| * |Real.cos θ + Real.cos θ'| ≤ |θ - θ'| * 2 :=
          mul_le_mul hc h1 (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |θ - θ'| := by ring
  have hsq : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_sq]; nlinarith [abs_le.mp hc1]
  have hs1 : |Real.sin θ'| ≤ 1 := by
    rw [abs_le]; exact ⟨Real.neg_one_le_sin θ', Real.sin_le_one θ'⟩
  rw [show Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2
      = (Real.sin θ - Real.sin θ') * Real.cos θ ^ 2
        + Real.sin θ' * (Real.cos θ ^ 2 - Real.cos θ' ^ 2) by ring]
  calc |(Real.sin θ - Real.sin θ') * Real.cos θ ^ 2
        + Real.sin θ' * (Real.cos θ ^ 2 - Real.cos θ' ^ 2)|
      ≤ |(Real.sin θ - Real.sin θ') * Real.cos θ ^ 2|
        + |Real.sin θ' * (Real.cos θ ^ 2 - Real.cos θ' ^ 2)| := abs_add_le _ _
    _ = |Real.sin θ - Real.sin θ'| * |Real.cos θ ^ 2|
        + |Real.sin θ'| * |Real.cos θ ^ 2 - Real.cos θ' ^ 2| := by rw [abs_mul, abs_mul]
    _ ≤ |θ - θ'| * 1 + 1 * (2 * |θ - θ'|) :=
        add_le_add (mul_le_mul hs hsq (abs_nonneg _) (abs_nonneg _))
          (mul_le_mul hs1 hcos2 (abs_nonneg _) (by norm_num))
    _ = 3 * |θ - θ'| := by ring

/-- `θ ↦ Γ(θ)/c(3α)` is `40`-Hölder with exponent `α` on `Iθ`, for `0 < α ≤ 1/3`.  This is
`|u^α - v^α| ≤ |u - v|^α` for `u = sin θ cos²θ`, the `3`-Lipschitz bound on `u` and
`1/10 ≤ c(3α)`. -/
theorem rhsJet_gam_div_c_holder {α θ θ' : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ / Work.Spaces.c (Work.FTS.Regularity.pExp α)
      - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
    ≤ 40 * |θ - θ'| ^ α := by
  have hα1 : α ≤ 1 := by linarith
  have hP : 0 < Work.FTS.Regularity.pExp α := by rw [Work.FTS.Regularity.pExp]; linarith
  have hP1 : Work.FTS.Regularity.pExp α ≤ 1 := by rw [Work.FTS.Regularity.pExp]; linarith
  obtain ⟨hc1, hc10⟩ := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hP hP1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith
  have hG : ∀ φ : ℝ, Work.Spaces.Gam (Work.FTS.Regularity.pExp α) φ
      = (Real.sin φ * Real.cos φ ^ 2) ^ α := by
    intro φ
    rw [Work.Spaces.Gam, Work.FTS.Regularity.pExp]
    norm_num
  have hs0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    exact mul_nonneg hs (by positivity)
  have hs0' : 0 ≤ Real.sin θ' * Real.cos θ' ^ 2 := by
    have hs : 0 ≤ Real.sin θ' := Real.sin_nonneg_of_mem_Icc ⟨hθ'.1, by linarith [hθ'.2, Real.pi_pos]⟩
    exact mul_nonneg hs (by positivity)
  have hbase : |(Real.sin θ * Real.cos θ ^ 2) ^ α - (Real.sin θ' * Real.cos θ' ^ 2) ^ α|
      ≤ |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α :=
    rhsJet_rpow_abs_sub_le hs0 hs0' hα hα1
  have hlip : |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α
      ≤ (3 * |θ - θ'|) ^ α :=
    Real.rpow_le_rpow (abs_nonneg _) (rhsJet_sin_cos_sq_lipschitz θ θ') hα.le
  have h3 : (3:ℝ) ^ α ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hα1
    rwa [Real.rpow_one] at h
  have hmain : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'| ≤ 3 * |θ - θ'| ^ α := by
    rw [hG θ, hG θ']
    calc |(Real.sin θ * Real.cos θ ^ 2) ^ α - (Real.sin θ' * Real.cos θ' ^ 2) ^ α|
        ≤ |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α := hbase
      _ ≤ (3 * |θ - θ'|) ^ α := hlip
      _ = 3 ^ α * |θ - θ'| ^ α := Real.mul_rpow (by norm_num) (abs_nonneg _)
      _ ≤ 3 * |θ - θ'| ^ α := by
          have h0 : (0:ℝ) ≤ |θ - θ'| ^ α := Real.rpow_nonneg (abs_nonneg _) _
          nlinarith [h3, h0]
  have hrew : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)
      - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' / Work.Spaces.c (Work.FTS.Regularity.pExp α)
      = (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ')
        / Work.Spaces.c (Work.FTS.Regularity.pExp α) := by
    ring
  rw [hrew, abs_div, abs_of_pos hcpos]
  have h10 : 1 / Work.Spaces.c (Work.FTS.Regularity.pExp α) ≤ 10 := by
    rw [div_le_iff₀ hcpos]; linarith
  have hd0 : (0:ℝ) ≤ |θ - θ'| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  calc |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'| / Work.Spaces.c (Work.FTS.Regularity.pExp α)
      ≤ (3 * |θ - θ'| ^ α) / Work.Spaces.c (Work.FTS.Regularity.pExp α) :=
        div_le_div_of_nonneg_right hmain hcpos.le
    _ = 3 * |θ - θ'| ^ α * (1 / Work.Spaces.c (Work.FTS.Regularity.pExp α)) := by ring
    _ ≤ 3 * |θ - θ'| ^ α * 10 := mul_le_mul_of_nonneg_left h10 (by positivity)
    _ ≤ 40 * |θ - θ'| ^ α := by linarith

/-- `|2z²/(1+z)³| ≤ 1` for `z ≥ 0`. -/
theorem rhsJet_zsqCube_bdd {z : ℝ} (hz : 0 ≤ z) : |2 * z ^ 2 / (1 + z) ^ 3| ≤ 1 := by
  have h1 : (0:ℝ) < (1 + z) ^ 3 := by positivity
  have h2 : (0:ℝ) ≤ 2 * z ^ 2 := by positivity
  rw [abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_of_nonneg h2]
  nlinarith [hz, sq_nonneg z]

/-- The polynomial inequality behind the Lipschitz bound for `2z²/(1+z)³`: for `p, u ≥ 0`,
`|p + 3u - u²| ≤ (1 + p + u)³`. -/
theorem rhsJet_tri_abs_aux {p u : ℝ} (hp : 0 ≤ p) (hu : 0 ≤ u) :
    |p + 3 * u - u ^ 2| ≤ (1 + p + u) ^ 3 := by
  rw [abs_le]
  constructor
  · nlinarith [hp, hu, sq_nonneg p, sq_nonneg u, pow_nonneg hp 3, pow_nonneg hu 3,
      mul_nonneg hp hu, mul_nonneg (pow_nonneg hp 2) hu, mul_nonneg hp (pow_nonneg hu 2),
      mul_nonneg (sq_nonneg p) (sq_nonneg u)]
  · nlinarith [hp, hu, sq_nonneg p, sq_nonneg u, pow_nonneg hp 3, pow_nonneg hu 3,
      mul_nonneg hp hu]

/-- `z ↦ 2z²/(1+z)³` is `2`-Lipschitz on `[0,∞)` (the true constant is `≈ 0.36`). -/
theorem rhsJet_zsqCube_lip {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 2 * |z - z'| := by
  have h1 : (0:ℝ) < (1 + z) ^ 3 := by positivity
  have h2 : (0:ℝ) < (1 + z') ^ 3 := by positivity
  have hp : (0:ℝ) ≤ z + z' := by linarith
  have hu : (0:ℝ) ≤ z * z' := by positivity
  have hq : |z + z' + 3 * z * z' - z ^ 2 * z' ^ 2| ≤ (1 + z) ^ 3 * (1 + z') ^ 3 := by
    have key := rhsJet_tri_abs_aux hp hu
    rwa [show (1 + (z + z') + z * z') ^ 3 = (1 + z) ^ 3 * (1 + z') ^ 3 by ring,
      show (z + z') + 3 * (z * z') - (z * z') ^ 2
        = z + z' + 3 * z * z' - z ^ 2 * z' ^ 2 by ring] at key
  have hfac : 2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3
      = 2 * (z - z') * (z + z' + 3 * z * z' - z ^ 2 * z' ^ 2)
        / ((1 + z) ^ 3 * (1 + z') ^ 3) := by
    field_simp
    ring
  have habs : |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3|
      = 2 * |z - z'| * |z + z' + 3 * z * z' - z ^ 2 * z' ^ 2|
        / ((1 + z) ^ 3 * (1 + z') ^ 3) := by
    rw [hfac, abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos (mul_pos h1 h2)]
  rw [habs, div_le_iff₀ (mul_pos h1 h2)]
  nlinarith [hq, abs_nonneg (z - z')]

/-- `z ↦ 2z²/(1+z)³` is `α`-Hölder with constant `2` on `[0,∞)`, for `0 < α ≤ 1`. -/
theorem rhsJet_zsqCube_holder {α z z' : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 2 * |z - z'| ^ α := by
  rcases le_or_gt |z - z'| 1 with hd | hd
  · have h1 : |z - z'| ≤ |z - z'| ^ α := by
      rcases eq_or_lt_of_le (abs_nonneg (z - z')) with h | h
      · refine le_of_eq ?_
        rw [h.symm]
        exact (Real.zero_rpow hα.ne').symm
      · have := Real.rpow_le_rpow_of_exponent_ge h hd hα1
        rwa [Real.rpow_one] at this
    have := rhsJet_zsqCube_lip hz hz'
    linarith
  · have h1 : (1:ℝ) ≤ |z - z'| ^ α := Real.one_le_rpow hd.le hα.le
    have h2 := rhsJet_zsqCube_bdd hz
    have h3 := rhsJet_zsqCube_bdd hz'
    have h4 : |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 2 := by
      calc |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3|
          = |2 * z ^ 2 / (1 + z) ^ 3 + -(2 * z' ^ 2 / (1 + z') ^ 3)| := by ring_nf
        _ ≤ |2 * z ^ 2 / (1 + z) ^ 3| + |-(2 * z' ^ 2 / (1 + z') ^ 3)| := abs_add_le _ _
        _ = |2 * z ^ 2 / (1 + z) ^ 3| + |2 * z' ^ 2 / (1 + z') ^ 3| := by rw [abs_neg]
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by norm_num
    have h0 : (0:ℝ) ≤ |z - z'| ^ α := Real.rpow_nonneg (abs_nonneg _) _
    nlinarith

/-- **Bound and Hölder modulus of `AK`.**  For `0 < α ≤ 1/3` the function
`AK (pExp α) z θ = (Γ(θ)/c(3α))·2z²/(1+z)³` satisfies `|AK| ≤ 10` on `[0,∞) × Iθ` and is
`α`-Hölder for the metric `|Δz| + |Δθ|` with constant `100`. -/
theorem rhsJet_ak_bounds {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    (∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ| ≤ 10) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ
        - Work.Construction.AK (Work.FTS.Regularity.pExp α) z' θ'|
      ≤ 100 * (|z - z'| + |θ - θ'|) ^ α) := by
  have hα1 : α ≤ 1 := by linarith
  have hP : 0 < Work.FTS.Regularity.pExp α := by rw [Work.FTS.Regularity.pExp]; linarith
  have hP1 : Work.FTS.Regularity.pExp α ≤ 1 := by rw [Work.FTS.Regularity.pExp]; linarith
  obtain ⟨hc1, hc10⟩ := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hP hP1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith
  have hgc : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        ≤ 10 := by
    intro θ hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hP hθ
    have h1 : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)
        ≤ 1 / Work.Spaces.c (Work.FTS.Regularity.pExp α) := by
      rw [div_le_iff₀ hcpos, div_mul_cancel₀ 1 hcpos.ne']
      exact hG1
    have h2 : 1 / Work.Spaces.c (Work.FTS.Regularity.pExp α) ≤ 10 := by
      rw [div_le_iff₀ hcpos]; linarith
    rw [abs_of_nonneg (div_nonneg hG0 hcpos.le)]
    linarith
  constructor
  · intro z hz θ hθ
    rw [Work.Construction.AK, abs_mul]
    calc |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)| * |2 * z ^ 2 / (1 + z) ^ 3|
        ≤ 10 * 1 := mul_le_mul (hgc θ hθ) (rhsJet_zsqCube_bdd hz) (abs_nonneg _) (by norm_num)
      _ = 10 := by norm_num
  · intro z z' hz hz' θ hθ θ' hθ'
    unfold Work.Construction.AK
    set d := |z - z'| + |θ - θ'| with hd
    have hd0 : 0 ≤ d := by rw [hd]; positivity
    have hzd : |z - z'| ^ α ≤ d ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by rw [hd]; linarith [abs_nonneg (θ - θ')]) hα.le
    have hθd : |θ - θ'| ^ α ≤ d ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by rw [hd]; linarith [abs_nonneg (z - z')]) hα.le
    have hg1 : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)
        - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        ≤ 40 * |θ - θ'| ^ α := rhsJet_gam_div_c_holder hα hα13 hθ hθ'
    have hF1 : |2 * z ^ 2 / (1 + z) ^ 3| ≤ 1 := rhsJet_zsqCube_bdd hz
    have hF2 : |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 2 * |z - z'| ^ α :=
      rhsJet_zsqCube_holder hα hα1 hz hz'
    have hg2 : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)| ≤ 10 := hgc θ' hθ'
    have h1 : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)
          - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        * |2 * z ^ 2 / (1 + z) ^ 3| ≤ 40 * d ^ α := by
      have h₁ : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
          * |2 * z ^ 2 / (1 + z) ^ 3| ≤ (40 * |θ - θ'| ^ α) * 1 :=
        mul_le_mul hg1 hF1 (abs_nonneg _) (by positivity)
      nlinarith [h₁, hθd, Real.rpow_nonneg hd0 α]
    have h2 : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        * |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 20 * d ^ α := by
      have h₁ : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
          * |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3|
          ≤ 10 * (2 * |z - z'| ^ α) :=
        mul_le_mul hg2 hF2 (abs_nonneg _) (by norm_num)
      nlinarith [h₁, hzd, Real.rpow_nonneg hd0 α]
    have key : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α) * (2 * z ^ 2 / (1 + z) ^ 3)
          - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α) * (2 * z' ^ 2 / (1 + z') ^ 3)
        = (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * (2 * z ^ 2 / (1 + z) ^ 3)
          + Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            * (2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3) := by ring
    rw [key]
    calc |(Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * (2 * z ^ 2 / (1 + z) ^ 3)
          + Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            * (2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3)|
        ≤ |(Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * (2 * z ^ 2 / (1 + z) ^ 3)|
          + |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            * (2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3)| := abs_add_le _ _
      _ = |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
          * |2 * z ^ 2 / (1 + z) ^ 3|
          + |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
            * |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| := by
          rw [abs_mul, abs_mul]
      _ ≤ 40 * d ^ α + 20 * d ^ α := add_le_add h1 h2
      _ ≤ 100 * d ^ α := by
          have h0 : (0:ℝ) ≤ d ^ α := Real.rpow_nonneg hd0 α
          linarith

/-! ## The `Jet`-closure API -/

/-- The sum of two `Jet`s. -/
theorem rhsJet_add {α S N₁ N₂ : ℝ} {f g : ℝ → ℝ → ℝ → ℝ}
    (hf : Work.FTS.Regularity.Jet α S N₁ f) (hg : Work.FTS.Regularity.Jet α S N₂ g) :
    Work.FTS.Regularity.Jet α S (N₁ + N₂) (fun z θ τ => f z θ τ + g z θ τ) := by
  refine ⟨add_nonneg hf.1 hg.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    calc |f z θ τ + g z θ τ| ≤ |f z θ τ| + |g z θ τ| := abs_add_le _ _
      _ ≤ N₁ + N₂ := add_le_add (hf.abs_le hz hθ hτ) (hg.abs_le hz hθ hτ)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h := hf.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h' := hg.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    simp only []
    rw [show f z θ τ + g z θ τ - (f z' θ' τ' + g z' θ' τ')
        = (f z θ τ - f z' θ' τ') + (g z θ τ - g z' θ' τ') by ring]
    calc |(f z θ τ - f z' θ' τ') + (g z θ τ - g z' θ' τ')|
        ≤ |f z θ τ - f z' θ' τ'| + |g z θ τ - g z' θ' τ'| := abs_add_le _ _
      _ ≤ N₁ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α
            + N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := add_le_add h h'
      _ = (N₁ + N₂) * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring

/-- The negation of a `Jet`. -/
theorem rhsJet_neg {α S N : ℝ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : Work.FTS.Regularity.Jet α S N f) :
    Work.FTS.Regularity.Jet α S N (fun z θ τ => -f z θ τ) := by
  refine ⟨hf.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ; simpa using hf.abs_le hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    simp only []
    rw [show -f z θ τ - -f z' θ' τ' = -(f z θ τ - f z' θ' τ') by ring, abs_neg]
    exact hf.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'

/-- Transport of a `Jet` along a pointwise equality. -/
theorem rhsJet_congr {α S N : ℝ} {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ z θ τ, f z θ τ = g z θ τ) (H : Work.FTS.Regularity.Jet α S N f) :
    Work.FTS.Regularity.Jet α S N g := by
  refine ⟨H.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    simpa only [← h z θ τ] using H.2.1 z θ τ hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    simpa only [← h z θ τ, ← h z' θ' τ'] using H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'

/-- **Product of a `τ`-dependent bounded Hölder scalar with a bounded Hölder function of
`(z,θ)`.** -/
theorem rhsJet_mul {α S M K₁ K₂ : ℝ} {m : ℝ → ℝ} {A : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hm : ∀ τ ∈ Set.Icc 0 S, |m τ| ≤ M)
    (hmh : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |m τ - m τ'| ≤ M * |τ - τ'| ^ α)
    (hA : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ, |A z θ| ≤ K₁)
    (hAh : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |A z θ - A z' θ'| ≤ K₂ * (|z - z'| + |θ - θ'|) ^ α) :
    Work.FTS.Regularity.Jet α S (M * K₁ + M * K₂) (fun z θ τ => m τ * A z θ) := by
  have hMK₁ : 0 ≤ M * K₁ := mul_nonneg hM hK₁
  have hMK₂ : 0 ≤ M * K₂ := mul_nonneg hM hK₂
  refine ⟨by linarith, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    calc |m τ * A z θ| = |m τ| * |A z θ| := abs_mul _ _
      _ ≤ M * K₁ := mul_le_mul (hm τ hτ) (hA z hz θ hθ) (abs_nonneg _) hM
      _ ≤ M * K₁ + M * K₂ := by linarith
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    set d := |z - z'| + |θ - θ'| + |τ - τ'| with hd
    have hd0 : 0 ≤ d := by rw [hd]; positivity
    have hτd : |τ - τ'| ^ α ≤ d ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by rw [hd]; linarith [abs_nonneg (z - z'), abs_nonneg (θ - θ')]) hα.le
    have hzd : (|z - z'| + |θ - θ'|) ^ α ≤ d ^ α :=
      Real.rpow_le_rpow (by positivity) (by rw [hd]; linarith [abs_nonneg (τ - τ')]) hα.le
    have h1 : |m τ - m τ'| * |A z θ| ≤ M * K₁ * d ^ α := by
      have h₁ : |m τ - m τ'| * |A z θ| ≤ (M * |τ - τ'| ^ α) * K₁ :=
        mul_le_mul (hmh τ hτ τ' hτ') (hA z hz θ hθ) (abs_nonneg _) (by positivity)
      have h₂ : M * K₁ * |τ - τ'| ^ α ≤ M * K₁ * d ^ α :=
        mul_le_mul_of_nonneg_left hτd hMK₁
      linarith
    have h2 : |m τ'| * |A z θ - A z' θ'| ≤ M * K₂ * d ^ α := by
      have h₁ : |m τ'| * |A z θ - A z' θ'| ≤ M * (K₂ * (|z - z'| + |θ - θ'|) ^ α) :=
        mul_le_mul (hm τ' hτ') (hAh z z' hz hz' θ hθ θ' hθ') (abs_nonneg _) hM
      have h₂ : M * (K₂ * (|z - z'| + |θ - θ'|) ^ α) ≤ M * (K₂ * d ^ α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzd hK₂) hM
      have h₃ : M * (K₂ * d ^ α) = M * K₂ * d ^ α := by ring
      linarith
    simp only []
    rw [show m τ * A z θ - m τ' * A z' θ'
        = (m τ - m τ') * A z θ + m τ' * (A z θ - A z' θ') by ring]
    calc |(m τ - m τ') * A z θ + m τ' * (A z θ - A z' θ')|
        ≤ |(m τ - m τ') * A z θ| + |m τ' * (A z θ - A z' θ')| := abs_add_le _ _
      _ = |m τ - m τ'| * |A z θ| + |m τ'| * |A z θ - A z' θ'| := by rw [abs_mul, abs_mul]
      _ ≤ M * K₁ * d ^ α + M * K₂ * d ^ α := add_le_add h1 h2
      _ = (M * K₁ + M * K₂) * d ^ α := by ring

end Work.FTS.RegPkgGal.Der
