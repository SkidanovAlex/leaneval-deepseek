/-
# `Work.FTS.Regularity.gammaFstarModuli` — the moduli of `Γ` and of the profile `F_*(3α)`

This file proves a single *packaged* modulus statement for node N7 of the audit, namely that the
angular factor `Γ(θ) = (sinθcos²θ)^α` and the fundamental-model profile at the profile exponent
`3α`,

  `F_*(z,θ) = Work.Construction.Fstar (3α) z θ = (3α)·(Γ(θ)/c(3α))·2z/(1+z)²`,

share **one** constant `C` for all the quantitative facts the transfer chapter needs:

* `|F_*(z,θ)| ≤ C·Γ(θ)` on `z ≥ 0`, `θ ∈ Iθ = [0,π/2]`;
* `F_*(z,0) = F_*(z,π/2) = 0`, i.e. the profile vanishes on the two angular boundaries;
* `F_*(0,θ) = 0`, the quadratic vanishing at the origin of the self-similar radial variable;
* `Γ` is `α`-Hölder on `Iθ` with constant `C`;
* `F_*` is *jointly* `α`-Hölder for the metric `|Δz| + |Δθ|` with constant `C`.

The last item is what makes the profile usable as a `VanishTheta`/`St1` datum after composition
with the self-similar coordinates, and it is the only non-trivial new ingredient of the file.
The proof splits the difference at the intermediate point `(z', θ)` (`abs_sub_le`), uses the
existing radial modulus `fstarModulus` (`≤ 20|z-z'|`) for the radial part, and a direct
factorisation for the angular part:

  `F_*(z,θ) = ((3α/c(3α))·2z/(1+z)²) · Γ(θ)`,

so that the angular difference is bounded by `|3α/c(3α)|·|2z/(1+z)²|·3^α|θ-θ'|^α`, the two
factors being `≤ 10` (`c ≥ 1/10`, `3α ≤ 1`) and `≤ 1/2` respectively.  The result
`20|z-z'| + 5·3^α|θ-θ'|^α` is then *joined* with the global bound `40` (from
`|F_*| ≤ 20Γ ≤ 20` and `Γ ≤ 1`) through the elementary lemma `join_rpow_le`: below `1` the
linear part is dominated by the `α`-power of the sum, above `1` the sum's power is `≥ 1`.

The packaged constant produced is `C = 100`.  Every ingredient is α-uniform: `20`, `5·3^α ≤ 5·3`
and `40` all fit under `100` for `0 < α ≤ 1/3`.

Quantitative helpers used: `Work.Spaces.c_bounds` (`1/10 ≤ c ≤ 10`),
`Work.FTS.Regularity.Moduli.fstarLip` (`2`-Lipschitz), `gammaModulus` and `fstarModulus` of the
sibling `fstarModuli`, and `Work.ConstructionInstance.Fstar_abs_le`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.LocData.FstarAux
import Submission.Work.FTS.Regularity.Moduli.fstarLip
import Submission.Work.FTS.Regularity.fstarModuli
import Submission.Work.FTS.LocData.vanishTheta_locG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FTS.Regularity

/-! ## The one-variable profile `F_*(z) = 2z/(1+z)²` -/

/-- `2z/(1+z)² ≥ 0` for `z ≥ 0`. -/
theorem fmFstar_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Work.FM.Fstar z := by
  rw [Work.FM.Fstar]
  exact div_nonneg (by linarith) (by positivity)

/-- `2z/(1+z)² ≤ 1/2` for `z ≥ 0` (`(1-z)² ≥ 0`). -/
theorem fmFstar_le_half {z : ℝ} (hz : 0 ≤ z) : Work.FM.Fstar z ≤ 1 / 2 := by
  rw [Work.FM.Fstar, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z)]

/-- `|2z/(1+z)²| ≤ 1/2` for `z ≥ 0`. -/
theorem fmFstar_abs_le_half {z : ℝ} (hz : 0 ≤ z) : |Work.FM.Fstar z| ≤ 1 / 2 := by
  rw [abs_of_nonneg (fmFstar_nonneg hz)]
  exact fmFstar_le_half hz

/-- `F_*(0) = 0`. -/
theorem fmFstar_zero : Work.FM.Fstar 0 = 0 := by
  rw [Work.FM.Fstar]
  norm_num

/-! ## The coefficient `3α/c(3α)` -/

/-- The coefficient of the profile is bounded: `|3α/c(3α)| ≤ 10` for `0 < α ≤ 1/3`, since
`3α ≤ 1` and `c(3α) ≥ 1/10`. -/
theorem threeAlpha_div_c_abs_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    |3 * α / Work.Spaces.c (3 * α)| ≤ 10 := by
  have h3a : 0 < 3 * α := by linarith
  have h3a1 : 3 * α ≤ 1 := by linarith
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c (3 * α) :=
    (Work.Spaces.c_bounds (3 * α) h3a h3a1).1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by linarith
  rw [abs_of_nonneg (div_nonneg (by linarith) hcpos.le), div_le_iff₀ hcpos]
  nlinarith

/-! ## Two elementary exponent inequalities -/

/-- For `0 ≤ d ≤ 1` and `0 < α ≤ 1`: `d ≤ d ^ α` (the map `x ↦ x ^ α` is `≥` the identity on
`[0,1]`).  The case `d = 0` is the null exponent case of `Real.zero_rpow`. -/
theorem self_le_rpow_of_le_one {α d : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) : d ≤ d ^ α := by
  rcases eq_or_lt_of_le hd0 with h | h
  · rw [← h, Real.zero_rpow hα0.ne']
  · have hle := Real.rpow_le_rpow_of_exponent_ge h hd1 hα1
    simpa [Real.rpow_one] using hle

/-- **The join inequality.**  If a nonnegative quantity `x` is bounded both by a constant `M`
and by a combination `A·t + B·s^α` of two nonnegative variables `t, s`, then it is bounded by
`max M (A + B)·(t + s)^α` — the standard way of merging a `C⁰` bound with a "Hölder-type" one
into a single modulus for the metric `t + s`.

Below the level `t + s ≤ 1` the linear term is dominated by `(t+s)^α` (`t ≤ (t+s) ≤ (t+s)^α`) and
so is `s^α`; above the level `1` the constant bound `M` is, since `(t+s)^α ≥ 1`. -/
theorem join_rpow_le {α M A B t s x : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hxM : x ≤ M) (hxAB : x ≤ A * t + B * s ^ α) :
    x ≤ max M (A + B) * (t + s) ^ α := by
  have hD : 0 ≤ t + s := by linarith
  have hmax0 : 0 ≤ max M (A + B) := le_trans hM (le_max_left M (A + B))
  by_cases hle : t + s ≤ 1
  · have hself : t + s ≤ (t + s) ^ α := self_le_rpow_of_le_one hα0 hα1 hD hle
    have hDα : 0 ≤ (t + s) ^ α := Real.rpow_nonneg hD α
    have htD : t ≤ (t + s) ^ α := le_trans (by linarith) hself
    have hAt : A * t ≤ A * (t + s) ^ α := mul_le_mul_of_nonneg_left htD hA
    have hBs : B * s ^ α ≤ B * (t + s) ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs (by linarith) hα0.le) hB
    have hsum : A * t + B * s ^ α ≤ (A + B) * (t + s) ^ α := by
      rw [add_mul]
      linarith
    exact le_trans hxAB
      (le_trans hsum (mul_le_mul_of_nonneg_right (le_max_right M (A + B)) hDα))
  · have hgt : 1 ≤ t + s := le_of_lt (not_le.mp hle)
    have hDα1 : 1 ≤ (t + s) ^ α := Real.one_le_rpow hgt hα0.le
    calc x ≤ M := hxM
      _ ≤ max M (A + B) := le_max_left M (A + B)
      _ = max M (A + B) * 1 := (mul_one _).symm
      _ ≤ max M (A + B) * (t + s) ^ α := mul_le_mul_of_nonneg_left hDα1 hmax0

/-! ## The angular vanishing of the profile and its `Γ`-bound -/

/-- `|F_*(z,θ)| ≤ 20·Γ(θ)` for `z ≥ 0`, `θ ∈ Iθ` and `0 < α ≤ 1/3`: the coefficient
`20·(3α) ≤ 20` of `Work.ConstructionInstance.Fstar_abs_le` (which is `≤ 20·p·Γ(p/3)`) has
`p = 3α`. -/
theorem fstar_abs_le_gamma {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (3 * α) z θ| ≤ 20 * Gamma α θ := by
  have h := Work.ConstructionInstance.Fstar_abs_le (p := 3 * α) (by linarith) (by linarith) hz hθ
  have h3 : (3 * α) / 3 = α := by ring
  rw [h3] at h
  refine le_trans h ?_
  have hG0 : 0 ≤ Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  have h20 : 20 * (3 * α) ≤ 20 := by linarith
  exact mul_le_mul_of_nonneg_right h20 hG0

/-! ## The angular modulus of a fixed `z`-slice -/

/-- **The angular modulus of `F_*` at fixed `z`**: for `z ≥ 0` and `θ, θ' ∈ Iθ`,

  `|F_*(z,θ) - F_*(z,θ')| ≤ 5·3^α·|θ-θ'|^α`.

The profile factors as `((3α/c(3α))·2z/(1+z)²)·Γ(θ)`; the first factor is bounded by
`10·(1/2) = 5` and the second difference by the angular modulus `3^α|θ-θ'|^α` of `Γ`. -/
theorem fstar_theta_modulus {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z θ θ' : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z θ'|
      ≤ 5 * 3 ^ α * |θ - θ'| ^ α := by
  have hkey : Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z θ'
      = ((3 * α / Work.Spaces.c (3 * α)) * Work.FM.Fstar z)
        * (Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ') := by
    simp only [Work.Construction.Fstar]
    ring
  have hK : |(3 * α / Work.Spaces.c (3 * α)) * Work.FM.Fstar z| ≤ 5 := by
    rw [abs_mul]
    calc |3 * α / Work.Spaces.c (3 * α)| * |Work.FM.Fstar z|
        ≤ 10 * (1 / 2) :=
          mul_le_mul (threeAlpha_div_c_abs_le hα hα13) (fmFstar_abs_le_half hz) (abs_nonneg _)
            (by norm_num)
      _ = 5 := by norm_num
  have hG : |Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'| ≤ 3 ^ α * |θ - θ'| ^ α := by
    rw [gam_three α θ, gam_three α θ']
    exact gammaModulus (α := α) hα hα13 θ θ' hθ hθ'
  rw [hkey, abs_mul]
  calc |(3 * α / Work.Spaces.c (3 * α)) * Work.FM.Fstar z|
        * |Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'|
      ≤ 5 * (3 ^ α * |θ - θ'| ^ α) :=
        mul_le_mul hK hG (abs_nonneg _) (by norm_num)
    _ = 5 * 3 ^ α * |θ - θ'| ^ α := by ring

/-! ## The split bound and the joint modulus -/

/-- **The split bound**: splitting the joint difference at the intermediate point `(z',θ)`, the
radial part is `fstarModulus` (`≤ 20|z-z'|`) and the angular part is `fstar_theta_modulus`
(`≤ 5·3^α|θ-θ'|^α`). -/
theorem fstar_diff_le_split {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z z' θ θ' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ'|
      ≤ 20 * |z - z'| + 5 * 3 ^ α * |θ - θ'| ^ α := by
  have h1 : |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ|
      ≤ 20 * |z - z'| := fstarModulus (α := α) hα hα13 z z' θ hz hz' hθ
  have h2 : |Work.Construction.Fstar (3 * α) z' θ - Work.Construction.Fstar (3 * α) z' θ'|
      ≤ 5 * 3 ^ α * |θ - θ'| ^ α := fstar_theta_modulus hα hα13 hz' hθ hθ'
  exact le_trans (abs_sub_le _ _ _) (add_le_add h1 h2)

/-- **The joint `α`-Hölder modulus of the profile `F_*(3α)`** for the metric
`|Δz| + |Δθ|` on `[0,∞) × Iθ`, with the structural constant `100`. -/
theorem fstar_joint_modulus {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z z' θ θ' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ'|
      ≤ 100 * (|z - z'| + |θ - θ'|) ^ α := by
  have hsplit := fstar_diff_le_split hα hα13 hz hz' hθ hθ'
  -- the global (`C⁰`) bound `|F_*| ≤ 20Γ ≤ 20`
  have hglob : |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ'|
      ≤ 40 := by
    have hz1 : |Work.Construction.Fstar (3 * α) z θ| ≤ 20 * Gamma α θ :=
      fstar_abs_le_gamma hα hα13 hz hθ
    have hz2 : |Work.Construction.Fstar (3 * α) z' θ'| ≤ 20 * Gamma α θ' :=
      fstar_abs_le_gamma hα hα13 hz' hθ'
    have hG1 : Gamma α θ ≤ 1 := Work.ConstructionInstance.Gamma_le_one hα.le hθ
    have hG2 : Gamma α θ' ≤ 1 := Work.ConstructionInstance.Gamma_le_one hα.le hθ'
    calc |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ'|
        ≤ |Work.Construction.Fstar (3 * α) z θ| + |Work.Construction.Fstar (3 * α) z' θ'| := by
          have := abs_sub_le (Work.Construction.Fstar (3 * α) z θ) 0
            (Work.Construction.Fstar (3 * α) z' θ')
          simpa using this
      _ ≤ 20 * Gamma α θ + 20 * Gamma α θ' := add_le_add hz1 hz2
      _ ≤ 40 := by nlinarith
  have hjoin := join_rpow_le (M := 40) (A := 20) (B := 5 * 3 ^ α) hα (by linarith)
    (by norm_num) (by norm_num) (by positivity) (abs_nonneg _) (abs_nonneg _) hglob hsplit
  have hmax : max (40 : ℝ) (20 + 5 * 3 ^ α) ≤ 100 := by
    refine max_le (by norm_num) ?_
    have h3 : (3 : ℝ) ^ α ≤ 3 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by linarith : α ≤ 1)
      simpa [Real.rpow_one] using this
    linarith
  exact le_trans hjoin (mul_le_mul_of_nonneg_right hmax (Real.rpow_nonneg (by positivity) α))

/-! ## The packaged statement -/

theorem gammaFstarModuli {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
        |Work.Construction.Fstar (3 * α) z θ| ≤ C * Work.FTS.Regularity.Gamma α θ) ∧
      (∀ z : ℝ, Work.Construction.Fstar (3 * α) z 0 = 0) ∧
      (∀ z : ℝ, Work.Construction.Fstar (3 * α) z (Real.pi / 2) = 0) ∧
      (∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → Work.Construction.Fstar (3 * α) 0 θ = 0) ∧
      (∀ θ θ' : ℝ, θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
        |Work.FTS.Regularity.Gamma α θ - Work.FTS.Regularity.Gamma α θ'|
          ≤ C * |θ - θ'| ^ α) ∧
      (∀ z z' θ θ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
        |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ'|
          ≤ C * (|z - z'| + |θ - θ'|) ^ α) := by
  refine ⟨100, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z θ hz hθ
    refine le_trans (fstar_abs_le_gamma hα hα13 hz hθ) ?_
    have hG0 : 0 ≤ Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
    exact mul_le_mul_of_nonneg_right (by norm_num : (20 : ℝ) ≤ 100) hG0
  · intro z
    exact Work.FTS.LocData.Fstar_theta_zero (3 * α) (by linarith) z
  · intro z
    exact Work.FTS.LocData.Fstar_theta_pi_half (3 * α) (by linarith) z
  · intro θ _
    rw [Work.Construction.Fstar, fmFstar_zero, mul_zero]
  · intro θ θ' hθ hθ'
    refine le_trans (gammaModulus (α := α) hα hα13 θ θ' hθ hθ') ?_
    have h3 : (3 : ℝ) ^ α ≤ 3 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by linarith : α ≤ 1)
      simpa [Real.rpow_one] using this
    exact mul_le_mul_of_nonneg_right (by linarith : (3 : ℝ) ^ α ≤ 100)
      (Real.rpow_nonneg (abs_nonneg _) α)
  · intro z z' θ θ' hz hz' hθ hθ'
    exact fstar_joint_modulus hα hα13 hz hz' hθ hθ'

end Work.FTS.Regularity
