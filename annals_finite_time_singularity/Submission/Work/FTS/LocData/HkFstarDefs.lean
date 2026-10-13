/-
# `Work.FTS.LocData.HkFstarDefs` — the angular polynomials of the `F_*` estimate

This module contains the *definitions* used by the proof of
`Work.FTS.LocData.HkIntegrand_Fstar_le`, namely the explicit polynomials
`Qf i u a` (i = 0,…,4) with the property

  `DthIter i (fun _ θ => Gam α θ) z θ = Gam α θ * (α * Qf i (cos (2θ)) α)`   (i ≥ 1)

(and `= Gam α θ` for `i = 0`), together with their formal `u`-derivatives `dQf i u a`.
The recursion is

  `Qf (i+1) u a = -2*(1-u^2)*dQf i u a + a * Qf 1 u a * Qf i u a`.

Everything here is pure algebra (`ring`/`norm_num`); the analytic content (the
`deriv` computation for `Gam`) lives in the sibling modules.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- **The angular polynomials of the `F_*` estimate.**  `Qf i u a` is the polynomial with

  `DthIter i (fun _ θ' => Gam α θ') z θ = Gam α θ * (a * Qf i (cos (2θ)) a)`

for `i ≥ 1` (and `= Gam α θ` for `i = 0`), where `a = α` and `u = cos(2θ)`.
Concretely

* `Qf 0 u a = 1`
* `Qf 1 u a = (3u-1)/3`
* `Qf 2 u a = -2(1-u²) + a(3u-1)²/9`
* `Qf 3 u a = -8u(1-u²) - 6a(u-1/3)(1-u²) + a²(u-1/3)³`
* `Qf 4 u a = 16(1-u²)(1-3u²) + 12a(1-u²)² - 32au(u-1/3)(1-u²)
              - 12a²(u-1/3)²(1-u²) + a³(u-1/3)⁴`. -/
noncomputable def Qf : ℕ → ℝ → ℝ → ℝ
  | 0, u, a => 1
  | 1, u, a => (3 * u - 1) / 3
  | 2, u, a => -2 * (1 - u ^ 2) + a * (3 * u - 1) ^ 2 / 9
  | 3, u, a => -8 * u * (1 - u ^ 2) - 6 * a * (u - 1 / 3) * (1 - u ^ 2)
      + a ^ 2 * (u - 1 / 3) ^ 3
  | 4, u, a => 16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * a * (1 - u ^ 2) ^ 2
      - 32 * a * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * a ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + a ^ 3 * (u - 1 / 3) ^ 4
  | _, u, a => 0

/-- **The formal `u`-derivative of `Qf`**: `dQf i u a = ∂_u (Qf i · a)`.  It is chosen so that

  `HasDerivAt (fun u => Qf i u a) (dQf i u a) u`

and the recursion `Qf (i+1) u a = -2(1-u²)·dQf i u a + a·Qf 1 u a·Qf i u a` holds. -/
noncomputable def dQf : ℕ → ℝ → ℝ → ℝ
  | 0, u, a => 0
  | 1, u, a => 1
  | 2, u, a => 4 * u + 2 * a * (u - 1 / 3)
  | 3, u, a => 24 * u ^ 2 - 8 + a * (18 * u ^ 2 - 4 * u - 6)
      + 3 * a ^ 2 * (u - 1 / 3) ^ 2
  | 4, u, a => 192 * u ^ 3 - 128 * u
      + a * (176 * u ^ 3 - 32 * u ^ 2 - 112 * u + 32 / 3)
      + a ^ 2 * (-24 * (u - 1 / 3) * (1 + u / 3 - 2 * u ^ 2))
      + 4 * a ^ 3 * (u - 1 / 3) ^ 3
  | _, u, a => 0

@[simp] theorem Qf_zero (u a : ℝ) : Qf 0 u a = 1 := rfl
@[simp] theorem Qf_one (u a : ℝ) : Qf 1 u a = (3 * u - 1) / 3 := rfl
@[simp] theorem Qf_two (u a : ℝ) : Qf 2 u a = -2 * (1 - u ^ 2) + a * (3 * u - 1) ^ 2 / 9 := rfl
@[simp] theorem Qf_three (u a : ℝ) :
    Qf 3 u a = -8 * u * (1 - u ^ 2) - 6 * a * (u - 1 / 3) * (1 - u ^ 2)
      + a ^ 2 * (u - 1 / 3) ^ 3 := rfl
@[simp] theorem Qf_four (u a : ℝ) :
    Qf 4 u a = 16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * a * (1 - u ^ 2) ^ 2
      - 32 * a * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * a ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + a ^ 3 * (u - 1 / 3) ^ 4 := rfl

@[simp] theorem dQf_zero (u a : ℝ) : dQf 0 u a = 0 := rfl
@[simp] theorem dQf_one (u a : ℝ) : dQf 1 u a = 1 := rfl
@[simp] theorem dQf_two (u a : ℝ) : dQf 2 u a = 4 * u + 2 * a * (u - 1 / 3) := rfl
@[simp] theorem dQf_three (u a : ℝ) :
    dQf 3 u a = 24 * u ^ 2 - 8 + a * (18 * u ^ 2 - 4 * u - 6)
      + 3 * a ^ 2 * (u - 1 / 3) ^ 2 := rfl
@[simp] theorem dQf_four (u a : ℝ) :
    dQf 4 u a = 192 * u ^ 3 - 128 * u
      + a * (176 * u ^ 3 - 32 * u ^ 2 - 112 * u + 32 / 3)
      + a ^ 2 * (-24 * (u - 1 / 3) * (1 + u / 3 - 2 * u ^ 2))
      + 4 * a ^ 3 * (u - 1 / 3) ^ 3 := rfl

/-- The recursion of the angular polynomials: `Qf (i+1)` in terms of `Qf i`, `dQf i`
and `Qf 1` (which is `(3u-1)/3`). -/
theorem Qf_rec_one (u a : ℝ) : Qf 2 u a = -2 * (1 - u ^ 2) * dQf 1 u a + a * Qf 1 u a * Qf 1 u a := by
  simp only [Qf_two, dQf_one, Qf_one]; ring

theorem Qf_rec_two (u a : ℝ) : Qf 3 u a = -2 * (1 - u ^ 2) * dQf 2 u a + a * Qf 1 u a * Qf 2 u a := by
  simp only [Qf_three, dQf_two, Qf_one, Qf_two]; ring

theorem Qf_rec_three (u a : ℝ) : Qf 4 u a = -2 * (1 - u ^ 2) * dQf 3 u a + a * Qf 1 u a * Qf 3 u a := by
  simp only [Qf_four, dQf_three, Qf_one, Qf_three]; ring

/-- `Qf 1 u a = (3u-1)/3 = u - 1/3`. -/
theorem Qf_one_eq (u a : ℝ) : Qf 1 u a = u - 1 / 3 := by simp only [Qf_one]; ring

/-- `Pf i u a = a · Qf i u a` for `i ≥ 1`, and `Pf 0 = 1`: this is the function such that

  `DthIter i (fun _ θ' => Gam α θ') z θ = Gam α θ * Pf i (cos (2θ)) α`

for every `i ≤ 4`. -/
noncomputable def Pf : ℕ → ℝ → ℝ → ℝ := fun i u a => if i = 0 then 1 else a * Qf i u a

@[simp] theorem Pf_zero (u a : ℝ) : Pf 0 u a = 1 := rfl
theorem Pf_one (u a : ℝ) : Pf 1 u a = a * ((3 * u - 1) / 3) := by
  simp only [Pf, Qf_one, one_ne_zero, ↓reduceIte]
theorem Pf_two (u a : ℝ) : Pf 2 u a = a * (-2 * (1 - u ^ 2) + a * (3 * u - 1) ^ 2 / 9) := by
  simp only [Pf, Qf_two, (by norm_num : (2:ℕ) ≠ 0), ↓reduceIte]
theorem Pf_three (u a : ℝ) : Pf 3 u a = a * (-8 * u * (1 - u ^ 2) - 6 * a * (u - 1 / 3) * (1 - u ^ 2)
      + a ^ 2 * (u - 1 / 3) ^ 3) := by
  simp only [Pf, Qf_three, (by norm_num : (3:ℕ) ≠ 0), ↓reduceIte]
theorem Pf_four (u a : ℝ) : Pf 4 u a = a * (16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * a * (1 - u ^ 2) ^ 2
      - 32 * a * u * (u - 1 / 3) * (1 - u ^ 2) - 12 * a ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2)
      + a ^ 3 * (u - 1 / 3) ^ 4) := by
  simp only [Pf, Qf_four, (by norm_num : (4:ℕ) ≠ 0), ↓reduceIte]

/-- `DzIter` of a function of the form `(z,θ) ↦ A θ * B z` (the `θ`-factor is a constant
for `∂_z`): this is where the product structure of `F_* = α(Γ(θ)/c)·φ(z)` is used. -/
theorem DzIter_mul_theta_factor (j : ℕ) (A : ℝ → ℝ) (B : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A θ * B z θ) = fun z θ => A θ * Work.Spaces.DzIter j B z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-- **The radial factor** `PhiR i z`: the `z`-part of the `i`-th iterated `D_z`-derivative of
`F_* = α(Γ(θ)/c)·φ(z)`, where `φ = FM.Fstar = 2z/(1+z)²`.  Namely

  `D_z^i φ(z) = PhiR i z / (1+z)^{i+2}`,

with `PhiR i z = 2z·R_i(z)` for the palindromic polynomials
`R_0 = 1`, `R_1 = 1-z`, `R_2 = 1-4z+z²`, `R_3 = 1-11z+11z²-z³`, `R_4 = 1-26z+66z²-26z³+z⁴`. -/
noncomputable def PhiR : ℕ → ℝ → ℝ
  | 0, z => 2 * z
  | 1, z => 2 * z * (1 - z)
  | 2, z => 2 * z * (1 - 4 * z + z ^ 2)
  | 3, z => 2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3)
  | 4, z => 2 * z * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4)
  | _, _ => 0

/-- `Phi i z = DzIter i (fun z _ => FM.Fstar z) z θ`, the (θ-independent) `z`-derivative in
normalised form. -/
noncomputable def Phi (i : ℕ) (z θ : ℝ) : ℝ := PhiR i z / (1 + z) ^ (i + 2)

@[simp] theorem PhiR_zero (z : ℝ) : PhiR 0 z = 2 * z := rfl
@[simp] theorem PhiR_one (z : ℝ) : PhiR 1 z = 2 * z * (1 - z) := rfl
@[simp] theorem PhiR_two (z : ℝ) : PhiR 2 z = 2 * z * (1 - 4 * z + z ^ 2) := rfl
@[simp] theorem PhiR_three (z : ℝ) : PhiR 3 z = 2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) := rfl
@[simp] theorem PhiR_four (z : ℝ) :
    PhiR 4 z = 2 * z * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) := rfl

end Work.FTS.LocData
