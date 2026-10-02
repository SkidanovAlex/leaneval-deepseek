/-
# `T10_armC1`: the tenth iterate of the angle map on the arm-`C` angles

The angle-doubling map of the antiholomorphic quadratic family is
`T θ = -2θ mod 1 = Int.fract (-2 * θ)` (`Work.EL.T`, `Submission/Work/ELTop/Defs.lean`), and
the degree-`1024` map `F c = (T_c)^{10}` acts on external rays by its tenth iterate, which is
`T^[10] θ = fract (1024 * θ)` (`Submission/Work/ELNest/T_iterate_bAng.lean`, `T_iterate_ten`).

The level-`n` arm pairs of the certificate `lead_mb/mb_EL_cert.py` are the three pairs of rays

* arm `A`: `(22/63, 25/63)`,   angles `armA1 n = contract (371/1023) (22/63) (64^n)`,
  `armA2 n = contract (404/1023) (25/63) (64^n)`;
* arm `B`: `(25/63, 37/63)`,   angles `armB1 n = contract (461/1023) (25/63) (64^n)`,
  `armB2 n = contract (593/1023) (37/63) (64^n)`;
* arm `C`: `(37/63, 22/63 + 1)`, angles `armC1 n = contract (821/1023) (37/63) (64^n)`,
  `armC2 n = contract (1349/1023) (22/63) (64^n)`,

where `contract t fix N = Int.fract (fix + centred (t - fix)/N)` contracts `t` towards `fix`
by the factor `N` (mod `1`).  The level-`(n+1)` triple of arms maps onto the level-`n` triple,
with the arms cycling `A → C → B → A` (up to two `F`-iterates): here we need the step

    T^[10] (armC1 n) = armB1 (n - 2)      for `n ≥ 2`,

i.e. `1024 * armC1 n ≡ armB1 (n-2) (mod 1)`.

**Proof.**  The two relevant "contraction offsets" are the rationals

    armC1 n - 37/63 = (4624/21483)/64ⁿ,      armB1 m - 25/63 = (1156/21483)/64ᵐ,

because `821/1023 - 37/63 = 4624/21483` and `461/1023 - 25/63 = 1156/21483` both lie in
`[-1/2, 1/2)`, so `centred` is the identity on them.  With `n = m + 2` we then have

    1024 * (37/63 + (4624/21483)/64^(m+2))
      = 1024 * 37/63 + 1024 * (4624/21483)/(64^m * 4096)
      = (601 + 25/63) + (1156/21483)/64^m,

using `64^(m+2) = 64^m · 4096`, `1024·37/63 = 601 + 25/63` and `1024·4624/4096 = 1156`.  The
integer `601` disappears in `Int.fract`, and `fract (1024 · fract X) = fract (1024 · X)`
because the two arguments differ by the integer `1024·⌊X⌋`.
-/
import Mathlib
import Submission.Work.ELNest.Defs
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

/-! ## Auxiliary arithmetic and `Int.fract` lemmas

The helpers are kept in the sub-namespace `Work.ELNest.ArmC1` so that the sibling files
`T10_armA1.lean`, `T10_armB1.lean` (whose proofs proceed along exactly the same lines) can
declare their own copies without clashing. -/

namespace ArmC1

/-- `centred` is the identity on `[-1/2, 1/2)`: the fold `x ↦ fract (x + 1/2) - 1/2`
does nothing to a point already in the fundamental domain. -/
theorem centred_eq_of_mem (x : ℝ) (h1 : -1/2 ≤ x) (h2 : x < 1/2) : centred x = x := by
  unfold centred
  rw [Int.fract_eq_self.mpr (by constructor <;> linarith)]
  ring

/-- In the region `W` of the certificate, the contraction defining `contract` multiplies the
signed distance to the fixed angle by exactly `1/N`: for `-1/2 ≤ t - fix < 1/2`,
`contract t fix N = fract (fix + (t - fix)/N)`. -/
theorem contract_eq_of_centred {t fix : ℝ} {N : ℕ} (h1 : -1/2 ≤ t - fix) (h2 : t - fix < 1/2) :
    contract t fix N = Int.fract (fix + (t - fix) / (N : ℝ)) := by
  rw [contract, centred_eq_of_mem (t - fix) h1 h2]

/-- The level-`n` arm-`C` angle in the explicit form used below: its distance to the fixed
angle `37/63` is `(4624/21483)/64ⁿ`. -/
theorem armC1_eq (n : ℕ) : armC1 n = Int.fract (37/63 + (4624/21483 : ℝ) / (64:ℝ)^n) := by
  rw [armC1, contract_eq_of_centred (by norm_num) (by norm_num)]
  norm_num

/-- The level-`m` arm-`B` angle in the explicit form used below: its distance to the fixed
angle `25/63` is `(1156/21483)/64ᵐ`. -/
theorem armB1_eq (m : ℕ) : armB1 m = Int.fract (25/63 + (1156/21483 : ℝ) / (64:ℝ)^m) := by
  rw [armB1, contract_eq_of_centred (by norm_num) (by norm_num)]
  norm_num

/-- Multiplying a fractional part by an integer does not change the fractional part of the
product: `fract (N · fract a) = fract (N · a)`, because `N·a - N·fract a = N·⌊a⌋ ∈ ℤ`. -/
theorem fract_mul_fract (N : ℕ) (a : ℝ) :
    Int.fract ((N:ℝ) * Int.fract a) = Int.fract ((N:ℝ) * a) := by
  rw [Int.fract_eq_fract]
  refine ⟨-(N * ⌊a⌋), ?_⟩
  push_cast
  have h2 : a - Int.fract a = (⌊a⌋ : ℝ) := by linarith [Int.fract_add_floor a]
  have h3 : (N:ℝ) * a - (N:ℝ) * Int.fract a = (N:ℝ) * (⌊a⌋ : ℝ) := by rw [← mul_sub, h2]
  linarith

/-- The exact congruence `1024 · armC1 (m+2) ≡ armB1 m (mod 1)`, in the form of an identity
of real numbers differing by the integer `601`:
`1024 · (37/63 + (4624/21483)/(y·4096)) = 601 + (25/63 + (1156/21483)/y)` for `y ≠ 0`. -/
theorem key_arith (y : ℝ) (_hy : y ≠ 0) :
    1024 * (37/63 + (4624/21483 : ℝ)/(y*4096)) = 601 + (25/63 + (1156/21483 : ℝ)/y) := by
  field_simp
  ring

end ArmC1

/-- **The step `C → B` of the arm cycle.**  The tenth iterate of the angle map sends the
level-`(m+2)` arm-`C` angle to the level-`m` arm-`B` angle of the certificate. -/
theorem T10_armC1_shift (m : ℕ) : Work.EL.T^[10] (armC1 (m + 2)) = armB1 m := by
  rw [T_iterate_ten, ArmC1.armC1_eq (m + 2), ArmC1.armB1_eq m]
  have hpow : (64:ℝ)^(m+2) = (64:ℝ)^m * 4096 := by rw [pow_add]; norm_num
  rw [hpow]
  -- absorb the integer part produced by the multiplication by `1024`
  have h1 : Int.fract (1024 * Int.fract (37/63 + (4624/21483 : ℝ)/((64:ℝ)^m*4096)))
      = Int.fract (1024 * (37/63 + (4624/21483 : ℝ)/((64:ℝ)^m*4096))) :=
    ArmC1.fract_mul_fract 1024 _
  rw [h1, ArmC1.key_arith ((64:ℝ)^m) (pow_ne_zero _ (by norm_num))]
  -- `601` is an integer, so it disappears in `Int.fract`
  rw [Int.fract_eq_fract]
  exact ⟨601, by push_cast; ring⟩

theorem T10_armC1 (n : ℕ) (hn : 2 ≤ n) :
    Work.EL.T^[10] (Work.ELNest.armC1 n) = Work.ELNest.armB1 (n - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + m - 2 = m from by omega, show 2 + m = m + 2 from by omega]
  exact T10_armC1_shift m

end Work.ELNest
