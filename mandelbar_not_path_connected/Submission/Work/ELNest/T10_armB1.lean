/-
# `T10_armB1`: the tenth iterate of the angle map sends the `B`-arm pair to the `A`-arm pair

Area `Submission/Work/ELNest/`.  This file proves the `B → A` step of the arm rotation of the
equator-leak argument: the degree-`1024` map `F c = (T_c)^{10}`, whose action on rays is
`T^[10]`, sends the level-`n` first angle of the arm pair `B` (the arm `(25/63, 37/63)`) to the
level-`(n-2)` first angle of the arm pair `A` (the arm `(22/63, 25/63)`):

    T^[10] (armB1 n) = armA1 (n - 2)      (n ≥ 2).

Recall the definitions (`Submission/Work/ELNest/Defs.lean`):

    centred x    = Int.fract (x + 1/2) - 1/2
    contract t fix N = Int.fract (fix + centred (t - fix) / N)
    armB1 n     = contract (461/1023) (25/63) (64^n)
    armA1 n     = contract alpha1 (22/63) (64^n),   alpha1 = 371/1023.

The statement is pure arithmetic.  Since all the arms angles involved are very close to the
contraction centre `fix` (`centred (t - fix) = t - fix`, the argument lying in `(-1/2, 1/2)`)
and the contracted value lies in `[0, 1)`, both `contract`s evaluate to the plain affine
expression:

    armB1 n = 25/63 + (461/1023 - 25/63)/64^n,     armA1 m = 22/63 + (alpha1 - 22/63)/64^m.

Then `T^[10] θ = Int.fract (1024 θ)` (`T_iterate_ten`), and the key numerical congruence

    1024 · armB1 n = 406 + armA1 (n - 2)

(valid for `n ≥ 2`) is a computation with `1024 · (461/1023 - 25/63) = 4096 · (alpha1 - 22/63)`
and `64^n = 64^{n-2} · 4096`): the integer `406` and the fractional part `armA1 (n-2) ∈ [0,1)`
disappear in `Int.fract`.
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


open scoped Topology ComplexConjugate

namespace Work.ELNest

/-! ## `centred` on small arguments -/

/-- `centred` is the identity on the open interval `(-1/2, 1/2)`: there `x + 1/2 ∈ (0, 1)` has
fractional part `x + 1/2`. -/
lemma centred_eq_self {x : ℝ} (h1 : -(1 / 2 : ℝ) < x) (h2 : x < 1 / 2) : centred x = x := by
  unfold centred
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  ring

/-! ## The two arm angles as affine expressions -/

/-- The `B`-arm angle `armB1 n` is the contraction centre `25/63` plus the (positive, tiny)
displacement `(461/1023 - 25/63)/64^n`. -/
lemma armB1_eq (n : ℕ) : armB1 n = 25 / 63 + (461 / 1023 - 25 / 63) / (64 : ℝ) ^ n := by
  unfold armB1 contract
  rw [centred_eq_self (x := 461 / 1023 - 25 / 63) (by norm_num) (by norm_num)]
  push_cast
  have hd0 : 0 ≤ (461 / 1023 - 25 / 63 : ℝ) := by norm_num
  have h1 : (1 : ℝ) ≤ (64 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hle : (461 / 1023 - 25 / 63) / (64 : ℝ) ^ n ≤ 461 / 1023 - 25 / 63 :=
    div_le_self hd0 h1
  have hlow : 0 ≤ 25 / 63 + (461 / 1023 - 25 / 63) / (64 : ℝ) ^ n :=
    add_nonneg (by norm_num) (div_nonneg hd0 (pow_nonneg (by norm_num) n))
  have hlt : 25 / 63 + (461 / 1023 - 25 / 63) / (64 : ℝ) ^ n < 1 := by
    have hup : (25 / 63 : ℝ) + (461 / 1023 - 25 / 63) = 461 / 1023 := by norm_num
    have hb : (461 / 1023 : ℝ) < 1 := by norm_num
    linarith
  rw [Int.fract_eq_self.mpr ⟨hlow, hlt⟩]

/-- The `A`-arm angle `armA1 m` is the contraction centre `22/63` plus the displacement
`(alpha1 - 22/63)/64^m`. -/
lemma armA1_eq (m : ℕ) : armA1 m = 22 / 63 + (alpha1 - 22 / 63) / (64 : ℝ) ^ m := by
  unfold armA1 contract
  rw [centred_eq_self (x := alpha1 - 22 / 63) (by unfold alpha1; norm_num)
    (by unfold alpha1; norm_num)]
  push_cast
  have he0 : 0 ≤ (alpha1 - 22 / 63 : ℝ) := by unfold alpha1; norm_num
  have h1 : (1 : ℝ) ≤ (64 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hle : (alpha1 - 22 / 63) / (64 : ℝ) ^ m ≤ alpha1 - 22 / 63 := div_le_self he0 h1
  have hlow : 0 ≤ 22 / 63 + (alpha1 - 22 / 63) / (64 : ℝ) ^ m :=
    add_nonneg (by norm_num) (div_nonneg he0 (pow_nonneg (by norm_num) m))
  have hlt : 22 / 63 + (alpha1 - 22 / 63) / (64 : ℝ) ^ m < 1 := by
    have hup : (22 / 63 : ℝ) + (alpha1 - 22 / 63) = alpha1 := by ring
    have hb : (alpha1 : ℝ) < 1 := by unfold alpha1; norm_num
    linarith
  rw [Int.fract_eq_self.mpr ⟨hlow, hlt⟩]

/-- The `A`-arm angles lie in `[0, 1)`. -/
lemma armA1_mem (m : ℕ) : 0 ≤ armA1 m ∧ armA1 m < 1 := by
  rw [armA1_eq m]
  have he0 : 0 ≤ (alpha1 - 22 / 63 : ℝ) := by unfold alpha1; norm_num
  have h1 : (1 : ℝ) ≤ (64 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hle : (alpha1 - 22 / 63) / (64 : ℝ) ^ m ≤ alpha1 - 22 / 63 := div_le_self he0 h1
  refine ⟨add_nonneg (by norm_num) (div_nonneg he0 (pow_nonneg (by norm_num) m)), ?_⟩
  have hup : (22 / 63 : ℝ) + (alpha1 - 22 / 63) = alpha1 := by ring
  have hb : (alpha1 : ℝ) < 1 := by unfold alpha1; norm_num
  linarith

/-! ## The numerical congruence -/

/-- **The key congruence.**  Multiplying the level-`n` `B`-arm angle by `1024 = (-2)^{10}`
gives the level-`(n-2)` `A`-arm angle plus the integer `406`: indeed
`1024·(461/1023 - 25/63) = 4096·(alpha1 - 22/63)` and `1024·25/63 = 406 + 22/63`, while
`64^n = 64^{n-2}·4096` for `n ≥ 2`. -/
lemma armB1_mul (n : ℕ) (hn : 2 ≤ n) :
    (1024 : ℝ) * armB1 n = 406 + armA1 (n - 2) := by
  rw [armB1_eq n, armA1_eq (n - 2)]
  have key : (1024 : ℝ) * ((461 / 1023 - 25 / 63) / (64 : ℝ) ^ n)
      = (alpha1 - 22 / 63) / (64 : ℝ) ^ (n - 2) := by
    have hp : (64 : ℝ) ^ n = (64 : ℝ) ^ (n - 2) * 4096 := by
      nth_rewrite 1 [show n = (n - 2) + 2 by omega]
      rw [pow_add]
      norm_num
    rw [hp]
    have hne : (64 : ℝ) ^ (n - 2) ≠ 0 := by positivity
    field_simp
    norm_num [alpha1]
  have h1 : (1024 : ℝ) * (25 / 63) = 406 + 22 / 63 := by norm_num
  rw [mul_add, h1, key]
  ring

/-! ## The theorem -/

theorem T10_armB1 (n : ℕ) (hn : 2 ≤ n) :
    Work.EL.T^[10] (Work.ELNest.armB1 n) = Work.ELNest.armA1 (n - 2) := by
  rw [T_iterate_ten, armB1_mul n hn]
  have hcast : (406 : ℝ) = ((406 : ℤ) : ℝ) := by norm_num
  rw [hcast, add_comm, Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr (armA1_mem (n - 2))

end Work.ELNest
