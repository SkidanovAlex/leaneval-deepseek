/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — the integer angle model `ℤ/1023` and its bridge to the real circle

The finite certificate of the portrait argument (`Cert.lean`) is checked on the angle model
`j ↦ j/1023` (`0 ≤ j < 1023`), where the angle map `T θ = -2θ mod 1` is the map `TN` of
`Defs.lean`.  This file contains the bridges between the integer model and the real circle: the
computation of `Int.fract ((b - a)/1023)`, the equivariance of the angle maps, and the arithmetic
of the four surviving angles `371, 372, 403, 404`.
-/
import Submission.Work.SeedSimple2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Function
open scoped Topology

noncomputable section

namespace Work.SeedSimple2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## `Int.fract` of `(b - a)/1023` -/

/-- The representative in `[0,1023)` of `(b - a) mod 1023`, for `a, b < 1023`. -/
def subB (b a : ℕ) : ℕ := (b + 1023 - a) % 1023

theorem subB_lt (b a : ℕ) : subB b a < 1023 := Nat.mod_lt _ (by norm_num)

/-- **The bridge of `Int.fract ((b-a)/1023)`** (for `a, b < 1023`). -/
theorem fract_sub_div (a b : ℕ) (ha : a < 1023) (hb : b < 1023) :
    Int.fract (((b : ℝ) - a) / 1023) = ((subB b a : ℕ) : ℝ) / 1023 := by
  have hcast : ((b : ℝ) - a) = (((b : ℤ) - a : ℤ) : ℝ) := by push_cast; ring
  rw [hcast, ← Nat.cast_ofNat (n := 1023),
    Int.fract_div_intCast_eq_div_intCast_mod (m := (b : ℤ) - a) (n := 1023)]
  have hmod : (((b : ℤ) - a) % ((1023 : ℕ) : ℤ)) = ((subB b a : ℕ) : ℤ) := by
    rw [subB, Int.natCast_emod]
    have h2 : ((b + 1023 - a : ℕ) : ℤ) = (b : ℤ) + ((1023 : ℕ) : ℤ) - a := by
      rw [Nat.cast_sub (by omega : a ≤ b + 1023)]
      push_cast
      ring
    have h3 : ((b : ℤ) + ((1023 : ℕ) : ℤ) - a) % ((1023 : ℕ) : ℤ)
        = ((b : ℤ) - a) % ((1023 : ℕ) : ℤ) := by
      rw [show (b : ℤ) + ((1023 : ℕ) : ℤ) - a = ((b : ℤ) - a) + ((1023 : ℕ) : ℤ) by ring]
      exact Int.add_emod_right ((b : ℤ) - a) ((1023 : ℕ) : ℤ)
    rw [h2, h3]
  rw [hmod]
  norm_num

/-! ## The in-arc and unlinked predicates of the integer model -/

/-- The in-arc predicate of the integer model: `x` lies in the open counterclockwise arc `(a,b)`,
computed on the representatives in `[0,1023)`. -/
def inArcP (x a b : ℕ) : Prop := 0 < subB x a ∧ subB x a < subB b a

/-- The Boolean check of the in-arc predicate, computable by the kernel. -/
def inArcB (x a b : ℕ) : Bool := Nat.blt 0 (subB x a) && Nat.blt (subB x a) (subB b a)

theorem inArcB_eq_true (x a b : ℕ) : (inArcB x a b = true) ↔ inArcP x a b := by
  simp [inArcB, inArcP, Nat.blt_eq]

theorem inArcP_lt_iff (p q : ℕ) : (p : ℝ) / 1023 < (q : ℝ) / 1023 ↔ p < q := by
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 1023), Nat.cast_lt]

theorem inArcP_pos_iff (p : ℕ) : (0 : ℝ) < (p : ℝ) / 1023 ↔ 0 < p := by
  rw [div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 1023), Nat.cast_pos]

/-- **The bridge of the arc predicate** (for `x, a, b < 1023`). -/
theorem inArcP_iff (x a b : ℕ) (hx : x < 1023) (ha : a < 1023) (hb : b < 1023) :
    inArcP x a b ↔
      Work.ELPull.InArc ((x : ℝ) / 1023) ((a : ℝ) / 1023) ((b : ℝ) / 1023) := by
  have hx' : ((x : ℝ) - a) / 1023 = (x : ℝ) / 1023 - (a : ℝ) / 1023 := by ring
  have hb' : ((b : ℝ) - a) / 1023 = (b : ℝ) / 1023 - (a : ℝ) / 1023 := by ring
  have e1 : Int.fract ((x : ℝ) / 1023 - (a : ℝ) / 1023) = ((subB x a : ℕ) : ℝ) / 1023 := by
    rw [← hx']; exact fract_sub_div a x ha hx
  have e2 : Int.fract ((b : ℝ) / 1023 - (a : ℝ) / 1023) = ((subB b a : ℕ) : ℝ) / 1023 := by
    rw [← hb']; exact fract_sub_div a b ha hb
  simp only [inArcP, Work.ELPull.InArc, Work.ELPull.arcLen, e1, e2]
  exact and_congr (inArcP_pos_iff _).symm (inArcP_lt_iff _ _).symm

/-- The unlinked predicate of the integer model. -/
def unlinkedP (a b c d : ℕ) : Prop :=
  (inArcP c a b ↔ inArcP d a b) ∧ (inArcP a c d ↔ inArcP b c d)

/-- The Boolean checker of the unlinked predicate. -/
def unlinkedB (a b c d : ℕ) : Bool :=
  (inArcB c a b == inArcB d a b) && (inArcB a c d == inArcB b c d)

/-- **The bridge of the unlinked predicate** (for the four angles `< 1023`). -/
theorem unlinkedB_eq_true (a b c d : ℕ) (ha : a < 1023) (hb : b < 1023) (hc : c < 1023)
    (hd : d < 1023) :
    (unlinkedB a b c d = true) ↔
      Work.ELPull.Unlinked ((a : ℝ) / 1023) ((b : ℝ) / 1023) ((c : ℝ) / 1023)
        ((d : ℝ) / 1023) := by
  have hb' : ∀ p q : Bool, (p == q) = true ↔ (p = true ↔ q = true) := by
    intro p q
    rw [beq_iff_eq]
    exact Bool.coe_iff_coe.symm
  rw [unlinkedB, Bool.and_eq_true, hb', hb', inArcB_eq_true, inArcB_eq_true, inArcB_eq_true,
    inArcB_eq_true]
  simp only [Work.ELPull.Unlinked]
  exact and_congr (iff_congr (inArcP_iff c a b hc ha hb) (inArcP_iff d a b hd ha hb))
    (iff_congr (inArcP_iff a c d ha hc hd) (inArcP_iff b c d hb hc hd))

theorem not_unlinked_of_unlinkedB_false (a b c d : ℕ) (ha : a < 1023) (hb : b < 1023)
    (hc : c < 1023) (hd : d < 1023) (h : unlinkedB a b c d = false) :
    ¬ Work.ELPull.Unlinked ((a : ℝ) / 1023) ((b : ℝ) / 1023) ((c : ℝ) / 1023)
        ((d : ℝ) / 1023) := by
  intro hp
  rw [(unlinkedB_eq_true a b c d ha hb hc hd).mpr hp] at h
  exact Bool.noConfusion h

/-! ## The angle map on `ℤ/1023` -/

theorem TN_lt (j : ℕ) : TN j < 1023 := Nat.mod_lt _ (by norm_num)

/-- **The bridge of the angle map**: on the `/1023` model, `T` is `TN`. -/
theorem T_div (j : ℕ) :
    Work.EL.T ((j : ℝ) / 1023) = ((TN j : ℕ) : ℝ) / 1023 := by
  have hr : (2 * j) % 1023 ≤ 1023 := le_of_lt (Nat.mod_lt _ (by norm_num))
  have hlin : -2 * ((j : ℝ) / 1023) =
      (((1023 - (2 * j) % 1023 : ℕ)) : ℝ) / 1023 - (((2 * j / 1023 + 1 : ℕ)) : ℝ) := by
    have h2j : (2 * j : ℝ) = (((2 * j) % 1023 : ℕ) : ℝ) + (((2 * j) / 1023 : ℕ) : ℝ) * 1023 := by
      have h'' : (((2 * j) % 1023 : ℕ) : ℝ) + (((2 * j) / 1023 : ℕ) : ℝ) * (1023 : ℝ)
          = ((2 * j : ℕ) : ℝ) := by
        norm_cast
        rw [mul_comm (2 * j / 1023) 1023, Nat.mod_add_div]
      rw [h'']
      push_cast
      ring
    have hc : (((1023 - (2 * j) % 1023 : ℕ)) : ℝ) = 1023 - (((2 * j) % 1023 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hr]; norm_num
    have hq : (((2 * j / 1023 + 1 : ℕ)) : ℝ) = (((2 * j) / 1023 : ℕ) : ℝ) + 1 := by push_cast; ring
    have hmain : -2 * (j : ℝ) = (1023 - (((2 * j) % 1023 : ℕ) : ℝ))
        - ((((2 * j) / 1023 : ℕ) : ℝ) + 1) * 1023 := by
      linarith [h2j]
    rw [hc, hq]
    field_simp
    linarith
  rw [Work.EL.T, hlin, Int.fract_sub_natCast]
  rcases eq_or_ne ((2 * j) % 1023) 0 with hr0 | hr0
  · have hTN : TN j = 0 := by simp [TN, hr0]
    rw [hTN, hr0, Nat.sub_zero]
    norm_num
  · have hTN : TN j = 1023 - (2 * j) % 1023 := by
      unfold TN
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hTN]
    refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
    rw [div_lt_one (by norm_num)]
    exact_mod_cast (by omega : 1023 - (2 * j) % 1023 < 1023)

/-- **Iterated bridge**: `T^i (j/1023) = TN^i j /1023`. -/
theorem T_iterate_div (j : ℕ) (i : ℕ) :
    (Work.EL.T^[i]) ((j : ℝ) / 1023) = (((TN^[i]) j : ℕ) : ℝ) / 1023 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, T_div]

/-! ## The arithmetic of the survivor angles -/

theorem TN_alpha1 : TN α₁N = 281 := by decide
theorem TN_alpha2 : TN α₂N = 215 := by decide
theorem gN_alpha1 : gN α₁N = α₂N := by decide
theorem gN_alpha2 : gN α₂N = α₁N := by decide
theorem gN_372 : gN 372 = 372 := by decide
theorem gN_403 : gN 403 = 403 := by decide
theorem FN_alpha1 : FN α₁N = α₁N := by decide
theorem FN_alpha2 : FN α₂N = α₂N := by decide
theorem alpha1N_lt : α₁N < 1023 := by decide
theorem alpha2N_lt : α₂N < 1023 := by decide
theorem survivors_371 : (371 : ℕ) ∈ survivors := by decide
theorem survivors_372 : (372 : ℕ) ∈ survivors := by decide
theorem survivors_403 : (403 : ℕ) ∈ survivors := by decide
theorem survivors_404 : (404 : ℕ) ∈ survivors := by decide

/-- The two root angles in the `/1023` model are `Work.EL.alpha1`, `Work.EL.alpha2`. -/
theorem alpha1_eq : ((α₁N : ℕ) : ℝ) / 1023 = Work.EL.alpha1 := by
  norm_num [α₁N, Work.EL.alpha1]

theorem alpha2_eq : ((α₂N : ℕ) : ℝ) / 1023 = Work.EL.alpha2 := by
  norm_num [α₂N, Work.EL.alpha2]

/-- `372/1023 = 12/33` lies in the arc `(α₁, α₂)`. -/
theorem inArc_372 : Work.ELPull.InArc ((372 : ℝ) / 1023) Work.EL.alpha1 Work.EL.alpha2 := by
  rw [← alpha1_eq, ← alpha2_eq]
  exact (inArcP_iff 372 371 404 (by norm_num) (by norm_num) (by norm_num)).mp
    (by norm_num [inArcP, subB])

/-- `403/1023 = 13/33` lies in the arc `(α₁, α₂)`. -/
theorem inArc_403 : Work.ELPull.InArc ((403 : ℝ) / 1023) Work.EL.alpha1 Work.EL.alpha2 := by
  rw [← alpha1_eq, ← alpha2_eq]
  exact (inArcP_iff 403 371 404 (by norm_num) (by norm_num) (by norm_num)).mp
    (by norm_num [inArcP, subB])

end Work.SeedSimple2

end
