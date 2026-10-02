/-
# `Work.ELRig.cert` — the arithmetic certificate of the equator-leak argument

The equator-leak (`ELRig`) proof consumes a finite list of arithmetic facts about the
angle-doubling map `T θ = Int.fract (-2 * θ)` of the antiholomorphic quadratic family:

* the root-portrait angles `α₁ = 371/1023`, `α₂ = 404/1023` form a period-`5` orbit of `T`
  (with `T^[5] α₁ = α₂`, `T^[5] α₂ = α₁`, hence `T^[10]` fixes both);
* the tripod angles `22/63, 25/63, 37/63` are cyclically permuted by `T^[4]`
  (with `T^[4] (22/63) = 37/63`, `T^[4] (25/63) = 22/63`, `T^[4] (37/63) = 25/63`), and
  `T^[4] (22/63 + 1) = 37/63` as well;
* each of `α₁`, `α₂` lies in the open cyclic arc `(22/63, 25/63)`.

All of these are pure rational arithmetic; the file reduces them to computations in `ℚ`,
where `Int.fract` of a ratio `p / N` is the residue `(-2 * p) % N` over `N`, so that a
finite iterate is evaluated by `norm_num` and `decide`.
-/
import Mathlib
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical

noncomputable section

namespace Work.ELRig

/-! ## The rational model of the angle map -/

/-- The angle map `θ ↦ fract (-2θ)` on the rationals. -/
def Tq (q : ℚ) : ℚ := Int.fract (-2 * q)

/-- A rational of the form `p / N`, the shape in which the certificate angles are presented. -/
abbrev qq (p : ℤ) (N : ℕ) : ℚ := (p : ℚ) / (N : ℚ)

/-- One step of `Tq` on a ratio `p / N`: it sends `p / N` to the residue `(-2 * p) % N`
over `N`.  This is `Int.fract_div_intCast_eq_div_intCast_mod`. -/
theorem Tq_qq (p : ℤ) (N : ℕ) : Tq (qq p N) = qq ((-2 * p) % N) N := by
  rw [Tq,
    show -2 * ((p : ℚ) / ((N : ℕ) : ℚ)) = (((-2 * p : ℤ)) : ℚ) / ((N : ℕ) : ℚ) by
      push_cast; ring,
    Int.fract_div_intCast_eq_div_intCast_mod]

/-- The real angle map agrees with the rational one under the canonical embedding. -/
theorem T_cast (q : ℚ) : Work.EL.T (q : ℝ) = ((Tq q : ℚ) : ℝ) := by
  rw [Work.EL.T, Tq, Rat.cast_fract]
  congr 1
  push_cast
  ring

/-- Iterating commutes with the embedding `ℚ → ℝ`. -/
theorem iterate_T_cast (n : ℕ) (q : ℚ) :
    Work.EL.T^[n] ((q : ℚ) : ℝ) = ((Tq^[n] q : ℚ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, T_cast]

/-! ## The certificate angles as rationals -/

theorem alpha1_eq : Work.EL.alpha1 = ((qq 371 1023 : ℚ) : ℝ) := by
  norm_num [Work.EL.alpha1, qq]

theorem alpha2_eq : Work.EL.alpha2 = ((qq 404 1023 : ℚ) : ℝ) := by
  norm_num [Work.EL.alpha2, qq]

theorem b2a_eq : Work.EL.b2a = ((qq 22 63 : ℚ) : ℝ) := by
  norm_num [Work.EL.b2a, qq]

theorem b2b_eq : Work.EL.b2b = ((qq 25 63 : ℚ) : ℝ) := by
  norm_num [Work.EL.b2b, qq]

theorem b2c_eq : Work.EL.b2c = ((qq 37 63 : ℚ) : ℝ) := by
  norm_num [Work.EL.b2c, qq]

theorem b2a_add_one_eq : Work.EL.b2a + 1 = ((qq 85 63 : ℚ) : ℝ) := by
  norm_num [Work.EL.b2a, qq]

/-! ## The five-fold and ten-fold iterates on the root-portrait angles -/

theorem Tq5_alpha1 : Tq^[5] (qq 371 1023) = qq 404 1023 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq]
  norm_num [qq]

theorem Tq5_alpha2 : Tq^[5] (qq 404 1023) = qq 371 1023 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq]
  norm_num [qq]

theorem Tq10_alpha1 : Tq^[10] (qq 371 1023) = qq 371 1023 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq]
  norm_num [qq]

theorem Tq10_alpha2 : Tq^[10] (qq 404 1023) = qq 404 1023 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq, Tq_qq]
  norm_num [qq]

/-! ## The four-fold iterate on the tripod angles -/

theorem Tq4_22 : Tq^[4] (qq 22 63) = qq 37 63 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [Tq_qq, Tq_qq, Tq_qq, Tq_qq]
  norm_num [qq]

theorem Tq4_25 : Tq^[4] (qq 25 63) = qq 22 63 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [Tq_qq, Tq_qq, Tq_qq, Tq_qq]
  norm_num [qq]

theorem Tq4_37 : Tq^[4] (qq 37 63) = qq 25 63 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [Tq_qq, Tq_qq, Tq_qq, Tq_qq]
  norm_num [qq]

theorem Tq4_85 : Tq^[4] (qq 85 63) = qq 37 63 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [Tq_qq, Tq_qq, Tq_qq, Tq_qq]
  norm_num [qq]

/-! ## The membership of the root-portrait angles in the arc `(22/63, 25/63)` -/

theorem InArc_alpha1 : Work.EL.InArc Work.EL.alpha1 Work.EL.b2a Work.EL.b2b := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : Int.fract (Work.EL.alpha1 - Work.EL.b2a) = Work.EL.alpha1 - Work.EL.b2a :=
    Int.fract_eq_self.mpr (by unfold Work.EL.alpha1 Work.EL.b2a; constructor <;> norm_num)
  have h2 : Int.fract (Work.EL.b2b - Work.EL.b2a) = Work.EL.b2b - Work.EL.b2a :=
    Int.fract_eq_self.mpr (by unfold Work.EL.b2b Work.EL.b2a; constructor <;> norm_num)
  rw [h1, h2]
  unfold Work.EL.alpha1 Work.EL.b2a Work.EL.b2b
  constructor <;> norm_num

theorem InArc_alpha2 : Work.EL.InArc Work.EL.alpha2 Work.EL.b2a Work.EL.b2b := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : Int.fract (Work.EL.alpha2 - Work.EL.b2a) = Work.EL.alpha2 - Work.EL.b2a :=
    Int.fract_eq_self.mpr (by unfold Work.EL.alpha2 Work.EL.b2a; constructor <;> norm_num)
  have h2 : Int.fract (Work.EL.b2b - Work.EL.b2a) = Work.EL.b2b - Work.EL.b2a :=
    Int.fract_eq_self.mpr (by unfold Work.EL.b2b Work.EL.b2a; constructor <;> norm_num)
  rw [h1, h2]
  unfold Work.EL.alpha2 Work.EL.b2a Work.EL.b2b
  constructor <;> norm_num

/-! ## The certificate -/

theorem cert :
    (Work.EL.T^[5] Work.EL.alpha1 = Work.EL.alpha2) ∧
    (Work.EL.T^[5] Work.EL.alpha2 = Work.EL.alpha1) ∧
    (Work.EL.T^[10] Work.EL.alpha1 = Work.EL.alpha1) ∧
    (Work.EL.T^[10] Work.EL.alpha2 = Work.EL.alpha2) ∧
    (Work.EL.T^[4] Work.EL.b2a = Work.EL.b2c) ∧
    (Work.EL.T^[4] Work.EL.b2b = Work.EL.b2a) ∧
    (Work.EL.T^[4] Work.EL.b2c = Work.EL.b2b) ∧
    Work.EL.InArc Work.EL.alpha1 Work.EL.b2a Work.EL.b2b ∧
    Work.EL.InArc Work.EL.alpha2 Work.EL.b2a Work.EL.b2b ∧
    (Work.EL.T^[4] (Work.EL.b2a + 1) = Work.EL.b2c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, InArc_alpha1, InArc_alpha2, ?_⟩
  · rw [alpha1_eq, alpha2_eq, iterate_T_cast, Tq5_alpha1]
  · rw [alpha2_eq, alpha1_eq, iterate_T_cast, Tq5_alpha2]
  · rw [alpha1_eq, iterate_T_cast, Tq10_alpha1]
  · rw [alpha2_eq, iterate_T_cast, Tq10_alpha2]
  · rw [b2a_eq, b2c_eq, iterate_T_cast, Tq4_22]
  · rw [b2b_eq, b2a_eq, iterate_T_cast, Tq4_25]
  · rw [b2c_eq, b2b_eq, iterate_T_cast, Tq4_37]
  · rw [b2a_add_one_eq, b2c_eq, iterate_T_cast, Tq4_85]

end Work.ELRig
