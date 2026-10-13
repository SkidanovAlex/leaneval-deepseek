import Mathlib
import Submission.Work.DSREG.Defs

/-!
# DSREG: Krull dimension of a quotient by one element, and discrete arithmetic in `WithBot ℕ∞`

* `Work.DSREG.ringKrullDim_le_quotient_span_add_one`: killing an element of the maximal ideal of a
  Noetherian local ring drops the Krull dimension by at most one.
* `Work.DSREG.natCast_le_of_succ_le_add_one`: discrete arithmetic in `WithBot ℕ∞`, used to extract
  a lower bound for the dimension from that inequality.
* `Work.DSREG.height_add_coheight_le_krullDim`: height plus coheight is at most the Krull
  dimension.
-/

namespace Work.DSREG

open IsLocalRing

universe u

/-- Killing one element of the maximal ideal of a Noetherian local ring drops the Krull dimension
by at most one. -/
theorem ringKrullDim_le_quotient_span_add_one (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (x : R) (hx : x ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
  have hj : Ring.jacobson R = maximalIdeal R := by
    rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have h : ({x} : Set R) ⊆ Ring.jacobson R := by
    rw [Set.singleton_subset_iff, hj]
    exact hx
  calc ringKrullDim R
      ≤ ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + ({x} : Set R).encard :=
        ringKrullDim_le_ringKrullDim_quotient_add_encard {x} h
    _ = ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by simp

/-- Discrete arithmetic in `WithBot ℕ∞`: `n + 1 ≤ b + 1` forces `n ≤ b`. -/
theorem natCast_le_of_succ_le_add_one {b : WithBot ℕ∞} {n : ℕ}
    (h : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ b + 1) : ((n : ℕ) : WithBot ℕ∞) ≤ b := by
  by_contra hb
  have hb' : b < ((n : ℕ) : WithBot ℕ∞) := not_le.mp hb
  have hb2 : b + 1 ≤ ((n : ℕ) : WithBot ℕ∞) := ENat.WithBot.add_one_le_natCast_iff.mpr hb'
  have hle : (((n : ℕ) : WithBot ℕ∞) + 1) ≤ ((n : ℕ) : WithBot ℕ∞) := by
    calc (((n : ℕ) : WithBot ℕ∞) + 1) = ((n + 1 : ℕ) : WithBot ℕ∞) := by push_cast; ring
      _ ≤ b + 1 := h
      _ ≤ ((n : ℕ) : WithBot ℕ∞) := hb2
  exact absurd (ENat.WithBot.add_one_le_natCast_iff.mp hle) (lt_irrefl _)

/-- Height plus coheight of an element of a nonempty preorder is at most the Krull dimension. -/
theorem height_add_coheight_le_krullDim {α : Type*} [Preorder α] [Nonempty α] (a : α) :
    ↑(Order.height a + Order.coheight a) ≤ Order.krullDim α := by
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a => Order.height a + Order.coheight a) a)

end Work.DSREG
