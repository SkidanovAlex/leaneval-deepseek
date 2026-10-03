/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The concrete ultraproduct ring `P^U_{ω,τ} = W U ⧸ ker rk_ω`

[JZLA20, §3.2].  Let `U` be a ring with a twist `τ` (`MulSemiringAction (Multiplicative ℤ) U`),
`rk` a Sylvester rank function on `U` and `ω` a non-principal ultrafilter.  Then
`W U = ∏_{n ≥ 1} M_{n+1}(U)` carries the ultralimit `rkAmp ω rk` of the amplified ranks
`rk ⊗ id_{n+1}` (normalized by `n+1`), and

  `P^U_{ω,τ} = W U ⧸ ker rkAmp ω rk`

is the rank-zero quotient, carrying a *faithful* rank function `rkSP ω rk`.

This file exposes that quotient concretely — `SPideal`, `SP`, `mkSP`, `rkSP` — together with

* `rkSP_apply_mk` : the rank of a matrix over the quotient is the rank of any lift;
* `rkSP_faithful` : `rkSP` is faithful;
* `tok` : the `W U`-valued family of Toeplitz matrices of a skew Laurent *series*, together with
  its additive/multiplicative unit axioms.

The reason for exposing the construction is [JZLA20, (4)]: the Toeplitz family is a ring
homomorphism `U((t;τ)) →+* P^U_{ω,τ}` *after* passing to the quotient (see
`NaturalExtension/SeriesPsi.lean`).
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.blimRankW
import Submission.Work.ORHughesFree.NaturalExtension.blimRank_toeplitzT
import Submission.Work.ORHughesFree.Epic.exists_faithful_quotient
import Submission.Work.ORHughesFree.NaturalExtension.exists_powerSeriesToeplitz

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORHughesFree.NaturalExtension

open Matrix
open Work.ORHughesFree

variable {U : Type} [Ring U]

/-- The ultralimit rank on `W U = ∏_{n ≥ 1} M_{n+1}(U)`: the ultralimit of the ranks of the
block flattenings, normalized by `n + 1`. -/
noncomputable def rkAmp (ω : Ultrafilter ℕ) (rk : SylvesterRank U) : SylvesterRank (W U) :=
  (blimRankW (U := U) ω rk).choose

theorem rkAmp_apply (ω : Ultrafilter ℕ) (rk : SylvesterRank U) (k m : ℕ)
    (A : Matrix (Fin k) (Fin m) (W U)) :
    (rkAmp ω rk).rk k m A = blimRank ω rk k m A :=
  (blimRankW (U := U) ω rk).choose_spec k m A

/-- The rank-zero ideal of `rkAmp ω rk`, i.e. the kernel of the rank function on `W U`. -/
noncomputable abbrev SPideal (ω : Ultrafilter ℕ) (rk : SylvesterRank U) : Ideal (W U) :=
  Epic.rkZeroIdeal (rkAmp ω rk)

theorem mem_SPideal (ω : Ultrafilter ℕ) (rk : SylvesterRank U) (a : W U) :
    a ∈ SPideal ω rk ↔ (rkAmp ω rk).rk 1 1 (oneByOne a) = 0 :=
  Epic.mem_rkZeroIdeal (rkAmp ω rk) a

instance (ω : Ultrafilter ℕ) (rk : SylvesterRank U) : (SPideal ω rk).IsTwoSided :=
  Epic.rkZeroIdeal_isTwoSided (rkAmp ω rk)

/-- **The ring `P^U_{ω,τ}` of [JZLA20, §3.2]**, as the faithful quotient of `W U` by the
rank-zero ideal. -/
noncomputable abbrev SP (ω : Ultrafilter ℕ) (rk : SylvesterRank U) : Type :=
  W U ⧸ SPideal ω rk

/-- The quotient map `W U →+* P^U_{ω,τ}`. -/
noncomputable abbrev mkSP (ω : Ultrafilter ℕ) (rk : SylvesterRank U) : W U →+* SP ω rk :=
  Ideal.Quotient.mk (SPideal ω rk)

/-- The **faithful** rank function `rk_ω` of `P^U_{ω,τ}`. -/
noncomputable def rkSP (ω : Ultrafilter ℕ) (rk : SylvesterRank U) : SylvesterRank (SP ω rk) :=
  Epic.quotientRank (rkAmp ω rk)

/-- The rank of a matrix over `P^U_{ω,τ}` is the rank of any lift to `W U`. -/
theorem rkSP_apply_mk (ω : Ultrafilter ℕ) (rk : SylvesterRank U) (n m : ℕ)
    (A : Matrix (Fin n) (Fin m) (W U)) :
    (rkSP ω rk).rk n m (A.map (mkSP ω rk)) = (rkAmp ω rk).rk n m A := by
  have h : (Epic.matLift (SPideal ω rk) (A.map (mkSP ω rk))).map
      (Ideal.Quotient.mk (SPideal ω rk)) = A.map (Ideal.Quotient.mk (SPideal ω rk)) :=
    Epic.matLift_map (SPideal ω rk) _
  exact Epic.rk_eq_of_map_mk_eq (rkAmp ω rk) _ _ h

/-- `rk_ω` is faithful: an element of `P^U_{ω,τ}` of rank zero is zero. -/
theorem rkSP_faithful (ω : Ultrafilter ℕ) (rk : SylvesterRank U) : (rkSP ω rk).IsFaithful := by
  intro a ha
  have hmat : Epic.matLift (SPideal ω rk) (oneByOne a) =
      oneByOne (Epic.elLift (SPideal ω rk) a) := by
    ext i j
    simp [Epic.matLift, oneByOne]
  have ha' : (rkAmp ω rk).rk 1 1 (oneByOne (Epic.elLift (SPideal ω rk) a)) = 0 := by
    have ha'' : (rkAmp ω rk).rk 1 1 (Epic.matLift (SPideal ω rk) (oneByOne a)) = 0 := ha
    rwa [hmat] at ha''
  have hmem : Epic.elLift (SPideal ω rk) a ∈ SPideal ω rk :=
    (Epic.mem_rkZeroIdeal (rkAmp ω rk) _).mpr ha'
  have hzero : Ideal.Quotient.mk (SPideal ω rk) (Epic.elLift (SPideal ω rk) a) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rwa [Epic.mk_elLift] at hzero

/-! ## The Toeplitz family of a skew Laurent series -/

variable [MulSemiringAction (Multiplicative ℤ) U]

/-- The `W U`-valued Toeplitz family of a skew Laurent series `p`: its `n`-th coordinate is the
`(n+1) × (n+1)` Toeplitz matrix of `p`. -/
noncomputable def tok (p : SkewLaurentSeries U) : W U :=
  fun n => toeplitzSeries (n + 1) p

@[simp] theorem tok_apply (p : SkewLaurentSeries U) (n : ℕ) (r s : Fin (n + 1)) :
    tok p n r s =
      (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • p.1 (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ)) := rfl

theorem tok_add (p q : SkewLaurentSeries U) : tok (p + q) = tok p + tok q := by
  funext n
  exact toeplitzSeries_add (n + 1) p q

theorem tok_zero : tok (0 : SkewLaurentSeries U) = 0 := by
  funext n
  exact toeplitzSeries_zero (n + 1)

theorem tok_one : tok (1 : SkewLaurentSeries U) = 1 := by
  funext n
  exact toeplitzSeries_one (n + 1)

/-- The `n`-th coordinate of the multiplicativity defect of `tok` is the multiplicative defect of
the `(n+1) × (n+1)` Toeplitz matrix. -/
theorem tok_sub_mul_apply (p q : SkewLaurentSeries U) (n : ℕ) :
    (tok (p * q) - tok p * tok q) n =
      toeplitzSeries (n + 1) (p * q)
        - toeplitzSeries (n + 1) p * toeplitzSeries (n + 1) q := by
  rw [Pi.sub_apply, Pi.mul_apply]
  rfl

end Work.ORHughesFree.NaturalExtension
