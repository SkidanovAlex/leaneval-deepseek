import Mathlib

/-!
# DSTRI: the characteristic trichotomy of a local domain

This area provides the vocabulary and the basic API for the three characteristic
regimes of a local (commutative, unital) ring `R` with residue field
`k = ResidueField R = R ⧸ maximalIdeal R`:

* `EqualCharZero R` : `char R = 0 = char k` (equal characteristic zero),
* `EqualCharPos R`  : `char R = p` for some prime `p` (equal characteristic `p`),
* `MixedChar R`     : `char R = 0` and `char k = p` for some prime `p` (mixed characteristic).

For a local *domain* exactly one of the three holds: existence is
`Work.DSTRI.Regime.regime_trichotomy` and uniqueness is
`Work.DSTRI.Regime.regimes_pairwise_exclusive`; the paper's `area_TRI` disjunction
(`DSMap.area_TRI_proved`, module `Submission.Work.DSTRI.Main`) is an immediate
corollary.  The intended use in the direct-summand proof is the case split in
`DSMap.main_dsplit`, where the three regimes are dispatched to the areas
EQ0 / EQP / MIX respectively.

Mathlib has `CharP.exists'`, which gives the trichotomy of a *single* ring
(`CharZero R ∨ ∃ p, p.Prime ∧ CharP R p` for a domain), and the residue-field
lemmas `Work.DSTRI.Residue.charP_residueField` (positive characteristic descends
to the residue field) and `Work.DSTRI.Regime.equalCharZero_iff_residue_charZero`
(characteristic zero is detected on the residue field) justify the word "equal"
in `EqualCharZero` / `EqualCharPos`; the whole content of the area is combining
these two.
-/

universe u

namespace Work.DSTRI

open IsLocalRing

section CharPos

variable (R : Type u) [CommRing R]

/-- **Equal positive characteristic**: `R` has characteristic `p` for some prime `p`.
For a local ring this also forces its residue field to have characteristic `p`. -/
def EqualCharPos : Prop := ∃ p : ℕ, p.Prime ∧ CharP R p

variable {R}

lemma EqualCharPos.primeChar (h : EqualCharPos R) : ∃ p : ℕ, p.Prime ∧ CharP R p := h

end CharPos

section Local

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- **Equal characteristic zero**: both `R` and its residue field have characteristic `0`. -/
def EqualCharZero : Prop := CharZero R ∧ CharZero (ResidueField R)

/-- **Mixed characteristic `(0, p)`**: `R` has characteristic `0` while its residue field has
characteristic the prime `p`. -/
def MixedChar : Prop := ∃ p : ℕ, p.Prime ∧ CharZero R ∧ CharP (ResidueField R) p

variable {R}

lemma EqualCharZero.charZero (h : EqualCharZero R) : CharZero R := h.1

lemma EqualCharZero.residue (h : EqualCharZero R) : CharZero (ResidueField R) := h.2

lemma MixedChar.prime (h : MixedChar R) : h.choose.Prime := h.choose_spec.1

lemma MixedChar.charZero (h : MixedChar R) : CharZero R := h.choose_spec.2.1

lemma MixedChar.residue (h : MixedChar R) : CharP (ResidueField R) h.choose := h.choose_spec.2.2

end Local

end Work.DSTRI
