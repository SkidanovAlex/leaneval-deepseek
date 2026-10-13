import Mathlib
import Submission.Work.DSREG.Main

/-!
# Killing a minimal generator of the maximal ideal of a regular local ring

Let `A` be a regular local ring with maximal ideal `𝔪`, and let `x ∈ 𝔪 \ 𝔪²` (a *minimal*
generator of `𝔪`, i.e. a regular parameter).  Then the quotient `A ⧸ (x)` is again a regular
local ring, and both its Krull dimension and its embedding dimension are one less than those
of `A`.

The two numerical statements follow from the two general inequalities

* `μ(𝔪 ⧸ x𝔪) ≤ μ(𝔪) - 1` — deleting a minimal generator of `𝔪` gives a generating set of the
  image of `𝔪` in `A ⧸ (x)`
  (`Work.DSREG.SpanFinrankQuotient.spanFinrank_maximalIdeal_quotient_span_le`), and
* `dim A ≤ dim (A ⧸ (x)) + 1` — Krull's theorem on killing one element
  (`Work.DSREG.ringKrullDim_le_quotient_span_add_one`), together with `dim ≤ μ(𝔪)` in the other
  direction (`ringKrullDim_le_spanFinrank_maximalIdeal`),

and from the regularity of `A`, which says `dim A = μ(𝔪)`.  Chaining these and using the fact
that `x ∈ 𝔪 \ 𝔪²` forces `𝔪 ≠ 0`, so that `μ(𝔪) ≥ 1`, gives
`μ(𝔪) - 1 ≤ dim (A ⧸ (x)) ≤ μ(𝔪 ⧸ x𝔪) ≤ μ(𝔪) - 1`; hence all three quantities agree and
`A ⧸ (x)` is regular local.

The statement is the one requested as `Work.DSNORM.quotient_span_isRegularLocalRing`; the same
statement appears as `Work.DSNORM.isRegularLocalRing_quotient_span_singleton` in the sibling file
`Submission/Work/DSNORM/isRegularLocalRing_quotient_span_singleton.lean`.
-/

namespace Work.DSNORM

theorem quotient_span_isRegularLocalRing (A : Type*) [CommRing A]
    [IsRegularLocalRing A] {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A)
    (hx2 : x ∉ IsLocalRing.maximalIdeal A ^ 2) [Nontrivial (A ⧸ Ideal.span {x})] :
    IsRegularLocalRing (A ⧸ Ideal.span {x}) ∧
      ringKrullDim (A ⧸ Ideal.span {x}) + 1 = ringKrullDim A ∧
      (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank + 1
        = (IsLocalRing.maximalIdeal A).spanFinrank := by
  classical
  set d := (IsLocalRing.maximalIdeal A).spanFinrank with hd
  -- `x ∈ 𝔪 \ 𝔪²` forces `𝔪 ≠ 0`, so `d ≥ 1`.
  have hd1 : 1 ≤ d := by
    by_contra h
    have h0 : d = 0 := by omega
    have hbot : IsLocalRing.maximalIdeal A = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot
        (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A))).mp (hd ▸ h0)
    have hx0 : x = 0 := by
      rw [hbot] at hx
      simpa using hx
    exact hx2 (by rw [hx0, hbot]; simp)
  -- the maximal ideal of `A ⧸ (x)` is the image of `𝔪`
  have hmax : IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})
      = (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x})) :=
    Work.DSREG.maximalIdeal_quotient_span_singleton A x
  -- deleting the minimal generator `x` leaves a generating set of the image of `𝔪`
  have he_le : (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank ≤ d - 1 := by
    rw [hmax]
    refine Work.DSREG.SpanFinrankQuotient.spanFinrank_maximalIdeal_quotient_span_le A x hx hx2
      (d - 1) ?_
    rw [← hd]
    omega
  -- `dim A = μ(𝔪) = d`, by regularity of `A`
  have hdimA : ringKrullDim A = (d : WithBot ℕ∞) := by
    rw [hd]
    exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  -- Krull: killing one element drops the dimension by at most one
  have hdimA_le : ringKrullDim A ≤ ringKrullDim (A ⧸ Ideal.span {x}) + 1 :=
    Work.DSREG.ringKrullDim_le_quotient_span_add_one A x hx
  -- hence `dim (A ⧸ (x)) ≥ d - 1`
  have hkey : ((d - 1 + 1 : ℕ) : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
    rw [Nat.sub_add_cancel hd1]
  have hdim_ge : ((d - 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ Ideal.span {x}) := by
    refine Work.DSREG.natCast_le_of_succ_le_add_one
      (b := ringKrullDim (A ⧸ Ideal.span {x})) (n := d - 1) ?_
    rw [hkey, ← hdimA]
    exact hdimA_le
  -- and `dim ≤ μ(𝔪)` always
  have hdim_le : ringKrullDim (A ⧸ Ideal.span {x})
      ≤ ((IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
    ringKrullDim_le_spanFinrank_maximalIdeal (A ⧸ Ideal.span {x})
  have he_le' : ((IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞)
      ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast he_le
  -- so `dim (A ⧸ (x)) = d - 1`
  have hdim_eq : ringKrullDim (A ⧸ Ideal.span {x}) = ((d - 1 : ℕ) : WithBot ℕ∞) :=
    le_antisymm (le_trans hdim_le he_le') hdim_ge
  -- and the two quantities `dim` and `μ` agree on the quotient: it is regular local
  have he_dim : ((IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞)
      = ringKrullDim (A ⧸ Ideal.span {x}) :=
    le_antisymm (he_le'.trans (le_of_eq hdim_eq.symm)) hdim_le
  have he_eq : (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank = d - 1 := by
    exact_mod_cast (he_dim.trans hdim_eq)
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (A ⧸ Ideal.span {x})
    (le_of_eq he_dim), ?_, ?_⟩
  · rw [hdim_eq, hdimA, ← Nat.sub_add_cancel hd1]
    push_cast
    ring
  · rw [he_eq]
    omega

end Work.DSNORM
