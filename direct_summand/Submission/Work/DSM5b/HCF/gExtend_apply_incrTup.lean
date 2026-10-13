import Mathlib
import Submission.Work.DSM5b.HCF.LksAux
import Submission.Work.DSM5b.HCF.HtcAboveAux

/-!
# `gExtend` is a section on the increasing tuples

`Work.DSM5b.HCF.gExtend 𝒜 k q hk y` extends a sorted cochain `y : Stc ℰ q` (where
`ℰ = CoeffSys.exactlyCoeff 𝒜 k` and `q + 1 = k`) to an honest cochain: at a tuple `τ` whose range has
`k` elements it is the sign section of the block `tupRng τ`, and it is `0` at the other tuples.

This file records the elementary fact that the extension *is* the cochain `y` on the increasing
tuples: on an increasing tuple `τ₀` its range has `q + 1 = k` elements, the block sign of an
increasing tuple is `1` (`gSignOfR_self`), the block value is the value of `y` at the increasing
enumeration of the range (`gBlockVal` plus `htcAbove_res_eq_cast`), and the increasing enumeration
of `tupRng τ₀` is `τ₀` itself (`gIncrTup_eq_of_range_eq`).
-/

namespace Work.DSM5b.HCF

universe u

open Classical Finset

/-- **Transport of the values of a family of cochains along an equality of increasing tuples.**

For `F : ∀ s : IncrTuple q, M (tupRng s.1)` and an equality `h : t = u` of increasing tuples, the
transport of `F t` along the induced equality `tupRng t.1 = tupRng u.1` of the ranges is `F u`.
(The content is that the ranges of two *equal* tuples coincide; the equality of ranges is the one
induced by `h`, and the transport is the coherent one.) -/
lemma congrArg_tupRng_eq_rec_apply {ι : Type u} [DecidableEq ι] [LinearOrder ι] {q : ℕ}
    {M : Finset ι → Sort*} {t u : IncrTuple (ι := ι) q}
    (F : ∀ s : IncrTuple (ι := ι) q, M (Work.DSM5b.tupRng s.1)) (h : t = u) :
    congrArg (fun s : IncrTuple (ι := ι) q => Work.DSM5b.tupRng s.1) h ▸ F t = F u := by
  cases h
  rfl

theorem gExtend_apply_incrTup {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k q : ℕ) (hk : q + 1 = k)
    (y : Work.DSM5b.Stc (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) q)
    (τ₀ : Work.DSM5b.IncrTuple (ι := ι) q) :
    Work.DSM5b.HCF.gExtend 𝒜 k q hk y τ₀.1 = y τ₀ := by
  have hcard : (Work.DSM5b.tupRng τ₀.1).card = k := by
    rw [card_tupRng_of_isIncr τ₀, hk]
  rw [gExtend_of_card 𝒜 k q hk y τ₀.1 hcard]
  rw [gSignOfR_self (R := R) (hk.trans hcard.symm) ⟨τ₀.1, rfl⟩ τ₀.2, one_smul]
  rw [gBlockVal]
  rw [htcAbove_res_eq_cast (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k)
        (tupRng_gIncrTup (Work.DSM5b.tupRng τ₀.1) q (hk.trans hcard.symm))
        (y (gIncrTup (Work.DSM5b.tupRng τ₀.1) q (hk.trans hcard.symm)))]
  have hg : gIncrTup (Work.DSM5b.tupRng τ₀.1) q (hk.trans hcard.symm) = τ₀ :=
    (gIncrTup_eq_of_range_eq (hk.trans hcard.symm) τ₀ rfl).symm
  rw [show tupRng_gIncrTup (Work.DSM5b.tupRng τ₀.1) q (hk.trans hcard.symm)
        = congrArg (fun s : IncrTuple (ι := ι) q => Work.DSM5b.tupRng s.1) hg
      from Subsingleton.elim _ _]
  exact congrArg_tupRng_eq_rec_apply y hg

end Work.DSM5b.HCF
