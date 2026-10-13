import Mathlib
import Submission.Work.DSM5b.HCF.GSurjSign
import Submission.Work.DSM5b.HCF.HtcAboveAux

/-!
# The extension of a sorted cochain to an honest cochain, on the size-`k` graded piece

Let `ℰ = Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k` be the coefficient system supported on the subsets
of size exactly `k`, and let `q` be a natural number with `q + 1 = k`.  The graded piece then lives in
degree `q`, and the honest complex `Htc ℰ q` decomposes into the blocks `GSurjIdx S₀ q` (the tuples
whose range is the `k`-element subset `S₀`).

This file contains the *extension* of a sorted cochain `y : Stc ℰ q` to an honest cochain:

* `gBlockVal 𝒜 k q y S₀ hq` — the value of `y` at the increasing enumeration of `S₀`, moved into
  the single coefficient module `ℰ.M S₀` by the restriction map along the equality of the two
  ranges;
* `gExtend 𝒜 k q hk y τ` — the extension: on the tuples `τ` whose range has `k` elements it is the
  sign section `τ ↦ sign(τ) • gBlockVal` of the block `tupRng τ` (the sign being the block sign of
  the block `tupRng τ`, i.e. the one relative to the increasing enumeration of `tupRng τ`), and it
  is `0` on the tuples whose range does not have `k` elements (where the coefficient module is a
  subsingleton).

The file also records the two elementary facts about the sign that make the block computations
independent of the presentation of the block: `gRefEquiv_val_congr` (the reference enumeration of a
finset depends only on the finset), `gPermOf_eq_of_apply_eq` (the sorting permutation is determined
by its effect on the values of the tuple) and the resulting `gPermOf_congr_block`,
`gSignOfR_congr_block`.
-/

namespace Work.DSM5b.HCF

universe u

open Classical Finset

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]

/-! ### The two reference enumerations of equal finsets agree -/

/-- The reference enumeration of a finset depends only on the finset. -/
lemma gRefEquiv_val_congr {S₀ S₀' : Finset ι} {q : ℕ} (hq : q + 1 = S₀.card)
    (hq' : q + 1 = S₀'.card) (he : S₀ = S₀') (i : Fin (q+1)) :
    ((gRefEquiv S₀ q hq i : ↥S₀) : ι) = ((gRefEquiv S₀' q hq' i : ↥S₀') : ι) := by
  rw [gRefEquiv_apply, gRefEquiv_apply]
  subst he
  rw [Subsingleton.elim hq.symm hq'.symm]

/-- **The sorting permutation is determined by its effect on the values of the tuple.** -/
lemma gPermOf_eq_of_apply_eq {S₀ : Finset ι} {q : ℕ} (hq : q + 1 = S₀.card)
    {τ : Fin (q+1) → ι} (ht : Work.DSM5b.tupRng τ = S₀) (π : Equiv.Perm (Fin (q+1)))
    (hπ : ∀ i, ((gRefEquiv S₀ q hq (π i) : ↥S₀) : ι) = τ i) :
    π = gPermOf (⟨τ, ht⟩ : GSurjIdx S₀ q) hq := by
  apply Equiv.ext
  intro i
  have h1 : gRefEquiv S₀ q hq (π i)
      = gRefEquiv S₀ q hq ((gPermOf (⟨τ, ht⟩ : GSurjIdx S₀ q) hq) i) := by
    apply Subtype.ext
    rw [hπ i, gPermOf, Equiv.trans_apply, Equiv.apply_symm_apply, gPosEquiv_apply]
  exact (gRefEquiv S₀ q hq).injective h1

/-- The sorting permutation of a tuple does not depend on the presentation of the block. -/
lemma gPermOf_congr_block {S₀ S₀' : Finset ι} {q : ℕ} (hq : q + 1 = S₀.card)
    (hq' : q + 1 = S₀'.card) (he : S₀ = S₀') {τ : Fin (q+1) → ι} (ht : Work.DSM5b.tupRng τ = S₀)
    (ht' : Work.DSM5b.tupRng τ = S₀') :
    gPermOf (⟨τ, ht⟩ : GSurjIdx S₀ q) hq = gPermOf (⟨τ, ht'⟩ : GSurjIdx S₀' q) hq' := by
  refine (gPermOf_eq_of_apply_eq hq ht _ (fun i => ?_)).symm
  have hπ : gPermOf (⟨τ, ht'⟩ : GSurjIdx S₀' q) hq' i
      = (gRefEquiv S₀' q hq').symm (⟨τ i, gMem ⟨τ, ht'⟩ i⟩ : ↥S₀') := by
    rw [gPermOf, Equiv.trans_apply, gPosEquiv, Equiv.ofBijective_apply]
  rw [hπ]
  rw [gRefEquiv_val_congr hq hq' he]
  rw [Equiv.apply_symm_apply]

/-- The sign of a tuple of the surjection complex does not depend on the presentation of the
block. -/
lemma gSignOfR_congr_block {S₀ S₀' : Finset ι} {q : ℕ} (hq : q + 1 = S₀.card)
    (hq' : q + 1 = S₀'.card) (he : S₀ = S₀') {τ : Fin (q+1) → ι} (ht : Work.DSM5b.tupRng τ = S₀)
    (ht' : Work.DSM5b.tupRng τ = S₀') :
    gSignOfR (R := R) (⟨τ, ht⟩ : GSurjIdx S₀ q) hq
      = gSignOfR (R := R) (⟨τ, ht'⟩ : GSurjIdx S₀' q) hq' := by
  have h : gSignOf (⟨τ, ht⟩ : GSurjIdx S₀ q) hq
      = gSignOf (⟨τ, ht'⟩ : GSurjIdx S₀' q) hq' := by
    rw [gSignOf, gSignOf, gPermOf_congr_block hq hq' he ht ht']
  rw [gSignOfR, gSignOfR, h]

/-! ### The block value and the extension -/

/-- The value of a sorted cochain `y` at the increasing enumeration of `S₀`, moved into the single
coefficient module `ℰ.M S₀` (by the restriction map along the equality of the two ranges). -/
noncomputable def gBlockVal (𝒜 : CoeffSys R ι) (k q : ℕ)
    (y : Stc (CoeffSys.exactlyCoeff 𝒜 k) q) (S₀ : Finset ι) (hq : q + 1 = S₀.card) :
    (CoeffSys.exactlyCoeff 𝒜 k).M S₀ :=
  (CoeffSys.exactlyCoeff 𝒜 k).res (le_of_eq (tupRng_gIncrTup S₀ q hq)) (y (gIncrTup S₀ q hq))

/-- **The extension of a sorted cochain to an honest cochain**, on the graded piece of size `k`:
on the tuples `τ` whose range has `k` elements it is the sign section of the block `tupRng τ`
(with the sign relative to the increasing enumeration of `tupRng τ`), and it is `0` on the other
tuples. -/
noncomputable def gExtend (𝒜 : CoeffSys R ι) (k q : ℕ) (hk : q + 1 = k)
    (y : Stc (CoeffSys.exactlyCoeff 𝒜 k) q) (τ : Fin (q+1) → ι) :
    (CoeffSys.exactlyCoeff 𝒜 k).M (Work.DSM5b.tupRng τ) :=
  if h : (Work.DSM5b.tupRng τ).card = k then
    gSignOfR (R := R) ⟨τ, rfl⟩ (hk.trans h.symm) •
      gBlockVal 𝒜 k q y (Work.DSM5b.tupRng τ) (hk.trans h.symm)
  else 0

lemma gExtend_of_card (𝒜 : CoeffSys R ι) (k q : ℕ) (hk : q + 1 = k)
    (y : Stc (CoeffSys.exactlyCoeff 𝒜 k) q) (τ : Fin (q+1) → ι)
    (h : (Work.DSM5b.tupRng τ).card = k) :
    gExtend 𝒜 k q hk y τ = gSignOfR (R := R) ⟨τ, rfl⟩ (hk.trans h.symm) •
      gBlockVal 𝒜 k q y (Work.DSM5b.tupRng τ) (hk.trans h.symm) :=
  dif_pos h

lemma gExtend_of_ne (𝒜 : CoeffSys R ι) (k q : ℕ) (hk : q + 1 = k)
    (y : Stc (CoeffSys.exactlyCoeff 𝒜 k) q) (τ : Fin (q+1) → ι)
    (h : (Work.DSM5b.tupRng τ).card ≠ k) : gExtend 𝒜 k q hk y τ = 0 :=
  dif_neg h

end Work.DSM5b.HCF
