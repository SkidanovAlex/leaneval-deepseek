import Mathlib
import Submission.Work.DSM5b.HCF.Complex

/-!
# Blocks of the honest tuple complex

For a coefficient system `ℰ` on the finite subsets of `ι` and a finset `S₀`, the *block* of `S₀` in
degree `m` is the set of tuples `τ : Fin (m+1) → ι` with `tupRng τ = S₀` (`BlkIdx S₀ m`).  On a
block the coefficient modules `ℰ.M (tupRng τ)` are propositionally the same, and an element of a
block cochain can be moved into the single module `ℰ.M S₀` by the restriction map along the
inclusion `tupRng τ ⊆ S₀`.  Recording this *cast-free* presentation is the point of `blkVal`:

  `blkVal ℰ S₀ m z σ = ℰ.res (fun x hx => σ.2 ▸ hx) (z σ.1) : ℰ.M S₀`,

and `blkVal_eq_res` shows that it agrees with the restriction of `z` along any other proof of the
same inclusion (so that different presentations of `z`'s value on the block can be compared
without any `Eq.rec` bookkeeping).

The file also contains

* the elementary facts about the coefficient system `CoeffSys.exactlyCoeff 𝒜 k` (supported on the
  subsets of size exactly `k`) that reduce a cochain on the honest complex to the blocks of the
  `k`-element subsets;
* `swapBlk`, the adjacent transposition of two entries of a tuple with prescribed range;
* `incrBlk S₀ m h` (for `h : m + 1 = S₀.card`), the increasing enumeration of `S₀` as an element of
  `BlkIdx S₀ m`, together with the fact that it is increasing.
-/

namespace Work.DSM5b.HCF

open Work.DSM5b

universe u

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]

/-- The tuples of length `m+1` whose range is exactly `S₀` (the block of `S₀` in degree `m`). -/
abbrev BlkIdx (S₀ : Finset ι) (m : ℕ) : Type u := {τ : Fin (m + 1) → ι // tupRng τ = S₀}

/-- The range of a tuple depends on the tuple only up to a permutation of the positions. -/
lemma tupRng_comp_perm' {m : ℕ} (e : Equiv.Perm (Fin (m + 1))) (f : Fin (m + 1) → ι) :
    tupRng (f ∘ e) = tupRng f := by
  ext x
  simp only [tupRng, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩

/-- Swapping two adjacent entries (`i` and `i+1`) of a tuple with prescribed range. -/
noncomputable def swapBlk {m : ℕ} {S₀ : Finset ι} (σ : BlkIdx S₀ m) (i : Fin m) : BlkIdx S₀ m :=
  ⟨σ.1 ∘ Equiv.swap i.castSucc i.succ,
    (tupRng_comp_perm' (Equiv.swap i.castSucc i.succ) σ.1).trans σ.2⟩

@[simp] lemma swapBlk_val {m : ℕ} {S₀ : Finset ι} (σ : BlkIdx S₀ m) (i : Fin m) :
    (swapBlk σ i).1 = σ.1 ∘ Equiv.swap i.castSucc i.succ := rfl

/-- **The cast-free presentation of a block cochain.**  The value of a cochain `z` at a tuple `σ`
whose range is `S₀`, restricted into the fixed module `ℰ.M S₀`.  The restriction map is the one
given by the proof `σ.2` of `tupRng σ.1 = S₀`, so that no `Eq.rec` appears here. -/
noncomputable def blkVal (ℰ : CoeffSys R ι) (S₀ : Finset ι) (m : ℕ) (z : ℰ.Htc m)
    (σ : BlkIdx S₀ m) : ℰ.M S₀ :=
  ℰ.res (fun x hx => σ.2 ▸ hx) (z σ.1)

/-- `blkVal` is the restriction of `z` along any proof of the inclusion of the range into `S₀`. -/
lemma blkVal_eq_res {ℰ : CoeffSys R ι} {m : ℕ} {z : ℰ.Htc m} {S₀ : Finset ι}
    {τ : Fin (m + 1) → ι} (h : tupRng τ = S₀) (hτ : tupRng τ ⊆ S₀) :
    blkVal ℰ S₀ m z ⟨τ, h⟩ = ℰ.res hτ (z τ) :=
  CoeffSys.res_congr ℰ (z τ)

/-- On a block, restricting a cochain along a proof of the inclusion is the same as restricting it
along an *equality* of finsets (the two are cast-free `blkVal`s of the same element). -/
lemma blkVal_self (ℰ : CoeffSys R ι) {m : ℕ} (z : ℰ.Htc m) (τ : Fin (m + 1) → ι) :
    blkVal ℰ (tupRng τ) m z ⟨τ, rfl⟩ = z τ :=
  (blkVal_eq_res (ℰ := ℰ) (z := z) rfl (le_refl _)).trans (ℰ.res_self_apply (z τ))

/-- Restricting a cochain `z` at two *equal* tuples gives the same value (in a common module). -/
lemma res_apply_congr {ℰ : CoeffSys R ι} {m : ℕ} {z : ℰ.Htc m} {τ τ' : Fin (m + 1) → ι}
    (h : τ = τ') {T : Finset ι} (hτ : tupRng τ ⊆ T) (hτ' : tupRng τ' ⊆ T) :
    ℰ.res hτ (z τ) = ℰ.res hτ' (z τ') := by
  cases h
  exact CoeffSys.res_congr ℰ (z τ)

section Sorted

variable [LinearOrder ι]

/-- The increasing enumeration of `S₀` (`h : m + 1 = S₀.card`), as a tuple of length `m+1` whose
range is `S₀`. -/
noncomputable def incrBlk (S₀ : Finset ι) (m : ℕ) (h : m + 1 = S₀.card) : BlkIdx S₀ m :=
  ⟨fun i => ((S₀.orderIsoOfFin h.symm i : ↥S₀) : ι), by
    ext x
    simp only [tupRng, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (S₀.orderIsoOfFin h.symm i).2
    · intro hx
      refine ⟨(S₀.orderIsoOfFin h.symm).symm ⟨x, hx⟩, ?_⟩
      simp⟩

/-- The increasing enumeration of `S₀` is increasing. -/
lemma isIncr_incrBlk (S₀ : Finset ι) (m : ℕ) (h : m + 1 = S₀.card) :
    IsIncr (incrBlk S₀ m h).1 := by
  intro i j hij
  exact (S₀.orderIsoOfFin h.symm).strictMono hij

end Sorted

/-- The first `m` entries of the increasing enumeration of a finset: the underlying function is the
order isomorphism `S₀.orderIsoOfFin`. -/
@[simp] lemma incrBlk_apply (S₀ : Finset ι) [LinearOrder ι] (m : ℕ) (h : m + 1 = S₀.card)
    (i : Fin (m + 1)) :
    (incrBlk S₀ m h).1 i = ((S₀.orderIsoOfFin h.symm i : ↥S₀) : ι) := rfl

/-- **The coefficient module of `exactlyCoeff 𝒜 k` at a subset of size `≠ k` is a subsingleton**
(so the zero module): for `card S < k` both sub-systems vanish, and for `card S > k` the quotient is
`⊤ ⧸ ⊤`. -/
lemma exactlyCoeff_subsingleton_of_card_ne (𝒜 : CoeffSys R ι) (k : ℕ) {S : Finset ι}
    (h : S.card ≠ k) : Subsingleton ((CoeffSys.exactlyCoeff 𝒜 k).M S) := by
  by_cases hlt : S.card < k
  · haveI : Subsingleton ↥((CoeffSys.sizeSubSys 𝒜 k).N S) := by
      rw [show (CoeffSys.sizeSubSys 𝒜 k).N S = ⊥ from if_neg (by omega)]
      infer_instance
    exact Function.Surjective.subsingleton (Submodule.mkQ_surjective _)
  · have hNk1 : (CoeffSys.sizeSubSys 𝒜 (k + 1)).N S = ⊤ := if_pos (by omega)
    change Subsingleton (↥((CoeffSys.sizeSubSys 𝒜 k).N S) ⧸
      (Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 k S)).range)
    rw [Submodule.Quotient.subsingleton_iff]
    apply Submodule.eq_top_iff'.mpr
    intro y
    refine ⟨⟨y.1, by rw [hNk1]; exact Submodule.mem_top⟩, ?_⟩
    exact Subtype.ext rfl

end Work.DSM5b.HCF
