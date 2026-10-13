import Mathlib
import Submission.Work.DSM5b.HCF.GenSurj
import Submission.Work.DSM5b.HCF.Sorted

/-!
# Signs on the surjection complex over an arbitrary finset

`Submission/Work/DSM5b/HCF/SurjSign.lean` defines the sign of a tuple of the surjection complex
attached to a finset `S₀ : Finset (Fin n)`.  For the coefficient system
`Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k` — supported on the subsets of size exactly `k` — the
relevant finsets are arbitrary subsets `S₀ : Finset ι` of an arbitrary linearly ordered index type,
and the sign has to be available there as well.

This file provides, for `S₀ : Finset ι` and `τ : GSurjIdx S₀ q` (a tuple of length `q+1` with
`tupRng τ = S₀`, where `♯S₀ = q+1`):

* `gRefEquiv S₀ q hq` — the reference enumeration of `S₀` (the increasing one);
* `gPosEquiv τ hq` — the corestriction of `τ` to `S₀` (a bijection);
* `gPermOf τ hq` — the sorting permutation of `τ` (comparing the two);
* `gSignOf τ hq`, `gSignOfR τ hq` — its sign, in `ℤˣ` resp. in `R`;
* `gIncr S₀ q hq` / `gIncrTup S₀ q hq` — the increasing enumeration of `S₀`, as an element of the
  surjection complex resp. as an increasing tuple;
* the elementary facts: `gPosEquiv_apply`, `gPermOf_eq_one_of_isIncr` (the sign of an *increasing*
  tuple is `1`, hence `gSignOfR_self` and `gSignOfR_gIncr`), and `gIncrTup_ext` (an increasing
  tuple is determined by its range).
-/

namespace Work.DSM5b.HCF

universe u

open Classical Finset

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]

/-- Every entry of a tuple whose range is `S₀` lies in `S₀`. -/
lemma gMem {S₀ : Finset ι} {q : ℕ} (τ : GSurjIdx S₀ q) (i : Fin (q+1)) : τ.1 i ∈ S₀ :=
  Finset.mem_of_subset (le_of_eq τ.2) (by
    rw [Work.DSM5b.tupRng]
    exact Finset.mem_image_of_mem τ.1 (Finset.mem_univ i))

/-- The reference enumeration of `S₀` (`hq : q+1 = ♯S₀`): the increasing one. -/
noncomputable def gRefEquiv (S₀ : Finset ι) (q : ℕ) (hq : q + 1 = S₀.card) : Fin (q + 1) ≃ ↥S₀ :=
  Equiv.ofBijective
    (fun i => (⟨(S₀.orderEmbOfFin hq.symm i : ι), Finset.orderEmbOfFin_mem S₀ hq.symm i⟩ : ↥S₀))
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨by
      intro y
      have hy : (y : ι) ∈ Set.range ⇑(S₀.orderEmbOfFin hq.symm) := by
        rw [Finset.range_orderEmbOfFin]
        exact y.2
      obtain ⟨i, hi⟩ := hy
      exact ⟨i, Subtype.ext hi⟩, by simp [Fintype.card_coe, hq]⟩)

@[simp] theorem gRefEquiv_apply (S₀ : Finset ι) (q : ℕ) (hq : q + 1 = S₀.card)
    (i : Fin (q+1)) : ((gRefEquiv S₀ q hq i : ↥S₀) : ι) = (S₀.orderEmbOfFin hq.symm) i := by
  rw [gRefEquiv, Equiv.ofBijective_apply]

/-- The corestriction of a tuple with range `S₀` to `S₀` (a bijection when `♯S₀ = q+1`). -/
noncomputable def gPosEquiv {S₀ : Finset ι} {q : ℕ} (τ : GSurjIdx S₀ q) (hq : q + 1 = S₀.card) :
    Fin (q + 1) ≃ ↥S₀ :=
  Equiv.ofBijective (fun i => (⟨τ.1 i, gMem τ i⟩ : ↥S₀))
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨by
      intro y
      have hy : y.1 ∈ Work.DSM5b.tupRng τ.1 := by rw [τ.2]; exact y.2
      rw [Work.DSM5b.tupRng, Finset.mem_image] at hy
      obtain ⟨i, -, hi⟩ := hy
      exact ⟨i, Subtype.ext hi⟩, by simp [Fintype.card_coe, hq]⟩)

@[simp] theorem gPosEquiv_apply {S₀ : Finset ι} {q : ℕ} (τ : GSurjIdx S₀ q)
    (hq : q + 1 = S₀.card) (i : Fin (q+1)) : ((gPosEquiv τ hq i : ↥S₀) : ι) = τ.1 i := by
  rw [gPosEquiv, Equiv.ofBijective_apply]

/-- The permutation sorting the entries of a tuple of the surjection complex. -/
noncomputable def gPermOf {S₀ : Finset ι} {q : ℕ} (τ : GSurjIdx S₀ q) (hq : q + 1 = S₀.card) :
    Equiv.Perm (Fin (q + 1)) :=
  (gPosEquiv τ hq).trans (gRefEquiv S₀ q hq).symm

/-- The sign of a tuple of the surjection complex. -/
noncomputable def gSignOf {S₀ : Finset ι} {q : ℕ} (τ : GSurjIdx S₀ q) (hq : q + 1 = S₀.card) :
    ℤˣ :=
  Equiv.Perm.sign (gPermOf τ hq)

/-- The sign of a tuple of the surjection complex, as an element of `R`. -/
noncomputable def gSignOfR {S₀ : Finset ι} {q : ℕ} (τ : GSurjIdx S₀ q) (hq : q + 1 = S₀.card) :
    R :=
  ((gSignOf τ hq : ℤˣ) : ℤ)

/-- The increasing enumeration of `S₀` (`hq : q+1 = ♯S₀`), as an element of the surjection
complex. -/
noncomputable def gIncr (S₀ : Finset ι) (q : ℕ) (hq : q + 1 = S₀.card) : GSurjIdx S₀ q :=
  ⟨fun i => ((gRefEquiv S₀ q hq i : ↥S₀) : ι), by
    ext x
    simp only [Work.DSM5b.tupRng, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (gRefEquiv S₀ q hq i).2
    · intro hx
      refine ⟨(gRefEquiv S₀ q hq).symm ⟨x, hx⟩, ?_⟩
      simp⟩

lemma gIncr_val (S₀ : Finset ι) (q : ℕ) (hq : q + 1 = S₀.card) :
    (gIncr S₀ q hq).1 = fun i => ((gRefEquiv S₀ q hq i : ↥S₀) : ι) := rfl

/-- The increasing enumeration of `S₀`, as an increasing tuple. -/
noncomputable def gIncrTup (S₀ : Finset ι) (q : ℕ) (hq : q + 1 = S₀.card) :
    IncrTuple (ι := ι) q :=
  ⟨(gIncr S₀ q hq).1, fun i j hij => by
    simp only [gIncr_val, gRefEquiv_apply]
    exact (S₀.orderEmbOfFin hq.symm).strictMono hij⟩

@[simp] lemma gIncrTup_val (S₀ : Finset ι) (q : ℕ) (hq : q + 1 = S₀.card) :
    (gIncrTup S₀ q hq).1 = (gIncr S₀ q hq).1 := rfl

@[simp] lemma tupRng_gIncrTup (S₀ : Finset ι) (q : ℕ) (hq : q + 1 = S₀.card) :
    Work.DSM5b.tupRng (gIncrTup S₀ q hq).1 = S₀ := (gIncr S₀ q hq).2

lemma card_tupRng_gIncrTup (S₀ : Finset ι) (q : ℕ) (hq : q + 1 = S₀.card) :
    (Work.DSM5b.tupRng (gIncrTup S₀ q hq).1).card = q + 1 := by
  rw [tupRng_gIncrTup, hq]

/-- **The sorting permutation of an increasing tuple is `1`.**

The corestriction `gPosEquiv τ hq` and the reference enumeration `gRefEquiv S₀ q hq` are two
strictly increasing enumerations of the same finset `S₀`, hence equal
(`Finset.orderEmbOfFin_unique`). -/
theorem gPermOf_eq_one_of_isIncr {S₀ : Finset ι} {q : ℕ} (hq : q + 1 = S₀.card)
    (τ : GSurjIdx S₀ q) (hτ : IsIncr τ.1) : gPermOf τ hq = 1 := by
  rw [gPermOf]
  have hpos : gPosEquiv τ hq = gRefEquiv S₀ q hq := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rw [gPosEquiv_apply, gRefEquiv_apply]
    exact congrFun (Finset.orderEmbOfFin_unique hq.symm
      (fun j => gMem τ j) (fun a b hab => hτ a b hab)) i
  rw [hpos, Equiv.self_trans_symm]
  rfl

@[simp] theorem gSignOf_self {S₀ : Finset ι} {q : ℕ} (hq : q + 1 = S₀.card)
    (τ : GSurjIdx S₀ q) (hτ : IsIncr τ.1) : gSignOf τ hq = 1 := by
  rw [gSignOf, gPermOf_eq_one_of_isIncr hq τ hτ, Equiv.Perm.sign_one]

@[simp] theorem gSignOfR_self {S₀ : Finset ι} {q : ℕ} (hq : q + 1 = S₀.card)
    (τ : GSurjIdx S₀ q) (hτ : IsIncr τ.1) : gSignOfR (R := R) τ hq = 1 := by
  rw [gSignOfR, gSignOf_self hq τ hτ]
  simp

@[simp] theorem gSignOfR_gIncr (S₀ : Finset ι) (q : ℕ) (hq : q + 1 = S₀.card) :
    gSignOfR (R := R) (gIncr S₀ q hq) hq = 1 :=
  gSignOfR_self hq _ (fun i j hij => by
    simp only [gIncr_val, gRefEquiv_apply]
    exact (S₀.orderEmbOfFin hq.symm).strictMono hij)

/-- The range of an increasing tuple of length `q+1` has cardinality `q+1`. -/
theorem card_tupRng_of_isIncr {q : ℕ} (τ : IncrTuple (ι := ι) q) :
    (Work.DSM5b.tupRng τ.1).card = q + 1 := by
  rw [Work.DSM5b.tupRng]
  have hinj : Function.Injective τ.1 :=
    (show StrictMono τ.1 from fun a b hab => τ.2 a b hab).injective
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **An increasing tuple is determined by its range.** -/
theorem gIncrTup_ext {q : ℕ} {τ τ' : IncrTuple (ι := ι) q}
    (h : Work.DSM5b.tupRng τ.1 = Work.DSM5b.tupRng τ'.1) : τ = τ' := by
  have hc : (Work.DSM5b.tupRng τ'.1).card = q + 1 := card_tupRng_of_isIncr τ'
  have h₁ : τ.1 = ⇑((Work.DSM5b.tupRng τ'.1).orderEmbOfFin hc) :=
    Finset.orderEmbOfFin_unique hc
      (fun j => by rw [← h]; exact Finset.mem_image_of_mem τ.1 (Finset.mem_univ j))
      (fun a b hab => τ.2 a b hab)
  have h₂ : τ'.1 = ⇑((Work.DSM5b.tupRng τ'.1).orderEmbOfFin hc) :=
    Finset.orderEmbOfFin_unique hc
      (fun j => Finset.mem_image_of_mem τ'.1 (Finset.mem_univ j))
      (fun a b hab => τ'.2 a b hab)
  exact Subtype.ext (h₁.trans h₂.symm)

/-- The increasing enumeration of a finset is the only increasing tuple with that range. -/
theorem gIncrTup_eq_of_range_eq {S₀ : Finset ι} {q : ℕ} (hq : q + 1 = S₀.card)
    (τ : IncrTuple (ι := ι) q) (h : Work.DSM5b.tupRng τ.1 = S₀) : τ = gIncrTup S₀ q hq :=
  gIncrTup_ext (by rw [h, tupRng_gIncrTup])

end Work.DSM5b.HCF
