import Mathlib
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.HCd_comp
import Submission.Work.DSEQ0.surj_tuple_vanishing

/-!
# DSM5b — vocabulary for the vanishing of the honest chart Čech cohomology

`HCX t m = ∀ τ : Fin (m+1) → ι, chartRing t (tupRng τ)` and `HCd t m` are the coordinates of the
honest chart Čech complex (`Submission/Work/DSM5b/H0Defs.lean`): the unnormalized (tuples with
repetitions) Čech complex of the chart cover `{D₊(t_i)}` of `Bl_J (Spec R)`, `J = (t_i)`.

The vanishing above the number of charts is proved by the *image-size filtration*:
for `j : ℕ` let `F j` be the subcomplex of families supported on tuples whose range has at least
`j` elements.  Deleting a coordinate never increases the range, so `F j` is indeed a subcomplex,
and `F 0 = F 1 = HCX`.  The graded piece `F j / F (j+1)` splits as the sum, over the `j`-element
subsets `S ⊆ ι`, of the *surjection complex* of `S`, which has **constant** coefficients
`chartRing t S`; that complex's vanishing (a purely combinatorial statement, proved in the
workspace as `Work.DSEQ0.surj_tuple_vanishing`) gives the block solutions, and the descending
induction of `Work.DSM5b.cocycle_is_coboundary` replaces the long exact sequences of the
filtration.

This file contains the vocabulary of that argument:

* `toI S x` — a tuple of elements of `S ⊆ ι`, regarded as a tuple of elements of `ι`;
* `corestr S σ h` — conversely, a tuple `σ` with `tupRng σ = S` regarded as a tuple of `S`;
* `SuppAbove j z` — the support condition `z τ = 0` whenever `tupRng τ` has fewer than `j` elements.
-/

namespace Work.DSM5b

open DSMap DSMap.Mix DSMap.Mix2

universe a

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Defs

variable {ι : Type a} [DecidableEq ι] {R : Type a} [CommRing R]

/-- A tuple of elements of a finset `S ⊆ ι`, regarded as a tuple of elements of `ι`. -/
def toI (S : Finset ι) {m : ℕ} (x : Fin (m + 1) → ↥S) : Fin (m + 1) → ι := fun i => (x i : ι)

/-- The canonical reindexing of a tuple `σ : Fin (m+1) → ι` whose range is `S`: the same tuple,
regarded as a tuple of elements of `S`. -/
def corestr (S : Finset ι) {m : ℕ} (σ : Fin (m + 1) → ι) (h : tupRng σ = S) : Fin (m + 1) → ↥S :=
  fun i => ⟨σ i, h ▸ Finset.mem_image_of_mem σ (Finset.mem_univ i)⟩

@[simp] lemma toI_corestr (S : Finset ι) {m : ℕ} (σ : Fin (m + 1) → ι) (h : tupRng σ = S) :
    toI S (corestr S σ h) = σ := rfl

lemma toI_injective (S : Finset ι) {m : ℕ} : Function.Injective (toI (ι := ι) S (m := m)) :=
  fun x y h => funext fun i => Subtype.ext (congrFun h i)

lemma tupRng_toI_subset (S : Finset ι) {m : ℕ} (x : Fin (m + 1) → ↥S) : tupRng (toI S x) ⊆ S := by
  intro y hy
  simp only [tupRng, toI, Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  exact (x i).2

lemma tupRng_toI_eq_image (S : Finset ι) {m : ℕ} (x : Fin (m + 1) → ↥S) :
    tupRng (toI S x) = (Finset.univ.image x).image Subtype.val := by
  rw [tupRng, Finset.image_image]
  rfl

lemma card_tupRng_toI (S : Finset ι) {m : ℕ} (x : Fin (m + 1) → ↥S) :
    (tupRng (toI S x)).card = (Finset.univ.image x).card := by
  rw [tupRng_toI_eq_image, Finset.card_image_of_injective _ Subtype.val_injective]

lemma image_val_univ (S : Finset ι) :
    (Finset.univ.image (Subtype.val : ↥S → ι)) = S := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

lemma surjective_iff_image_univ (S : Finset ι) {m : ℕ} (x : Fin (m + 1) → ↥S) :
    Function.Surjective x ↔ Finset.univ.image x = Finset.univ := by
  constructor
  · intro h
    ext b
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => h b⟩
  · intro h b
    have hb : b ∈ (Finset.univ.image x : Finset ↥S) := by rw [h]; exact Finset.mem_univ b
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hb

lemma tupRng_toI_eq_iff (S : Finset ι) {m : ℕ} (x : Fin (m + 1) → ↥S) :
    tupRng (toI S x) = S ↔ Function.Surjective x := by
  constructor
  · intro h
    rw [surjective_iff_image_univ]
    have h1 : (Finset.univ.image x).card = S.card := by
      rw [← card_tupRng_toI S x, h]
    have h2 : (Finset.univ.image x).card = (Finset.univ : Finset ↥S).card := by
      rw [Finset.card_univ, Fintype.card_coe, h1]
    exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (le_of_eq h2.symm)
  · intro h
    rw [tupRng_toI_eq_image, (surjective_iff_image_univ S x).mp h, image_val_univ]

lemma tupRng_toI_of_surjective (S : Finset ι) {m : ℕ} {x : Fin (m + 1) → ↥S}
    (h : Function.Surjective x) : tupRng (toI S x) = S :=
  (tupRng_toI_eq_iff S x).mpr h

lemma card_tupRng_toI_lt_of_not_surjective (S : Finset ι) {m : ℕ} {x : Fin (m + 1) → ↥S}
    (h : ¬ Function.Surjective x) : (tupRng (toI S x)).card < S.card := by
  rw [card_tupRng_toI]
  have h1 : (Finset.univ.image x).card ≤ (Finset.univ : Finset ↥S).card :=
    Finset.card_le_univ _
  rw [Finset.card_univ, Fintype.card_coe] at h1
  refine lt_of_le_of_ne h1 ?_
  intro h2
  refine h ((surjective_iff_image_univ S x).mpr ?_)
  refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
  rw [Finset.card_univ, Fintype.card_coe, h2]

lemma corestr_surjective (S : Finset ι) {m : ℕ} (σ : Fin (m + 1) → ι) (h : tupRng σ = S) :
    Function.Surjective (corestr S σ h) := by
  intro b
  have hb : (b : ι) ∈ tupRng σ := by rw [h]; exact b.2
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hb
  exact ⟨i, Subtype.ext hi⟩

lemma tupRng_toI_corestr (S : Finset ι) {m : ℕ} (σ : Fin (m + 1) → ι) (h : tupRng σ = S) :
    tupRng (toI S (corestr S σ h)) = S := by
  rw [toI_corestr]; exact h

/-- The support condition of the image-size filtration: `z` vanishes on tuples whose range has
fewer than `j` elements. -/
def SuppAbove {ι : Type a} [DecidableEq ι] {R : Type a} [CommRing R] {t : ι → R} (j : ℕ)
    {m : ℕ} (z : HCX t m) : Prop :=
  ∀ τ : Fin (m + 1) → ι, (tupRng τ).card < j → z τ = 0

/-- `rhoH` along a proof of `S ⊆ S` is the identity (`locRes` is an algebra map, and the
localisation map along an inclusion of equal sets is the identity). -/
lemma rhoH_self (t : ι → R) {S : Finset ι} (h : S ⊆ S) (x : chartRing t S) : rhoH t h x = x := by
  apply Subtype.ext
  rw [rhoH_coe]
  have h1 : locRes t h = AlgHom.id R (Localization.Away (tS t S)) :=
    (locRes_eq t h (AlgHom.id R _)).symm
  rw [h1]
  rfl

/-- The canonical `R`-linear identification of the chart rings of two equal finsets, realised by
`rhoH` (rather than by `Eq.rec`). -/
noncomputable def liftAlong (t : ι → R) {S T : Finset ι} (h : S = T) :
    chartRing t S ≃ₗ[R] chartRing t T where
  toFun x := rhoH t (le_of_eq h) x
  map_add' x y := map_add _ x y
  map_smul' r x := map_smul _ r x
  invFun y := rhoH t (le_of_eq h.symm) y
  left_inv x := by
    show rhoH t (le_of_eq h.symm) (rhoH t (le_of_eq h) x) = x
    rw [HCd_rhoH_comp]
    rw [show rhoH t ((le_of_eq h).trans (le_of_eq h.symm)) x = rhoH t (le_rfl : S ⊆ S) x from
      HCd_rhoH_congr x]
    exact rhoH_self t _ x
  right_inv y := by
    show rhoH t (le_of_eq h) (rhoH t (le_of_eq h.symm) y) = y
    rw [HCd_rhoH_comp]
    rw [show rhoH t ((le_of_eq h.symm).trans (le_of_eq h)) y = rhoH t (le_rfl : T ⊆ T) y from
      HCd_rhoH_congr y]
    exact rhoH_self t _ y

@[simp] lemma liftAlong_apply (t : ι → R) {S T : Finset ι} (h : S = T) (x : chartRing t S) :
    liftAlong t h x = rhoH t (le_of_eq h) x := rfl

lemma suppAbove_zero_eq {t : ι → R} {m : ℕ} {z : HCX t m} : SuppAbove 0 z :=
  fun τ hτ => absurd hτ (by omega)

lemma suppAbove_of_le {t : ι → R} {m j j' : ℕ} {z : HCX t m} (h : j ≤ j')
    (hz : SuppAbove j' z) : SuppAbove j z :=
  fun τ hτ => hz τ (lt_of_lt_of_le hτ h)

/-- A tuple cannot take more values than there are elements of `ι`. -/
lemma card_tupRng_le {ι : Type a} [Fintype ι] [DecidableEq ι] {m : ℕ} (τ : Fin (m + 1) → ι) :
    (tupRng τ).card ≤ Nat.card ι := by
  rw [tupRng]
  calc (Finset.univ.image τ).card ≤ Fintype.card ι := Finset.card_le_univ _
    _ = Nat.card ι := Nat.card_eq_fintype_card.symm

/-- The `ℤ`-scalar `(-1)^n` and the `R`-scalar `(-1)^n` agree on an `R`-module. -/
lemma negOne_zsmul_eq (R : Type*) [Ring R] {M : Type*} [AddCommGroup M] [Module R M] (n : ℕ)
    (x : M) : ((-1 : ℤ) ^ n) • x = ((-1 : R) ^ n) • x := by
  rw [← Int.cast_smul_eq_zsmul (R := R), Int.cast_pow, Int.cast_neg, Int.cast_one]

end Defs

end Work.DSM5b
