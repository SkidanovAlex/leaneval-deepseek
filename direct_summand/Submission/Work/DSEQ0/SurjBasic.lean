import Mathlib

/-!
# `Work.DSEQ0`: the surjection (Čech) complex and its acyclicity predicates

This file sets up the combinatorial cochain complexes needed for
`Work.DSEQ0.surjCech_vanishing`.

Fix a finite type `ι` and an additive comm group `M`.  For `k : ℕ` let

* `D k := (Fin (k+1) → ι) → M`            (all `M`-valued functions on `(k+1)`-tuples),
* `F m k := { f : D k // f g = 0 whenever imgCard g < m }`  (`inF m f` below),
* `C k := F (Fintype.card ι) k`  (functions vanishing on *non-surjective* tuples),

all with the **alternating coboundary**

`(cob k f) x = ∑ j : Fin (k+2), (-1 : ℤ) ^ (j : ℕ) • f (x ∘ Fin.succAbove j)`.

The main theorem is: for `n ≥ Fintype.card ι`, every cocycle in `C n` is a coboundary
in `C (n-1)`.  It is proved by strong induction on `Fintype.card ι`, using the
*image-size filtration* `F 0 ⊇ F 1 ⊇ … ⊇ F (card ι) = C ⊇ F (card ι + 1) = 0` of `D`
(whose graded pieces are sums of the same complexes on proper subsets) together with
the acyclicity of `D` above degree `1`.

## Predicates used to organise the induction

* `DAcyclic m₀`  : the full complex `D` is acyclic above degree `m₀`.
* `FAcyclic m m₀`: `F m` is acyclic above degree `m₀`.
* `GrAcyclic m m₀`: the graded piece `F m / F (m+1)` is acyclic above degree `m₀`
  (stated with representatives, avoiding quotients).
-/

open Classical Finset

namespace Work.DSEQ0

universe u

variable {ι : Type u} [Fintype ι] {M : Type u} [AddCommGroup M]

/-- The image of a tuple, as a `Finset`. -/
noncomputable def imgFinset {k : ℕ} (g : Fin (k + 1) → ι) : Finset ι :=
  Finset.univ.image g

/-- The number of distinct values taken by a tuple. -/
noncomputable def imgCard {k : ℕ} (g : Fin (k + 1) → ι) : ℕ := (imgFinset g).card

/-- The alternating coboundary. -/
noncomputable def cob (k : ℕ) (f : (Fin (k + 1) → ι) → M) : (Fin (k + 2) → ι) → M :=
  fun x => ∑ j : Fin (k + 2), (-1 : ℤ) ^ (j : ℕ) • f (x ∘ Fin.succAbove j)

/-- `f` vanishes on all tuples whose image has fewer than `m` elements. -/
def inF (m : ℕ) {k : ℕ} (f : (Fin (k + 1) → ι) → M) : Prop :=
  ∀ g, imgCard g < m → f g = 0

@[simp] theorem imgFinset_def {k : ℕ} (g : Fin (k + 1) → ι) :
    imgFinset g = Finset.univ.image g := rfl

theorem imgCard_le {k : ℕ} (g : Fin (k + 1) → ι) : imgCard g ≤ Fintype.card ι := by
  rw [imgCard]; exact Finset.card_le_univ _

theorem image_eq_univ_iff {k : ℕ} (g : Fin (k + 1) → ι) :
    (Finset.univ.image g : Finset ι) = Finset.univ ↔ Function.Surjective g := by
  constructor
  · intro h x
    have hx : x ∈ (Finset.univ.image g : Finset ι) := by rw [h]; exact Finset.mem_univ x
    simpa using hx
  · intro h
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => h x⟩

theorem surjective_iff_imgCard_eq {k : ℕ} (g : Fin (k + 1) → ι) :
    Function.Surjective g ↔ imgCard g = Fintype.card ι := by
  rw [imgCard, imgFinset]
  constructor
  · intro h; rw [(image_eq_univ_iff g).mpr h, Finset.card_univ]
  · intro h
    rw [← image_eq_univ_iff]
    exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ]; exact le_of_eq h.symm)

/-- The image of a composite is contained in the image of the outer map. -/
theorem imgCard_comp_le {k j : ℕ} (g : Fin (k + 1) → ι) (e : Fin (j + 1) → Fin (k + 1)) :
    imgCard (g ∘ e) ≤ imgCard g := by
  rw [imgCard, imgCard, imgFinset, imgFinset]
  apply Finset.card_le_card
  intro x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨a, rfl⟩
  exact ⟨e a, rfl⟩

theorem inF_anti {m m' : ℕ} (h : m' ≤ m) {k : ℕ} {f : (Fin (k + 1) → ι) → M}
    (hf : inF m f) : inF m' f := fun g hg => hf g (lt_of_lt_of_le hg h)

theorem inF_zero {k : ℕ} (f : (Fin (k + 1) → ι) → M) : inF 0 f :=
  fun g hg => absurd hg (Nat.not_lt_zero _)

/-- A tuple with nonempty domain has image of positive cardinality. -/
theorem one_le_imgCard {k : ℕ} (hk : 0 < k + 1) (g : Fin (k + 1) → ι) : 1 ≤ imgCard g := by
  rw [imgCard, imgFinset, Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
  exact ⟨g ⟨0, hk⟩, Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩

theorem inF_of_card {k : ℕ} (f : (Fin (k + 1) → ι) → M)
    (h : ∀ g, ¬ Function.Surjective g → f g = 0) : inF (Fintype.card ι) f := by
  intro g hg
  exact h g (fun hs => absurd (surjective_iff_imgCard_eq g |>.mp hs) (by omega))

theorem inF_card_of {k : ℕ} (f : (Fin (k + 1) → ι) → M)
    (h : inF (Fintype.card ι) f) : ∀ g, ¬ Function.Surjective g → f g = 0 := by
  intro g hg
  exact h g (lt_of_le_of_ne (imgCard_le g) (fun he => hg ((surjective_iff_imgCard_eq g).mpr he)))

/-- `cob` is additive. -/
theorem cob_add (k : ℕ) (f g : (Fin (k + 1) → ι) → M) :
    cob k (f + g) = cob k f + cob k g := by
  funext x
  simp only [Pi.add_apply, cob, smul_add, Finset.sum_add_distrib]

theorem cob_neg (k : ℕ) (f : (Fin (k + 1) → ι) → M) : cob k (-f) = -cob k f := by
  funext x
  simp only [Pi.neg_apply, cob, smul_neg, Finset.sum_neg_distrib]

theorem cob_sub (k : ℕ) (f g : (Fin (k + 1) → ι) → M) :
    cob k (f - g) = cob k f - cob k g := by
  ext x
  simp only [Pi.sub_apply, cob, smul_sub, Finset.sum_sub_distrib]

theorem cob_smul (k : ℕ) (c : ℤ) (f : (Fin (k + 1) → ι) → M) :
    cob k (c • f) = c • cob k f := by
  funext x
  simp only [Pi.smul_apply, cob]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_comm]

/-- The coboundary preserves the subcomplexes `F m`. -/
theorem cob_inF {m k : ℕ} {f : (Fin (k + 1) → ι) → M} (hf : inF m f) :
    inF m (cob k f) := by
  intro x hx
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [hf _ (lt_of_le_of_lt (imgCard_comp_le x (Fin.succAbove j)) hx), smul_zero]

/-- The full complex `D` is acyclic above degree `m₀`.  (`k+1` is the degree of the cocycle.) -/
def DAcyclic (m₀ : ℕ) : Prop :=
  ∀ k : ℕ, m₀ ≤ k + 1 → ∀ f : (Fin (k + 2) → ι) → M, cob (k + 1) f = 0 →
    ∃ h : (Fin (k + 1) → ι) → M, cob k h = f

/-- The subcomplex `F m` is acyclic above degree `m₀`. -/
def FAcyclic (m m₀ : ℕ) : Prop :=
  ∀ k : ℕ, m₀ ≤ k + 1 → ∀ f : (Fin (k + 2) → ι) → M, inF m f → cob (k + 1) f = 0 →
    ∃ h : (Fin (k + 1) → ι) → M, inF m h ∧ cob k h = f

/-- The graded piece `F m / F (m+1)` is acyclic above degree `m₀`.
Stated with representatives: a representative `f ∈ F m` whose residue is a cocycle
(`cob (k+1) f ∈ F (m+1)`) becomes a coboundary modulo `F (m+1)`. -/
def GrAcyclic (m m₀ : ℕ) : Prop :=
  ∀ k : ℕ, m₀ ≤ k + 1 → ∀ f : (Fin (k + 2) → ι) → M, inF m f → inF (m + 1) (cob (k + 1) f) →
    ∃ h : (Fin (k + 1) → ι) → M, inF m h ∧
      inF (m + 1) (fun x => cob k h x - f x)

end Work.DSEQ0
