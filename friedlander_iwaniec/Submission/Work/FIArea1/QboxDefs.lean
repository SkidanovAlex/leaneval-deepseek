/-
# `Submission.Work.FIArea1.QboxDefs` — the boxes of the prime substitution of *FI* (5.22)

This module only contains **definitions** (and elementary membership calculus), so that the
delegated inequalities about them can be stated without importing the main file.

The per-range bound of *FI* (5.22) (proved in `Submission/Work/FIArea1/offdiag_pi_range_le.lean`)
substitutes `z = π y` in the inner variable of the off-diagonal count, where `π` is a Gaussian
prime of norm in the dyadic range `(q, 2q]` and `z` runs over `Zbox N` (`N < |z|² ≤ 2N`).  Since
`|z|² > N` and `|π|² ≤ 2q` on the one hand, and `|z|² ≤ 2N`, `|π|² > q` on the other, the
substituted variable `y` satisfies

  `N/(2q) = X/2 < |y|² ≤ 2N/q = 2X`,   where `X := N/q`.

Because `|y| ≤ √(2X) ≤ ⌈√(2X)⌉ = KZ X`, the whole range of `y` is contained in the single
**ball** `Qbig X := {y : |y|² ≤ 2X}`, i.e. the points of `gBox (KZ X)` with `gnorm ≤ 2X`.  (The
ball is used — rather than an annulus — because it is *monotone* in `X`, which lets the main proof
replace `X` by `max X 2` when `X` is small; see `Qbig_mono`.)

`Qbig X` splits into the points with `Im y ≠ 0` (`Qbim X`) and the real points (`Qbre X`).  The
counts needed for the two pieces are delegated:

* `Work.FIArea1.offdiag_count_Qbim` (`Qbim`): the off-diagonal count of *FI* Lemma 5.1 adapted to
  the ball, `≪ |R| X^{3/2} (log)^{514}`;
* `Work.FIArea1.offdiag_count_Qbre_cross` (`Qbre × Qbim`): a crude lattice count (no logarithm),
  `≪ |R| X^{3/2}`.
-/
import Mathlib
import Submission.Work.FIArea1.L51Defs
import Submission.Work.FIArea1.Basic

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The ball of substituted inner points at scale `X`**: the *nonzero* Gaussian integers of
`gBox (KZ X)` with `|z|² ≤ 2X`.  (The `gBox` condition is actually implied by the norm bound, see
`mem_gBox_KZ_of_gnorm_le`; the point `0` is removed because a substituted point `y = z/π` is
never `0`, and because the degenerate pairs `(0, y)` would otherwise break the crude count of
`Work.FIArea1.offdiag_count_Qbre_cross`.) -/
def Qbig (X : ℝ) : Finset GaussianInt :=
  ((Work.FIPlan.gBox (KZ X)).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ 2 * X)).erase 0

/-- The non-real part of `Qbig X`. -/
def Qbim (X : ℝ) : Finset GaussianInt := (Qbig X).filter (fun z => z.im ≠ 0)

/-- The real part of `Qbig X`. -/
def Qbre (X : ℝ) : Finset GaussianInt := (Qbig X).filter (fun z => z.im = 0)

/-- **The substituted inner points at scale `X`**: the non-real points of the ball `Qbig X`,
together with the two real units `±1`.

A substituted point `y = z/π` (with `z ∈ Zbox N` *primitive* and `π ∣ z`) is in the ball `Qbig X`
(`X = N/q`) by `gnorm_zQuot_le`; if in addition `y` is real then `y` must be a unit
(`zQuot_mem_Yset`), which is why only `±1` — and not all real points of the ball — occur.  The
cross terms with the real part are then handled by the crude count
`Work.FIArea1.offdiag_count_Qre_cross`. -/
def Yset (X : ℝ) : Finset GaussianInt := Qbim X ∪ ({1, -1} : Finset GaussianInt)

lemma mem_Yset_iff {X : ℝ} {z : GaussianInt} :
    z ∈ Yset X ↔ z ∈ Qbim X ∨ z = 1 ∨ z = -1 := by
  simp only [Yset, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

lemma one_mem_Yset (X : ℝ) : (1 : GaussianInt) ∈ Yset X := mem_Yset_iff.mpr (Or.inr (Or.inl rfl))

lemma neg_one_mem_Yset (X : ℝ) : (-1 : GaussianInt) ∈ Yset X :=
  mem_Yset_iff.mpr (Or.inr (Or.inr rfl))

/-- **The Gaussian primes of the dyadic range `(q, 2q]`** inside the box `gBox (KZ N)`: the outer
sum of the prime substitution of *FI* (5.22). -/
def PiSet (q N : ℝ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (KZ N)).filter (fun π =>
    Prime π ∧ q < (Work.FIPlan.gnorm π : ℝ) ∧ (Work.FIPlan.gnorm π : ℝ) ≤ 2 * q)

/-- The Gaussian primes of `PiSet q N` that divide a fixed Gaussian integer `W` (materialised as a
definition, so that the delegated statements about it do not need a `Decidable` instance for
divisibility). -/
def PiDvd (q N : ℝ) (W : GaussianInt) : Finset GaussianInt :=
  (Work.FIPlan.gBox (KZ N)).filter (fun π =>
    Prime π ∧ q < (Work.FIPlan.gnorm π : ℝ) ∧ (Work.FIPlan.gnorm π : ℝ) ≤ 2 * q ∧ π ∣ W)

/-! ## Membership calculus -/

/-- **The norm bound implies the box membership.**  If `|z|² ≤ 2X` then `|Re z|, |Im z| ≤ √(2X)`,
and `KZ X = ⌈√(2X)⌉`. -/
lemma mem_gBox_KZ_of_gnorm_le {X : ℝ} {z : GaussianInt} (h : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * X) :
    z ∈ Work.FIPlan.gBox (KZ X) := by
  rw [Work.FIArea2.mem_gBox_iff, Finset.mem_Icc, Finset.mem_Icc]
  have hz : ((Work.FIPlan.gnorm z : ℕ) : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
    rw [Work.FIPlan.gnorm, Zsqrtd.norm_def]
    rw [show (((z.re * z.re - -1 * z.im * z.im).natAbs : ℕ) : ℝ)
          = |((z.re * z.re - -1 * z.im * z.im : ℤ) : ℝ)| from by
      rw [← Int.cast_abs, Nat.cast_natAbs]]
    rw [abs_of_nonneg (by ring_nf; positivity)]
    push_cast
    ring
  have hceil : Real.sqrt (2 * X) ≤ ((KZ X : ℤ) : ℝ) := by
    rw [KZ]; exact_mod_cast Nat.le_ceil _
  have key : ∀ {a : ℤ}, (a : ℝ) ^ 2 ≤ 2 * X → -(KZ X) ≤ a ∧ a ≤ KZ X := by
    intro a ha
    have h1 : |(a : ℝ)| ≤ Real.sqrt (2 * X) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt ha
    have h2 : |(a : ℝ)| ≤ ((KZ X : ℤ) : ℝ) := le_trans h1 hceil
    have h3 : |a| ≤ KZ X := by
      have h4 : ((|a| : ℤ) : ℝ) ≤ ((KZ X : ℤ) : ℝ) := by rwa [Int.cast_abs]
      exact_mod_cast h4
    exact abs_le.mp h3
  refine ⟨key ?_, key ?_⟩
  · have : (0 : ℝ) ≤ (z.im : ℝ) ^ 2 := sq_nonneg _
    linarith [hz ▸ h]
  · have : (0 : ℝ) ≤ (z.re : ℝ) ^ 2 := sq_nonneg _
    linarith [hz ▸ h]

/-- Membership in the ball `Qbig X` is just "nonzero and `|z|² ≤ 2X`". -/
lemma mem_Qbig_iff {X : ℝ} {z : GaussianInt} :
    z ∈ Qbig X ↔ z ≠ 0 ∧ (Work.FIPlan.gnorm z : ℝ) ≤ 2 * X := by
  rw [Qbig, Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro ⟨h0, -, h2⟩; exact ⟨h0, h2⟩
  · rintro ⟨h0, h2⟩; exact ⟨h0, mem_gBox_KZ_of_gnorm_le h2, h2⟩

lemma mem_Qbig_of_gnorm_le {X : ℝ} {z : GaussianInt} (h0 : z ≠ 0)
    (h : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * X) : z ∈ Qbig X :=
  mem_Qbig_iff.mpr ⟨h0, h⟩

lemma mem_Qbim_iff {X : ℝ} {z : GaussianInt} :
    z ∈ Qbim X ↔ z ≠ 0 ∧ (Work.FIPlan.gnorm z : ℝ) ≤ 2 * X ∧ z.im ≠ 0 := by
  rw [Qbim, Finset.mem_filter, mem_Qbig_iff, and_assoc]

lemma mem_Qbre_iff {X : ℝ} {z : GaussianInt} :
    z ∈ Qbre X ↔ z ≠ 0 ∧ (Work.FIPlan.gnorm z : ℝ) ≤ 2 * X ∧ z.im = 0 := by
  rw [Qbre, Finset.mem_filter, mem_Qbig_iff, and_assoc]

lemma Qbim_subset_Qbig (X : ℝ) : Qbim X ⊆ Qbig X := Finset.filter_subset _ _

lemma Qbre_subset_Qbig (X : ℝ) : Qbre X ⊆ Qbig X := Finset.filter_subset _ _

/-- `Qbig X` is the disjoint union of its non-real and its real part. -/
lemma Qbig_eq_union (X : ℝ) : Qbig X = Qbim X ∪ Qbre X := by
  ext z
  simp only [Qbim, Qbre, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro h
    by_cases hz : z.im = 0
    · exact Or.inr ⟨h, hz⟩
    · exact Or.inl ⟨h, hz⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h

lemma Qbig_mono {X Y : ℝ} (h : X ≤ Y) : Qbig X ⊆ Qbig Y := by
  intro z hz
  obtain ⟨h0, h1⟩ := mem_Qbig_iff.mp hz
  exact mem_Qbig_iff.mpr ⟨h0, by linarith⟩

lemma Qbim_mono {X Y : ℝ} (h : X ≤ Y) : Qbim X ⊆ Qbim Y := by
  intro z hz
  obtain ⟨h0, h1, h2⟩ := mem_Qbim_iff.mp hz
  exact mem_Qbim_iff.mpr ⟨h0, by linarith, h2⟩

lemma Qbre_mono {X Y : ℝ} (h : X ≤ Y) : Qbre X ⊆ Qbre Y := by
  intro z hz
  obtain ⟨h0, h1, h2⟩ := mem_Qbre_iff.mp hz
  exact mem_Qbre_iff.mpr ⟨h0, by linarith, h2⟩

lemma Yset_mono {X Y : ℝ} (h : X ≤ Y) : Yset X ⊆ Yset Y := by
  intro z hz
  rw [mem_Yset_iff] at hz ⊢
  rcases hz with h1 | h1 | h1
  · exact Or.inl (Qbim_mono h h1)
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

end

end Work.FIArea1
