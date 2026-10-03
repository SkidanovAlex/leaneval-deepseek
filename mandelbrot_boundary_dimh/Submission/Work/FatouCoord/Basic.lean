/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib

/-!
# Fatou coordinates for parabolic germs

This file is the language layer of the `FatouCoord` chapter.  It sets up

* the **parabolic chart** `chart z = -1/z` and its conjugate dynamics `wMap f`, which turns a
  parabolic germ `f z = z + z ^ 2 * h z` (`h 0 = 1`) into a map that is a translation by `1`
  up to `O(1/w)`;
* **petals** `Petal r M`, the sector-like domains `‖z‖ < r`, `Re (-1/z) > M` in which the
  attracting dynamics takes place;
* the predicates `IsAttractingPetal`, `IsRepellingPetal` for the geometric set-up of the
  Leau–Fatou flower;
* `IsFatouCoordinateOn f φ P`: `φ` is holomorphic on `P` and `φ ∘ f = φ + 1` there;
* the **antiholomorphic** variant (`IsAntiholomorphicOn`, `IsAntiholomorphicFatouOn`), the
  Ecalle height and the **equator** `equator φ = {z | Im (φ z) = 0}`;
* the orbit relation on a petal and the **Écalle cylinder** of a petal.

Complex conjugation is written `star` (equivalently `starRingEnd ℂ`); the lemmas
`Complex.conj_im`, `Complex.conj_ofReal`, `star_add`, `star_star` are used throughout.

The main existence theorem (Leau–Fatou) is in `Submission/Work/FatouCoord/Existence.lean`,
uniqueness in `.../Unique.lean`, the antiholomorphic statement (Hubbard–Schleicher Lemma 2.3)
in `.../Antiholomorphic.lean`.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord

noncomputable section

variable {f g h finv φ φ₁ φ₂ : ℂ → ℂ} {P Q : Set ℂ} {r r' M M' : ℝ} {z w : ℂ}

/-! ## Elementary tools -/

/-- Iterates of a function commute with each other. -/
theorem iterate_comm {α : Type*} (f : α → α) (m n : ℕ) (x : α) :
    f^[m] (f^[n] x) = f^[n] (f^[m] x) := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

/-- A function mapping `s` into itself has all its iterates mapping `s` into itself. -/
theorem mapsTo_iterate_of_mapsTo {α : Type*} {s : Set α} {F : α → α} (hF : MapsTo F s s)
    (n : ℕ) : MapsTo (F^[n]) s s := by
  intro x hx
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa [Function.iterate_succ_apply'] using hF ih

/-- `1/2` is real, hence fixed by complex conjugation. -/
theorem star_one_half : star (1 / 2 : ℂ) = 1 / 2 := by simp

theorem im_star_add_half (w : ℂ) : (star w + (1 / 2 : ℂ)).im = -w.im := by
  simp [Complex.conj_im]

/-- Conjugating twice and adding `1/2` returns `w + 1/2`. -/
theorem star_star_add_half (w : ℂ) : star (star w + (1 / 2 : ℂ)) = w + 1 / 2 := by
  simp

/-! ## The parabolic chart `w = -1/z` -/

/-- The parabolic chart `z ↦ -1/z`, an involution of `ℂ \ {0}`. -/
def chart (z : ℂ) : ℂ := -1 / z

@[simp] theorem chart_zero : chart 0 = 0 := by simp [chart]

theorem chart_ne_zero {z : ℂ} (hz : z ≠ 0) : chart z ≠ 0 := by
  simpa [chart] using hz

@[simp] theorem chart_chart {z : ℂ} (hz : z ≠ 0) : chart (chart z) = z := by
  simp only [chart, ne_eq] at *
  field_simp

theorem chart_injective : Function.Injective (chart : ℂ → ℂ) := by
  intro z w hzw
  rcases eq_or_ne z 0 with rfl | hz
  · have hw : w = 0 := by
      by_contra hw0
      have : chart w = 0 := by rw [← hzw]; simp
      exact chart_ne_zero hw0 this
    exact hw.symm
  · have hw : w ≠ 0 := by
      intro hw
      rw [hw, chart_zero] at hzw
      exact chart_ne_zero hz hzw
    have := congrArg chart hzw
    rwa [chart_chart hz, chart_chart hw] at this

theorem norm_chart {z : ℂ} (hz : z ≠ 0) : ‖chart z‖ = (‖z‖)⁻¹ := by
  simp only [chart, norm_div, norm_neg, norm_one, one_div]

theorem re_chart {z : ℂ} (hz : z ≠ 0) : (chart z).re = -z.re / Complex.normSq z := by
  rw [chart, Complex.div_re]
  simp

/-- The dynamics induced by `f` in the chart `w = -1/z`. -/
def wMap (f : ℂ → ℂ) (w : ℂ) : ℂ := chart (f (chart w))

theorem wMap_apply (w : ℂ) : wMap f w = -1 / f (-1 / w) := rfl

/-! ## Petals -/

/-- The **petal** of radius `r` and level `M`: the set of `z` with `‖z‖ < r` and
`Re (-1/z) > M`.  For `M > 0` this is a sector-like domain near `0` opening in the direction
of the negative real axis; it is the region in which the attracting dynamics of
`f z = z + z ^ 2 * h z` takes place. -/
def Petal (r M : ℝ) : Set ℂ := {z : ℂ | ‖z‖ < r ∧ z.re < -M * Complex.normSq z}

@[simp] theorem mem_Petal {z : ℂ} : z ∈ Petal r M ↔ ‖z‖ < r ∧ z.re < -M * Complex.normSq z :=
  Iff.rfl

theorem Petal_subset_ball : Petal r M ⊆ ball 0 r := fun z hz => by simpa using hz.1

theorem Petal_mono (hr : r ≤ r') (hM : M' ≤ M) : Petal r M ⊆ Petal r' M' := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  refine ⟨lt_of_lt_of_le h1 hr, ?_⟩
  have h3 : -M * Complex.normSq z ≤ -M' * Complex.normSq z := by
    nlinarith [Complex.normSq_nonneg z]
  linarith

theorem isOpen_Petal : IsOpen (Petal r M) := by
  rw [Petal]
  exact isOpen_lt continuous_norm continuous_const |>.inter
    (isOpen_lt Complex.continuous_re (continuous_const.mul Complex.continuous_normSq))

theorem not_mem_Petal_zero : (0 : ℂ) ∉ Petal r M := by
  simp [Petal]

theorem Petal_subset_compl_zero : Petal r M ⊆ {0}ᶜ := fun _ hz h => not_mem_Petal_zero (h ▸ hz)

theorem ne_zero_of_mem_Petal (hz : z ∈ Petal r M) : z ≠ 0 :=
  fun h => not_mem_Petal_zero (h ▸ hz)

theorem normSq_pos_of_mem_Petal (hz : z ∈ Petal r M) : 0 < Complex.normSq z :=
  Complex.normSq_pos.mpr (ne_zero_of_mem_Petal hz)

/-- Inside a petal `Petal r M` with `M > 0` the modulus is bounded by `1/M`. -/
theorem norm_lt_inv_of_mem_Petal (hM : 0 < M) (hz : z ∈ Petal r M) : ‖z‖ < 1 / M := by
  have hz0 : z ≠ 0 := ne_zero_of_mem_Petal hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h4 : M * Complex.normSq z < -z.re := by linarith [hz.2]
  have h5 : -z.re ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [abs_le] at this
    linarith [this.1]
  rw [Complex.normSq_eq_norm_sq] at h4
  have h7 : M * ‖z‖ < 1 := by nlinarith
  rw [lt_div_iff₀ hM]
  linarith

/-- The **repelling petal**: the mirror image of `Petal r M` in the positive real direction.
It is the domain on which the inverse germ of a parabolic germ acts as an attracting petal. -/
def PetalRep (r M : ℝ) : Set ℂ := {z : ℂ | ‖z‖ < r ∧ M * Complex.normSq z < z.re}

@[simp] theorem mem_PetalRep {z : ℂ} :
    z ∈ PetalRep r M ↔ ‖z‖ < r ∧ M * Complex.normSq z < z.re := Iff.rfl

theorem neg_mem_Petal_iff {z : ℂ} : -z ∈ Petal r M ↔ z ∈ PetalRep r M := by
  rw [mem_Petal, mem_PetalRep]
  simp only [norm_neg, Complex.neg_re, Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> exact ⟨h.1, by linarith [h.2]⟩

theorem mem_Petal_neg_iff {z : ℂ} : z ∈ Petal r M ↔ -z ∈ PetalRep r M := by
  rw [← neg_mem_Petal_iff, neg_neg]

theorem isOpen_PetalRep : IsOpen (PetalRep r M) := by
  rw [PetalRep]
  exact isOpen_lt continuous_norm continuous_const |>.inter
    (isOpen_lt (continuous_const.mul Complex.continuous_normSq) Complex.continuous_re)

theorem not_mem_PetalRep_zero : (0 : ℂ) ∉ PetalRep r M := by
  simp [PetalRep]

theorem PetalRep_subset_compl_zero : PetalRep r M ⊆ {0}ᶜ :=
  fun _ hz h => not_mem_PetalRep_zero (h ▸ hz)

/-- The image of the petal `Petal r M` under the chart `w = -1/z`. -/
def PetalChart (r M : ℝ) : Set ℂ := {w : ℂ | M < w.re ∧ 1 / r < ‖w‖}

@[simp] theorem mem_PetalChart {w : ℂ} :
    w ∈ PetalChart r M ↔ M < w.re ∧ 1 / r < ‖w‖ := Iff.rfl

/-- The chart identifies the petal `Petal r M` with the "right sector" `PetalChart r M`. -/
theorem Petal_eq_preimage_chart (hr : 0 < r) : Petal r M = chart ⁻¹' PetalChart r M := by
  ext z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mem_Petal, mem_preimage, mem_PetalChart, chart_zero]
    simp only [norm_zero, Complex.zero_re, Complex.normSq_zero, mul_zero, neg_zero,
      lt_self_iff_false, and_false, false_iff, not_and]
    intro _
    exact not_lt.mpr (le_of_lt (one_div_pos.mpr hr))
  · rw [mem_Petal, mem_preimage, mem_PetalChart, re_chart hz, norm_chart hz]
    have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hlt : (1 / r : ℝ) < (‖z‖)⁻¹ ↔ ‖z‖ < r := by
      rw [one_div, inv_lt_inv₀ (by positivity) hn]
    have hdiv : M < -z.re / Complex.normSq z ↔ z.re < -M * Complex.normSq z := by
      rw [lt_div_iff₀ hns]
      constructor <;> intro hh <;> linarith
    rw [hlt, hdiv, and_comm]

theorem chart_mem_Petal_iff (hr : 0 < r) (hz : z ≠ 0) :
    z ∈ Petal r M ↔ chart z ∈ PetalChart r M := by
  rw [Petal_eq_preimage_chart hr]
  exact Iff.rfl

/-! ## Petals as dynamical domains -/

/-- An **attracting petal** for `f`: an open domain not containing `0`, mapped into itself by
`f`, in which all orbits converge to `0`. -/
def IsAttractingPetal (f : ℂ → ℂ) (P : Set ℂ) : Prop :=
  IsOpen P ∧ P ⊆ {0}ᶜ ∧ MapsTo f P P ∧ ∀ z ∈ P, Tendsto (fun n : ℕ => f^[n] z) atTop (𝓝 0)

/-- A **repelling petal** for `f`: the domain of a local inverse `finv` of `f` which maps `P`
into itself and whose `finv`-orbits converge to `0`. -/
def IsRepellingPetal (f finv : ℂ → ℂ) (P : Set ℂ) : Prop :=
  IsOpen P ∧ P ⊆ {0}ᶜ ∧ MapsTo finv P P ∧ (∀ z ∈ P, f (finv z) = z) ∧
    ∀ z ∈ P, Tendsto (fun n : ℕ => finv^[n] z) atTop (𝓝 0)

theorem IsAttractingPetal.mapsTo_iterate (h : IsAttractingPetal f P) (n : ℕ) :
    MapsTo (f^[n]) P P := mapsTo_iterate_of_mapsTo h.2.2.1 n

theorem IsAttractingPetal.isOpen (h : IsAttractingPetal f P) : IsOpen P := h.1

theorem IsAttractingPetal.not_mem_zero (h : IsAttractingPetal f P) : (0 : ℂ) ∉ P :=
  fun hz => h.2.1 hz rfl

theorem IsRepellingPetal.isOpen (h : IsRepellingPetal f finv P) : IsOpen P := h.1

/-- The repelling petal is contained in the image of `f`. -/
theorem IsRepellingPetal.subset_image (h : IsRepellingPetal f finv P) : P ⊆ f '' P :=
  fun z hz => ⟨finv z, h.2.2.1 hz, h.2.2.2.1 z hz⟩

theorem IsRepellingPetal.mapsTo_iterate (h : IsRepellingPetal f finv P) (n : ℕ) :
    MapsTo (finv^[n]) P P := mapsTo_iterate_of_mapsTo h.2.2.1 n

/-! ## Fatou coordinates -/

/-- `φ` is a **Fatou coordinate** for `f` on `P` if it is holomorphic on `P` and satisfies
the Abel equation `φ (f z) = φ z + 1` on `P`. -/
def IsFatouCoordinateOn (f φ : ℂ → ℂ) (P : Set ℂ) : Prop :=
  DifferentiableOn ℂ φ P ∧ ∀ z ∈ P, φ (f z) = φ z + 1

theorem IsFatouCoordinateOn.iterate (h : IsFatouCoordinateOn f φ P) (hP : MapsTo f P P)
    (hz : z ∈ P) (n : ℕ) : φ (f^[n] z) = φ z + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', h.2 _ (mapsTo_iterate_of_mapsTo hP n hz), ih]
    push_cast
    ring

theorem IsFatouCoordinateOn.add_const (h : IsFatouCoordinateOn f φ P) (c : ℂ) :
    IsFatouCoordinateOn f (fun z => φ z + c) P :=
  ⟨h.1.add_const c, fun z hz => by
    show φ (f z) + c = φ z + c + 1
    rw [h.2 z hz]; ring⟩

theorem IsFatouCoordinateOn.sub_const (h : IsFatouCoordinateOn f φ P) (c : ℂ) :
    IsFatouCoordinateOn f (fun z => φ z - c) P :=
  ⟨h.1.sub_const c, fun z hz => by
    show φ (f z) - c = φ z - c + 1
    rw [h.2 z hz]; ring⟩

/-- On an open set, being a Fatou coordinate only requires analyticity, which is the same
as complex differentiability there. -/
theorem isFatouCoordinateOn_iff_analyticOn (hP : IsOpen P) :
    IsFatouCoordinateOn f φ P ↔ AnalyticOn ℂ φ P ∧ ∀ z ∈ P, φ (f z) = φ z + 1 := by
  rw [Complex.analyticOn_iff_differentiableOn hP]
  exact Iff.rfl

theorem IsFatouCoordinateOn.differentiableOn (h : IsFatouCoordinateOn f φ P) :
    DifferentiableOn ℂ φ P := h.1

theorem IsFatouCoordinateOn.analyticOn (h : IsFatouCoordinateOn f φ P) (hP : IsOpen P) :
    AnalyticOn ℂ φ P := (Complex.analyticOn_iff_differentiableOn hP).mpr h.1

/-- The difference of two Fatou coordinates on the same set is invariant under `f`. -/
theorem IsFatouCoordinateOn.difference_invariant (h₁ : IsFatouCoordinateOn f φ₁ P)
    (h₂ : IsFatouCoordinateOn f φ₂ P) {z : ℂ} (hz : z ∈ P) :
    (φ₁ - φ₂) (f z) = (φ₁ - φ₂) z := by
  simp only [Pi.sub_apply, h₁.2 z hz, h₂.2 z hz]
  ring

/-- The difference `φ₁ (f^[n] z) - φ₂ (f^[n] z)` is independent of `n`. -/
theorem IsFatouCoordinateOn.difference_invariant_iterate (h₁ : IsFatouCoordinateOn f φ₁ P)
    (h₂ : IsFatouCoordinateOn f φ₂ P) (hP : MapsTo f P P) (hz : z ∈ P) (n : ℕ) :
    (φ₁ - φ₂) (f^[n] z) = (φ₁ - φ₂) z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', h₁.difference_invariant h₂ (mapsTo_iterate_of_mapsTo hP n hz),
      ih]

/-! ## The antiholomorphic variant -/

/-- `g` is **antiholomorphic** on `U` if `star ∘ g` (i.e. `conj ∘ g`) is holomorphic there. -/
def IsAntiholomorphicOn (g : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ (fun z => star (g z)) U

/-- The **Ecalle height** of a point with respect to a chart `φ` (its imaginary part). -/
def ecalleHeight (φ : ℂ → ℂ) (z : ℂ) : ℝ := (φ z).im

/-- The **equator** in the dynamical plane for a chart `φ`: the level set `Im φ = 0`. -/
def equator (φ : ℂ → ℂ) : Set ℂ := {z : ℂ | (φ z).im = 0}

@[simp] theorem mem_equator {z : ℂ} : z ∈ equator φ ↔ (φ z).im = 0 := Iff.rfl

/-- **Hubbard–Schleicher Lemma 2.3**, local form: an antiholomorphic map `g` whose square is
parabolic is conjugate, via the holomorphic chart `φ`, to `w ↦ w̄ + 1/2`; equivalently
`φ ∘ g = star ∘ φ + 1/2`, and then `φ ∘ g^2 = φ + 1` and the equator `Im φ = 0` is
`g`-invariant. -/
def IsAntiholomorphicFatouOn (g φ : ℂ → ℂ) (P : Set ℂ) : Prop :=
  IsAntiholomorphicOn g P ∧ DifferentiableOn ℂ φ P ∧
    ∀ z ∈ P, φ (g z) = star (φ z) + 1 / 2

/-- Squaring the antiholomorphic Fatou coordinate gives a (holomorphic) Fatou coordinate for
`g ∘ g`. -/
theorem IsAntiholomorphicFatouOn.comp_self (h : IsAntiholomorphicFatouOn g φ P)
    (hg : MapsTo g P P) : IsFatouCoordinateOn (g ∘ g) φ P :=
  ⟨h.2.1, fun z hz => by
    have h1 := h.2.2 z hz
    have h2 := h.2.2 (g z) (hg hz)
    simp only [Function.comp_apply]
    rw [h2, h1, star_star_add_half]
    ring⟩

/-- The equator is invariant under the antiholomorphic dynamics. -/
theorem IsAntiholomorphicFatouOn.equator_mapsTo (h : IsAntiholomorphicFatouOn g φ P)
    {z : ℂ} (hz : z ∈ equator φ) (hP : z ∈ P) : g z ∈ equator φ := by
  rw [mem_equator] at hz ⊢
  rw [h.2.2 z hP, im_star_add_half, hz, neg_zero]

/-- The Ecalle height changes sign under the antiholomorphic map. -/
theorem IsAntiholomorphicFatouOn.ecalleHeight_map (h : IsAntiholomorphicFatouOn g φ P)
    {z : ℂ} (hz : z ∈ P) : ecalleHeight φ (g z) = -ecalleHeight φ z := by
  simp only [ecalleHeight, h.2.2 z hz, im_star_add_half]

/-! ## The Écalle cylinder -/

/-- The orbit relation of `f` on `P`: two points of `P` are equivalent if some forward
iterates of them agree. -/
def petalOrbitSetoid (f : ℂ → ℂ) (P : Set ℂ) : Setoid P where
  r a b := ∃ m n : ℕ, f^[m] a.1 = f^[n] b.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; exact ⟨0, 0, rfl⟩
    · rintro a b ⟨m, n, hmn⟩; exact ⟨n, m, hmn.symm⟩
    · rintro a b c ⟨m, n, hmn⟩ ⟨p, q, hpq⟩
      refine ⟨m + p, n + q, ?_⟩
      calc f^[m + p] a.1 = f^[p] (f^[m] a.1) :=
            (Function.iterate_add_apply f m p a.1).trans (iterate_comm f m p a.1)
        _ = f^[p] (f^[n] b.1) := by rw [hmn]
        _ = f^[n] (f^[p] b.1) := iterate_comm f p n b.1
        _ = f^[n] (f^[q] c.1) := by rw [hpq]
        _ = f^[n + q] c.1 := (Function.iterate_add_apply f n q c.1).symm

/-- The standard **Écalle cylinder** `ℂ/ℤ`. -/
def Cylinder : Type := ℂ ⧸ AddSubgroup.zmultiples (1 : ℂ)

end

end Work.FatouCoord
