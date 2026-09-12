import Mathlib
import Submission.XTransfer
import Submission.DirSet
import Submission.PolyaCore

/-!
# Isolated task: dependency-map step 1 -- monotonicity and spike-lengthening

Self-contained definitions.  Prove ONLY the declarations below; no other
placeholders may remain (add helpers freely).

PURPOSE: `dubinin_fekete_limsup` reduces, by monotonicity, to the
lengthened hedgehog with all spikes at the maximal length `L := maxSpikeLen
S` in the `|dirSet S|` directions.

1. `feketeNumber_mono` : `K ⊆ K'` implies `feketeNumber K n ≤ feketeNumber
   K' n` for every `n` **provided the smaller `feketeSet` is nonempty and
   the larger one is bounded above** (the raw unbounded statement is false:
   for unbounded `K'` the family `feketeSet K' n` is unbounded above so its
   `sSup` is `0`, e.g. `K = {0,1}`, `K' = ℕ`, `n = 2`).  (Every
   `n`-configuration with points in `K` is one with points in `K'`, so the
   defining set of `feketeNumber K n` is a subset of that of `K'`; use
   `csSup_le_csSup`.)

2. The LENGTHENED hedgehog: `dirUnit (theta) := Complex.exp (theta *
   Complex.I)` (unit complex number of argument theta) and
   `starL S L := ⋃ theta ∈ (dirSet S : Set ℝ), segment ℝ 0 (L •
   dirUnit theta)` where `L • dirUnit theta` is the complex scalar
   `(L : ℂ) * dirUnit theta` (real scalar on the complex line -- expressed
   with `(L : ℂ) * ...`, equal to `L • dirUnit theta` by `Complex.real_smul`).

3. `star_subset_starL` : `star S ⊆ starL S (maxSpikeLen S)`.  Proof: if
   `X ∈ star S`, then `X ∈ segment ℝ 0 w` for some `w ∈ spikeEndpoints S`.
   Let `theta := Complex.arg w` (`theta ∈ dirSet S`), and
   `L := maxSpikeLen S` satisfies `‖w‖ ≤ L` and `0 ≤ L`; the polar form
   `w = ‖w‖ • dirUnit theta` (`Complex.norm_mul_exp_arg_mul_I` +
   `Complex.real_smul`) shows `X = (t·‖w‖) • dirUnit theta` with
   `0 ≤ t·‖w‖ ≤ ‖w‖ ≤ L`, hence `X` lies in `segment ℝ 0 (L • dirUnit
   theta)` (helper `smul_mem_segment_zero_of_le`).

4. Conclude (consequence):
   `feketeNumber_mono` applied to `star_subset_starL` gives
   `m_n(star S) ≤ m_n(starL S (maxSpikeLen S))`.

NOTES: `Complex.exp (theta * Complex.I)` is the unit vector; `(L : ℂ) *
Complex.exp (theta * Complex.I)` is the complex scalar version.  Real
scalars `t • c` and complex scalars `(t : ℂ) * c` agree on `ℂ`
(`Complex.real_smul`); the existing `Submission.XTransfer.mem_segment_zero_
iff` uses real scalar multiples `t • c` -- prefer that form.  Add whatever
hypotheses are genuinely needed (e.g. boundedness of the larger
`feketeSet`) and state them explicitly in the theorem statements.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.DubininMap

open Submission.XTransfer
open Submission.DirSet
open Submission.PolyaCore

/-- The Vandermonde product of `n` points. -/
def vdm (x : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖

/-- The set of Vandermonde products over `n`-point configurations in `K`. -/
def feketeSet (K : Set ℂ) (n : ℕ) : Set ℝ :=
  {d : ℝ | ∃ x : ℕ → ℂ, (∀ i : ℕ, i < n → x i ∈ K) ∧ d = vdm x n}

/-- **Fekete number.** -/
def feketeNumber (K : Set ℂ) (n : ℕ) : ℝ := sSup (feketeSet K n)

/-- Maximal spike length of the hedgehog over `S`. -/
def maxSpikeLen (S : Finset ℂ) : ℝ :=
  sSup {r : ℝ | ∃ w ∈ spikeEndpoints S, r = ‖w‖}

/-- Unit complex number of argument `theta`. -/
def dirUnit (theta : ℝ) : ℂ := Complex.exp (theta * Complex.I)

/-- The lengthened hedgehog: in every direction `theta ∈ dirSet S`, the
segment `[0, L · dirUnit theta]`. -/
def starL (S : Finset ℂ) (L : ℝ) : Set ℂ :=
  {X : ℂ | ∃ theta ∈ dirSet S, X ∈ segment ℝ 0 ((L : ℂ) * dirUnit theta)}

/-! ## Basic Fekete-set bookkeeping (nonemptiness and boundedness) -/

/-- A nonempty set of complex numbers yields nonempty Fekete families. -/
lemma feketeSet_nonempty_of_nonempty {K : Set ℂ} (hK : K.Nonempty) (n : ℕ) :
    (feketeSet K n).Nonempty := by
  rcases hK with ⟨c, hc⟩
  let x : ℕ → ℂ := fun _ => c
  refine ⟨vdm x n, x, ?_, rfl⟩
  intro i hi
  exact hc

/-- Pointwise bound on an `n`-tuple in a norm-ball: `vdm x n` is bounded by
the product over `i < n` of `(2R)^i` (each pair `j < i` contributes at most
`2R`). -/
lemma vdm_le_prod (x : ℕ → ℂ) (n : ℕ) (R : ℝ)
    (h : ∀ i : ℕ, i < n → ‖x i‖ ≤ R) :
    vdm x n ≤ ∏ i ∈ Finset.range n, (∏ _j ∈ Finset.range i, (2 * R)) := by
  unfold vdm
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.prod_nonneg (fun j _ => norm_nonneg (x j - x i))
  · intro i hi
    apply Finset.prod_le_prod
    · intro j _
      exact norm_nonneg (x j - x i)
    · intro j hj
      calc
        ‖x j - x i‖ ≤ ‖x j‖ + ‖x i‖ := norm_sub_le _ _
        _ ≤ R + R := by
          exact add_le_add
            (h j (lt_trans (Finset.mem_range.mp hj) (Finset.mem_range.mp hi)))
            (h i (Finset.mem_range.mp hi))
        _ = 2 * R := by ring

/-- If every point of `E` lies in the closed ball of radius `R`, then the
Fekete family of `E` is bounded above. -/
lemma feketeSet_bddAbove_of_norm_le {E : Set ℂ} {R : ℝ}
    (hE : ∀ X ∈ E, ‖X‖ ≤ R) (n : ℕ) : BddAbove (feketeSet E n) := by
  refine ⟨∏ i ∈ Finset.range n, (∏ _j ∈ Finset.range i, (2 * max R 0)), ?_⟩
  intro d hd
  rcases hd with ⟨x, hx, rfl⟩
  exact vdm_le_prod x n (max R 0) (fun i hi =>
    le_trans (hE (x i) (hx i hi)) (le_max_left R 0))

/-- The defining family of `feketeNumber` is monotone in the set `K`. -/
lemma feketeSet_subset_of_subset {K K' : Set ℂ} (h : K ⊆ K') (n : ℕ) :
    feketeSet K n ⊆ feketeSet K' n := by
  intro d hd
  rcases hd with ⟨x, hx, rfl⟩
  exact ⟨x, (fun i hi => h (hx i hi)), rfl⟩

/-- Monotonicity of the Fekete numbers under set inclusion (for a nonempty
smaller family and a bounded-above larger family).  The statement with no
further hypotheses is *false*: for unbounded `K'`, `feketeSet K' n` is
unbounded above so its `sSup` is `0` (e.g. `K = {0,1}`, `K' = ℕ`, `n =
2`). -/
lemma feketeNumber_mono {K K' : Set ℂ} (h : K ⊆ K') (n : ℕ)
    (hKne : (feketeSet K n).Nonempty) (hK'bdd : BddAbove (feketeSet K' n)) :
    feketeNumber K n ≤ feketeNumber K' n := by
  exact csSup_le_csSup hK'bdd hKne (feketeSet_subset_of_subset h n)

/-! ## Spike-length geometry -/

/-- Each spike endpoint norm is bounded by the maximal spike length. -/
lemma norm_le_maxSpikeLen {S : Finset ℂ} (hne : (spikeEndpoints S).Nonempty)
    {w : ℂ} (hw : w ∈ spikeEndpoints S) : ‖w‖ ≤ maxSpikeLen S := by
  classical
  have _hne' : (spikeEndpoints S).Nonempty := hne
  unfold maxSpikeLen
  let A : Finset ℝ := (spikeEndpoints S).image (fun w : ℂ => ‖w‖)
  have hA : ({r : ℝ | ∃ w ∈ spikeEndpoints S, r = ‖w‖} : Set ℝ) = (A : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    · intro hr
      rcases (Finset.mem_image.mp (Finset.mem_coe.mp hr)) with ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [hA]
  exact le_csSup A.bddAbove (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩))

/-- The maximal spike length is nonnegative when there is a spike. -/
lemma maxSpikeLen_nonneg {S : Finset ℂ} (hne : (spikeEndpoints S).Nonempty) :
    0 ≤ maxSpikeLen S := by
  have hne' : (spikeEndpoints S).Nonempty := hne
  rcases hne with ⟨w, hw⟩
  exact le_trans (norm_nonneg w) (norm_le_maxSpikeLen hne' hw)

/-! ## Segment nesting along a ray -/

/-- A point `a • d` with `0 ≤ a ≤ L` (and `0 ≤ L`) lies on the segment
from `0` to `L • d`. -/
lemma smul_mem_segment_zero_of_le {d : ℂ} {a L : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ L)
    (hL0 : 0 ≤ L) : a • d ∈ segment ℝ 0 (L • d) := by
  classical
  by_cases hL : L = 0
  · have ha : a = 0 := le_antisymm (by simpa [hL] using haL) ha0
    subst a
    rw [hL, zero_smul]
    exact left_mem_segment ℝ (0 : ℂ) (0 : ℂ)
  · let s : ℝ := a / L
    have hs0 : 0 ≤ s := div_nonneg ha0 hL0
    have hs1 : s ≤ 1 := div_le_one_of_le₀ haL hL0
    have hsL : s * L = a := by
      dsimp [s]
      field_simp [hL]
    have hmem : a • d = s • (L • d) := by
      calc
        a • d = (s * L) • d := by rw [hsL]
        _ = s • (L • d) := (smul_smul s L d).symm
    exact (Submission.XTransfer.mem_segment_zero_iff (L • d) (a • d)).mpr
      ⟨s, ⟨hs0, hs1⟩, hmem⟩

/-- Membership in `star S` is equivalent to lying on a segment from `0` to
a spike endpoint. -/
lemma mem_star_iff_spikeEndpoints (S : Finset ℂ) (X : ℂ) :
    X ∈ Submission.XTransfer.star S ↔
      ∃ w ∈ spikeEndpoints S, X ∈ segment ℝ 0 w := by
  classical
  constructor
  · rintro ⟨z, hz, hseg⟩
    rcases hseg with hseg | hseg
    · refine ⟨z ^ 2, ?_, hseg⟩
      rw [spikeEndpoints, Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    · refine ⟨z ^ 4, ?_, hseg⟩
      rw [spikeEndpoints, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  · rintro ⟨w, hw, hseg⟩
    rw [spikeEndpoints, Finset.mem_union] at hw
    rcases hw with hw | hw
    · rcases (Finset.mem_image.mp hw) with ⟨z, hz, hwz⟩
      refine ⟨z, hz, Or.inl ?_⟩
      simpa [hwz] using hseg
    · rcases (Finset.mem_image.mp hw) with ⟨z, hz, hwz⟩
      refine ⟨z, hz, Or.inr ?_⟩
      simpa [hwz] using hseg

/-- A point on a segment `[0, w]` for a spike endpoint `w` lies in the
lengthened hedgehog `starL S (maxSpikeLen S)`. -/
lemma mem_starL_of_mem_segment_spike {S : Finset ℂ}
    (hne : (spikeEndpoints S).Nonempty) {w : ℂ} (hw : w ∈ spikeEndpoints S)
    {X : ℂ} (hX : X ∈ segment ℝ 0 w) : X ∈ starL S (maxSpikeLen S) := by
  classical
  let L : ℝ := maxSpikeLen S
  let theta : ℝ := Complex.arg w
  have hwL : ‖w‖ ≤ L := by
    dsimp [L]
    exact norm_le_maxSpikeLen hne hw
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact maxSpikeLen_nonneg hne
  have htheta : theta ∈ dirSet S := by
    dsimp [theta, dirSet]
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hpol : w = ‖w‖ • dirUnit theta := by
    dsimp [theta, dirUnit]
    exact (Complex.norm_mul_exp_arg_mul_I w).symm
  rcases (Submission.XTransfer.mem_segment_zero_iff w X).mp hX with ⟨t, ht, hXt⟩
  let a : ℝ := t * ‖w‖
  have hXa : X = a • dirUnit theta := by
    dsimp [a]
    calc
      X = t • w := hXt
      _ = t • (‖w‖ • dirUnit theta) := congrArg (fun z : ℂ => t • z) hpol
      _ = (t * ‖w‖) • dirUnit theta := by rw [smul_smul]
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg ht.1 (norm_nonneg w)
  have haL : a ≤ L := by
    dsimp [a]
    calc
      t * ‖w‖ ≤ ‖w‖ :=
        (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg w)).trans_eq (by rw [one_mul])
      _ ≤ L := hwL
  have hseg0 : a • dirUnit theta ∈ segment ℝ 0 (L • dirUnit theta) :=
    smul_mem_segment_zero_of_le (d := dirUnit theta) (a := a) (L := L) ha0 haL hL0
  rw [← hXa] at hseg0
  exact ⟨theta, htheta, hseg0⟩

/-- **Star ⊆ lengthened star.**  Every spike segment `[0,w]` extends to
length `maxSpikeLen S` along its own direction. -/
theorem star_subset_starL (S : Finset ℂ) (hne : (spikeEndpoints S).Nonempty) :
    Submission.XTransfer.star S ⊆ starL S (maxSpikeLen S) := by
  intro X hX
  rcases (mem_star_iff_spikeEndpoints S X).mp hX with ⟨w, hw, hseg⟩
  exact mem_starL_of_mem_segment_spike hne hw hseg

/-! ## Boundedness of the lengthened hedgehog -/

/-- Every point of `starL S L` (with `0 ≤ L`) has norm at most `L`. -/
lemma norm_le_of_mem_starL {S : Finset ℂ} {L : ℝ} (hL0 : 0 ≤ L) {X : ℂ}
    (hX : X ∈ starL S L) : ‖X‖ ≤ L := by
  rcases hX with ⟨theta, htheta, hseg⟩
  have hnorm : ‖(L : ℂ) * dirUnit theta‖ = L := by
    dsimp [dirUnit]
    simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hL0]
  rcases (Submission.XTransfer.mem_segment_zero_iff ((L : ℂ) * dirUnit theta) X).mp hseg with
    ⟨t, ht, hXt⟩
  calc
    ‖X‖ = ‖t • ((L : ℂ) * dirUnit theta)‖ := by rw [hXt]
    _ = |t| * ‖(L : ℂ) * dirUnit theta‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ = t * ‖(L : ℂ) * dirUnit theta‖ := by rw [abs_of_nonneg ht.1]
    _ = t * L := by rw [hnorm]
    _ ≤ L := by
      nlinarith [ht.1, ht.2, hL0]

/-- Consequence: the Fekete numbers of the hedgehog are at most those of
the lengthened hedgehog. -/
theorem feketeNumber_le_starL (S : Finset ℂ) (hne : (spikeEndpoints S).Nonempty)
    (n : ℕ) :
    feketeNumber (Submission.XTransfer.star S) n ≤ feketeNumber (starL S (maxSpikeLen S)) n := by
  classical
  have hL0 : 0 ≤ maxSpikeLen S := maxSpikeLen_nonneg hne
  have hKstar : (Submission.XTransfer.star S).Nonempty := by
    rcases hne with ⟨w, hw⟩
    rw [spikeEndpoints, Finset.mem_union] at hw
    rcases hw with hw | hw
    · rcases (Finset.mem_image.mp hw) with ⟨z, hz, _⟩
      exact ⟨0, Submission.XTransfer.zero_mem_star ⟨z, hz⟩⟩
    · rcases (Finset.mem_image.mp hw) with ⟨z, hz, _⟩
      exact ⟨0, Submission.XTransfer.zero_mem_star ⟨z, hz⟩⟩
  have hKne : (feketeSet (Submission.XTransfer.star S) n).Nonempty :=
    feketeSet_nonempty_of_nonempty hKstar n
  have hbdd : BddAbove (feketeSet (starL S (maxSpikeLen S)) n) :=
    feketeSet_bddAbove_of_norm_le
      (E := starL S (maxSpikeLen S)) (R := maxSpikeLen S) (n := n)
      (fun X hX => norm_le_of_mem_starL hL0 hX)
  exact feketeNumber_mono (K := Submission.XTransfer.star S)
    (K' := starL S (maxSpikeLen S)) (star_subset_starL S hne) n hKne hbdd

end Submission.DubininMap

end
