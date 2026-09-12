import Mathlib

/-!
# Discrete convexity on `{0, …, d}` (Grayson-polygon layer, item (i) — core API)

This module develops the elementary real analysis needed by the Section-3 (Grayson
polygon / Harder–Narasimhan) layer of de Saxcé's *Rational approximations to linear
subspaces*: discrete convex functions on the integer interval `{0, …, d}` vanishing at
the endpoints, and their slope arithmetic.

The Grayson polygon `c` of a lattice `∆ ≤ ℝᵈ` is the largest convex function on
`{0,…,d}` lying below the points `(dim W, φ(W))` over all discrete subgroups `W ≤ ∆`,
with `c(0) = c(d) = 0` (the trivial and the full subgroup give `φ = log 1 = 0` when the
lattice is unimodular).  All subsequent use (Prop. 4: `log λ_i = c(i) − c(i−1) + O(1)`;
Lemma 4: the derivative identity `⟨ċ_t, c_t⟩ = −(1/ℓ + 1/(d−ℓ))·Σ_s (ℓ'_{s+1}−ℓ'_s)Λ_{j_s+1}`;
Prop. 5) is slope arithmetic on such functions, so we record here the basic API:

- `dslope c i := c(i+1) − c i` — the slope `Λ_{i+1}` of `c` at index `i+1` (paper notation:
  `Λ_i = c(i) − c(i−1)` for `i = 1,…,d`, i.e. `Λ_{i+1} = dslope c i`);
- `DiscreteConvexOn c d` — slope monotonicity `dslope c i ≤ dslope c (i+1)` for
  `i + 2 ≤ d` (equivalently `c(i) + c(i+2) ≥ 2·c(i+1)`), the discrete version of
  convexity on `{0,…,d}`;
- telescope: `c n = c 0 + Σ_{i < n} dslope c i`, hence with `c 0 = c d = 0` the slopes sum
  to `0` (Lemma 4 uses `Σ_{i=1}^d Λ_i = c(d) − c(0) = 0`);
- slope monotonicity across a whole range (`dslope c i ≤ dslope c j` for `i ≤ j` inside
  the range);
- three-term form `c(i) + c(i+2) ≥ 2·c(i+1)`;
- block-affine sums: if the slopes are constantly `Λ` on `[a, b)`, then
  `c b − c a = (b − a) · Λ` — the identity behind "`c` is affine of slope `Λ` between
  consecutive angular points" of the Grayson polygon.

All declarations are Mathlib-only (they will be promoted to the shared commons once the
downstream §3 modules have fixed the exact API shape).
-/

open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace Submission.Polygon

/-- Discrete slope (forward difference) of `c : ℕ → ℝ` at `i`; in the paper notation
`Λ_{i+1} = c(i+1) − c(i)`. -/
def dslope (c : ℕ → ℝ) (i : ℕ) : ℝ := c (i + 1) - c i

/-- `c` is discrete-convex on `{0, …, d}` iff its slope sequence is non-decreasing on
`0, …, d−1`. -/
def DiscreteConvexOn (c : ℕ → ℝ) (d : ℕ) : Prop :=
  ∀ i : ℕ, i + 2 ≤ d → dslope c i ≤ dslope c (i + 1)

/-- Telescoping: `c n = c 0 + Σ_{i < n} dslope c i`. -/
lemma telescope (c : ℕ → ℝ) (n : ℕ) : (∑ i ∈ Finset.range n, dslope c i) = c n - c 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      dsimp [dslope]
      ring

/-- The slopes over `{0,…,d}` sum to `c d − c 0`. -/
lemma sum_slopes_eq_sub (c : ℕ → ℝ) (d : ℕ) :
    (∑ i ∈ Finset.range d, dslope c i) = c d - c 0 :=
  telescope c d

/-- If `c` vanishes at both endpoints of `{0,…,d}`, its `d` slopes sum to zero (this is
`Σ_{i=1}^d Λ_i = c(d) − c(0) = 0` in Lemma 4). -/
lemma sum_slopes_eq_zero_of_ends {c : ℕ → ℝ} {d : ℕ} (h0 : c 0 = 0) (hd0 : c d = 0) :
    (∑ i ∈ Finset.range d, dslope c i) = 0 := by
  rw [telescope, h0, hd0]
  ring

/-- Convexity implies slope monotonicity over any sub-range `i ≤ j` (both inside the
interval `{0,…,d}`). -/
lemma slope_le_of_le {c : ℕ → ℝ} {d : ℕ} (hcvx : DiscreteConvexOn c d) {i j : ℕ}
    (hij : i ≤ j) (hj : j + 1 < d) : dslope c i ≤ dslope c j := by
  induction' j with j ih generalizing i
  · have : i = 0 := by omega
    subst i
    rfl
  · by_cases h : i ≤ j
    · have hstep : dslope c j ≤ dslope c (j + 1) := by
        apply hcvx j
        omega
      have hrest : dslope c i ≤ dslope c j := ih h (by omega)
      exact le_trans hrest hstep
    · have hji : j + 1 = i := by omega
      subst i
      rfl

/-- Three-term (midpoint) form of discrete convexity: `c(i) + c(i+2) ≥ 2·c(i+1)`. -/
lemma three_term_of_convex {c : ℕ → ℝ} {d : ℕ} (hcvx : DiscreteConvexOn c d) {i : ℕ}
    (hi : i + 2 ≤ d) : c i + c (i + 2) ≥ 2 * c (i + 1) := by
  have h1 := hcvx i hi
  -- dslope c i ≤ dslope c (i+1): c(i+1)-c(i) ≤ c(i+2)-c(i+1)
  dsimp [dslope] at h1
  nlinarith

/-- Converse of the three-term form. -/
lemma convex_of_three_term {c : ℕ → ℝ} {d : ℕ}
    (h : ∀ i : ℕ, i + 2 ≤ d → c i + c (i + 2) ≥ 2 * c (i + 1)) : DiscreteConvexOn c d := by
  intro i hi
  have ht := h i hi
  dsimp [dslope]
  nlinarith

/-- Affine-on-a-block sum: if every slope in `[a, b)` equals `Λ`, then
`c b − c a = (b − a) · Λ`.  (This is the identity that makes a convex function with
constant slope `Λ` on a whole block `[j_s+1, j_{s+1}]` affine there.) -/
lemma slope_const_sum {c : ℕ → ℝ} {a b : ℕ} (Λ : ℝ) (hab : a ≤ b)
    (h : ∀ i : ℕ, a ≤ i → i < b → dslope c i = Λ) :
    c b - c a = ((b - a : ℕ) : ℝ) * Λ := by
  have hsum : (∑ i ∈ Finset.Ico a b, dslope c i) = ((b - a : ℕ) : ℝ) * Λ := by
    -- each term equals Λ, and the Ico has b-a elements
    calc
      (∑ i ∈ Finset.Ico a b, dslope c i) = (∑ _ ∈ Finset.Ico a b, Λ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact h i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
      _ = ((Finset.Ico a b).card : ℝ) * Λ := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]
      _ = ((b - a : ℕ) : ℝ) * Λ := by
            rw [Nat.card_Ico]
  -- telescope over the Ico
  have htel : (∑ i ∈ Finset.Ico a b, dslope c i) = c b - c a := by
    rw [Finset.sum_Ico_eq_sub (fun i : ℕ => dslope c i) hab]
    rw [telescope c b, telescope c a]
    ring
  rw [← htel, hsum]

/-- Two-point bound inside a block of constant slope: with `dslope = Λ` on `[a, b)`,
`c i = c a + (i − a)·Λ` for `a ≤ i ≤ b`. -/
lemma slope_const_apply {c : ℕ → ℝ} {a b : ℕ} (Λ : ℝ) (_hab : a ≤ b)
    (h : ∀ i : ℕ, a ≤ i → i < b → dslope c i = Λ) {i : ℕ} (hai : a ≤ i) (hib : i ≤ b) :
    c i = c a + ((i - a : ℕ) : ℝ) * Λ := by
  have hseg : c i - c a = ((i - a : ℕ) : ℝ) * Λ :=
    slope_const_sum Λ hai (fun j h1 h2 => h j h1 (lt_of_lt_of_le h2 hib))
  linarith

/-! ## Largest convex minorant

The Grayson polygon of a lattice is the largest convex minorant of the submodular data
`(dim W, φ(W))` over its discrete subgroups; per rank the data collapses to a function
`g : {0,…,d} → ℝ` (the binding constraint is `c(i) ≤ g(i)`).  We record here that the
pointwise supremum of all convex minorants of such a `g` is again a convex minorant and
dominates every convex minorant. -/

/-- All discrete-convex minorants of `g` on `{0,…,d}`. -/
def MinorantSet (d : ℕ) (g : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {c : ℕ → ℝ | DiscreteConvexOn c d ∧ ∀ i : ℕ, i ≤ d → c i ≤ g i}

/-- The constant minorant of `g` equal to its minimum over `{0,…,d}`. -/
def minMinorant (d : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun _ => ((Finset.range (d + 1)).image g).min' (by
    have hne : (Finset.range (d + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    exact (Finset.image_nonempty (s := Finset.range (d + 1)) (f := g)).mpr hne)

/-- `minMinorant` is indeed a convex minorant of `g`. -/
lemma minMinorant_mem (d : ℕ) (g : ℕ → ℝ) : minMinorant d g ∈ MinorantSet d g := by
  constructor
  · intro i hi
    dsimp [DiscreteConvexOn, dslope, minMinorant]
    simp
  · intro i hi
    dsimp [minMinorant]
    exact Finset.min'_le ((Finset.range (d + 1)).image g) (g i) (by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩)

/-- The family of convex minorants of `g` is nonempty. -/
lemma minorantSet_nonempty (d : ℕ) (g : ℕ → ℝ) : (MinorantSet d g).Nonempty :=
  ⟨minMinorant d g, minMinorant_mem d g⟩

/-- The values at index `i` of all convex minorants of `g`. -/
def minorantValues (d : ℕ) (g : ℕ → ℝ) (i : ℕ) : Set ℝ :=
  {x : ℝ | ∃ c : ℕ → ℝ, c ∈ MinorantSet d g ∧ c i = x}

/-- The set of minorant values is nonempty (at any index). -/
lemma minorantValues_nonempty (d : ℕ) (g : ℕ → ℝ) (i : ℕ) :
    (minorantValues d g i).Nonempty :=
  ⟨minMinorant d g i, minMinorant d g, minMinorant_mem d g, rfl⟩

/-- For `i ≤ d`, the values of the minorants at `i` are bounded above by `g i`. -/
lemma bddAbove_minorantValues (d : ℕ) (g : ℕ → ℝ) {i : ℕ} (hi : i ≤ d) :
    BddAbove (minorantValues d g i) := by
  refine ⟨g i, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  exact hc.2 i hi

/-- The largest convex minorant of `g` on `{0,…,d}`, pointwise the supremum of all
convex minorants. -/
def largestConvexMinorant (d : ℕ) (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  sSup (minorantValues d g i)

/-- The largest convex minorant lies below `g` on `{0,…,d}`. -/
lemma largestConvexMinorant_le_g (d : ℕ) (g : ℕ → ℝ) {i : ℕ} (hi : i ≤ d) :
    largestConvexMinorant d g i ≤ g i := by
  unfold largestConvexMinorant
  exact csSup_le (minorantValues_nonempty d g i) (by
    rintro x ⟨c, hc, rfl⟩
    exact hc.2 i hi)

/-- Every convex minorant lies below the largest one. -/
lemma convexMinorant_le_largest (d : ℕ) (g : ℕ → ℝ) {c : ℕ → ℝ}
    (hc : c ∈ MinorantSet d g) {i : ℕ} (hi : i ≤ d) :
    c i ≤ largestConvexMinorant d g i := by
  unfold largestConvexMinorant
  exact le_csSup (bddAbove_minorantValues d g hi) (by
    exact ⟨c, hc, rfl⟩)

/-- The largest convex minorant is discrete-convex. -/
lemma largestConvexMinorant_convex (d : ℕ) (g : ℕ → ℝ) :
    DiscreteConvexOn (largestConvexMinorant d g) d := by
  apply convex_of_three_term
  intro i hi
  have hi1 : i + 1 ≤ d := by omega
  have hi2 : i + 2 ≤ d := hi
  have hleW : ∀ x ∈ minorantValues d g (i + 1),
      x ≤ (largestConvexMinorant d g i + largestConvexMinorant d g (i + 2)) / 2 := by
    rintro x ⟨c, hcS, rfl⟩
    have hthree : c i + c (i + 2) ≥ 2 * c (i + 1) := three_term_of_convex hcS.1 (i := i) hi
    have hid : i ≤ d := by omega
    have h1 : c i ≤ largestConvexMinorant d g i := convexMinorant_le_largest d g hcS hid
    have h2 : c (i + 2) ≤ largestConvexMinorant d g (i + 2) := convexMinorant_le_largest d g hcS hi
    nlinarith
  have hsup : largestConvexMinorant d g (i + 1) ≤
      (largestConvexMinorant d g i + largestConvexMinorant d g (i + 2)) / 2 := by
    unfold largestConvexMinorant
    exact csSup_le (minorantValues_nonempty d g (i + 1)) hleW
  nlinarith

/-- The largest convex minorant is itself a convex minorant. -/
lemma largestConvexMinorant_mem (d : ℕ) (g : ℕ → ℝ) :
    largestConvexMinorant d g ∈ MinorantSet d g := by
  constructor
  · exact largestConvexMinorant_convex d g
  · intro i hi
    exact largestConvexMinorant_le_g d g hi


/-! ## Endpoint vanishing of the largest convex minorant (affine-tent)

The Grayson polygon of a lattice `∆ ≤ ℝᵈ` is the largest convex minorant of the data
function

    `g(i) := min { φ(W) : W ≤ ∆ a discrete subgroup, rank W = i }`,

`φ(W) = log ‖W‖ + A·(rank W)(d − rank W)`, `i = 0, …, d`  (per rank the binding
constraint `c(i) ≤ φ(W)` over all subgroups `W` of rank `i` is `c(i) ≤ g(i)`).  Its two
endpoint values vanish because the *trivial* subgroup (rank `0`, empty wedge of norm `1`)
and the *full* lattice (rank `d`, `φ(∆) = log covol(∆)`) are themselves part of the data:
`g(0) = log 1 + 0 = 0`, and `g(d) = log covol(∆)`, which is `0` for the unimodular flow
lattices `a_t s_x ℤᵈ` (established in `ImageLatticeCovolume.covol_flowSpan_sx_exp`).

We prove the endpoint condition for *any* data function with vanishing endpoints — the
affine-tent argument: to force `c(0) = 0` it suffices to exhibit *one* convex minorant
through `(0,0)`, namely the affine `a(i) = s·i` whose slope `s` is the minimum of
`g(i)/i` over `1 ≤ i ≤ d` (then `a ≤ g` pointwise); the mirror construction
`a(i) = s'·(d − i)` forces `c(d) = 0`.  (A one-sided constraint suffices at an endpoint;
an interior zero data point would *not* force the minorant through it, so the endpoints
are special.)  With both endpoints vanishing, `sum_slopes_eq_zero_of_ends` gives
`Σ_{i<d} Λ_{i+1} = 0` — the identity used in Lemma 4 of the paper. -/

/-- The slope of the affine minorant through `(0, 0)`: the minimum of `g i / i` over
`1 ≤ i ≤ d` (arbitrary when `d = 0`). -/
def leftSlope (d : ℕ) (g : ℕ → ℝ) : ℝ :=
  if hd : 0 < d then
    ((Finset.Icc 1 d).image (fun i : ℕ => g i / (i : ℝ))).min' (by
      exact (Finset.image_nonempty (f := fun i : ℕ => g i / (i : ℝ))).mpr
        ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hd⟩⟩)
  else 0

/-- `leftSlope` is `≤ g i / i` for every `1 ≤ i ≤ d`. -/
lemma leftSlope_le_div (d : ℕ) (g : ℕ → ℝ) {i : ℕ} (hi1 : 1 ≤ i) (hid : i ≤ d) :
    leftSlope d g ≤ g i / (i : ℝ) := by
  by_cases hd : 0 < d
  · have hmem : g i / (i : ℝ) ∈
        (Finset.Icc 1 d).image (fun j : ℕ => g j / (j : ℝ)) := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨hi1, hid⟩, rfl⟩
    dsimp [leftSlope]
    rw [dif_pos hd]
    exact Finset.min'_le ((Finset.Icc 1 d).image (fun j : ℕ => g j / (j : ℝ)))
      (g i / (i : ℝ)) hmem
  · have : i ≤ 0 := by omega
    omega

/-- The affine minorant through `(0, 0)`: `a(i) = leftSlope · i`. -/
def leftAffine (d : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun i => leftSlope d g * (i : ℝ)

/-- `leftAffine` is a convex minorant of `g` whenever `g 0 = 0`. -/
lemma leftAffine_mem (d : ℕ) (g : ℕ → ℝ) (hg0 : g 0 = 0) : leftAffine d g ∈ MinorantSet d g := by
  constructor
  · intro i hi
    dsimp [DiscreteConvexOn, dslope, leftAffine]
    simp only [Nat.cast_add, Nat.cast_one]
    ring_nf
    exact le_rfl
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      dsimp [leftAffine]
      simp [hg0]
    · have hi1 : 1 ≤ i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
      have hs := leftSlope_le_div d g hi1 hi
      have hiR : 0 < (i : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hi0)
      dsimp [leftAffine]
      exact (le_div_iff₀ hiR).mp hs

/-- **Left endpoint**: if the data vanishes at `0` (`g 0 = 0`), the largest convex
minorant vanishes at `0` too. -/
lemma largestConvexMinorant_zero_left (d : ℕ) (g : ℕ → ℝ) (hg0 : g 0 = 0) :
    largestConvexMinorant d g 0 = 0 := by
  apply le_antisymm
  · have hle := largestConvexMinorant_le_g d g (i := 0) (by omega)
    rwa [hg0] at hle
  · have h := convexMinorant_le_largest d g (leftAffine_mem d g hg0) (i := 0) (by omega)
    simpa [leftAffine] using h

/-- The slope of the affine minorant through `(d, 0)`: the minimum of `g i / (d − i)`
over `0 ≤ i < d` (arbitrary when `d = 0`). -/
def rightSlope (d : ℕ) (g : ℕ → ℝ) : ℝ :=
  if hd : 0 < d then
    ((Finset.Icc 0 (d - 1)).image (fun i : ℕ => g i / ((d - i : ℕ) : ℝ))).min' (by
      exact (Finset.image_nonempty (f := fun i : ℕ => g i / ((d - i : ℕ) : ℝ))).mpr
        ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩)
  else 0

/-- `rightSlope` is `≤ g i / (d − i)` for every `0 ≤ i < d`. -/
lemma rightSlope_le (d : ℕ) (g : ℕ → ℝ) {i : ℕ} (hid : i < d) :
    rightSlope d g ≤ g i / ((d - i : ℕ) : ℝ) := by
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le i) hid
  have hmem : g i / ((d - i : ℕ) : ℝ) ∈
        (Finset.Icc 0 (d - 1)).image (fun j : ℕ => g j / ((d - j : ℕ) : ℝ)) := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨Nat.zero_le i, by omega⟩, rfl⟩
  simp [rightSlope, hd]
  exact Finset.min'_le ((Finset.Icc 0 (d - 1)).image (fun j : ℕ => g j / ((d - j : ℕ) : ℝ)))
    (g i / ((d - i : ℕ) : ℝ)) hmem

/-- The affine minorant through `(d, 0)`: `a(i) = rightSlope · (d − i)`. -/
def rightAffine (d : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun i => rightSlope d g * ((d : ℝ) - (i : ℝ))

/-- `rightAffine` is a convex minorant of `g` whenever `g d = 0`. -/
lemma rightAffine_mem (d : ℕ) (g : ℕ → ℝ) (hgd : g d = 0) : rightAffine d g ∈ MinorantSet d g := by
  constructor
  · intro i hi
    dsimp [DiscreteConvexOn, dslope, rightAffine]
    simp only [Nat.cast_add, Nat.cast_one]
    ring_nf
    exact le_rfl
  · intro i hi
    by_cases hid : i = d
    · subst i
      dsimp [rightAffine]
      simp [hgd]
    · have hidlt : i < d := lt_of_le_of_ne hi hid
      have hs := rightSlope_le d g hidlt
      have hpos : 0 < ((d - i : ℕ) : ℝ) := by
        exact_mod_cast (Nat.sub_pos_of_lt hidlt)
      dsimp [rightAffine]
      rw [← Nat.cast_sub (le_of_lt hidlt)]
      exact (le_div_iff₀ hpos).mp hs

/-- **Right endpoint**: if the data vanishes at `d` (`g d = 0`), the largest convex
minorant vanishes at `d` too. -/
lemma largestConvexMinorant_zero_right (d : ℕ) (g : ℕ → ℝ) (hgd : g d = 0) :
    largestConvexMinorant d g d = 0 := by
  apply le_antisymm
  · have hle := largestConvexMinorant_le_g d g (i := d) (by omega)
    rwa [hgd] at hle
  · have h := convexMinorant_le_largest d g (rightAffine_mem d g hgd) (i := d) (by omega)
    simpa [rightAffine] using h

/-- **Endpoints of the Grayson polygon**: when the data vanishes at both endpoints
(`g 0 = 0`, `g d = 0` — true for the subgroup data of a unimodular lattice), the largest
convex minorant vanishes at both endpoints, and hence its slopes sum to zero. -/
lemma largestConvexMinorant_ends_zero (d : ℕ) (g : ℕ → ℝ) (hg0 : g 0 = 0) (hgd : g d = 0) :
    largestConvexMinorant d g 0 = 0 ∧ largestConvexMinorant d g d = 0 := by
  constructor
  · exact largestConvexMinorant_zero_left d g hg0
  · exact largestConvexMinorant_zero_right d g hgd
/-- **Slope-total of the Grayson polygon**: when the data vanishes at both endpoints, the
largest convex minorant vanishes there too, so its `d` slopes sum to zero —
`Σ_{i<d} Λ_{i+1} = c(d) − c(0) = 0`, the identity used in Lemma 4 of de Saxcé §3. -/
lemma grayson_slopes_sum_zero (d : ℕ) (g : ℕ → ℝ) (hg0 : g 0 = 0) (hgd : g d = 0) :
    (∑ i ∈ Finset.range d, dslope (largestConvexMinorant d g) i) = 0 := by
  have hends := largestConvexMinorant_ends_zero d g hg0 hgd
  exact sum_slopes_eq_zero_of_ends (c := largestConvexMinorant d g) hends.1 hends.2


/-! ## The slope inner product `⟨u, c⟩` of §3 (Prop 5 / Lemma 4)

The §3 space `a` of real functions on `{0,…,d}` is equipped with the inner product
`⟨u, c⟩ := Σ_{i=0}^{d−1} (u(i+1) − u(i)) · (c(i+1) − c(i))` and the associated norm
`‖c‖² = ⟨c, c⟩` (used in Prop 5's bound `log‖v₁∧…∧v_ℓ‖ ≤ −ℓ(d−ℓ)/d · ⟨ċ_t, c_t⟩ + O(1)`
and in the time-selection step `⟨ċ_t,c_t⟩ = (1/2)(d/dt)‖c_t‖²`).  In the notation of this
module it is the bilinear form on the slope sequences:

    `slopeInner d u c := Σ_{i<d} dslope u i · dslope c i`

(`dslope c i = c(i+1) − c(i)`).  The algebraic Lemma 4 of §3 — `⟨ċ_t, c_t⟩ =
−(1/ℓ+1/(d−ℓ))·Σ_s (ℓ_{s+1}−ℓ_s)·Λ_{j_s+1}` — is exactly
`lemma4_flow`/`lemma4_ends_zero` of `Lemma4Algebra` stated in the form
`Σ_{i<d} dslope u i · dslope c i = …`; the definitions here make that recognition
explicit. -/

/-- The slope inner product `⟨u, c⟩ = Σ_{i<d} (u(i+1)−u(i))·(c(i+1)−c(i))` of §3. -/
def slopeInner (d : ℕ) (u c : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range d, dslope u i * dslope c i

/-- Symmetry of the slope inner product. -/
lemma slopeInner_symm (d : ℕ) (u c : ℕ → ℝ) : slopeInner d u c = slopeInner d c u := by
  unfold slopeInner
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The square norm `‖c‖² = ⟨c, c⟩` equals the sum of squared slopes. -/
lemma slopeInner_self_eq_sum_sq (d : ℕ) (c : ℕ → ℝ) :
    slopeInner d c c = ∑ i ∈ Finset.range d, (dslope c i) ^ 2 := by
  unfold slopeInner
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- `slopeInner` is additive in the first argument (it is a bilinear form on the slope
sequences). -/
lemma slopeInner_add_left (d : ℕ) (u v c : ℕ → ℝ) :
    slopeInner d (fun i => u i + v i) c = slopeInner d u c + slopeInner d v c := by
  unfold slopeInner
  have h : ∀ i ∈ Finset.range d,
      dslope (fun i => u i + v i) i * dslope c i =
        dslope u i * dslope c i + dslope v i * dslope c i := by
    intro i hi
    have hd : dslope (fun i => u i + v i) i = dslope u i + dslope v i := by
      dsimp [dslope]
      ring
    rw [hd]
    ring
  calc
    (∑ i ∈ Finset.range d, dslope (fun i => u i + v i) i * dslope c i)
        = ∑ i ∈ Finset.range d,
            (dslope u i * dslope c i + dslope v i * dslope c i) := by
            apply Finset.sum_congr rfl
            exact h
    _ = (∑ i ∈ Finset.range d, dslope u i * dslope c i) +
        (∑ i ∈ Finset.range d, dslope v i * dslope c i) := by
            rw [Finset.sum_add_distrib]
    _ = slopeInner d u c + slopeInner d v c := by
          unfold slopeInner
          rfl

/-- A discrete-convex function is its own largest convex minorant on `{0,…,d}`: it is a
convex minorant of itself (`DiscreteConvexOn`, `g ≤ g`), and the largest convex minorant
lies below `g`, so the two coincide pointwise on `i ≤ d`. -/
lemma largestConvexMinorant_eq_self_of_convex (d : ℕ) (g : ℕ → ℝ)
    (hg : DiscreteConvexOn g d) {i : ℕ} (hi : i ≤ d) :
    largestConvexMinorant d g i = g i := by
  apply le_antisymm
  · exact largestConvexMinorant_le_g d g hi
  · have hmem : g ∈ MinorantSet d g := ⟨hg, fun j hj => le_rfl⟩
    exact convexMinorant_le_largest d g hmem hi


end Submission.Polygon
