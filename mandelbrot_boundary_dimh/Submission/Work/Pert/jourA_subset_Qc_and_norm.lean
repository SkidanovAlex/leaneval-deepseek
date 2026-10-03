import Mathlib
import Submission.Work.Pert.CoordDefs
import Submission.Work.Pert.Om_arc_subset_Qc

namespace Work.Pert

open MandelDim Complex Set Metric

set_option linter.unusedVariables false

noncomputable section

/-!
# PERT · `Work.Pert.jourA_subset_Qc_and_norm`

`JourA η = Om η ∪ [iη, -η] ∪ [-η, -iη]` (the two discs together with the two chords of the
semicircle through `-η`).  The lemma says that `JourA η ⊆ Qc η ξ₁ α` and that the modulus of
every point of `JourA η` lies between `13η/40` and `3η`.

Route.

* On `Om η` the inclusion is the first conjunct of the proved `Work.Pert.Om_arc_subset_Qc`, and the
  norm bounds are `η - 13η/40 ≤ ‖ζ‖` and `‖ζ‖ ≤ η + 13η/40 = 53η/40 ≤ 3η`.
* A point of the first chord is `ζ = (1-t)·iη + t·(-η)` with `t ∈ [0,1]`, so its real and imaginary
  parts are `-tη` and `(1-t)η`; the second chord is the same with `(t, 1-t)` swapped.  In both cases
  `ζ.re - |ζ.im| = -η` exactly and `‖ζ‖² = (a² + b²)η²` with `a,b ≥ 0`, `a + b = 1`, whence
  `η/√2 ≤ ‖ζ‖ ≤ η`.  Since `13/40 ≤ 1/√2` this gives `13η/40 ≤ ‖ζ‖`, and `‖ζ‖ ≤ η ≤ 3η`.
* The gate membership of the chord points uses the general cone criterion `mem_Qc_of_geom_three`:
  a point `ζ` with `Re ζ - |Im ζ| ≤ -η + (13√2/40)η` and `‖ζ‖ ≤ 3η` lies in `Qc η ξ₁ α`.  This is
  the argument of `Work.Pert.Om_arc_subset_Qc`'s private workhorse repeated with the larger norm
  bound `3η` (needed because `‖ζ‖ ≤ √2 η ≈ 1.414η` on the chords, whereas the earlier version only
  allowed `53η/40 = 1.325η`).  The A-cone estimate has the huge slack `128πη - 2·(3.01η) vs ξ₁`, so
  nothing is lost.
-/

/-! ### Elementary arithmetic -/

private lemma sqrt_two_lt_two : Real.sqrt 2 < (2 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- `13√2/40 + 1/50 < 1/2` (the margin in the upper cone estimate on `Om η`). -/
private lemma thirteen_sqrt_two_div_forty_add : 13 * Real.sqrt 2 / 40 + 1 / 50 < (1 / 2 : ℝ) := by
  have h : Real.sqrt 2 < 96 / 65 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  nlinarith [h]

/-- `13η/40 ≤ η/√2`: the chord distance bound `η/√2` implies the requested lower bound. -/
private lemma thirteen_div_forty_le_div_sqrt_two (η : ℝ) (hη : 0 ≤ η) :
    13 * η / 40 ≤ η / Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [le_div_iff₀ hs]
  have h2 : Real.sqrt 2 < 2 := sqrt_two_lt_two
  nlinarith [hη, h2, hs]

/-! ### Norm bounds on the discs `Om η` -/

/-- Points of `Om η` are within `53η/40 = η + 13η/40` of the origin. -/
private lemma norm_le_of_mem_Om {η : ℝ} (hη : 0 < η) {ζ : ℂ} (h : ζ ∈ Om η) :
    ‖ζ‖ ≤ 53 * η / 40 := by
  rw [Om, Set.mem_union] at h
  have hc : ‖Complex.I * (η : ℂ)‖ = η := by
    rw [norm_mul, Complex.norm_I, one_mul]
    simp [abs_of_pos hη]
  rcases h with h | h
  · rw [Metric.mem_closedBall, dist_eq_norm] at h
    calc ‖ζ‖ = ‖(ζ - Complex.I * (η : ℂ)) + Complex.I * (η : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖ζ - Complex.I * (η : ℂ)‖ + ‖Complex.I * (η : ℂ)‖ := norm_add_le _ _
      _ ≤ 13 * η / 40 + η := by rw [hc]; linarith
      _ = 53 * η / 40 := by ring
  · rw [Metric.mem_closedBall, dist_eq_norm] at h
    have hc' : ‖-(Complex.I * (η : ℂ))‖ = η := by rw [norm_neg, hc]
    calc ‖ζ‖ = ‖(ζ - -(Complex.I * (η : ℂ))) + -(Complex.I * (η : ℂ))‖ := by rw [sub_add_cancel]
      _ ≤ ‖ζ - -(Complex.I * (η : ℂ))‖ + ‖-(Complex.I * (η : ℂ))‖ := norm_add_le _ _
      _ ≤ 13 * η / 40 + η := by rw [hc']; linarith
      _ = 53 * η / 40 := by ring

/-- Points of `Om η` are at distance at least `27η/40 ≥ 13η/40` from the origin. -/
private lemma norm_ge_of_mem_Om {η : ℝ} (hη : 0 < η) {ζ : ℂ} (h : ζ ∈ Om η) :
    13 * η / 40 ≤ ‖ζ‖ := by
  rw [Om, Set.mem_union] at h
  have hc : ‖Complex.I * (η : ℂ)‖ = η := by
    rw [norm_mul, Complex.norm_I, one_mul]
    simp [abs_of_pos hη]
  rcases h with h | h
  · rw [Metric.mem_closedBall, dist_eq_norm] at h
    have h1 : ‖Complex.I * (η : ℂ)‖ ≤ ‖ζ‖ + ‖ζ - Complex.I * (η : ℂ)‖ := by
      have e : ζ - (ζ - Complex.I * (η : ℂ)) = Complex.I * (η : ℂ) := by ring
      calc ‖Complex.I * (η : ℂ)‖ = ‖ζ - (ζ - Complex.I * (η : ℂ))‖ := by rw [e]
        _ ≤ ‖ζ‖ + ‖ζ - Complex.I * (η : ℂ)‖ := norm_sub_le _ _
    rw [hc] at h1
    linarith
  · rw [Metric.mem_closedBall, dist_eq_norm] at h
    have h1 : ‖-(Complex.I * (η : ℂ))‖ ≤ ‖ζ‖ + ‖ζ - -(Complex.I * (η : ℂ))‖ := by
      have e : ζ - (ζ - -(Complex.I * (η : ℂ))) = -(Complex.I * (η : ℂ)) := by ring
      calc ‖-(Complex.I * (η : ℂ))‖ = ‖ζ - (ζ - -(Complex.I * (η : ℂ)))‖ := by rw [e]
        _ ≤ ‖ζ‖ + ‖ζ - -(Complex.I * (η : ℂ))‖ := norm_sub_le _ _
    rw [norm_neg, hc] at h1
    have h2 : ‖ζ - -(Complex.I * (η : ℂ))‖ ≤ 13 * η / 40 := by simpa using h
    linarith

/-! ### The two chords -/

/-- `Re ζ - |Im ζ| = -η` for a point with `Re ζ = -aη` and `|Im ζ| = bη`, `a, b ≥ 0`, `a + b = 1`. -/
private lemma cone_of_re_im {η a b : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {ζ : ℂ} (hre : ζ.re = -a * η) (him : |ζ.im| = b * η) :
    ζ.re - |ζ.im| = -η := by
  rw [hre, him]
  nlinarith [hab]

/-- `‖ζ‖ ≤ η` for a point with `Re ζ = -aη` and `|Im ζ| = bη`, `a, b ≥ 0`, `a + b = 1`. -/
private lemma norm_le_of_re_im {η a b : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {ζ : ℂ} (hre : ζ.re = -a * η) (him : |ζ.im| = b * η) :
    ‖ζ‖ ≤ η := by
  have h2 : ‖ζ‖ ^ 2 = (a ^ 2 + b ^ 2) * η ^ 2 := by
    have him2 : ζ.im ^ 2 = (b * η) ^ 2 := by rw [← sq_abs ζ.im, him]
    rw [Complex.sq_norm, Complex.normSq_apply, hre]
    have : ζ.im * ζ.im = ζ.im ^ 2 := by ring
    rw [this, him2]
    ring
  have hab2 : a ^ 2 + b ^ 2 ≤ 1 := by nlinarith [hab, ha, hb]
  have h3 : ‖ζ‖ ^ 2 ≤ η ^ 2 := by nlinarith [h2, hab2, sq_nonneg η]
  have h4 : |‖ζ‖| ≤ |η| := (sq_le_sq).mp h3
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hη] at h4

/-- `η/√2 ≤ ‖ζ‖` for a point with `Re ζ = -aη` and `|Im ζ| = bη`, `a, b ≥ 0`, `a + b = 1`. -/
private lemma norm_ge_of_re_im {η a b : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {ζ : ℂ} (hre : ζ.re = -a * η) (him : |ζ.im| = b * η) :
    η / Real.sqrt 2 ≤ ‖ζ‖ := by
  have h2 : ‖ζ‖ ^ 2 = (a ^ 2 + b ^ 2) * η ^ 2 := by
    have him2 : ζ.im ^ 2 = (b * η) ^ 2 := by rw [← sq_abs ζ.im, him]
    rw [Complex.sq_norm, Complex.normSq_apply, hre]
    have : ζ.im * ζ.im = ζ.im ^ 2 := by ring
    rw [this, him2]
    ring
  have hhalf : (1 / 2 : ℝ) ≤ a ^ 2 + b ^ 2 := by nlinarith [hab, sq_nonneg (a - b)]
  have hsq : (η / Real.sqrt 2) ^ 2 = η ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h3 : (η / Real.sqrt 2) ^ 2 ≤ ‖ζ‖ ^ 2 := by nlinarith [h2, hhalf, sq_nonneg η, hsq]
  have h4 : |η / Real.sqrt 2| ≤ |‖ζ‖| := (sq_le_sq).mp h3
  have h5 : |η / Real.sqrt 2| = η / Real.sqrt 2 := abs_of_nonneg (by positivity)
  have h6 : |‖ζ‖| = ‖ζ‖ := abs_of_nonneg (norm_nonneg _)
  linarith [h4, h5, h6]

private lemma chord1_re {η t : ℝ} :
    ((1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ))).re = -t * η := by
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- The imaginary part of the first chord point is `(1-t)η ≥ 0`. -/
private lemma chord1_abs_im {η t : ℝ} (hη : 0 ≤ η) (ht : t ≤ 1) :
    |((1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ))).im| = (1 - t) * η := by
  have him : ((1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ))).im = (1 - t) * η := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [him, abs_of_nonneg (mul_nonneg (by linarith) hη)]

private lemma chord2_re {η t : ℝ} :
    ((1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ)))).re = -(1 - t) * η := by
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

/-- The imaginary part of the second chord point is `-tη`, so `|Im| = tη ≥ 0`. -/
private lemma chord2_abs_im {η t : ℝ} (hη : 0 ≤ η) (ht : 0 ≤ t) :
    |((1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ)))).im| = t * η := by
  have him : ((1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ)))).im = -t * η := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [him, abs_mul, abs_neg, abs_of_nonneg hη, abs_of_nonneg ht]

/-! ### The general cone criterion for `Qc` -/

/-- **The gate geometry with the norm bound `3η`.**  A point `ζ` with `‖ζ‖ ≤ 3η` whose cone
quantity satisfies `Re ζ - |Im ζ| ≤ -η + (13√2/40)η` belongs to the safe core `Qc η ξ₁ α`, provided
`η > 0`, `0 < ξ₁`, `2ξ₁ < η`, `η/2 + 2ξ₁ < Re(1/α)` and `2πη‖α‖ ≤ 1/64`.

This is `Work.Pert.Qc_of_geom_noF1`'s workhorse with the (much larger) norm bound `3η` instead of
`53η/40`; the A-cone estimate still has the slack `128π - 2·(3 + 1/100) vs 1/2`. -/
private lemma mem_Qc_of_geom_three {ξ₁ η : ℝ} {α : ℂ} (hη : 0 < η) (hξ₁ : 0 < ξ₁)
    (h2ξ : 2 * ξ₁ < η) (hRe : η / 2 + 2 * ξ₁ < (1 / α).re)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64)
    {ζ : ℂ} (hn : ‖ζ‖ ≤ 3 * η)
    (hc : ζ.re - |ζ.im| ≤ -η + 13 * Real.sqrt 2 / 40 * η) :
    ζ ∈ Qc η ξ₁ α := by
  have hαne : α ≠ 0 := by
    intro h0
    rw [h0] at hRe
    simp at hRe
    linarith
  have hnpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  -- `‖1/α‖ ≥ 128πη`
  have hD : 128 * Real.pi * η ≤ ‖1 / α‖ := by
    rw [norm_div, norm_one, le_div_iff₀ hnpos]
    have e : 128 * Real.pi * η * ‖α‖ = 64 * (2 * Real.pi * ‖α‖ * η) := by ring
    rw [e]
    linarith [hαη]
  have hd : 0 < (1 / α).re := by linarith
  have hsum : ‖1 / α‖ ≤ (1 / α).re + |(1 / α).im| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (1 / α)
    rwa [abs_of_pos hd] at h1
  have hnum : (1 / 2 : ℝ) < 128 * Real.pi - 301 / 50 := by
    have h3 := Real.pi_gt_three
    nlinarith [h3]
  have h8 : ξ₁ < (128 * Real.pi - 301 / 50) * η := by
    have h1 : (1 / 2 : ℝ) * η < (128 * Real.pi - 301 / 50) * η :=
      mul_lt_mul_of_pos_right hnum hη
    have h2 : ξ₁ < η / 2 := by linarith
    linarith
  have h13 := thirteen_sqrt_two_div_forty_add
  have hb : -η + 13 * Real.sqrt 2 / 40 * η + 2 * (η / 100) < -ξ₁ := by
    have hmul : (13 * Real.sqrt 2 / 40 + 1 / 50) * η < (1 / 2 : ℝ) * η :=
      mul_lt_mul_of_pos_right h13 hη
    nlinarith [hmul, h2ξ]
  have hball : ∀ v : ℂ, dist v ζ ≤ η / 100 → v ∈ Qm ξ₁ α := by
    intro v hv
    rw [Qm_mem_iff]
    have hvnorm : ‖v - ζ‖ ≤ η / 100 := by simpa [dist_eq_norm] using hv
    have hvn : ‖v‖ ≤ 301 * η / 100 := by
      calc ‖v‖ = ‖(v - ζ) + ζ‖ := by rw [sub_add_cancel]
        _ ≤ ‖v - ζ‖ + ‖ζ‖ := norm_add_le _ _
        _ ≤ η / 100 + 3 * η := add_le_add hvnorm hn
        _ = 301 * η / 100 := by ring
    have hvr : v.re ≤ ζ.re + η / 100 := by
      have h1 : |(v - ζ).re| ≤ ‖v - ζ‖ := Complex.abs_re_le_norm _
      have h2 : (v - ζ).re = v.re - ζ.re := by simp
      rw [h2] at h1
      have h3 := (abs_le.mp h1).2
      linarith
    have hvi : |ζ.im| - η / 100 ≤ |v.im| := by
      have h1 : |v.im - ζ.im| ≤ ‖v - ζ‖ := by
        have h2 : (v - ζ).im = v.im - ζ.im := by simp
        rw [← h2]; exact Complex.abs_im_le_norm (v - ζ)
      have h3 : |ζ.im| - |v.im| ≤ |ζ.im - v.im| := abs_sub_abs_le_abs_sub ζ.im v.im
      have h4 : |ζ.im - v.im| ≤ η / 100 := by
        rw [abs_sub_comm]; linarith
      linarith
    constructor
    · -- A-cone (lower): `ξ₁ - Re(1/α) - |Im v + Im(1/α)| < Re v`
      have h4 : 128 * Real.pi * η ≤ (1 / α).re + |(1 / α).im| := le_trans hD hsum
      have h5 : |(1 / α).im| - ‖v‖ ≤ |v.im + (1 / α).im| := by
        have h1 := abs_sub_abs_le_abs_sub ((1 / α).im) (-(v.im))
        rw [abs_neg, sub_neg_eq_add, add_comm (1 / α).im v.im] at h1
        have h2 : |v.im| ≤ ‖v‖ := Complex.abs_im_le_norm v
        linarith
      have h6 : -‖v‖ ≤ v.re := by
        have h1 := Complex.abs_re_le_norm v
        have h2 := neg_abs_le v.re
        linarith
      have : ξ₁ < v.re + (1 / α).re + |v.im + (1 / α).im| := by
        nlinarith [h4, h5, h6, hvn, h8]
      linarith
    · -- B-cone (upper): `Re v < |Im v| - ξ₁`
      have h3 : v.re - |v.im| ≤ ζ.re - |ζ.im| + 2 * (η / 100) := by linarith
      have : v.re - |v.im| < -ξ₁ := by linarith
      linarith
  rw [Qc, Set.mem_ofPred_eq]
  exact ⟨hball ζ (by rw [dist_self]; linarith), fun v hv => hball v hv⟩

/-! ### The statement -/

/-- The new journey `JourA η` (defined in `CoordDefs.lean` as `Om η` together with the two chords
from `±iη` to the point `-η` of the real axis) lies in the safe core `Qc η ξ₁ α`, and has modulus
between `13η/40` and `3η`.

ROUTE.  `Om η ⊆ Qc` is exactly the first conjunct of the PROVED `Work.Pert.Om_arc_subset_Qc`; the
norm bounds on `Om` come from `‖w ∓ iη‖ ≤ 13η/40`.  For a chord point
`ζ = (1-t)·(iη) + t·(-η)` (`t ∈ [0,1]`), i.e. `ζ.re = -tη`, `ζ.im = (1-t)η`, one has
`ζ.re - |ζ.im| = -η` exactly, `‖ζ‖ ≤ η` and `‖ζ‖ ≥ η/√2 ≥ 13η/40` (closest point of the chord to
`0`).

WATCH OUT: the private workhorse `mem_Qc_of_geom` of `Om_arc_subset_Qc.lean` requires
`‖ζ‖ ≤ 53η/40`, which is FALSE for the chord points (`√2 ≈ 1.414 > 1.325`).  Repeat its cone
argument with the larger norm bound `‖v‖ ≤ η(1/100 + √2)`; this is harmless because the decisive
`A`-cone estimate has the huge slack `128πη` versus `O(η)` (see `Work.Pert.Qc_of_geom_noF1.lean`
for the same computation with a larger norm bound). -/
theorem jourA_subset_Qc_and_norm {ξ₁ η : ℝ} {α : ℂ} (hη : 0 < η) (hη100 : 100 ≤ η)
    (hξ₁ : 0 < ξ₁) (h2ξ : 2 * ξ₁ < η) (hRe : η / 2 + 2 * ξ₁ < (1 / α).re)
    (hF1 : |α.im| < α.re) (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64) :
    (Work.Pert.JourA η ⊆ Work.Pert.Qc η ξ₁ α) ∧
    (∀ ζ ∈ Work.Pert.JourA η, 13 * η / 40 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 3 * η) := by
  have hη0 : 0 ≤ η := le_of_lt hη
  have hOmQc : ∀ ζ ∈ Om η, ζ ∈ Qc η ξ₁ α :=
    (Om_arc_subset_Qc hη hη100 hξ₁ h2ξ hRe hF1 hαη).1
  -- the uniform statement for a point `ζ` with `ζ.re = -aη`, `ζ.im = bη`, `a + b = 1`, `a,b ≥ 0`
  have hkey : ∀ (a b : ℝ) (ζ : ℂ), 0 ≤ a → 0 ≤ b → a + b = 1 → ζ.re = -a * η →
      |ζ.im| = b * η → ζ ∈ Qc η ξ₁ α ∧ 13 * η / 40 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 3 * η := by
    intro a b ζ ha hb hab hre him
    have hcone : ζ.re - |ζ.im| ≤ -η + 13 * Real.sqrt 2 / 40 * η := by
      rw [cone_of_re_im hη0 ha hb hab hre him]
      have := Real.sqrt_nonneg 2
      nlinarith [hη, this]
    have hnle : ‖ζ‖ ≤ η := norm_le_of_re_im hη0 ha hb hab hre him
    have hnge : η / Real.sqrt 2 ≤ ‖ζ‖ := norm_ge_of_re_im hη0 ha hb hab hre him
    exact ⟨mem_Qc_of_geom_three hη hξ₁ h2ξ hRe hαη (by linarith) hcone,
      le_trans (thirteen_div_forty_le_div_sqrt_two η hη0) hnge, by linarith⟩
  have ch1 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ))) ∈ Qc η ξ₁ α ∧
      (13 * η / 40 ≤ ‖(1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ))‖ ∧
       ‖(1 - t) * (Complex.I * (η : ℂ)) + t * (-(η : ℂ))‖ ≤ 3 * η) := by
    intro t ht
    exact ⟨(hkey t (1 - t) _ (le_trans ht.1 (by linarith)) (by linarith [ht.2]) (by ring)
        (chord1_re (η := η) (t := t)) (chord1_abs_im hη0 ht.2)).1,
      (hkey t (1 - t) _ (le_trans ht.1 (by linarith)) (by linarith [ht.2]) (by ring)
        (chord1_re (η := η) (t := t)) (chord1_abs_im hη0 ht.2)).2⟩
  have ch2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ)))) ∈ Qc η ξ₁ α ∧
      (13 * η / 40 ≤ ‖(1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ)))‖ ∧
       ‖(1 - t) * (-(η : ℂ)) + t * (-(Complex.I * (η : ℂ)))‖ ≤ 3 * η) := by
    intro t ht
    exact ⟨(hkey (1 - t) t _ (by linarith [ht.2]) (le_trans ht.1 (by linarith)) (by ring)
        (chord2_re (η := η) (t := t)) (chord2_abs_im hη0 ht.1)).1,
      (hkey (1 - t) t _ (by linarith [ht.2]) (le_trans ht.1 (by linarith)) (by ring)
        (chord2_re (η := η) (t := t)) (chord2_abs_im hη0 ht.1)).2⟩
  constructor
  · intro ζ hζ
    rw [JourA, Set.mem_union, Set.mem_union] at hζ
    rcases hζ with (hOm | h) | h
    · exact hOmQc ζ hOm
    · obtain ⟨t, ht, rfl⟩ := h
      exact (ch1 t ht).1
    · obtain ⟨t, ht, rfl⟩ := h
      exact (ch2 t ht).1
  · intro ζ hζ
    rw [JourA, Set.mem_union, Set.mem_union] at hζ
    rcases hζ with (hOm | h) | h
    · exact ⟨norm_ge_of_mem_Om hη hOm, by linarith [norm_le_of_mem_Om hη hOm, hη]⟩
    · obtain ⟨t, ht, rfl⟩ := h
      exact (ch1 t ht).2
    · obtain ⟨t, ht, rfl⟩ := h
      exact (ch2 t ht).2

end

end Work.Pert
