import Mathlib
import Submission.ChordModel
import Submission.MobiusModel
import Submission.CirclePairs

noncomputable section

open Complex
open ComplexConjugate

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# The trigonometric chord parametrisation of the circle-pair model

(Second half of the `OpenMobius ≃ MobiusModel` bridge; first half:
`Submission/CirclePairs.lean`.)

An unordered pair `{u, v}` of *distinct* points of the unit circle
`Circle = {z : ℂ | ‖z‖ = 1}` determines its chord — the line through `u`
and `v` — which we describe by the chord data of `ChordModel.lean`:
a unit *normal* `n = I·(v-u)/‖v-u‖` (perpendicular to the chord) and the
signed *offset* `d = ⟪u, n⟫ ∈ (-1,1)` (the distance of the chord from the
origin).  The two orders `(u,v)` and `(v,u)` give the flipped data
`(-n,-d)`, so the map descends to the unordered pair `{u,v}` (a point of
`CircleOpenPairs`/`OpenMobius`) and lands in `MobiusModel = ChordData/flip`.

The inverse map sends chord data `(n, d)` to the unordered pair of the two
unit points `n·(d ± I·√(1-d²))` — the intersection of the chord with the
unit circle (see Mathlib's `normSq_ofReal_add_I_mul_sqrt_one_sub`).

This file develops the *analytic core*:  all algebraic identities needed to
certify the bijection, at the level of chord data and circle points

  `forward : (u v : Circle) (h : u ≠ v) → ChordData`   (mod flip),
  `backward : ChordData → pair of distinct circle points` (mod swap),

including `forward (backward q) = q` exactly and
`backward (forward p) = p` up to the swap.  The topological quotient
descent (continuity of the induced maps between `OpenMobius ≃ CircleOpenPairs`
and `MobiusModel`, using the open-quotient-map machinery of `SecantSpace.lean`
and `MobiusModel.lean`) is layered on top in a later module.
-/

/-! ## Basic complex facts for chord lines -/

/-- `conj z * (z / ‖z‖) = ‖z‖` for `z ≠ 0` (real division coerced). -/
lemma conj_mul_div_norm (z : ℂ) (hz : z ≠ 0) : conj z * (z / ‖z‖) = (‖z‖ : ℂ) := by
  rw [← mul_div_assoc]
  rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_eq_norm_sq]
  have hnz : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  field_simp [hnz]
  norm_cast

/-- `(z / ‖z‖) * conj z = ‖z‖` for `z ≠ 0`. -/
lemma div_norm_mul_conj (z : ℂ) (hz : z ≠ 0) : (z / ‖z‖) * conj z = (‖z‖ : ℂ) := by
  rw [div_mul_eq_mul_div]
  rw [mul_comm z (conj z)]
  rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_eq_norm_sq]
  have hnz : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  field_simp [hnz]
  norm_cast

/-- The raw chord normal `I * (v - u) / ‖v - u‖` of the chord through two
distinct complex points `u ≠ v`. -/
def rawCircleNormal (u v : ℂ) : ℂ := I * ((v - u) / ‖v - u‖)

/-- The raw chord normal is a unit complex number. -/
lemma rawCircleNormal_norm (u v : ℂ) (hvu : v ≠ u) : ‖rawCircleNormal u v‖ = 1 := by
  rw [rawCircleNormal, norm_mul]
  simp
  exact sub_ne_zero.mpr hvu

/-- The chord normal as an element of the unit circle. -/
def circleNormal (u v : ℂ) (hvu : v ≠ u) : Circle :=
  ⟨rawCircleNormal u v, by
    exact mem_sphere_zero_iff_norm.mpr (by simpa [rawCircleNormal] using rawCircleNormal_norm u v hvu)⟩

@[simp]
lemma circleNormal_coe (u v : ℂ) (hvu : v ≠ u) :
    ((circleNormal u v hvu : Circle) : ℂ) = rawCircleNormal u v := rfl

/-- The real inner product on `ℂ` computes as `(z * conj w).re`. -/
lemma inner_complex (w z : ℂ) : inner ℝ w z = (z * conj w).re := by
  rw [Complex.inner]

/-- The chord normal is perpendicular to the chord direction: the real inner
product `⟪v - u, n⟫` vanishes. -/
lemma inner_sub_normal_eq_zero (u v : ℂ) (hvu : v ≠ u) :
    inner ℝ (v - u) (circleNormal u v hvu) = 0 := by
  rw [inner_complex]
  have hz : v - u ≠ 0 := sub_ne_zero.mpr hvu
  have hm : (circleNormal u v hvu : ℂ) * conj (v - u) = I * (‖v - u‖ : ℂ) := by
    rw [circleNormal_coe, rawCircleNormal, mul_assoc]
    rw [div_norm_mul_conj (v - u) hz]
  rw [hm]
  simp

/-- The two endpoints of a chord have the same inner product with the normal
(`⟪v, n⟫ = ⟪u, n⟫`). -/
lemma inner_endpoints_eq (u v : ℂ) (hvu : v ≠ u) :
    inner ℝ v (circleNormal u v hvu) = inner ℝ u (circleNormal u v hvu) := by
  rw [inner_complex v (circleNormal u v hvu)]
  rw [inner_complex u (circleNormal u v hvu)]
  have h := inner_sub_normal_eq_zero u v hvu
  rw [inner_complex] at h
  have hcv : conj (v - u) = conj v - conj u := by simp
  have hm : (circleNormal u v hvu : ℂ) * conj (v - u) =
      (circleNormal u v hvu : ℂ) * conj v - (circleNormal u v hvu : ℂ) * conj u := by
    rw [hcv]
    ring
  rw [hm] at h
  have hsub : ((circleNormal u v hvu : ℂ) * conj v).re -
      ((circleNormal u v hvu : ℂ) * conj u).re = 0 := by
    simpa [Complex.sub_re] using h
  linarith

/-! ## The signed offset of a chord -/

/-- Symmetry of the real part of `z * conj w`: `(z * conj w).re = (w * conj z).re`. -/
lemma re_mul_conj_symm (z w : ℂ) : (z * conj w).re = (w * conj z).re := by
  calc (z * conj w).re = (conj (z * conj w)).re := by rw [Complex.conj_re]
    _ = (conj z * w).re := by
      congr 1
      rw [map_mul, Complex.conj_conj]
    _ = (w * conj z).re := by rw [mul_comm]

/-- The signed offset of the chord `{u,v}`: the inner product of an endpoint
with the normal (`chordOffset u v`). -/
def chordOffset (u v : ℂ) (hvu : v ≠ u) : ℝ := inner ℝ u (circleNormal u v hvu)

/-- The offset equals the real part of `u · conj n`. -/
lemma offset_eq_re_mul_conj (u v : ℂ) (hvu : v ≠ u) :
    chordOffset u v hvu = (u * conj (circleNormal u v hvu : ℂ)).re := by
  unfold chordOffset
  rw [inner_complex]
  exact (re_mul_conj_symm u (circleNormal u v hvu : ℂ)).symm

/-- A unit multiple of a unit complex number has unit modulus. -/
lemma norm_unit_mul_conj_unit (u : ℂ) (hu : ‖u‖ = 1) (n : Circle) :
    ‖u * conj (n : ℂ)‖ = 1 := by
  rw [norm_mul, RCLike.norm_conj, Circle.norm_coe, hu, one_mul]

/-- The chord offset has modulus at most 1 (Cauchy–Schwarz for the endpoint
and the unit normal). -/
lemma abs_chordOffset_le_one (u v : ℂ) (hu : ‖u‖ = 1) (hvu : v ≠ u) :
    |chordOffset u v hvu| ≤ 1 := by
  rw [offset_eq_re_mul_conj]
  calc |(u * conj (circleNormal u v hvu : ℂ)).re|
      ≤ ‖u * conj (circleNormal u v hvu : ℂ)‖ := abs_re_le_norm _
    _ = 1 := norm_unit_mul_conj_unit u hu (circleNormal u v hvu)

/-- If a unit complex number has real part of modulus 1, it is real. -/
lemma unit_imag_eq_zero_of_abs_re_eq_one (t : ℂ) (ht : ‖t‖ = 1)
    (htr : |t.re| = 1) : t.im = 0 := by
  have hre2 : t.re ^ 2 = 1 := by
    rw [(sq_abs t.re).symm, htr]
    norm_num
  have hsq : t.im ^ 2 = 0 := by
    calc t.im ^ 2 = ‖t‖ ^ 2 - t.re ^ 2 := by rw [sq_norm_sub_sq_re]
      _ = 1 - t.re ^ 2 := by rw [ht]; norm_num
      _ = 0 := by rw [hre2]; norm_num
  exact sq_eq_zero_iff.mp hsq

/-- The `v`-analogue of `offset_eq_re_mul_conj`: since both endpoints have
equal inner products with the normal, `v · conj n` has the same real part. -/
lemma offset_eq_re_mul_conj_v (u v : ℂ) (hvu : v ≠ u) :
    chordOffset u v hvu = (v * conj (circleNormal u v hvu : ℂ)).re := by
  rw [offset_eq_re_mul_conj]
  have he : inner ℝ v (circleNormal u v hvu) = inner ℝ u (circleNormal u v hvu) :=
    inner_endpoints_eq u v hvu
  rw [inner_complex, inner_complex] at he
  calc (u * conj (circleNormal u v hvu : ℂ)).re
      = ((circleNormal u v hvu : ℂ) * conj u).re := re_mul_conj_symm u (circleNormal u v hvu : ℂ)
    _ = ((circleNormal u v hvu : ℂ) * conj v).re := he.symm
    _ = (v * conj (circleNormal u v hvu : ℂ)).re :=
      (re_mul_conj_symm v (circleNormal u v hvu : ℂ)).symm

/-- A unit circle element has a nonzero coefficient. -/
lemma circle_coe_ne_zero (n : Circle) : (n : ℂ) ≠ 0 := by
  intro h
  have hn := Circle.norm_coe n
  rw [h] at hn
  norm_num at hn

/-- `conj n · n = 1` for a unit complex `n`. -/
lemma conj_mul_self_one (n : Circle) : conj (n : ℂ) * (n : ℂ) = (1 : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self]
  norm_num [Complex.normSq_eq_norm_sq, Circle.norm_coe]

/-- If both endpoints are distinct unit points, the offset is not ±1. -/
lemma chordOffset_abs_ne_one (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : u ≠ v) : |chordOffset u v (Ne.symm huv)| ≠ 1 := by
  intro habs
  let n : Circle := circleNormal u v (Ne.symm huv)
  have htu_im : (u * conj (n : ℂ)).im = 0 := by
    apply unit_imag_eq_zero_of_abs_re_eq_one (u * conj (n : ℂ))
    · exact norm_unit_mul_conj_unit u hu n
    · rwa [← offset_eq_re_mul_conj u v (Ne.symm huv)]
  have htv_im : (v * conj (n : ℂ)).im = 0 := by
    apply unit_imag_eq_zero_of_abs_re_eq_one (v * conj (n : ℂ))
    · exact norm_unit_mul_conj_unit v hv n
    · rwa [← offset_eq_re_mul_conj_v u v (Ne.symm huv)]
  have htu : u * conj (n : ℂ) = (chordOffset u v (Ne.symm huv) : ℂ) := by
    apply Complex.ext
    · change (u * conj (n : ℂ)).re = chordOffset u v (Ne.symm huv)
      exact (offset_eq_re_mul_conj u v (Ne.symm huv)).symm
    · change (u * conj (n : ℂ)).im = 0
      exact htu_im
  have htv : v * conj (n : ℂ) = (chordOffset u v (Ne.symm huv) : ℂ) := by
    apply Complex.ext
    · change (v * conj (n : ℂ)).re = chordOffset u v (Ne.symm huv)
      exact (offset_eq_re_mul_conj_v u v (Ne.symm huv)).symm
    · change (v * conj (n : ℂ)).im = 0
      exact htv_im
  have hmult : (u * conj (n : ℂ)) * (n : ℂ) = (v * conj (n : ℂ)) * (n : ℂ) := by
    rw [htu, htv]
  rw [mul_assoc, mul_assoc] at hmult
  rw [conj_mul_self_one] at hmult
  norm_num at hmult
  exact huv hmult

/-! ## Forward: chord data of an ordered pair of distinct circle points -/

/-- Coercions of distinct circle elements are distinct complex numbers. -/
lemma coe_ne_of_ne {u v : Circle} (h : u ≠ v) : (u : ℂ) ≠ (v : ℂ) := by
  intro hc
  apply h
  exact Circle.coe_injective hc

/-- The swapped-order variant of `coe_ne_of_ne`. -/
lemma ne_symm_of_ne {u v : Circle} (h : u ≠ v) : (v : ℂ) ≠ (u : ℂ) := by
  intro hc
  apply h
  exact Circle.coe_injective hc.symm

/-- The signed offset of the chord through two distinct circle points. -/
def circleChordOffset (u v : Circle) (h : u ≠ v) : ℝ :=
  chordOffset (u : ℂ) (v : ℂ) (ne_symm_of_ne h)

/-- The offset of a chord through two distinct unit points is strictly
between `-1` and `1`. -/
lemma abs_circleChordOffset_lt_one (u v : Circle) (h : u ≠ v) :
    |circleChordOffset u v h| < 1 := by
  have hle : |circleChordOffset u v h| ≤ 1 := by
    exact abs_chordOffset_le_one (u : ℂ) (v : ℂ) (Circle.norm_coe u) (ne_symm_of_ne h)
  have hne : |circleChordOffset u v h| ≠ 1 := by
    exact chordOffset_abs_ne_one (u : ℂ) (v : ℂ) (Circle.norm_coe u) (Circle.norm_coe v)
      (coe_ne_of_ne h)
  exact lt_of_le_of_ne hle hne

/-- The offset lies in the open interval `(-1,1)` (the chord genuinely cuts
the disk). -/
lemma circleChordOffset_mem (u v : Circle) (h : u ≠ v) :
    circleChordOffset u v h ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (abs_circleChordOffset_lt_one u v h)

/-- **Forward**: chord data of the ordered pair `(u,v)` of distinct circle
points: unit normal `circleNormal` and offset in `(-1,1)`. -/
def chordDataOf (u v : Circle) (h : u ≠ v) : ChordData :=
  ⟨(circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h), circleChordOffset u v h),
    circleChordOffset_mem u v h⟩

/-- Swapping the two endpoints negates the raw normal. -/
lemma rawCircleNormal_swap (u v : ℂ) (_hvu : v ≠ u) (_huv : u ≠ v) :
    rawCircleNormal v u = - rawCircleNormal u v := by
  unfold rawCircleNormal
  have hnorm : ‖u - v‖ = ‖v - u‖ := by rw [norm_sub_rev]
  rw [hnorm]
  rw [show u - v = -(v - u) by ring]
  ring_nf

/-- Swapping the two endpoints negates the normal. -/
lemma circleNormal_swap (u v : ℂ) (hvu : v ≠ u) (huv : u ≠ v) :
    circleNormal v u huv = - circleNormal u v hvu := by
  apply Subtype.ext
  change rawCircleNormal v u = - rawCircleNormal u v
  exact rawCircleNormal_swap u v hvu huv

/-- Swapping the two endpoints negates the offset. -/
lemma chordOffset_swap (u v : ℂ) (hvu : v ≠ u) (huv : u ≠ v) :
    chordOffset v u huv = - chordOffset u v hvu := by
  unfold chordOffset
  have hneg : (circleNormal v u huv : ℂ) = - (circleNormal u v hvu : ℂ) := by
    rw [circleNormal_swap u v hvu huv]
    simp
  rw [hneg, inner_neg_right]
  have he : inner ℝ v (circleNormal u v hvu) = inner ℝ u (circleNormal u v hvu) :=
    inner_endpoints_eq u v hvu
  rw [he]

/-- The offset of a circle pair is flip-antisymmetric. -/
lemma circleChordOffset_swap (u v : Circle) (h : u ≠ v) :
    circleChordOffset v u (Ne.symm h) = - circleChordOffset u v h := by
  unfold circleChordOffset
  exact chordOffset_swap (u : ℂ) (v : ℂ) (ne_symm_of_ne h) (coe_ne_of_ne h)

/-- Swapping the endpoints of an ordered pair flips the chord data (the two
descriptions of the same chord). -/
lemma chordDataOf_swap (u v : Circle) (h : u ≠ v) :
    chordDataOf v u (Ne.symm h) = chordFlip (chordDataOf u v h) := by
  apply Subtype.ext
  ext
  · simp [chordDataOf, chordFlip, chordDataFlip]
    exact rawCircleNormal_swap (u : ℂ) (v : ℂ) (ne_symm_of_ne h) (coe_ne_of_ne h)
  · simp [chordDataOf, chordFlip, chordDataFlip, circleChordOffset_swap u v h]

/-! ## Backward: the chord endpoints from chord data -/

/-- `√(1-d²)`, the (nonnegative) half-spread used to recover the endpoints
of a chord from its data. -/
def chordHalfSpread (d : ℝ) : ℝ := Real.sqrt (1 - d ^ 2)

/-- An element of the unit circle from a unit complex number. -/
def unitCircleOf (z : ℂ) (hz : ‖z‖ = 1) : Circle :=
  ⟨z, mem_sphere_zero_iff_norm.mpr (by simpa using hz)⟩

@[simp]
lemma unitCircleOf_coe (z : ℂ) (hz : ‖z‖ = 1) : (unitCircleOf z hz : ℂ) = z := rfl

/-- `‖d + I·√(1-d²)‖ = 1` for `|d| ≤ 1` (Mathlib:
`normSq_ofReal_add_I_mul_sqrt_one_sub`). -/
lemma norm_add_I_mul_sqrt_one_sub (d : ℝ) (hd : |d| ≤ 1) :
    ‖(d : ℂ) + I * Real.sqrt (1 - d ^ 2)‖ = 1 := by
  have hns : Complex.normSq ((d : ℂ) + I * Real.sqrt (1 - d ^ 2)) = 1 := by
    apply normSq_ofReal_add_I_mul_sqrt_one_sub
    rwa [Real.norm_eq_abs]
  have hn2 : ‖(d : ℂ) + I * Real.sqrt (1 - d ^ 2)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hns
  have hnn : 0 ≤ ‖(d : ℂ) + I * Real.sqrt (1 - d ^ 2)‖ := norm_nonneg _
  rcases (sq_eq_sq_iff_eq_or_eq_neg (a := ‖(d : ℂ) + I * Real.sqrt (1 - d ^ 2)‖) (b := 1)).mp
      (by simpa using hn2) with h | h
  · exact h
  · linarith

/-- The analogous norm fact for the `-` sign. -/
lemma norm_sub_I_mul_sqrt_one_sub (d : ℝ) (hd : |d| ≤ 1) :
    ‖(d : ℂ) - I * Real.sqrt (1 - d ^ 2)‖ = 1 := by
  have hns : Complex.normSq ((d : ℂ) - I * Real.sqrt (1 - d ^ 2)) = 1 := by
    simpa using (normSq_ofReal_sub_I_mul_sqrt_one_sub (x := d) (by rwa [Real.norm_eq_abs]))
  have hn2 : ‖(d : ℂ) - I * Real.sqrt (1 - d ^ 2)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hns
  have hnn : 0 ≤ ‖(d : ℂ) - I * Real.sqrt (1 - d ^ 2)‖ := norm_nonneg _
  rcases (sq_eq_sq_iff_eq_or_eq_neg (a := ‖(d : ℂ) - I * Real.sqrt (1 - d ^ 2)‖) (b := 1)).mp
      (by simpa using hn2) with h | h
  · exact h
  · linarith

/-- The `+` chord endpoint `n·(d + I·√(1-d²))` (a unit point). -/
def chordEndpointPlus (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1) : Circle :=
  unitCircleOf ((n : ℂ) * ((d : ℂ) + I * Real.sqrt (1 - d ^ 2))) (by
    rw [norm_mul, Circle.norm_coe, one_mul]
    exact norm_add_I_mul_sqrt_one_sub d (le_of_lt (abs_lt.mpr hd)))

/-- The `-` chord endpoint `n·(d - I·√(1-d²))` (a unit point). -/
def chordEndpointMinus (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1) : Circle :=
  unitCircleOf ((n : ℂ) * ((d : ℂ) - I * Real.sqrt (1 - d ^ 2))) (by
    rw [norm_mul, Circle.norm_coe, one_mul]
    exact norm_sub_I_mul_sqrt_one_sub d (le_of_lt (abs_lt.mpr hd)))

/-- For `d ∈ (-1,1)` the half-spread is positive. -/
lemma chordHalfSpread_pos (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1) : 0 < chordHalfSpread d := by
  unfold chordHalfSpread
  exact Real.sqrt_pos.mpr (by nlinarith [hd.1, hd.2])

/-- The two endpoints of a nondegenerate chord data are distinct unit
points. -/
lemma chordEndpoint_plus_ne_minus (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1) :
    chordEndpointPlus n d hd ≠ chordEndpointMinus n d hd := by
  intro h
  have hc : (n : ℂ) * ((d : ℂ) + I * Real.sqrt (1 - d ^ 2)) =
      (n : ℂ) * ((d : ℂ) - I * Real.sqrt (1 - d ^ 2)) := by
    exact congrArg (fun x : Circle => (x : ℂ)) h
  have hnz : (n : ℂ) ≠ 0 := circle_coe_ne_zero n
  have hdiff : (d : ℂ) + I * Real.sqrt (1 - d ^ 2) = (d : ℂ) - I * Real.sqrt (1 - d ^ 2) :=
    mul_left_cancel₀ hnz hc
  have him := congrArg Complex.im hdiff
  simp at him
  have hs : Real.sqrt (1 - d ^ 2) ≠ 0 := ne_of_gt (chordHalfSpread_pos d hd)
  exact hs (by linarith)

/-- **Backward**: from chord data `(n,d)` the ordered pair of the two chord
endpoints (distinct circle points). -/
def backwardOrdered (q : ChordData) : {p : Circle × Circle // p.1 ≠ p.2} :=
  ⟨(chordEndpointPlus q.1.1 q.1.2 q.2, chordEndpointMinus q.1.1 q.1.2 q.2),
    chordEndpoint_plus_ne_minus q.1.1 q.1.2 q.2⟩

/-! ## Recovering the endpoints from the chord data -/

/-- `Re(w · conj n) = inner w n` for unit `n` (uses `re_mul_conj_symm`). -/
lemma re_mul_conj_eq_inner (w : ℂ) (n : Circle) :
    (w * conj (n : ℂ)).re = inner ℝ w (n : ℂ) := by
  rw [inner_complex]
  exact re_mul_conj_symm w (n : ℂ)

/-- A unit point `w` with `⟪w, n⟫ = d` is one of the two chord endpoints of
the chord data `(n, d)`.  (The heart of the recovery identity.) -/
lemma unit_endpoint_of_inner_eq (w : Circle) (n : Circle) (d : ℝ)
    (hd : d ∈ Set.Ioo (-1) 1) (hin : inner ℝ (w : ℂ) (n : ℂ) = d) :
    w = chordEndpointPlus n d hd ∨ w = chordEndpointMinus n d hd := by
  let t : ℂ := (w : ℂ) * conj (n : ℂ)
  have ht_norm : ‖t‖ = 1 := norm_unit_mul_conj_unit (w : ℂ) (Circle.norm_coe w) n
  have ht_re : t.re = d := by
    change ((w : ℂ) * conj (n : ℂ)).re = d
    rw [re_mul_conj_eq_inner]
    exact hin
  have ht_im_sq : t.im ^ 2 = (chordHalfSpread d) ^ 2 := by
    have h1 : t.im ^ 2 = ‖t‖ ^ 2 - t.re ^ 2 := by rw [sq_norm_sub_sq_re]
    calc t.im ^ 2 = ‖t‖ ^ 2 - t.re ^ 2 := h1
      _ = 1 - d ^ 2 := by rw [ht_norm, ht_re]; norm_num
      _ = (chordHalfSpread d) ^ 2 := by
        unfold chordHalfSpread
        rw [Real.sq_sqrt]
        nlinarith [hd.1, hd.2]
  have ht_im : t.im = chordHalfSpread d ∨ t.im = - chordHalfSpread d := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp ht_im_sq
  have htw : (w : ℂ) = t * (n : ℂ) := by
    change (w : ℂ) = ((w : ℂ) * conj (n : ℂ)) * (n : ℂ)
    rw [mul_assoc, conj_mul_self_one, mul_one]
  rcases ht_im with him | him
  · left
    -- t = (d : ℂ) + I * s, so w = n(d + I s) = chordEndpointPlus
    have ht_f : t = (d : ℂ) + I * (chordHalfSpread d : ℂ) := by
      apply Complex.ext
      · simp [ht_re]
      · simp [him]
    have hw' : (w : ℂ) = (n : ℂ) * ((d : ℂ) + I * (chordHalfSpread d : ℂ)) := by
      rw [htw, ht_f]
      ring
    apply Circle.ext
    simpa [chordEndpointPlus, unitCircleOf, chordHalfSpread] using hw'
  · right
    have ht_f : t = (d : ℂ) - I * (chordHalfSpread d : ℂ) := by
      apply Complex.ext
      · simp [ht_re]
      · simp [him]
    have hw' : (w : ℂ) = (n : ℂ) * ((d : ℂ) - I * (chordHalfSpread d : ℂ)) := by
      rw [htw, ht_f]
      ring
    apply Circle.ext
    simpa [chordEndpointMinus, unitCircleOf, chordHalfSpread] using hw'

/-- The recovered chord data of `chordDataOf u v h` (the `v`-endpoint also
lies on the chord). -/
lemma inner_v_chordData (u v : Circle) (h : u ≠ v) :
    inner ℝ (v : ℂ) (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h)) =
      circleChordOffset u v h := by
  unfold circleChordOffset chordOffset
  exact inner_endpoints_eq (u : ℂ) (v : ℂ) (ne_symm_of_ne h)

/-- **Recovery identity (A)**: the chord data computed from the pair
`(u,v)` recover the pair `{u,v}` as an unordered pair (up to the swap). -/
lemma backwardOrdered_of_chordDataOf_rel (u v : Circle) (h : u ≠ v) :
    circleSwapRel (backwardOrdered (chordDataOf u v h)).1 (u, v) := by
  change circleSwapRel
    (chordEndpointPlus (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
        (circleChordOffset u v h) (circleChordOffset_mem u v h),
      chordEndpointMinus (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
        (circleChordOffset u v h) (circleChordOffset_mem u v h))
    (u, v)
  have hu : u = chordEndpointPlus (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
        (circleChordOffset u v h) (circleChordOffset_mem u v h) ∨
      u = chordEndpointMinus (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
        (circleChordOffset u v h) (circleChordOffset_mem u v h) := by
    apply unit_endpoint_of_inner_eq u (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
      (circleChordOffset u v h) (circleChordOffset_mem u v h)
    rfl
  have hv : v = chordEndpointPlus (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
        (circleChordOffset u v h) (circleChordOffset_mem u v h) ∨
      v = chordEndpointMinus (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
        (circleChordOffset u v h) (circleChordOffset_mem u v h) := by
    apply unit_endpoint_of_inner_eq v (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
      (circleChordOffset u v h) (circleChordOffset_mem u v h)
    exact inner_v_chordData u v h
  have hp_ne_m : chordEndpointPlus (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
        (circleChordOffset u v h) (circleChordOffset_mem u v h) ≠
      chordEndpointMinus (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
        (circleChordOffset u v h) (circleChordOffset_mem u v h) :=
    chordEndpoint_plus_ne_minus (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h))
      (circleChordOffset u v h) (circleChordOffset_mem u v h)
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exfalso
    apply h
    exact hu.trans hv.symm
  · left
    ext <;> simp [hu.symm, hv.symm]
  · right
    ext <;> simp [circleSwap, hu.symm, hv.symm]
  · exfalso
    apply h
    exact hu.trans hv.symm

/-! ## Identity (B): `forward (backward q) = q` -/

/-- For `d ∈ (-1,1)` with `s = √(1-d²)`, the two ordered endpoints of the
chord data are `n·(d - I s)` and `n·(d + I s)`, and `I` times their
difference is `2s·n`. -/
lemma backward_I_mul_sub (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1) :
    I * ((chordEndpointMinus n d hd : ℂ) - (chordEndpointPlus n d hd : ℂ)) =
      (2 * chordHalfSpread d : ℂ) * (n : ℂ) := by
  have hX : ((chordEndpointPlus n d hd : ℂ)) = (n : ℂ) * ((d : ℂ) + I * (chordHalfSpread d : ℂ)) := by
    simp [chordEndpointPlus, unitCircleOf, chordHalfSpread]
  have hY : ((chordEndpointMinus n d hd : ℂ)) = (n : ℂ) * ((d : ℂ) - I * (chordHalfSpread d : ℂ)) := by
    simp [chordEndpointMinus, unitCircleOf, chordHalfSpread]
  have hdiffs : (d : ℂ) - I * (chordHalfSpread d : ℂ) - ((d : ℂ) + I * (chordHalfSpread d : ℂ)) =
      -2 * (I * (chordHalfSpread d : ℂ)) := by ring
  have hIs : I * (-2 * (I * (chordHalfSpread d : ℂ))) = 2 * (chordHalfSpread d : ℂ) := by
    rw [show I * (-2 * (I * (chordHalfSpread d : ℂ))) =
        -2 * (I * I) * (chordHalfSpread d : ℂ) by ring]
    rw [Complex.I_mul_I]
    ring
  rw [hX, hY]
  calc I * ((n : ℂ) * ((d : ℂ) - I * (chordHalfSpread d : ℂ)) -
        (n : ℂ) * ((d : ℂ) + I * (chordHalfSpread d : ℂ)))
      = (n : ℂ) * (I * (((d : ℂ) - I * (chordHalfSpread d : ℂ)) -
        ((d : ℂ) + I * (chordHalfSpread d : ℂ)))) := by ring
    _ = (n : ℂ) * (I * (-2 * (I * (chordHalfSpread d : ℂ)))) := by rw [hdiffs]
    _ = (n : ℂ) * (2 * (chordHalfSpread d : ℂ)) := by rw [hIs]
    _ = (2 * chordHalfSpread d : ℂ) * (n : ℂ) := by ring

/-- The norm of the endpoint difference is `2s` (positive). -/
lemma norm_backward_sub (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1) :
    ‖(chordEndpointMinus n d hd : ℂ) - (chordEndpointPlus n d hd : ℂ)‖ =
      2 * chordHalfSpread d := by
  have hs_pos : 0 < chordHalfSpread d := chordHalfSpread_pos d hd
  have h1 := backward_I_mul_sub n d hd
  have hnorm_rhs : ‖(2 * chordHalfSpread d : ℂ) * (n : ℂ)‖ = 2 * chordHalfSpread d := by
    calc ‖(2 * chordHalfSpread d : ℂ) * (n : ℂ)‖
        = ‖(2 * chordHalfSpread d : ℂ)‖ * ‖(n : ℂ)‖ := norm_mul _ _
      _ = ‖(2 * chordHalfSpread d : ℂ)‖ := by rw [Circle.norm_coe, mul_one]
      _ = 2 * chordHalfSpread d := by
          rw [norm_mul]
          simp only [norm_real, Real.norm_eq_abs]
          rw [abs_of_nonneg (le_of_lt hs_pos)]
          norm_num
  calc ‖(chordEndpointMinus n d hd : ℂ) - (chordEndpointPlus n d hd : ℂ)‖
      = ‖I * ((chordEndpointMinus n d hd : ℂ) - (chordEndpointPlus n d hd : ℂ))‖ := by
        rw [norm_mul, norm_I, one_mul]
    _ = ‖(2 * chordHalfSpread d : ℂ) * (n : ℂ)‖ := by rw [h1]
    _ = 2 * chordHalfSpread d := hnorm_rhs

/-- The raw normal computed from the two endpoints of chord data `(n,d)` is
`n` again. -/
lemma rawCircleNormal_endpoints (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1) :
    rawCircleNormal (chordEndpointPlus n d hd : ℂ) (chordEndpointMinus n d hd : ℂ) =
      (n : ℂ) := by
  have hsub := backward_I_mul_sub n d hd
  have hnorm : ‖(chordEndpointMinus n d hd : ℂ) - (chordEndpointPlus n d hd : ℂ)‖ ≠ 0 := by
    have hpos : 0 < 2 * chordHalfSpread d := mul_pos (by norm_num) (chordHalfSpread_pos d hd)
    rw [norm_backward_sub n d hd]
    exact ne_of_gt hpos
  unfold rawCircleNormal
  rw [← mul_div_assoc]
  rw [hsub]
  rw [norm_backward_sub n d hd]
  have hnz : ((2 * chordHalfSpread d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (mul_pos (by norm_num) (chordHalfSpread_pos d hd)))
  field_simp [hnz]
  norm_num

/-- The normal of the endpoints is the original normal (as circle elements). -/
lemma circleNormal_endpoints (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1) :
    circleNormal (chordEndpointPlus n d hd : ℂ) (chordEndpointMinus n d hd : ℂ)
      (ne_symm_of_ne (chordEndpoint_plus_ne_minus n d hd)) = n := by
  apply Subtype.ext
  change rawCircleNormal (chordEndpointPlus n d hd : ℂ) (chordEndpointMinus n d hd : ℂ) =
    (n : ℂ)
  exact rawCircleNormal_endpoints n d hd

/-- The inner product of the `+` endpoint with the normal is `d`. -/
lemma inner_endpoint_plus_normal (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1) :
    inner ℝ (chordEndpointPlus n d hd : ℂ) (n : ℂ) = d := by
  have hX : ((chordEndpointPlus n d hd : ℂ)) = (n : ℂ) * ((d : ℂ) + I * (chordHalfSpread d : ℂ)) := by
    simp [chordEndpointPlus, unitCircleOf, chordHalfSpread]
  rw [hX, inner_complex]
  have hn : (n : ℂ) * conj (n : ℂ) = (1 : ℂ) := by rw [mul_comm, conj_mul_self_one]
  rw [map_mul]
  rw [← mul_assoc, hn, one_mul]
  -- Re (conj ((d : ℂ) + I*s)) = d
  have hc : conj ((d : ℂ) + I * (chordHalfSpread d : ℂ)) = (d : ℂ) - I * (chordHalfSpread d : ℂ) := by
    simp
    ring
  rw [hc]
  simp

/-- **Identity (B)**: forward of the backward pair is the identity on chord
data. -/
lemma chordDataOf_backwardOrdered (q : ChordData) :
    chordDataOf (backwardOrdered q).1.1 (backwardOrdered q).1.2 (backwardOrdered q).2 = q := by
  rcases q with ⟨p, hp⟩
  rcases p with ⟨n, d⟩
  change chordDataOf (chordEndpointPlus n d hp) (chordEndpointMinus n d hp)
      (chordEndpoint_plus_ne_minus n d hp) = (⟨(n, d), hp⟩ : ChordData)
  apply Subtype.ext
  change ((circleNormal (chordEndpointPlus n d hp : ℂ) (chordEndpointMinus n d hp : ℂ)
        (ne_symm_of_ne (chordEndpoint_plus_ne_minus n d hp)),
      circleChordOffset (chordEndpointPlus n d hp) (chordEndpointMinus n d hp)
        (chordEndpoint_plus_ne_minus n d hp)) : RawChordData) = ((n, d) : RawChordData)
  refine Prod.ext ?_ ?_
  · exact circleNormal_endpoints n d hp
  · unfold circleChordOffset chordOffset
    rw [circleNormal_endpoints n d hp]
    exact inner_endpoint_plus_normal n d hp

/-- The half-spread is even in the offset: `√(1-(-d)²) = √(1-d²)`. -/
lemma chordHalfSpread_neg (d : ℝ) : chordHalfSpread (-d) = chordHalfSpread d := by
  unfold chordHalfSpread
  congr 1
  ring

/-- Negating the chord data swaps the endpoints: the `+`-endpoint of `(n,d)`
is the `-`-endpoint of `(-n,-d)`. -/
lemma chordEndpointMinus_neg (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1)
    (hd' : -d ∈ Set.Ioo (-1) 1) :
    chordEndpointPlus n d hd = chordEndpointMinus (-n) (-d) hd' := by
  apply Circle.ext
  simp [chordEndpointMinus, chordEndpointPlus, unitCircleOf]
  ring

/-- Negating the chord data swaps the endpoints: the `-`-endpoint of `(n,d)`
is the `+`-endpoint of `(-n,-d)`. -/
lemma chordEndpointPlus_neg (n : Circle) (d : ℝ) (hd : d ∈ Set.Ioo (-1) 1)
    (hd' : -d ∈ Set.Ioo (-1) 1) :
    chordEndpointMinus n d hd = chordEndpointPlus (-n) (-d) hd' := by
  apply Circle.ext
  simp [chordEndpointMinus, chordEndpointPlus, unitCircleOf]
  ring

/-- The backward pair of flipped chord data is the swapped backward pair
(the two endpoint orders of the same chord). -/
lemma backwardOrdered_flip_rel (q : ChordData) :
    circleSwapRel (backwardOrdered (chordFlip q)).1 (backwardOrdered q).1 := by
  rcases q with ⟨p, hp⟩
  rcases p with ⟨n, d⟩
  simp only [backwardOrdered, chordFlip, chordDataFlip]
  right
  change (chordEndpointMinus (-n) (-d) (chordFlip ⟨(n, d), hp⟩).property,
        chordEndpointPlus (-n) (-d) (chordFlip ⟨(n, d), hp⟩).property) =
      (chordEndpointPlus n d hp, chordEndpointMinus n d hp)
  refine Prod.ext ?_ ?_
  · exact (chordEndpointMinus_neg n d hp (chordFlip ⟨(n, d), hp⟩).property).symm
  · exact (chordEndpointPlus_neg n d hp (chordFlip ⟨(n, d), hp⟩).property).symm
