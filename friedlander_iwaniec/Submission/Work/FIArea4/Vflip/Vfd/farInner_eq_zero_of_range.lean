import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs

/-!
# Vanishing of the far `(m,c,Q)`-pieces outside the `q'`-range (FI §12)

The flipped-modulus form of the far part of the variance is split into `(m,c,Q₁,Q₂)`-pieces
`farInner D R S a b α m c Q₁ Q₂`, where the flipped modulus `q'` runs over the interval
`Q₁ < q' ≤ Q₂`.  Friedlander–Iwaniec observe that only the `q'` in the dyadic window

`2SR / (5 H c D) ≤ q' ≤ 8RS / (c D)`

can contribute: outside this window the smooth weight `bump (|x|·y) · nearCut a b x` vanishes
identically on the piece, so the piece is `0`.

This file records that vanishing: the companion `(m,c,Q)`-pieces whose range condition
`Q₂·(5H c D) ≤ 2SR` or `8RS ≤ Q₁ c D` holds are empty of support.

The two key elementary inputs (`bump` nonzero forces `1/2 < y < 5/2`, `nearCut` nonzero forces
`|x| > a/2`) are proved here, so the module is self-contained.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary support facts for the two smooth cutoffs -/

lemma farRange_smoothTransition_pos_of_ne_zero {x : ℝ} (h : Real.smoothTransition x ≠ 0) :
    0 < x := by
  by_contra hx
  exact h (Real.smoothTransition.zero_of_nonpos (not_lt.mp hx))

lemma farRange_bump_ne_zero_bounds {y : ℝ} (h : Work.FIArea4.Vflip.bump y ≠ 0) :
    1 / 2 < y ∧ y < 5 / 2 := by
  rw [Work.FIArea4.Vflip.bump] at h
  have h1 : Real.smoothTransition (2 * y - 1) ≠ 0 := fun hh => h (by rw [hh, zero_mul])
  have h2 : Real.smoothTransition (5 - 2 * y) ≠ 0 := fun hh => h (by rw [hh, mul_zero])
  have h1' := farRange_smoothTransition_pos_of_ne_zero h1
  have h2' := farRange_smoothTransition_pos_of_ne_zero h2
  constructor <;> linarith

lemma farRange_nearCut_ne_zero_abs_lower {a b x : ℝ} (ha : 0 < a)
    (h : Work.FIArea4.Vflip.nearCut a b x ≠ 0) : a / 2 < |x| := by
  rw [Work.FIArea4.Vflip.nearCut] at h
  have h1 : Real.smoothTransition ((4 * x ^ 2 - a ^ 2) / a ^ 2) ≠ 0 :=
    fun hh => h (by rw [hh, zero_mul])
  have h1' := farRange_smoothTransition_pos_of_ne_zero h1
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have h4 : (0 : ℝ) < 4 * x ^ 2 - a ^ 2 := (div_pos_iff_of_pos_right ha2).mp h1'
  by_contra hle
  have hx2 : x ^ 2 ≤ (a / 2) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) (not_lt.mp hle) 2
    rwa [sq_abs] at h
  nlinarith

/-! ## The separation arguments of an index -/

lemma farRange_xOrig_unfold (c q r1 s1 r2 s2 : ℕ) :
    xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩
      = (s1 : ℝ) / ((c : ℝ) * (r1 : ℝ)) - (s2 : ℝ) / ((c : ℝ) * (r2 : ℝ)) := by
  simp only [xOrig, Work.FIArea4.Vflip.xPair]
  push_cast
  ring

lemma farRange_ySep_unfold (c D q r1 s1 r2 s2 : ℕ) :
    ySep c D ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩
      = (c : ℝ) * (r1 : ℝ) * (r2 : ℝ) / ((q : ℝ) * (D : ℝ)) := by
  simp only [ySep]

lemma farRange_xOrig_eq_div (c q r1 s1 r2 s2 : ℕ) (hc : 0 < c) (h1 : 0 < r1) (h2 : 0 < r2) :
    xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩
      = ((s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)) / ((c : ℝ) * (r1 : ℝ) * (r2 : ℝ)) := by
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have h1' : (0 : ℝ) < (r1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < (r2 : ℝ) := by exact_mod_cast h2
  rw [farRange_xOrig_unfold]
  field_simp

lemma farRange_abs_xOrig_eq (c q r1 s1 r2 s2 : ℕ) (hc : 0 < c) (h1 : 0 < r1) (h2 : 0 < r2) :
    |xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩|
      = |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)| / ((c : ℝ) * (r1 : ℝ) * (r2 : ℝ)) := by
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have h1' : (0 : ℝ) < (r1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < (r2 : ℝ) := by exact_mod_cast h2
  rw [farRange_xOrig_eq_div c q r1 s1 r2 s2 hc h1 h2, abs_div]
  rw [abs_of_pos (show (0 : ℝ) < (c : ℝ) * (r1 : ℝ) * (r2 : ℝ) by positivity)]

lemma farRange_abs_xOrig_mul_ySep_eq (c D q r1 s1 r2 s2 : ℕ) (hc : 0 < c) (hq : 0 < q)
    (hD : 0 < D) (h1 : 0 < r1) (h2 : 0 < r2) :
    |xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩| * ySep c D ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩
      = |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)| / ((q : ℝ) * (D : ℝ)) := by
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hD' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have h1' : (0 : ℝ) < (r1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < (r2 : ℝ) := by exact_mod_cast h2
  rw [farRange_abs_xOrig_eq c q r1 s1 r2 s2 hc h1 h2, farRange_ySep_unfold]
  field_simp

/-! ## Unfolding of the far weight -/

lemma farWeight_eq (D : ℕ) (a b : ℝ) (c : ℕ) (i : FarIx) :
    farWeight D a b c i
      = ((Work.FIArea4.Vflip.bump (|xOrig c i| * ySep c D i)
          * Work.FIArea4.Vflip.nearCut a b (xOrig c i) : ℝ) : ℂ) := rfl

/-! ## The two-sided `q'`-bound of a nonvanishing far summand

This is the strict form of the first half of the paper's range bound: a nonvanishing summand forces
`2SR < 5H c D q'` (strict!) and `c D q' ≤ 8RS`. -/

theorem farRange_bounds {D R S m c Q1 Q2 : ℕ} {a b H : ℝ} {i : FarIx}
    (hi : i ∈ farSet D R S a b m c Q1 Q2) (hD : 0 < D) (hH : 0 < H) (ha : 0 < a)
    (haH : a * H * (R : ℝ) = 2 * (S : ℝ))
    (hw : farWeight D a b c i ≠ 0) :
    2 * (S : ℝ) * (R : ℝ) < 5 * H * (c : ℝ) * (D : ℝ) * (i.1.1 : ℝ)
      ∧ (c : ℝ) * (D : ℝ) * (i.1.1 : ℝ) ≤ 8 * (R : ℝ) * (S : ℝ) := by
  rcases i with ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩
  obtain ⟨hQ1, -, -, -, -, -, -, hfar⟩ := mem_farSet.mp hi
  obtain ⟨hc, hcop, hA1, hA2, hB1, hB2, hC1, hC2, hD1, hD2, hmc, hmq⟩ := hfar
  have hQ1' : Q1 < q := hQ1
  have hq : 0 < q := by omega
  have hr1 : 0 < r1 := Nat.pos_of_mul_pos_left (lt_of_le_of_lt (Nat.zero_le R) hA1)
  have hr2 : 0 < r2 := Nat.pos_of_mul_pos_left (lt_of_le_of_lt (Nat.zero_le R) hB1)
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hr1R : (0 : ℝ) < (r1 : ℝ) := by exact_mod_cast hr1
  have hr2R : (0 : ℝ) < (r2 : ℝ) := by exact_mod_cast hr2
  have hcpos : (0 : ℝ) < (c : ℝ) * (r1 : ℝ) * (r2 : ℝ) := by positivity
  have hqDpos : (0 : ℝ) < (q : ℝ) * (D : ℝ) := by positivity
  -- the smooth weight factors into two nonvanishing cutoffs
  have hw' : Work.FIArea4.Vflip.bump (|xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩|
        * ySep c D ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩)
      * Work.FIArea4.Vflip.nearCut a b (xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩) ≠ 0 := by
    intro hh
    exact hw (by rw [farWeight_eq, hh, Complex.ofReal_zero])
  have hbump : Work.FIArea4.Vflip.bump (|xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩|
        * ySep c D ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩) ≠ 0 := fun h => hw' (by rw [h, zero_mul])
  have hnc : Work.FIArea4.Vflip.nearCut a b (xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩) ≠ 0 :=
    fun h => hw' (by rw [h, mul_zero])
  obtain ⟨hb1, hb2⟩ := farRange_bump_ne_zero_bounds hbump
  have hnc' : a / 2 < |xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩| := farRange_nearCut_ne_zero_abs_lower ha hnc
  have hxy : |xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩| * ySep c D ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩
      = |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)| / ((q : ℝ) * (D : ℝ)) :=
    farRange_abs_xOrig_mul_ySep_eq c D q r1 s1 r2 s2 hc hq hD hr1 hr2
  have hxval : |xOrig c ⟨⟨q, r1, s1⟩, ⟨r2, s2⟩⟩|
      = |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)| / ((c : ℝ) * (r1 : ℝ) * (r2 : ℝ)) :=
    farRange_abs_xOrig_eq c q r1 s1 r2 s2 hc hr1 hr2
  have hBlow : (q : ℝ) * (D : ℝ) / 2
      < |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)| := by
    have h := hb1
    rw [hxy] at h
    rw [lt_div_iff₀ hqDpos] at h
    linarith
  have hBup : |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)|
      < 5 * ((q : ℝ) * (D : ℝ)) / 2 := by
    have h := hb2
    rw [hxy] at h
    rw [div_lt_iff₀ hqDpos] at h
    linarith
  have hBnear : (a / 2) * ((c : ℝ) * (r1 : ℝ) * (r2 : ℝ))
      < |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)| := by
    have h := hnc'
    rw [hxval] at h
    rw [lt_div_iff₀ hcpos] at h
    linarith
  refine ⟨?_, ?_⟩
  · -- strict lower bound `2SR < 5H c D q'`
    have hR1 : (R : ℝ) < (c : ℝ) * (r1 : ℝ) := by exact_mod_cast hA1
    have hR2 : (R : ℝ) < (c : ℝ) * (r2 : ℝ) := by exact_mod_cast hB1
    have hX : a * ((c : ℝ) * (r1 : ℝ) * (r2 : ℝ)) < 5 * ((q : ℝ) * (D : ℝ)) := by
      linarith [hBnear, hBup]
    have hRR : (R : ℝ) * (R : ℝ) < ((c : ℝ) * (r1 : ℝ)) * ((c : ℝ) * (r2 : ℝ)) := by
      have h1 : (R : ℝ) * (R : ℝ) ≤ ((c : ℝ) * (r1 : ℝ)) * (R : ℝ) :=
        mul_le_mul_of_nonneg_right (le_of_lt hR1) (Nat.cast_nonneg R)
      have h2 : ((c : ℝ) * (r1 : ℝ)) * (R : ℝ) < ((c : ℝ) * (r1 : ℝ)) * ((c : ℝ) * (r2 : ℝ)) :=
        mul_lt_mul_of_pos_left hR2 (mul_pos hcR hr1R)
      linarith
    have hmain : a * (R : ℝ) * (R : ℝ) < 5 * (c : ℝ) * ((q : ℝ) * (D : ℝ)) := by
      have h3 : a * ((c : ℝ) * (r1 : ℝ) * (r2 : ℝ)) * (c : ℝ)
          < 5 * ((q : ℝ) * (D : ℝ)) * (c : ℝ) := mul_lt_mul_of_pos_right hX hcR
      have h4 : a * ((R : ℝ) * (R : ℝ)) < a * (((c : ℝ) * (r1 : ℝ)) * ((c : ℝ) * (r2 : ℝ))) :=
        mul_lt_mul_of_pos_left hRR ha
      nlinarith [h3, h4]
    rw [show 2 * (S : ℝ) * (R : ℝ) = a * H * (R : ℝ) * (R : ℝ) by rw [← haH]]
    have h6H : H * (a * (R : ℝ) * (R : ℝ)) < H * (5 * (c : ℝ) * ((q : ℝ) * (D : ℝ))) :=
      mul_lt_mul_of_pos_left hmain hH
    nlinarith [h6H]
  · -- upper bound `c D q' ≤ 8RS`
    have hqD : (q : ℝ) * (D : ℝ)
        < 2 * |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)| := by linarith [hBlow]
    have hA4 : (c : ℝ) * (s1 : ℝ) * (r2 : ℝ) ≤ 4 * (R : ℝ) * (S : ℝ) := by
      have hcr2 : (0 : ℝ) ≤ (c : ℝ) * (r2 : ℝ) := by positivity
      have hcr2le : (c : ℝ) * (r2 : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hB2
      have hs1le : (s1 : ℝ) ≤ 2 * (S : ℝ) := by exact_mod_cast hC2
      have hs1nn : (0 : ℝ) ≤ (s1 : ℝ) := Nat.cast_nonneg s1
      have := mul_le_mul hcr2le hs1le hs1nn (by positivity : (0 : ℝ) ≤ 2 * (R : ℝ))
      nlinarith
    have hB4 : (c : ℝ) * (s2 : ℝ) * (r1 : ℝ) ≤ 4 * (R : ℝ) * (S : ℝ) := by
      have hcr1 : (0 : ℝ) ≤ (c : ℝ) * (r1 : ℝ) := by positivity
      have hcr1le : (c : ℝ) * (r1 : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hA2
      have hs2le : (s2 : ℝ) ≤ 2 * (S : ℝ) := by exact_mod_cast hD2
      have hs2nn : (0 : ℝ) ≤ (s2 : ℝ) := Nat.cast_nonneg s2
      have := mul_le_mul hcr1le hs2le hs2nn (by positivity : (0 : ℝ) ≤ 2 * (R : ℝ))
      nlinarith
    have hcabs : (c : ℝ) * |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)|
        = |(c : ℝ) * ((s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ))| := by
      rw [abs_mul, abs_of_pos hcR]
    have ht1 : (0 : ℝ) ≤ (c : ℝ) * (s1 : ℝ) * (r2 : ℝ) := by positivity
    have ht2 : (0 : ℝ) ≤ (c : ℝ) * (s2 : ℝ) * (r1 : ℝ) := by positivity
    have hcB : (c : ℝ) * |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)|
        ≤ 4 * (R : ℝ) * (S : ℝ) := by
      rw [hcabs,
        show (c : ℝ) * ((s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ))
          = (c : ℝ) * (s1 : ℝ) * (r2 : ℝ) - (c : ℝ) * (s2 : ℝ) * (r1 : ℝ) by ring]
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · linarith [hA4, ht2]
      · linarith [hB4, ht1]
    have h1 : (c : ℝ) * ((q : ℝ) * (D : ℝ))
        < (c : ℝ) * (2 * |(s1 : ℝ) * (r2 : ℝ) - (s2 : ℝ) * (r1 : ℝ)|) :=
      mul_lt_mul_of_pos_left hqD hcR
    nlinarith only [h1, hcB]

/-! ## The vanishing of the far pieces outside the range -/

theorem farInner_eq_zero_of_range {D R S m c Q1 Q2 : ℕ} {a b H : ℝ} {α : ℕ → ℕ → ℂ}
    (hD : 0 < D) (hH : 0 < H) (ha : 0 < a)
    (haH : a * H * (R : ℝ) = 2 * (S : ℝ)) :
    ((Q2 : ℝ) * (5 * H * (c : ℝ) * (D : ℝ)) ≤ 2 * (S : ℝ) * (R : ℝ)
        → farInner D R S a b α m c Q1 Q2 = 0)
      ∧ (8 * (R : ℝ) * (S : ℝ) ≤ (Q1 : ℝ) * (c : ℝ) * (D : ℝ)
        → farInner D R S a b α m c Q1 Q2 = 0) := by
  constructor
  · intro h
    have hcDnn : (0 : ℝ) ≤ 5 * H * (c : ℝ) * (D : ℝ) := by positivity
    rw [farInner]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hw0 : farWeight D a b c i = 0 := by
      by_contra hw
      have hstrict := (farRange_bounds hi hD hH ha haH hw).1
      have hqQ2 : i.1.1 ≤ Q2 := (mem_farSet.mp hi).2.1
      have hmono : 5 * H * (c : ℝ) * (D : ℝ) * (i.1.1 : ℝ)
          ≤ 5 * H * (c : ℝ) * (D : ℝ) * (Q2 : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hqQ2) hcDnn
      have hbound : 5 * H * (c : ℝ) * (D : ℝ) * (Q2 : ℝ)
          ≤ 2 * (S : ℝ) * (R : ℝ) := by
        calc 5 * H * (c : ℝ) * (D : ℝ) * (Q2 : ℝ)
            = (Q2 : ℝ) * (5 * H * (c : ℝ) * (D : ℝ)) := by ring
          _ ≤ 2 * (S : ℝ) * (R : ℝ) := h
      linarith [hstrict, hmono, hbound]
    rw [hw0, mul_zero]
  · intro h
    rw [farInner]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hw0 : farWeight D a b c i = 0 := by
      by_contra hw
      have hq : Q1 < i.1.1 := (mem_farSet.mp hi).1
      have hc : 0 < c := (farCond_pos (farCond_of_mem_farSet hi)).1
      have hcd : (0 : ℝ) < (c : ℝ) * (D : ℝ) := by
        have h1 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
        have h2 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
        positivity
      have h2 := (farRange_bounds hi hD hH ha haH hw).2
      have hle : (c : ℝ) * (D : ℝ) * (i.1.1 : ℝ) ≤ (c : ℝ) * (D : ℝ) * (Q1 : ℝ) := by
        calc (c : ℝ) * (D : ℝ) * (i.1.1 : ℝ) ≤ 8 * (R : ℝ) * (S : ℝ) := h2
          _ ≤ (Q1 : ℝ) * (c : ℝ) * (D : ℝ) := h
          _ = (c : ℝ) * (D : ℝ) * (Q1 : ℝ) := by ring
      have hqle : (i.1.1 : ℝ) ≤ (Q1 : ℝ) := le_of_mul_le_mul_left hle hcd
      have hnat : i.1.1 ≤ Q1 := by exact_mod_cast hqle
      omega
    rw [hw0, mul_zero]

end

end Work.FIArea4.Vflip.Vfd
