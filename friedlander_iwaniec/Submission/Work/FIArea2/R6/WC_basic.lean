import Mathlib
import Submission.Work.FIArea2.R6.WCbasicDefs
import Submission.Work.FIArea2.R6.gcdBox_bound
import Submission.Work.FIArea2.R6.wc_minVec_and_parallel
import Submission.Work.FIArea2.R6.wc_det_card_le
import Submission.Work.FIArea2.R6.wc_det_zero_primitive
import Submission.Work.FIArea2.R6.wc_sum_inv_sup

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

section Helpers

/-- `a.natAbs ≤ t` in terms of the interval `[-t,t]` in `ℤ`. -/
lemma natAbs_le_iff (a : ℤ) (t : ℕ) : a.natAbs ≤ t ↔ (-(t : ℤ) ≤ a ∧ a ≤ (t : ℤ)) := by
  have h : ((a.natAbs : ℕ) : ℤ) ≤ ((t : ℕ) : ℤ) ↔ a.natAbs ≤ t := by exact_mod_cast Iff.rfl
  rw [← h, Int.natCast_natAbs]
  exact abs_le

/-- `wcSup` is zero only for the zero vector. -/
lemma wcSup_eq_zero_iff (w : ℤ × ℤ) : wcSup w = 0 ↔ w = 0 := by
  rw [wcSup, Nat.max_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Int.natAbs_eq_zero] at h1 h2
    exact Prod.ext h1 h2
  · rintro rfl
    simp

/-- A nonzero integer vector has sup-norm at least `1`. -/
lemma one_le_wcSup_iff (w : ℤ × ℤ) : 1 ≤ wcSup w ↔ w ≠ 0 := by
  rw [Nat.one_le_iff_ne_zero]
  exact not_congr (wcSup_eq_zero_iff w)

/-- Membership in the sup-norm box. -/
lemma mem_wcBox_iff (t : ℕ) (w : ℤ × ℤ) : w ∈ wcBox t ↔ wcSup w ≤ t := by
  simp only [wcBox, Finset.mem_product, Finset.mem_Icc, wcSup, max_le_iff, natAbs_le_iff]

/-- The lattice condition `wcInL` in terms of the original `h`-coordinates. -/
lemma wcInL_iff_sq (c : ℕ) (h1 h2 : ℤ) (w : ℤ × ℤ) :
    wcInL c (h1.natAbs ^ 2) (h2.natAbs ^ 2) w ↔ (c : ℤ) ∣ w.1 * h1 ^ 2 - w.2 * h2 ^ 2 := by
  rw [wcInL, ← sq_eq_cast_natAbs_sq h1, ← sq_eq_cast_natAbs_sq h2]
  rw [show h1 ^ 2 * w.1 - h2 ^ 2 * w.2 = w.1 * h1 ^ 2 - w.2 * h2 ^ 2 by ring]

/-- The square of an integer, cast to `ℝ`, is the cast of the square of its absolute value. -/
lemma cast_sq_eq_natAbs_sq (h : ℤ) : ((h : ℝ)) ^ 2 = (((h.natAbs) ^ 2 : ℕ) : ℝ) := by
  have := congrArg (fun z : ℤ => (z : ℝ)) (sq_eq_cast_natAbs_sq h)
  simpa using this

/-- `min 1 (Z/c) = min c Z / c`. -/
lemma min_one_div_eq (c : ℕ) (hc : 1 ≤ c) (Z : ℝ) :
    min 1 (Z / (c : ℝ)) = min (c : ℝ) Z / (c : ℝ) := by
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  rcases le_total Z (c : ℝ) with h | h
  · have h' : Z / (c : ℝ) ≤ 1 := (div_le_one hcpos).mpr h
    rw [min_eq_right h', min_eq_right h]
  · have h' : 1 ≤ Z / (c : ℝ) := by
      rw [le_div_iff₀ hcpos]; linarith
    rw [min_eq_left h', min_eq_left h, div_self (ne_of_gt hcpos)]

end Helpers

/-- **A non-zero divisible value forces the box to be large enough.**
If `c ∣ w₁h₁²-w₂h₂² ≠ 0` then the value has absolute value at least `c` while being at most
`max(|w₁|,|w₂|)·(h₁²+h₂²)`; hence `c ≤ max(|w₁|,|w₂|)·(h₁²+h₂²)`.

(Reproduced verbatim from `R6/WC_perMod.lean`, which cannot be imported because it ends with an
unproved main theorem.) -/
lemma le_max_mul_of_dvd (h1 h2 : ℤ) (c : ℕ) (hc : 1 ≤ c) (w1 w2 : ℤ)
    (hdvd : (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2) (hne : w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0) :
    (c : ℤ) ≤ (max w1.natAbs w2.natAbs : ℤ) * (h1 ^ 2 + h2 ^ 2) := by
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : (k : ℤ) ≠ 0 := by
    rintro h0
    exact hne (by rw [hk, h0]; ring)
  have hc0 : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
  have hstep1 : (c : ℤ) ≤ |w1 * h1 ^ 2 - w2 * h2 ^ 2| := by
    rw [hk, abs_mul, abs_of_nonneg (le_of_lt hc0)]
    nlinarith [hc0, hk1]
  have hA : |w1| ≤ (max w1.natAbs w2.natAbs : ℤ) := by
    rw [← Int.natCast_natAbs]; exact_mod_cast le_max_left w1.natAbs w2.natAbs
  have hB : |w2| ≤ (max w1.natAbs w2.natAbs : ℤ) := by
    rw [← Int.natCast_natAbs]; exact_mod_cast le_max_right w1.natAbs w2.natAbs
  have hsq : (0 : ℤ) ≤ h1 ^ 2 := sq_nonneg _
  have hsq2 : (0 : ℤ) ≤ h2 ^ 2 := sq_nonneg _
  have hupper : w1 * h1 ^ 2 - w2 * h2 ^ 2 ≤ |w1| * h1 ^ 2 + |w2| * h2 ^ 2 := by
    have ha := le_abs_self w1
    have hb := neg_le_abs w2
    nlinarith [hsq, hsq2]
  have hlower : -(|w1| * h1 ^ 2 + |w2| * h2 ^ 2) ≤ w1 * h1 ^ 2 - w2 * h2 ^ 2 := by
    have ha := neg_le_abs w1
    have hb := le_abs_self w2
    nlinarith [hsq, hsq2]
  have hstep2 : |w1 * h1 ^ 2 - w2 * h2 ^ 2| ≤ (max w1.natAbs w2.natAbs : ℤ) * (h1 ^ 2 + h2 ^ 2) := by
    have h3 : |w1 * h1 ^ 2 - w2 * h2 ^ 2| ≤ |w1| * h1 ^ 2 + |w2| * h2 ^ 2 :=
      abs_le.mpr ⟨hlower, hupper⟩
    nlinarith [h3, hA, hB, abs_nonneg w1, abs_nonneg w2, hsq, hsq2]
  linarith [hstep1, hstep2]

/-- **The per-`(h₁,h₂)` bound.**

For fixed `h₁,h₂ ≠ 0` the weighted primitive-pair count satisfies

  `wcThStar c r h₁ h₂ ≤ 80·r·gcd(c,h₁²,h₂²)/c + 2·min(1, (h₁²+h₂²)/c)`.

The second term is the contribution of the two vectors `±v` on the shortest-vector line of the
lattice `{w : c ∣ w₁h₁² - w₂h₂²}`; for a non-zero divisible value `c ≤ |v|∞(h₁²+h₂²)`
(`le_max_mul_of_dvd`), giving `2/|v|∞ ≤ 2·min(1,(h₁²+h₂²)/c)`. -/
theorem wcThStar_le (c r : ℕ) (hc : 1 ≤ c) (hr : 1 ≤ r) (h1 h2 : ℤ) (hh1 : h1 ≠ 0)
    (hh2 : h2 ≠ 0) :
    wcThStar c r h1 h2
      ≤ 80 * (r : ℝ) * ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ) / (c : ℝ)
        + 2 * min 1 ((((h1.natAbs ^ 2 : ℕ) : ℝ) + ((h2.natAbs ^ 2 : ℕ) : ℝ)) / (c : ℝ)) := by
  set A : ℕ := h1.natAbs ^ 2 with hAdef
  set B : ℕ := h2.natAbs ^ 2 with hBdef
  have hA1 : 1 ≤ A := by
    rw [hAdef]; exact Nat.one_le_pow 2 _ (Int.natAbs_pos.mpr hh1)
  have hB1 : 1 ≤ B := by
    rw [hBdef]; exact Nat.one_le_pow 2 _ (Int.natAbs_pos.mpr hh2)
  obtain ⟨v, hvL, hv0, hmin, hpar⟩ := wc_minVec_and_parallel c A B hA1 hc
  have hInL : ∀ w : ℤ × ℤ, wcInL c A B w ↔ (c : ℤ) ∣ w.1 * h1 ^ 2 - w.2 * h2 ^ 2 := by
    intro w
    rw [hAdef, hBdef]
    exact wcInL_iff_sq c h1 h2 w
  set I : ℕ := wcI c A B with hIdef
  have hGdvd : wcG c A B ∣ c := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hGI : wcG c A B * I = c := by
    rw [hIdef, wcI]; exact Nat.mul_div_cancel' hGdvd
  have hI1 : 1 ≤ I := by
    refine Nat.one_le_iff_ne_zero.mpr (fun h0 => ?_)
    have h := hGI
    rw [h0, mul_zero] at h
    omega
  -- the selected set
  set Sel : Finset (ℤ × ℤ) := ((zPz r) ×ˢ (zPz r)).filter
      (fun w => Int.gcd w.1 w.2 = 1 ∧ w.1 * h1 ^ 2 - w.2 * h2 ^ 2 ≠ 0
        ∧ (c : ℤ) ∣ w.1 * h1 ^ 2 - w.2 * h2 ^ 2) with hSeldef
  have hTh : wcThStar c r h1 h2 = ∑ w ∈ Sel, (1 : ℝ) / (wcSup w : ℝ) := by
    rw [hSeldef]
    simp only [wcThStar, wcSup, Finset.sum_filter, Finset.sum_product]
  have hsplit : ∑ w ∈ Sel, (1 : ℝ) / (wcSup w : ℝ)
      = (∑ w ∈ Sel.filter (fun w => wcDet v w = 0), (1 : ℝ) / (wcSup w : ℝ))
        + ∑ w ∈ Sel.filter (fun w => ¬ (wcDet v w = 0)), (1 : ℝ) / (wcSup w : ℝ) := by
    rw [Finset.sum_filter_add_sum_filter_not Sel (fun w => wcDet v w = 0)
      (fun w => (1 : ℝ) / (wcSup w : ℝ))]
  -- the `det = 0` part: only `±v`
  have hS0 : (∑ w ∈ Sel.filter (fun w => wcDet v w = 0), (1 : ℝ) / (wcSup w : ℝ))
      ≤ 2 * min 1 (((A : ℝ) + (B : ℝ)) / (c : ℝ)) := by
    by_cases h0 : (Sel.filter (fun w => wcDet v w = 0)).Nonempty
    · obtain ⟨w0, hw0⟩ := h0
      simp only [Finset.mem_filter, hSeldef, Finset.mem_product] at hw0
      obtain ⟨hw0sel, hw0det⟩ := hw0
      obtain ⟨-, hw0prim, hw0Nne, hw0dvd⟩ := hw0sel
      have hw0L : wcInL c A B w0 := (hInL w0).mpr hw0dvd
      have hw0eq : w0 = v ∨ w0 = (-v.1, -v.2) :=
        wc_det_zero_primitive c A B hA1 hc v hvL hv0 hmin w0 hw0L hw0prim hw0det
      have hneg : Int.gcd (-v.1) (-v.2) = Int.gcd v.1 v.2 := by
        calc Int.gcd (-v.1) (-v.2) = Int.gcd (-v.1) v.2 := by rw [Int.gcd_neg]
          _ = Int.gcd v.2 (-v.1) := by rw [Int.gcd_comm]
          _ = Int.gcd v.2 v.1 := by rw [Int.gcd_neg]
          _ = Int.gcd v.1 v.2 := by rw [Int.gcd_comm]
      have hvNne : v.1 * h1 ^ 2 - v.2 * h2 ^ 2 ≠ 0 := by
        rcases hw0eq with h | h
        · rw [← h]; exact hw0Nne
        · have e : w0.1 * h1 ^ 2 - w0.2 * h2 ^ 2
              = -(v.1 * h1 ^ 2 - v.2 * h2 ^ 2) := by rw [h]; ring
          rw [e] at hw0Nne
          intro hcon
          exact hw0Nne (by rw [hcon]; ring)
      have hvdvd : (c : ℤ) ∣ v.1 * h1 ^ 2 - v.2 * h2 ^ 2 := by
        rcases hw0eq with h | h
        · rw [← h]; exact hw0dvd
        · have e : w0.1 * h1 ^ 2 - w0.2 * h2 ^ 2
              = -(v.1 * h1 ^ 2 - v.2 * h2 ^ 2) := by rw [h]; ring
          rw [e] at hw0dvd
          exact dvd_neg.mp hw0dvd
      have hcle : (c : ℤ) ≤ (wcSup v : ℤ) * (h1 ^ 2 + h2 ^ 2) := by
        rw [wcSup, Nat.cast_max]
        exact le_max_mul_of_dvd h1 h2 c hc v.1 v.2 hvdvd hvNne
      have hsub0 : Sel.filter (fun w => wcDet v w = 0) ⊆ ({v, (-v.1, -v.2)} : Finset (ℤ × ℤ)) := by
        intro w hw
        simp only [Finset.mem_filter, hSeldef, Finset.mem_product] at hw
        obtain ⟨hwsel, hwdet⟩ := hw
        obtain ⟨-, hwprim, hwNne, hwdvd⟩ := hwsel
        have hwL : wcInL c A B w := (hInL w).mpr hwdvd
        rcases wc_det_zero_primitive c A B hA1 hc v hvL hv0 hmin w hwL hwprim hwdet with h | h
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
      have hle0 : (∑ w ∈ Sel.filter (fun w => wcDet v w = 0), (1 : ℝ) / (wcSup w : ℝ))
          ≤ 2 / (wcSup v : ℝ) := by
        calc ∑ w ∈ Sel.filter (fun w => wcDet v w = 0), (1 : ℝ) / (wcSup w : ℝ)
            ≤ ∑ w ∈ ({v, (-v.1, -v.2)} : Finset (ℤ × ℤ)), (1 : ℝ) / (wcSup w : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub0 (by intro w _ _; positivity)
          _ ≤ 2 / (wcSup v : ℝ) := by
              have hmem : ∀ w ∈ ({v, (-v.1, -v.2)} : Finset (ℤ × ℤ)),
                  (1 : ℝ) / (wcSup w : ℝ) ≤ 1 / (wcSup v : ℝ) := by
                intro w hw
                simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with h | h
                · rw [h]
                · rw [h]
                  simp only [wcSup, Int.natAbs_neg, le_refl]
              calc ∑ w ∈ ({v, (-v.1, -v.2)} : Finset (ℤ × ℤ)), (1 : ℝ) / (wcSup w : ℝ)
                  ≤ ∑ _w ∈ ({v, (-v.1, -v.2)} : Finset (ℤ × ℤ)), (1 : ℝ) / (wcSup v : ℝ) :=
                    Finset.sum_le_sum hmem
                _ = (({v, (-v.1, -v.2)} : Finset (ℤ × ℤ)).card : ℝ) * (1 / (wcSup v : ℝ)) := by
                    rw [Finset.sum_const, nsmul_eq_mul]
                _ ≤ 2 * (1 / (wcSup v : ℝ)) := by
                    apply mul_le_mul_of_nonneg_right _ (by positivity)
                    have hc2 : ({v, (-v.1, -v.2)} : Finset (ℤ × ℤ)).card ≤ 2 := by
                      have h := Finset.card_insert_le v ({(-v.1, -v.2)} : Finset (ℤ × ℤ))
                      simp only [Finset.card_singleton] at h
                      omega
                    exact_mod_cast hc2
                _ = 2 / (wcSup v : ℝ) := by ring
      have h2le : 2 / (wcSup v : ℝ) ≤ 2 * min 1 (((A : ℝ) + (B : ℝ)) / (c : ℝ)) := by
        have hlam1 : (1 : ℝ) ≤ (wcSup v : ℝ) := by
          exact_mod_cast (one_le_wcSup_iff v).mpr hv0
        have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
        have hle1 : 2 / (wcSup v : ℝ) ≤ 2 := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < (wcSup v : ℝ))]
          linarith
        have hcleR : (c : ℝ) ≤ (wcSup v : ℝ) * ((A : ℝ) + (B : ℝ)) := by
          have hcast : (((c : ℤ)) : ℝ)
              ≤ (((wcSup v : ℤ)) : ℝ) * ((((h1 : ℤ)) : ℝ) ^ 2 + (((h2 : ℤ)) : ℝ) ^ 2) := by
            exact_mod_cast hcle
          have hw : (((wcSup v : ℤ)) : ℝ) = (wcSup v : ℝ) := by exact_mod_cast rfl
          have hc' : ((c : ℤ) : ℝ) = (c : ℝ) := by exact_mod_cast rfl
          rw [hw, hc'] at hcast
          have e1 : ((h1 : ℝ)) ^ 2 = (A : ℝ) := by rw [hAdef]; exact cast_sq_eq_natAbs_sq h1
          have e2 : ((h2 : ℝ)) ^ 2 = (B : ℝ) := by rw [hBdef]; exact cast_sq_eq_natAbs_sq h2
          rw [e1, e2] at hcast
          exact hcast
        have hle2 : 2 / (wcSup v : ℝ) ≤ 2 * (((A : ℝ) + (B : ℝ)) / (c : ℝ)) := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < (wcSup v : ℝ))]
          rw [show 2 * (((A : ℝ) + (B : ℝ)) / (c : ℝ)) * (wcSup v : ℝ)
              = 2 * ((wcSup v : ℝ) * ((A : ℝ) + (B : ℝ))) / (c : ℝ) by
            field_simp]
          rw [le_div_iff₀ hcpos]
          nlinarith [hcleR]
        calc 2 / (wcSup v : ℝ) ≤ min 2 (2 * (((A : ℝ) + (B : ℝ)) / (c : ℝ))) := le_min hle1 hle2
          _ = 2 * min 1 (((A : ℝ) + (B : ℝ)) / (c : ℝ)) := by
              rw [mul_min_of_nonneg 1 _ (by norm_num : (0 : ℝ) ≤ 2)]
              norm_num
      linarith [hle0, h2le]
    · rw [Finset.not_nonempty_iff_eq_empty] at h0
      rw [h0, Finset.sum_empty]
      have : (0 : ℝ) ≤ 2 * min 1 (((A : ℝ) + (B : ℝ)) / (c : ℝ)) := by
        apply mul_nonneg (by norm_num)
        exact le_min zero_le_one (by positivity)
      linarith
  -- the `det ≠ 0` part: layer cake along the sup-norm
  have hS1 : (∑ w ∈ Sel.filter (fun w => ¬ (wcDet v w = 0)), (1 : ℝ) / (wcSup w : ℝ))
      ≤ 80 * (r : ℝ) / (I : ℝ) := by
    set W : Finset (ℤ × ℤ) :=
      (wcBox r).filter (fun w => wcInL c A B w ∧ wcDet v w ≠ 0) with hWdef
    have hsub : Sel.filter (fun w => ¬ (wcDet v w = 0)) ⊆ W := by
      intro w hw
      simp only [Finset.mem_filter, hSeldef, Finset.mem_product] at hw
      obtain ⟨hwsel, hwd⟩ := hw
      obtain ⟨hwprod, -, -, hwdvd⟩ := hwsel
      rw [hWdef]
      simp only [Finset.mem_filter]
      refine ⟨?_, (hInL w).mpr hwdvd, hwd⟩
      rw [mem_wcBox_iff, wcSup, max_le_iff]
      obtain ⟨hw1, hw2⟩ := hwprod
      simp only [zPz, Finset.mem_filter, Finset.mem_Icc] at hw1 hw2
      exact ⟨(natAbs_le_iff w.1 r).mpr hw1.1, (natAbs_le_iff w.2 r).mpr hw2.1⟩
    have hneW : ∀ w ∈ W, w ≠ 0 := by
      intro w hw h0
      rw [hWdef] at hw
      simp only [Finset.mem_filter] at hw
      exact hw.2.2 (by rw [h0]; simp [wcDet])
    have hboxW : ∀ w ∈ W, wcSup w ≤ r := by
      intro w hw
      rw [hWdef] at hw
      simp only [Finset.mem_filter] at hw
      exact (mem_wcBox_iff r w).mp hw.1
    have hcnt : ∀ t : ℕ, ((W.filter (fun w => wcSup w ≤ t)).card : ℝ) ≤ 40 * (t : ℝ) ^ 2 / (I : ℝ) := by
      intro t
      have hsub2 : W.filter (fun w => wcSup w ≤ t)
          ⊆ (wcBox t).filter (fun w => wcInL c A B w ∧ wcDet v w ≠ 0) := by
        intro w hw
        rw [hWdef] at hw
        simp only [Finset.mem_filter] at hw
        obtain ⟨⟨hwb, hwL, hwd⟩, hws⟩ := hw
        simp only [Finset.mem_filter]
        exact ⟨(mem_wcBox_iff t w).mpr hws, hwL, hwd⟩
      have hcard : ((W.filter (fun w => wcSup w ≤ t)).card : ℝ)
          ≤ (((wcBox t).filter (fun w => wcInL c A B w ∧ wcDet v w ≠ 0)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub2
      refine le_trans hcard ?_
      simpa only [hIdef] using wc_det_card_le c A B t hA1 hB1 hc v hvL hv0 hmin
    have hterm : ∀ t ∈ Finset.Icc 1 r,
        ((W.filter (fun w => wcSup w ≤ t)).card : ℝ) / ((t : ℝ) * ((t : ℝ) + 1))
          ≤ 40 / (I : ℝ) := by
      intro t ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
      have hden : (0 : ℝ) < (t : ℝ) * ((t : ℝ) + 1) := by positivity
      have hIpos : (0 : ℝ) < (I : ℝ) := by exact_mod_cast hI1
      have step1 : ((W.filter (fun w => wcSup w ≤ t)).card : ℝ) / ((t : ℝ) * ((t : ℝ) + 1))
          ≤ (40 * (t : ℝ) ^ 2 / (I : ℝ)) / ((t : ℝ) * ((t : ℝ) + 1)) :=
        div_le_div_of_nonneg_right (hcnt t) (le_of_lt hden)
      have step2 : (40 * (t : ℝ) ^ 2 / (I : ℝ)) / ((t : ℝ) * ((t : ℝ) + 1))
          = (40 / (I : ℝ)) * ((t : ℝ) / ((t : ℝ) + 1)) := by
        field_simp
      have step3 : (t : ℝ) / ((t : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity : (0 : ℝ) < (t : ℝ) + 1)]
        linarith
      calc ((W.filter (fun w => wcSup w ≤ t)).card : ℝ) / ((t : ℝ) * ((t : ℝ) + 1))
          ≤ (40 * (t : ℝ) ^ 2 / (I : ℝ)) / ((t : ℝ) * ((t : ℝ) + 1)) := step1
        _ = (40 / (I : ℝ)) * ((t : ℝ) / ((t : ℝ) + 1)) := step2
        _ ≤ (40 / (I : ℝ)) * 1 := mul_le_mul_of_nonneg_left step3 (by positivity)
        _ = 40 / (I : ℝ) := by ring
    have hsumT : (∑ t ∈ Finset.Icc 1 r,
          ((W.filter (fun w => wcSup w ≤ t)).card : ℝ) / ((t : ℝ) * ((t : ℝ) + 1)))
        ≤ 40 * (r : ℝ) / (I : ℝ) := by
      calc ∑ t ∈ Finset.Icc 1 r,
            ((W.filter (fun w => wcSup w ≤ t)).card : ℝ) / ((t : ℝ) * ((t : ℝ) + 1))
          ≤ ∑ _t ∈ Finset.Icc 1 r, (40 / (I : ℝ)) := Finset.sum_le_sum hterm
        _ = ((Finset.Icc 1 r).card : ℝ) * (40 / (I : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = (r : ℝ) * (40 / (I : ℝ)) := by
            have hcardr : (Finset.Icc 1 r).card = r := by
              rw [Nat.card_Icc]; omega
            rw [hcardr]
        _ = 40 * (r : ℝ) / (I : ℝ) := by ring
    have hboundW : (W.card : ℝ) / ((r : ℝ) + 1) ≤ 40 * (r : ℝ) / (I : ℝ) := by
      have hWr : (W.card : ℝ) ≤ 40 * (r : ℝ) ^ 2 / (I : ℝ) := by
        have h := hcnt r
        rwa [Finset.filter_true_of_mem (fun w hw => hboxW w hw)] at h
      have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
      calc (W.card : ℝ) / ((r : ℝ) + 1) ≤ (40 * (r : ℝ) ^ 2 / (I : ℝ)) / ((r : ℝ) + 1) :=
            div_le_div_of_nonneg_right hWr (le_of_lt hr1)
        _ = (40 * (r : ℝ) / (I : ℝ)) * ((r : ℝ) / ((r : ℝ) + 1)) := by
            field_simp
        _ ≤ (40 * (r : ℝ) / (I : ℝ)) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_one (by positivity : (0 : ℝ) < (r : ℝ) + 1)]
            linarith
        _ = 40 * (r : ℝ) / (I : ℝ) := by ring
    have hcake := wc_sum_inv_sup r hr W hneW hboxW
    have hWsum : (∑ w ∈ W, (1 : ℝ) / (wcSup w : ℝ)) ≤ 80 * (r : ℝ) / (I : ℝ) := by
      rw [hcake]
      have h80 : 80 * (r : ℝ) / (I : ℝ) = 40 * (r : ℝ) / (I : ℝ) + 40 * (r : ℝ) / (I : ℝ) := by
        ring
      linarith [hsumT, hboundW, h80]
    calc (∑ w ∈ Sel.filter (fun w => ¬ (wcDet v w = 0)), (1 : ℝ) / (wcSup w : ℝ))
        ≤ ∑ w ∈ W, (1 : ℝ) / (wcSup w : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro w _ _; positivity)
      _ ≤ 80 * (r : ℝ) / (I : ℝ) := hWsum
  have hconv : 80 * (r : ℝ) / (I : ℝ) = 80 * (r : ℝ) * ((wcG c A B : ℕ) : ℝ) / (c : ℝ) := by
    have hgI : ((wcG c A B : ℕ) : ℝ) * (I : ℝ) = (c : ℝ) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) hGI
      push_cast at h
      exact h
    have hIpos : (0 : ℝ) < (I : ℝ) := by exact_mod_cast hI1
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    rw [div_eq_div_iff (ne_of_gt hIpos) (ne_of_gt hcpos), ← hgI]
    ring
  have hmain : wcThStar c r h1 h2
      ≤ 80 * (r : ℝ) / (I : ℝ) + 2 * min 1 (((A : ℝ) + (B : ℝ)) / (c : ℝ)) := by
    rw [hTh, hsplit]
    have := add_le_add hS0 hS1
    linarith [this]
  rw [hconv] at hmain
  exact hmain

/-- **The elementary per-modulus weighted primitive-pair count (counting along the shortest vector).**

`Work.FIArea2.R6.WC c r X Y` (from `Submission/Work/FIArea2/R6/WCDefs.lean`) is the weighted count

  `Σ_{h₁∈zPz X} Σ_{h₂∈zPz Y} Σ_{w₁,w₂∈zPz r, gcd(w₁,w₂)=1, N≠0, c ∣ N} 1/max(|w₁|,|w₂|)`,
  `N = w₁h₁² − w₂h₂²`.

Claim: for all `c,r,X,Y ≥ 1`,

  `WC c r X Y ≤ C·X·Y·r·τ(c)/c + C·X·Y·min(c, X²+Y²)/c`.
-/
theorem WC_basic :
    ∃ C : ℝ, 0 < C ∧ ∀ (c r X Y : ℕ), 1 ≤ c → 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      Work.FIArea2.R6.WC c r X Y
        ≤ C * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℕ) : ℝ) / (c : ℝ)
          + C * (X : ℝ) * (Y : ℝ) * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2))
              / (c : ℝ) := by
  refine ⟨320, by norm_num, ?_⟩
  intro c r X Y hc hr hX hY
  rw [WC_eq_sum_wcThStar]
  have hper : ∀ h1 ∈ zPz X, ∀ h2 ∈ zPz Y,
      wcThStar c r h1 h2
        ≤ 80 * (r : ℝ) * ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ) / (c : ℝ)
          + 2 * min 1 ((((h1.natAbs ^ 2 : ℕ) : ℝ) + ((h2.natAbs ^ 2 : ℕ) : ℝ)) / (c : ℝ)) := by
    intro h1 hh1 h2 hh2
    have hh1' : h1 ≠ 0 := by
      have := hh1; simp only [zPz, Finset.mem_filter] at this; exact this.2
    have hh2' : h2 ≠ 0 := by
      have := hh2; simp only [zPz, Finset.mem_filter] at this; exact this.2
    exact wcThStar_le c r hc hr h1 h2 hh1' hh2'
  have hsplit : ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, wcThStar c r h1 h2
      ≤ (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
            80 * (r : ℝ) * ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ) / (c : ℝ))
        + ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
            2 * min 1 ((((h1.natAbs ^ 2 : ℕ) : ℝ) + ((h2.natAbs ^ 2 : ℕ) : ℝ)) / (c : ℝ)) := by
    calc ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, wcThStar c r h1 h2
        ≤ ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
            (80 * (r : ℝ) * ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ) / (c : ℝ)
              + 2 * min 1 ((((h1.natAbs ^ 2 : ℕ) : ℝ)
                + ((h2.natAbs ^ 2 : ℕ) : ℝ)) / (c : ℝ))) := by
          apply Finset.sum_le_sum
          intro h1 hh1
          apply Finset.sum_le_sum
          intro h2 hh2
          exact hper h1 hh1 h2 hh2
      _ = _ := by
          simp only [Finset.sum_add_distrib]
  have hgsum : (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
        ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ)) = (gcdBox c X Y : ℝ) := by
    rw [gcdBox]
    push_cast
    simp only [wcG, Int.natAbs_pow]
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hA : (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
        80 * (r : ℝ) * ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ) / (c : ℝ))
      ≤ 320 * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℕ) : ℝ) / (c : ℝ) := by
    have hstep : ∀ i : ℤ, (∑ h2 ∈ zPz Y,
          80 * (r : ℝ) * ((wcG c (i.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ) / (c : ℝ))
        = (80 * (r : ℝ) / (c : ℝ))
            * (∑ h2 ∈ zPz Y, ((wcG c (i.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ)) := by
      intro i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h2 _
      ring
    have hrew : (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
          80 * (r : ℝ) * ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ) / (c : ℝ))
        = (80 * (r : ℝ) / (c : ℝ)) * (gcdBox c X Y : ℝ) := by
      calc (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
            80 * (r : ℝ) * ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ) / (c : ℝ))
          = ∑ h1 ∈ zPz X, (80 * (r : ℝ) / (c : ℝ))
              * (∑ h2 ∈ zPz Y, ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hstep i
        _ = (80 * (r : ℝ) / (c : ℝ))
              * (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
                  ((wcG c (h1.natAbs ^ 2) (h2.natAbs ^ 2) : ℕ) : ℝ)) := by
            rw [Finset.mul_sum]
        _ = (80 * (r : ℝ) / (c : ℝ)) * (gcdBox c X Y : ℝ) := by rw [hgsum]
    rw [hrew]
    have hgb := gcdBox_bound c X Y hc hX hY
    have hcoef : (0 : ℝ) ≤ 80 * (r : ℝ) / (c : ℝ) := by positivity
    calc (80 * (r : ℝ) / (c : ℝ)) * (gcdBox c X Y : ℝ)
        ≤ (80 * (r : ℝ) / (c : ℝ))
            * (4 * (X : ℝ) * (Y : ℝ) * ((c.divisors.card : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hgb hcoef
      _ = 320 * (X : ℝ) * (Y : ℝ) * (r : ℝ) * ((c.divisors.card : ℕ) : ℝ) / (c : ℝ) := by
          ring
  have hB : (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
        2 * min 1 ((((h1.natAbs ^ 2 : ℕ) : ℝ) + ((h2.natAbs ^ 2 : ℕ) : ℝ)) / (c : ℝ)))
      ≤ 18 * (X : ℝ) * (Y : ℝ)
          * (min 1 (((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ))) := by
    set K : ℝ := 2 * min 1 (((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ)) with hK
    have hKnn : (0 : ℝ) ≤ K := by rw [hK]; positivity
    have hterm : ∀ h1 ∈ zPz X, ∀ h2 ∈ zPz Y,
        2 * min 1 ((((h1.natAbs ^ 2 : ℕ) : ℝ) + ((h2.natAbs ^ 2 : ℕ) : ℝ)) / (c : ℝ)) ≤ K := by
      intro h1 hh1 h2 hh2
      have h1le : h1.natAbs ≤ X := by
        have := hh1
        simp only [zPz, Finset.mem_filter, Finset.mem_Icc] at this
        exact (natAbs_le_iff h1 X).mpr this.1
      have h2le : h2.natAbs ≤ Y := by
        have := hh2
        simp only [zPz, Finset.mem_filter, Finset.mem_Icc] at this
        exact (natAbs_le_iff h2 Y).mpr this.1
      have hsq1 : ((h1.natAbs ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ 2 := by
        have := Nat.pow_le_pow_left h1le 2
        exact_mod_cast this
      have hsq2 : ((h2.natAbs ^ 2 : ℕ) : ℝ) ≤ (Y : ℝ) ^ 2 := by
        have := Nat.pow_le_pow_left h2le 2
        exact_mod_cast this
      have hdiv : ((((h1.natAbs ^ 2 : ℕ) : ℝ) + ((h2.natAbs ^ 2 : ℕ) : ℝ)) / (c : ℝ))
          ≤ (((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ)) :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hcpos)
      rw [hK]
      exact mul_le_mul_of_nonneg_left (min_le_min le_rfl hdiv) (by norm_num)
    have hcardX : ((zPz X).card : ℝ) ≤ 2 * (X : ℝ) + 1 := by
      have hsub : zPz X ⊆ Finset.Icc (-(X : ℤ)) (X : ℤ) := Finset.filter_subset _ _
      have hle : (zPz X).card ≤ (Finset.Icc (-(X : ℤ)) (X : ℤ)).card := Finset.card_le_card hsub
      have hcard : (Finset.Icc (-(X : ℤ)) (X : ℤ)).card = 2 * X + 1 := by
        rw [Int.card_Icc]
        have h1 : ((X : ℤ) + 1 - (-(X : ℤ))) = ((2 * X + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h1, Int.toNat_natCast]
      rw [hcard] at hle
      exact_mod_cast hle
    have hcardY : ((zPz Y).card : ℝ) ≤ 2 * (Y : ℝ) + 1 := by
      have hsub : zPz Y ⊆ Finset.Icc (-(Y : ℤ)) (Y : ℤ) := Finset.filter_subset _ _
      have hle : (zPz Y).card ≤ (Finset.Icc (-(Y : ℤ)) (Y : ℤ)).card := Finset.card_le_card hsub
      have hcard : (Finset.Icc (-(Y : ℤ)) (Y : ℤ)).card = 2 * Y + 1 := by
        rw [Int.card_Icc]
        have h1 : ((Y : ℤ) + 1 - (-(Y : ℤ))) = ((2 * Y + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h1, Int.toNat_natCast]
      rw [hcard] at hle
      exact_mod_cast hle
    calc ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
          2 * min 1 ((((h1.natAbs ^ 2 : ℕ) : ℝ) + ((h2.natAbs ^ 2 : ℕ) : ℝ)) / (c : ℝ))
        ≤ ∑ h1 ∈ zPz X, ∑ _h2 ∈ zPz Y, K := by
          apply Finset.sum_le_sum
          intro h1 hh1
          apply Finset.sum_le_sum
          intro h2 hh2
          exact hterm h1 hh1 h2 hh2
      _ = ((zPz X).card : ℝ) * (((zPz Y).card : ℝ) * K) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      _ ≤ (2 * (X : ℝ) + 1) * ((2 * (Y : ℝ) + 1) * K) :=
          mul_le_mul hcardX (mul_le_mul_of_nonneg_right hcardY hKnn)
            (mul_nonneg (by positivity) hKnn) (by positivity)
      _ = ((2 * (X : ℝ) + 1) * (2 * (Y : ℝ) + 1)) * K := by ring
      _ ≤ (9 * (X : ℝ) * (Y : ℝ)) * K := by
          apply mul_le_mul_of_nonneg_right _ hKnn
          have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
          have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY
          nlinarith [hX1, hY1]
      _ = 18 * (X : ℝ) * (Y : ℝ)
            * (min 1 (((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ))) := by rw [hK]; ring
  have hmin : min 1 (((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ))
      = min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ) := min_one_div_eq c hc _
  rw [hmin] at hB
  have hXYnn : (0 : ℝ) ≤ (X : ℝ) * (Y : ℝ) := by positivity
  have hminnn : (0 : ℝ) ≤ min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ) :=
    div_nonneg (le_min (by positivity) (by positivity)) (le_of_lt hcpos)
  have hB2 : 18 * (X : ℝ) * (Y : ℝ) * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ))
      ≤ 320 * (X : ℝ) * (Y : ℝ) * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ)) := by
    have := mul_le_mul_of_nonneg_right (by linarith : (18:ℝ) * ((X : ℝ) * (Y : ℝ))
      ≤ 320 * ((X : ℝ) * (Y : ℝ))) hminnn
    linarith [this]
  have hxy : 320 * (X : ℝ) * (Y : ℝ)
        * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2) / (c : ℝ))
      = 320 * (X : ℝ) * (Y : ℝ)
        * (min (c : ℝ) ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2)) / (c : ℝ) := by ring
  linarith [hsplit, hA, hB, hB2, hxy]

end

end Work.FIArea2.R6
