import Mathlib
import Submission.Work.FIArea2.R6.WCbasicDefs
import Submission.Work.FIArea2.R6.wcI_dvd_wcDet
import Submission.Work.FIArea2.R6.wc_parallel_of_min
import Submission.Work.FIArea2.R6.wc_fibre_card_le
import Submission.Work.FIArea2.R6.wc_det_image_card_le

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Elementary helpers -/

/-- `wcI c A B ≥ 1` for `c ≥ 1`. -/
lemma wcI_pos {c A B : ℕ} (hc : 1 ≤ c) : 1 ≤ wcI c A B := by
  have hc0 : 0 < c := hc
  have hg1 : 0 < Nat.gcd c A := Nat.gcd_pos_of_pos_left A hc0
  have hG1 : 0 < wcG c A B := Nat.gcd_pos_of_pos_left B hg1
  have hdvd : wcG c A B ∣ c := (Nat.gcd_dvd_left (Nat.gcd c A) B).trans (Nat.gcd_dvd_left c A)
  have h : 0 < c / wcG c A B := Nat.div_pos (Nat.le_of_dvd hc0 hdvd) hG1
  exact h

/-- First coordinate of a vector in the box is bounded by `t` in absolute value. -/
lemma coordinate₁_natAbs_le {t : ℕ} {w : ℤ × ℤ} (hw : w ∈ wcBox t) : w.1.natAbs ≤ t := by
  simp only [wcBox, Finset.mem_product, Finset.mem_Icc] at hw
  have h : |w.1| ≤ (t : ℤ) := abs_le.mpr hw.1
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- Second coordinate of a vector in the box is bounded by `t` in absolute value. -/
lemma coordinate₂_natAbs_le {t : ℕ} {w : ℤ × ℤ} (hw : w ∈ wcBox t) : w.2.natAbs ≤ t := by
  simp only [wcBox, Finset.mem_product, Finset.mem_Icc] at hw
  have h : |w.2| ≤ (t : ℤ) := abs_le.mpr hw.2
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- Sup-norm of a vector in the box is at most `t`. -/
lemma wcSup_le_of_mem_wcBox {t : ℕ} {w : ℤ × ℤ} (hw : w ∈ wcBox t) : wcSup w ≤ t :=
  max_le (coordinate₁_natAbs_le hw) (coordinate₂_natAbs_le hw)

/-- `wcDet` is additive in its second argument. -/
lemma wcDet_sub (v w w' : ℤ × ℤ) : wcDet v (w - w') = wcDet v w - wcDet v w' := by
  simp only [wcDet, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `wcInL` is closed under subtraction. -/
lemma wcInL_sub {c A B : ℕ} {w w' : ℤ × ℤ} (hw : wcInL c A B w) (hw' : wcInL c A B w') :
    wcInL c A B (w - w') := by
  obtain ⟨k, hk⟩ := hw
  obtain ⟨k', hk'⟩ := hw'
  refine ⟨k - k', ?_⟩
  simp only [Prod.fst_sub, Prod.snd_sub]
  have e : (A : ℤ) * (w.1 - w'.1) - (B : ℤ) * (w.2 - w'.2)
      = ((A : ℤ) * w.1 - (B : ℤ) * w.2) - ((A : ℤ) * w'.1 - (B : ℤ) * w'.2) := by ring
  rw [e, hk, hk']
  ring

end

/-! ## The main theorem -/

/-- **Point count off the shortest-vector line.**

`L = {w : c ∣ A w₁ - B w₂}` is a sublattice of `ℤ²` of index `wcI c A B`; `v ∈ L`, `v ≠ 0`, has
minimal sup-norm `λ = wcSup v`. Then the number of `w ∈ L` with `|w|∞ ≤ t` and `det(v,w) ≠ 0` is at
most `40 t² / I`.

PROOF ROUTE (all steps elementary):
* (S1) if `u, w ∈ L` then `wcI c A B ∣ wcDet u w`. Indeed `A·det = w₂(Au₁-Bu₂) - u₂(Aw₁-Bw₂)`,
  `B·det = u₁(Aw₁-Bw₂) - w₁(Au₁-Bu₂)` are both divisible by `c`, and `c ∣ c·det`, so
  `c ∣ gcd(A,B,c)·det = wcG c A B · det`; divide by `gcd`. Use Bézout twice for
  `gcd(gcd A B) c = αA + βB + γc`.
* (S2) if `z ∈ L` and `wcDet v z = 0` then `z = k • v` for some `k : ℤ`
  (see `wc_minVec_and_parallel`; reproduce the argument here).
* Group the counted set by the fibre `m = wcDet v ·`. Each nonempty fibre is contained in a coset
  `w₀ + ℤv` (by S2 applied to differences), and choosing a coordinate `i` with `|v_i| = λ` makes
  `w ↦ w_i` injective on the fibre with image inside one arithmetic progression of step `λ` in
  `[-t,t]`, so `#fibre ≤ 2t/λ + 1`.
* The fibre labels `m = wcDet v w` are nonzero multiples of `I` with `|m| ≤ 2λt`, so there are at
  most `4λt/I` of them (counted in `ℝ`).
* If `t < λ` no nonzero `w ∈ L` has `|w|∞ ≤ t`, so the count is `0`. Otherwise `t ≥ λ`, and
  `(4λt/I)(2t/λ + 1) = 8t²/I + 4λt/I ≤ 12t²/I`. In particular the stated constant `40` has slack. -/
theorem wc_det_card_le (c A B t : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hc : 1 ≤ c) (v : ℤ × ℤ)
    (hvL : wcInL c A B v) (hv0 : v ≠ 0)
    (hmin : ∀ w : ℤ × ℤ, wcInL c A B w → w ≠ 0 → wcSup v ≤ wcSup w) :
    (((wcBox t).filter (fun w => wcInL c A B w ∧ wcDet v w ≠ 0)).card : ℝ)
      ≤ 40 * (t : ℝ) ^ 2 / (wcI c A B : ℝ) := by
  classical
  set S : Finset (ℤ × ℤ) := (wcBox t).filter (fun w => wcInL c A B w ∧ wcDet v w ≠ 0) with hSdef
  change ((S.card : ℕ) : ℝ) ≤ 40 * (t : ℝ) ^ 2 / (wcI c A B : ℝ)
  have hSmem : ∀ w : ℤ × ℤ, w ∈ S ↔ w ∈ wcBox t ∧ wcInL c A B w ∧ wcDet v w ≠ 0 := by
    intro w
    rw [hSdef, Finset.mem_filter]
  have hIpos : 1 ≤ wcI c A B := wcI_pos hc
  have hlamp : 1 ≤ wcSup v := by
    show 1 ≤ max v.1.natAbs v.2.natAbs
    by_contra h
    simp only [not_le] at h
    have h1 : v.1.natAbs = 0 := by omega
    have h2 : v.2.natAbs = 0 := by omega
    exact hv0 (Prod.ext (Int.natAbs_eq_zero.mp h1) (Int.natAbs_eq_zero.mp h2))
  rcases lt_or_ge t (wcSup v) with hlt | hge
  · -- no nonzero lattice vector has sup-norm `≤ t`
    have hempty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      obtain ⟨hb, hL, hdet⟩ := (hSmem w).mp hw
      have hw0 : w ≠ 0 := by
        intro h
        rw [h] at hdet
        simp [wcDet] at hdet
      have h1 : wcSup v ≤ wcSup w := hmin w hL hw0
      have h2 : wcSup w ≤ t := wcSup_le_of_mem_wcBox hb
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · -- main case `t ≥ λ`
    have hlamp_le : wcSup v ≤ t := hge
    let f : ℤ × ℤ → ℤ := fun w => wcDet v w
    have hfval : ∀ w : ℤ × ℤ, f w = wcDet v w := fun w => rfl
    set M : Finset ℤ := S.image f with hMdef
    have hMaps : ∀ w ∈ S, f w ∈ M := by
      intro w hw
      rw [hMdef]
      exact Finset.mem_image_of_mem f hw
    have hcard : S.card = ∑ m ∈ M, (S.filter (fun w => f w = m)).card :=
      Finset.card_eq_sum_card_fiberwise (fun a ha => hMaps a ha)
    -- fibre bound
    have hfib : ∀ m ∈ M, ((S.filter (fun w => f w = m)).card : ℝ)
        ≤ 2 * (t : ℝ) / (wcSup v : ℝ) + 1 := by
      intro m hm
      apply wc_fibre_card_le t v hv0
      · intro w hw
        rw [Finset.mem_filter] at hw
        exact (hSmem w).mp hw.1 |>.1
      · intro w hw w' hw'
        rw [Finset.mem_filter] at hw hw'
        obtain ⟨hwS, hwm⟩ := hw
        obtain ⟨hw'S, hw'm⟩ := hw'
        have hLw : wcInL c A B w := ((hSmem w).mp hwS).2.1
        have hLw' : wcInL c A B w' := ((hSmem w').mp hw'S).2.1
        have hzero : wcDet v (w - w') = 0 := by
          have h1 : f w = m := hwm
          have h2 : f w' = m := hw'm
          rw [hfval w] at h1
          rw [hfval w'] at h2
          rw [wcDet_sub, h1, h2, sub_self]
        obtain ⟨k, hk⟩ :=
          wc_parallel_of_min c A B v (w - w') hvL hv0 hmin (wcInL_sub hLw hLw') hzero
        have hcoords : w - w' = (w.1 - w'.1, w.2 - w'.2) := Prod.mk_sub_mk w.1 w'.1 w.2 w'.2
        rw [hcoords] at hk
        exact ⟨k, (Prod.mk.injEq _ _ _ _).mp hk⟩
    -- the fibre labels
    have hMdvd : ∀ m ∈ M, (wcI c A B : ℤ) ∣ m := by
      intro m hm
      rw [hMdef, Finset.mem_image] at hm
      obtain ⟨w, hwS, hwm⟩ := hm
      rw [hfval w] at hwm
      rw [← hwm]
      exact wcI_dvd_wcDet c A B hc v w hvL ((hSmem w).mp hwS).2.1
    have hMne : ∀ m ∈ M, m ≠ 0 := by
      intro m hm
      rw [hMdef, Finset.mem_image] at hm
      obtain ⟨w, hwS, hwm⟩ := hm
      rw [hfval w] at hwm
      rw [← hwm]
      exact ((hSmem w).mp hwS).2.2
    have hMabs : ∀ m ∈ M, m.natAbs ≤ 2 * wcSup v * t := by
      intro m hm
      rw [hMdef, Finset.mem_image] at hm
      obtain ⟨w, hwS, hwm⟩ := hm
      rw [hfval w] at hwm
      rw [← hwm]
      have hb : w ∈ wcBox t := (hSmem w).mp hwS |>.1
      have h1 : w.1.natAbs ≤ t := coordinate₁_natAbs_le hb
      have h2 : w.2.natAbs ≤ t := coordinate₂_natAbs_le hb
      have hv1 : v.1.natAbs ≤ wcSup v := le_max_left _ _
      have hv2 : v.2.natAbs ≤ wcSup v := le_max_right _ _
      calc (wcDet v w).natAbs
          = (v.1 * w.2 - v.2 * w.1).natAbs := rfl
        _ ≤ (v.1 * w.2).natAbs + (v.2 * w.1).natAbs := Int.natAbs_sub_le _ _
        _ = v.1.natAbs * w.2.natAbs + v.2.natAbs * w.1.natAbs := by
              rw [Int.natAbs_mul, Int.natAbs_mul]
        _ ≤ wcSup v * t + wcSup v * t :=
              Nat.add_le_add (Nat.mul_le_mul hv1 h2) (Nat.mul_le_mul hv2 h1)
        _ = 2 * wcSup v * t := by ring
    have hMcard : (M.card : ℝ) ≤ 2 * ((2 * wcSup v * t : ℕ) : ℝ) / (wcI c A B : ℝ) :=
      wc_det_image_card_le (wcI c A B) (2 * wcSup v * t) hIpos M hMdvd hMne hMabs
    -- assembly
    have hsecond : (0 : ℝ) ≤ 2 * (t : ℝ) / (wcSup v : ℝ) + 1 := by
      have : (0 : ℝ) < (wcSup v : ℝ) := by exact_mod_cast hlamp
      positivity
    have hsum_eq : (S.card : ℝ) = ∑ m ∈ M, ((S.filter (fun w => f w = m)).card : ℝ) := by
      rw [hcard]
      push_cast
      rfl
    have hL1 : (1 : ℝ) ≤ (wcSup v : ℝ) := by exact_mod_cast hlamp
    have hLT : (wcSup v : ℝ) ≤ (t : ℝ) := by exact_mod_cast hlamp_le
    have hi1 : (1 : ℝ) ≤ (wcI c A B : ℝ) := by exact_mod_cast hIpos
    have hL0 : (0 : ℝ) < (wcSup v : ℝ) := by linarith
    have hi0 : (0 : ℝ) < (wcI c A B : ℝ) := by linarith
    have hcast : ((2 * wcSup v * t : ℕ) : ℝ) = 2 * (wcSup v : ℝ) * (t : ℝ) := by
      push_cast
      ring
    calc (S.card : ℝ)
        = ∑ m ∈ M, ((S.filter (fun w => f w = m)).card : ℝ) := hsum_eq
      _ ≤ ∑ m ∈ M, (2 * (t : ℝ) / (wcSup v : ℝ) + 1) := Finset.sum_le_sum hfib
      _ = (M.card : ℝ) * (2 * (t : ℝ) / (wcSup v : ℝ) + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * ((2 * wcSup v * t : ℕ) : ℝ) / (wcI c A B : ℝ))
            * (2 * (t : ℝ) / (wcSup v : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hMcard hsecond
      _ ≤ 40 * (t : ℝ) ^ 2 / (wcI c A B : ℝ) := by
            rw [hcast, div_mul_eq_mul_div]
            apply div_le_div_of_nonneg_right _ (le_of_lt hi0)
            have hkey : 2 * (2 * (wcSup v : ℝ) * (t : ℝ))
                * (2 * (t : ℝ) / (wcSup v : ℝ) + 1) ≤ 40 * (t : ℝ) ^ 2 := by
              have hne : (wcSup v : ℝ) ≠ 0 := ne_of_gt hL0
              field_simp
              nlinarith [hLT, hL0, hL1]
            linarith [hkey]

end Work.FIArea2.R6
