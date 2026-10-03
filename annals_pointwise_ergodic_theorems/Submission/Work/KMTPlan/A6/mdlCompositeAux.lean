/-
# Auxiliary lemmas for `mdlComposite_uniformSigns_le`

This module collects the elementary facts about narrowly supported functions, the periodisation
of the Ionescu--Wainger cutoff `η_{≤k}` at non-positive heights, and the cardinality of the
arithmetic frequency sets `(ℚ/ℤ)_{≤l}`, that the uniform-in-signs composite estimate
`Work.KMTPlan.A6.mdlComposite_uniformSigns_le` and the model bound
`Work.KMTPlan.A6.mdlF_two_le_of_pred` rest on.

* `summable_shift_of_narrow` — for `φ` supported in `ℝ_{≤k}` with `2^k < 1/2`, the translate
  family `j ↦ φ (x + j)` is summable (at most one translate is non-zero).
* `memLp_periodize_of_narrow` — the periodisation of such a `φ` is in `L^∞(ℝ/ℤ)`.
* `norm_periodize_etaCut_le_two`, `norm_periodize_etaCut_le_one` — the sharp sup norms of the
  periodisation of the cutoff `η_{≤k}` at the heights `k ≤ 0` (at most two translates of
  `η(·/2^k)` can meet a point of `[0,1)`, and at most one when `2^{k+1} ≤ 1`).
* `card_iwArithFreqs_le` — if all denominators in `P_{≤l}` are at most `Q`, then
  `#(ℚ/ℤ)_{≤l} ≤ Q²`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTPlan.A6.besselG

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-! ## Narrowly supported functions -/

/-- **Translated sums of a narrowly supported function are summable.**  If `φ` is supported in the
arc `ℝ_{≤k}` with `2^k < 1/2`, then for every `x` at most one of the translates `φ (x + j)`,
`j ∈ ℤ`, is non-zero (two non-zero translates would force `|j - j'| < 2 · 2^k < 1`). -/
theorem summable_shift_of_narrow {k : ℤ} (hk : (2 : ℝ) ^ k < 1 / 2) {φ : ℝ → ℂ}
    (hφ : ∀ x : ℝ, φ x ≠ 0 → x ∈ realArc k) (x : ℝ) :
    Summable fun j : ℤ => φ (x + j) := by
  have h2 : (2 : ℝ) ^ k * 2 < 1 := by linarith
  by_cases h : ∃ j : ℤ, φ (x + j) ≠ 0
  · obtain ⟨j₀, hj₀⟩ := h
    refine summable_of_ne_finset_zero (s := {j₀}) fun j hj => ?_
    by_contra hne
    have h1 : x + j ∈ realArc k := hφ _ hne
    have h2' : x + j₀ ∈ realArc k := hφ _ hj₀
    rw [realArc, Set.mem_Icc] at h1 h2'
    have hcast : ((j - j₀ : ℤ) : ℝ) = (x + j) - (x + j₀) := by push_cast; ring
    have hlt : |((j - j₀ : ℤ) : ℝ)| < 1 := by
      rw [abs_lt]
      constructor
      · rw [hcast]; linarith [h1.1, h2'.2, h2]
      · rw [hcast]; linarith [h1.2, h2'.1, h2]
    have hlt' : |(j - j₀ : ℤ)| < 1 := by exact_mod_cast hlt
    have h1' : (-1 : ℤ) < j - j₀ := (abs_lt.mp hlt').1
    have h2'' : (j - j₀ : ℤ) < 1 := (abs_lt.mp hlt').2
    have hzero : j - j₀ = 0 := by omega
    exact hj (by rw [Finset.mem_singleton]; omega)
  · push_neg at h
    exact summable_of_ne_finset_zero (s := ∅) (by simp [h])

/-- **The periodisation of a narrowly supported bounded measurable function is in `L^∞`.** -/
theorem memLp_periodize_of_narrow {k : ℤ} (hk : (2 : ℝ) ^ k < 1 / 2) {φ : ℝ → ℂ}
    (hm : Measurable φ) (hφ : ∀ x : ℝ, φ x ≠ 0 → x ∈ realArc k) {C : ℝ}
    (hC : ∀ x : ℝ, ‖φ x‖ ≤ C) :
    MemLp (periodize φ) ⊤ circleMeasure :=
  memLp_periodize hm (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) k))
    (fun x hx => by
      by_contra hne
      have h1 : x ∈ realArc k := hφ x hne
      rw [realArc, Set.mem_Icc] at h1
      have h2 : |x| ≤ (2 : ℝ) ^ k := abs_le.mpr ⟨h1.1, h1.2⟩
      linarith)
    hC

/-! ## The periodisation of the cutoff at non-positive heights -/

/-- The support of `etaCut kmtEta k` for `k ≤ 0` meets at most the two translates `j = -1, 0`
of a point `x ∈ [0,1)`. -/
theorem etaCut_shift_eq_zero_of_notMem {k : ℤ} (hk : (2 : ℝ) ^ k ≤ 1) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) {j : ℤ} (hj1 : j ≠ -1) (hj0 : j ≠ 0) :
    etaCut Work.KMTContract.kmtEta k (x + j) = 0 := by
  refine Work.KMTAreas.A7.etaCut_eq_zero_of_le ?_
  rcases lt_trichotomy j 0 with h | h | h
  · -- `j ≤ -2`: then `x + j ≤ x - 2 < -1`, so `|x + j| ≥ 1 ≥ 2^k`
    have hj2 : (2 : ℤ) ≤ -j := by omega
    have hj2' : (2 : ℝ) ≤ -((j : ℤ) : ℝ) := by exact_mod_cast hj2
    push_cast at hj2'
    have hle : x + (j : ℝ) ≤ -1 := by linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  · exact absurd h hj0
  · -- `j ≥ 1`: then `x + j ≥ 1 ≥ 2^k`
    have hj1' : (1 : ℤ) ≤ j := by omega
    have hj1'' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1'
    have hge : 1 ≤ x + (j : ℝ) := by linarith
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **The periodisation of `η_{≤k}` is bounded by `2` for `k ≤ 0`**: at most two of its
translates can meet a point of `[0,1)`, and each is bounded by `η ≤ 1`. -/
theorem norm_periodize_etaCut_le_two (k : ℤ) (hk : k ≤ 0) (ξ : AddCircle (1 : ℝ)) :
    ‖periodize (etaCut Work.KMTContract.kmtEta k) ξ‖ ≤ 2 := by
  have hk1 : (2 : ℝ) ^ k ≤ 1 := by
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    simpa using this
  set v : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hv
  have hx0 : 0 ≤ v := (AddCircle.equivIco (1 : ℝ) 0 ξ).prop.1
  have hx1 : v < 1 := by
    rw [hv]; simpa using (AddCircle.equivIco (1 : ℝ) 0 ξ).prop.2
  have hshift : ∀ j : ℤ, j ∉ ({-1, 0} : Finset ℤ) →
      etaCut Work.KMTContract.kmtEta k ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j) = 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact etaCut_shift_eq_zero_of_notMem hk1 hx0 hx1 hj.1 hj.2
  have hsum : periodize (etaCut Work.KMTContract.kmtEta k) ξ
      = ∑ j ∈ ({-1, 0} : Finset ℤ),
          etaCut Work.KMTContract.kmtEta k ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j) :=
    tsum_eq_sum hshift
  rw [hsum]
  calc ‖∑ j ∈ ({-1, 0} : Finset ℤ),
          etaCut Work.KMTContract.kmtEta k ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j)‖
      ≤ ∑ j ∈ ({-1, 0} : Finset ℤ),
          ‖etaCut Work.KMTContract.kmtEta k ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ ({-1, 0} : Finset ℤ), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => norm_etaCut_le_one k _
    _ = 2 := by norm_num

/-- **The periodisation of `η_{≤k}` is bounded by `1` when `2^{k+1} ≤ 1`**: the two candidate
translates cannot both be non-zero. -/
theorem norm_periodize_etaCut_le_one {k : ℤ} (hk : (2 : ℝ) ^ (k + 1) ≤ 1)
    (ξ : AddCircle (1 : ℝ)) :
    ‖periodize (etaCut Work.KMTContract.kmtEta k) ξ‖ ≤ 1 := by
  have hsplit : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
  have hkpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num : (0 : ℝ) < 2) k
  have hk1 : (2 : ℝ) ^ k ≤ 1 := by
    have hlt : 2 * (2 : ℝ) ^ k ≤ 1 := by rw [← hsplit]; exact hk
    linarith
  set v : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hv
  have hx0 : 0 ≤ v := (AddCircle.equivIco (1 : ℝ) 0 ξ).prop.1
  have hx1 : v < 1 := by
    rw [hv]; simpa using (AddCircle.equivIco (1 : ℝ) 0 ξ).prop.2
  have hshift : ∀ j : ℤ, j ∉ ({-1, 0} : Finset ℤ) →
      etaCut Work.KMTContract.kmtEta k ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j) = 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact etaCut_shift_eq_zero_of_notMem hk1 hx0 hx1 hj.1 hj.2
  have hsum : periodize (etaCut Work.KMTContract.kmtEta k) ξ
      = etaCut Work.KMTContract.kmtEta k (v + ((-1 : ℤ) : ℝ))
        + etaCut Work.KMTContract.kmtEta k v := by
    rw [periodize, tsum_eq_sum (s := ({-1, 0} : Finset ℤ)) hshift,
      Finset.sum_insert (by decide), Finset.sum_singleton]
    push_cast
    rw [add_zero]
  have hkey : etaCut Work.KMTContract.kmtEta k v = 0
      ∨ etaCut Work.KMTContract.kmtEta k (v + ((-1 : ℤ) : ℝ)) = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hA, hB⟩ := hcon
    have ha : |v| < (2 : ℝ) ^ k := by
      by_contra hc
      push_neg at hc
      exact hA (Work.KMTAreas.A7.etaCut_eq_zero_of_le hc)
    have hb : |v + ((-1 : ℤ) : ℝ)| < (2 : ℝ) ^ k := by
      by_contra hc
      push_neg at hc
      exact hB (Work.KMTAreas.A7.etaCut_eq_zero_of_le hc)
    have hcast : v + ((-1 : ℤ) : ℝ) = v - 1 := by push_cast; ring
    rw [hcast, abs_lt] at hb
    rw [abs_lt] at ha
    have hhalf : (2 : ℝ) ^ k ≤ 1 / 2 := by linarith
    linarith [ha.1, ha.2, hb.1, hb.2, hhalf]
  rw [hsum]
  rcases hkey with hkey | hkey
  · rw [hkey, add_zero]
    exact norm_etaCut_le_one k _
  · rw [hkey, zero_add]
    exact norm_etaCut_le_one k _

/-! ## Cardinality of the arithmetic frequency sets -/

/-- **If every denominator in `P_{≤l}` is at most `Q`, then `#(ℚ/ℤ)_{≤l} ≤ Q²`.**  The arithmetic
frequency set is the union of the `q`-torsion subgroups over `q ∈ P_{≤l}`; each contributes at
most `q ≤ Q` points and there are at most `Q` denominators. -/
theorem card_iwArithFreqs_le (ρ : ℝ) (l Q : ℕ)
    (hQ : ∀ q ∈ iwP ρ l, q ≤ Q) :
    (iwArithFreqs ρ l).card ≤ Q * Q := by
  classical
  have hsub : iwP ρ l ⊆ Finset.Icc 1 Q := by
    intro q hq
    rw [Finset.mem_Icc]
    exact ⟨pos_of_mem_iwP hq, hQ q hq⟩
  calc (iwArithFreqs ρ l).card
      = ((iwP ρ l).biUnion fun q => (Finset.range q).image
          (fun a : ℕ => (((a : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))).card := rfl
    _ ≤ ∑ q ∈ iwP ρ l, ((Finset.range q).image
          (fun a : ℕ => (((a : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ q ∈ iwP ρ l, q := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact le_trans Finset.card_image_le (le_of_eq (Finset.card_range q))
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, Q :=
        Finset.sum_le_sum fun q hq => (Finset.mem_Icc.mp hq).2
    _ = Q * Q := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp

end

end Work.KMTPlan.A6
