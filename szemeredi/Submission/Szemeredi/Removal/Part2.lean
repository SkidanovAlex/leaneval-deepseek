import Mathlib
import Submission.Szemeredi.Removal.Partite
import Submission.Szemeredi.Removal.Main2
import Submission.Commons.Combinatorics.Finset.card_filter_succAbove
import Submission.Commons.Combinatorics.Finset.card_le_mul_card_image_succAbove

/-!
# The partite corollary of the hypergraph removal lemma

Deduction of `Szemeredi.SimplexRemovalProgrammeD d` (for `d ≥ 1`) from the σ-algebra form of
the hypergraph removal lemma.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Szemeredi

section Partite

variable {d : ℕ} {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem prod_sum_Fsimp (E : Fin (d+1) → Finset (Fin d → G)) :
    (∑ x : Pt (VG d G), ∏ e ∈ HdC d, SigAlg.indicator (Fsimp E e) x)
      = ((simplexFinsetD E).card : ℝ) := by
  classical
  have h1 : ∀ x : Pt (VG d G), (∏ e ∈ HdC d, SigAlg.indicator (Fsimp E e) x)
      = (if IsSimplexD E x then (1:ℝ) else 0) := by
    intro x
    by_cases h : IsSimplexD E x
    · rw [prod_Fsimp_pos E x h, if_pos h]
    · rw [prod_Fsimp_zero E x h, if_neg h]
  rw [Finset.sum_congr rfl (fun x _ => h1 x)]
  rw [Finset.sum_boole]
  rfl

theorem card_Pt : Fintype.card (Pt (VG d G)) = (Fintype.card G) ^ (d+1) := by
  rw [Fintype.card_pi]
  have h : (∏ i : Fin (d+1), Fintype.card (VG d G i))
      = ∏ _i : Fin (d+1), Fintype.card G :=
    Finset.prod_congr rfl (fun i _ => rfl)
  rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem Fsimp_card (E : Fin (d+1) → Finset (Fin d → G)) (j : Fin (d+1)) :
    (Fsimp E (Finset.univ.erase j)).card = (E j).card * Fintype.card G := by
  rw [Fsimp_of_erase]
  exact Commons.Combinatorics.Finset.card_filter_succAbove d j (E j)

/-- Projecting the `j`-faces of a subset of the `j`-lift lands in `E j`. -/
theorem image_faceD_subset (E : Fin (d+1) → Finset (Fin d → G)) {j : Fin (d+1)}
    {S : Finset (Pt (VG d G))} (hSsub : S ⊆ Fsimp E (Finset.univ.erase j)) :
    S.image (fun x : Pt (VG d G) => faceD j x) ⊆ E j := by
  intro p hp
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
  exact (mem_Fsimp.mp (hSsub hxS)) j rfl

/-- For a `coord`-measurable set, lifting the projection to the `j`-face recovers the set. -/
theorem filter_image_faceD_eq {j : Fin (d+1)} {S : Finset (Pt (VG d G))}
    (hSmeas : (coord (V := VG d G) (Finset.univ.erase j)).IsMeas S) :
    Finset.univ.filter (fun x : Pt (VG d G) =>
        faceD j x ∈ S.image (fun x : Pt (VG d G) => faceD j x)) = S := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    obtain ⟨y, hyS, hyx⟩ := Finset.mem_image.mp hx
    have hiff := (coord_isMeas_iff.mp hSmeas) y x (fun i hi => ?_)
    exact hiff.mpr hyS
    have hi' : i ≠ j := (Finset.mem_erase.mp hi).1
    obtain ⟨k, hk⟩ : ∃ k : Fin d, j.succAbove k = i := by
      refine ⟨(finSuccAboveEquiv j).symm ⟨i, hi'⟩, ?_⟩
      exact congrArg Subtype.val ((finSuccAboveEquiv j).apply_symm_apply ⟨i, hi'⟩)
    rw [← hk]
    exact (congrFun hyx k).symm
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- The deletion bound for a single face. -/
theorem card_sub_le (E : Fin (d+1) → Finset (Fin d → G)) {j : Fin (d+1)}
    {S : Finset (Pt (VG d G))}
    (hSmeas : (coord (V := VG d G) (Finset.univ.erase j)).IsMeas S)
    (hSsub : S ⊆ Fsimp E (Finset.univ.erase j)) :
    ((E j).card : ℝ) - ((S.image (fun x : Pt (VG d G) => faceD j x)).card : ℝ)
      ≤ (((Fsimp E (Finset.univ.erase j)).card : ℝ) - (S.card : ℝ)) / (Fintype.card G : ℝ) := by
  have hGpos : (0 : ℝ) < Fintype.card G := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨(0 : G)⟩
    exact_mod_cast this
  have h1 : ((Fsimp E (Finset.univ.erase j)).card : ℝ)
      = ((E j).card : ℝ) * (Fintype.card G : ℝ) := by
    rw [Fsimp_card]
    push_cast
    ring
  have h2 : (S.card : ℝ)
      ≤ ((S.image (fun x : Pt (VG d G) => faceD j x)).card : ℝ) * (Fintype.card G : ℝ) := by
    have h := Commons.Combinatorics.Finset.card_le_mul_card_image_succAbove d j S
    exact_mod_cast h
  rw [h1, le_div_iff₀ hGpos]
  nlinarith [h2]


theorem erase_card (j : Fin (d+1)) :
    (Finset.univ.erase j : Finset (Fin (d+1))).card = d := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
  simp

end Partite

/-- **The partite corollary**: the simplex removal lemma in dimension `d ≥ 1`, deduced from the
σ-algebra form of the hypergraph removal lemma. -/
theorem simplexRemovalProgrammeD_of_main2 (d : ℕ) (hd : 1 ≤ d) : SimplexRemovalProgrammeD d := by
  intro ε hε
  set εrm : ℝ := ε * (((d+1) ^ (d-1) : ℕ) : ℝ) / 2 with hεrmdef
  have hεrm : 0 < εrm := by
    rw [hεrmdef]; positivity
  obtain ⟨δ, hδpos, hrem⟩ := Removal.hypergraph_removal_complete d hd εrm hεrm
  refine ⟨δ / ((((d+1) ^ (d+1) : ℕ)) : ℝ), by positivity, 1, ?_⟩
  intro G _ _ _ hG E hfar
  haveI : Nonempty G := ⟨0⟩
  have hHg : ∀ j : Fin (d+1), (Finset.univ.erase j : Finset (Fin (d+1))).card = d := erase_card
  have hHdC : ∀ e ∈ HdC d, e.card = d := fun e he => mem_HdC.mp he
  have hreindex : HdC d = (Finset.univ : Finset (Fin (d+1))).image fun j => Finset.univ.erase j := by
    ext e
    rw [mem_HdC, Finset.mem_image]
    constructor
    · intro he
      obtain ⟨j, hj, -⟩ := exists_erase_of_card e he
      exact ⟨j, Finset.mem_univ j, hj.symm⟩
    · rintro ⟨j, -, rfl⟩
      exact erase_card j
  by_cases hle : avg (fun x : Pt (VG d G) =>
      ∏ e ∈ HdC d, SigAlg.indicator (Fsimp E e) x) ≤ δ
  · exfalso
    obtain ⟨E', hE'sub, hE'meas, hE'err, hE'empty⟩ :=
      hrem (Fsimp E) (fun e _ => Fsimp_isMeas E e) hle
    set E'' : Fin (d+1) → Finset (Fin d → G) :=
      fun j => (E' (Finset.univ.erase j)).image (fun x : Pt (VG d G) => faceD j x) with hE''def
    refine hfar ⟨E'', fun j => ?_, ?_, ?_⟩
    · rw [hE''def]
      exact image_faceD_subset E (hE'sub _ (hHg j))
    · intro w hw
      have hw' : ∀ j : Fin (d+1), w ∈ E' (Finset.univ.erase j) := by
        intro j
        have h1' : faceD j w ∈ (E' (Finset.univ.erase j)).image
            (fun x : Pt (VG d G) => faceD j x) := by
          have h := hw j
          rwa [hE''def] at h
        have h1 : w ∈ Finset.univ.filter (fun x : Pt (VG d G) =>
            faceD j x ∈ (E' (Finset.univ.erase j)).image (fun x : Pt (VG d G) => faceD j x)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ w, h1'⟩
        exact (filter_image_faceD_eq (j := j) (hE'meas _ (hHg j))) ▸ h1
      obtain ⟨e, he, hne⟩ := hE'empty w
      obtain ⟨j, hje, -⟩ := exists_erase_of_card e he
      exact hne (hje ▸ hw' j)
    · have h1 : ∀ j : Fin (d+1), ((E j).card : ℝ) - ((E'' j).card : ℝ)
          ≤ (((Fsimp E (Finset.univ.erase j)).card : ℝ) - ((E' (Finset.univ.erase j)).card : ℝ))
              / (Fintype.card G : ℝ) := by
        intro j
        rw [hE''def]
        exact card_sub_le E (hE'meas _ (hHg j)) (hE'sub _ (hHg j))
      have h2 : (∑ j : Fin (d+1), (((Fsimp E (Finset.univ.erase j)).card : ℝ)
            - ((E' (Finset.univ.erase j)).card : ℝ)))
          = ∑ e ∈ HdC d, (((Fsimp E e).card : ℝ) - ((E' e).card : ℝ)) := by
        rw [hreindex, Finset.sum_image]
        intro a _ b _ hab
        exact erase_inj hab
      have h3 : ∀ e ∈ HdC d, (((Fsimp E e).card : ℝ) - ((E' e).card : ℝ))
          ≤ εrm * (Fintype.card (Pt (VG d G)) : ℝ) := by
        intro e he
        have hcard : (((Fsimp E e) \ (E' e)).card : ℝ)
            = ((Fsimp E e).card : ℝ) - ((E' e).card : ℝ) := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hE'sub e (hHdC e he)),
            Nat.cast_sub (Finset.card_le_card (hE'sub e (hHdC e he)))]
        rw [← hcard]
        rw [show (((Fsimp E e) \ (E' e)).card : ℝ)
            = avg (SigAlg.indicator (Fsimp E e \ E' e))
              * (Fintype.card (Pt (VG d G)) : ℝ) from by
          rw [avg_indicator]
          field_simp]
        exact mul_le_mul_of_nonneg_right (hE'err e (hHdC e he)) (Nat.cast_nonneg _)
      have h4 : (∑ e ∈ HdC d, (((Fsimp E e).card : ℝ) - ((E' e).card : ℝ)))
          ≤ ((HdC d).card : ℝ) * (εrm * (Fintype.card (Pt (VG d G)) : ℝ)) := by
        calc (∑ e ∈ HdC d, (((Fsimp E e).card : ℝ) - ((E' e).card : ℝ)))
            ≤ ∑ _e ∈ HdC d, (εrm * (Fintype.card (Pt (VG d G)) : ℝ)) := Finset.sum_le_sum h3
          _ = ((HdC d).card : ℝ) * (εrm * (Fintype.card (Pt (VG d G)) : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have h5 : ((HdC d).card : ℝ) = (d+1 : ℝ) := by
        rw [hreindex, Finset.card_image_of_injOn]
        · simp
        · intro a _ b _ hab
          exact erase_inj hab
      have h6 : (Fintype.card (Pt (VG d G)) : ℝ) = (Fintype.card G : ℝ) ^ (d+1) := by
        rw [card_Pt]
        push_cast
        ring
      have hGpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
        have hpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨(0 : G)⟩
        exact_mod_cast hpos
      have hsum : (∑ j : Fin (d+1), (((E j).card : ℝ) - ((E'' j).card : ℝ)))
          ≤ (d+1 : ℝ) * εrm * (Fintype.card G : ℝ) ^ d := by
        have hsum1 : (∑ j : Fin (d+1), (((E j).card : ℝ) - ((E'' j).card : ℝ)))
            ≤ (∑ j : Fin (d+1), (((Fsimp E (Finset.univ.erase j)).card : ℝ)
                - ((E' (Finset.univ.erase j)).card : ℝ))) / (Fintype.card G : ℝ) := by
          rw [Finset.sum_div]
          exact Finset.sum_le_sum (fun j _ => h1 j)
        rw [h2] at hsum1
        have hbound : (∑ e ∈ HdC d, (((Fsimp E e).card : ℝ) - ((E' e).card : ℝ)))
            ≤ (d+1 : ℝ) * (εrm * ((Fintype.card G : ℝ) ^ (d+1))) := by
          calc (∑ e ∈ HdC d, (((Fsimp E e).card : ℝ) - ((E' e).card : ℝ)))
              ≤ ((HdC d).card : ℝ) * (εrm * (Fintype.card (Pt (VG d G)) : ℝ)) := h4
            _ = (d+1 : ℝ) * (εrm * ((Fintype.card G : ℝ) ^ (d+1))) := by rw [h5, h6]
        have hfinal : (d+1 : ℝ) * (εrm * ((Fintype.card G : ℝ) ^ (d+1))) / (Fintype.card G : ℝ)
            = (d+1 : ℝ) * εrm * (Fintype.card G : ℝ) ^ d := by
          field_simp
          ring
        rw [← hfinal]
        exact le_trans hsum1 (div_le_div_of_nonneg_right hbound hGpos.le)
      have hlt2 : ((d : ℝ) + 1) * εrm * (Fintype.card G : ℝ) ^ d
          < ε * (((d + 1) * Fintype.card G : ℕ) : ℝ) ^ d := by
        have h1 : (((d + 1) * Fintype.card G : ℕ) : ℝ) ^ d
            = ((((d+1)^d : ℕ)) : ℝ) * (Fintype.card G : ℝ) ^ d := by
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
          rw [mul_pow]
        have h2 : ((((d+1)^d : ℕ)) : ℝ) = ((d : ℝ) + 1) * ((((d+1)^(d-1) : ℕ)) : ℝ) := by
          have h : ((d+1)^d : ℕ) = (d+1)^(d-1) * (d+1) := by
            rw [← pow_succ]
            congr 1
            omega
          rw [h]
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
          ring
        rw [h1, h2, hεrmdef]
        have hpos : (0 : ℝ) < ε * ((((d+1)^(d-1) : ℕ)) : ℝ) * ((d : ℝ) + 1)
            * (Fintype.card G : ℝ) ^ d := by
          have h3 : (0 : ℝ) < ((((d+1)^(d-1) : ℕ)) : ℝ) := by positivity
          have h4 : (0 : ℝ) < ((d : ℝ) + 1) := by positivity
          have h5 : (0 : ℝ) < (Fintype.card G : ℝ) ^ d := by positivity
          positivity
        nlinarith [hpos]
      linarith [hsum, hlt2]
  · push_neg at hle
    have hden : (0 : ℝ) < (((d+1) ^ (d+1) : ℕ) : ℝ) := by positivity
    have havg : avg (fun x : Pt (VG d G) => ∏ e ∈ HdC d, SigAlg.indicator (Fsimp E e) x)
        = ((simplexFinsetD E).card : ℝ) / (Fintype.card (Pt (VG d G)) : ℝ) := by
      rw [Removal.SigAlg.avg, prod_sum_Fsimp]
    have hPtpos : (0 : ℝ) < (Fintype.card (Pt (VG d G)) : ℝ) := by
      have hpos : 0 < Fintype.card (Pt (VG d G)) := Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
      exact_mod_cast hpos
    have hsimp : ((simplexFinsetD E).card : ℝ)
        = avg (fun x : Pt (VG d G) => ∏ e ∈ HdC d, SigAlg.indicator (Fsimp E e) x)
          * (Fintype.card (Pt (VG d G)) : ℝ) := by
      rw [havg]
      field_simp
    rw [hsimp]
    have hcast : (((d + 1) * Fintype.card G : ℕ) : ℝ) ^ (d+1)
        = (((d+1)^(d+1) : ℕ) : ℝ) * (Fintype.card (Pt (VG d G)) : ℝ) := by
      rw [card_Pt]
      push_cast
      rw [mul_pow]
    rw [hcast]
    have h1 : δ * (Fintype.card (Pt (VG d G)) : ℝ)
        < avg (fun x : Pt (VG d G) => ∏ e ∈ HdC d, SigAlg.indicator (Fsimp E e) x)
          * (Fintype.card (Pt (VG d G)) : ℝ) :=
      mul_lt_mul_of_pos_right hle hPtpos
    have h2 : δ / (((d+1)^(d+1) : ℕ) : ℝ)
          * ((((d+1)^(d+1) : ℕ) : ℝ) * (Fintype.card (Pt (VG d G)) : ℝ))
        = δ * (Fintype.card (Pt (VG d G)) : ℝ) := by
      field_simp
    rw [h2]
    exact h1.le

end Szemeredi
