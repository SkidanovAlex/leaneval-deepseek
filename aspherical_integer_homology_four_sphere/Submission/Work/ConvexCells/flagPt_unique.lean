import Mathlib
import Submission.Work.ConvexCells.Basic
import Submission.Work.ConvexCells.exists_exit
import Submission.Work.ConvexCells.tightAt_flagPt
import Submission.Work.ConvexCells.FlagPt_mem

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ConvexCells

open scoped BigOperators
open PolytopeData

/-! ### Generic list/`Fin` index helpers -/

/-- If `i < l.dropLast.length` then `i < l.length`. -/
theorem lt_length_of_lt_dropLast {α : Type*} {l : List α} {i : ℕ} (h : i < l.dropLast.length) :
    i < l.length := by rw [List.length_dropLast] at h; omega

/-- If `i < l.length - 1` then `i < l.dropLast.length`. -/
theorem lt_dropLast_of_lt_length {α : Type*} {l : List α} {i : ℕ} (h : i < l.length - 1) :
    i < l.dropLast.length := by rw [List.length_dropLast]; exact h

/-- Split a sum over `Fin n` into a sum over `Fin (n-1)` plus the last term. -/
theorem sum_univ_eq_sum_erase_last {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 0 < n)
    (f : Fin n → M) :
    ∑ i : Fin n, f i =
      (∑ i : Fin (n - 1), f ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩) + f ⟨n - 1, by omega⟩ := by
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f (Finset.mem_univ ⟨n-1, by omega⟩)]
  congr 1
  · symm
    refine Finset.sum_bij (fun (a : Fin (n-1)) _ => ⟨a.val, Nat.lt_of_lt_pred a.isLt⟩) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      have := Fin.ext_iff.mp h
      simp at this
      omega
    · intro a1 ha1 a2 ha2 h
      apply Fin.ext
      simpa using Fin.ext_iff.mp h
    · intro b hb
      rw [Finset.mem_erase] at hb
      have hbne : b ≠ ⟨n-1, by omega⟩ := hb.1
      have hbv : b.val ≠ n - 1 := fun h => hbne (Fin.ext h)
      refine ⟨⟨b.val, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp
    · intro a ha
      rfl

/-- Reindex a sum indexed by `Fin l.dropLast.length` as a sum indexed by `Fin (l.length - 1)`. -/
theorem sum_dropLast_congr {M : Type*} [AddCommMonoid M] {α : Type*} (l : List α)
    (f : Fin l.length → M) :
    (∑ i : Fin l.dropLast.length, f ⟨i.val, lt_length_of_lt_dropLast i.isLt⟩)
      = ∑ i : Fin (l.length - 1), f ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  simp only [List.length_dropLast]

/-- Reindex a sum indexed by `Fin (l.length - 1)` as a sum indexed by `Fin l.dropLast.length`. -/
theorem sum_dropLast_reindex {M : Type*} [AddCommMonoid M] {α : Type*} (l : List α)
    (g : Fin l.dropLast.length → M) :
    ∑ i : Fin l.dropLast.length, g i
      = ∑ i : Fin (l.length - 1), g ⟨i.val, lt_dropLast_of_lt_length i.isLt⟩ := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  simp only [List.length_dropLast]

theorem div_smul_eq_inv_smul {d : ℕ} (a c : ℝ) (v : E d) : (a / c) • v = c⁻¹ • (a • v) := by
  rw [div_eq_mul_inv, smul_smul, mul_comm c⁻¹ a]

namespace PolytopeData
namespace FlagPt

variable {d : ℕ} {P : PolytopeData d}

theorem length_pos (s : P.FlagPt) : 0 < s.flag.length :=
  List.length_pos_of_ne_nil s.flag_ne_nil

/-- The index of the last (largest) face of a flag. -/
def lastIdx (s : P.FlagPt) : Fin s.flag.length :=
  ⟨s.flag.length - 1, by have h := List.length_pos_of_ne_nil s.flag_ne_nil; omega⟩

theorem get_lastIdx (s : P.FlagPt) : s.flag.get s.lastIdx = s.topFace := by
  unfold lastIdx topFace
  rw [List.getLast_eq_getElem, List.get_eq_getElem]

theorem get_dropLast (s : P.FlagPt) (i : Fin s.flag.dropLast.length) :
    s.flag.dropLast.get i = s.flag.get ⟨i.val, lt_length_of_lt_dropLast i.isLt⟩ := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_dropLast]

theorem wt_last_lt_one (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) : s.wt s.lastIdx < 1 := by
  have hlen : 0 < s.flag.length := List.length_pos_of_ne_nil s.flag_ne_nil
  have herase := Finset.sum_erase_add (Finset.univ : Finset (Fin s.flag.length)) s.wt
    (Finset.mem_univ s.lastIdx)
  have hpos : 0 < ∑ x ∈ (Finset.univ : Finset (Fin s.flag.length)).erase s.lastIdx, s.wt x := by
    apply Finset.sum_pos'
    · intro i hi; exact le_of_lt (s.wt_pos i)
    · refine ⟨⟨0, hlen⟩, ?_, s.wt_pos _⟩
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      have h2' : (0:ℕ) = s.flag.length - 1 := by
        have := Fin.ext_iff.mp h
        simpa only [lastIdx, Fin.val_zero, Fin.val_mk] using this
      omega
  linarith [s.wt_sum]

theorem sum_wt_dropLast (s : P.FlagPt) :
    (∑ i : Fin (s.flag.length - 1), s.wt ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩) =
      1 - s.wt s.lastIdx := by
  have hsplit := sum_univ_eq_sum_erase_last (List.length_pos_of_ne_nil s.flag_ne_nil) s.wt
  have hsum : (∑ i : Fin s.flag.length, s.wt i) = 1 := s.wt_sum
  rw [hsum] at hsplit
  have heq : s.wt ⟨s.flag.length - 1, by have h := List.length_pos_of_ne_nil s.flag_ne_nil; omega⟩ = s.wt s.lastIdx := rfl
  rw [heq] at hsplit
  linarith [hsplit]

/-- The flag point obtained by deleting the last (largest) face of a flag, with the remaining
weights rescaled so that they again sum to one. -/
noncomputable def subPt (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) : P.FlagPt where
  flag := s.flag.dropLast
  isFlag := List.Pairwise.sublist (List.dropLast_sublist s.flag) s.isFlag
  wt := fun i => s.wt ⟨i.val, lt_length_of_lt_dropLast i.isLt⟩ / (1 - s.wt s.lastIdx)
  wt_pos := fun i => div_pos (s.wt_pos _) (by have h := wt_last_lt_one s h2; linarith)
  wt_sum := by
    rw [← Finset.sum_div]
    rw [sum_dropLast_congr]
    rw [sum_wt_dropLast]
    exact div_self (by have h := wt_last_lt_one s h2; linarith)

/-- The last weight times the last face's `posR` point. -/
theorem last_term (s : P.FlagPt) :
    s.wt ⟨s.flag.length - 1, by have h := List.length_pos_of_ne_nil s.flag_ne_nil; omega⟩ •
      P.posR (s.flag.get ⟨s.flag.length - 1,
        by have h := List.length_pos_of_ne_nil s.flag_ne_nil; omega⟩)
      = s.wt s.lastIdx • P.posR s.topFace := by
  have h : (⟨s.flag.length - 1,
      by have h := List.length_pos_of_ne_nil s.flag_ne_nil; omega⟩ : Fin s.flag.length) = s.lastIdx :=
    Fin.ext rfl
  rw [h, get_lastIdx]

/-- The realization of the restriction of a flag, rescaled. -/
theorem subPt_toE' (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    (subPt s h2).toE' = (1 - s.wt s.lastIdx)⁻¹ •
      (∑ i : Fin (s.flag.length - 1),
        s.wt ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ •
          P.posR (s.flag.get ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)) := by
  change (∑ i : Fin s.flag.dropLast.length,
        (s.wt ⟨i.val, lt_length_of_lt_dropLast i.isLt⟩ / (1 - s.wt s.lastIdx)) •
          P.posR (s.flag.dropLast.get i)) = (1 - s.wt s.lastIdx)⁻¹ •
      (∑ i : Fin (s.flag.length - 1),
        s.wt ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ •
          P.posR (s.flag.get ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩))
  rw [show (∑ i : Fin s.flag.dropLast.length,
        (s.wt ⟨i.val, lt_length_of_lt_dropLast i.isLt⟩ / (1 - s.wt s.lastIdx)) •
          P.posR (s.flag.dropLast.get i))
      = ∑ i : Fin s.flag.dropLast.length,
        (s.wt ⟨i.val, lt_length_of_lt_dropLast i.isLt⟩ / (1 - s.wt s.lastIdx)) •
          P.posR (s.flag.get ⟨i.val, lt_length_of_lt_dropLast i.isLt⟩) from by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [get_dropLast]]
  rw [sum_dropLast_reindex s.flag]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_smul_eq_inv_smul]

/-- Splitting off the last face from the realization of a flag. -/
theorem toE'_split_last (s : P.FlagPt) (_h2 : 2 ≤ s.flag.length) :
    s.toE' = s.wt s.lastIdx • P.posR s.topFace +
      (∑ i : Fin (s.flag.length - 1),
        s.wt ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ •
          P.posR (s.flag.get ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)) := by
  simp only [toE']
  rw [sum_univ_eq_sum_erase_last (List.length_pos_of_ne_nil s.flag_ne_nil)
        (fun i => s.wt i • P.posR (s.flag.get i))]
  rw [last_term, add_comm]


/-! ### The restriction of a flag point and its geometry -/

/-- The realization of a flag as an affine combination of the `posR` of its top face and the
realization of its restriction. -/
theorem toE'_combo (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    s.toE' = s.wt s.lastIdx • P.posR s.topFace
      + (1 - s.wt s.lastIdx) • (subPt s h2).toE' := by
  have hne : (1 - s.wt s.lastIdx) ≠ 0 :=
    ne_of_gt (by have h := wt_last_lt_one s h2; linarith)
  rw [toE'_split_last s h2, subPt_toE', smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem subPt_mem_Pset (h : P.Ok) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    (subPt s h2).toE' ∈ P.Pset := FlagPt_mem h (subPt s h2)

theorem subPt_tightAt (h : P.Ok) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    P.tightAt (subPt s h2).toE' = P.tight (subPt s h2).topFace :=
  tightAt_flagPt P h (subPt s h2)

/-- The top face of the restriction of a flag is its second largest face. -/
theorem subPt_topFace (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    (subPt s h2).topFace = s.flag.get ⟨s.flag.length - 2,
      by have := List.length_pos_of_ne_nil s.flag_ne_nil; omega⟩ := by
  unfold topFace
  rw [show (subPt s h2).flag.getLast (subPt s h2).flag_ne_nil
      = (s.flag.dropLast).getLast
          (List.ne_nil_of_length_pos (by rw [List.length_dropLast]; omega)) from rfl]
  rw [List.getLast_dropLast, List.get_eq_getElem]

/-- The tight set of the top face of the restriction strictly contains the tight set of the top
face of the original flag. -/
theorem tight_ssubset_subPt (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    P.tight s.topFace ⊂ P.tight (subPt s h2).topFace := by
  rw [← get_lastIdx, subPt_topFace]
  have hlt : (⟨s.flag.length - 2,
      by have h := List.length_pos_of_ne_nil s.flag_ne_nil; omega⟩ : Fin s.flag.length) <
      s.lastIdx := by
    rw [Fin.lt_def]
    simp only [lastIdx, Fin.val_mk]
    omega
  exact List.Pairwise.rel_get_of_lt s.isFlag hlt

/-- The realization of the restriction of a flag is not the `posR` of its top face. -/
theorem subPt_ne_posR (h : P.Ok) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    (subPt s h2).toE' ≠ P.posR s.topFace := by
  intro heq
  have h1 : P.tight (subPt s h2).topFace = P.tight s.topFace := by
    rw [← subPt_tightAt h s h2, heq, tightAt_posR P h]
  exact (Finset.ssubset_iff_subset_ne.mp (tight_ssubset_subPt s h2)).2 h1.symm

/-- The realization of the restriction of a flag lies on the ray from `posR` of the top face
through the realization of the flag. -/
theorem subPt_on_ray (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    (subPt s h2).toE' = P.posR s.topFace +
      (1 - s.wt s.lastIdx)⁻¹ • (s.toE' - P.posR s.topFace) := by
  have hne : (1 - s.wt s.lastIdx) ≠ 0 :=
    ne_of_gt (by have h := wt_last_lt_one s h2; linarith)
  rw [toE'_combo s h2]
  rw [show s.wt s.lastIdx • P.posR s.topFace + (1 - s.wt s.lastIdx) • (subPt s h2).toE'
        - P.posR s.topFace
      = (1 - s.wt s.lastIdx) • ((subPt s h2).toE' - P.posR s.topFace) by module]
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  abel

/-- Past the realization of the restriction of a flag, the ray from `posR` of the top face leaves
the polytope. -/
theorem subPt_max (h : P.Ok) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    ∀ τ : ℝ, 1 < τ →
      (P.posR s.topFace + τ • ((subPt s h2).toE' - P.posR s.topFace)) ∉ P.Pset := by
  obtain ⟨j, hj_mem, hj_not⟩ := Finset.exists_of_ssubset (tight_ssubset_subPt s h2)
  intro τ hτ hmem
  have hz : (subPt s h2).toE' ∈ P.Pset := subPt_mem_Pset h s h2
  have hzt : j ∈ P.tightAt (subPt s h2).toE' := by rw [subPt_tightAt h s h2]; exact hj_mem
  have hzj : inner ℝ (P.nR j) (subPt s h2).toE' = P.bR j := (tightAt_of_mem P hz j).mp hzt
  have hcj : inner ℝ (P.nR j) (P.posR s.topFace) < P.bR j :=
    inner_nR_posR_of_not_mem P h s.topFace j hj_not
  have hle : inner ℝ (P.nR j)
      (P.posR s.topFace + τ • ((subPt s h2).toE' - P.posR s.topFace)) ≤ P.bR j := hmem j
  have hcalc : inner ℝ (P.nR j)
        (P.posR s.topFace + τ • ((subPt s h2).toE' - P.posR s.topFace))
      = inner ℝ (P.nR j) (P.posR s.topFace)
        + τ * (P.bR j - inner ℝ (P.nR j) (P.posR s.topFace)) := by
    rw [inner_add_right, inner_smul_right, inner_sub_right, hzj]
  rw [hcalc] at hle
  have : P.bR j < inner ℝ (P.nR j) (P.posR s.topFace)
      + τ * (P.bR j - inner ℝ (P.nR j) (P.posR s.topFace)) := by nlinarith [hcj, hτ]
  linarith

/-- Uniqueness of the exit parameter along a ray of the polytope. -/
theorem ray_param_unique {c x : E d} {σ₁ σ₂ : ℝ} {z₁ z₂ : E d}
    (hz₁ : z₁ ∈ P.Pset) (hm₁ : ∀ t : ℝ, σ₁ < t → (c + t • (x - c)) ∉ P.Pset)
    (hz₂ : z₂ ∈ P.Pset) (hm₂ : ∀ t : ℝ, σ₂ < t → (c + t • (x - c)) ∉ P.Pset)
    (h₁ : z₁ = c + σ₁ • (x - c)) (h₂ : z₂ = c + σ₂ • (x - c)) : σ₁ = σ₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := hm₁ σ₂ hlt
    rw [h₂] at hz₂
    exact this hz₂
  · have := hm₂ σ₁ hlt
    rw [h₁] at hz₁
    exact this hz₁


/-! ### Flags with a single face -/

theorem wt_eq_one_of_length_one (s : P.FlagPt) (h : s.flag.length = 1)
    (i : Fin s.flag.length) : s.wt i = 1 := by
  have hsum : ∑ j, s.wt j = s.wt i :=
    Finset.sum_eq_single i (fun j _ hj => absurd (Fin.ext (by have := j.isLt; omega)) hj)
      (fun hi => absurd (Finset.mem_univ i) hi)
  rw [← hsum]; exact s.wt_sum

theorem flag_eq_singleton (s : P.FlagPt) (h : s.flag.length = 1) :
    s.flag = [s.topFace] := by
  rw [← List.dropLast_append_getLast s.flag_ne_nil]
  have hnil : s.flag.dropLast = [] := by rw [List.dropLast_eq_nil_iff]; omega
  rw [hnil]
  rfl

theorem toE'_of_length_one (s : P.FlagPt) (h : s.flag.length = 1) :
    s.toE' = P.posR s.topFace := by
  have hget : s.flag.get ⟨0, by omega⟩ = s.topFace := by
    have heq : (⟨0, by omega⟩ : Fin s.flag.length) = s.lastIdx := by
      apply Fin.ext; simp [lastIdx]; omega
    rw [heq, get_lastIdx]
  have hwt : s.wt ⟨0, by omega⟩ = 1 := wt_eq_one_of_length_one s h _
  unfold toE'
  trans s.wt ⟨0, by omega⟩ • P.posR (s.flag.get ⟨0, by omega⟩)
  · refine Finset.sum_eq_single _ ?_ ?_
    · intro j _ hj
      exact absurd (Fin.ext (by have := j.isLt; omega)) hj
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [hwt, one_smul, hget]

theorem toE'_ne_posR (h : P.Ok) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    s.toE' ≠ P.posR s.topFace := by
  intro heq
  have hray := subPt_on_ray s h2
  rw [heq, sub_self, smul_zero, add_zero] at hray
  exact subPt_ne_posR h s h2 hray

theorem topFace_eq_of_toE'_eq (h : P.Ok) {s t : P.FlagPt} (hst : s.toE' = t.toE') :
    s.topFace = t.topFace := by
  have h1 : P.tight s.topFace = P.tight t.topFace := by
    rw [← tightAt_flagPt P h s, hst, tightAt_flagPt P h t]
  exact Ok.tight_inj P h h1

theorem length_one_of_toE'_eq (h : P.Ok) {s t : P.FlagPt} (hs : s.flag.length = 1)
    (hst : s.toE' = t.toE') : t.flag.length = 1 := by
  have hft : t.topFace = s.topFace := (topFace_eq_of_toE'_eq h hst).symm
  by_contra hne
  have h2t : 2 ≤ t.flag.length := by
    have := List.length_pos_of_ne_nil t.flag_ne_nil; omega
  refine toE'_ne_posR h t h2t ?_
  rw [← hst, toE'_of_length_one s hs, hft]

theorem two_le_of_toE'_eq (h : P.Ok) {s t : P.FlagPt} (h2s : 2 ≤ s.flag.length)
    (hst : s.toE' = t.toE') : 2 ≤ t.flag.length := by
  have hft : t.topFace = s.topFace := (topFace_eq_of_toE'_eq h hst).symm
  by_contra hne
  have h1t : t.flag.length = 1 := by
    have := List.length_pos_of_ne_nil t.flag_ne_nil; omega
  refine toE'_ne_posR h s h2s ?_
  rw [hst, toE'_of_length_one t h1t, hft]

/-! ### The ray form of the maximality and the main induction -/

theorem wt_apply_eq_of_eq {s t : P.FlagPt} (h : s = t) {k : ℕ}
    (hs : k < s.flag.length) (ht : k < t.flag.length) :
    s.wt ⟨k, hs⟩ = t.wt ⟨k, ht⟩ := by
  have := congrArg (fun (x : P.FlagPt) => if h : k < x.flag.length then x.wt ⟨k, h⟩ else 0) h
  simpa [dite_eq_left hs, dite_eq_left ht] using this

theorem flag_apply_eq_of_eq {s t : P.FlagPt} (h : s = t) : s.flag = t.flag :=
  congrArg FlagPt.flag h

theorem eq_of_flag_eq_wt (s t : P.FlagPt) (hfl : s.flag = t.flag)
    (hwt : ∀ i : Fin s.flag.length, s.wt i = t.wt ⟨i.val, hfl ▸ i.isLt⟩) : s = t := by
  obtain ⟨fl₁, if₁, w₁, p₁, q₁⟩ := s
  obtain ⟨fl₂, if₂, w₂, p₂, q₂⟩ := t
  simp only at hfl hwt
  subst fl₂
  rw [FlagPt.mk.injEq]
  exact ⟨rfl, heq_of_eq (funext hwt)⟩

/-- Past the exit parameter, the ray from the realisation of a flag leaves the polytope. -/
theorem subPt_max_x (h : P.Ok) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    ∀ τ : ℝ, (1 - s.wt s.lastIdx)⁻¹ < τ →
      (P.posR s.topFace + τ • (s.toE' - P.posR s.topFace)) ∉ P.Pset := by
  intro τ hτ
  have hpos : 0 < 1 - s.wt s.lastIdx := by have h := wt_last_lt_one s h2; linarith
  have hzsub : (subPt s h2).toE' - P.posR s.topFace
      = (1 - s.wt s.lastIdx)⁻¹ • (s.toE' - P.posR s.topFace) := by
    rw [subPt_on_ray s h2, add_sub_cancel_left]
  have hxc : s.toE' - P.posR s.topFace
      = (1 - s.wt s.lastIdx) • ((subPt s h2).toE' - P.posR s.topFace) := by
    rw [hzsub, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  have h1 : 1 < τ * (1 - s.wt s.lastIdx) := by
    have := mul_lt_mul_of_pos_right hτ hpos
    rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at this
  rw [hxc, smul_smul]
  exact subPt_max h s h2 _ h1

/-- Two flags with the same realisation have the same restriction point and the same last
weight. -/
theorem subPt_data_eq (h : P.Ok) {s t : P.FlagPt} (h2s : 2 ≤ s.flag.length)
    (h2t : 2 ≤ t.flag.length) (hst : s.toE' = t.toE') :
    (subPt s h2s).toE' = (subPt t h2t).toE' ∧ s.wt s.lastIdx = t.wt t.lastIdx := by
  have hft : s.topFace = t.topFace := topFace_eq_of_toE'_eq h hst
  set c := P.posR s.topFace with hc
  set x := s.toE' with hx
  have hct : P.posR t.topFace = c := by rw [← hft]
  have hxt : t.toE' = x := hst.symm
  have hsr : (subPt s h2s).toE' = c + (1 - s.wt s.lastIdx)⁻¹ • (x - c) := by
    rw [subPt_on_ray s h2s]
  have htr : (subPt t h2t).toE' = c + (1 - t.wt t.lastIdx)⁻¹ • (x - c) := by
    rw [subPt_on_ray t h2t, hxt, hct]
  have hms : ∀ τ : ℝ, (1 - s.wt s.lastIdx)⁻¹ < τ → (c + τ • (x - c)) ∉ P.Pset := by
    intro τ hτ
    have h1 := subPt_max_x h s h2s τ hτ
    simpa [hc, hx] using h1
  have hmt : ∀ τ : ℝ, (1 - t.wt t.lastIdx)⁻¹ < τ → (c + τ • (x - c)) ∉ P.Pset := by
    intro τ hτ
    have h1 := subPt_max_x h t h2t τ hτ
    simpa [hc, hx, hxt, hct] using h1
  have hσ : (1 - s.wt s.lastIdx)⁻¹ = (1 - t.wt t.lastIdx)⁻¹ :=
    ray_param_unique (subPt_mem_Pset h s h2s) hms (subPt_mem_Pset h t h2t) hmt hsr htr
  have hlam : s.wt s.lastIdx = t.wt t.lastIdx := by
    have h2 : 1 - s.wt s.lastIdx = 1 - t.wt t.lastIdx := inv_injective hσ
    linarith
  refine ⟨?_, hlam⟩
  rw [hsr, htr, hσ]

/-- The weights of a flag away from the last face are the rescaled weights of its restriction. -/
theorem wt_eq_mul_subPt_wt (s : P.FlagPt) (h2 : 2 ≤ s.flag.length)
    (i : Fin (s.flag.length - 1)) :
    s.wt ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ =
      (1 - s.wt s.lastIdx) * (subPt s h2).wt ⟨i.val, lt_dropLast_of_lt_length i.isLt⟩ := by
  have hne : (1 - s.wt s.lastIdx) ≠ 0 :=
    ne_of_gt (by have h := wt_last_lt_one s h2; linarith)
  change s.wt ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ =
      (1 - s.wt s.lastIdx) *
        (s.wt ⟨i.val, lt_length_of_lt_dropLast (lt_dropLast_of_lt_length i.isLt)⟩
          / (1 - s.wt s.lastIdx))
  rw [div_eq_mul_inv, ← mul_assoc, mul_comm (1 - s.wt s.lastIdx)
        (s.wt ⟨i.val, lt_length_of_lt_dropLast (lt_dropLast_of_lt_length i.isLt)⟩),
      mul_assoc, mul_inv_cancel₀ hne, mul_one]
theorem flagPt_unique_aux (hok : P.Ok) (n : ℕ) :
    ∀ s t : P.FlagPt, s.flag.length = n → s.toE' = t.toE' → s = t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s t hslen hst
    have hnp : 0 < n := by rw [← hslen]; exact List.length_pos_of_ne_nil s.flag_ne_nil
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have h1s : s.flag.length = 1 := by omega
      have h1t : t.flag.length = 1 := length_one_of_toE'_eq hok h1s hst
      have hft : s.topFace = t.topFace := topFace_eq_of_toE'_eq hok hst
      have hfl : s.flag = t.flag := by
        rw [flag_eq_singleton s h1s, flag_eq_singleton t h1t, hft]
      have hwt : ∀ i : Fin s.flag.length, s.wt i = t.wt ⟨i.val, hfl ▸ i.isLt⟩ := by
        intro i
        rw [wt_eq_one_of_length_one s h1s i,
            wt_eq_one_of_length_one t h1t ⟨i.val, hfl ▸ i.isLt⟩]
      exact eq_of_flag_eq_wt s t hfl hwt
    · have h2s : 2 ≤ s.flag.length := by omega
      have h2t : 2 ≤ t.flag.length := two_le_of_toE'_eq hok h2s hst
      have hft : s.topFace = t.topFace := topFace_eq_of_toE'_eq hok hst
      obtain ⟨hzeq, hlam⟩ := subPt_data_eq hok h2s h2t hst
      have hlen : (subPt s h2s).flag.length = n - 1 := by
        have hh : (subPt s h2s).flag.length = s.flag.length - 1 := by
          rw [show (subPt s h2s).flag = s.flag.dropLast from rfl, List.length_dropLast]
        omega
      have hsub : subPt s h2s = subPt t h2t :=
        ih (n - 1) (by omega) (subPt s h2s) (subPt t h2t) hlen hzeq
      have hfl : s.flag = t.flag := by
        rw [← List.dropLast_append_getLast s.flag_ne_nil,
            ← List.dropLast_append_getLast t.flag_ne_nil]
        have h1 : s.flag.dropLast = t.flag.dropLast := by
          rw [show s.flag.dropLast = (subPt s h2s).flag from rfl,
              flag_apply_eq_of_eq hsub,
              show (subPt t h2t).flag = t.flag.dropLast from rfl]
        rw [h1, show s.flag.getLast s.flag_ne_nil = s.topFace from rfl,
            show t.flag.getLast t.flag_ne_nil = t.topFace from rfl, hft]
      have hwt : ∀ i : Fin s.flag.length, s.wt i = t.wt ⟨i.val, hfl ▸ i.isLt⟩ := by
        intro i
        rcases lt_or_eq_of_le (Nat.le_pred_of_lt i.isLt) with hlt | heq
        · have hkt : i.val < t.flag.length - 1 := by
            have hlen' : s.flag.length = t.flag.length := congrArg List.length hfl
            rw [← hlen']; exact hlt
          have hsi : i = (⟨i.val, Nat.lt_of_lt_pred hlt⟩ : Fin s.flag.length) := Fin.ext rfl
          rw [hsi]
          rw [show (⟨i.val, hfl ▸ i.isLt⟩ : Fin t.flag.length)
                = ⟨i.val, Nat.lt_of_lt_pred hkt⟩ from Fin.ext rfl]
          rw [wt_eq_mul_subPt_wt s h2s ⟨i.val, hlt⟩,
              wt_eq_mul_subPt_wt t h2t ⟨i.val, hkt⟩]
          rw [hlam, wt_apply_eq_of_eq hsub (lt_dropLast_of_lt_length hlt)
                (lt_dropLast_of_lt_length hkt)]
        · have hi : i = s.lastIdx := Fin.ext (by simp only [lastIdx, Fin.val_mk]; exact heq)
          have hj : (⟨i.val, hfl ▸ i.isLt⟩ : Fin t.flag.length) = t.lastIdx := by
            apply Fin.ext
            have hlen' : s.flag.length = t.flag.length := congrArg List.length hfl
            simp only [lastIdx, Fin.val_mk]
            rw [heq, hlen']
            exact Nat.pred_eq_sub_one
          calc s.wt i = s.wt s.lastIdx := by rw [hi]
            _ = t.wt t.lastIdx := hlam
            _ = t.wt ⟨i.val, hfl ▸ i.isLt⟩ := by rw [hj]
      exact eq_of_flag_eq_wt s t hfl hwt

end FlagPt
end PolytopeData

/-- Two flag points with the same realization are equal: the open simplices of the barycentric
subdivision are pairwise disjoint. -/
theorem flagPt_unique {d : ℕ} (P : PolytopeData d) (h : P.Ok) (s t : P.FlagPt)
    (hst : s.toE' = t.toE') : s = t :=
  PolytopeData.FlagPt.flagPt_unique_aux (P := P) h s.flag.length s t rfl hst

end Work.ConvexCells
