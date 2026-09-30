import Mathlib
import Submission.Work.ConvexCells.flagPt_unique
import Submission.Work.MbarHomology.ConvexCells.sd_carrier_of_basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

/-!
# Uniqueness of flag points from the basic checks only

`P.OkBasic` is the first conjunct of `P.Ok`: it carries the positivity of the common denominator,
the injectivity of `tight`, the `pos` points realising the tight sets of their faces, the Farkas
certificates for the `gface` faces and the boundedness certificate -- but *not* the
`OkEmp`/`OkAdd` certificate groups, which are spent only on deriving `Carriers`.

The disjointness of the open flag simplices `FlagPt.toE'` never uses those two groups: it rests on
the `pos` conditions alone.  This file redoes `flagPt_unique` under `OkBasic`.
-/

namespace Work.MbarHomology.ConvexCells

open scoped BigOperators
open Work.ConvexCells
open Work.ConvexCells.PolytopeData
open Work.ConvexCells.PolytopeData.FlagPt

namespace FlagPtUniqueBasic

variable {d : ℕ} {P : Work.ConvexCells.PolytopeData d}

/-- Injectivity of `tight` from `OkBasic`. -/
theorem tight_inj (h : P.OkBasic) {f g : Fin P.K} (hfg : P.tight f = P.tight g) : f = g :=
  h.2.2.1 f g hfg

/-- The affine realization of the open simplex of a flag lies in the polytope, from `OkBasic`. -/
theorem flagPt_mem (h : P.OkBasic) (s : P.FlagPt) : s.toE' ∈ P.Pset := by
  refine P.Pset_convex.sum_mem (t := Finset.univ)
    (fun i _ => le_of_lt (s.wt_pos i)) s.wt_sum (fun i _ => ?_)
  exact posR_mem_Pset_basic h (s.flag.get i)

theorem subPt_mem (h : P.OkBasic) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    (subPt s h2).toE' ∈ P.Pset := flagPt_mem h (subPt s h2)

theorem subPt_tightAt (h : P.OkBasic) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    P.tightAt (subPt s h2).toE' = P.tight (subPt s h2).topFace :=
  tightAt_flagPt_basic P h (subPt s h2)

theorem subPt_ne_posR (h : P.OkBasic) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    (subPt s h2).toE' ≠ P.posR s.topFace := by
  intro heq
  have h1 : P.tight (subPt s h2).topFace = P.tight s.topFace := by
    rw [← subPt_tightAt h s h2, heq, tightAt_posR_basic h]
  exact (Finset.ssubset_iff_subset_ne.mp (tight_ssubset_subPt s h2)).2 h1.symm

/-- Past the realization of the restriction of a flag, the ray from `posR` of the top face leaves
the polytope. -/
theorem subPt_max (h : P.OkBasic) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    ∀ τ : ℝ, 1 < τ →
      (P.posR s.topFace + τ • ((subPt s h2).toE' - P.posR s.topFace)) ∉ P.Pset := by
  obtain ⟨j, hj_mem, hj_not⟩ := Finset.exists_of_ssubset (tight_ssubset_subPt s h2)
  intro τ hτ hmem
  have hz : (subPt s h2).toE' ∈ P.Pset := subPt_mem h s h2
  have hzt : j ∈ P.tightAt (subPt s h2).toE' := by rw [subPt_tightAt h s h2]; exact hj_mem
  have hzj : inner ℝ (P.nR j) (subPt s h2).toE' = P.bR j := (tightAt_of_mem P hz j).mp hzt
  have hcj : inner ℝ (P.nR j) (P.posR s.topFace) < P.bR j :=
    inner_nR_posR_of_not_mem_basic h s.topFace j hj_not
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

theorem toE'_ne_posR (h : P.OkBasic) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
    s.toE' ≠ P.posR s.topFace := by
  intro heq
  have hray := subPt_on_ray s h2
  rw [heq, sub_self, smul_zero, _root_.add_zero] at hray
  exact subPt_ne_posR h s h2 hray

theorem topFace_eq_of_toE'_eq (h : P.OkBasic) {s t : P.FlagPt} (hst : s.toE' = t.toE') :
    s.topFace = t.topFace := by
  have h1 : P.tight s.topFace = P.tight t.topFace := by
    rw [← tightAt_flagPt_basic P h s, hst, tightAt_flagPt_basic P h t]
  exact tight_inj h h1

theorem length_one_of_toE'_eq (h : P.OkBasic) {s t : P.FlagPt} (hs : s.flag.length = 1)
    (hst : s.toE' = t.toE') : t.flag.length = 1 := by
  have hft : t.topFace = s.topFace := (topFace_eq_of_toE'_eq h hst).symm
  by_contra hne
  have h2t : 2 ≤ t.flag.length := by
    have := List.length_pos_of_ne_nil t.flag_ne_nil; omega
  refine toE'_ne_posR h t h2t ?_
  rw [← hst, toE'_of_length_one s hs, hft]

theorem two_le_of_toE'_eq (h : P.OkBasic) {s t : P.FlagPt} (h2s : 2 ≤ s.flag.length)
    (hst : s.toE' = t.toE') : 2 ≤ t.flag.length := by
  have hft : t.topFace = s.topFace := (topFace_eq_of_toE'_eq h hst).symm
  by_contra hne
  have h1t : t.flag.length = 1 := by
    have := List.length_pos_of_ne_nil t.flag_ne_nil; omega
  refine toE'_ne_posR h s h2s ?_
  rw [hst, toE'_of_length_one t h1t, hft]

/-- Past the exit parameter, the ray from the realisation of a flag leaves the polytope. -/
theorem subPt_max_x (h : P.OkBasic) (s : P.FlagPt) (h2 : 2 ≤ s.flag.length) :
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
theorem subPt_data_eq (h : P.OkBasic) {s t : P.FlagPt} (h2s : 2 ≤ s.flag.length)
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
    ray_param_unique (subPt_mem h s h2s) hms (subPt_mem h t h2t) hmt hsr htr
  have hlam : s.wt s.lastIdx = t.wt t.lastIdx := by
    have h2 : 1 - s.wt s.lastIdx = 1 - t.wt t.lastIdx := inv_injective hσ
    linarith
  refine ⟨?_, hlam⟩
  rw [hsr, htr, hσ]

/-- The main induction: two flags of the same length with the same realisation are equal. -/
theorem unique_aux (hok : P.OkBasic) (n : ℕ) :
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

end FlagPtUniqueBasic

theorem flagPt_unique_basic {d : ℕ} (P : Work.ConvexCells.PolytopeData d) (h : P.OkBasic)
    (s t : P.FlagPt) (hst : s.toE' = t.toE') : s = t :=
  FlagPtUniqueBasic.unique_aux (P := P) h s.flag.length s t rfl hst

end Work.MbarHomology.ConvexCells
