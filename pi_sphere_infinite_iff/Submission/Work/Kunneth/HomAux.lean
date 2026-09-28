import Mathlib
import Submission.Work.Kunneth.HomDefs
import Submission.Work.Kunneth.tpDpq_comp

/-!
# The differential of `homTens C M` in components

The differential of `homTens C M = tpC C (sumShift M)` is `d ⊗ 1` on every bidegree summand.
This file computes it in components (`tpD_sumShift_lof`, `tpD_sumShift_apply`) and derives the
descriptions of the kernel and of the range of the incoming differential `hIn` as products, over
the bidegrees, of the kernels and the ranges of the coefficient differentials `hDIn` / `hDOut`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

variable (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)

/-- The structure maps of the direct sum reconstruct an element: `∑ j, tpLof j (z j) = z`. -/
theorem tpX_sum_lof (n : ℕ) (z : tpX C (sumShift M) n) :
    ∑ j : tpIdx n, tpLof C (sumShift M) n j (z j) = z := by
  apply DirectSum.ext
  intro k
  rw [← DirectSum.coeFnLinearMap_apply (R := ℤ)
    (v := ∑ j : tpIdx n, tpLof C (sumShift M) n j (z j))]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
  · simp only [DirectSum.coeFnLinearMap_apply, DirectSum.lof_apply]
  · intro j _ hj
    change DirectSum.component ℤ (tpIdx n)
      (fun rs => tpSummand C (sumShift M) rs.1.1 rs.1.2) k
        (DirectSum.lof ℤ (tpIdx n)
          (fun rs => tpSummand C (sumShift M) rs.1.1 rs.1.2) j (z j)) = 0
    rw [DirectSum.component.of]
    simp [hj]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The `tpLof` of the `tpStep`-shifted summand, evaluated at its own (definitionally equal)
index. -/
theorem tpLof_tpStep_self (n : ℕ) (j : tpIdx n)
    (X : tpSummand C (sumShift M) ((tpStep n j).1.1 - 1) (tpStep n j).1.2) :
    (tpLof C (sumShift M) n
        ⟨((tpStep n j).1.1 - 1, (tpStep n j).1.2),
          by rw [tpStep_fst_sub_one, tpStep_snd']; exact j.2⟩ X) j = X := by
  show DirectSum.component ℤ (tpIdx n)
      (fun rs => tpSummand C (sumShift M) rs.1.1 rs.1.2) j
        (DirectSum.lof ℤ (tpIdx n) (fun rs => tpSummand C (sumShift M) rs.1.1 rs.1.2)
          ⟨((tpStep n j).1.1 - 1, (tpStep n j).1.2),
            by rw [tpStep_fst_sub_one, tpStep_snd']; exact j.2⟩ X) = X
  rw [DirectSum.component.of,
    dif_pos (show (⟨((tpStep n j).1.1 - 1, (tpStep n j).1.2),
      by rw [tpStep_fst_sub_one, tpStep_snd']; exact j.2⟩ : tpIdx n) = j from rfl)]

/-- The second summand of `tpDpq` for the complex `sumShift M` is zero, since `sumShift M` has
zero differential. -/
theorem sumShift_tpDpq_snd (n : ℕ) (pq : tpIdx (n + 1)) :
    ((if hq : 1 ≤ pq.1.2 then
        (-1 : ℤ) ^ pq.1.1 •
          ((tpLof C (sumShift M) n ⟨(pq.1.1, pq.1.2 - 1), by omega⟩).comp
            (TensorProduct.map (LinearMap.id) ((sumShift M).d pq.1.2 (pq.1.2 - 1)).hom))
        else 0) : tpSummand C (sumShift M) pq.1.1 pq.1.2 →ₗ[ℤ] tpX C (sumShift M) n) = 0 := by
  by_cases hq : 1 ≤ pq.1.2
  · rw [dif_pos hq]
    have hz : TensorProduct.map (LinearMap.id :
          ↥(C.X pq.1.1) →ₗ[ℤ] ↥(C.X pq.1.1))
        ((sumShift M).d pq.1.2 (pq.1.2 - 1)).hom = 0 := by
      rw [show ((sumShift M).d pq.1.2 (pq.1.2 - 1)).hom = 0 from by
        rw [show (sumShift M).d pq.1.2 (pq.1.2 - 1) = 0 from by
          rw [← Nat.sub_add_cancel hq]; exact sumShift_d M (pq.1.2 - 1)]
        rfl]
      rw [← LinearMap.lTensor_def, LinearMap.lTensor_zero]
    rw [hz, LinearMap.comp_zero]
    apply LinearMap.ext
    intro m
    rw [smul_lmap_apply, LinearMap.zero_apply]
    exact zsmul_zero _
  · rw [dif_neg hq]

/-- The value of `tpD` on a summand generator.  Only the first (decreasing) part of the Koszul
differential survives, because `sumShift M` has zero differential. -/
theorem tpD_sumShift_lof (n : ℕ) (pq : tpIdx (n + 1)) :
    ∀ c : tpSummand C (sumShift M) pq.1.1 pq.1.2,
      tpD C (sumShift M) n (tpLof C (sumShift M) (n + 1) pq c)
        = (if hp : 1 ≤ pq.1.1 then
            tpLof C (sumShift M) n ⟨(pq.1.1 - 1, pq.1.2), by omega⟩
              (hDIn C M pq.1.1 pq.1.2 c)
          else 0) := by
  intro c
  rw [tpD, DirectSum.toModule_lof, tpDpq, sumShift_tpDpq_snd C M n pq, add_zero]
  by_cases hp : 1 ≤ pq.1.1
  · rw [dif_pos hp, dif_pos hp, LinearMap.comp_apply]
    rfl
  · rw [dif_neg hp, dif_neg hp, LinearMap.zero_apply]

/-- The `j`-component of `tpD n x`. -/
theorem tpD_sumShift_apply (n : ℕ) (x : tpX C (sumShift M) (n + 1)) (j : tpIdx n) :
    tpD C (sumShift M) n x j
      = hDOut C M j.1.1 j.1.2 (x (tpStep n j)) := by
  have h : (hProj C M n j).comp (tpD C (sumShift M) n)
      = (hDOut C M j.1.1 j.1.2).comp (hProj C M (n + 1) (tpStep n j)) := by
    apply DirectSum.linearMap_ext ℤ
    intro r
    apply LinearMap.ext
    intro c
    show tpD C (sumShift M) n (tpLof C (sumShift M) (n + 1) r c) j
      = hDOut C M j.1.1 j.1.2 ((tpLof C (sumShift M) (n + 1) r c) (tpStep n j))
    rw [tpD_sumShift_lof C M n r c]
    by_cases hr : r = tpStep n j
    · subst hr
      rw [dif_pos (show 1 ≤ (tpStep n j).1.1 by simp [tpStep]), DirectSum.lof_apply,
        tpLof_tpStep_self C M n j (hDIn C M (tpStep n j).1.1 (tpStep n j).1.2 c)]
      show hDIn C M (j.1.1 + 1) j.1.2 c = hDOut C M j.1.1 j.1.2 c
      rw [hDIn_succ_eq_hDOut]
      rfl
    · have hR : (tpLof C (sumShift M) (n + 1) r c) (tpStep n j) = 0 := by
        change DirectSum.component ℤ (tpIdx (n + 1))
          (fun rs => tpSummand C (sumShift M) rs.1.1 rs.1.2) (tpStep n j)
            (DirectSum.lof ℤ (tpIdx (n + 1))
              (fun rs => tpSummand C (sumShift M) rs.1.1 rs.1.2) r c) = 0
        rw [DirectSum.component.of]
        have hne : r ≠ tpStep n j := hr
        simp [hne]
      rw [hR, map_zero]
      by_cases hr1 : 1 ≤ r.1.1
      · rw [dif_pos hr1]
        have hL : (tpLof C (sumShift M) n ⟨(r.1.1 - 1, r.1.2), by
              have := r.2; omega⟩ (hDIn C M r.1.1 r.1.2 c)) j = 0 := by
          change DirectSum.component ℤ (tpIdx n)
            (fun rs => tpSummand C (sumShift M) rs.1.1 rs.1.2) j
              (DirectSum.lof ℤ (tpIdx n)
                (fun rs => tpSummand C (sumShift M) rs.1.1 rs.1.2)
                ⟨(r.1.1 - 1, r.1.2), by have := r.2; omega⟩
                (hDIn C M r.1.1 r.1.2 c)) = 0
          rw [DirectSum.component.of]
          have hne : (⟨(r.1.1 - 1, r.1.2), by have := r.2; omega⟩ : tpIdx n) ≠ j := by
            intro hh
            apply hr
            have h1 : r.1.1 - 1 = j.1.1 := congrArg (fun i : tpIdx n => i.1.1) hh
            have h2 : r.1.2 = j.1.2 := congrArg (fun i : tpIdx n => i.1.2) hh
            apply Subtype.ext
            apply Prod.ext
            · show r.1.1 = j.1.1 + 1
              omega
            · exact h2
          simp [hne]
        rw [hL]
      · rw [dif_neg hr1]
        simp
  exact LinearMap.congr_fun h x

/-- The kernel of `hIn` in degree `0`. -/
theorem hIn_ker_zero :
    (hIn C M 0).ker = hProdSub C M 0 (fun pq => (hDIn C M pq.1.1 pq.1.2).ker) := by
  rw [hIn_zero, LinearMap.ker_zero]
  rw [show (fun pq : tpIdx 0 => (hDIn C M pq.1.1 pq.1.2).ker) = (fun _ => ⊤) from by
    funext pq
    have hp : pq.1.1 = 0 := by have := pq.2; omega
    rw [hp, hDIn_zero, LinearMap.ker_zero]]
  symm
  rw [eq_top_iff]
  intro x _
  rw [mem_hProdSub]
  intro pq
  exact Submodule.mem_top

/-- The kernel of `hIn` in positive degree. -/
theorem hIn_ker_succ (n : ℕ) :
    (hIn C M (n + 1)).ker
      = hProdSub C M (n + 1) (fun pq => (hDIn C M pq.1.1 pq.1.2).ker) := by
  rw [hIn_succ]
  ext x
  rw [mem_hProdSub, LinearMap.mem_ker]
  constructor
  · intro hx pq
    by_cases hp : pq.1.1 = 0
    · have hpq : pq = (⟨(0, pq.1.2), by have := pq.2; omega⟩ : tpIdx (n + 1)) := by
        apply Subtype.ext
        apply Prod.ext
        · simpa using hp
        · rfl
      rw [hpq, hDIn_zero, LinearMap.ker_zero]
      exact Submodule.mem_top
    · have hp1 : 1 ≤ pq.1.1 := by omega
      obtain ⟨j, hj⟩ : ∃ j : tpIdx n, pq = tpStep n j :=
        ⟨⟨(pq.1.1 - 1, pq.1.2), by omega⟩, eq_tpStep_of_pos hp1⟩
      have h0 : tpD C (sumShift M) n x j = 0 := by
        have := congrArg (fun z => z j) hx
        rwa [DFinsupp.zero_apply] at this
      rw [tpD_sumShift_apply C M n x j] at h0
      rw [hj, LinearMap.mem_ker]
      exact h0
  · intro hx
    show tpD C (sumShift M) n x = (0 : tpX C (sumShift M) n)
    apply DirectSum.ext
    intro j
    rw [tpD_sumShift_apply C M n x j, DFinsupp.zero_apply]
    have h := hx (tpStep n j)
    rw [LinearMap.mem_ker] at h
    exact h

/-- The kernel of `hIn`. -/
theorem hIn_ker (n : ℕ) :
    (hIn C M n).ker = hProdSub C M n (fun pq => (hDIn C M pq.1.1 pq.1.2).ker) := by
  cases n with
  | zero => exact hIn_ker_zero C M
  | succ m => exact hIn_ker_succ C M m

/-- The range of the incoming differential is the product of the coefficient ranges. -/
theorem hIn_range_succ (n : ℕ) :
    (hIn C M (n + 1)).range
      = hProdSub C M n (fun pq => (hDOut C M pq.1.1 pq.1.2).range) := by
  rw [hIn_succ]
  ext z
  rw [mem_hProdSub, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩ pq
    rw [← hy]
    show tpD C (sumShift M) n y pq ∈ (hDOut C M pq.1.1 pq.1.2).range
    rw [tpD_sumShift_apply C M n y pq]
    exact ⟨y (tpStep n pq), rfl⟩
  · intro hz
    choose g hg using hz
    refine ⟨∑ j : tpIdx n, tpLof C (sumShift M) (n + 1) (tpStep n j) (g j), ?_⟩
    rw [map_sum]
    have hterm : ∀ j : tpIdx n,
        tpD C (sumShift M) n (tpLof C (sumShift M) (n + 1) (tpStep n j) (g j))
          = tpLof C (sumShift M) n j (z j) := by
      intro j
      rw [tpD_sumShift_lof C M n (tpStep n j) (g j),
        dif_pos (show 1 ≤ (tpStep n j).1.1 by simp [tpStep])]
      exact congrArg (tpLof C (sumShift M) n j) (hg j)
    have hsum : (∑ j : tpIdx n, tpD C (sumShift M) n
          (tpLof C (sumShift M) (n + 1) (tpStep n j) (g j)))
        = (∑ j : tpIdx n, tpLof C (sumShift M) n j (z j)) :=
      Finset.sum_congr rfl (fun j _ => hterm j)
    exact hsum.trans (tpX_sum_lof C M n z)

end

end Work.Kunneth
