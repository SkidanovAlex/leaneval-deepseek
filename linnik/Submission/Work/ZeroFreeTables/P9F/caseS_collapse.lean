import Mathlib
import Submission.Work.ZeroFreeTables.P9F.caseS_defs
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.frame_count_prov_helpers

open scoped BigOperators

namespace Work.ZeroFreeTables.P9F

/-- **Case S of the frame count, first reduction.**

`Work.LinnikBurgess.sum2 H m d g Work.LinnikBurgess.CaseS` is the iterated sum over
`x0 x1 x2 y0 y1 y2 ∈ [1,H]` of `[condAB d g ![x0,x1,x2] ![y0,y1,y2] ∧ x1 = x2] · wtAB m ![x0,x1,x2] ![y0,y1,y2]`
(with `condAB = NotInB ∧ a0 ≠ a1 ∧ a0 ≠ a2 ∧ DLd d a b ∧ g ∣ contAB a b`).

Rewriting the `y`-sum as a sum over `box3 H` (`Work.ZeroFreeTables.P9F.sum2_eq_box3`), then
collapsing `∑_{x2}` to the single term at `x2 = x1` (`Finset.sum_eq_single`, valid because all
other terms vanish), and finally dropping `DLd` and `contAB` in favour of
`g ∣ contAB ⟹ g ∣ ∏_k del x0 (y k)` (`Work.LinnikBurgess.contAB_dvd_prod_del`) together with
`wtAB m ![x0,s,s] y = (wg m x0 s)^2 · ∏_k wg m x0 (y k)` (`Work.LinnikBurgess.wtAB_caseS`),
gives the relaxed sum, which factors into the product of
`Ss H m α = ∑_{s ∈ [1,H], s ≠ α} (wg m α s)^2` and
`Ys H m g α = ∑_{y ∈ box3 H} [∀l, y l ≠ α][g ∣ ∏_k del α (y k)] ∏_k wg m α (y k)`.

Note the bounds `x2 = x1 ∈ [1,H]` and that all dropped summands are nonnegative, so `≤`. -/
theorem caseS_collapse (H m d g : ℕ) :
    Work.LinnikBurgess.sum2 H m d g Work.LinnikBurgess.CaseS
      ≤ ∑ α ∈ Finset.Icc 1 H,
          Work.ZeroFreeTables.P9F.Ss H m α * Work.ZeroFreeTables.P9F.Ys H m g α := by
  classical
  rw [Work.ZeroFreeTables.P9F.sum2_eq_box3]
  apply Finset.sum_le_sum
  intro x0 hx0
  have hcol : (∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H, ∑ y ∈ Work.LinnikBurgess.box3 H,
        (if Work.LinnikBurgess.condAB d g ![x0, x1, x2] y ∧ Work.LinnikBurgess.CaseS ![x0, x1, x2] y
          then Work.LinnikBurgess.wtAB m ![x0, x1, x2] y else 0))
      = ∑ x1 ∈ Finset.Icc 1 H, ∑ y ∈ Work.LinnikBurgess.box3 H,
        (if Work.LinnikBurgess.condAB d g ![x0, x1, x1] y then Work.LinnikBurgess.wtAB m ![x0, x1, x1] y else 0) := by
    apply Finset.sum_congr rfl
    intro x1 hx1
    refine (Finset.sum_eq_single_of_mem x1 hx1 (fun x2 hx2 hne => ?_)).trans ?_
    · apply Finset.sum_eq_zero
      intro y hy
      have hf : ¬ (Work.LinnikBurgess.condAB d g ![x0, x1, x2] y ∧ Work.LinnikBurgess.CaseS ![x0, x1, x2] y) := by
        rintro ⟨_, hcs⟩
        simp [Work.LinnikBurgess.CaseS] at hcs
        exact hne hcs.symm
      rw [if_neg hf]
    · apply Finset.sum_congr rfl
      intro y hy
      simp [Work.LinnikBurgess.CaseS]
  rw [hcol]
  have hstep : (∑ x1 ∈ Finset.Icc 1 H, ∑ y ∈ Work.LinnikBurgess.box3 H,
        (if Work.LinnikBurgess.condAB d g ![x0, x1, x1] y then Work.LinnikBurgess.wtAB m ![x0, x1, x1] y else 0))
      ≤ ∑ x1 ∈ Finset.Icc 1 H, ∑ y ∈ Work.LinnikBurgess.box3 H,
        (if x1 ≠ x0 then (Work.LinnikBurgess.wg m x0 x1) ^ 2 else 0) *
        (if (∀ l : Fin 3, y l ≠ x0) ∧ g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del x0 (y k)
          then ∏ k : Fin 3, Work.LinnikBurgess.wg m x0 (y k) else 0) := by
    apply Finset.sum_le_sum
    intro x1 hx1
    apply Finset.sum_le_sum
    intro y hy
    by_cases hc : Work.LinnikBurgess.condAB d g ![x0, x1, x1] y
    · rw [if_pos hc]
      obtain ⟨hnib, h01, h02, hdl, hg⟩ := hc
      have hx1ne : x1 ≠ x0 := by simpa using h01.symm
      have hQ1 : ∀ l : Fin 3, y l ≠ x0 := fun l => by simpa using (hnib l).symm
      have hQ2 : g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del x0 (y k) := by
        simpa using dvd_trans hg (Work.LinnikBurgess.contAB_dvd_prod_del ![x0, x1, x1] y 0)
      rw [if_pos hx1ne, if_pos ⟨hQ1, hQ2⟩, Work.LinnikBurgess.wtAB_caseS, Fin.prod_univ_three]
    · rw [if_neg hc]
      apply mul_nonneg
      · split_ifs with h
        · positivity
        · exact le_refl 0
      · split_ifs with h
        · exact Finset.prod_nonneg (fun k _ => Work.LinnikBurgess.wg_nonneg m x0 (y k))
        · exact le_refl 0
  have hfac : (∑ x1 ∈ Finset.Icc 1 H, ∑ y ∈ Work.LinnikBurgess.box3 H,
        (if x1 ≠ x0 then (Work.LinnikBurgess.wg m x0 x1) ^ 2 else 0) *
        (if (∀ l : Fin 3, y l ≠ x0) ∧ g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del x0 (y k)
          then ∏ k : Fin 3, Work.LinnikBurgess.wg m x0 (y k) else 0))
      = Ss H m x0 * Ys H m g x0 := by
    rw [← Finset.sum_mul_sum, Ss, Ys]
  exact le_trans hstep (le_of_eq hfac)

end Work.ZeroFreeTables.P9F
