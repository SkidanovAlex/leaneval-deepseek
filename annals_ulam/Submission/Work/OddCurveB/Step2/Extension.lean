import Mathlib
import Submission.Work.OddVolterra.WinData.contDiffOn_Ioi_extension

/-!
# The Seeley/Borel extension of the window solution, with **global** smoothness

`Work.OddVolterra.WinData.contDiffOn_Ioi_extension` produces a state `Zfin` which is `C^∞` on
`(0, ∞)` and agrees with `Z` on `[1/4, ∞)`.  Its proof in fact constructs a *globally* `C^∞`
`Zfin` (each component is a global `C^∞` extension, `exists_contDiff_eqOn_Ici`) and throws away the
stronger conclusion; this file records the stronger form, which is what lets one take the
*right-hand limit* `deriv Zfin → deriv Zfin (1/4)` at the left end of the transition window
(the hypothesis `ContDiffOn ℝ ⊤ Z (Ioi (1/4))` alone does not give any information at `1/4`).
-/

namespace Work.OddCurveB.Step2

open MeasureTheory Set Filter
open Work.OddVolterra
open scoped Topology ContDiff Interval

noncomputable section

theorem w_extension {Z : ℝ → Work.OddVolterra.St}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Icc (1 / 4 : ℝ) (19 / 20)))
    (hZtail : ∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s)
    (hrow0 : ∀ s : ℝ, 1 / 4 < s → deriv (fun u : ℝ => Z u 0) s = Z s 2)
    (hrow1 : ∀ s : ℝ, 1 / 4 < s → deriv (fun u : ℝ => Z u 1) s = Z s 3) :
    ∃ Zfin : ℝ → Work.OddVolterra.St,
      ContDiff ℝ (⊤ : ℕ∞) Zfin ∧
      (∀ s : ℝ, 1 / 4 ≤ s → Zfin s = Z s) ∧
      (∀ s : ℝ, 1 / 4 ≤ s →
        deriv (fun u : ℝ => Zfin u 0) s = Zfin s 2 ∧
        deriv (fun u : ℝ => Zfin u 1) s = Zfin s 3) := by
  have hZhalf : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ici (1 / 4 : ℝ)) := Work.OddVolterra.WinData.contDiffOn_Z_Ici hZ hZtail
  have hcomp : ∀ i : Fin 4,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Z s i) (Set.Ici (1 / 4 : ℝ)) :=
    fun i => (contDiffOn_pi.mp hZhalf) i
  choose Fi hFic hFieq using
    fun i : Fin 4 => Work.OddVolterra.WinData.exists_contDiff_eqOn_Ici (a := (1 / 4 : ℝ)) (hcomp i)
  let Zfin : ℝ → Work.OddVolterra.St := fun s => ![Fi 0 s, Fi 1 s, Fi 2 s, Fi 3 s]
  have hZfinc : ContDiff ℝ (⊤ : ℕ∞) Zfin := by
    rw [show Zfin = fun s : ℝ => ![Fi 0 s, Fi 1 s, Fi 2 s, Fi 3 s] from rfl, contDiff_pi]
    intro i
    fin_cases i
    · exact hFic 0
    · exact hFic 1
    · exact hFic 2
    · exact hFic 3
  have hZfineq : ∀ s : ℝ, 1 / 4 ≤ s → Zfin s = Z s := by
    intro s hs
    funext i
    fin_cases i
    · exact hFieq 0 s hs
    · exact hFieq 1 s hs
    · exact hFieq 2 s hs
    · exact hFieq 3 s hs
  have hbnd : ∀ (i j : Fin 4),
      (∀ s : ℝ, 1 / 4 < s → deriv (fun u : ℝ => Z u i) s = Z s j) →
      derivWithin (fun u : ℝ => Z u i) (Set.Ici (1 / 4 : ℝ)) (1 / 4) = Z (1 / 4) j := by
    intro i j hrow
    refine Work.OddVolterra.WinData.derivWithin_Ici_eq_of_tendsto_deriv (f := fun u : ℝ => Z u i)
      (g := fun u : ℝ => Z u j) (by norm_num : (1 / 4 : ℝ) < 19 / 20) ?_ ?_ ?_ ?_
    · exact ((contDiffOn_pi.mp hZ) i).continuousOn
    · exact ((contDiffOn_pi.mp hZ) i).differentiableOn (by simp) |>.mono Ioo_subset_Icc_self
    · intro s hs
      exact hrow s hs.1
    · exact ((contDiffOn_pi.mp hZhalf) j).continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)
  have hb0 : derivWithin (fun u : ℝ => Z u 0) (Set.Ici (1 / 4 : ℝ)) (1 / 4) = Z (1 / 4) 2 :=
    hbnd 0 2 hrow0
  have hb1 : derivWithin (fun u : ℝ => Z u 1) (Set.Ici (1 / 4 : ℝ)) (1 / 4) = Z (1 / 4) 3 :=
    hbnd 1 3 hrow1
  refine ⟨Zfin, hZfinc, hZfineq, ?_⟩
  intro s hs
  constructor
  · rcases eq_or_lt_of_le hs with h | h
    · subst h
      have hder : deriv (fun u : ℝ => Zfin u 0) (1 / 4)
          = derivWithin (fun u : ℝ => Z u 0) (Set.Ici (1 / 4 : ℝ)) (1 / 4) :=
        Work.Anchor.deriv_eq_derivWithin_of_contDiff_eqOn (1 / 4) (hFic 0)
          (fun x hx => hFieq 0 x hx) (1 / 4) le_rfl
      rw [hder, hb0]
      exact (hFieq 2 (1 / 4) le_rfl).symm
    · have hev : (fun u : ℝ => Zfin u 0) =ᶠ[𝓝 s] (fun u : ℝ => Z u 0) := by
        filter_upwards [isOpen_Ioi.mem_nhds h] with u hu
        exact congrFun (hZfineq u hu.le) 0
      rw [Filter.EventuallyEq.deriv_eq hev, hrow0 s h]
      exact (congrFun (hZfineq s hs) 2).symm
  · rcases eq_or_lt_of_le hs with h | h
    · subst h
      have hder : deriv (fun u : ℝ => Zfin u 1) (1 / 4)
          = derivWithin (fun u : ℝ => Z u 1) (Set.Ici (1 / 4 : ℝ)) (1 / 4) :=
        Work.Anchor.deriv_eq_derivWithin_of_contDiff_eqOn (1 / 4) (hFic 1)
          (fun x hx => hFieq 1 x hx) (1 / 4) le_rfl
      rw [hder, hb1]
      exact (hFieq 3 (1 / 4) le_rfl).symm
    · have hev : (fun u : ℝ => Zfin u 1) =ᶠ[𝓝 s] (fun u : ℝ => Z u 1) := by
        filter_upwards [isOpen_Ioi.mem_nhds h] with u hu
        exact congrFun (hZfineq u hu.le) 1
      rw [Filter.EventuallyEq.deriv_eq hev, hrow1 s h]
      exact (congrFun (hZfineq s hs) 3).symm


end

end Work.OddCurveB.Step2
