import Mathlib
import Submission.Work.C7.xdefs
import Submission.Work.C7.trans
import Submission.Work.C7.g_form
import Submission.Work.C7.J_ode
import Submission.Work.C7.g67_deriv
import Submission.Work.C7.transport
import Submission.Work.C7.indep_four
import Submission.Work.C7.indep_five
import Submission.Work.C7.rat_ode
import Submission.Work.C7.rat_ode2
import Submission.Work.C7.indep_seven
import Submission.Work.C7.pureB_indep_of_subst

/-!
# Area C7 — assembly of the x-side proof of Lemma `seven`

Wiring of the x-side pieces into `PolyIndependent pureB`: the seven pullbacks
`g i = Bᵢ∘y` are `ℚ[x]`-linearly independent, and `pureB_indep_of_subst` descends this to
`ℚ[y]`-linear independence of `B₁,…,B₇`.
-/

noncomputable section

namespace Work.C7

open PowerSeries
open Submission.CDTPlan

/-- `g 0 = B₁∘y = 1`. -/
theorem g_zero : g 0 = 1 := by
  show (pureB 0).subst yps = 1
  have h : pureB 0 = (1 : PowerSeries ℚ) := by simp [pureB, B1]
  rw [h, show (1 : PowerSeries ℚ) = PowerSeries.C (1 : ℚ) by simp]
  rw [PowerSeries.subst_C]
  rfl

/-- The seven pullbacks are `ℚ[x]`-linearly independent. -/
theorem pullback_indep : PolyIndependent (fun i : Fin 7 => g i) := by
  obtain ⟨hf1, hf2, hf3⟩ := g_form
  obtain ⟨htr5, htr6, htr7⟩ := transport
  have hJ : 2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Jps
      - PowerSeries.X * Jps = 2 * (1 - PowerSeries.X) * Lps := J_ode hf1 g4_form_c7 htr5
  have h5i : PolyIndependent (fun i : Fin 5 => ![1, Lps, Lps ^ 2, Li2ps, Jps] i) :=
    indep_five indep_four hJ rat_ode.1 rat_ode.2.1 rat_ode.2.2
  exact indep_seven g_zero hf1 hf2 hf3 g4_form_c7 htr6 htr7 h5i hJ
    rat_ode2.1 rat_ode2.2 rat_ode.1 rat_ode.2.1

/-- **Lemma `seven`**: `B₁,…,B₇` are `ℚ(y)`-linearly independent. -/
theorem pureB_independent : PolyIndependent pureB :=
  pureB_indep_of_subst pullback_indep

end Work.C7
