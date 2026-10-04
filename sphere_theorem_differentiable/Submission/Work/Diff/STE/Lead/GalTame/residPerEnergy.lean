import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.Lead.GalTame.GalCenter
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory

/-!
# The `Hᵐ` energy of the periodisation on the centred cube

For a smooth `f : (Fin n → ℝ) → ℂ` whose *topological* support is contained in the open cube
`(-1/2,1/2)^n` — in particular for any chart function localised in a ball of radius `< 1/2` — the
periodisation `P f = ∑' k : Fin n → ℤ, f (· + k)` is a smooth `1`-periodic function, and its `Hᵐ`
energy over the unit cube `(0,1]^n` is bounded by a constant (depending only on `n`) times the `Hᵐ`
energy of `f` over the *centred* cube `(-1/2,1/2]^n`:

  `ENormSq m (per f) ≤ C * CENormSq m f`.

The proof is a reduction to the already proved tail estimate

`Work.Diff.STE.B3.steB3_ENormSq_periodization_le_integral`,

which bounds `ENormSq m (per f)` by `(2^n)^2` times the sum of the *whole space* integrals
`∫_{ℝⁿ} ‖∂^l f‖²`, together with the observation that — because the support of every iterated
partial derivative of `f` is contained in the topological support of `f` — those derivatives are
supported inside the open cube, hence inside the centred cube; the integrals over `ℝⁿ` and over
`(-1/2,1/2]^n` therefore agree.
-/

/-- The support of an iterated partial derivative of `f` is contained in the topological support
of `f`: off `tsupport f` the function `f` vanishes on a neighbourhood, and there all its partial
derivatives vanish. -/
lemma support_pdVec_subset_tsupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (l : Fin m → ι) (f : (ι → ℝ) → ℂ) :
    Function.support (Work.Diff.STE.pdVec m l f) ⊆ tsupport f := by
  have h := Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn l) f
  simpa [Work.Diff.STE.pdVec, tsupport] using h

/-- The open cube `(-1/2,1/2)^ι` is contained in the centred cube `(-1/2,1/2]^ι`. -/
lemma openCube_subset_cubeC (ι : Type*) :
    Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
      ⊆ cubeC ι := by
  intro x hx
  rw [cubeC]
  intro i _
  have h := hx i (Set.mem_univ i)
  exact ⟨h.1, le_of_lt h.2⟩

/-- A function supported in the open cube `(-1/2,1/2)^ι` has the same `L²` norm over all of
`ℝ^ι` as over the centred cube `(-1/2,1/2]^ι`. -/
lemma integral_normSq_eq_setIntegral_cubeC {ι : Type*} [Fintype ι]
    {g : (ι → ℝ) → ℂ}
    (hg : Function.support g ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    (∫ x : ι → ℝ, ‖g x‖ ^ 2) = ∫ x in cubeC ι, ‖g x‖ ^ 2 := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
  have hxC : x ∉ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun h => hx (openCube_subset_cubeC ι h)
  have hzero : g x = 0 := by
    by_contra h0
    exact hxC (hg (Function.mem_support.mpr h0))
  rw [hzero]
  simp

theorem residPerEnergy {n m : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (Fin n → ℝ) → ℂ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f →
      tsupport f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ =>
          ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k))
        ≤ C * Work.Diff.STE.Lead.GalTame.CENormSq m f := by
  classical
  refine ⟨((Work.Diff.STE.csqp_boxIdx (Fin n)).card : ℝ) ^ 2, by positivity, ?_⟩
  intro f hf hts
  have hf' : ContDiff ℝ (⊤ : ℕ∞) f := hf
  have hsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun x hx => hts (subset_closure hx)
  have hmain := Work.Diff.STE.B3.steB3_ENormSq_periodization_le_integral
    (ι := Fin n) hf' hsupp m
  have hkey : ∀ l : Fin m → Fin n,
      (∫ x : Fin n → ℝ, ‖Work.Diff.STE.pdVec m l f x‖ ^ 2)
        = ∫ x in cubeC (Fin n), ‖Work.Diff.STE.pdVec m l f x‖ ^ 2 :=
    fun l => integral_normSq_eq_setIntegral_cubeC
      ((support_pdVec_subset_tsupport m l f).trans hts)
  calc Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ =>
          ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k))
      ≤ ((Work.Diff.STE.csqp_boxIdx (Fin n)).card : ℝ) ^ 2
          * ∑ l : Fin m → Fin n,
              ∫ x : Fin n → ℝ, ‖Work.Diff.STE.pdVec m l f x‖ ^ 2 := hmain
    _ = ((Work.Diff.STE.csqp_boxIdx (Fin n)).card : ℝ) ^ 2
          * Work.Diff.STE.Lead.GalTame.CENormSq m f := by
        rw [CENormSq]
        exact congrArg _ (Finset.sum_congr rfl (fun l _ => hkey l))

end Work.Diff.STE.Lead.GalTame
