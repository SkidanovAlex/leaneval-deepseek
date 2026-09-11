import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ChallengeDeps
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open Classical
open scoped NNReal ENNReal BigOperators

namespace Submission

namespace The13SupEval

/-- coefficient commutes with a Fintype-indexed NNReal sup -/
lemma coe_iSup_fintype {γ : Type*} [Fintype γ] (g : γ → ℝ≥0) :
    ((⨆ i : γ, g i : ℝ≥0) : ℝ≥0∞) = ⨆ i : γ, ((g i : ℝ≥0) : ℝ≥0∞) := by
  calc
    ((⨆ i : γ, g i : ℝ≥0) : ℝ≥0∞) = (((Finset.univ : Finset γ).sup g : ℝ≥0) : ℝ≥0∞) := by
      rw [Finset.sup_univ_eq_ciSup]
    _ = (Finset.univ : Finset γ).sup (fun i : γ => ((g i : ℝ≥0) : ℝ≥0∞)) := by
      exact ENNReal.coe_finset_sup
    _ = ⨆ i : γ, ((g i : ℝ≥0) : ℝ≥0∞) := by
      rw [Finset.sup_eq_iSup]
      simp

/-- membership sup over a finite set 𝓕 equals the sup over the subtype of its members -/
lemma mem_iSup_eq_subtype_iSup {ι : Type*} (𝓕 : Set ι) (h𝓕 : Finite 𝓕) (g : ι → ℝ≥0) :
    (⨆ f : ι, ⨆ (_ : f ∈ 𝓕), g f) = ⨆ i : {f // f ∈ 𝓕}, g i.1 := by
  classical
  let γ := {f : ι // f ∈ 𝓕}
  haveI : Finite γ := h𝓕
  letI : Fintype γ := Fintype.ofFinite γ
  change (⨆ f : ι, ⨆ (_ : f ∈ 𝓕), g f) = ⨆ i : γ, g i.1
  have hbdd : BddAbove (Set.range (fun i : γ => g i.1)) := by
    refine ⟨(Finset.univ : Finset γ).sup (fun i : γ => g i.1), ?_⟩
    rintro y hy
    rcases hy with ⟨i, rfl⟩
    exact Finset.le_sup (s := (Finset.univ : Finset γ)) (f := fun i : γ => g i.1) (Finset.mem_univ i)
  have hempty : sSup ∅ ≤ ⨆ i : γ, g i.1 := by
    rw [csSup_empty]
    exact bot_le
  exact cbiSup_eq_ciSup_subtype (p := fun f : ι => f ∈ 𝓕) (f := fun (f : ι) (_ : f ∈ 𝓕) => g f) hbdd hempty

/-- coefficient commutes with the finite-family function sup, pointwise -/
lemma eval_sup_coe {ι Ω : Type*} (𝓕 : Set ι) (h𝓕 : Finite 𝓕) (Z : ι → Ω → ℝ≥0) (ω : Ω) :
    (((⨆ f ∈ 𝓕, Z f) ω : ℝ≥0) : ℝ≥0∞) = ⨆ i : {f // f ∈ 𝓕}, ((Z i.1 ω : ℝ≥0) : ℝ≥0∞) := by
  classical
  let γ := {f : ι // f ∈ 𝓕}
  haveI : Finite γ := h𝓕
  letI : Fintype γ := Fintype.ofFinite γ
  simp only [iSup_apply]
  rw [show (⨆ f : ι, ⨆ (_ : f ∈ 𝓕), Z f ω) = (⨆ i : γ, Z i.1 ω) from
    mem_iSup_eq_subtype_iSup 𝓕 h𝓕 (fun f : ι => Z f ω)]
  exact coe_iSup_fintype (fun i : γ => Z i.1 ω)

end The13SupEval
end Submission
