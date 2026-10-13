import Mathlib
import Submission.Work.WilC4aP.Basic

namespace Work.WilC4aP

open scoped BigOperators Topology
open Filter

/-- A finite family of functions that is injective at a point `z₀` and continuous there is
injective on a whole ball around `z₀`. -/
theorem exists_ball_injective {m : ℕ} {η : Fin m → ℂ → ℂ} {z₀ : ℂ} (hη : ∀ j, ContinuousAt (η j) z₀)
    (hinj : Function.Injective fun j => η j z₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ Metric.ball z₀ ρ, Function.Injective fun j => η j z := by
  -- The product over all ordered pairs `i ≠ j` of `η i z - η j z`; it is continuous at `z₀`
  -- and nonzero there, so it stays nonzero on a ball, which forces injectivity.
  set F : ℂ → ℂ := fun z => ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i, (η i z - η j z) with hFdef
  have hcont : ContinuousAt F z₀ := by
    rw [hFdef]
    apply tendsto_finsetProd
    intro i _
    apply tendsto_finsetProd
    intro j _
    exact (hη i).sub (hη j)
  have hFne : F z₀ ≠ 0 := by
    rw [hFdef, Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hinj h).symm)
  have hev : ∀ᶠ z in 𝓝 z₀, F z ≠ 0 := hcont.eventually_ne hFne
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := hev
  refine ⟨ε, hεpos, ?_⟩
  intro z hz
  rw [Metric.mem_ball] at hz
  have hz0 : F z ≠ 0 := hε hz
  intro i j hij
  by_contra hne
  apply hz0
  rw [hFdef, Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [Finset.prod_eq_zero_iff]
  exact ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j⟩, sub_eq_zero.mpr hij⟩

end Work.WilC4aP
