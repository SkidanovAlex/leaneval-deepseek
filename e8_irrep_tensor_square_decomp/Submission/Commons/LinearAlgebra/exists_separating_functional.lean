import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.GroupTheory.GroupAction.Ring

namespace Commons.LinearAlgebra

open Matrix

variable {K : Type*} [Field K]

/-- The linear functional `x ↦ ∑ i, v i * x i` on `ι → K`, i.e. the dot product with `v`. -/
def dotLin {ι : Type*} [Fintype ι] (v : ι → K) : Module.Dual K (ι → K) where
  toFun x := v ⬝ᵥ x
  map_add' x y := dotProduct_add v x y
  map_smul' a x := dotProduct_smul a v x

@[simp]
lemma dotLin_apply {ι : Type*} [Fintype ι] (v x : ι → K) : dotLin v x = v ⬝ᵥ x := rfl

lemma dotLin_single {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → K) (i : ι) :
    dotLin v (Pi.single i 1) = v i := by
  rw [dotLin_apply, dotProduct_single_one]

theorem exists_separating_functional {K ι : Type*} [Field K] [Infinite K] [Fintype ι]
    (s : Finset (ι → K)) :
    ∃ c : ι → K, ∀ μ ∈ s, ∀ ν ∈ s, (∑ i, c i * μ i) = (∑ i, c i * ν i) → μ = ν := by
  classical
  let T : Finset ((ι → K) × (ι → K)) := (s.product s).filter (fun p => p.1 ≠ p.2)
  let f : T → Module.Dual K (ι → K) := fun p => dotLin (p.1.1 - p.1.2)
  have hf : ∀ p : T, ∃ x, f p x ≠ 0 := by
    intro p
    have hp : p.1.1 ≠ p.1.2 := (Finset.mem_filter.mp p.2).2
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (sub_ne_zero.mpr hp)
    refine ⟨Pi.single i 1, ?_⟩
    show dotLin (p.1.1 - p.1.2) (Pi.single i 1) ≠ 0
    rw [dotLin_single]
    simpa using hi
  obtain ⟨c, hc⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨c, ?_⟩
  intro μ hμ ν hν hsum
  by_contra hne
  have hmem : (μ, ν) ∈ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hμ, hν⟩, hne⟩
  have hcontra : f ⟨(μ, ν), hmem⟩ c ≠ 0 := hc ⟨(μ, ν), hmem⟩
  apply hcontra
  show dotLin (μ - ν) c = 0
  rw [dotLin_apply, dotProduct]
  have h1 : (∑ i, (μ - ν) i * c i) = (∑ i, c i * μ i) - (∑ i, c i * ν i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, sub_mul]
    ring
  rw [h1, hsum, sub_self]

end Commons.LinearAlgebra