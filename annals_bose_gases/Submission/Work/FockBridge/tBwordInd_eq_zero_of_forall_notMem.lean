import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FockBridge

open MeasureTheory

/-- **The box mean-free projection is killed by vanishing on the `A`-slabs.**  If the state `Ψ`
vanishes at every configuration having some slot in `A` (`∃ i, x i ∈ A`), then FS's box projection
`Q_{B,i}Ψ` — with the box indicator — vanishes identically in every slot.  Indeed, in the
box-indicator term either `x i ∉ A` (indicator `0`) or `x i ∈ A`, and then also `Ψ x = 0`; while
in the fibre integral `∫_{z∈A} Ψ(x[i↦z])` every `z ∈ A` makes `x[i↦z]` a configuration with slot
`i` in `A`, so the integrand is identically zero on `A`. -/
theorem boxQInd_eq_zero_of_forall_notMem {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {volA : ℝ} {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hΨ : ∀ x : Fin N → EuclideanSpace ℝ (Fin 3), (∃ i : Fin N, x i ∈ A) → Ψ x = 0) :
    ∀ i : Fin N, Work.UBBInputs8.boxQInd volA A i Ψ = 0 := by
  intro i
  funext x
  change Work.UBBInputs8.boxQInd volA A i Ψ x = 0
  rw [Work.UBBInputs8.boxQInd]
  have hInt : (∫ z in A, Ψ (Function.update x i z)) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro z hz
    exact hΨ _ ⟨i, by simpa using hz⟩
  have hxi : Work.UBBInputs8.boxPInd volA A i Ψ x = 0 := by
    rw [Work.UBBInputs8.boxPInd]
    by_cases hmem : x i ∈ A
    · rw [hInt, Set.indicator_of_mem hmem]
      ring
    · rw [Set.indicator_of_notMem hmem]
      ring
  rw [hxi]
  by_cases hmem : x i ∈ A
  · rw [Set.indicator_of_mem hmem, one_mul, hΨ x ⟨i, hmem⟩]
    ring
  · rw [Set.indicator_of_notMem hmem, zero_mul]
    ring

/-- **The FS box word `𝒯_B` annihilates states vanishing on the `A`-slabs.**  Both halves of
`tBwordInd` are built from `Q_{B,i}Ψ = boxQInd volA A i Ψ` — the gap term through the excited
count `cnPlusBoxInd` and the spectral term through the amplitude `tBamp χ p (Q_{B,i}Ψ)` — so when
every `Q_{B,i}Ψ` vanishes (`boxQInd_eq_zero_of_forall_notMem`) both vanish and the word is `0`. -/
theorem tBwordInd_eq_zero_of_forall_notMem {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {volA a s ε c : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hΨ : ∀ x : Fin N → EuclideanSpace ℝ (Fin 3), (∃ i : Fin N, x i ∈ A) → Ψ x = 0) :
    Work.UBBInputs8.tBwordInd a A volA χ s ε c Ψ = 0 := by
  have hQ := boxQInd_eq_zero_of_forall_notMem (volA := volA) hΨ
  simp only [Work.UBBInputs8.tBwordInd, Work.UBBInputs8.cnPlusBoxInd,
    Work.UBBInputs8.tBwordKinInd, Work.UBBInputs8.tBdiagFormInd, hQ]
  simp [Work.SmallBoxTBWord.tBamp]

end Work.FockBridge
