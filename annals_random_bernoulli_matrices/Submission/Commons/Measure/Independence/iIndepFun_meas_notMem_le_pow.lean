import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Probability.Independence.Basic

namespace Commons.Measure.Independence

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Let `ξ : Fin m → Ω → ℝ` be a family of mutually independent real-valued random variables on
`(Ω, P)` in the sense of `iIndepFun ξ P` (the same independence notion as in the challenge
statements: `iIndepFun ξ P`), and suppose each of them satisfies the small-ball bound
`P {x | |ξ i x| ≤ η} ≤ τ` with `τ : ℝ≥0∞`.  Then for any subset `B : Finset (Fin m)` of indices,
the probability that `|ξ i x| ≤ η` holds for every index outside `B` is at most `τ^(m − B.card)`.

Note: no measurability hypothesis on `ξ` is required; the sets below are preimages of Borel sets.
Use `iIndepFun.meas_iInter` (or `iIndepFun.precomp` to restrict the family to the complement of `B`). -/
theorem iIndepFun_meas_notMem_le_pow {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {ξ : Fin m → Ω → ℝ} (hξ : iIndepFun ξ P) (B : Finset (Fin m))
    {η : ℝ} (τ : ℝ≥0∞) (hsmall : ∀ i : Fin m, P {x | |ξ i x| ≤ η} ≤ τ) :
    P {x | ∀ i : Fin m, i ∉ B → |ξ i x| ≤ η} ≤ τ ^ (m - B.card) := by
  classical
  let A : Fin m → Set Ω := fun i => {x | |ξ i x| ≤ η}
  let C : Finset (Fin m) := Bᶜ
  have hA : ∀ i : Fin m, P (A i) ≤ τ := by
    intro i
    simpa [A] using hsmall i
  have hmeas : ∀ i : Fin m,
      MeasurableSet[(inferInstance : MeasurableSpace ℝ).comap (ξ i)] (A i) := by
    intro i
    dsimp [A]
    rw [show {x | |ξ i x| ≤ η} = (ξ i) ⁻¹' (Set.Icc (-η) η) by
      ext x
      simp [abs_le]]
    exact (MeasurableSpace.measurableSet_comap
      (m := (inferInstance : MeasurableSpace ℝ))
      (s := (ξ i) ⁻¹' (Set.Icc (-η) η))).2
        ⟨Set.Icc (-η) η, measurableSet_Icc, rfl⟩
  have hprod : P (⋂ i ∈ C, A i) = ∏ i ∈ C, P (A i) := by
    exact hξ.meas_biInter (S := C) (s := A) (by intro i hi; exact hmeas i)
  have hset : {x | ∀ i : Fin m, i ∉ B → |ξ i x| ≤ η} = ⋂ i ∈ C, A i := by
    ext x
    simp only [Set.mem_iInter₂]
    constructor
    · intro hx i hiC
      exact hx i (by simpa [C] using hiC)
    · intro hx i hiB
      exact hx i (by simp [C, hiB])
  calc
    P {x | ∀ i : Fin m, i ∉ B → |ξ i x| ≤ η} = P (⋂ i ∈ C, A i) := by rw [hset]
    _ = ∏ i ∈ C, P (A i) := hprod
    _ ≤ ∏ i ∈ C, τ := by
      refine Finset.prod_le_prod ?_ ?_
      · intro i hi
        exact bot_le
      · intro i hi
        exact hA i
    _ = τ ^ C.card := by
      exact Finset.prod_const τ
    _ = τ ^ (m - B.card) := by
      congr 1
      simpa [C] using Finset.card_compl B

end Commons.Measure.Independence