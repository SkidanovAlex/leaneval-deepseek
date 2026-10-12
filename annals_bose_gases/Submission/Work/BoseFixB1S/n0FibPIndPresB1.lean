import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.n0FibPIndPresB1` — the box projection preserves the `i`-fibre structure

Let `P_j = UBBInputs8.boxPInd volA A j` be FS's box condensate projection
`(P_{B,j}ψ)(x) = |B|⁻¹⟨1_B, ψ(x|j↦·)⟩·1_B(x j)` in slot `j`, and let `Ψ` be a state that is
*constant along the `i`-fibre through `c₀ ∈ A`*, in the sense that

  `Ψ x = 1_A(x i) · Ψ (x|i↦c₀)`  for every configuration `x`   (`hΨ`).

Then every `P_j Ψ` (`j` arbitrary, `x` arbitrary) satisfies the same relation:

  `(P_j Ψ)(x) = 1_A(x i) · (P_j Ψ)(x|i↦c₀)`.

## Proof

The projection unfolds to `(P_j Ψ)(x) = (1/volA)·(∫_A Ψ(x|j↦z) dz)·1_A(x j)`.

* If `j = i` the two-slot update `(update (update x i c₀) i z)` collapses to `update x i z`
  (`Function.update_idem`) while the outer box indicator becomes `1_A c₀ = 1` (`hc₀`); the
  resulting scalars commute.  (`hΨ` is not even needed here.)
* If `j ≠ i` the two channels in the integral are handled pointwise by `hΨ` at the configuration
  `x|j↦z`: the `i`-th slot of that configuration is still `x i` (`Function.update_of_ne`), and
  the two updates in distinct slots commute (`Function.update_comm`).  Pulling the resulting
  constant `1_A(x i)` out of the integral (`MeasureTheory.integral_const_mul`) and using that
  the `j`-th slot is untouched by the update at `i` (`Function.update_of_ne`, `hji`) leaves a
  commutativity-of-scalars identity.
-/

namespace Work.BoseFixB1S

theorem n0FibPIndPresB1 {N : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {i : Fin N} {c₀ : EuclideanSpace ℝ (Fin 3)}
    (hc₀ : c₀ ∈ A) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x : Submission.BoseGases.X N,
      Ψ x = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ (Function.update x i c₀)) :
    ∀ j : Fin N, ∀ x : Submission.BoseGases.X N,
      Work.UBBInputs8.boxPInd volA A j Ψ x
        = A.indicator (fun _ => (1 : ℝ)) (x i)
          * Work.UBBInputs8.boxPInd volA A j Ψ (Function.update x i c₀) := by
  intro j x
  simp only [Work.UBBInputs8.boxPInd]
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_idem, Function.update_self, Set.indicator_of_mem hc₀]
    ring
  · have hij : i ≠ j := fun h => hji h.symm
    have hupd : (Function.update x i c₀) j = x j := Function.update_of_ne hji c₀ x
    have hIntEq : (∫ z in A, Ψ (Function.update x j z))
        = ∫ z in A, A.indicator (fun _ => (1 : ℝ)) (x i)
            * Ψ (Function.update (Function.update x i c₀) j z) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [hΨ (Function.update x j z), Function.update_of_ne hij,
        (Function.update_comm hij c₀ z x).symm]
    rw [hIntEq, MeasureTheory.integral_const_mul, hupd]
    ring

end Work.BoseFixB1S
