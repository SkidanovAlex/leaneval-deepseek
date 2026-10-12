import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.TrialState.Basic.integral_actPerm_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.TrialState.Basic

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

/-- Combinatorial input: given two distinct indices `a ≠ c` and two distinct indices
`b ≠ d`, there is a permutation of the particle labels sending `a` to `b` and `c` to `d`.

The witness is `(a b) · (σ₁ c, d)` where `σ₁ = (a b)`: the transposition `(a b)` moves
`a` to `b`, and the second transposition then fixes `b` (it acts on the two points
`σ₁ c` and `d`, neither of which is `b`) while sending `σ₁ c` to `d`. -/
lemma exists_perm_apply_eq_apply_eq {N : ℕ} {a b c d : Fin N} (hac : a ≠ c) (hbd : b ≠ d) :
    ∃ σ : Equiv.Perm (Fin N), σ a = b ∧ σ c = d := by
  have hb : b ≠ Equiv.swap a b c := by
    intro h
    rcases eq_or_ne c b with hcb | hcb
    · rw [hcb, Equiv.swap_apply_right] at h
      exact hac (h.symm.trans hcb.symm)
    · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) hcb] at h
      exact hcb h.symm
  refine ⟨(Equiv.swap a b).trans (Equiv.swap (Equiv.swap a b c) d), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hb hbd
  · rw [Equiv.trans_apply]
    exact Equiv.swap_apply_left _ _

theorem integral_mul_pairSum_eq_card {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Λ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hΛperm : ∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → EuclideanSpace ℝ (Fin 3)),
      Λ (Submission.BoseGases.actPerm N σ x) = Λ x)
    (hΛm : AEStronglyMeasurable Λ (volume.restrict (Submission.BoseGases.abox N ℓ)))
    (hΛint : Integrable Λ (volume.restrict (Submission.BoseGases.abox N ℓ)))
    (hGm : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => G p.1 p.2))
    {B : ℝ} (hB : ∀ a b : EuclideanSpace ℝ (Fin 3), ‖G a b‖ ≤ B)
    (hint : ∀ p ∈ Submission.BoseGases.pairSet N,
      Integrable (fun x : Fin N → EuclideanSpace ℝ (Fin 3) => Λ x * G (x p.1) (x p.2))
        (volume.restrict (Submission.BoseGases.abox N ℓ)))
    {i j : Fin N} (hij : i ≠ j) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Λ x * (∑ p ∈ Submission.BoseGases.pairSet N, G (x p.1) (x p.2)))
      = ((Submission.BoseGases.pairSet N).card : ℝ)
        * (∫ x in Submission.BoseGases.abox N ℓ, Λ x * G (x i) (x j)) := by
  -- All the pair integrals `∫ Λ x * G (x p.1) (x p.2)` are equal, by relabelling.
  have hconst : ∀ p ∈ Submission.BoseGases.pairSet N,
      (∫ x in Submission.BoseGases.abox N ℓ, Λ x * G (x p.1) (x p.2))
        = ∫ x in Submission.BoseGases.abox N ℓ, Λ x * G (x i) (x j) := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by
      simpa [Submission.BoseGases.pairSet] using hp
    obtain ⟨σ, hσ1, hσ2⟩ :=
      exists_perm_apply_eq_apply_eq (a := i) (b := p.1) (c := j) (d := p.2) hij hpne
    have hσ := integral_actPerm_abox (N := N) (ℓ := ℓ) σ
      (fun y : Fin N → EuclideanSpace ℝ (Fin 3) => Λ y * G (y i) (y j))
    have hpt : ∀ x : Fin N → EuclideanSpace ℝ (Fin 3),
        (fun y => Λ y * G (y i) (y j)) (Submission.BoseGases.actPerm N σ x)
          = Λ x * G (x p.1) (x p.2) := by
      intro x
      change Λ (Submission.BoseGases.actPerm N σ x)
          * G ((Submission.BoseGases.actPerm N σ x) i)
              ((Submission.BoseGases.actPerm N σ x) j)
          = Λ x * G (x p.1) (x p.2)
      rw [hΛperm σ x]
      have hidx1 : (Submission.BoseGases.actPerm N σ x) i = x p.1 := by
        simp [Submission.BoseGases.actPerm, hσ1]
      have hidx2 : (Submission.BoseGases.actPerm N σ x) j = x p.2 := by
        simp [Submission.BoseGases.actPerm, hσ2]
      rw [hidx1, hidx2]
    rw [funext hpt] at hσ
    simpa using hσ
  -- Interchange the finite sum and the integral.
  have hsum : (∫ x in Submission.BoseGases.abox N ℓ,
        Λ x * (∑ p ∈ Submission.BoseGases.pairSet N, G (x p.1) (x p.2)))
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ, Λ x * G (x p.1) (x p.2) := by
    rw [show (fun x : Fin N → EuclideanSpace ℝ (Fin 3) =>
          Λ x * (∑ p ∈ Submission.BoseGases.pairSet N, G (x p.1) (x p.2)))
        = (fun x : Fin N → EuclideanSpace ℝ (Fin 3) =>
            ∑ p ∈ Submission.BoseGases.pairSet N, Λ x * G (x p.1) (x p.2)) by
          funext x
          rw [Finset.mul_sum]]
    exact integral_finsetSum (Submission.BoseGases.pairSet N) (fun p hp => hint p hp)
  rw [hsum]
  calc ∑ p ∈ Submission.BoseGases.pairSet N,
        (∫ x in Submission.BoseGases.abox N ℓ, Λ x * G (x p.1) (x p.2))
      = ∑ _p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ, Λ x * G (x i) (x j) :=
        Finset.sum_congr rfl (fun p hp => hconst p hp)
    _ = ((Submission.BoseGases.pairSet N).card : ℝ)
        * (∫ x in Submission.BoseGases.abox N ℓ, Λ x * G (x i) (x j)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Work.TrialState.Basic
