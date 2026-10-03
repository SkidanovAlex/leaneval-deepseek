/-
# The final bookkeeping of `blindConvertK`

Step 7 of the route in `NOTES_blindConvertK_SESSION.md`: once a family `P` of pairs is known with

* `P ⊆` the pair box,
* the Gowers transform of `β` at `(p.1, ĥ(p.1), p.2)` equal to the pinned value `v₀`, and
* the summands of the aggregate at `β` bounded below by `γ/2` on `P`,

then the aggregate at the **blind** phases `∑ i, blindPhase β (ĥ u) v₀ u v i` is at least
`(γ/2)·|P|/|pair box|`.  The blind phases agree with `β` on `P` (that is `sum_blindPhase` plus the
pinning), so this is pure bookkeeping.
-/

import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_front
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_lowrank

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

/-- **Step 7 of the route.**  If the pairs of `P` have the transform of `β` at `(p.1, ĥ p.1, p.2)`
pinned to `v₀`, then the blind phases agree with `β` on `P`, and the aggregate at the blind phases
is at least `(γ/2)·|P|/|pairBox|`. -/
theorem blind_bookkeeping {σ B D : ℕ} {F : ℤ → ℂ}
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
    {P : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))} (hfr : (Fin σ → ℤ) → Fin σ → ℤ)
    (v₀ : ℝ) (i₀ : Fin σ) {γ : ℝ} (hD : 1 ≤ D)
    (hPbox : P ⊆ pairBox σ D)
    (hpin : ∀ p ∈ P, gowersDiff β (hfr p.1) p.1 p.2 = v₀)
    (hlvl : ∀ p ∈ P, γ / 2 ≤ cubeCorr σ B F β p.1 p.2) :
    γ / 2 * (P.card : ℝ) ≤ ((pairBox σ D).card : ℝ) *
      aggr σ D B F (fun u v => ∑ i : Fin σ, blindPhase β (hfr u) v₀ u v i₀ i) := by
  classical
  -- the blind phases agree with `β` on `P`
  have hphase : ∀ p ∈ P, (∑ i : Fin σ, blindPhase β (hfr p.1) v₀ p.1 p.2 i₀ i) = β p.1 p.2 := by
    intro p hp
    rw [sum_blindPhase, hpin p hp]
    ring
  -- the aggregate at the blind phases dominates the `P`-part at `β`
  have hPpos : (0 : ℝ) < ((pairBox σ D).card : ℝ) := by
    have hc : 0 < (pairBox σ D).card := Finset.card_pos.mpr ⟨(1, 1), by
      rw [pairBox, Finset.mem_product]
      constructor <;> refine Fintype.mem_piFinset.mpr (fun _ => ?_)
      · show (1 : ℤ) ∈ Work.Peluse.arithIcc 1 D
        rw [Work.Peluse.Ulower.mem_arithIcc_one]
        exact ⟨le_refl 1, by exact_mod_cast hD⟩
      · show (1 : ℤ) ∈ Work.Peluse.arithIcc 1 D
        rw [Work.Peluse.Ulower.mem_arithIcc_one]
        exact ⟨le_refl 1, by exact_mod_cast hD⟩⟩
    exact_mod_cast hc
  have hsum_eq : ∑ p ∈ P, cubeCorr σ B F (fun u v => ∑ i : Fin σ,
        blindPhase β (hfr u) v₀ u v i₀ i) p.1 p.2
      = ∑ p ∈ P, cubeCorr σ B F β p.1 p.2 := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [cubeCorr]
    rw [hphase p hp]
  have hsplit : ∑ p ∈ P, cubeCorr σ B F β p.1 p.2 ≤
      ∑ p ∈ pairBox σ D, cubeCorr σ B F (fun u v => ∑ i : Fin σ,
        blindPhase β (hfr u) v₀ u v i₀ i) p.1 p.2 := by
    have hbound : ∀ p ∈ pairBox σ D, p ∉ P → (0 : ℝ) ≤
        cubeCorr σ B F (fun u v => ∑ i : Fin σ, blindPhase β (hfr u) v₀ u v i₀ i) p.1 p.2 :=
      fun p _ _ => sq_nonneg _
    calc ∑ p ∈ P, cubeCorr σ B F β p.1 p.2
        = ∑ p ∈ P, cubeCorr σ B F (fun u v => ∑ i : Fin σ,
            blindPhase β (hfr u) v₀ u v i₀ i) p.1 p.2 := hsum_eq.symm
      _ ≤ ∑ p ∈ pairBox σ D, cubeCorr σ B F (fun u v => ∑ i : Fin σ,
            blindPhase β (hfr u) v₀ u v i₀ i) p.1 p.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hPbox hbound
  have hlower : (γ / 2) * (P.card : ℝ) ≤ ∑ p ∈ P, cubeCorr σ B F β p.1 p.2 := by
    have h1 : ∑ p ∈ P, (γ / 2) ≤ ∑ p ∈ P, cubeCorr σ B F β p.1 p.2 :=
      Finset.sum_le_sum hlvl
    rwa [Finset.sum_const, nsmul_eq_mul, mul_comm] at h1
  rw [aggr_eq]
  have hfin : ((pairBox σ D).card : ℝ) *
      (((pairBox σ D).card : ℝ)⁻¹ *
        ∑ p ∈ pairBox σ D, cubeCorr σ B F (fun u v => ∑ i : Fin σ,
          blindPhase β (hfr u) v₀ u v i₀ i) p.1 p.2)
      = ∑ p ∈ pairBox σ D, cubeCorr σ B F (fun u v => ∑ i : Fin σ,
          blindPhase β (hfr u) v₀ u v i₀ i) p.1 p.2 := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hPpos), one_mul]
  rw [hfin]
  exact le_trans hlower hsplit

end

end Work.Peluse.Ulower.StepLe
