import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.boxQInd_eq_sum_sectorPiece
import Submission.Work.FockBridge.boxQInd_eq_zero_of_notMem_sectorSet
import Submission.Work.FockBridge.cnPlusBoxInd_eq_sum_sectorPiece
import Submission.Work.FockBridge.tBamp_eq_zero_of_notMem_ampSector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.FockBridge.sum_tBamp_normSq`

**The squared-norm (Parseval) form of the Fock decomposition of the windowed amplitude.**

The windowed amplitude `tBamp χ p Ψ i x = ∫_z (χ z)e^{−i⟪p,z⟫}Ψ(x_{i←z})dz` is a linear functional
of the state `Ψ` (`tBamp_eq_sum_sectorPiece`), but the *energy* of the residual involves its squared
norm, and the squared norm of a sum is **not** the sum of the squared norms unless the summands are
orthogonal.  Here the orthogonality is the geometric content of the Fock/particle-number
decomposition:

* the state `Φ` splits into its `A`-occupancy pieces `Φ = Σ_k 1_{sector k}Φ` (`sum_sectorPiece`);
* FS's projection `Q_{A,i} = 1_A(x_i) − P_{A,i}` (`Work.UBBInputs8.boxQInd`) maps the count-`k`
  piece to a function **supported in the `A`-sector of count `k`**
  (`boxQInd_sectorPiece_eq_zero`), so the amplitude of that piece is supported in the *amplitude*
  sector `ampSector A i k`;
* the amplitude sectors of distinct counts are disjoint (`ampSector_disjoint`), because the
  amplitude replaces slot `i` by a point `z ∈ supp χ ⊆ A`: it counts the box occupancy of
  `x[i↦z]`, which is the *shifted* count `if x i ∈ A then n_A(x) else n_A(x)+1`.

Hence for a fixed configuration `x` **at most one** of the amplitudes
`k ↦ tBamp χ p (Q_{A,i}(1_{sector k}Φ)) i x` can be nonzero, namely the one at the shifted count
`k₀(x)`.  The sum over `k` therefore reduces to a single term, and the target identity follows from
the amplitude identity `tBamp χ p (Q_{A,i}Φ) i x = tBamp χ p (Q_{A,i}(1_{sector k₀}Φ)) i x`, which
is just the linearity of `tBamp` in the state *evaluated on the fibre* over `supp χ`.

Two auxiliary lemmas are proved in this file:

* `tBamp_congr_of_eqOn_fibre` — `tBamp` depends on its state only through the slot-`i` fibre values
  over `supp χ` (the general congruence form of the amplitude identity);
* `ampShift_le` — the shifted count never exceeds `N` (`ampSector A i k = ∅` for `k > N`, the
  amplitude-sector analogue of `sectorSet_eq_empty_of_lt`).  This is what puts the shifted count
  into the summation range `range (N+1)`.

The two `Integrable` hypotheses of the statement are not needed for this identity: it is a pointwise
statement about the amplitudes, not an integral identity over `x`.
-/

noncomputable section

open MeasureTheory Filter
open Classical
open scoped BigOperators

namespace Work.FockBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

variable {N : ℕ}

/-! ## 1. The amplitude only sees the fibre over `supp χ` -/

/-- **`tBamp` depends on its state only through the slot-`i` fibre over the support of `χ`.**
For every `z` either `χ z = 0` — in which case the integrand of the amplitude vanishes whatever the
state is — or `χ z ≠ 0`, in which case `z ∈ A` by `hχ` and the hypothesis `h` gives the equality of
the fibre values.  So the two integrands agree *everywhere* and the Bochner integrals agree; no
measurability or integrability is needed (the Bochner integral is a total function). -/
theorem tBamp_congr_of_eqOn_fibre {N : ℕ} {A : Set ℝ³}
    (χ : ℝ³ → ℝ) (hχ : ∀ z, χ z ≠ 0 → z ∈ A)
    (p : ℝ³) (i : Fin N)
    {Ψ₁ Ψ₂ : (Fin N → ℝ³) → ℝ} {x : Fin N → ℝ³}
    (h : ∀ z ∈ A, Ψ₁ (Function.update x i z) = Ψ₂ (Function.update x i z)) :
    Work.SmallBoxTBWord.tBamp χ p Ψ₁ i x = Work.SmallBoxTBWord.tBamp χ p Ψ₂ i x := by
  unfold Work.SmallBoxTBWord.tBamp
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  by_cases hz : χ z = 0
  · rw [hz]
    simp
  · rw [h z (hχ z hz)]

/-! ## 2. The shifted (amplitude-sector) count is bounded by `N` -/

/-- **The amplitude sector of count `k` is empty for `k > N`.**  The amplitude replaces slot `i` by
a point of `A`, so the count it sees is the shifted count
`if x i ∈ A then n_A(x) else n_A(x)+1`; when the `+1` is taken, slot `i` itself is *not* counted, so
the shifted count is still at most `N`. -/
theorem ampShift_le (A : Set ℝ³) (i : Fin N) {x : Fin N → ℝ³} {k : ℕ}
    (hk : x ∈ ampSector A i k) : k ≤ N := by
  have hN : 0 < N := i.pos
  rw [mem_ampSector_iff] at hk
  by_cases hxi : x i ∈ A
  · rw [if_pos hxi] at hk
    rw [← hk]
    exact boxOccupancy_le A x
  · rw [if_neg hxi] at hk
    -- slot `i` is not counted in the `A`-occupancy, so the count is at most `N - 1`
    have hcard : boxOccupancy A x ≤ (Finset.univ.erase i).card :=
      Finset.card_le_card (fun j hj => by
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_erase]
        exact ⟨fun hji => hxi (hji ▸ hj.2), Finset.mem_univ j⟩)
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      at hcard
    rw [← hk]
    omega

/-! ## 3. The squared-norm decomposition -/

theorem sum_tBamp_normSq {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (hχ : ∀ z, χ z ≠ 0 → z ∈ A)
    {volA : ℝ} (i : Fin N) (p : EuclideanSpace ℝ (Fin 3))
    {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hint : ∀ (k : ℕ) (x : Fin N → EuclideanSpace ℝ (Fin 3)),
      MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ)
              (Function.update x i z)) : ℂ)))
    (hint0 : ∀ x : Fin N → EuclideanSpace ℝ (Fin 3),
      MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z)) : ℂ)))
    (x : Fin N → EuclideanSpace ℝ (Fin 3)) :
    ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2
      = ∑ k ∈ Finset.range (N + 1),
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i
            (Work.FockBridge.sectorPiece A k Φ)) i x‖ ^ 2 := by
  classical
  -- the shifted count of `x`: the unique sector index whose amplitude can survive
  set k0 : ℕ := (if x i ∈ A then boxOccupancy A x else boxOccupancy A x + 1) with hk0
  have hxk0 : x ∈ ampSector A i k0 := (mem_ampSector_iff A i k0 x).mpr hk0.symm
  have hk0mem : k0 ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (ampShift_le A i hxk0))
  -- the full amplitude is the amplitude of the `k0`-piece
  have hB : Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x
      = Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k0 Φ)) i x := by
    refine tBamp_congr_of_eqOn_fibre χ hχ p i (fun z hz => ?_)
    have hocc : boxOccupancy A (Function.update x i z) = k0 :=
      (boxOccupancy_update_of_mem A x i hz).trans hk0.symm
    exact boxQInd_sectorPiece_eq_of_mem (A := A) (volA := volA) hA i
      ((mem_sectorSet_iff A k0 (Function.update x i z)).mpr hocc)
  -- every other amplitude vanishes
  have hzero : ∀ k ∈ Finset.range (N + 1), k ≠ k0 →
      ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2 = 0 := by
    intro k _ hne
    have hxnot : x ∉ ampSector A i k := by
      intro hmem
      rw [mem_ampSector_iff] at hmem
      exact hne (hmem.symm.trans hk0.symm)
    have h0 : Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (sectorPiece A k Φ)) i x = 0 :=
      tBamp_eq_zero_of_notMem_ampSector hχ p
        (fun y hy => boxQInd_sectorPiece_eq_zero hA i hy) i hxnot
    rw [h0]
    simp
  rw [hB, Finset.sum_eq_single k0 hzero (fun hnot => absurd hk0mem hnot)]

end Work.FockBridge
