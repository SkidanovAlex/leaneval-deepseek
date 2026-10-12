import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.Strat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PerSector

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

variable {N : ℕ}

/-- **The windowed amplitude of a slot piece is supported in the amplitude shift set.**  The amplitude
`tBamp χ p Ψ i x = ∫_z χ z·e^{−i⟪p,z⟫}·Ψ(x[i↦z])dz` samples only the points `z` with `χ z ≠ 0`, i.e.
(by `hχ`) `z ∈ A`; replacing slot `i` of a configuration by such a point `z` puts slot `i` *into*
the box, so the only way the projection `Q_{A,i}` of the slot piece `slotPiece A S Φ` can be nonzero
along the fibre is that `i ∈ S` and all *other* slots agree with `S` — i.e. that `x ∈ slotAmpSet A S i`.
This is the atom of the slot additivity of the spectral half of the localised kinetic word. -/
theorem tBamp_slotPiece_eq_zero_of_notMem_slotAmpSet {A : Set ℝ³} (χ : ℝ³ → ℝ)
    (hχ : ∀ z : ℝ³, χ z ≠ 0 → z ∈ A) {volA : ℝ} (i : Fin N) {Φ : X N → ℝ}
    (S : Finset (Fin N)) (p : ℝ³) {x : X N} (hx : x ∉ slotAmpSet A S i) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ)) i x = 0 := by
  classical
  -- **The combinatorial core.**  If slot `i` of the point `z` lies in `A`, then no configuration
  -- agreeing with `x` off `i` and carrying `z` at slot `i` can lie in the slot set `S`: the slot
  -- condition at `i` forces `i ∈ S`, and then the conditions at the other slots would put `x`
  -- itself in the amplitude shift set `slotAmpSet A S i`, contradicting `hx`.
  have hkey : ∀ z ∈ A, Function.update x i z ∉ slotSet A S := by
    intro z hz hmem
    rw [mem_slotAmpSet_iff] at hx
    have hmemall : ∀ j : Fin N, (Function.update x i z j ∈ A ↔ j ∈ S) :=
      (mem_slotSet_iff A S (Function.update x i z)).mp hmem
    refine hx ⟨?_, ?_⟩
    · have h := hmemall i
      rw [Function.update_self] at h
      exact h.mp hz
    · intro j hj
      have h := hmemall j
      rwa [Function.update_of_ne hj] at h
  -- **The projection vanishes along the fibre.**  `Q_{A,i}` of the slot piece is killed at every
  -- `Function.update x i z`: either `z ∉ A`, in which case both of its terms carry the box
  -- indicator at `z`, or `z ∈ A`, in which case the slot piece and the slot-`i` fibre mean it
  -- contains both vanish by the combinatorial core.
  have hq : ∀ z : ℝ³, Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ)
      (Function.update x i z) = 0 := by
    intro z
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Function.update_self]
    by_cases hzA : z ∈ A
    · have hval : slotPiece A S Φ (Function.update x i z) = 0 :=
        Set.indicator_of_notMem (hkey z hzA) Φ
      have hInt : (∫ z' in A, slotPiece A S Φ
          (Function.update (Function.update x i z) i z')) = 0 := by
        refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun z' hz' => ?_)
        rw [Function.update_idem]
        exact Set.indicator_of_notMem (hkey z' hz') Φ
      have hind : A.indicator (fun _ : ℝ³ => (1 : ℝ)) z = 1 :=
        Set.indicator_of_mem hzA _
      rw [hind, hval, hInt]
      ring
    · have hind : A.indicator (fun _ : ℝ³ => (1 : ℝ)) z = 0 :=
        Set.indicator_of_notMem hzA _
      rw [hind]
      ring
  -- Hence the amplitude integrand is identically zero, and so is the integral.
  simp only [Work.SmallBoxTBWord.tBamp]
  have hfun : (fun z : ℝ³ =>
      (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        ((Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) (Function.update x i z) : ℝ) : ℂ))
      = (fun _ : ℝ³ => (0 : ℂ)) := by
    funext z
    rw [hq z]
    simp
  rw [hfun]
  simp

end Work.PerSector

open Submission BoseGases

variable {N : ℕ}

/-- **The windowed amplitude of a slot piece is supported in the amplitude shift set**,
re-exported at the chapter's outer namespace `Work.PerSector` (the declaration proved above sits in
the doubly nested namespace produced by this file's header). -/
theorem tBamp_slotPiece_eq_zero_of_notMem_slotAmpSet
    {A : Set (EuclideanSpace ℝ (Fin 3))} (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hχ : ∀ z : EuclideanSpace ℝ (Fin 3), χ z ≠ 0 → z ∈ A) {volA : ℝ} (i : Fin N)
    {Φ : X N → ℝ} (S : Finset (Fin N)) (p : EuclideanSpace ℝ (Fin 3)) {x : X N}
    (hx : x ∉ slotAmpSet A S i) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ)) i x = 0 :=
  Work.PerSector.Work.PerSector.tBamp_slotPiece_eq_zero_of_notMem_slotAmpSet χ hχ i S p hx

end Work.PerSector
