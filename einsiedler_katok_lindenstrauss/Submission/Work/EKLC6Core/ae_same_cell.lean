import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.ae_ball_in_atom
import Submission.Work.EKLC6Core.ae_not_crosses

/-!
# `Work.EKLC6Core.ae_same_cell` — the "same cell" tracking lemma (Pisa 7.31/7.32)

For an `A`-invariant probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a finite family `P : Fin N → Set X₃`
of open pairwise disjoint sets covering a `μ`-conull set, whose boundary is `μ`-thin
(`μ (Nbd P η) ≤ c η`), and a subgroup `U ≤ SL₃(ℝ)` contracted by `aDiag t` at the geometric rate
`e^{-α n}`, we prove that for `μ`-a.e. `x` there is `δ > 0` such that for every `n : ℕ` and every
`u ∈ U` with `u ∈ V δ`, the two orbit points `aDiag t ^ n • x` and `aDiag t ^ n • (u • x)` lie in
the *same* cell `P i` of the partition.

## Structure of the proof

* `not_crosses_imp`: if `y` is not crossed at scale `τ` (`ae_ball_in_atom`'s relation
  `Crosses P τ y`) and `y ∈ P i`, then no `v ∈ V τ` moves `y` out of `P i`.
* `ae_not_crosses` (`Submission/Work/EKLC6Core/ae_not_crosses`): for `μ`-a.e. `x` there is `δ > 0`
  such that `aDiag t ^ n • x` is uncrossed at the geometric scale `δ * exp (-(α n))` for every
  `n`.  This is the Borel–Cantelli tracking argument of `ae_ball_in_atom` extracted from its
  proof.
* the closure of the partition (`hPcov`) and invariance (`hmp`) give, for `μ`-a.e. `x`, that
  `aDiag t ^ n • x` lies in some cell for every `n`.
* since `aDiag t ^ n • (u • x) = (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • (aDiag t ^ n • x)` and the
  conjugated element lies in `V (δ * exp (-(α n)))` by the contraction hypothesis `hexp`, the
  two orbit points lie in the same cell.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The negation of the crossing relation: an uncrossed point at scale `τ` is not moved out of its
cell by any perturbation in `V τ`. -/
theorem not_crosses_imp {N : ℕ} {P : Fin N → Set X3} {τ : ℝ} {y : X3}
    (h : ¬ Crosses P τ y) {i : Fin N} (hy : y ∈ P i) {v : SL3} (hv : v ∈ V τ) : v • y ∈ P i := by
  by_contra hcon
  exact h ⟨i, v, hv, Or.inl ⟨hy, hcon⟩⟩

/-- The orbit of a conull set is conull: if the cells cover `μ`-a.e. point, then for `μ`-a.e. `x`
every point `aDiag t ^ n • x` of the forward orbit lies in some cell. -/
theorem ae_orbit_mem_iUnion {t : Fin 3 → ℝ}
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {N : ℕ} (P : Fin N → Set X3) (hPcov : μ ((⋃ i, P i))ᶜ = 0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, aDiag t ^ n • x ∈ ⋃ i, P i := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : X3 | ¬ ∀ n : ℕ, aDiag t ^ n • x ∈ ⋃ i, P i}
      = ⋃ n : ℕ, (fun x : X3 => aDiag t ^ n • x) ⁻¹' (⋃ i, P i)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_compl_iff,
      not_forall]
  rw [hset]
  refine measure_iUnion_null fun n => ?_
  have hfun : (fun x : X3 => aDiag t ^ n • x) = (fun x : X3 => aDiag t • x)^[n] := by
    funext y; rw [iterate_smul_eq]
  rw [hfun]
  exact (hmp.iterate n).preimage_null hPcov

theorem ae_same_cell {U : Subgroup Work.EKLContract.SL3} {t : Fin 3 → ℝ}
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hexp : ∃ (α : ℝ), 0 < α ∧ ∀ (ε : ℝ), 0 < ε → ∀ (n : ℕ) (u : Work.EKLContract.SL3),
      u ∈ U → u ∈ Work.EKLContract.V ε →
      Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹
        ∈ Work.EKLContract.V (ε * Real.exp (-(α * ↑n))))
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {N : ℕ} (P : Fin N → Set Work.EKLContract.X3) (c : ℝ) (hc : 0 < c)
    (hPopen : ∀ i, IsOpen (P i))
    (hPdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hPcov : μ ((⋃ i, P i))ᶜ = 0)
    (hPthin : ∀ η : ℝ, 0 < η →
      μ (⋃ i, (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
          ((Work.EKLContract.V η) ×ˢ (frontier (P i)))) ≤ ENNReal.ofReal (c * η)) :
    ∀ᵐ x ∂μ, ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (u : Work.EKLContract.SL3),
      u ∈ U → u ∈ Work.EKLContract.V δ →
      ∃ i, Work.EKLContract.aDiag t ^ n • x ∈ P i ∧
        Work.EKLContract.aDiag t ^ n • (u • x) ∈ P i := by
  obtain ⟨α, hα, hexp⟩ := hexp
  filter_upwards [ae_not_crosses (t := t) (α := α) hα hmp P c hc (by simpa only [Nbd] using hPthin),
    ae_orbit_mem_iUnion (t := t) hmp P hPcov] with x hncx hcovx
  obtain ⟨δ, hδpos, hδ⟩ := hncx
  refine ⟨δ, hδpos, ?_⟩
  intro n u huU huV
  have hconj : aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ V (δ * Real.exp (-(α * ↑n))) :=
    hexp δ hδpos n u huU huV
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcovx n)
  refine ⟨i, hi, ?_⟩
  have hkey : (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • (aDiag t ^ n • x)
      = aDiag t ^ n • (u • x) := by
    rw [← iterate_smul_eq t n x, ← iterate_smul_eq t n (u • x)]
    exact (orbit_smul_eq t n u x).symm
  rw [← hkey]
  exact not_crosses_imp (hδ n) hi hconj

end Work.EKLC6Core
