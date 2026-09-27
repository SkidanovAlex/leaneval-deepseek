import Mathlib
import Submission.Work.EKLRelCross.covariant_shape
import Submission.Work.EKLRelCross.LeafBasic

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-- **Powers of `aDiag t0` preserve `μ`.**  If `x ↦ aDiag t0 • x` preserves `μ`, then so does
`x ↦ aDiag (n • t0) • x` for every `n : ℕ`: the latter is the `n`-fold iterate of the former,
because `t ↦ aDiag t` is a homomorphism (`aDiag_nsmul`). -/
theorem measurePreserving_aDiag_nsmul {μ : Measure X3} {t0 : Fin 3 → ℝ}
    (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ) (n : ℕ) :
    MeasurePreserving (fun x : X3 => aDiag (n • t0) • x) μ μ := by
  have hfun : (fun x : X3 => aDiag (n • t0) • x)
      = (fun x : X3 => aDiag t0 • x)^[n] := by
    rw [smul_iterate, aDiag_nsmul]
  rw [hfun]
  exact ht0.iterate n

theorem ae_covariant_shape_all
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    {ι : Type} [Countable ι] {Z : ι → Set Work.EKLContract.X3}
    {m : ι → MeasurableSpace Work.EKLContract.X3}
    (hZ : ∀ i, Work.EKLContract.IsPlaqueAlgebra U (Z i) (m i))
    (hZpos : ∀ i, μ (Z i) ≠ 0) :
    ∀ᵐ x ∂μ, ∀ p : ℕ × ι,
      x ∈ X' →
      Work.EKLContract.aDiag (p.1 • t0) • x ∈ X' →
      Work.EKLContract.aDiag (p.1 • t0) • x ∈ Z p.2 →
      (∀ u ∈ U, u • (Work.EKLContract.aDiag (p.1 • t0) • x) =
          Work.EKLContract.aDiag (p.1 • t0) • x → u = 1) →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ∀ C : Set Work.EKLContract.SL3, MeasurableSet C →
          C ⊆ Work.EKLContract.shape (m p.2) U (Work.EKLContract.aDiag (p.1 • t0) • x) →
          ν (Work.EKLContract.aDiag (p.1 • t0) • x) C =
            c * (ν x).map (fun g => Work.EKLContract.aDiag (p.1 • t0) * g *
              (Work.EKLContract.aDiag (p.1 • t0))⁻¹) C := by
  classical
  have htpow : ∀ n : ℕ, MeasurePreserving (fun x : X3 => aDiag (n • t0) • x) μ μ :=
    fun n => measurePreserving_aDiag_nsmul ht0 n
  -- The single-plaque covariance at `t = n • t0`, for every `n` and every index `i`.
  have hcov : ∀ (n : ℕ) (i : ι), ∀ᵐ x ∂μ,
      x ∈ X' → aDiag (n • t0) • x ∈ X' → aDiag (n • t0) • x ∈ Z i →
      (∀ u ∈ U, u • (aDiag (n • t0) • x) = aDiag (n • t0) • x → u = 1) →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ∀ C : Set SL3, MeasurableSet C →
          C ⊆ shape (m i) U (aDiag (n • t0) • x) →
          ν (aDiag (n • t0) • x) C =
            c * (ν x).map (fun g => aDiag (n • t0) * g * (aDiag (n • t0))⁻¹) C :=
    fun n i => covariant_shape hU hL (n • t0) (htpow n) (hZ i) (hZpos i)
  -- Countably many indices, hence every `p : ℕ × ι` simultaneously on a conull set.
  rw [MeasureTheory.ae_all_iff]
  rintro ⟨n, i⟩
  filter_upwards [hcov n i] with x hx
  intro hxX hTxX hTxZ hstab
  exact hx hxX hTxX hTxZ hstab

end

end Work.EKLRelCross
