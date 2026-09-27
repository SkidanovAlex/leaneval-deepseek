import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.HasPlaquePartition` — the geometric input of the equality case of Pisa 7.6(ii)

The equality case of Pisa 7.6(ii),

`ent μ (aDiag t ·) ≤ ofReal (∫ growthFun (Uminus t) ν t)`,

proved in `Work.EKLC6Core.ent_le_growth_of_aerg`, needs a *generating partition* subordinate to
the contracted horospherical subgroup `U = Uminus t` (Pisa Prop. 7.43, together with the
plaque-algebra construction of Pisa 7.37/7.38).

This file fixes the form of that geometric input in the vocabulary of this development.  It is
free of `sorry` and of any entropy: it is the interface between the geometry
(`Work.EKLC6Core.hasPlaquePartition`) and the entropy assembly in
`Work.EKLC6Core.ent_le_growth_of_aerg`.

The data are a finite partition `P` of `X₃`, a σ-algebra `M`, and a `μ`-conull set `Z` with

* `A := ⨆ n, comap ((aDiag t ·)^[n]) M` a plaque algebra for `Uminus t` on `Z`,
* `partSigma P ≤ M ≤ A` (so that `A` is also the past σ-algebra of `P`), and
* `P` computes the entropy: `ent μ (aDiag t ·) ≤ ofReal (hPart μ (aDiag t ·) P)`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The geometric input of Pisa 7.37–7.43, in the form consumed by the entropy assembly.** -/
def HasPlaquePartition (μ : MeasureTheory.Measure X3) (t : Fin 3 → ℝ) : Prop :=
  ∃ (M : MeasurableSpace X3) (Z : Set X3)
      (P : @Work.EKLContract.FinPart X3 Work.EKLContract.instMeasurableSpaceX3),
    IsPlaqueAlgebra (Uminus t) Z
      (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) M) ∧
    μ Zᶜ = 0 ∧
    @Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P ≤ M ∧
    M ≤ (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
        (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P)) ∧
    @Work.EKLContract.ent X3 Work.EKLContract.instMeasurableSpaceX3 μ
        (fun x : X3 => aDiag t • x)
      ≤ ENNReal.ofReal
          (@Work.EKLContract.hPart X3 Work.EKLContract.instMeasurableSpaceX3 μ
            (fun x : X3 => aDiag t • x) P)

/-- Monotonicity of the past σ-algebra in the σ-algebra. -/
theorem comap_past_le_of_le (t : Fin 3 → ℝ) {M N : MeasurableSpace X3} (h : M ≤ N) :
    (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) M)
      ≤ (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) N) :=
  iSup_le fun n => le_trans (MeasurableSpace.comap_mono h)
    (le_iSup (fun m : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m]) N) n)

/-- If `M` is contained in the past σ-algebra of `P`, then so is the past σ-algebra of `M`. -/
theorem past_le_of_le_past (t : Fin 3 → ℝ) {M : MeasurableSpace X3}
    {P : @Work.EKLContract.FinPart X3 Work.EKLContract.instMeasurableSpaceX3}
    (h : M ≤ (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
        (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P))) :
    (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) M)
      ≤ (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P)) := by
  refine iSup_le fun n => ?_
  refine le_trans (MeasurableSpace.comap_mono h) ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun m => ?_
  have hcomp : ((fun x : X3 => aDiag t • x)^[m]) ∘ ((fun x : X3 => aDiag t • x)^[n])
      = ((fun x : X3 => aDiag t • x)^[m + n]) :=
    (Function.iterate_add (fun x : X3 => aDiag t • x) m n).symm
  rw [MeasurableSpace.comap_comp, hcomp]
  exact le_iSup (fun k : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[k])
    (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P)) (m + n)

/-- The past σ-algebra `⨆ n, comap ((aDiag t ·)^[n]) M` is `aDiag t ·`-decreasing. -/
theorem comap_past_le (t : Fin 3 → ℝ) (M : MeasurableSpace X3) :
    MeasurableSpace.comap (fun x : X3 => aDiag t • x)
        (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) M)
      ≤ (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) M) := by
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun n => ?_
  have hcomp : ((fun x : X3 => aDiag t • x)^[n]) ∘ (fun x : X3 => aDiag t • x)
      = ((fun x : X3 => aDiag t • x)^[n + 1]) :=
    (Function.iterate_succ (fun x : X3 => aDiag t • x) n).symm
  rw [MeasurableSpace.comap_comp, hcomp]
  exact le_iSup (fun m : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m]) M) (n + 1)

/-- `comap` of the past σ-algebra of `P` is the shifted past σ-algebra of `P`. -/
theorem comap_pastFinPart_eq (t : Fin 3 → ℝ)
    (P : @Work.EKLContract.FinPart X3 Work.EKLContract.instMeasurableSpaceX3) :
    MeasurableSpace.comap (fun x : X3 => aDiag t • x)
        (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P))
      = (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n + 1])
          (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P)) := by
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun n => ?_
  have hcomp : ((fun x : X3 => aDiag t • x)^[n + 1])
      = ((fun x : X3 => aDiag t • x)^[n]) ∘ (fun x : X3 => aDiag t • x) :=
    Function.iterate_succ (fun x : X3 => aDiag t • x) n
  rw [MeasurableSpace.comap_comp, hcomp]

/-- The past σ-algebra of a finite partition is `aDiag t ·`-decreasing. -/
theorem comap_pastFinPart_le (t : Fin 3 → ℝ)
    (P : @Work.EKLContract.FinPart X3 Work.EKLContract.instMeasurableSpaceX3) :
    MeasurableSpace.comap (fun x : X3 => aDiag t • x)
        (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P))
      ≤ (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P)) :=
  comap_past_le t _

/-- The σ-algebra of the partition is contained in its past σ-algebra. -/
theorem partSigma_le_pastFinPart (t : Fin 3 → ℝ)
    (P : @Work.EKLContract.FinPart X3 Work.EKLContract.instMeasurableSpaceX3) :
    (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P)
      ≤ (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P)) := by
  have h := le_iSup (fun n : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
    (@Work.EKLContract.partSigma X3 Work.EKLContract.instMeasurableSpaceX3 P)) 0
  rw [Function.iterate_zero, MeasurableSpace.comap_id] at h
  exact h

end Work.EKLC6Core

end
