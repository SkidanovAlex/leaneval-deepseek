import Submission.Work.EKLC6Core.Basic

/-!
# `EKLC6Core.Sigma` — σ-algebra bookkeeping for the entropy contribution

The finite-partition form of the entropy inequality of Pisa 7.40 (used in `PLAN.md` as L3)
compares `Hcond μ P (comap T A)` with `Hcond μ P (⋁_n comap (T^[n+1]) (partSigma P))`, so it
needs the elementary fact that a `T`-decreasing σ-algebra whose finite sub-partition `P` sits
inside it contains the whole past `⋁_{n≥1} T^{-n}(partSigma P)`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The past of a `T`-decreasing σ-algebra is contained in `comap T A`. -/
theorem comap_iterate_le {X : Type*} (T : X → X) (A : MeasurableSpace X)
    (hdec : MeasurableSpace.comap T A ≤ A) (n : ℕ) :
    MeasurableSpace.comap (T^[n]) A ≤ A := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcomp : (T^[n+1]) = T^[n] ∘ T := Function.iterate_succ T n
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact le_trans (MeasurableSpace.comap_mono ih) hdec

/-- If `partSigma P ≤ A` and `A` is `T`-decreasing then the whole past of `P` is contained in
`comap T A`. -/
theorem past_le_comap {X : Type*} [mX : MeasurableSpace X] (T : X → X) (A : MeasurableSpace X)
    (hdec : MeasurableSpace.comap T A ≤ A) (P : @FinPart X mX)
    (hP : @partSigma X mX P ≤ A) :
    (⨆ n : ℕ, MeasurableSpace.comap (T^[n+1]) (@partSigma X mX P)) ≤
      MeasurableSpace.comap T A := by
  refine iSup_le fun n => ?_
  have h1 : MeasurableSpace.comap (T^[n+1]) (@partSigma X mX P) ≤
      MeasurableSpace.comap (T^[n+1]) A := MeasurableSpace.comap_mono hP
  have h2 : MeasurableSpace.comap (T^[n+1]) A =
      MeasurableSpace.comap T (MeasurableSpace.comap (T^[n]) A) := by
    rw [Function.iterate_succ, MeasurableSpace.comap_comp]
  have h3 : MeasurableSpace.comap (T^[n]) A ≤ A := comap_iterate_le T A hdec n
  calc MeasurableSpace.comap (T^[n+1]) (@partSigma X mX P)
      ≤ MeasurableSpace.comap (T^[n+1]) A := h1
    _ = MeasurableSpace.comap T (MeasurableSpace.comap (T^[n]) A) := h2
    _ ≤ MeasurableSpace.comap T A := MeasurableSpace.comap_mono h3

end Work.EKLC6Core

end
