import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassAux
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsJetMajMass
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsTriglJetBounds
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsA2JetBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

/-
Intended namespace: `Work.FTS.StrongPersist.L3Rhs`.
The `α`-uniform mass bound (`0 < α ≤ 1`) for the angular majorant `VfsAngMaj α` of the two
angular factors `VfsA1 α` and `VfsA2 α` of the separated part `Vfs α` of `Bf α f`
(see `FTS/StrongPersist/L3Rhs/N0gAuxDefs`), namely
`angMaj α C θ = (C θ)^2 sin(2θ)^{-η} + Σ_{1 ≤ i ≤ 3} (dthU^[i] C θ)^2 sin(2θ)^{-γ(α)}`.
Route: `Work.FTS.StrongPersist.L3Aux.GamJetBounds` supplies the `η`-mass of `Γ/c` and the
`γ`-masses of its `dthU`-jets (`dthU φ = sin 2θ · φ'`), all bounded by `10^15`; Leibniz for
`dthU` (`dthU` is the derivation `sin 2θ · d/dθ`) plus explicit uniform bounds on the
`dthU`-jets of `sin 2θ` and of `c₂ = cos 2θ - sin²θ` (orders ≤ 3, e.g. ≤ 100) transfer these
to `VfsA1 = (3/2) sin 2θ · dthU(Γ/c)` and `VfsA2 = -α c₂ · Γ/c`.
-/
theorem VfsAngMass : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1,
    MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.L3Rhs.VfsAngMaj α) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Rhs.VfsAngMaj α θ) ≤ K :=
  VfsAngMass_of_pieces
    (fun α hα hα1 => VfsJetMajMass α hα hα1)
    (by
      obtain ⟨B, hB, _hS, h2⟩ := VfsTriglJetBounds
      exact ⟨B, hB, h2⟩)
    VfsA2JetBound

end Work.FTS.StrongPersist.L3Rhs
