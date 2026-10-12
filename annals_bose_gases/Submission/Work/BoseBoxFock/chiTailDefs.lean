import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.PotGroupDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiTailDefs` — the lattice-truncation tails of the FS `Q₁` row

The two `χ`-rows of FS's `Q₁` (the `Q₁` of `prop:Hamilton2ndQuant`, realised on the box as the
`potChiLin` rows of `Work.BoseBoxFock.PotGroupDefs`) carry the **truncated** lattice sums

    ∑_{k : Lab N} (hatChi k) • qVec(ℓ, kmomLab ℓ N k)          (the χ-row),
    ∑_{s ≠ 0, s : Lab N} (hatChiSq s) • thetaExp(ℓ, kmomLab ℓ N s)   (the χ²-row),

against the weights `hatChi k = corpusBox.hatChi (ℓ • kmomLab ℓ N k)` (`= ℓ⁻³χ̂_Λ(kmom)`) and
`hatChiSq k = corpusBox.hatChiSq (ℓ • kmomLab ℓ N k)`.  The *continuum* (whole-dual-lattice)
sums are the classical Poisson/Parseval identities for the unit-cell function `χ`

    ∑_{m ∈ ℤ³} ĉ_m e^{i⟨2π m, ·/ℓ⟩} = χ_Λ ,     ∑_{m ∈ ℤ³} ĉ_m² = ∫χ² = 1     (ĉ_m = χ̂(2πm)) ,

which give the *ideal* position-space modes

    ∑_{k} (hatChi k) qVec(ℓ, k) = χ_Λ² − θ ,     ∑_{s} (hatChiSq s) thetaExp(ℓ, s) = χ_Λ² .

`chiTail` and `thetaTail` below are the **truncation errors**, i.e. the difference between the
ideal mode and the truncated lattice sum, as a function of the *position* `x`; their sup-norm is
`O(N^{-K})` for every `K` (the Fourier coefficients of the `C^∞` compactly supported `χ` decay
faster than any polynomial), uniformly in `ℓ`.  These are the quantities that the `∃ Nmin` of
`Work.BoseBoxFock.PotChiLin_exists` exploits: `Nmin μ` is taken so large that the tails are far
below every polynomial slot of `errKafz`.

Statement of the bound: `Submission/Work/BoseBoxFock/chiTail_lattice.lean`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- **The χ-row truncation tail**: the difference between the ideal position-space mode
`χ_Λ² − θ` of the FS `Q₁` χ-row and the *truncated* lattice sum
`∑_{k : Lab N} hatChi(k) • qVec(ℓ, kmomLab ℓ N k)`. -/
noncomputable def chiTail (ℓ : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) ^ 2 - Work.BoseK15.corpusBox.thetaFun ℓ x)
    - ∑ k : Lab N,
        ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomLab ℓ N k) : ℝ) : ℂ) *
          Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k) x

/-- **The χ²-row truncation tail**: the difference between the ideal position-space mode
`χ_Λ² − θ` of the FS `Q₁` χ²-row (the `ω`-row of `potChiLin`) and the *truncated* lattice sum
`∑_{s ≠ 0} hatChiSq(s) • thetaExp(ℓ, kmomLab ℓ N s)`. -/
noncomputable def thetaTail (ℓ : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) ^ 2 - Work.BoseK15.corpusBox.thetaFun ℓ x)
    - ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
        ((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ) *
          Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) x

/-! ## The summed form of the FS `Q₁` χ-row -/

variable {m : ℕ} [NeZero m]

/-- **The summed form of the FS `Q₁` χ-row**: `potChiLin` with the two mode sums collapsed into
the single superposed modes `c = ∑_k hatChi_k • f k` (the χ-row) and
`c' = ∑_{s ≠ 0} hatChiSq_s • g s` (the χ²-row).  The identity
`potChiLin B f g E = potChiLinSummed B (∑_k hatChi_k • f k) (∑_{s≠0} hatChiSq_s • g s) E`
holds whenever `B` is additive and `ℝ`-homogeneous in its one-body argument (in particular for
`B = fun T => boxSlotSum e T`); it is the step that turns the *two* lattice sums of FS
`lem:2ndQuand`'s `Q₁` into a single superposed mode, whose pinning is `etaOf_summed_chi`. -/
noncomputable def potChiLinSummed {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ι : Type*}
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → EuclideanSpace ℝ (Fin 3)) → ℂ) →
      ((ι → EuclideanSpace ℝ (Fin 3)) → ℂ))
    (c c' : Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    ((ι → EuclideanSpace ℝ (Fin 3)) → ℂ) → ((ι → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
  (E.ell ^ (-(3 : ℝ)) * E.W1 0) •
      ((B (rankOne (evec0 m))) ∘ (B (rankOnePair c (evec0 m))))
    - (E.mu * E.W1 0) • (B (rankOnePair c (evec0 m)))
    + (E.ell ^ (-(3 : ℝ)) * E.W1 0) •
        ((B (rankOnePair (evec0 m) c)) ∘ (B (rankOne (evec0 m))))
    - (E.mu * E.W1 0) • (B (rankOnePair (evec0 m) c))
    + (E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
        ((B (rankOne (evec0 m))) ∘ (B (rankOnePair c' (evec0 m))))
    + (E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
        ((B (rankOnePair (evec0 m) c')) ∘ (B (rankOne (evec0 m))))

end Work.BoseBoxFock
