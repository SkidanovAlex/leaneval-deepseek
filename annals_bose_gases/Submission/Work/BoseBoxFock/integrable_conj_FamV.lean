import Mathlib
import Submission.Work.BoseBoxFock.ModeFam
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integrable_conj_FamV` — the pairings of the physical mode family are
integrable

Every vector of the physical family `FamV v μ HM` is one of the corpus box modes
`Q(e^{ikx}χ_Λ)` (`qVec`, on the left summand of the index) or `e^{isx}θ_Λ` (`thetaExp`, on the
right summand), at the box side `ℓ = ellH v μ > 0` and the lattice momentum `kmomLab ℓ N ·`
(`FamV` unfolds by `rfl`).  These are `L²` by `memLp_modes` — they are supported in the
compact box `Λ(ℓ)` and bounded there.

Consequently, for any two indices `i j` the pointwise product
`x ↦ conj (FamV i x) * FamV j x` is `L¹`: it is the product of two `L²` functions
(`MemLp.mul'`, Hölder with the conjugate exponents `2, 2` giving exponent `1`), the first
factor being `L²` because `star` preserves the norm.  In particular the integral in the
Gram entry `∫ x, conj (FamV i x) * FamV j x` is absolutely convergent, which is the
hypothesis the Gram comparison `gramFamV` needs.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- Every member of the physical mode family is `L²` on `ℝ³` (it is a `qVec` or a `thetaExp`
at side `ellH v μ > 0`, both `L²` by `memLp_modes`). -/
theorem memLp_FamV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i : Lab HM.N ⊕ Lab HM.N) :
    MemLp (FamV v μ HM i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨hq, ht, _⟩ := memLp_modes (ellH v μ) (ellH_pos v μ)
  rcases i with k | s
  · exact hq (kmomLab (ellH v μ) HM.N k)
  · exact ht (kmomLab (ellH v μ) HM.N s)

/-- The pointwise product `conj (FamV i) * FamV j` of two members of the physical mode family
is integrable on `ℝ³`: a product of two `L²` functions is `L¹`. -/
theorem integrable_conj_FamV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (HM : HonestModes v μ) (i j : Lab HM.N ⊕ Lab HM.N) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        (starRingEnd ℂ) (FamV v μ HM i x) * FamV v μ HM j x)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
  memLp_one_iff_integrable.mp ((memLp_FamV v μ HM i).star.mul' (memLp_FamV v μ HM j))

end Work.BoseBoxFock
