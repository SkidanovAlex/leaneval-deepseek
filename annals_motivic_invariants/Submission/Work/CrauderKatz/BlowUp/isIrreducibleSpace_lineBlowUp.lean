import Mathlib
import Submission.Work.CrauderKatz.BlowUp.LineDefs
import Submission.Work.CrauderKatz.BlowUp.LineGlue
import Submission.Work.CrauderKatz.BlowUp.isPrime_nilradical_lineRing
import Submission.Work.CrauderKatz.BlowUp.isIrreducibleSpace_thickBlowUp
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
-- `haveI` is used deliberately: the local `IrreducibleSpace` instances are needed as
-- typeclass arguments.
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.CrauderKatz.BlowUp

noncomputable section

/-- The overlap ring `lineOvRing 𝕜 = R 𝕜[1/t]` is nontrivial: it receives a ring homomorphism
from the chart ring (with `x ↦ 1`, `t ↦ 1`, `z ↦ 0`, `ε ↦ 0`) *and* a ring homomorphism to `𝕜`
(the induced map out of the localization, well defined since `t ↦ 1` is a unit in `𝕜`).  This is
the three-dimensional mirror of `nontrivial_ovRing`. -/
private theorem nontrivial_lineOvRing (𝕜 : Type) [Field 𝕜] : Nontrivial (lineOvRing 𝕜) := by
  let f : Fin 4 → 𝕜 := fun i => if i = 0 then 1 else if i = 1 then 1 else 0
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f]
  have hf3 : f 3 = 0 := by simp [f]
  have hker : ∀ a ∈ lineI 𝕜, MvPolynomial.eval f a = 0 := by
    intro a ha
    rw [lineI, Ideal.mem_span_pair] at ha
    obtain ⟨A, B, hAB⟩ := ha
    rw [← hAB]
    simp only [map_add, map_mul, map_pow, MvPolynomial.eval_X, hf0, hf3]
    first | refl_ring1 | ring
  let psi : lineRing 𝕜 →+* 𝕜 := Ideal.Quotient.lift (lineI 𝕜) (MvPolynomial.eval f) hker
  have hpsi : psi (lineT 𝕜) = 1 := by
    show Ideal.Quotient.lift (lineI 𝕜) (MvPolynomial.eval f) hker
      (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 1)) = 1
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval_X, hf1]
  exact (IsLocalization.Away.lift (lineT 𝕜) (g := psi)
    (by rw [hpsi]; exact isUnit_one)).domain_nontrivial

/-- The overlap `lineOvS 𝕜 = Spec R 𝕜[1/t]` is nonempty. -/
private theorem nonempty_lineOvS (𝕜 : Type) [Field 𝕜] : Nonempty (lineOvS 𝕜) :=
  haveI := nontrivial_lineOvRing 𝕜
  inferInstance

/-- **The thickened blow-up of `𝔸³` along a coordinate line is irreducible.**  Its two affine
charts `Spec R 𝕜[1/t]`-glued along the overlap are irreducible (the nilradical of
`lineRing 𝕜 = 𝕜[x,t,z,ε]/(ε², x·ε)` is prime), they cover it, and their images meet in the image
of the (nonempty) overlap. -/
theorem isIrreducibleSpace_lineBlowUp (𝕜 : Type) [Field 𝕜] :
    IrreducibleSpace (lineBlowUp 𝕜) := by
  -- each chart is irreducible
  have hchart : IrreducibleSpace (lineChartS 𝕜) :=
    (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical).mpr (isPrime_nilradical_lineRing 𝕜)
  haveI hU₁ : IrreducibleSpace ↥((lineChart₁ 𝕜).opensRange) :=
    ((lineChart₁ 𝕜).isoOpensRange.hom.homeomorph.irreducibleSpace_iff).mp hchart
  haveI hU₂ : IrreducibleSpace ↥((lineChart₂ 𝕜).opensRange) :=
    ((lineChart₂ 𝕜).isoOpensRange.hom.homeomorph.irreducibleSpace_iff).mp hchart
  -- the two charts cover `lineBlowUp 𝕜`
  have hcov := opensRange_lineChart₁_sup_opensRange_lineChart₂ 𝕜
  -- and their images meet in the image of the (nonempty) overlap
  have hne : ((↑((lineChart₁ 𝕜).opensRange) : Set (lineBlowUp 𝕜)) ∩
      ↑((lineChart₂ 𝕜).opensRange)).Nonempty := by
    obtain ⟨y⟩ := nonempty_lineOvS 𝕜
    refine ⟨lineChart₁ 𝕜 (lineOvToChart₁ 𝕜 y), ?_, ?_⟩
    · exact Scheme.Hom.mem_opensRange.mpr ⟨lineOvToChart₁ 𝕜 y, rfl⟩
    · rw [lineChart₁_ovToChart₁_eq_lineChart₂_ovToChart₂ 𝕜 y]
      exact Scheme.Hom.mem_opensRange.mpr ⟨lineOvToChart₂ 𝕜 y, rfl⟩
  exact irreducibleSpace_of_open_union (U := ↑((lineChart₁ 𝕜).opensRange))
    (V := ↑((lineChart₂ 𝕜).opensRange)) ((lineChart₁ 𝕜).opensRange.isOpen)
    ((lineChart₂ 𝕜).opensRange.isOpen)
    (by rw [← TopologicalSpace.Opens.coe_sup, hcov, TopologicalSpace.Opens.coe_top]) hne

end

end Work.CrauderKatz.BlowUp
