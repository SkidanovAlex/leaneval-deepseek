import Mathlib
import Submission.Work.SSGRoute.PT.coherent_pTorsion_chi
import Submission.Work.SSGRoute.PT.g1plus_levelInfl
import Submission.Work.SSGRoute.PT.pt_coherent_pTorsion_invariant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # `S1` in the `IntermediateField k Ω` vocabulary, transported from the proved `K Ω` form

`Work.SSGRoute.PT.coherent_pTorsion_chi` (`PT/coherent_pTorsion_chi.lean`, **proved**) is the
coherent `p`-torsion invariant of the class-formation `H²` at levels `L : IntermediateField K Ω`.
The `G1⁺` assembly (`PT/g1plus_finHalf.lean`) chooses its levels through
`PT.exists_level_factors_locConstOnTwo`, i.e. as `L : IntermediateField k Ω` containing `K`; the
corresponding statement there is `PT.coherent_pTorsion_chi_k`
(`PT/coherent_pTorsion_chi_k.lean`, still a `sorry`).

This file supplies that statement, *proved*, by the round trip through `IntermediateField K Ω`:
a level `L : IntermediateField k Ω` with `K ≤ L` is the same subset of `Ω` as the level
`kLevelUp K L hKL : IntermediateField K Ω`, and `↥(kLevelUp K L hKL) = ↥L` definitionally, so the
proved `χ` applies and the two levels' inflation maps `PT.inflLevel` / `PTDefsOmega.inflCIn` are the
same term.

Consequence: the `S1` ingredient of the `G1⁺` assembly is available with no `sorry`, in either
vocabulary; `PT.coherent_pTorsion_chi_k` and `PT.pt_coherent_pTorsion_invariant` can be re-pointed
to `coherent_pTorsion_chi_k_of_KΩ` / `coherent_pTorsion_chi` in one line each. -/

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.SSGRoute.PT

open SSGRoute.PTExt CategoryTheory

noncomputable section

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **A level of `Ω/k` containing `K`, viewed as a level of `Ω/K`.**  The carrier is the same
subset of `Ω`; the `K`-algebra structure is the one induced by `K ≤ L`. -/
def kLevelUp (K L : IntermediateField k Ω) (hKL : K ≤ L) : IntermediateField K Ω where
  carrier := (L : Set Ω)
  mul_mem' hx hy := mul_mem hx hy
  one_mem' := one_mem L
  add_mem' hx hy := add_mem hx hy
  zero_mem' := zero_mem L
  algebraMap_mem' r := by
    show (r : Ω) ∈ (L : Set Ω)
    exact hKL r.2
  inv_mem' x hx := inv_mem hx

@[simp] theorem mem_kLevelUp (K L : IntermediateField k Ω) (hKL : K ≤ L) (x : Ω) :
    x ∈ kLevelUp K L hKL ↔ x ∈ L := Iff.rfl

/-- **`S1` at levels of `Ω/k`.**  Statement of `PT.coherent_pTorsion_chi_k`, proved from the
`IntermediateField K Ω` form `PT.coherent_pTorsion_chi`. -/
theorem coherent_pTorsion_chi_k_of_KΩ (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] :
    ∃ χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 → ZMod p,
      (∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
          p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v) ∧
      (∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
          p • u = 0 → χ L hKL u = 0 → u = 0) ∧
      (∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
          [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
          (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
          p • u = 0 →
          χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  obtain ⟨χ, h1, h2, h3⟩ := coherent_pTorsion_chi p k K Ω
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L hNF hFD hGal hKL
    letI : NumberField (kLevelUp K L hKL) := hNF
    letI : FiniteDimensional k (kLevelUp K L hKL) := hFD
    letI : IsGalois k (kLevelUp K L hKL) := hGal
    exact χ (kLevelUp K L hKL)
  · intro L hNF hFD hGal hKL u v hu hv
    letI : NumberField (kLevelUp K L hKL) := hNF
    letI : FiniteDimensional k (kLevelUp K L hKL) := hFD
    letI : IsGalois k (kLevelUp K L hKL) := hGal
    exact h1 (kLevelUp K L hKL) u v hu hv
  · intro L hNF hFD hGal hKL u hu h0
    letI : NumberField (kLevelUp K L hKL) := hNF
    letI : FiniteDimensional k (kLevelUp K L hKL) := hFD
    letI : IsGalois k (kLevelUp K L hKL) := hGal
    exact h2 (kLevelUp K L hKL) u hu h0
  · intro L hNF hFD hGal hKL L' hNF' hFD' hGal' hKL' hLL u hu
    letI : NumberField (kLevelUp K L hKL) := hNF
    letI : FiniteDimensional k (kLevelUp K L hKL) := hFD
    letI : IsGalois k (kLevelUp K L hKL) := hGal
    letI : NumberField (kLevelUp K L' hKL') := hNF'
    letI : FiniteDimensional k (kLevelUp K L' hKL') := hFD'
    letI : IsGalois k (kLevelUp K L' hKL') := hGal'
    exact h3 (kLevelUp K L hKL) (kLevelUp K L' hKL')
      (fun x hx => hLL hx) u hu

end

end Work.SSGRoute.PT
