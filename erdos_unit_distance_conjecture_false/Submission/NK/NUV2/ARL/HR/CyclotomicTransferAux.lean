import Mathlib
import Submission.NK.NUV2.Final.Wiring
import Submission.NK.NUV2.RouteE.exists_compatible_fundamentalClasses
import Submission.NK.NUV2.Wild.levelSymbol_ker_adicCompletion
import Submission.NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw
import Submission.NK.LocalCFT.NormGroup.normGroup_sup_eq_inf
import Submission.NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Target

/-!
# Local class field theory at a completion, and its second axiom, unconditionally

The cohomological route to local class field theory is complete on disk:
`NK.NUV2.RouteE.exists_compatible_fundamentalClasses` (a compatible system of fundamental
classes, König's lemma) together with `NK.NUV2.Wild.levelSymbol_ker_adicCompletion` (the kernel
of the level symbol is the norm group) and the assembly
`NK.NUV2.Final.nonempty_kernelCondition_of_family` produce
`NK.LocalArtin.KernelCondition F (SeparableClosure F)` for every `p`-adic field `F` of the form
`F = Q.adicCompletion K`.

This file records that consequence (`kernelCondition_adicCompletion`), the derived canonical Artin
reciprocity datum (`artinReciprocity_adicCompletion`) and the **second axiom of the class
formation** in its intersection form, `normGroup_sup_eq_inf_adicCompletion`, with *no* further
hypotheses beyond abelian-ness of the two levels.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace NK.NUV2.ARL.HR

/-- **The local reciprocity law (kernel form) at every completion.**

Assembled from the sorry-free cohomological route on disk: a compatible family of fundamental
classes (`NK.NUV2.RouteE.exists_compatible_fundamentalClasses`) plus the per-level kernel
computation (`NK.NUV2.Wild.levelSymbol_ker_adicCompletion`) give a single Artin map
`Fˣ →* Gal(F^{ab}/F)` whose level kernels are the norm groups
(`NK.NUV2.Final.nonempty_kernelCondition_of_family`). -/
theorem kernelCondition_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) :=
  NK.NUV2.Final.nonempty_kernelCondition_of_family (K := K) Q
    (NK.NUV2.RouteE.exists_compatible_fundamentalClasses (K := K) Q)
    (fun _ _ _ _ hcomm u hu => NK.NUV2.Wild.levelSymbol_ker_adicCompletion (Q := Q) hcomm u hu)

/-- **The canonical Artin reciprocity datum at every completion**, from the local reciprocity law
in kernel form and the norm index theorem + the existence theorem. -/
theorem artinReciprocity_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nonempty (NK.LocalCFT.ArtinReciprocity (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) := by
  obtain ⟨Kc⟩ := kernelCondition_adicCompletion (K := K) Q
  obtain ⟨R⟩ := NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap Kc
    (NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q)
  exact ⟨R.toArtinReciprocity
    (NK.LocalReciprocityLubinTate.existenceTheorem_adicCompletion Q)⟩

/-- **The second axiom of the local class formation over a completion, unconditionally.**

For a finite place `Q` of a number field `K` and two finite abelian levels `L₁, L₂` of the maximal
abelian extension of `F = Q.adicCompletion K`, the norm group of the compositum is the intersection
of the two norm groups:

  `N_{L₁L₂/F}(L₁L₂)ˣ = N_{L₁/F}L₁ˣ ⊓ N_{L₂/F}L₂ˣ`.

This is Hasse's *Normensatz* in its lattice form; the previously open input
(`NK.LocalArtin.KernelCondition`) is now available (`kernelCondition_adicCompletion`), so the
statement is unconditional. -/
theorem normGroup_sup_eq_inf_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L₁ L₂ : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) L₁] [Normal (Q.adicCompletion K) L₁]
    [FiniteDimensional (Q.adicCompletion K) L₂] [Normal (Q.adicCompletion K) L₂]
    [FiniteDimensional (Q.adicCompletion K) ↥(L₁ ⊔ L₂)]
    [Normal (Q.adicCompletion K) ↥(L₁ ⊔ L₂)] :
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(L₁ ⊔ L₂)
      = NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₁
        ⊓ NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₂ := by
  obtain ⟨D⟩ := artinReciprocity_adicCompletion (K := K) Q
  exact NK.LocalCFT.NormGroup.normGroup_sup_eq_inf D L₁ L₂
    (NK.LocalCFT.Reduction.commutative_level L₁)
    (NK.LocalCFT.Reduction.commutative_level L₂)
    (NK.LocalCFT.Reduction.commutative_level (L₁ ⊔ L₂))

end NK.NUV2.ARL.HR
