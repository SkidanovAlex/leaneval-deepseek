import Mathlib
import Submission.Work.SSSR.serreE1PieceDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

/-- **The cokernel sequence of a composition is short exact.**  In an abelian category, for
morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` with `g` a monomorphism, the short complex
`cokernel f ⟶ cokernel (f ≫ g) ⟶ cokernel g` is short exact — the third isomorphism theorem.

Indeed it is the `L₃` row of the long exact sequence
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0` of
`kernelCokernelCompSequence`.  Its exactness is `SnakeInput.L₃_exact`; its last map is a cokernel
projection in disguise, hence an epimorphism; and its first map is a monomorphism because `Mono g`
forces `ker g = 0`, so the connecting map `δ : ker g ⟶ coker f` of the snake lemma vanishes and
`Exact.mono_g` applies to the exact sequence `ker g ⟶ coker f ⟶ coker (f ≫ g)`. -/
theorem cokernelComp_shortExact {C : Type*} [Category* C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    (ShortComplex.SnakeInput.L₃ (kernelCokernelCompSequence.snakeInput f g)).ShortExact := by
  let S := kernelCokernelCompSequence.snakeInput f g
  change S.L₃.ShortExact
  have hepi : Epi S.L₃.g := by
    have h : cokernel.π (f ≫ g) ≫ S.L₃.g = cokernel.π g := by
      show cokernel.π (f ≫ g) ≫ cokernel.map (f ≫ g) g f (𝟙 Z) (by simp) = cokernel.π g
      rw [cokernel.π_desc, Category.id_comp]
    haveI : Epi (cokernel.π (f ≫ g) ≫ S.L₃.g) := by
      rw [h]
      exact (inferInstance : Epi (cokernel.π g))
    exact epi_of_epi (cokernel.π (f ≫ g)) S.L₃.g
  have hδ : S.δ = 0 := by
    show kernelCokernelCompSequence.δ f g = 0
    rw [kernelCokernelCompSequence.δ_fac, Limits.kernel.ι_of_mono]
    simp
  have hmono : Mono S.L₃.f := by
    have h := ShortComplex.Exact.mono_g (ShortComplex.SnakeInput.L₂'_exact S) hδ
    simpa [ShortComplex.SnakeInput.L₂'] using h
  exact ShortComplex.ShortExact.mk' (ShortComplex.SnakeInput.L₃_exact S) hmono hepi

end

end Work.SSSR
