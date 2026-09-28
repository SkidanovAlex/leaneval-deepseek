import Mathlib
import Submission.Work.SSS.serreE1PieceDefs

/-!
# The connecting isomorphism of the σ-descent

For `Λ ≤ ∂T_σ ≤ T_σ` the subcomplexes of the pullback `T_σ = Δ[s] ×_Y X` cut out by the horn, the
boundary and everything (see `Submission/Work/SSS/serreE1PieceDefs.lean`), the two quotient
complexes

* `C(T_σ)/C(Λ) = pieceHornC f σ` and
* `C(∂T_σ)/C(Λ) = pieceBdryHornC f σ`,  `C(T_σ)/C(∂T_σ) = pieceAlong f σ`

fit into the short exact sequence

`0 ⟶ C(∂T_σ)/C(Λ) ⟶ C(T_σ)/C(Λ) ⟶ C(T_σ)/C(∂T_σ) ⟶ 0`

of the third isomorphism theorem.  Consequently, whenever the middle term `C(T_σ)/C(Λ)` has
vanishing homology in degrees `m` and `m - 1`, the connecting map of the associated long exact
sequence is an isomorphism in degree `m`.

The only homological input is `CategoryTheory.kernelCokernelCompSequence`, the long exact sequence

`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`

associated to two composable morphisms `f`, `g` of an abelian category: with `Mono g` the kernel of
`g` vanishes, so its last three terms form a short exact sequence.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

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

/-- **The connecting isomorphism of the σ-descent.**  For a morphism of simplicial sets `f : X ⟶ Y`,
a simplex `σ : Δ[t+1] ⟶ Y` and `1 ≤ m`, if the horn quotient complex `C(T_σ)/C(Λ)`
(`Work.SSS.pieceHornC`) has vanishing homology in degrees `m` and `m-1`, then the σ-piece of `σ` in
degree `m` is the boundary-over-horn quotient `C(∂T_σ)/C(Λ)` (`Work.SSS.pieceBdryHornC`) in degree
`m-1`.  This is the connecting map of the short exact sequence
`0 ⟶ C(∂T_σ)/C(Λ) ⟶ C(T_σ)/C(Λ) ⟶ C(T_σ)/C(∂T_σ) ⟶ 0`, which is an isomorphism because the middle
term has vanishing homology in the two relevant degrees (`ShortComplex.ShortExact.δIso`). -/
theorem pieceConnectingIso {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y)
    (m : ℕ) (hm : 1 ≤ m)
    (hi : IsZero ((Work.SSS.pieceHornC f σ).homology m))
    (hj : IsZero ((Work.SSS.pieceHornC f σ).homology (m-1))) :
    Nonempty ((Work.SSS.pieceAlong f σ).homology m ≅
      (Work.SSS.pieceBdryHornC f σ).homology (m-1)) := by
  -- The three chain maps whose cokernels are the three complexes of the short exact sequence.
  let i := Work.SSS.sCCMap (SSet.Subcomplex.homOfLE (Work.SSS.pieceHorn_le_bdryAlong f σ))
  let j := Work.SSS.sCCMap (Work.SSS.bdryAlong f σ).ι
  let k := Work.SSS.sCCMap (Work.SSS.pieceHorn f σ).ι
  -- The horn sits inside the boundary inside the pullback, so `i ≫ j = k`.
  have hkey : i ≫ j = k := by
    show Work.SSS.sCCMap (SSet.Subcomplex.homOfLE (Work.SSS.pieceHorn_le_bdryAlong f σ)) ≫
      Work.SSS.sCCMap (Work.SSS.bdryAlong f σ).ι = Work.SSS.sCCMap (Work.SSS.pieceHorn f σ).ι
    rw [Work.SSS.sChainMap_comp ℤ _ _]
    rw [Subfunctor.homOfLe_ι]
  -- The inclusion of the boundary into the pullback is a monomorphism, hence so is its chain map.
  have hmono : Mono j := by
    change Mono (Work.SSS.sChainMap ℤ (Work.SSS.bdryAlong f σ).ι)
    exact Work.SSS.sChainMap_mono ℤ _ inferInstance
  haveI : Mono j := hmono
  -- The third isomorphism theorem for `i` and `j`.
  have hS : (ShortComplex.SnakeInput.L₃ (kernelCokernelCompSequence.snakeInput i j)).ShortExact :=
    cokernelComp_shortExact i j
  -- Transport the vanishing of the homology of `C(T_σ)/C(Λ) = cokernel k` across `cokernel k ≅
  -- cokernel (i ≫ j)` (an isomorphism since `i ≫ j = k`).
  have hi' : IsZero ((cokernel (i ≫ j)).homology m) :=
    IsZero.of_iso hi ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso
      (cokernelIsoOfEq hkey))
  have hj' : IsZero ((cokernel (i ≫ j)).homology (m-1)) :=
    IsZero.of_iso hj ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (m-1)).mapIso
      (cokernelIsoOfEq hkey))
  exact ⟨hS.δIso m (m-1) (ComplexShape.down_mk m (m-1) (by omega)) hi' hj'⟩

end

end Work.SSS
