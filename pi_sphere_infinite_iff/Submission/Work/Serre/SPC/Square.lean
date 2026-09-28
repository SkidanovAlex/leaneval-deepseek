import Mathlib
import Submission.Work.Serre.SPC.Setup
import Submission.Work.Serre.CWModel.Maps
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Serre.Assembly.pullbackPairMap_comp

set_option synthInstance.maxHeartbeats 400000


/-!
# The pullback square of the three comparison maps

The assembly of `Work.Serre.serrePairComparison` needs the commutativity of the square

```
                  pullbackPairMap g p γ₀ b₀ hbase
  C_*(Γ ×_B E, q⁻¹γ₀) ------------------------> C_*(E, p⁻¹b₀)
        |                                             |
 relPairMap (pullbackFst g p) γ₀              relPairMap p b₀
        v                                             v
  C_*(Γ, {γ₀}) -------------------------------> C_*(B, {b₀})
                  pairMapOf g γ₀ b₀ hbase
```

Both composites are the pair map of the *same* pair map `(Γ ×_B E, q⁻¹γ₀) → (B, {b₀})`
(`p ∘ pullbackSnd = g ∘ pullbackFst`), so the identity is formal: it is
`Work.Serre.Assembly.pullbackPairMap_comp` (proved there) together with the definitional
identification `Work.Serre.SPC.stagePairMap_eq_relPairMap` of the first-projection pair map.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

/-- Congruence of `relChainsMapOf` in its two map arguments. -/
theorem relChainsMapOf_congr {X Y : TopCat} {A : Set X} {B : Set Y}
    {f f' : X ⟶ Y} (h : f = f') {g g' : TopCat.of A ⟶ TopCat.of B} (h2 : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf X Y A B f' g' w' := by
  subst h
  subst h2
  exact congrArg (fun w => Work.Cohomology.relChainsMapOf X Y A B f g w)
    (Subsingleton.elim w w')

/-- **The commutative square of the three pair maps**, at the level of chain complexes. -/
theorem pullbackSquare_chain {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase ≫ Work.StemsB.relPairMap p b₀
      = Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀ ≫
        Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase := by
  rw [← stagePairMap_eq_relPairMap g p γ₀]
  exact Work.Serre.Assembly.pullbackPairMap_comp g p γ₀ b₀ hbase

/-- **The commutative square in homology** (immediate from `pullbackSquare_chain`). -/
theorem pullbackSquare_homology {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀)
    (i : ℕ) :
    HomologicalComplex.homologyMap (Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase) i ≫
        HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i
      = HomologicalComplex.homologyMap
          (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) i ≫
        HomologicalComplex.homologyMap (Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase) i := by
  have h := congrArg (fun m => HomologicalComplex.homologyMap m i)
    (pullbackSquare_chain g p γ₀ b₀ hbase)
  simpa only [HomologicalComplex.homologyMap_comp] using h

end

end Work.Serre.SPC
