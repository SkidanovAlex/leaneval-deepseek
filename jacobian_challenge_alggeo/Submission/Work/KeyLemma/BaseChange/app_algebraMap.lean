import Mathlib
import Submission.Work.CurveBasics.BaseChange.range_germ_baseChange

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# The projection `C_L ⟶ C` is a morphism of `k`-algebras on sections

For a curve `C` over `k`, a field extension `L/k` and an open `W ⊆ C`, the ring of
sections `Γ(C, W)` is a `k`-algebra (via the structure morphism `C ⟶ Spec k`, see
`Work.CurveBasics.Curve.instAlgebraSections`) and the ring of sections of the base
change `Γ(C_L, W_L)` over the preimage `W_L = fst ⁻¹ᵁ W` is an `L`-algebra.  The main
result of this file, `app_algebraMap`, says that these two structures are compatible
along the pullback map `fst.app W : Γ(C, W) ⟶ Γ(C_L, W_L)`: the `k`-algebra structure
of `Γ(C_L, W_L)` obtained by restriction of scalars along `k → L` is the one induced
from `Γ(C, W)`.

The proof is a computation with the composites of sheaf maps coming from the pullback
square

```
C_L --p₂--> Spec L
 |             |
 p₁            g
 v             v
 C --f------> Spec k
```

which defines `C_L`.  Concretely, both sides of the claimed identity are the map `k → Γ(C_L, W_L)`
induced on global sections by the composite `C_L ⟶ Spec k`; the two paths are related by

* `Scheme.Hom.appLE_comp_appLE`, which combines `f.appLE ⊤ W` with `p₁.app W`,
* `Scheme.Hom.comp_appLE`, which splits `(p₂ ≫ g).appLE` into `g.app ⊤` and `p₂.appLE`,
* `Scheme.ΓSpecIso_inv_naturality`, which says that `g : Spec L ⟶ Spec k` corresponds to
  `algebraMap k L` on global sections, and
* `pullback.condition`, which identifies the two composite morphisms `C_L ⟶ Spec k`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

namespace Work.KeyLemma.BaseChange

universe u

/-- The section-level map induced by the projection `C_L ⟶ C` commutes with the structure
constants: it sends the image of `c : k` in `Γ(C, W)` to the image of `c` in `Γ(C_L, W_L)`,
where the latter is computed via `k → L`. -/
theorem app_algebraMap {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (L : Type u)
    [Field L] [Algebra k L] (W : C.left.Opens) (c : k) :
    (C.baseChangeFst L).app W (algebraMap k (C.left.presheaf.obj (Opposite.op W)) c) =
      algebraMap L (((C.baseChange L).left).presheaf.obj (Opposite.op (C.bcOpens L W)))
        (algebraMap k L c) := by
  -- First combine `f.appLE ⊤ W` with `p₁.app W` into a single `appLE` of the composite
  -- `p₁ ≫ f : C_L ⟶ Spec k`, using `app_eq_appLE` for the second factor.
  have hLsub : C.hom.appLE ⊤ W (by rw [Scheme.Hom.preimage_top]; exact le_top) ≫
        (C.baseChangeFst L).app W
      = ((C.baseChangeFst L) ≫ C.hom).appLE ⊤ (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top) := by
    rw [Scheme.Hom.app_eq_appLE]
    rw [Scheme.Hom.appLE_comp_appLE]
    rfl
  -- The two paths `p₁ ≫ f` and `p₂ ≫ g` from `C_L` to `Spec k` agree.
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        C.hom.appLE ⊤ W (by rw [Scheme.Hom.preimage_top]; exact le_top) ≫
          (C.baseChangeFst L).app W
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        ((C.baseChangeFst L) ≫ C.hom).appLE ⊤ (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top) := by
    rw [hLsub]
    rfl
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        ((C.baseChangeFst L) ≫ C.hom).appLE ⊤ (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top)
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        ((C.baseChange L).hom ≫ Work.CurveBasics.Curve.specMap k L).appLE ⊤ (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top) := by
    rw [show (C.baseChangeFst L) ≫ C.hom =
        (C.baseChange L).hom ≫ Work.CurveBasics.Curve.specMap k L from pullback.condition]
    rfl
  -- Split the `appLE` of `p₂ ≫ g` along the other path.
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        ((C.baseChange L).hom ≫ Work.CurveBasics.Curve.specMap k L).appLE ⊤ (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top)
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        ((Work.CurveBasics.Curve.specMap k L).app ⊤ ≫
          (C.baseChange L).hom.appLE (Work.CurveBasics.Curve.specMap k L ⁻¹ᵁ ⊤) (C.bcOpens L W)
            (by rw [Scheme.Hom.preimage_top]; exact le_top)) := by
    rw [Scheme.Hom.comp_appLE]
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        ((Work.CurveBasics.Curve.specMap k L).app ⊤ ≫
          (C.baseChange L).hom.appLE (Work.CurveBasics.Curve.specMap k L ⁻¹ᵁ ⊤) (C.bcOpens L W)
            (by rw [Scheme.Hom.preimage_top]; exact le_top))
      = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (Work.CurveBasics.Curve.specMap k L).app ⊤) ≫
        (C.baseChange L).hom.appLE (Work.CurveBasics.Curve.specMap k L ⁻¹ᵁ ⊤) (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top) := by
    rw [← Category.assoc]
  -- `specMap k L` corresponds to `algebraMap k L` on global sections.
  have hnat' : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Work.CurveBasics.Curve.specMap k L).app ⊤
      = CommRingCat.ofHom (algebraMap k L) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality]
    rfl
  have h5 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (Work.CurveBasics.Curve.specMap k L).app ⊤) ≫
        (C.baseChange L).hom.appLE (Work.CurveBasics.Curve.specMap k L ⁻¹ᵁ ⊤) (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top)
      = (CommRingCat.ofHom (algebraMap k L) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).inv) ≫
        (C.baseChange L).hom.appLE (Work.CurveBasics.Curve.specMap k L ⁻¹ᵁ ⊤) (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top) := by
    rw [hnat']
    rfl
  have h6 : (CommRingCat.ofHom (algebraMap k L) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).inv) ≫
        (C.baseChange L).hom.appLE (Work.CurveBasics.Curve.specMap k L ⁻¹ᵁ ⊤) (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top)
      = CommRingCat.ofHom (algebraMap k L) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
        (C.baseChange L).hom.appLE (Work.CurveBasics.Curve.specMap k L ⁻¹ᵁ ⊤) (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top) :=
    Category.assoc _ _ _
  -- The two opens `specMap k L ⁻¹ᵁ ⊤` and `⊤` agree definitionally.
  have h7 : CommRingCat.ofHom (algebraMap k L) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
        (C.baseChange L).hom.appLE (Work.CurveBasics.Curve.specMap k L ⁻¹ᵁ ⊤) (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top)
      = CommRingCat.ofHom (algebraMap k L) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
        (C.baseChange L).hom.appLE ⊤ (C.bcOpens L W)
          (by rw [Scheme.Hom.preimage_top]; exact le_top) := by
    rfl
  have hAB := h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))
  -- Unfold the two algebra structures on the rings of sections:
  -- `Γ(C, W)` is a `k`-algebra via `Γ(Spec k) ≅ k` and `C.hom.appLE ⊤ W`,
  -- `Γ(C_L, W_L)` is an `L`-algebra via `Γ(Spec L) ≅ L` and `(C_L).hom.appLE ⊤ W_L`.
  have hkey : algebraMap k ↑(C.left.presheaf.obj (Opposite.op W)) c
      = (ConcreteCategory.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          C.hom.appLE ⊤ W (by rw [Scheme.Hom.preimage_top]; exact le_top))) c := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  have hkey2 : algebraMap L ↑((C.baseChange L).left.presheaf.obj (Opposite.op (C.bcOpens L W)))
        (algebraMap k L c)
      = (ConcreteCategory.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
          (C.baseChange L).hom.appLE ⊤ (C.bcOpens L W)
            (by rw [Scheme.Hom.preimage_top]; exact le_top))) ((algebraMap k L) c) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  rw [hkey, hkey2]
  rw [show (algebraMap k L) c
      = (ConcreteCategory.hom (CommRingCat.ofHom (algebraMap k L))) c from rfl]
  -- Collect both sides into a single morphism of `CommRingCat` evaluated at `c`.
  change (ConcreteCategory.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      C.hom.appLE ⊤ W (by rw [Scheme.Hom.preimage_top]; exact le_top) ≫
        (C.baseChangeFst L).app W)) c =
    (ConcreteCategory.hom (CommRingCat.ofHom (algebraMap k L) ≫
      (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
      (C.baseChange L).hom.appLE ⊤ (C.bcOpens L W)
        (by rw [Scheme.Hom.preimage_top]; exact le_top))) c
  exact congrArg (fun m => (ConcreteCategory.hom m) c) hAB

end Work.KeyLemma.BaseChange
