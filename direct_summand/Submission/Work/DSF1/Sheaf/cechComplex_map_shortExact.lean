import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.SSEBasic
import Submission.Work.DSF1.Sheaf.SSECore

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

namespace Work.DSF1.Sheaf

/-!
# Short exactness of the Čech complex of a short exact sequence of presheaves

Let `X` be a scheme, `U : ι → X.Opens` a family of opens and
`T : ShortComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat)` a short complex of presheaves of abelian groups
which is pointwise short exact on all the opens `(cechN U n).obj x` of the Čech nerve of `U`.
Then the short complex of cochain complexes obtained by applying Mathlib's `cechComplexFunctor U`
is short exact.

The proof has three ingredients.

* `cechComplexFunctor_map_f_eq_pi_map` — in degree `n`, the Čech complex is the product, over all
  `x : (cechN U n).I`, of the values of the presheaf on `(cechN U n).obj x`, and the map induced by
  a morphism of presheaves is the product of the componentwise maps.
* `pi_map_shortExact` — a product of pointwise short exact sequences of abelian groups is short
  exact.  (This is where the real work is: `Mono`/`Epi` are detected by injectivity/surjectivity of
  the underlying functions and `Exact` by the elementwise kernel-equals-image condition
  `ShortComplex.ab_exact_iff`, with elements of a product handled through
  `Limits.Concrete.productEquiv` together with `Pi.map_π`.)
* `HomologicalComplex.shortExact_of_degreewise_shortExact` — a short complex of cochain complexes is
  short exact as soon as it is degreewise, and the passage from `T` to the degreewise complex is an
  isomorphism of short complexes, which is where `cechComplexFunctor_map_f_eq_pi_map` is used.
-/

/-- In degree `n`, the map induced by a morphism `η` of presheaves of abelian groups under
Mathlib's `cechComplexFunctor U` is the product, over the `n`-fold intersections of the family `U`,
of the componentwise maps `η.app`. -/
theorem cechComplexFunctor_map_f_eq_pi_map {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {P P' : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (η : P ⟶ P') (n : ℕ) :
    ((cechComplexFunctor U).map η).f n =
      Limits.Pi.map (fun x : (cechN U n).I => η.app (op ((cechN U n).obj x))) := by
  refine Pi.hom_ext _ _ (fun x => ?_)
  rw [Pi.map_π]
  exact Work.DSF1.Cech.cechComplexFunctor_map_pi U η n x

/-- The product of a pointwise short exact sequence of abelian groups is short exact.

Concretely, if `f i : G₁ i ⟶ G₂ i` and `g i : G₂ i ⟶ G₃ i` are, for every `i`, the maps of a short
exact sequence of abelian groups (`f i` injective, `g i` surjective, and everything in the kernel of
`g i` is a value of `f i`), then the product maps `Limits.Pi.map f` and `Limits.Pi.map g` form a
short exact sequence of abelian groups. -/
theorem pi_map_shortExact {I : Type u} (G₁ G₂ G₃ : I → AddCommGrpCat.{u})
    (f : (i : I) → G₁ i ⟶ G₂ i) (g : (i : I) → G₂ i ⟶ G₃ i)
    (hinj : ∀ i, Function.Injective (f i))
    (hsurj : ∀ i, Function.Surjective (g i))
    (hex : ∀ i (y : ↥(G₂ i)), g i y = 0 → ∃ z : ↥(G₁ i), f i z = y)
    (hzero : Limits.Pi.map f ≫ Limits.Pi.map g = 0) :
    (ShortComplex.mk (Limits.Pi.map f) (Limits.Pi.map g) hzero).ShortExact := by
  -- the components of `Pi.map p` against the projections of the target product
  have hπmap : ∀ {A B : I → AddCommGrpCat.{u}} (p : ∀ i, A i ⟶ B i) (i : I) (x : ↥(∏ᶜ A)),
      (Pi.π B i) ((Limits.Pi.map p) x) = (p i) ((Pi.π A i) x) := by
    intro A B p i x
    have h := congrArg (fun ψ => (ConcreteCategory.hom ψ) x) (Pi.map_π p i)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h
  haveI : ∀ i, Mono (f i) := fun i => (AddCommGrpCat.mono_iff_injective _).2 (hinj i)
  haveI : ∀ i, Epi (g i) := fun i => (AddCommGrpCat.epi_iff_surjective _).2 (hsurj i)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- exactness at the middle term, read off the kernels of the components
    refine (ShortComplex.ab_exact_iff _).2 (fun y hy => ?_)
    have hy' : ∀ i, (g i) ((Pi.π G₂ i) y) = 0 := by
      intro i
      rw [← hπmap g i y, hy]
      exact map_zero _
    choose z hz using fun i => hex i ((Pi.π G₂ i) y) (hy' i)
    refine ⟨(Concrete.productEquiv G₁).symm z, ?_⟩
    apply (Concrete.productEquiv G₂).injective
    funext i
    rw [Concrete.productEquiv_apply_apply, hπmap f i, Concrete.productEquiv_symm_apply_π, hz i,
      Concrete.productEquiv_apply_apply]
  · exact Limits.Pi.map_mono f
  · -- surjectivity, by choosing preimages of the components
    refine (AddCommGrpCat.epi_iff_surjective _).2 (fun y => ?_)
    choose z hz using fun i => hsurj i ((Pi.π G₃ i) y)
    refine ⟨(Concrete.productEquiv G₂).symm z, ?_⟩
    apply (Concrete.productEquiv G₃).injective
    funext i
    rw [Concrete.productEquiv_apply_apply, hπmap g i, Concrete.productEquiv_symm_apply_π, hz i,
      Concrete.productEquiv_apply_apply]

theorem cechComplex_map_shortExact {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (T : ShortComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hzero : ((cechComplexFunctor U).map T.f) ≫ ((cechComplexFunctor U).map T.g) = 0)
    (hinj : ∀ (n : ℕ) (x : Fin (n + 1) → ι),
      Function.Injective (T.f.app (op ((cechN U n).obj x))))
    (hsurj : ∀ (n : ℕ) (x : Fin (n + 1) → ι),
      Function.Surjective (T.g.app (op ((cechN U n).obj x))))
    (hex : ∀ (n : ℕ) (x : Fin (n + 1) → ι) (y : T.X₂.obj (op ((cechN U n).obj x))),
      T.g.app (op ((cechN U n).obj x)) y = 0 →
      ∃ z : T.X₁.obj (op ((cechN U n).obj x)), T.f.app (op ((cechN U n).obj x)) z = y) :
    (ShortComplex.mk ((cechComplexFunctor U).map T.f) ((cechComplexFunctor U).map T.g)
      hzero).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  let G₁ : (cechN U n).I → AddCommGrpCat.{u} := fun x => T.X₁.obj (op ((cechN U n).obj x))
  let G₂ : (cechN U n).I → AddCommGrpCat.{u} := fun x => T.X₂.obj (op ((cechN U n).obj x))
  let G₃ : (cechN U n).I → AddCommGrpCat.{u} := fun x => T.X₃.obj (op ((cechN U n).obj x))
  let f' : ∀ x, G₁ x ⟶ G₂ x := fun x => T.f.app (op ((cechN U n).obj x))
  let g' : ∀ x, G₂ x ⟶ G₃ x := fun x => T.g.app (op ((cechN U n).obj x))
  have hf : ((ShortComplex.mk ((cechComplexFunctor U).map T.f) ((cechComplexFunctor U).map T.g)
        hzero).map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n)).f
      = Limits.Pi.map f' := by
    rw [ShortComplex.map_f]
    exact cechComplexFunctor_map_f_eq_pi_map U T.f n
  have hg : ((ShortComplex.mk ((cechComplexFunctor U).map T.f) ((cechComplexFunctor U).map T.g)
        hzero).map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n)).g
      = Limits.Pi.map g' := by
    rw [ShortComplex.map_g]
    exact cechComplexFunctor_map_f_eq_pi_map U T.g n
  -- the degreewise short complex is the product short complex of `f'` and `g'`
  have hS₀ : (ShortComplex.mk (Limits.Pi.map f') (Limits.Pi.map g') (by
      have h : ((ShortComplex.mk ((cechComplexFunctor U).map T.f) ((cechComplexFunctor U).map T.g)
          hzero).map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n)).f ≫
          ((ShortComplex.mk ((cechComplexFunctor U).map T.f) ((cechComplexFunctor U).map T.g)
          hzero).map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n)).g = 0 :=
        (ShortComplex.mk ((cechComplexFunctor U).map T.f) ((cechComplexFunctor U).map T.g)
          hzero).map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n) |>.zero
      rw [hf, hg] at h
      exact h)).ShortExact :=
    pi_map_shortExact G₁ G₂ G₃ f' g' (fun x => hinj n x) (fun x => hsurj n x)
      (fun x => hex n x) _
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)) hS₀

end Work.DSF1.Sheaf

namespace Work.DSF1.Sheaf.Work.DSF1.Sheaf

/-- Alias of `Work.DSF1.Sheaf.cechComplex_map_shortExact` under the (doubled) namespace name that
the file of `Submission/Work/DSF1/Sheaf/cechComplex_map_shortExact.lean` produced while the
statement was wrapped in a second copy of the enclosing namespace.  Kept so that files already
written against that name keep building. -/
theorem cechComplex_map_shortExact {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (T : ShortComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hzero : ((cechComplexFunctor U).map T.f) ≫ ((cechComplexFunctor U).map T.g) = 0)
    (hinj : ∀ (n : ℕ) (x : Fin (n + 1) → ι),
      Function.Injective (T.f.app (op ((cechN U n).obj x))))
    (hsurj : ∀ (n : ℕ) (x : Fin (n + 1) → ι),
      Function.Surjective (T.g.app (op ((cechN U n).obj x))))
    (hex : ∀ (n : ℕ) (x : Fin (n + 1) → ι) (y : T.X₂.obj (op ((cechN U n).obj x))),
      T.g.app (op ((cechN U n).obj x)) y = 0 →
      ∃ z : T.X₁.obj (op ((cechN U n).obj x)), T.f.app (op ((cechN U n).obj x)) z = y) :
    (ShortComplex.mk ((cechComplexFunctor U).map T.f) ((cechComplexFunctor U).map T.g)
      hzero).ShortExact :=
  _root_.Work.DSF1.Sheaf.cechComplex_map_shortExact U T hzero hinj hsurj hex

end Work.DSF1.Sheaf.Work.DSF1.Sheaf
