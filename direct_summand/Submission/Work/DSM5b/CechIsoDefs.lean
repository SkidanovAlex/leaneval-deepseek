import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.PerfComplexDefs

/-!
# DSM5b — coordinates of the perfected chart Čech complex

Let `R` be perfect of characteristic `p`, `t : ι → R` finite (`[Finite ι]`), `P = perfChartPresheaf p t`
the presheaf of perfected chart rings on `(Finset ι)ᵒᵖᵒᵖ`, and

`K = (cechComplexFunctor (chartIdx ι)).obj P`

Mathlib's (non-normalised, alternating coface) Čech complex of the cover `i ↦ {i}`.  In degree `m`
it is the product (over all `(m+1)`-tuples `τ : Fin (m+1) → ι`) of `P` evaluated at the product in
`(Finset ι)ᵒᵖ` of the objects `op {τ a}`.

This file collects the *coordinates* of `K`.  In degree `m` the term of `K` is identified (by
definitional equality) with the product `KX p t m = ∏ᶜ (pFam p t m)` over the tuples `τ`, where
`pFam p t m τ = P.obj (op (chartPrd τ))`; `Kd p t m` is the differential.  Then:

* `chartPrd τ = ∏ᶜ (fun a => op {τ a})`, with `(chartPrd τ).unop = tupRng τ` (`chartPrd_unop_eq`)
  and the canonical isomorphism `chartPrdIso τ : op (tupRng τ) ≅ chartPrd τ` (which exists because
  `(Finset ι)ᵒᵖ` is a thin category, so all parallel arrows are equal);
* `dblHom h : op (op S) ⟶ op (op T)` (`h : S ⊆ T`), the presheaf-level restriction, so that
  `P.map (dblHom h) = rho p t h` (`perfChartPresheaf_map_dblHom`);
* `psi τ = P.map ((chartPrdIso τ).op) : P.obj (op (chartPrd τ)) ⟶ perfChartRing p t (tupRng τ)`,
  the "τ-component" identification (`psiIso` is its iso form);
* `coordIso m : KX p t m ≅ ModuleCat.of R (PCX p t m)`, the degree-by-degree identification of `K`
  with the explicit tuple complex `PCX`/`PCd` of `Submission/Work/DSM5b/PerfComplexDefs.lean`,
  together with its components (`coordIso_hom_apply`);
* `psi_coface`, the key naturality statement: the composite of `psi` with an (arbitrary) coface is
  the composite of `psi` with the restriction `rho` — a consequence of thinness, and the reason the
  differential of `K` computes to `PCd` in coordinates (`coordIso_comm`).

Everything here is determined by the (unique) isomorphisms in the thin category `(Finset ι)ᵒᵖ`, so
no choices are made beyond irrelevant ones.

Do NOT use the frozen sorried declaration `DSMap.Mix2.area_M5b`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open Opposite Limits
open scoped Simplicial BigOperators

universe a

/-! ## The components of the Čech differential in any target category -/

section Components

variable {C : Type*} [Category C] [HasFiniteProducts C]
variable {A : Type*} [Category A] [HasProducts A] [Preadditive A]
variable {ι : Type*} (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ)

/-- **Component formula for the Čech differential**, with the universe parameters of the target
category left free (unlike `Work.DSF1.Cech.cechComplexFunctor_d_π`, whose target has its object and
hom universes identified, and which therefore does not apply to `ModuleCat R`): the `x`-th component
of `d n (n+1)` is the alternating sum of the components of the individual cofaces. -/
theorem cech_d_comp_π_gen
    (x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n+1⦌)).I) :
    ((cechComplexFunctor U).obj P).d n (n+1) ≫
      Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n+1⦌)).obj y))) x
    = ∑ a : Fin (n+2), (-1 : ℤ) ^ (a : ℕ) •
      (Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
        (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f x) ≫
      P.map (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).φ x).op) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

end Components

/-! ## Elementary structure of the thin index category `(Finset ι)ᵒᵖ` -/

section Prd

variable {ι : Type a} [DecidableEq ι]

/-- The product in the thin category `(Finset ι)ᵒᵖ` of the singleton charts `op {τ a}`.  This is the
object of `(Finset ι)ᵒᵖ` at which the `τ`-component of the degree-`m` term of the chart Čech
complex is evaluated. -/
noncomputable abbrev chartPrd {m : ℕ} (τ : Fin (m + 1) → ι) : (Finset ι)ᵒᵖ :=
  ∏ᶜ (fun a : Fin (m + 1) => op ({τ a} : Finset ι))

/-- The canonical morphism `op (tupRng τ) ⟶ chartPrd τ`: it exists since `{τ a} ⊆ tupRng τ` for all
`a`. -/
noncomputable abbrev chartPrdLift {m : ℕ} (τ : Fin (m + 1) → ι) : op (tupRng τ) ⟶ chartPrd τ :=
  Pi.lift (fun a : Fin (m + 1) =>
    (homOfLE (Finset.singleton_subset_iff.mpr
      (Finset.mem_image_of_mem τ (Finset.mem_univ a)))).op)

/-- The underlying finset of `chartPrd τ` is contained in `tupRng τ`: through the universal property
of the product (any element of `chartPrd τ` is one of the `τ a`). -/
lemma chartPrd_unop_le_tupRng {m : ℕ} (τ : Fin (m + 1) → ι) :
    (chartPrd τ).unop ≤ tupRng τ :=
  leOfHom (chartPrdLift τ).unop

/-- `tupRng τ` is contained in the underlying finset of `chartPrd τ`: through the projections of the
product. -/
lemma tupRng_le_chartPrd_unop {m : ℕ} (τ : Fin (m + 1) → ι) :
    tupRng τ ≤ (chartPrd τ).unop := by
  intro x hx
  rw [tupRng, Finset.mem_image] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact leOfHom (Pi.π (fun a : Fin (m + 1) => op ({τ a} : Finset ι)) a).unop
    (Finset.mem_singleton_self _)

/-- The underlying finset of `chartPrd τ` is `tupRng τ`. -/
lemma chartPrd_unop_eq {m : ℕ} (τ : Fin (m + 1) → ι) : (chartPrd τ).unop = tupRng τ :=
  le_antisymm (chartPrd_unop_le_tupRng τ) (tupRng_le_chartPrd_unop τ)

/-- The canonical identification `op (tupRng τ) ≅ chartPrd τ` in the thin category `(Finset ι)ᵒᵖ`. -/
noncomputable def chartPrdIso {m : ℕ} (τ : Fin (m + 1) → ι) : op (tupRng τ) ≅ chartPrd τ where
  hom := chartPrdLift τ
  inv := (homOfLE (tupRng_le_chartPrd_unop τ)).op
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The restriction morphism of the (double) opposite of the thin category `(Finset ι)ᵒᵖ` induced by
`h : S ⊆ T`: this is the morphism of the index category of the chart presheaf. -/
noncomputable abbrev dblHom {S T : Finset ι} (h : S ⊆ T) : op (op S) ⟶ op (op T) :=
  (homOfLE h).op.op

/-- The `a`-th coface of the Čech nerve of the chart cover, as a morphism of index objects: it is
the `τ`-component of the simplicial face map `δ a`, i.e. the morphism
`chartPrd τ ⟶ chartPrd (tupDel a τ)` obtained from the projection onto the `a`-deleted tuple. -/
noncomputable abbrev coface {m : ℕ} (a : Fin (m + 2)) (τ : Fin (m + 2) → ι) :
    chartPrd τ ⟶ chartPrd (tupDel a τ) :=
  (((FormalCoproduct.mk ι (chartIdx ι)).cech.map (SimplexCategory.δ a).op).φ τ)

lemma coface_f {m : ℕ} (a : Fin (m + 2)) (τ : Fin (m + 2) → ι) :
    (((FormalCoproduct.mk ι (chartIdx ι)).cech.map (SimplexCategory.δ a).op).f τ) = tupDel a τ :=
  rfl

end Prd

/-! ## Elementwise calculus of morphisms of `ModuleCat` -/

section Elementwise

variable {R₀ : Type*} [Ring R₀] {M N : ModuleCat R₀} {β : Type*}

/-- The underlying linear map of a finite sum of morphisms of `ModuleCat`, as a sum of linear maps. -/
lemma hom_finset_sum (s : Finset β) (f : β → (M ⟶ N)) :
    ((Finset.sum s f)).hom = ∑ i ∈ s, (f i).hom := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        show ((f a + Finset.sum s f).hom) = (f a).hom + (Finset.sum s f).hom from rfl, ih]

/-- Elementwise form of `hom_finset_sum`. -/
lemma hom_finset_sum_apply (s : Finset β) (f : β → (M ⟶ N)) (x : M) :
    ((Finset.sum s f)).hom x = ∑ i ∈ s, (f i).hom x := by
  rw [hom_finset_sum]
  exact LinearMap.sum_apply s (fun i => (f i).hom) x

/-- Elementwise form of a finite sum of `ℤ`-multiples of morphisms of `ModuleCat`. -/
lemma hom_finset_sum_zsmul_apply (s : Finset β) (c : β → ℤ) (f : β → (M ⟶ N)) (x : M) :
    ((Finset.sum s (fun i => c i • f i))).hom x = ∑ i ∈ s, c i • (f i).hom x := by
  rw [hom_finset_sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The components of the identification of a categorical product with the concrete product, after a
componentwise isomorphism: the `i`-component of the image is the `i`-component of the isomorphism
applied to the `i`-coordinate. -/
lemma pi_mapIso_piIsoPi_hom_apply {F G : β → ModuleCat R₀} [HasProductsOfShape β (ModuleCat R₀)]
    (e : ∀ i, F i ≅ G i) (x : ↥(∏ᶜ F)) (i : β) :
    (ModuleCat.ofHom
        (LinearMap.proj i : (∀ i, ↥(G i)) →ₗ[R₀] ↥(G i))).hom
        (((Pi.mapIso e) ≪≫ (ModuleCat.piIsoPi G)).hom.hom x)
      = ((e i).hom.hom) ((Pi.π F i).hom x) := by
  rw [Iso.trans_hom, ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ModuleCat.piIsoPi_hom_ker_subtype, ← ModuleCat.comp_apply, Pi.mapIso_hom_π,
    ModuleCat.comp_apply]

end Elementwise

/-! ## The chart complex in coordinates -/

section Chart

variable (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R)

/-- The presheaf map of `perfChartPresheaf` for the index morphism `dblHom h` is the restriction map
`rho p t h` of perfected chart rings. -/
lemma perfChartPresheaf_map_dblHom {S T : Finset ι} (h : S ⊆ T) :
    (perfChartPresheaf p t).map (dblHom h) = ModuleCat.ofHom (rho p t h).toLinearMap := by
  ext x
  exact Subtype.ext rfl

/-- The `τ`-component identification: the perfected chart ring at the product of the singleton charts
`{τ a}` is the perfected chart ring at `tupRng τ`. -/
noncomputable def psiIso {m : ℕ} (τ : Fin (m + 1) → ι) :
    (perfChartPresheaf p t).obj (op (chartPrd τ)) ≅
      (perfChartPresheaf p t).obj (op (op (tupRng τ))) :=
  (perfChartPresheaf p t).mapIso ((chartPrdIso τ).op)

/-- The underlying map of `psiIso`. -/
noncomputable abbrev psi {m : ℕ} (τ : Fin (m + 1) → ι) :
    (perfChartPresheaf p t).obj (op (chartPrd τ)) ⟶
      (perfChartPresheaf p t).obj (op (op (tupRng τ))) :=
  (psiIso p t τ).hom

lemma psi_eq_map_chartPrdIso {m : ℕ} (τ : Fin (m + 1) → ι) :
    psi p t τ = (perfChartPresheaf p t).map ((chartPrdIso τ).op).hom :=
  Functor.mapIso_hom _ _

/-- **Key naturality in coordinates.**  Composing the component identification `psi p t τ` with the
presheaf map of an arbitrary coface equals composing `psi p t (tupDel a τ)` with the restriction map.
Both sides reduce to `P.map` of parallel morphisms of the (thin!) index category, so this holds for
*any* morphism `chartPrd τ ⟶ chartPrd (tupDel a τ)`. -/
theorem psi_coface {m : ℕ} (a : Fin (m + 2)) (τ : Fin (m + 2) → ι) :
    (perfChartPresheaf p t).map ((coface a τ).op) ≫ psi p t τ
      = psi p t (tupDel a τ) ≫ (perfChartPresheaf p t).map (dblHom (tupRng_del_subset a τ)) := by
  rw [psi_eq_map_chartPrdIso, psi_eq_map_chartPrdIso, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (Subsingleton.elim _ _)

/-- The factors of the degree-`m` term of the chart Čech complex, in coordinates. -/
noncomputable abbrev pFam (m : ℕ) : (Fin (m + 1) → ι) → ModuleCat R :=
  fun τ => (perfChartPresheaf p t).obj (op (chartPrd τ))

/-- The factors of the explicit tuple module `PCX p t m`, in coordinates. -/
noncomputable abbrev piFam (m : ℕ) : (Fin (m + 1) → ι) → ModuleCat R :=
  fun τ => ModuleCat.of R ↥(perfChartRing p t (tupRng τ))

/-- The degree-`m` term of the chart Čech complex, written as the product of the chart rings in
coordinates.  This is the same object as `((cechComplexFunctor (chartIdx ι)).obj
(perfChartPresheaf p t)).X m`, by definitional equality. -/
noncomputable abbrev KX (m : ℕ) : ModuleCat R := ∏ᶜ (pFam p t m)

/-- The differential `d m (m+1)` of the chart Čech complex, with source and target written in
coordinates. -/
noncomputable abbrev Kd (m : ℕ) : KX p t m ⟶ KX p t (m + 1) :=
  ((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)).d m (m + 1)

/-- The coordinate identification of the degree-`m` term of the perfected chart Čech complex with the
explicit tuple module `PCX p t m`: componentwise, at the tuple `τ`, the identification `psi p t τ` of
the chart at `∏ᶜ op {τ a}` with the chart at `tupRng τ`. -/
noncomputable def coordIso (m : ℕ) : KX p t m ≅ ModuleCat.of R (PCX p t m) :=
  Pi.mapIso (fun τ : Fin (m + 1) → ι => psiIso p t τ) ≪≫ ModuleCat.piIsoPi (piFam p t m)

/-- The components of `coordIso`: the `τ`-coordinate of `(coordIso m).hom z` is the image of the
`τ`-coordinate of `z` under `psi p t τ`. -/
lemma coordIso_hom_apply (m : ℕ) (z : ↥(KX p t m)) (τ : Fin (m + 1) → ι) :
    (coordIso p t m).hom z τ = (psi p t τ).hom ((Pi.π (pFam p t m) τ).hom z) :=
  pi_mapIso_piIsoPi_hom_apply (fun τ => psiIso p t τ) z τ

/-- The component formula for the differential of the chart Čech complex, in coordinates: the
`τ`-coordinate of `d m (m+1)` is the alternating sum of the coface components. -/
lemma K_d_pi (m : ℕ) (τ : Fin (m + 2) → ι) :
    Kd p t m ≫ Pi.π (pFam p t (m + 1)) τ
      = ∑ a : Fin (m + 2), (-1 : ℤ) ^ (a : ℕ) •
          (Pi.π (pFam p t m) (tupDel a τ) ≫
            (perfChartPresheaf p t).map ((coface a τ).op)) :=
  cech_d_comp_π_gen (chartIdx ι) (perfChartPresheaf p t) m τ

/-- Elementwise form of `K_d_pi`. -/
lemma K_d_apply (m : ℕ) (z : ↥(KX p t m)) (τ : Fin (m + 2) → ι) :
    (Pi.π (pFam p t (m + 1)) τ).hom ((Kd p t m) z)
      = ∑ a : Fin (m + 2), (-1 : ℤ) ^ (a : ℕ) •
          ((Pi.π (pFam p t m) (tupDel a τ) ≫
            (perfChartPresheaf p t).map ((coface a τ).op)).hom z) := by
  rw [← ModuleCat.comp_apply, K_d_pi, hom_finset_sum_zsmul_apply]

/-- The composite of `psi p t τ` with the presheaf map of a coface, evaluated on an element: this is
the restriction map `rho` applied to the image under `psi p t (tupDel a τ)`. -/
lemma psi_apply_map_coface (m : ℕ) (a : Fin (m + 2)) (τ : Fin (m + 2) → ι)
    (y : ↥(pFam p t m (tupDel a τ))) :
    (psi p t τ).hom (((perfChartPresheaf p t).map ((coface a τ).op)).hom y)
      = rho p t (tupRng_del_subset a τ) ((psi p t (tupDel a τ)).hom y) := by
  rw [← ModuleCat.comp_apply, psi_coface, ModuleCat.comp_apply, perfChartPresheaf_map_dblHom]
  rfl

/-- The `a`-th summand of the differential in coordinates, after applying `psi p t τ`: it is the
restriction map `rho` applied to the `(tupDel a τ)`-coordinate. -/
lemma coordIso_d_term (m : ℕ) (a : Fin (m + 2)) (τ : Fin (m + 2) → ι) (z : ↥(KX p t m)) :
    (psi p t τ).hom
        ((Pi.π (pFam p t m) (tupDel a τ) ≫
          (perfChartPresheaf p t).map ((coface a τ).op)).hom z)
      = rho p t (tupRng_del_subset a τ) ((coordIso p t m).hom z (tupDel a τ)) := by
  rw [ModuleCat.comp_apply, psi_apply_map_coface]
  exact congrArg _ (coordIso_hom_apply p t m z (tupDel a τ)).symm

/-- The `a`-th summand of the differential in coordinates, after applying `psi p t τ`: the `ℤ`-scalar
`(-1)^a` is the `R`-scalar `(-1)^a` and the differential component is the restriction map `rho`. -/
lemma coordIso_d_term_zsmul (m : ℕ) (a : Fin (m + 2)) (τ : Fin (m + 2) → ι) (z : ↥(KX p t m)) :
    (psi p t τ).hom
        (((-1 : ℤ) ^ (a : ℕ)) •
          ((Pi.π (pFam p t m) (tupDel a τ) ≫
            (perfChartPresheaf p t).map ((coface a τ).op)).hom z))
      = ((-1 : R) ^ (a : ℕ)) •
          rho p t (tupRng_del_subset a τ) ((coordIso p t m).hom z (tupDel a τ)) := by
  have h : ((-1 : ℤ) ^ (a : ℕ)) •
        rho p t (tupRng_del_subset a τ) ((coordIso p t m).hom z (tupDel a τ))
      = ((-1 : R) ^ (a : ℕ)) •
        rho p t (tupRng_del_subset a τ) ((coordIso p t m).hom z (tupDel a τ)) := by
    rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [map_zsmul, coordIso_d_term]
  exact h

/-- **The differential of the chart Čech complex is `PCd` in coordinates.** -/
theorem coordIso_comm (m : ℕ) (z : ↥(KX p t m)) :
    (coordIso p t (m + 1)).hom ((Kd p t m) z)
      = ModuleCat.ofHom (PCd p t m) ((coordIso p t m).hom z) := by
  funext τ
  change (coordIso p t (m + 1)).hom ((Kd p t m) z) τ
      = (PCd p t m) ((coordIso p t m).hom z) τ
  rw [coordIso_hom_apply, K_d_apply, map_sum, PCd_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact coordIso_d_term_zsmul p t m a τ z

end Chart

end Work.DSM5b
