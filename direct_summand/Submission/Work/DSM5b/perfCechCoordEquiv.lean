import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSF1.Cech.CechComponents
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSM5b

universe a

/-! ## 1. The components of the Čech differential, with the universes of the target free

`Work.DSF1.Cech.cechComplexFunctor_d_π` requires the target category to have its object and hom
universes identified, which fails for `ModuleCat R`; this is the same computation with the universes
left free. -/
section Components

variable {C : Type*} [Category C] [HasFiniteProducts C]
variable {A : Type*} [Category A] [HasProducts A] [Preadditive A]
variable {ι : Type*} (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ)

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

/-! ## 2. Elementwise calculus for morphisms of `ModuleCat` -/
section Elementwise

variable {R₀ : Type*} [Ring R₀] {M N : ModuleCat R₀} {β : Type*}

lemma hom_finset_sum (s : Finset β) (f : β → (M ⟶ N)) :
    ((Finset.sum s f)).hom = ∑ i ∈ s, (f i).hom := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        show ((f a + Finset.sum s f).hom) = (f a).hom + (Finset.sum s f).hom from rfl, ih]

lemma hom_finset_sum_apply (s : Finset β) (f : β → (M ⟶ N)) (x : M) :
    ((Finset.sum s f)).hom x = ∑ i ∈ s, (f i).hom x := by
  rw [hom_finset_sum]
  exact LinearMap.sum_apply s (fun i => (f i).hom) x

lemma hom_finset_sum_zsmul_apply (s : Finset β) (c : β → ℤ) (f : β → (M ⟶ N)) (x : M) :
    ((Finset.sum s (fun i => c i • f i))).hom x = ∑ i ∈ s, c i • (f i).hom x := by
  rw [hom_finset_sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl

end Elementwise

/-! ## 3. The chart Čech complex in coordinates -/
namespace PCAux

variable (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R)

/-- The `n`-th simplex object of the Čech nerve of the chart cover. -/
noncomputable abbrev ES (n : ℕ) : FormalCoproduct ((Finset ι)ᵒᵖ) :=
  (FormalCoproduct.mk ι (chartIdx ι)).cech.obj (op (SimplexCategory.mk n))

/-- The chart Čech complex. -/
noncomputable abbrev KK : CochainComplex (ModuleCat R) ℕ :=
  (cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)

/-- The factors of the degree-`n` term of the chart Čech complex. -/
noncomputable abbrev fam (n : ℕ) : (ES (ι := ι) n).I → ModuleCat R :=
  fun y => (perfChartPresheaf p t).obj (op ((ES (ι := ι) n).obj y))

/-- The degree-`n` term of the chart Čech complex, in coordinates. -/
noncomputable abbrev KX (m : ℕ) : ModuleCat R := ∏ᶜ (fam p R t m)

/-- The differential `d m (m+1)`, with source and target in coordinates. -/
noncomputable def Kd (m : ℕ) : KX p R t m ⟶ KX p R t (m + 1) := (KK p R t).d m (m + 1)

/-- The deletion of the `a`-th entry, as a map of simplex types. -/
noncomputable def tupDelE {m : ℕ} (a : Fin (m + 2)) (τ : (ES (ι := ι) (m + 1)).I) :
    (ES (ι := ι) m).I :=
  fun b => τ (Fin.succAbove a b)

/-- The finset of values of a simplex of the Čech nerve (the counterpart of `tupRng` for the index
type of the nerve; the two are definitionally equal). -/
noncomputable abbrev tupRngE {m : ℕ} (τ : (ES (ι := ι) m).I) : Finset ι := Finset.univ.image τ

/-- The explicit tuple module of the chart Čech complex, indexed by the simplices of the nerve. -/
noncomputable abbrev PCXE (m : ℕ) : Type a :=
  ∀ τ : (ES (ι := ι) m).I, ↥(perfChartRing p t (tupRngE τ))

/-- The `a`-th coface of the Čech nerve, as a morphism of index objects. -/
noncomputable def cofHom (a : Fin 2) : ES (ι := ι) 1 ⟶ ES (ι := ι) 0 :=
  (FormalCoproduct.mk ι (chartIdx ι)).cech.map (SimplexCategory.δ a).op

lemma cofHom_f (a : Fin 2) (τ : (ES (ι := ι) 1).I) :
    (cofHom (ι := ι) a).f τ = tupDelE (ι := ι) a τ := rfl

/-- The `a`-th coface of the Čech nerve, as a morphism of the chart objects.  (A `def` with the
index types spelled out, so that it can be manipulated by rewriting.) -/
noncomputable def coface (a : Fin 2) (τ : (ES (ι := ι) 1).I) :
    (ES (ι := ι) 1).obj τ ⟶ (ES (ι := ι) 0).obj (tupDelE (ι := ι) a τ) :=
  (cofHom (ι := ι) a).φ τ

lemma tupRngE_del_subsetE (a : Fin 2) (τ : (ES (ι := ι) 1).I) :
    tupRngE (tupDelE (ι := ι) a τ) ⊆ tupRngE τ := by
  intro x hx
  rw [tupRngE, Finset.mem_image] at hx ⊢
  obtain ⟨b, -, hb⟩ := hx
  exact ⟨Fin.succAbove a b, Finset.mem_univ _, hb⟩

/-! ### The underlying finset of a product of singletons -/

lemma ES_obj_unop_gen {α : Type} [Fintype α] (Z : α → Finset ι) :
    ((∏ᶜ (fun a : α => op (Z a))).unop : Finset ι) = Finset.univ.sup Z := by
  have e := CategoryTheory.Limits.opCoproductIsoProduct Z
  have h1 : ((∏ᶜ (fun a : α => op (Z a))).unop : Finset ι) = (∐ Z) :=
    le_antisymm (leOfHom e.hom.unop) (leOfHom e.inv.unop)
  have h2 : (∐ Z : Finset ι) = Finset.univ.sup Z :=
    le_antisymm (leOfHom (Sigma.desc (fun b => homOfLE (Finset.le_sup (Finset.mem_univ b)))))
      (Finset.sup_le (fun b _ => leOfHom (Sigma.ι Z b)))
  rw [h1, h2]

lemma univ_sup_singleton_eq_univ_image {α : Type*} [Fintype α] (f : α → ι) :
    Finset.univ.sup (fun a : α => ({f a} : Finset ι)) = Finset.univ.image f := by
  ext y
  simp only [Finset.mem_sup, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

lemma ES_obj_unop (m : ℕ) (x : (ES (ι := ι) m).I) :
    ((ES (ι := ι) m).obj x).unop = tupRngE x := by
  have h := ES_obj_unop_gen (ι := ι)
    (Z := fun a : ToType (SimplexCategory.mk m) => ({x a} : Finset ι))
  rw [show (ES (ι := ι) m).obj x
      = (∏ᶜ (fun a : ToType (SimplexCategory.mk m) => op ({x a} : Finset ι))) from rfl, h]
  exact univ_sup_singleton_eq_univ_image (f := x)

/-! ### Transporting along equalities of finsets -/

/-- The identity equivalence between the perfected chart rings at equal finsets. -/
noncomputable def chartCongr {S T : Finset ι} (h : S = T) :
    ↥(perfChartRing p t S) ≃ₗ[R] ↥(perfChartRing p t T) :=
  h ▸ LinearEquiv.refl R ↥(perfChartRing p t S)

lemma chartCongr_algebraMap {S T : Finset ι} (h : S = T) (r : R) :
    chartCongr p R t h (algebraMap R ↥(perfChartRing p t S) r)
      = algebraMap R ↥(perfChartRing p t T) r := by
  cases h; rfl

lemma chartCongr_eq_zero {S T : Finset ι} (h : S = T) (x : ↥(perfChartRing p t S)) :
    chartCongr p R t h x = 0 ↔ x = 0 := by
  cases h
  exact Iff.rfl

lemma transport_naturality {S₀ T₀ S₁ T₁ : Finset ι} (hS : S₀ = S₁) (hT : T₀ = T₁)
    (h₀ : S₀ ⊆ T₀) (h₁ : S₁ ⊆ T₁) (x : ↥(perfChartRing p t S₀)) :
    chartCongr p R t hT (rho p t h₀ x) = rho p t h₁ (chartCongr p R t hS x) := by
  cases hS; cases hT
  exact rho_congr p t x

/-! ### The componentwise identification of the `τ`-factor with the chart ring at `tupRngE τ` -/

/-- The componentwise identification of the `τ`-factor `P (∏ᶜ op {τ a})` of the chart complex with
the perfected chart ring at `tupRngE τ`. -/
noncomputable def psiE {m : ℕ} (τ : (ES (ι := ι) m).I) :
    ↥((perfChartPresheaf p t).obj (op ((ES (ι := ι) m).obj τ))) ≃ₗ[R]
      ↥(perfChartRing p t (tupRngE τ)) :=
  chartCongr p R t (ES_obj_unop m τ)

lemma psiE_eq_chartCongr {m : ℕ} (τ : (ES (ι := ι) m).I) :
    psiE p R t τ = chartCongr p R t (ES_obj_unop m τ) := rfl

lemma psiE_algebraMap {m : ℕ} (τ : (ES (ι := ι) m).I) (w : R) :
    psiE p R t τ
        (algebraMap R ↥(perfChartRing p t ((ES (ι := ι) m).obj τ).unop) w)
      = algebraMap R ↥(perfChartRing p t (tupRngE τ)) w := by
  rw [psiE_eq_chartCongr]
  exact chartCongr_algebraMap p R t _ w

lemma psiE_eq_zero {m : ℕ} (τ : (ES (ι := ι) m).I)
    (y : ↥((perfChartPresheaf p t).obj (op ((ES (ι := ι) m).obj τ)))) :
    psiE p R t τ y = 0 ↔ y = 0 := by
  rw [psiE_eq_chartCongr]
  exact chartCongr_eq_zero p R t _ y

lemma psiE_map_sum {m : ℕ} (τ : (ES (ι := ι) m).I) {β : Type*} (s : Finset β) (c : β → ℤ)
    (f : β → ↥((perfChartPresheaf p t).obj (op ((ES (ι := ι) m).obj τ)))) :
    psiE p R t τ (∑ i ∈ s, c i • f i)
      = ∑ i ∈ s, c i • psiE p R t τ (f i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_zsmul (psiE p R t τ) (c i) (f i))

/-! ### The coaugmentation -/

lemma pi_lift_apply {M : Type*} [Ring M] {β : Type*} {f : β → ModuleCat M} [HasProduct f]
    {P : ModuleCat M} (q : (b : β) → P ⟶ f b) (b : β) (x : ↥P) :
    (Pi.π f b).hom ((Pi.lift q).hom x) = (q b).hom x := by
  rw [← ModuleCat.comp_apply, Pi.lift_comp_π]

lemma coaug_π_zero (y : (ES (ι := ι) 0).I) (w : R) :
    (Pi.π (fam p R t 0) y).hom ((perfChartCoaug p t).hom w)
      = algebraMap R ↥(perfChartRing p t ((ES (ι := ι) 0).obj y).unop) w := by
  have hpc : (perfChartCoaug p t).hom w
      = (Pi.lift (f := fam p R t 0) (fun y : (ES (ι := ι) 0).I => ModuleCat.ofHom
          (Algebra.linearMap R
            ↥(perfChartRing p t ((ES (ι := ι) 0).obj y).unop)))).hom w := rfl
  rw [hpc, pi_lift_apply]
  rfl

lemma piIsoPi_apply' (n : ℕ) (z : ↥(KX p R t n)) (i : (ES (ι := ι) n).I) :
    (ModuleCat.piIsoPi (fam p R t n)).toLinearEquiv z i = (Pi.π (fam p R t n) i).hom z := by
  rw [← ModuleCat.piIsoPi_hom_ker_subtype (fam p R t n) i, ModuleCat.comp_apply]
  rfl

/-- The degree-`0` coordinate equivalence. -/
noncomputable def PhiQ : ↥(KX p R t 0) ≃ₗ[R] PCX p t 0 :=
  (ModuleCat.piIsoPi (fam p R t 0)).toLinearEquiv.trans
    (LinearEquiv.piCongrRight (fun τ : (ES (ι := ι) 0).I => psiE p R t τ))

lemma PhiQ_apply (z : ↥(KX p R t 0)) (τ : (ES (ι := ι) 0).I) :
    PhiQ p R t z τ = psiE p R t τ ((Pi.π (fam p R t 0) τ).hom z) := by
  change (LinearEquiv.piCongrRight (fun x : (ES (ι := ι) 0).I => psiE p R t x)
      ((ModuleCat.piIsoPi (fam p R t 0)).toLinearEquiv z)) τ = _
  rw [LinearEquiv.piCongrRight_apply, piIsoPi_apply' p R t 0]

/-- The same, with the index type of the explicit tuple module written as the `0`-simplices of
the Čech nerve (a definition, so that the two index types are not confused by rewriting). -/
noncomputable def PhiQE : ↥(KX p R t 0) ≃ₗ[R] PCXE p R t 0 := PhiQ p R t

lemma PhiQE_apply (z : ↥(KX p R t 0)) (τ : (ES (ι := ι) 0).I) :
    PhiQE p R t z τ = psiE p R t τ ((Pi.π (fam p R t 0) τ).hom z) :=
  PhiQ_apply p R t z τ

lemma PhiQ_coaug (w : R) :
    PhiQ p R t ((perfChartCoaug p t).hom w) =
      fun τ : (ES (ι := ι) 0).I =>
        ⟨algebraMap R (Localization.Away (tS t (tupRngE τ))) w,
          (perfChartRing p t (tupRngE τ)).algebraMap_mem w⟩ := by
  funext τ
  rw [PhiQ_apply, coaug_π_zero, psiE_algebraMap]
  rfl

/-! ### The differential -/

lemma K_d_pi (τ : (ES (ι := ι) 1).I) :
    Kd p R t 0 ≫ Pi.π (fam p R t 1) τ
      = ∑ a : Fin 2, (-1 : ℤ) ^ (a : ℕ) •
          (Pi.π (fam p R t 0) (tupDelE (ι := ι) a τ) ≫
            (perfChartPresheaf p t).map (coface (ι := ι) a τ).op) :=
  cech_d_comp_π_gen (chartIdx ι) (perfChartPresheaf p t) 0 τ

lemma K_d_apply (z : ↥(KX p R t 0)) (τ : (ES (ι := ι) 1).I) :
    (Pi.π (fam p R t 1) τ).hom (Kd p R t 0 z)
      = ∑ a : Fin 2, (-1 : ℤ) ^ (a : ℕ) •
          ((Pi.π (fam p R t 0) (tupDelE (ι := ι) a τ) ≫
            (perfChartPresheaf p t).map (coface (ι := ι) a τ).op).hom z) := by
  rw [← ModuleCat.comp_apply, K_d_pi, hom_finset_sum_zsmul_apply]

lemma psiE_rho (a : Fin 2) (τ : (ES (ι := ι) 1).I)
    (x : ↥((perfChartPresheaf p t).obj (op ((ES (ι := ι) 0).obj (tupDelE (ι := ι) a τ))))) :
    psiE p R t τ (((perfChartPresheaf p t).map (coface (ι := ι) a τ).op).hom x)
      = rho p t (tupRngE_del_subsetE a τ) (psiE p R t (tupDelE (ι := ι) a τ) x) := by
  have hx : ((perfChartPresheaf p t).map (coface (ι := ι) a τ).op).hom x
      = rho p t (leOfHom (coface (ι := ι) a τ).unop) x := Subtype.ext rfl
  rw [psiE_eq_chartCongr, psiE_eq_chartCongr, hx]
  exact transport_naturality p R t (ES_obj_unop 0
      (tupDelE (ι := ι) a τ)) (ES_obj_unop 1 τ)
    _ (tupRngE_del_subsetE a τ) x

/-! ### Comparison with the explicit differential `PCd` -/

/-- The explicit differential `PCd`, with its index type written as the simplices of the nerve. -/
noncomputable def PCdE : PCXE p R t 0 →ₗ[R] PCXE p R t 1 := PCd p t 0

lemma PCdE_apply (z : PCXE p R t 0) (τ : (ES (ι := ι) 1).I) :
    PCdE p R t z τ
      = ∑ a : Fin 2, (-1 : R) ^ (a : ℕ) •
          rho p t (tupRngE_del_subsetE a τ) (z (tupDelE (ι := ι) a τ)) :=
  PCd_apply p t 0 z τ

/-- The `τ`-component of `PCd 0` applied to `PhiQ z`, written with the simplex index type of the
Čech nerve (a definition, so that the two index types are not confused by rewriting). -/
noncomputable def PCdcQ (z : ↥(KX p R t 0)) (τ : (ES (ι := ι) 1).I) :
    ↥(perfChartRing p t (tupRngE τ)) :=
  PCdE p R t (PhiQE p R t z) τ

/-- **The differential is `PCd` in coordinates.** -/
lemma PCdcQ_eq (z : ↥(KX p R t 0)) (τ : (ES (ι := ι) 1).I) :
    PCdcQ p R t z τ = psiE p R t τ ((Pi.π (fam p R t 1) τ).hom (Kd p R t 0 z)) := by
  rw [PCdcQ]
  rw [PCdE_apply]
  rw [K_d_apply]
  rw [psiE_map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [PhiQE_apply]
  rw [ModuleCat.comp_apply]
  exact congrArg (fun w => (-1 : R) ^ (a : ℕ) • w) (psiE_rho p R t a τ _).symm

/-- `PCd 0` vanishes on `PhiQ z` if and only if the differential vanishes at `z`. -/
lemma PhiQ_d_iff (z : ↥(KX p R t 0)) :
    Kd p R t 0 z = 0 ↔ PCd p t 0 (PhiQ p R t z) = 0 := by
  constructor
  · intro h
    have h1 : ∀ τ : (ES (ι := ι) 1).I, PCdcQ p R t z τ = 0 := by
      intro τ
      rw [PCdcQ_eq, h]
      simp only [map_zero]
    change (fun τ : (ES (ι := ι) 1).I => PCdcQ p R t z τ) = 0
    funext τ
    exact h1 τ
  · intro h
    have h1 : ∀ τ : (ES (ι := ι) 1).I,
        (Pi.π (fam p R t 1) τ).hom (Kd p R t 0 z) = 0 := by
      intro τ
      have h2 : psiE p R t τ ((Pi.π (fam p R t 1) τ).hom (Kd p R t 0 z)) = 0 := by
        rw [← PCdcQ_eq]
        show PCd p t 0 (PhiQ p R t z) τ = 0
        simpa using congrFun h τ
      exact (psiE_eq_zero p R t τ _).mp h2
    have h3 : (ModuleCat.piIsoPi (fam p R t 1)).toLinearEquiv (Kd p R t 0 z) = 0 := by
      funext τ
      rw [piIsoPi_apply' p R t 1]
      exact h1 τ
    exact (ModuleCat.piIsoPi (fam p R t 1)).toLinearEquiv.injective
      (by rw [h3, map_zero])

end PCAux

open PCAux in
/-- **Coordinates of the degree-`0` part of the perfected chart Čech complex.**

The degree-`0` term of `K = (cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)` is the
product, over the `0`-simplices `x : ToType ⦋0⦌ → ι`, of the perfected chart ring at the singleton
`{x 0}`; it is therefore canonically isomorphic, as an `R`-module, to the concrete tuple complex
`PCX p t 0 = ∀ τ : Fin 1 → ι, perfChartRing p t (tupRng τ)` of
`Submission/Work/DSM5b/PerfComplexDefs.lean`.

CLAIM: such an `R`-linear equivalence `Φ` exists, compatible with `perfChartCoaug p t` (whose
components are the maps `R → perfChartRing p t {i}`, i.e. the diagonal in coordinates) and
sending the Čech differential `d 0 1` to the concrete alternating coface differential `PCd p t 0`.

Route (all infrastructure exists in the workspace):
* `Work.DSF1.Cech.cech_obj_X_eq` identifies the degree-`n` term with the product over the
  `n`-simplices of the Čech nerve of `chartIdx ι`;
* `Work.DSF1.Cech.cechComplexFunctor_d_π` gives the component formula for `d n (n+1)` as the
  alternating sum of cofaces; the coface of a `0`-simplex `x` at a `1`-simplex `τ` is the
  restriction along `{x 0} ⊆ {τ 0, τ 1}`, i.e. `locRes t` (`Work.DSM5b.rho`-style), and for `n = 0`
  "delete the i-th index" matches `tupDel`/`tupRng` (`Work.DSM5b.tupRng_del_subset`);
* the component extraction at a single `0`-simplex is done explicitly in the proof of
  `Work.DSM5b.perfChartCoaug_kernel`; the component of a `Pi.lift` is
  `Work.DSM5b.pi_lift_apply_π` there;
* `(perfChartRing p t S, rho p t h)` of `PerfComplexDefs` is the presheaf of the complex, so `PCd`
  is literally the coordinate form of `d`.

Pure plumbing (no new mathematics); it exists so that the root/Frobenius bookkeeping for
`Work.DSM5b.perfChartH0_root_killing` can be done with explicit formulas. -/
theorem perfCechCoordEquiv (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) :
    ∃ Φ : ↥(((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)).X 0) ≃ₗ[R] PCX p t 0,
      (∀ w : R, Φ ((perfChartCoaug p t).hom w) =
        fun τ : Fin 1 → ι =>
          ⟨algebraMap R (Localization.Away (tS t (tupRng τ))) w,
            (perfChartRing p t (tupRng τ)).algebraMap_mem w⟩) ∧
      (∀ z : ↥(((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)).X 0),
        ((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)).d 0 1 z = 0 ↔
          PCd p t 0 (Φ z) = 0) := by
  refine ⟨PhiQ p R t, ?_, ?_⟩
  · intro w
    exact PhiQ_coaug p R t w
  · intro z
    exact PhiQ_d_iff p R t z

end Work.DSM5b
