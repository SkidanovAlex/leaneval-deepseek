import Mathlib
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.cechMap_exact
import Submission.Work.DSCOH.cechMap_natural
import Submission.Work.DSCOH.degZero_exact
import Submission.Work.DSCOH.ChartULift
import Submission.Work.DSCOH.chartCechULift_homology_finite

/-!
## Finiteness of the cohomology of a short exact sequence of chart Čech complexes

Given a degreewise short exact sequence of graded `A[X₀,…,X_{n-1}]`-modules

  `ℳ --f--> ℳ' --g--> ℳ''`,

the induced maps of chart Čech complexes form a short exact sequence of cochain complexes
(`cechMap`, with componentwise short exactness supplied by `Work.DSCOH.cechMap_exact`).
The associated long exact sequence in cohomology propagates finiteness of the `A`-modules
`H^q(-)` across the triangle, which is the induction step in Serre's finiteness theorem.

The three modules of the statement live in *independent* universes, so the three chart Čech
complexes are objects of the categories `CochainComplex (ModuleCat.{w} A) ℕ`,
`CochainComplex (ModuleCat.{w'} A) ℕ` and `CochainComplex (ModuleCat.{w''} A) ℕ`; they cannot
be compared directly.  We therefore transport all three into the common universe
`V = max uA (max w (max w' w''))` using `chartCechULift` (the degreewise `ULift` of the chart
Čech complex, see `Work.DSCOH.ChartULift`), run the long exact sequence there, and transport
finiteness back with `Work.DSCOH.chartCechULift_homology_finite`.
-/

open MvPolynomial CategoryTheory Limits

namespace Work.DSCOH

-- `chartCech` and `chartCechOf` are plain `def`s; unfolding them at `.reducible` transparency
-- is needed whenever the *types* of their components are identified with `ModuleCat.of A _`.
set_option allowUnsafeReducibility true
attribute [local reducible] chartCech chartCechOf

universe uA w w' w''

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The differential of the chart Čech complex, explicitly as `cechDiff`. -/
lemma chartCech_d {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ) :
    (chartCech (A := A) (n := n) (M := M) ℳ).d q (q + 1) =
      ModuleCat.ofHom (cechDiff (A := A) (n := n) (M := M) ℳ q) := by
  simp only [chartCech, chartCechOf, CochainComplex.of_d]

/-- **Finiteness of the middle term of an exact sequence.**  Over a Noetherian ring, if
`X → Y → Z` is exact and `X`, `Z` are finite `A`-modules, then so is `Y`.  (Only the exactness
at `Y` is used; `g` need not be surjective.) -/
theorem module_finite_middle_of_exact {A : Type*} [CommRing A] [IsNoetherianRing A]
    {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z]
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (h : Function.Exact f g)
    [Module.Finite A X] [Module.Finite A Z] : Module.Finite A Y := by
  haveI : IsNoetherian A Z := isNoetherian_of_isNoetherianRing_of_finite A Z
  haveI : Module.Finite A (LinearMap.range g) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  refine Module.Finite.of_exact (f := f)
    (g := g.codRestrict (LinearMap.range g) (fun y => ⟨y, rfl⟩)) ?_ ?_
  · intro y
    have hiff : ((g.codRestrict (LinearMap.range g) (fun y => ⟨y, rfl⟩)) y = 0) ↔ g y = 0 := by
      constructor
      · intro hy
        exact congrArg Subtype.val hy
      · intro hy
        exact Subtype.ext hy
    rw [hiff]
    exact h y
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

/-! ## The main result -/

/-- The version of `homology_finite_of_graded_shortExact` with the three universes named, so
that they can be identified inside the proof. -/
theorem homology_finite_of_graded_shortExact_aux {A : Type uA} [CommRing A] [IsNoetherianRing A]
    {n : ℕ} {M : Type w} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {M' : Type w'} [AddCommGroup M'] [Module A M'] [Module (Poly A n) M']
    [IsScalarTower A (Poly A n) M']
    {M'' : Type w''} [AddCommGroup M''] [Module A M''] [Module (Poly A n) M'']
    [IsScalarTower A (Poly A n) M'']
    {ℳ : ℕ → Submodule A M} {ℳ' : ℕ → Submodule A M'} {ℳ'' : ℕ → Submodule A M''}
    [SetLike.GradedSMul (homSub A n) ℳ] [SetLike.GradedSMul (homSub A n) ℳ']
    [SetLike.GradedSMul (homSub A n) ℳ'']
    (f : M →ₗ[Poly A n] M') (g : M' →ₗ[Poly A n] M'')
    (hinj : Function.Injective f) (hex : Function.Exact f g)
    (hgr1 : ∀ d, Submodule.map (f.restrictScalars A) (ℳ d) ≤ ℳ' d)
    (hgr2 : ∀ d, Submodule.map (g.restrictScalars A) (ℳ' d) = ℳ'' d)
    (hker : ∀ d, ℳ' d ⊓ LinearMap.ker (g.restrictScalars A) ≤
      Submodule.map (f.restrictScalars A) (ℳ d))
    (q : ℕ) :
    (Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) →
      Module.Finite A ((chartCech (A := A) (n := n) (M := M'') ℳ'').homology q) →
      Module.Finite A ((chartCech (A := A) (n := n) (M := M') ℳ').homology q)) ∧
    (Module.Finite A ((chartCech (A := A) (n := n) (M := M') ℳ').homology q) →
      Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology (q + 1)) →
      Module.Finite A ((chartCech (A := A) (n := n) (M := M'') ℳ'').homology q)) := by
  have hloc : ∀ q : ℕ,
      Function.Injective (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 q) ∧
      Function.Exact (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 q)
        (cechMap (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) q) ∧
      Function.Surjective (cechMap (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) q) :=
    fun q => cechMap_exact f g hinj hex hgr1 hgr2 hker q
  -- the three complexes, transported to the common universe `max uA (max w (max w' w''))`
  let C₁ : CochainComplex (ModuleCat.{max uA (max w (max w' w''))} A) ℕ :=
    chartCechULift.{uA, w, max uA (max w (max w' w''))} (A := A) (n := n) ℳ
  let C₂ : CochainComplex (ModuleCat.{max uA (max w (max w' w''))} A) ℕ :=
    chartCechULift.{uA, w', max uA (max w (max w' w''))} (A := A) (n := n) ℳ'
  let C₃ : CochainComplex (ModuleCat.{max uA (max w (max w' w''))} A) ℕ :=
    chartCechULift.{uA, w'', max uA (max w (max w' w''))} (A := A) (n := n) ℳ''
  -- the maps of complexes
  let F : C₁ ⟶ C₂ := CochainComplex.ofHom
    (fun i => ModuleCat.ofHom (uliftLinearMap (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 i)))
    (fun i => by
      rw [chartCechULift_d, chartCechULift_d, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp,
        uliftLinearMap_comp, uliftLinearMap_comp,
        cechMap_natural (A := A) (n := n) ℳ ℳ' f hgr1 i])
  let G : C₂ ⟶ C₃ := CochainComplex.ofHom
    (fun i => ModuleCat.ofHom (uliftLinearMap
      (cechMap (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) i)))
    (fun i => by
      rw [chartCechULift_d, chartCechULift_d, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp,
        uliftLinearMap_comp, uliftLinearMap_comp,
        cechMap_natural (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) i])
  have hGF : F ≫ G = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
    rw [show F.f i = ModuleCat.ofHom (uliftLinearMap
          (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 i)) from rfl,
      show G.f i = ModuleCat.ofHom (uliftLinearMap
          (cechMap (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) i)) from rfl]
    rw [← ModuleCat.ofHom_comp, uliftLinearMap_comp]
    have hz : (cechMap (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) i).comp
        (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 i) = 0 :=
      LinearMap.ext fun x => by simpa using (hloc i).2.1.apply_apply_eq_zero x
    rw [hz, uliftLinearMap_zero, ModuleCat.ofHom_zero]
  let S : ShortComplex (CochainComplex (ModuleCat.{max uA (max w (max w' w''))} A) ℕ) :=
    ShortComplex.mk F G hGF
  have hS : S.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact S (fun i =>
      ModuleCat.shortComplex_shortExact _
        (uliftLinearMap_exact (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 i)
          (cechMap (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) i) (hloc i).2.1)
        (uliftLinearMap_injective (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 i) (hloc i).1)
        (uliftLinearMap_surjective (cechMap (A := A) (n := n) ℳ' ℳ'' g
          (fun d => le_of_eq (hgr2 d)) i) (hloc i).2.2))
  -- finiteness transfer
  have hV₁ : Module.Finite A (S.X₁.homology q) ↔
      Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) :=
    chartCechULift_homology_finite.{uA, w, max uA (max w (max w' w''))}
      (A := A) (n := n) (ℳ := ℳ) q
  have hV₂ : Module.Finite A (S.X₂.homology q) ↔
      Module.Finite A ((chartCech (A := A) (n := n) (M := M') ℳ').homology q) :=
    chartCechULift_homology_finite.{uA, w', max uA (max w (max w' w''))}
      (A := A) (n := n) (ℳ := ℳ') q
  have hV₃ : Module.Finite A (S.X₃.homology q) ↔
      Module.Finite A ((chartCech (A := A) (n := n) (M := M'') ℳ'').homology q) :=
    chartCechULift_homology_finite.{uA, w'', max uA (max w (max w' w''))}
      (A := A) (n := n) (ℳ := ℳ'') q
  have hV₁' : Module.Finite A (S.X₁.homology (q + 1)) ↔
      Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology (q + 1)) :=
    chartCechULift_homology_finite.{uA, w, max uA (max w (max w' w''))}
      (A := A) (n := n) (ℳ := ℳ) (q + 1)
  constructor
  · intro hC hE
    haveI : Module.Finite A (S.X₁.homology q) := hV₁.mpr hC
    haveI : Module.Finite A (S.X₃.homology q) := hV₃.mpr hE
    have h2 := hS.homology_exact₂ q
    have hker2 : LinearMap.ker (HomologicalComplex.homologyMap S.g q).hom =
        LinearMap.range (HomologicalComplex.homologyMap S.f q).hom :=
      (ShortComplex.Exact.moduleCat_range_eq_ker h2).symm
    exact hV₂.mp (module_finite_middle_of_exact (HomologicalComplex.homologyMap S.f q).hom
      (HomologicalComplex.homologyMap S.g q).hom (LinearMap.exact_iff.mpr hker2))
  · intro hD hC
    haveI : Module.Finite A (S.X₂.homology q) := hV₂.mpr hD
    haveI : Module.Finite A (S.X₁.homology (q + 1)) := hV₁'.mpr hC
    have hrel : (ComplexShape.up ℕ).Rel q (q + 1) := by rw [ComplexShape.up_Rel]
    have h3 := hS.homology_exact₃ q (q + 1) hrel
    have hker3 : LinearMap.ker (hS.δ q (q + 1) hrel).hom =
        LinearMap.range (HomologicalComplex.homologyMap S.g q).hom :=
      (ShortComplex.Exact.moduleCat_range_eq_ker h3).symm
    exact hV₃.mp (module_finite_middle_of_exact (HomologicalComplex.homologyMap S.g q).hom
      (hS.δ q (q + 1) hrel).hom (LinearMap.exact_iff.mpr hker3))

theorem homology_finite_of_graded_shortExact {A : Type*} [CommRing A] [IsNoetherianRing A]
    {n : ℕ} {M M' M'' : Type*}
    [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    [AddCommGroup M'] [Module A M'] [Module (Poly A n) M'] [IsScalarTower A (Poly A n) M']
    [AddCommGroup M''] [Module A M''] [Module (Poly A n) M''] [IsScalarTower A (Poly A n) M'']
    {ℳ : ℕ → Submodule A M} {ℳ' : ℕ → Submodule A M'} {ℳ'' : ℕ → Submodule A M''}
    [SetLike.GradedSMul (homSub A n) ℳ] [SetLike.GradedSMul (homSub A n) ℳ']
    [SetLike.GradedSMul (homSub A n) ℳ'']
    (f : M →ₗ[Poly A n] M') (g : M' →ₗ[Poly A n] M'')
    (hinj : Function.Injective f) (hex : Function.Exact f g)
    (hgr1 : ∀ d, Submodule.map (f.restrictScalars A) (ℳ d) ≤ ℳ' d)
    (hgr2 : ∀ d, Submodule.map (g.restrictScalars A) (ℳ' d) = ℳ'' d)
    (hker : ∀ d, ℳ' d ⊓ LinearMap.ker (g.restrictScalars A) ≤
      Submodule.map (f.restrictScalars A) (ℳ d))
    (q : ℕ) :
    (Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) →
      Module.Finite A ((chartCech (A := A) (n := n) (M := M'') ℳ'').homology q) →
      Module.Finite A ((chartCech (A := A) (n := n) (M := M') ℳ').homology q)) ∧
    (Module.Finite A ((chartCech (A := A) (n := n) (M := M') ℳ').homology q) →
      Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology (q + 1)) →
      Module.Finite A ((chartCech (A := A) (n := n) (M := M'') ℳ'').homology q)) :=
  homology_finite_of_graded_shortExact_aux f g hinj hex hgr1 hgr2 hker q

end Work.DSCOH
