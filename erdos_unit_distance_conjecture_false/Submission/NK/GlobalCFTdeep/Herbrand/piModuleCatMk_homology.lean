import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.PiDefs

/-!
# Homology of the product short complex of `R`-modules

For a family of linear maps `f i : A i → B i`, `g i : B i → D i` with `g i ∘ f i = 0`,
the short complex `piModuleCatMk f g h` is the pointwise product of the short complexes
`ShortComplex.moduleCatMk (f i) (g i) (h i)`.  In this file we show that its homology is
the product of the homologies of the factors.

The proof is a concrete computation, in linear algebra, of both sides:
the homology of a short complex of modules is `ker g ⧸ im f` (up to the canonical
isomorphism `ShortComplex.moduleCatHomologyIso`), and for a product this is
`(∏ ker (g i)) ⧸ (∏ im (f i)) ≅ ∏ (ker (g i) ⧸ im (f i))`.
The comparison linear equivalence `piQuotientEquiv` below is the heart of the argument;
it is produced by the first isomorphism theorem from the evident componentwise map
`∏ ker (g i) → ∏ (ker (g i) ⧸ im (f i))`.
-/

set_option maxHeartbeats 1000000

namespace NK.GlobalCFTdeep.Herbrand

open CategoryTheory CategoryTheory.Limits

/-- The homology of a short complex of `k`-modules, computed as
`ker g ⧸ im (f : X₁ → ker g)`. -/
private lemma shortComplex_H_iso_aux {k : Type*} [Ring k] (S : ShortComplex (ModuleCat k)) :
    Nonempty (S.moduleCatLeftHomologyData.H ≃ₗ[k]
      (LinearMap.ker S.g.hom ⧸ (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype)) := by
  have h : LinearMap.range S.moduleCatToCycles
      = (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype :=
    LinearMap.range_codRestrict _ _ _
  exact ⟨Submodule.quotEquivOfEq _ _ h⟩

/-- **Quotients commute with products.**  For a family of linear maps `f i : A i → B i`
and `g i : B i → D i` with `g i ∘ f i = 0`, the quotient of the product of the kernels
`ker (g i)` by the product of the images `im (f i)` is the product of the quotients
`ker (g i) ⧸ im (f i)`. -/
private noncomputable def piQuotientEquiv {R : Type*} [Ring R] {ι : Type}
    {A B D : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]
    (f : ∀ i, A i →ₗ[R] B i) (g : ∀ i, B i →ₗ[R] D i) (_h : ∀ i, g i ∘ₗ f i = 0) :
    (LinearMap.ker (LinearMap.piMap g) ⧸
        (LinearMap.range (LinearMap.piMap f)).comap (LinearMap.ker (LinearMap.piMap g)).subtype) ≃ₗ[R]
      ((i : ι) → ↥(LinearMap.ker (g i)) ⧸ (LinearMap.range (f i)).comap (LinearMap.ker (g i)).subtype) := by
  classical
  let ri : (i : ι) → Submodule R ↥(LinearMap.ker (g i)) :=
    fun i => (LinearMap.range (f i)).comap (LinearMap.ker (g i)).subtype
  let psi : LinearMap.ker (LinearMap.piMap g) →ₗ[R] ((i : ι) → ↥(LinearMap.ker (g i))) :=
    { toFun := fun x i => ⟨x.1 i, by
        rw [LinearMap.mem_ker]
        have h1 : LinearMap.piMap g x.1 i = 0 := congr_fun (LinearMap.mem_ker.mp x.2) i
        simpa only [LinearMap.piMap, LinearMap.pi_apply, LinearMap.comp_apply,
          LinearMap.proj_apply] using h1⟩
      map_add' := by intro x y; ext i; rfl
      map_smul' := by intro c x; ext i; rfl }
  have psi_apply : ∀ (x : LinearMap.ker (LinearMap.piMap g)) (i : ι), (psi x i : B i) = x.1 i :=
    fun x i => rfl
  have hkerpi : LinearMap.ker (LinearMap.piMap (fun i => (ri i).mkQ)) = Submodule.pi Set.univ ri := by
    rw [LinearMap.ker_piMap]
    simp [Submodule.ker_mkQ]
  let Φ : LinearMap.ker (LinearMap.piMap g) →ₗ[R] ((i : ι) → ↥(LinearMap.ker (g i)) ⧸ ri i) :=
    (LinearMap.piMap fun i => (ri i).mkQ).comp psi
  have hker : Φ.ker =
      (LinearMap.range (LinearMap.piMap f)).comap (LinearMap.ker (LinearMap.piMap g)).subtype := by
    show ((LinearMap.piMap fun i => (ri i).mkQ).comp psi).ker = _
    rw [LinearMap.ker_comp]
    conv_lhs => rw [hkerpi]
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_imp_iff,
      LinearMap.mem_range]
    constructor
    · intro hx
      choose a ha using hx
      refine ⟨a, funext fun i => ?_⟩
      exact (ha i).trans (psi_apply x i)
    · rintro ⟨a, ha⟩ i
      exact ⟨a i, congr_fun ha i⟩
  have hsurj : Function.Surjective Φ := by
    intro z
    choose w hw using fun i => Submodule.mkQ_surjective (ri i) (z i)
    refine ⟨⟨fun i => (w i : B i), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]
      funext i
      show g i (w i : B i) = 0
      exact (LinearMap.mem_ker.mp (w i).2)
    · funext i
      show (ri i).mkQ ⟨(w i : B i), _⟩ = z i
      rw [show (⟨(w i : B i), _⟩ : ↥(LinearMap.ker (g i))) = w i from Subtype.ext rfl]
      exact hw i
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)

theorem piModuleCatMk_homology {R : Type*} [Ring R] {ι : Type}
    {A B D : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]
    (f : ∀ i, A i →ₗ[R] B i) (g : ∀ i, B i →ₗ[R] D i) (h : ∀ i, g i ∘ₗ f i = 0) :
    Nonempty ((NK.GlobalCFTdeep.Herbrand.piModuleCatMk f g h).homology ≅
      ∏ᶜ (fun i => (CategoryTheory.ShortComplex.moduleCatMk (f i) (g i) (h i)).homology)) := by
  classical
  obtain ⟨eH⟩ := shortComplex_H_iso_aux (piModuleCatMk f g h)
  have perFactor : ∀ i, ↥((ShortComplex.moduleCatMk (f i) (g i) (h i)).homology) ≃ₗ[R]
      (↥(LinearMap.ker (g i)) ⧸ (LinearMap.range (f i)).comap (LinearMap.ker (g i)).subtype) :=
    fun i =>
      ((ShortComplex.moduleCatHomologyIso (ShortComplex.moduleCatMk (f i) (g i) (h i))).toLinearEquiv).trans
        (shortComplex_H_iso_aux (ShortComplex.moduleCatMk (f i) (g i) (h i))).some
  have hall : ↥((piModuleCatMk f g h).homology) ≃ₗ[R]
      ((i : ι) → ↥((ShortComplex.moduleCatMk (f i) (g i) (h i)).homology)) :=
    ((ShortComplex.moduleCatHomologyIso (piModuleCatMk f g h)).toLinearEquiv.trans eH).trans
      ((piQuotientEquiv f g h).trans (LinearEquiv.piCongrRight perFactor).symm)
  exact ⟨hall.toModuleIso ≪≫
    (ModuleCat.piIsoPi (fun i => (ShortComplex.moduleCatMk (f i) (g i) (h i)).homology)).symm⟩

end NK.GlobalCFTdeep.Herbrand
