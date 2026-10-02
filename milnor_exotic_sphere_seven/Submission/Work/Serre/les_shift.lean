import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shifting an exact sequence of `ℚ`-modules (Serre's LES bookkeeping)

If `M --F--> P --G--> Q --δ--> M[+1]` is a long exact sequence of `ℚ`-modules indexed by `ℕ`
(exactness at every spot is expressed by the three hypotheses `e₁`, `e₂`, `e₃`), then it stays
exact after shifting the whole sequence by any `n : ℕ`.

The only content is *bookkeeping with casts*: the shifted differential at spot `k` is

`δ (k + n) ≫ eqToHom (congrArg M h)`,  `h : k + n + 1 = (k + 1) + n`,

i.e. `δ` followed by the transport of the index.  The transport is an isomorphism of `ℚ`-modules
(it is the `eqToHom` of an equality of objects of `ModuleCat ℚ`), and both `range` and `ker`
behave well under it: taking the kernel of a composite with an injective map is the kernel of the
first map, and the transport of `ker (F a)` along the cast is `ker (F b)`.

The helper lemmas below make this explicit.  Note `hom_eqToHom_comp_self` and its mirror: the
underlying linear map of `eqToHom (congrArg N h)` has inverse `eqToHom (congrArg N h.symm)`.
-/

namespace Work.Serre

open CategoryTheory

/-- `hom (eqToHom h.symm)` is a left inverse of `hom (eqToHom h)`: the underlying linear map of a
cast of objects of `ModuleCat ℚ` has inverse the underlying linear map of the reverse cast. -/
lemma les_shift_hom_eqToHom_comp_self {N : ℕ → ModuleCat ℚ} {a b : ℕ} (h : a = b) :
    (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h.symm))).comp
      (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h))) = LinearMap.id := by
  have hm : CategoryTheory.eqToHom (congrArg N h) ≫ CategoryTheory.eqToHom (congrArg N h.symm)
      = 𝟙 (N a) := by
    cases h
    simp
  have h2 := congrArg (fun (m : N a ⟶ N a) => ModuleCat.Hom.hom m) hm
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
  exact h2

/-- The mirror of `les_shift_hom_eqToHom_comp_self`. -/
lemma les_shift_hom_eqToHom_comp_self' {N : ℕ → ModuleCat ℚ} {a b : ℕ} (h : a = b) :
    (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h))).comp
      (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h.symm))) = LinearMap.id := by
  have hm : CategoryTheory.eqToHom (congrArg N h.symm) ≫ CategoryTheory.eqToHom (congrArg N h)
      = 𝟙 (N b) := by
    cases h
    simp
  have h2 := congrArg (fun (m : N b ⟶ N b) => ModuleCat.Hom.hom m) hm
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
  exact h2

/-- The underlying linear map of a cast of objects of `ModuleCat ℚ` is injective. -/
lemma les_shift_injective_hom_eqToHom {N : ℕ → ModuleCat ℚ} {a b : ℕ} (h : a = b) :
    Function.Injective (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h))) := by
  have hleft : Function.LeftInverse
      (fun x => ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h.symm)) x)
      (fun x => ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h)) x) := by
    intro x
    have h2 := congrArg (fun (l : ↥(N a) →ₗ[ℚ] ↥(N a)) => l x) (les_shift_hom_eqToHom_comp_self h)
    simpa using h2
  exact hleft.injective

/-- The kernel of the underlying linear map of a cast of objects of `ModuleCat ℚ` is zero. -/
lemma les_shift_ker_hom_eqToHom {N : ℕ → ModuleCat ℚ} {a b : ℕ} (h : a = b) :
    LinearMap.ker (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h))) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (les_shift_injective_hom_eqToHom h)

/-- **Transport of a family of morphisms along an index equality.**  A family
`F : ∀ k, N k ⟶ P k` is a dependent family, so the morphism `F b` is the conjugate of `F a` by the
casts along `h`. -/
lemma les_shift_transport_F {N P : ℕ → ModuleCat ℚ} (F : ∀ k, N k ⟶ P k) {a b : ℕ} (h : a = b) :
    F b = CategoryTheory.eqToHom (congrArg N h.symm) ≫ F a ≫ CategoryTheory.eqToHom (congrArg P h) := by
  cases h
  simp

/-- Underlying linear maps of `les_shift_transport_F`. -/
lemma les_shift_hom_transport_F {N P : ℕ → ModuleCat ℚ} (F : ∀ k, N k ⟶ P k) {a b : ℕ}
    (h : a = b) :
    ModuleCat.Hom.hom (F b)
      = (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg P h))).comp
          ((ModuleCat.Hom.hom (F a)).comp
            (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h.symm)))) := by
  rw [les_shift_transport_F F h, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]

/-- For mutually inverse linear maps `f` and `g`, the image of a submodule under `f` is the
preimage under `g`.  (Both `f` and `g` are bijections in the application, but only the two
composite identities are used.) -/
lemma les_shift_sub_map_eq_comap {X Y : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup Y]
    [Module ℚ Y] (f : X →ₗ[ℚ] Y) (g : Y →ₗ[ℚ] X) (hgf : g.comp f = LinearMap.id)
    (hfg : f.comp g = LinearMap.id) (S : Submodule ℚ X) : S.map f = S.comap g := by
  ext y
  rw [Submodule.mem_map, Submodule.mem_comap]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : g (f x) = x := by
      have := congrArg (fun (l : X →ₗ[ℚ] X) => l x) hgf
      simpa using this
    rw [h1]; exact hx
  · intro hy
    refine ⟨g y, hy, ?_⟩
    have := congrArg (fun (l : Y →ₗ[ℚ] Y) => l y) hfg
    simpa using this

/-- **Transport of a kernel along an index equality**: the kernel of `F b` is the image of the
kernel of `F a` under the cast. -/
lemma les_shift_ker_transport {N P : ℕ → ModuleCat ℚ} {a b : ℕ} (h : a = b)
    (F : ∀ k, N k ⟶ P k) :
    LinearMap.ker (ModuleCat.Hom.hom (F b))
      = (LinearMap.ker (ModuleCat.Hom.hom (F a))).map
          (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h))) := by
  rw [les_shift_hom_transport_F F h, LinearMap.ker_comp, les_shift_ker_hom_eqToHom h,
    Submodule.comap_bot, LinearMap.ker_comp,
    les_shift_sub_map_eq_comap (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h)))
        (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg N h.symm)))
        (les_shift_hom_eqToHom_comp_self h) (les_shift_hom_eqToHom_comp_self' h)]

theorem les_shift {M P Q : ℕ → ModuleCat ℚ} (n : ℕ)
    (F : ∀ k, M k ⟶ P k) (G : ∀ k, P k ⟶ Q k) (δ : ∀ k, Q k ⟶ M (k + 1))
    (e₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F k)) = LinearMap.ker (ModuleCat.Hom.hom (G k)))
    (e₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G k)) = LinearMap.ker (ModuleCat.Hom.hom (δ k)))
    (e₃ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ k)) = LinearMap.ker (ModuleCat.Hom.hom (F (k + 1)))) :
    (∀ k, LinearMap.range (ModuleCat.Hom.hom (F (k + n)))
        = LinearMap.ker (ModuleCat.Hom.hom (G (k + n)))) ∧
      (∀ k, LinearMap.range (ModuleCat.Hom.hom (G (k + n)))
        = LinearMap.ker (ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp (δ (k + n))
            (CategoryTheory.eqToHom (congrArg M (by omega : k + n + 1 = (k + 1) + n)))))) ∧
      (∀ k, LinearMap.range (ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp (δ (k + n))
            (CategoryTheory.eqToHom (congrArg M (by omega : k + n + 1 = (k + 1) + n)))))
        = LinearMap.ker (ModuleCat.Hom.hom (F ((k + 1) + n)))) := by
  refine ⟨fun k => e₁ (k + n), ?_, ?_⟩
  · -- exactness at `Q (k+n)`, transported along the index equality
    intro k
    have h : k + n + 1 = (k + 1) + n := by omega
    show LinearMap.range (ModuleCat.Hom.hom (G (k + n))) = LinearMap.ker (ModuleCat.Hom.hom
      (CategoryTheory.CategoryStruct.comp (δ (k + n)) (CategoryTheory.eqToHom (congrArg M h))))
    rw [ModuleCat.hom_comp, LinearMap.ker_comp, les_shift_ker_hom_eqToHom h, Submodule.comap_bot]
    exact e₂ (k + n)
  · -- exactness at `M ((k+1)+n)`: `range (δ ≫ eqToHom) = (range δ).map eqToHom`
    intro k
    have h : k + n + 1 = (k + 1) + n := by omega
    show LinearMap.range (ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp (δ (k + n))
      (CategoryTheory.eqToHom (congrArg M h)))) = LinearMap.ker (ModuleCat.Hom.hom (F ((k + 1) + n)))
    rw [ModuleCat.hom_comp, LinearMap.range_comp, les_shift_ker_transport h F, e₃ (k + n)]

end Work.Serre
