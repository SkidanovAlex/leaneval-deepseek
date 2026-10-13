import Mathlib
import Submission.Work.DSM5c.Lp.PiHelpers

/-!
# Kernel of a product map with kernels `(r) · ⊤`

For a family of `W`-module maps `pᵢ : Zᵢ ⟶ Z'ᵢ` whose kernels are all the principal multiple
`span {r} · ⊤` of the whole module, the kernel of the categorical product map
`∏ᶜ pᵢ : ∏ᶜ Z ⟶ ∏ᶜ Z'` is again `span {r} · ⊤`
(`Work.DSM5c.Lp.ker_Pi_map_span`).

Unlike `Work.DSM5c.Lp.ker_Pi_map` this version needs **no** finiteness or decidability of the
index type: the point is that a *principal* ideal behaves well on infinite products, because
`span {r} · ⊤ = r · ⊤` is a single scalar action.  Concretely,

* `Work.DSM5c.Lp.span_singleton_smul_top_eq_smul_top` — `span {r} · ⊤ = r · ⊤` on any module;
* `Work.DSM5c.Lp.smul_top_pi_single` — `r · ⊤` of a product of modules is the product of the
  `r · ⊤` of the factors (no finiteness!);
* `Work.DSM5c.Lp.span_singleton_smul_top_pi` — the same for `span {r} · ⊤`;
* `Work.DSM5c.Lp.piIsoPi_proj_comp_gen`, `Work.DSM5c.Lp.pi_map_pi_hom_gen`,
  `Work.DSM5c.Lp.piIsoPi_map_compat_gen` — the compatibility of `ModuleCat.piIsoPi` with
  `Limits.Pi.map` (instance-general restatements of the helpers used for `ker_Pi_map`);
* `Work.DSM5c.Lp.ker_Pi_map_span` — the target.
-/

open CategoryTheory Limits
open scoped Pointwise

namespace Work.DSM5c.Lp

/-! ## `span {r} · ⊤ = r · ⊤` and its behaviour on products -/

/-- A principal multiple of the whole module is a single scalar action: `span {r} · ⊤ = r · ⊤`. -/
lemma span_singleton_smul_top_eq_smul_top {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (r : R) :
    Ideal.span {r} • (⊤ : Submodule R M) = r • (⊤ : Submodule R M) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.smul_le]
    intro a ha n hn
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [mul_smul]
    exact Submodule.smul_mem _ c
      ((Submodule.mem_smul_pointwise_iff_exists (r • n) r ⊤).mpr ⟨n, hn, rfl⟩)
  · intro x hx
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists x r ⊤).mp hx
    rw [← hy]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) Submodule.mem_top

/-- `r · ⊤` of a product of modules is the product of the `r · ⊤` of the factors.  No finiteness
assumption on the index type is needed, in contrast with `Work.DSM5c.Lp.smul_top_pi`. -/
lemma smul_top_pi_single {R : Type*} [CommRing R] {ι : Type*} {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (r : R) :
    r • (⊤ : Submodule R ((i : ι) → M i)) =
      Submodule.pi Set.univ (fun i => r • (⊤ : Submodule R (M i))) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists x r ⊤).mp hx
    rw [Submodule.mem_pi]
    intro i _
    rw [← hy]
    exact (Submodule.mem_smul_pointwise_iff_exists (r • y i) r ⊤).mpr ⟨y i, Submodule.mem_top, rfl⟩
  · intro x hx
    rw [Submodule.mem_pi] at hx
    choose y hy using fun i =>
      (Submodule.mem_smul_pointwise_iff_exists (x i) r ⊤).mp (hx i (Set.mem_univ i))
    refine (Submodule.mem_smul_pointwise_iff_exists x r ⊤).mpr
      ⟨fun i => y i, Submodule.mem_top, ?_⟩
    ext i
    simpa only [Pi.smul_apply] using (hy i).2

/-- `span {r} · ⊤` of a product of modules is the product of the `span {r} · ⊤` of the factors. -/
lemma span_singleton_smul_top_pi {R : Type*} [CommRing R] {ι : Type*} {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (r : R) :
    Ideal.span {r} • (⊤ : Submodule R ((i : ι) → M i)) =
      Submodule.pi Set.univ (fun i => Ideal.span {r} • (⊤ : Submodule R (M i))) := by
  rw [span_singleton_smul_top_eq_smul_top]
  simp only [span_singleton_smul_top_eq_smul_top]
  exact smul_top_pi_single r

/-! ## Compatibility of `ModuleCat.piIsoPi` with `Limits.Pi.map`

These are instance-general restatements of the helpers in `Work.DSM5c.Lp.ker_Pi_map`
(the proofs are unchanged; only the unused `[DecidableEq ι] [Finite ι]` hypotheses are dropped).
Distinct names are used so that importing both files causes no clash. -/

/-- The `i`-th projection of the concrete product, read through `ModuleCat.piIsoPi`, is the
categorical projection `Pi.π`. -/
lemma piIsoPi_proj_comp_gen {W : Type*} [CommRing W] {ι : Type*} (Z : ι → ModuleCat W) (i : ι) :
    (LinearMap.proj (φ := fun i => ↥(Z i)) i).comp ((ModuleCat.piIsoPi Z).hom.hom)
      = (Pi.π Z i).hom := by
  have h := ModuleCat.piIsoPi_hom_ker_subtype Z i
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h2
  exact h2

/-- The `i`-th projection of the categorical product map `Limits.Pi.map p` computes the `i`-th
component. -/
lemma pi_map_pi_hom_gen {W : Type*} [CommRing W] {ι : Type*}
    (Z Z' : ι → ModuleCat W) (p : ∀ i, Z i ⟶ Z' i) (i : ι) :
    ((Pi.π Z' i).hom).comp (CategoryTheory.Limits.Pi.map p).hom =
      (p i).hom.comp (Pi.π Z i).hom := by
  have h := Pi.map_π p i
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
  exact h2

/-- Pointwise form of `piIsoPi_map_compat_gen`. -/
lemma piIsoPi_map_compat_apply_gen {W : Type*} [CommRing W] {ι : Type*}
    (Z Z' : ι → ModuleCat W) (p : ∀ i, Z i ⟶ Z' i)
    (x : ↥(CategoryTheory.Limits.piObj Z)) (i : ι) :
    (((ModuleCat.piIsoPi Z').hom.hom) ((CategoryTheory.Limits.Pi.map p).hom x)) i =
      ((p i).hom) ((((ModuleCat.piIsoPi Z).hom.hom) x) i) := by
  have A : ∀ y : ↥(CategoryTheory.Limits.piObj Z'),
      (((ModuleCat.piIsoPi Z').hom.hom) y) i = (Pi.π Z' i).hom y := by
    intro y
    have h := congrArg (fun g : ↥(CategoryTheory.Limits.piObj Z') →ₗ[W] ↥(Z' i) => g y)
      (piIsoPi_proj_comp_gen Z' i)
    simpa [LinearMap.comp_apply] using h
  have B : ∀ y : ↥(CategoryTheory.Limits.piObj Z),
      (((ModuleCat.piIsoPi Z).hom.hom) y) i = (Pi.π Z i).hom y := by
    intro y
    have h := congrArg (fun g : ↥(CategoryTheory.Limits.piObj Z) →ₗ[W] ↥(Z i) => g y)
      (piIsoPi_proj_comp_gen Z i)
    simpa [LinearMap.comp_apply] using h
  rw [A ((CategoryTheory.Limits.Pi.map p).hom x), B x]
  have h2 := congrArg (fun g : ↥(CategoryTheory.Limits.piObj Z) →ₗ[W] ↥(Z' i) => g x)
    (pi_map_pi_hom_gen Z Z' p i)
  simpa [LinearMap.comp_apply] using h2

/-- `ModuleCat.piIsoPi` intertwines the categorical product map `Limits.Pi.map p` with the
componentwise map `LinearMap.pi (fun i => (p i).hom ∘ₗ proj i)`. -/
lemma piIsoPi_map_compat_gen {W : Type*} [CommRing W] {ι : Type*}
    (Z Z' : ι → ModuleCat W) (p : ∀ i, Z i ⟶ Z' i) :
    ((ModuleCat.piIsoPi Z').hom.hom).comp (CategoryTheory.Limits.Pi.map p).hom =
      (LinearMap.pi (fun i => (p i).hom.comp (LinearMap.proj (φ := fun i => ↥(Z i)) i))).comp
        ((ModuleCat.piIsoPi Z).hom.hom) := by
  apply LinearMap.ext; intro x
  funext i
  simp only [LinearMap.comp_apply, LinearMap.pi_apply]
  exact piIsoPi_map_compat_apply_gen Z Z' p x i

/-! ## Kernels and `I · ⊤` under linear equivalences

Self-contained copies of the two general lemmas used by `Work.DSM5c.Lp.ker_Pi_map`
(kept under distinct names so that importing both files causes no clash). -/

/-- `I · ⊤` pulls back to `I · ⊤` along a linear equivalence. -/
lemma comap_smul_top_equiv_gen {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (I : Ideal R) :
    Submodule.comap (e : M →ₗ[R] N) (I • (⊤ : Submodule R N)) = I • (⊤ : Submodule R M) := by
  have h1 : Submodule.map (e : M →ₗ[R] N) (I • (⊤ : Submodule R M)) =
      I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  rw [← h1, Submodule.comap_map_eq]
  simp

/-- Kernels of maps related by composition with two maps, one of them injective: if `e' ∘ f = g ∘ e`
and `e'` is injective, then `ker f = (ker g).comap e`. -/
lemma ker_eq_comap_ker_gen {R : Type*} [Ring R] {M P N Q : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    (e : M →ₗ[R] P) (e' : N →ₗ[R] Q) (f : M →ₗ[R] N) (g : P →ₗ[R] Q)
    (he' : Function.Injective e') (h : e'.comp f = g.comp e) :
    LinearMap.ker f = (LinearMap.ker g).comap e := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker]
  have key : e' (f x) = g (e x) := by
    have := congrArg (fun k => k x) h
    simpa only [LinearMap.comp_apply] using this
  constructor
  · intro hx; rw [← key, hx, map_zero]
  · intro hx; rw [← key] at hx; exact he' (by rw [hx, map_zero])

/-! ## The target -/

theorem ker_Pi_map_span {W : Type*} [CommRing W] {ι : Type*}
    (Z Z' : ι → ModuleCat W) (p : ∀ i, Z i ⟶ Z' i) (r : W)
    (h : ∀ i, LinearMap.ker (p i).hom = Ideal.span {r} • (⊤ : Submodule W (Z i))) :
    LinearMap.ker ((CategoryTheory.Limits.Pi.map p).hom) =
      Ideal.span {r} • (⊤ : Submodule W ↥(CategoryTheory.Limits.piObj Z)) := by
  have hcompat := piIsoPi_map_compat_gen Z Z' p
  have hg : LinearMap.ker
      (LinearMap.pi (fun i => (p i).hom.comp (LinearMap.proj (φ := fun i => ↥(Z i)) i)))
      = Ideal.span {r} • (⊤ : Submodule W ((i : ι) → ↥(Z i))) := by
    rw [span_singleton_smul_top_pi]
    ext x
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_ker]
    rw [funext_iff]
    simp only [Pi.zero_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    constructor
    · intro hx i; rw [← h i, LinearMap.mem_ker]; exact hx i
    · intro hx i
      have hxi : x i ∈ LinearMap.ker (p i).hom := by rw [h i]; exact hx i
      simpa [LinearMap.mem_ker] using hxi
  have hinj : Function.Injective ((ModuleCat.piIsoPi Z').hom.hom) :=
    (CategoryTheory.Iso.toLinearEquiv (ModuleCat.piIsoPi Z')).injective
  have hker : LinearMap.ker (CategoryTheory.Limits.Pi.map p).hom =
      (LinearMap.ker (LinearMap.pi (fun i => (p i).hom.comp
        (LinearMap.proj (φ := fun i => ↥(Z i)) i)))).comap ((ModuleCat.piIsoPi Z).hom.hom) :=
    ker_eq_comap_ker_gen _ _ _ _ hinj hcompat
  rw [hker, hg]
  exact comap_smul_top_equiv_gen (CategoryTheory.Iso.toLinearEquiv (ModuleCat.piIsoPi Z))
    (Ideal.span {r})

end Work.DSM5c.Lp
