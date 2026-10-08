import Mathlib
import Submission.Work.Clifford.Orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.ResSetup`: restriction of a `G`-representation to a normal subgroup

Fix a finite group `G`, a normal subgroup `N ⊴ G`, and an object `V : FDRep ℂ G`.
Writing `ρ = V.ρ`, the module `Work.Clifford.ResMod N V` is `V` equipped with the
`ℂ[N]`-module structure obtained by restricting `ρ` along `N ↪ G`
(a type synonym for `Representation.asModule (ρ.comp N.subtype)`).

The main construction is `Work.Clifford.conjSub`: for `g : G` and a `ℂ[N]`-submodule
`W ≤ ResMod N V`, the image `ρ g '' W` is again a `ℂ[N]`-submodule.  Conjugation by `g`
is an order isomorphism of the lattice of `ℂ[N]`-submodules of `ResMod N V`, which is used
to show that `G` permutes the isotypic components of `ResMod N V`.
-/

noncomputable section

open Classical
open scoped MonoidAlgebra

namespace Work.Clifford

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The `ℂ[N]`-module obtained from `V : FDRep ℂ G` by restricting along `N ≤ G`. -/
abbrev ResMod (N : Subgroup G) (V : FDRep ℂ G) : Type _ :=
  Representation.asModule ((V.ρ.comp N.subtype) : Representation ℂ N V)

instance instResMod (N : Subgroup G) (V : FDRep ℂ G) : Module ℂ[N] (ResMod N V) :=
  inferInstance

/-- The action of `g : G` on `ResMod N V`, as a `ℂ`-linear map. -/
abbrev resAct (N : Subgroup G) (V : FDRep ℂ G) (g : G) : ResMod N V →ₗ[ℂ] ResMod N V := V.ρ g

theorem resAct_apply (N : Subgroup G) (V : FDRep ℂ G) (g : G) (x : ResMod N V) :
    resAct N V g x = V.ρ g x := rfl

/-- `resAct` is compatible with the product in `G`. -/
theorem resAct_mul (N : Subgroup G) (V : FDRep ℂ G) (g h : G) (x : ResMod N V) :
    resAct N V g (resAct N V h x) = resAct N V (g * h) x := by
  have h1 : resAct N V (g * h) = resAct N V g * resAct N V h := map_mul V.ρ g h
  rw [h1]
  rfl

theorem resAct_one (N : Subgroup G) (V : FDRep ℂ G) (x : ResMod N V) :
    resAct N V 1 x = x := by
  rw [resAct_apply, map_one]
  rfl

theorem resAct_inv (N : Subgroup G) (V : FDRep ℂ G) (g : G) (x : ResMod N V) :
    resAct N V g⁻¹ (resAct N V g x) = x := by
  rw [resAct_mul, inv_mul_cancel, resAct_one]

theorem resAct_injective (N : Subgroup G) (V : FDRep ℂ G) (g : G) :
    Function.Injective (resAct N V g) := by
  intro a b hab
  have h := congrArg (resAct N V g⁻¹) hab
  rwa [resAct_inv, resAct_inv] at h

variable {N : Subgroup G} [hN : N.Normal]

/-- Conjugation by `g : G` as a monoid homomorphism `N →* N`. -/
def conjHomHom (g : G) : N →* N where
  toFun n := ⟨g⁻¹ * (n : G) * g, by simpa only [inv_inv] using hN.conj_mem (n : G) n.2 g⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_mk]; group)

@[simp]
theorem conjHomHom_apply (g : G) (n : N) :
    ((conjHomHom (N := N) g n : N) : G) = g⁻¹ * (n : G) * g := rfl

/-- The algebra automorphism of `ℂ[N]` induced by conjugation by `g : G`. -/
def conjAlg (g : G) : ℂ[N] →ₐ[ℂ] ℂ[N] :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (conjHomHom (N := N) g)

@[simp]
theorem conjAlg_of (g : G) (n : N) :
    conjAlg (N := N) g (MonoidAlgebra.of ℂ N n) =
      MonoidAlgebra.of ℂ N (conjHomHom (N := N) g n) := by
  simp [conjAlg, MonoidAlgebra.of_apply]

theorem conjAlg_single (g : G) (n : N) (a : ℂ) :
    conjAlg (N := N) g (MonoidAlgebra.single n a) =
      MonoidAlgebra.single (conjHomHom (N := N) g n) a := by
  rw [conjAlg, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]

/-- The `ℂ[N]`-action on a single group element. -/
theorem single_smul (V : FDRep ℂ G) (n : N) (a : ℂ) (x : ResMod N V) :
    MonoidAlgebra.single n a • x = a • resAct N V n x :=
  Representation.single_smul ((V.ρ.comp N.subtype) : Representation ℂ N V) a n x

theorem of_smul (V : FDRep ℂ G) (n : N) (x : ResMod N V) :
    (MonoidAlgebra.of ℂ N n) • x = resAct N V n x := by
  rw [MonoidAlgebra.of_apply, single_smul, one_smul]

/-- Conjugation by `g` intertwines the `ℂ[N]`-action with the action of `resAct V g`. -/
theorem conjAlg_smul_resAct (V : FDRep ℂ G) (g : G) (c : ℂ[N]) (x : ResMod N V) :
    c • (resAct N V g x) = resAct N V g (conjAlg (N := N) g c • x) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, zero_smul, zero_smul, map_zero]
  | add c₁ c₂ h₁ h₂ => rw [add_smul, map_add, add_smul, map_add, ← h₁, ← h₂]
  | single n a =>
      rw [conjAlg_single, single_smul, single_smul, map_smul, resAct_mul, resAct_mul,
        conjHomHom_apply, show g * (g⁻¹ * (n : G) * g) = (n : G) * g from by group]

/-! ### The image of a submodule under conjugation -/

/-- For `g : G` and a `ℂ[N]`-submodule `W` of `ResMod N V`, the image `ρ g '' W`, viewed as a
`ℂ[N]`-submodule. -/
def conjSub (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V)) :
    Submodule ℂ[N] (ResMod N V) where
  carrier := resAct N V g '' (W : Set (ResMod N V))
  zero_mem' := ⟨0, W.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, W.add_mem ha hb, by simp⟩
  smul_mem' := by
    intro c x hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨conjAlg (N := N) g c • w, W.smul_mem _ hw,
      (conjAlg_smul_resAct (N := N) V g c w).symm⟩

@[simp]
theorem mem_conjSub (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V))
    (x : ResMod N V) :
    x ∈ conjSub (N := N) V g W ↔ ∃ w ∈ W, resAct N V g w = x := Iff.rfl

theorem conjSub_apply_mem (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V))
    {w : ResMod N V} (hw : w ∈ W) : resAct N V g w ∈ conjSub (N := N) V g W :=
  ⟨w, hw, rfl⟩

theorem conjSub_one (V : FDRep ℂ G) (W : Submodule ℂ[N] (ResMod N V)) :
    conjSub (N := N) V 1 W = W := by
  ext x
  rw [mem_conjSub]
  constructor
  · rintro ⟨w, hw, h⟩
    rw [resAct_one N V w] at h
    exact h ▸ hw
  · intro hx
    exact ⟨x, hx, resAct_one N V x⟩

theorem conjSub_mul (V : FDRep ℂ G) (g h : G) (W : Submodule ℂ[N] (ResMod N V)) :
    conjSub (N := N) V g (conjSub (N := N) V h W) = conjSub (N := N) V (g * h) W := by
  ext x
  simp only [mem_conjSub]
  constructor
  · rintro ⟨y, ⟨w, hw, hy⟩, hx⟩
    exact ⟨w, hw, by rw [← hx, ← hy, resAct_mul]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨resAct N V h w, ⟨w, hw, rfl⟩, resAct_mul N V g h w⟩

theorem conjSub_inv_left (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V)) :
    conjSub (N := N) V g⁻¹ (conjSub (N := N) V g W) = W := by
  rw [conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_inv_right (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V)) :
    conjSub (N := N) V g (conjSub (N := N) V g⁻¹ W) = W := by
  rw [conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_le_conjSub_iff (V : FDRep ℂ G) (g : G) {W₁ W₂ : Submodule ℂ[N] (ResMod N V)} :
    conjSub (N := N) V g W₁ ≤ conjSub (N := N) V g W₂ ↔ W₁ ≤ W₂ := by
  constructor
  · intro h x hx
    have h' : resAct N V g x ∈ conjSub (N := N) V g W₂ :=
      h (conjSub_apply_mem (N := N) V g W₁ hx)
    obtain ⟨y, hy, hyx⟩ := h'
    have hyx' : y = x := resAct_injective N V g hyx
    rwa [hyx'] at hy
  · intro h x hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact conjSub_apply_mem (N := N) V g W₂ (h hw)

theorem conjSub_mono (V : FDRep ℂ G) (g : G) {W₁ W₂ : Submodule ℂ[N] (ResMod N V)}
    (h : W₁ ≤ W₂) : conjSub (N := N) V g W₁ ≤ conjSub (N := N) V g W₂ :=
  (conjSub_le_conjSub_iff (N := N) V g).mpr h

theorem conjSub_bot (V : FDRep ℂ G) (g : G) :
    conjSub (N := N) V g (⊥ : Submodule ℂ[N] (ResMod N V)) = ⊥ := by
  ext x
  rw [mem_conjSub, Submodule.mem_bot]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Submodule.mem_bot] at hw
    rw [hw, map_zero]
  · intro h
    exact ⟨0, by simp, by rw [h, map_zero]⟩

theorem conjSub_top (V : FDRep ℂ G) (g : G) :
    conjSub (N := N) V g (⊤ : Submodule ℂ[N] (ResMod N V)) = ⊤ := by
  ext x
  rw [mem_conjSub]
  exact ⟨fun _ => Submodule.mem_top, fun _ =>
    ⟨resAct N V g⁻¹ x, Submodule.mem_top, by rw [resAct_mul, mul_inv_cancel, resAct_one]⟩⟩

/-! ### The action of `N` on a `ℂ[N]`-submodule -/

/-- The action of `n` on a `ℂ[N]`-submodule `W`, as an endomorphism of `W`.
(Every `ℂ[N]`-submodule is stable under the action of every `n : N`.) -/
def subAct (V : FDRep ℂ G) (W : Submodule ℂ[N] (ResMod N V)) (n : N) : W →ₗ[ℂ] W where
  toFun x := ⟨resAct N V n (x : ResMod N V), by
    have h : (MonoidAlgebra.of ℂ N n) • (x : ResMod N V) ∈ W := W.smul_mem _ x.2
    rwa [of_smul] at h⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' a x := Subtype.ext (by simp)

theorem subAct_apply (V : FDRep ℂ G) (W : Submodule ℂ[N] (ResMod N V)) (n : N)
    (x : W) : ((subAct V W n x : W) : ResMod N V) = resAct N V n x := rfl

/-- The character of a `ℂ[N]`-submodule `W` of `ResMod N V`: the trace of the action of `n` on
`W`. -/
def subChar (V : FDRep ℂ G) (W : Submodule ℂ[N] (ResMod N V)) (n : N) : ℂ :=
  LinearMap.trace ℂ W (subAct V W n)

theorem subChar_apply (V : FDRep ℂ G) (W : Submodule ℂ[N] (ResMod N V)) (n : N) :
    subChar V W n = LinearMap.trace ℂ W (subAct V W n) := rfl

/-! ### `conjSub` as an order isomorphism, and finiteness of the restricted module -/

theorem conjSub_iSup_le (V : FDRep ℂ G) (g : G) {ι : Type*}
    (W : ι → Submodule ℂ[N] (ResMod N V)) :
    (⨆ i, conjSub V g (W i)) ≤ conjSub V g (⨆ i, W i) :=
  iSup_le fun i => conjSub_mono V g (le_iSup W i)

theorem conjSub_eq_bot_iff (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V)) :
    conjSub V g W = ⊥ ↔ W = ⊥ :=
  ⟨fun h => by
      have h2 := congrArg (conjSub V g⁻¹) h
      rwa [conjSub_inv_left, conjSub_bot] at h2,
    fun h => by rw [h, conjSub_bot]⟩

theorem isSimpleModule_conjSub_iff (V : FDRep ℂ G) (g : G)
    (W : Submodule ℂ[N] (ResMod N V)) :
    IsSimpleModule ℂ[N] ↥(conjSub V g W) ↔ IsSimpleModule ℂ[N] ↥W := by
  rw [isSimpleModule_iff_isAtom, isSimpleModule_iff_isAtom]
  constructor
  · rintro ⟨hne, hmin⟩
    refine ⟨fun h => hne ((conjSub_eq_bot_iff V g W).mpr h), fun b hb => ?_⟩
    have h1 : conjSub V g b < conjSub V g W := by
      refine lt_of_le_of_ne ((conjSub_le_conjSub_iff V g).mpr hb.le) fun hEq => ?_
      have h2 : b = W := by
        have h3 := congrArg (conjSub V g⁻¹) hEq
        rwa [conjSub_inv_left, conjSub_inv_left] at h3
      exact hb.ne h2
    have h2 := hmin (conjSub V g b) h1
    have h3 : b = conjSub V g⁻¹ ⊥ := by
      have h4 := congrArg (conjSub V g⁻¹) h2
      rwa [conjSub_inv_left] at h4
    rwa [conjSub_bot] at h3
  · rintro ⟨hne, hmin⟩
    refine ⟨fun h => hne ((conjSub_eq_bot_iff V g W).mp h), fun b hb => ?_⟩
    have h1a : conjSub V g⁻¹ b ≤ W := by
      have h := (conjSub_le_conjSub_iff V g⁻¹).mpr hb.le
      rwa [conjSub_inv_left] at h
    have h1 : conjSub V g⁻¹ b < W := by
      refine lt_of_le_of_ne h1a fun hEq => ?_
      have h3 : b = conjSub V g W := by
        have h4 := congrArg (conjSub V g) hEq
        rwa [conjSub_inv_right] at h4
      exact hb.ne h3
    have h2 := hmin (conjSub V g⁻¹ b) h1
    have h3 : b = conjSub V g ⊥ := by
      have h4 := congrArg (conjSub V g) h2
      rwa [conjSub_inv_right] at h4
    rwa [conjSub_bot] at h3

/-! ### Finiteness of `ResMod N V` over the group algebra -/

/-- A module which is finite over a smaller ring is finite over a bigger one. -/
theorem moduleFinite_of_isScalarTower {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite R M] :
    Module.Finite S M := by
  rw [Module.finite_def]
  refine Submodule.FG.of_restrictScalars R ?_
  rw [show (⊤ : Submodule S M).restrictScalars R = ⊤ from rfl]
  exact Module.finite_def.mp (inferInstance : Module.Finite R M)

instance instModuleFiniteResMod (V : FDRep ℂ G) : Module.Finite ℂ[N] (ResMod N V) :=
  moduleFinite_of_isScalarTower (R := ℂ) (S := MonoidAlgebra ℂ ↥N) (M := ResMod N V)

theorem moduleFinite_subtype (V : FDRep ℂ G) (W : Submodule ℂ[N] (ResMod N V)) :
    Module.Finite ℂ[N] ↥W := by
  rw [Module.Finite.iff_fg]
  refine Submodule.FG.of_restrictScalars ℂ (Module.Finite.iff_fg.mp ?_)
  exact Module.Finite.of_injective (Submodule.subtype (W.restrictScalars ℂ))
    (Submodule.subtype_injective _)

theorem iSup_ne_subtype {α β : Type*} [CompleteLattice β] (f : α → β) (i : α) :
    (⨆ (j) (_ : j ≠ i), f j) = ⨆ j : {j // j ≠ i}, f j.1 :=
  (iSup_subtype (p := fun j => j ≠ i) (f := fun j : {j // j ≠ i} => f j.1)).symm

/-- Independence of a family of submodules is inherited by restricting scalars. -/
theorem iSupIndep_restrictScalars {ι : Type*} (V : FDRep ℂ G)
    {p : ι → Submodule ℂ[N] (ResMod N V)} (h : iSupIndep p) :
    iSupIndep fun i => (p i).restrictScalars ℂ := by
  rw [iSupIndep_def] at h ⊢
  intro i
  have h2 := h i
  rw [disjoint_iff] at h2 ⊢
  have h2' : p i ⊓ (⨆ j : {j // j ≠ i}, p j.1) = ⊥ := by
    rw [iSup_ne_subtype (fun j => p j) i] at h2
    exact h2
  have key : (⨆ j : {j // j ≠ i}, (p j.1).restrictScalars ℂ) =
      ((⨆ j : {j // j ≠ i}, p j.1).restrictScalars ℂ) :=
    (Submodule.restrictScalars_iSup (S := ℂ) (fun j : {j // j ≠ i} => p j.1)).symm
  rw [iSup_ne_subtype (fun j => (p j).restrictScalars ℂ) i, key,
    ← Submodule.restrictScalars_inf, h2', Submodule.restrictScalars_bot]

end Work.Clifford
