import Mathlib
import Submission.Work.ThmF.Prove.S3.clifford_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Conjugation of `F[K]`-submodules by an element of `L`

Fix a group `L`, a normal subgroup `K ⊴ L`, a field `F` and a representation `ρ : Representation F L V`.
The restriction of `ρ` to `K` makes `V` (i.e. `(resRep ρ).asModule`) an `F[K]`-module.  For `e : L`
the conjugation action `conjMod hKn ρ e` on the lattice of `F[K]`-submodules (defined in
`Work.ThmF.Prove.S3.clifford_dichotomy`) is an order isomorphism.

This file shows that `conjMod hKn ρ e` maps the `S`-isotypic component to the
`conjMod hKn ρ e S`-isotypic component, mirroring the `ℂ[N]`-theory of `Work.Clifford`.

The group element `e` acts on `(resRep ρ).asModule` by the `F`-linear bijection `ρ e`.  It is not
`F[K]`-linear, but it intertwines the `F[K]`-action with its twist by the algebra automorphism
`conjAlg hKn e` (`conjAlg_smul_resAct`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped MonoidAlgebra
open Classical

namespace Work.ThmF.Prove.S3

variable {L : Type*} [Group L] {F : Type*} [Field F] {K : Subgroup L} {V : Type*}
  [AddCommGroup V] [Module F V]

/-- The type of `F[K]`-submodules of `(resRep ρ).asModule`. -/
abbrev SubM (ρ : Representation F L V) : Type _ :=
  Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule

/-- The `F`-linear action of `e : L` on `(resRep ρ).asModule`. -/
abbrev act (ρ : Representation F L V) (e : L) :
    (resRep (K := K) ρ).asModule →ₗ[F] (resRep (K := K) ρ).asModule := ρ e

/-! ## The conjugation algebra automorphism of `F[K]` -/

/-- Conjugation by `e : L` as a monoid homomorphism `K →* K`. -/
def conjHom (hKn : K.Normal) (e : L) : K →* K where
  toFun k := ⟨e⁻¹ * (k : L) * e, by
    simpa only [inv_inv] using hKn.conj_mem (k : L) k.2 e⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp] theorem conjHom_apply (hKn : K.Normal) (e : L) (k : K) :
    ((conjHom hKn e k : K) : L) = e⁻¹ * (k : L) * e := rfl

/-- The algebra automorphism of `F[K]` induced by conjugation by `e : L`. -/
def conjAlg (hKn : K.Normal) (e : L) : MonoidAlgebra F K →ₐ[F] MonoidAlgebra F K :=
  MonoidAlgebra.mapDomainAlgHom F F (conjHom hKn e)

theorem conjAlg_single (hKn : K.Normal) (e : L) (k : K) (a : F) :
    conjAlg hKn e (MonoidAlgebra.single k a) =
      MonoidAlgebra.single (conjHom hKn e k) a := by
  rw [conjAlg, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]

/-! ## Elementary facts about the action of `L` -/

theorem act_mul_apply (ρ : Representation F L V) (a b : L)
    (x : (resRep (K := K) ρ).asModule) : act ρ a (act ρ b x) = act ρ (a * b) x := by
  rw [show act ρ a (act ρ b x) = ρ a (ρ b x) from rfl,
      show act ρ (a * b) x = ρ (a * b) x from rfl,
      ← Module.End.mul_apply, ← map_mul]

theorem act_one (ρ : Representation F L V) (x : (resRep (K := K) ρ).asModule) :
    act ρ (1 : L) x = x := by
  rw [show act ρ (1 : L) x = ρ (1 : L) x from rfl, map_one]
  rfl

theorem act_inv_comp (ρ : Representation F L V) (e : L)
    (x : (resRep (K := K) ρ).asModule) : act ρ e⁻¹ (act ρ e x) = x := by
  rw [act_mul_apply, inv_mul_cancel, act_one]

theorem act_comp_inv (ρ : Representation F L V) (e : L)
    (x : (resRep (K := K) ρ).asModule) : act ρ e (act ρ e⁻¹ x) = x := by
  rw [act_mul_apply, mul_inv_cancel, act_one]

theorem act_injective (ρ : Representation F L V) (e : L) :
    Function.Injective (act (K := K) ρ e) := by
  intro a b hab
  have h := congrArg (act (K := K) ρ e⁻¹) hab
  rwa [act_inv_comp, act_inv_comp] at h

/-- A single group-algebra element acts through the representation. -/
theorem single_smul' (ρ : Representation F L V) (k : K) (a : F)
    (x : (resRep (K := K) ρ).asModule) :
    MonoidAlgebra.single k a • x = a • act ρ k x := by
  rw [show MonoidAlgebra.single k a • x = (Representation.asAlgebraHom (resRep (K := K) ρ)
    (MonoidAlgebra.single k a)) x from rfl, Representation.asAlgebraHom_single]
  rfl

theorem of_smul' (ρ : Representation F L V) (k : K)
    (x : (resRep (K := K) ρ).asModule) :
    (MonoidAlgebra.of F K k) • x = act ρ k x := by
  rw [MonoidAlgebra.of_apply, single_smul', one_smul]

/-- Conjugation by `e` intertwines the `F[K]`-action with its twist by `conjAlg hKn e`. -/
theorem conjAlg_smul_resAct (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (c : MonoidAlgebra F K) (x : (resRep (K := K) ρ).asModule) :
    c • act ρ e x = act ρ e (conjAlg hKn e c • x) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, add_smul, add_smul, map_add, h₁, h₂]
  | single k a =>
      rw [conjAlg_single, single_smul', single_smul', map_smul, act_mul_apply, act_mul_apply,
        conjHom_apply, show e * (e⁻¹ * (k : L) * e) = (k : L) * e from by group]

/-! ## The image of a submodule under conjugation -/

theorem conjMod_apply_mem (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (W : SubM ρ) {w : (resRep (K := K) ρ).asModule} (hw : w ∈ W) :
    act ρ e w ∈ conjMod hKn ρ e W :=
  (mem_conjMod_iff hKn ρ e W (act ρ e w)).mpr ⟨w, hw, rfl⟩

/-- Regard an element of `conjMod hKn ρ e W` as an element of `W` by applying `ρ e⁻¹`. -/
def conjModToSub (hKn : K.Normal) (ρ : Representation F L V) (e : L) (W : SubM ρ) :
    ↥(conjMod hKn ρ e W) → ↥W :=
  fun y => ⟨act ρ e⁻¹ (y : (resRep (K := K) ρ).asModule), by
    obtain ⟨w, hw, hw'⟩ := (mem_conjMod_iff hKn ρ e W (y : (resRep (K := K) ρ).asModule)).mp y.2
    have hw'' : act ρ e w = (y : (resRep (K := K) ρ).asModule) := hw'
    rw [← hw'', act_inv_comp]
    exact hw⟩

/-- Send `x ∈ W` to `act ρ e x ∈ conjMod hKn ρ e W`. -/
def conjModOfSub (hKn : K.Normal) (ρ : Representation F L V) (e : L) (W : SubM ρ) :
    ↥W → ↥(conjMod hKn ρ e W) :=
  fun x => ⟨act ρ e (x : (resRep (K := K) ρ).asModule), conjMod_apply_mem hKn ρ e W x.2⟩

@[simp] theorem conjModToSub_apply (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (W : SubM ρ) (y : ↥(conjMod hKn ρ e W)) :
    ((conjModToSub hKn ρ e W y : ↥W) : (resRep (K := K) ρ).asModule) =
      act ρ e⁻¹ (y : (resRep (K := K) ρ).asModule) := rfl

@[simp] theorem conjModOfSub_apply (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (W : SubM ρ) (x : ↥W) :
    ((conjModOfSub hKn ρ e W x : ↥(conjMod hKn ρ e W)) :
        (resRep (K := K) ρ).asModule) = act ρ e (x : (resRep (K := K) ρ).asModule) := rfl

@[simp] theorem conjModOfSub_toSub (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (W : SubM ρ) (y : ↥(conjMod hKn ρ e W)) :
    conjModOfSub hKn ρ e W (conjModToSub hKn ρ e W y) = y := by
  apply Subtype.ext
  simp only [conjModOfSub_apply, conjModToSub_apply, act_comp_inv]

@[simp] theorem conjModToSub_ofSub (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (W : SubM ρ) (x : ↥W) :
    conjModToSub hKn ρ e W (conjModOfSub hKn ρ e W x) = x := by
  apply Subtype.ext
  simp only [conjModToSub_apply, conjModOfSub_apply, act_inv_comp]

theorem conjModToSub_add (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (W : SubM ρ) (y₁ y₂ : ↥(conjMod hKn ρ e W)) :
    conjModToSub hKn ρ e W (y₁ + y₂) = conjModToSub hKn ρ e W y₁ + conjModToSub hKn ρ e W y₂ := by
  apply Subtype.ext
  simp only [conjModToSub_apply, Submodule.coe_add, map_add]

theorem conjModOfSub_add (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (W : SubM ρ) (x₁ x₂ : ↥W) :
    conjModOfSub hKn ρ e W (x₁ + x₂) = conjModOfSub hKn ρ e W x₁ + conjModOfSub hKn ρ e W x₂ := by
  apply Subtype.ext
  simp only [conjModOfSub_apply, Submodule.coe_add, map_add]

/-- `conjModToSub` intertwines the `F[K]`-action on `conjMod hKn ρ e W` with its twist. -/
theorem conjModToSub_smul (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (W : SubM ρ) (c : MonoidAlgebra F K) (y : ↥(conjMod hKn ρ e W)) :
    conjModToSub hKn ρ e W (c • y) = conjAlg hKn e c • conjModToSub hKn ρ e W y := by
  apply Subtype.ext
  simp only [conjModToSub_apply, Submodule.coe_smul]
  have key : c • act ρ e (act ρ e⁻¹ (y : (resRep (K := K) ρ).asModule)) =
      act ρ e (conjAlg hKn e c • act ρ e⁻¹ (y : (resRep (K := K) ρ).asModule)) :=
    conjAlg_smul_resAct hKn ρ e c (act ρ e⁻¹ (y : (resRep (K := K) ρ).asModule))
  rw [act_comp_inv] at key
  rw [key, act_inv_comp]

/-! ## The `F[K]`-linear isomorphism `conjMod hKn ρ e m ≃ conjMod hKn ρ e S` -/

/-- Conjugation by `e` sends an isomorphism `m ≃ₗ[F[K]] S` to an isomorphism
`conjMod hKn ρ e m ≃ₗ[F[K]] conjMod hKn ρ e S`. -/
noncomputable def conjModLinearEquiv (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (m S : SubM ρ) (φ : m ≃ₗ[MonoidAlgebra F K] ↥S) :
    conjMod hKn ρ e m ≃ₗ[MonoidAlgebra F K] ↥(conjMod hKn ρ e S) where
  toFun y := conjModOfSub hKn ρ e S (φ (conjModToSub hKn ρ e m y))
  invFun z := conjModOfSub hKn ρ e m (φ.symm (conjModToSub hKn ρ e S z))
  left_inv y := by
    simp only [conjModOfSub_toSub, LinearEquiv.symm_apply_apply, conjModToSub_ofSub]
  right_inv z := by
    simp only [conjModToSub_ofSub, LinearEquiv.apply_symm_apply, conjModOfSub_toSub]
  map_add' y₁ y₂ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, conjModOfSub_apply, conjModToSub_add, map_add]
  map_smul' c y := by
    apply Subtype.ext
    rw [conjModToSub_smul, map_smul]
    simp only [conjModOfSub_apply, Submodule.coe_smul]
    rw [← conjAlg_smul_resAct]
    rfl

/-! ## Lattice properties of `conjMod` -/

theorem conjMod_bot (hKn : K.Normal) (ρ : Representation F L V) (e : L) :
    conjMod hKn ρ e (⊥ : SubM ρ) = ⊥ := by
  ext x
  rw [mem_conjMod_iff, Submodule.mem_bot]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [hw, map_zero]
  · intro h
    exact ⟨0, rfl, by rw [h, map_zero]⟩

theorem conjMod_inv_left (hKn : K.Normal) (ρ : Representation F L V) (e : L) (W : SubM ρ) :
    conjMod hKn ρ e⁻¹ (conjMod hKn ρ e W) = W := by
  rw [conjMod_mul, inv_mul_cancel, conjMod_one]

theorem conjMod_inv_right (hKn : K.Normal) (ρ : Representation F L V) (e : L) (W : SubM ρ) :
    conjMod hKn ρ e (conjMod hKn ρ e⁻¹ W) = W := by
  rw [conjMod_mul, mul_inv_cancel, conjMod_one]

theorem conjMod_eq_bot_iff (hKn : K.Normal) (ρ : Representation F L V) (e : L) (W : SubM ρ) :
    conjMod hKn ρ e W = ⊥ ↔ W = ⊥ :=
  ⟨fun h => by
      have h2 := congrArg (conjMod hKn ρ e⁻¹) h
      rwa [conjMod_inv_left, conjMod_bot] at h2,
    fun h => by rw [h, conjMod_bot]⟩

theorem conjMod_le_conjMod_iff (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    {W₁ W₂ : SubM ρ} : conjMod hKn ρ e W₁ ≤ conjMod hKn ρ e W₂ ↔ W₁ ≤ W₂ := by
  constructor
  · intro h x hx
    have h' : act ρ e x ∈ conjMod hKn ρ e W₂ := h (conjMod_apply_mem hKn ρ e W₁ hx)
    obtain ⟨y, hy, hyx⟩ := (mem_conjMod_iff hKn ρ e W₂ (act ρ e x)).mp h'
    have hyx' : y = x := act_injective ρ e hyx
    rwa [hyx'] at hy
  · intro h x hx
    obtain ⟨w, hw, rfl⟩ := (mem_conjMod_iff hKn ρ e W₁ x).mp hx
    exact conjMod_apply_mem hKn ρ e W₂ (h hw)

theorem conjMod_mono (hKn : K.Normal) (ρ : Representation F L V) (e : L) {W₁ W₂ : SubM ρ}
    (h : W₁ ≤ W₂) : conjMod hKn ρ e W₁ ≤ conjMod hKn ρ e W₂ :=
  (conjMod_le_conjMod_iff hKn ρ e).mpr h

/-- Conjugation by `e` preserves simplicity of an `F[K]`-submodule. -/
theorem isSimpleModule_conjMod_iff (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (W : SubM ρ) :
    IsSimpleModule (MonoidAlgebra F K) ↥(conjMod hKn ρ e W) ↔
      IsSimpleModule (MonoidAlgebra F K) ↥W := by
  rw [isSimpleModule_iff_isAtom, isSimpleModule_iff_isAtom]
  constructor
  · rintro ⟨hne, hmin⟩
    refine ⟨fun h => hne ((conjMod_eq_bot_iff hKn ρ e W).mpr h), fun b hb => ?_⟩
    have h1 : conjMod hKn ρ e b < conjMod hKn ρ e W := by
      refine lt_of_le_of_ne ((conjMod_le_conjMod_iff hKn ρ e).mpr hb.le) fun hEq => ?_
      have h2 : b = W := by
        have h3 := congrArg (conjMod hKn ρ e⁻¹) hEq
        rwa [conjMod_inv_left, conjMod_inv_left] at h3
      exact hb.ne h2
    have h2 := hmin (conjMod hKn ρ e b) h1
    have h3 : b = conjMod hKn ρ e⁻¹ ⊥ := by
      have h4 := congrArg (conjMod hKn ρ e⁻¹) h2
      rwa [conjMod_inv_left] at h4
    rwa [conjMod_bot] at h3
  · rintro ⟨hne, hmin⟩
    refine ⟨fun h => hne ((conjMod_eq_bot_iff hKn ρ e W).mp h), fun b hb => ?_⟩
    have h1a : conjMod hKn ρ e⁻¹ b ≤ W := by
      have h := (conjMod_le_conjMod_iff hKn ρ e⁻¹).mpr hb.le
      rwa [conjMod_inv_left] at h
    have h1 : conjMod hKn ρ e⁻¹ b < W := by
      refine lt_of_le_of_ne h1a fun hEq => ?_
      have h3 : b = conjMod hKn ρ e W := by
        have h4 := congrArg (conjMod hKn ρ e) hEq
        rwa [conjMod_inv_right] at h4
      exact hb.ne h3
    have h2 := hmin (conjMod hKn ρ e⁻¹ b) h1
    have h3 : b = conjMod hKn ρ e ⊥ := by
      have h4 := congrArg (conjMod hKn ρ e) h2
      rwa [conjMod_inv_right] at h4
    rwa [conjMod_bot] at h3

/-- Conjugation by `e` commutes with arbitrary suprema of submodules. -/
theorem conjMod_sSup (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (T : Set (SubM ρ)) : conjMod hKn ρ e (sSup T) = sSup (conjMod hKn ρ e '' T) := by
  apply le_antisymm
  · have h : sSup T ≤ conjMod hKn ρ e⁻¹ (sSup (conjMod hKn ρ e '' T)) := by
      apply sSup_le
      intro m hm
      have h1 : conjMod hKn ρ e m ≤ sSup (conjMod hKn ρ e '' T) := le_sSup ⟨m, hm, rfl⟩
      have h2 := conjMod_mono hKn ρ e⁻¹ h1
      rwa [conjMod_inv_left] at h2
    have h3 := conjMod_mono hKn ρ e h
    rwa [conjMod_inv_right] at h3
  · apply sSup_le
    rintro n ⟨m, hm, hmn⟩
    rw [← hmn]
    exact conjMod_mono hKn ρ e (le_sSup hm)

/-- Conjugation by `e` maps the `S`-isotypic component to the `conjMod hKn ρ e S`-isotypic
component. -/
theorem conjMod_isotypicComponent (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (S : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :
    conjMod hKn ρ e (isotypicComponent (MonoidAlgebra F K) (resRep (K := K) ρ).asModule S) =
      isotypicComponent (MonoidAlgebra F K) (resRep (K := K) ρ).asModule
        (conjMod hKn ρ e S) := by
  have hset : conjMod hKn ρ e '' {m : SubM ρ | Nonempty (m ≃ₗ[MonoidAlgebra F K] ↥S)} =
      {n : SubM ρ | Nonempty (n ≃ₗ[MonoidAlgebra F K] ↥(conjMod hKn ρ e S))} := by
    ext n
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, ⟨φ⟩, hm⟩
      rw [← hm]
      exact ⟨conjModLinearEquiv hKn ρ e m S φ⟩
    · rintro ⟨ψ⟩
      refine ⟨conjMod hKn ρ e⁻¹ n, ?_, ?_⟩
      · have h2 : Nonempty (conjMod hKn ρ e⁻¹ n ≃ₗ[MonoidAlgebra F K]
            ↥(conjMod hKn ρ e⁻¹ (conjMod hKn ρ e S))) :=
          ⟨conjModLinearEquiv hKn ρ e⁻¹ n (conjMod hKn ρ e S) ψ⟩
        rwa [show conjMod hKn ρ e⁻¹ (conjMod hKn ρ e S) = S from
          conjMod_inv_left hKn ρ e S] at h2
      · rw [conjMod_inv_right]
  unfold isotypicComponent
  rw [conjMod_sSup, hset]

end Work.ThmF.Prove.S3
