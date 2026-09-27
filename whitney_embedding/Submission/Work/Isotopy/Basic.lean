import Mathlib

/-!
# Isotopies and ambient isotopies

This file sets up the vocabulary of isotopy theory, which is the basic language in which
the remaining steps of Whitney's strong embedding theorem are phrased:

* `Work.Isotopy.AmbientIsotopy E` is an isotopy of the *ambient* space `E`: a homeomorphism of
  `E × ℝ` commuting with the projection onto `ℝ` and restricting to the identity on `E × {0}`.
  From it one gets, for every time `t`, a self-homeomorphism `AmbientIsotopy.apply Φ t` of `E`,
  and `apply Φ 0 = id`.

* `Work.Isotopy.Isotopy X E` is a continuous family `t ↦ f t` of *embeddings* `X → E`.
  An ambient isotopy of `E` acts on the space of embeddings of `X`, giving an isotopy
  (`AmbientIsotopy.isotopy`).

The main theorem that this vocabulary is set up for is the **isotopy extension theorem**:
every isotopy of a compact submanifold `X ⊆ E` is induced by an ambient isotopy of `E`.
-/

set_option linter.dupNamespace false

open Function Set Topology

namespace Work.Isotopy

/-- An **ambient isotopy** of a topological space `E`: a homeomorphism of `E × ℝ` which
commutes with the projection onto `ℝ` and restricts to the identity on `E × {0}`.

The first coordinate of the source parametrises `E`, the second one the time. -/
structure AmbientIsotopy (E : Type*) [TopologicalSpace E] where
  /-- The underlying homeomorphism of `E × ℝ`. -/
  toHomeomorph : (E × ℝ) ≃ₜ (E × ℝ)
  /-- The homeomorphism commutes with the projection onto the time coordinate. -/
  map_snd : ∀ p : E × ℝ, (toHomeomorph p).2 = p.2
  /-- At time `0` the isotopy is the identity. -/
  map_zero_fst : ∀ x : E, (toHomeomorph (x, 0)).1 = x

namespace AmbientIsotopy

variable {E : Type*} [TopologicalSpace E]

instance : CoeFun (AmbientIsotopy E) fun _ => E × ℝ → E × ℝ :=
  ⟨fun Φ => Φ.toHomeomorph⟩

@[simp]
theorem map_snd_apply (Φ : AmbientIsotopy E) (p : E × ℝ) : (Φ p).2 = p.2 :=
  Φ.map_snd p

@[simp]
theorem map_zero_apply (Φ : AmbientIsotopy E) (x : E) : Φ (x, 0) = (x, 0) :=
  Prod.ext (Φ.map_zero_fst x) (Φ.map_snd (x, 0))

/-- At time `t`, an ambient isotopy is the self-homeomorphism `x ↦ Φ (x, t)`. -/
noncomputable def apply (Φ : AmbientIsotopy E) (t : ℝ) : E ≃ₜ E where
  toFun x := (Φ (x, t)).1
  invFun y := (Φ.toHomeomorph.symm (y, t)).1
  left_inv x := by
    have h : Φ.toHomeomorph.symm ((Φ (x, t)).1, t) = (x, t) := by
      have h1 : ((Φ (x, t)).1, t) = Φ (x, t) := Prod.ext rfl (Φ.map_snd (x, t)).symm
      rw [h1, Φ.toHomeomorph.symm_apply_apply]
    simpa using congrArg Prod.fst h
  right_inv y := by
    have h2 : (Φ.toHomeomorph.symm (y, t)).2 = t := by
      have hh : (Φ (Φ.toHomeomorph.symm (y, t))).2 = (Φ.toHomeomorph.symm (y, t)).2 :=
        Φ.map_snd _
      rw [Φ.toHomeomorph.apply_symm_apply] at hh
      simpa using hh.symm
    have h : Φ ((Φ.toHomeomorph.symm (y, t)).1, t) = (y, t) := by
      have h1 : ((Φ.toHomeomorph.symm (y, t)).1, t) = Φ.toHomeomorph.symm (y, t) :=
        Prod.ext rfl h2.symm
      rw [h1, Φ.toHomeomorph.apply_symm_apply]
    simpa using congrArg Prod.fst h
  continuous_toFun :=
    (continuous_fst.comp Φ.toHomeomorph.continuous).comp (continuous_id.prodMk continuous_const)
  continuous_invFun :=
    (continuous_fst.comp Φ.toHomeomorph.symm.continuous).comp
      (continuous_id.prodMk continuous_const)

@[simp]
theorem apply_apply (Φ : AmbientIsotopy E) (t : ℝ) (x : E) : Φ.apply t x = (Φ (x, t)).1 := rfl

@[simp]
theorem apply_zero (Φ : AmbientIsotopy E) : Φ.apply 0 = Homeomorph.refl E := by
  ext x
  exact Φ.map_zero_fst x

/-- The joint continuity of `(t, x) ↦ Φ.apply t x`. -/
theorem continuous_apply_uncurry (Φ : AmbientIsotopy E) :
    Continuous fun p : ℝ × E => Φ.apply p.1 p.2 :=
  (continuous_fst.comp Φ.toHomeomorph.continuous).comp continuous_swap

/-- The ambient isotopy that is the identity at every time. -/
protected noncomputable def refl (E : Type*) [TopologicalSpace E] : AmbientIsotopy E where
  toHomeomorph := Homeomorph.refl _
  map_snd _ := rfl
  map_zero_fst _ := rfl

@[simp]
theorem refl_apply (t : ℝ) (x : E) : (AmbientIsotopy.refl E).apply t x = x := rfl

/-- Composition of ambient isotopies (first `Φ`, then `Ψ`). -/
protected noncomputable def comp (Ψ Φ : AmbientIsotopy E) : AmbientIsotopy E where
  toHomeomorph := Φ.toHomeomorph.trans Ψ.toHomeomorph
  map_snd p := by
    rw [Homeomorph.trans_apply, Ψ.map_snd, Φ.map_snd]
  map_zero_fst x := by
    rw [Homeomorph.trans_apply, map_zero_apply, map_zero_apply]

@[simp]
theorem comp_apply (Ψ Φ : AmbientIsotopy E) (t : ℝ) (x : E) :
    (Ψ.comp Φ).apply t x = Ψ.apply t (Φ.apply t x) := by
  have h : (((Φ (x, t)).1), t) = Φ (x, t) := Prod.ext rfl (Φ.map_snd (x, t)).symm
  have h2 : (Ψ.comp Φ).toHomeomorph (x, t) = Ψ.toHomeomorph (Φ (x, t)) := rfl
  rw [apply_apply, apply_apply, apply_apply, h2, h]

/-- An ambient isotopy is supported in a set `U` if it fixes the complement of `U`
(at every time). -/
def IsSupportedOn (Φ : AmbientIsotopy E) (U : Set E) : Prop :=
  ∀ (t : ℝ) (x : E), x ∉ U → Φ.apply t x = x

theorem IsSupportedOn.comp {Φ Ψ : AmbientIsotopy E} {U : Set E}
    (hΨ : Ψ.IsSupportedOn U) (hΦ : Φ.IsSupportedOn U) : (Ψ.comp Φ).IsSupportedOn U := by
  intro t x hx
  rw [comp_apply, hΦ t x hx, hΨ t x hx]

theorem IsSupportedOn.refl (U : Set E) : (AmbientIsotopy.refl E).IsSupportedOn U := by
  intro t x _; rfl

end AmbientIsotopy

/-- An **isotopy** of maps `X → E`: a continuous family `t ↦ f t` of embeddings of `X` in `E`. -/
structure Isotopy (X : Type*) (E : Type*) [TopologicalSpace X] [TopologicalSpace E] where
  /-- The family of maps. -/
  toFun : ℝ → X → E
  /-- The family is jointly continuous. -/
  continuous_uncurry : Continuous (Function.uncurry toFun)
  /-- Every member of the family is an embedding. -/
  isEmbedding_apply : ∀ t, IsEmbedding (toFun t)

namespace Isotopy

variable {X : Type*} {E : Type*} [TopologicalSpace X] [TopologicalSpace E]

instance : CoeFun (Isotopy X E) fun _ => ℝ → X → E := ⟨fun Φ => Φ.toFun⟩

theorem continuous_apply_uncurry (Φ : Isotopy X E) :
    Continuous fun p : ℝ × X => Φ p.1 p.2 := Φ.continuous_uncurry

theorem continuous_apply (Φ : Isotopy X E) (t : ℝ) : Continuous (Φ t) :=
  Φ.continuous_uncurry.comp (continuous_const.prodMk continuous_id) |>.congr fun _ => rfl

end Isotopy

/-- An ambient isotopy of `E` acts on embeddings of `X` into `E`, producing an isotopy. -/
noncomputable def AmbientIsotopy.isotopy {X : Type*} [TopologicalSpace X]
    {E : Type*} [TopologicalSpace E] (Φ : AmbientIsotopy E) (f : X → E)
    (hf : IsEmbedding f) : Isotopy X E where
  toFun t := fun x => Φ.apply t (f x)
  continuous_uncurry := by
    have h : Continuous fun p : ℝ × X => (p.1, f p.2) :=
      continuous_fst.prodMk (hf.continuous.comp continuous_snd)
    exact Φ.continuous_apply_uncurry.comp h
  isEmbedding_apply t := (Φ.apply t).isEmbedding.comp hf

@[simp]
theorem AmbientIsotopy.isotopy_apply {X : Type*} [TopologicalSpace X]
    {E : Type*} [TopologicalSpace E] (Φ : AmbientIsotopy E) (f : X → E) (hf : IsEmbedding f)
    (t : ℝ) (x : X) : Φ.isotopy f hf t x = Φ.apply t (f x) := rfl

@[simp]
theorem AmbientIsotopy.isotopy_zero {X : Type*} [TopologicalSpace X]
    {E : Type*} [TopologicalSpace E] (Φ : AmbientIsotopy E) (f : X → E) (hf : IsEmbedding f) :
    Φ.isotopy f hf 0 = f := by
  funext x
  rw [isotopy_apply, apply_zero]
  rfl

/-- Two maps are isotopic if they are the endpoints of an isotopy of embeddings. -/
def Isotopic {X : Type*} [TopologicalSpace X] {E : Type*} [TopologicalSpace E]
    (f g : X → E) : Prop :=
  ∃ Φ : Isotopy X E, Φ 0 = f ∧ Φ 1 = g

theorem Isotopic.refl {X : Type*} [TopologicalSpace X] {E : Type*} [TopologicalSpace E]
    {f : X → E} (hf : IsEmbedding f) : Isotopic f f :=
  ⟨{ toFun := fun _ => f
     continuous_uncurry := hf.continuous.comp continuous_snd
     isEmbedding_apply := fun _ => hf }, rfl, rfl⟩

end Work.Isotopy
