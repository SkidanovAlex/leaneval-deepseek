import Mathlib
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.Tensor
import Submission.Work.ORFlatness.range_map_eq_ker_map
import Submission.Work.ORFlatness.range_map_eq_ker_map_right
import Submission.Work.ORFlatness.rightFlat_of_projective

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

namespace BalTensor

/-- `BalTensor.map f 0 = 0`. -/
theorem map_zero_right {R : Type u} [Ring R] {X X' : Type u}
    [AddCommGroup X] [Module Rᵐᵒᵖ X] [AddCommGroup X'] [Module Rᵐᵒᵖ X']
    (f : X →ₗ[Rᵐᵒᵖ] X') {N N' : Type u} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] :
    map R f (0 : N →ₗ[R] N') = 0 := by
  apply BalTensor.ext R
  intro x n
  rw [BalTensor.map_mk]
  simp

/-- `BalTensor.map 0 g = 0`. -/
theorem map_zero_left {R : Type u} [Ring R] {X X' : Type u}
    [AddCommGroup X] [Module Rᵐᵒᵖ X] [AddCommGroup X'] [Module Rᵐᵒᵖ X']
    {N N' : Type u} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') :
    map R (0 : X →ₗ[Rᵐᵒᵖ] X') g = 0 := by
  apply BalTensor.ext R
  intro x n
  rw [BalTensor.map_mk]
  simp

end BalTensor

/-- The mirror of the proved `Work.ORFlatness.injective_of_tor1Vanishes`: if the cokernel `C` of an injection `f : A ↪ B` of **left** `R`-modules satisfies `Tor₁^R(X, C) = 0` for a **right** `R`-module `X` (`Work.ORFlatness.Tor1Vanishes R X C`), then the induced map `X ⊗[R] A → X ⊗[R] B` is injective.

Explicit element chase. Let `0 → K → P → X → 0` be the projective presentation of `X` (right modules) witnessing `hC`, so `ι : K ↪ P` and `map ι id_C` is injective. Given `z ∈ X ⊗ A` with `(id_X ⊗ f) z = 0`, lift `z = (π ⊗ id_A) w` with `w ∈ P ⊗ A` (surjectivity of `π ⊗ id_A`). Then `(π ⊗ id_B)((id_P ⊗ f) w) = (id_X ⊗ f) z = 0`, so `(id_P ⊗ f) w = (ι ⊗ id_B) u`, using right exactness in the first variable (`range_map_eq_ker_map`) for `K → P → X → 0` tensored with `B`. Then `(ι ⊗ id_C)((id_K ⊗ g) u) = (id_P ⊗ g)((id_P ⊗ f) w) = (id_P ⊗ (g ∘ f)) w = 0`, so `(id_K ⊗ g) u = 0` by injectivity of `ι ⊗ id_C`, hence `u = (id_K ⊗ f) u'` by right exactness in the second variable (`range_map_eq_ker_map_right`) for `A → B → C → 0` tensored with `K`. Functoriality gives `(id_P ⊗ f) w = (id_P ⊗ f)((ι ⊗ id_A) u')`, so `w = (ι ⊗ id_A) u'` by injectivity of `id_P ⊗ f`, which holds because `P` is projective (`Work.ORFlatness.rightFlat_of_projective`) and `f` is injective. Finally `z = (π ⊗ id_A) w = ((π ∘ ι) ⊗ id_A) u' = 0`. -/
theorem injective_of_tor1Vanishes_right {R : Type u} [Ring R] {A B C : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X] (hC : Work.ORFlatness.Tor1Vanishes R X C) :
    Function.Injective
      (Work.ORFlatness.BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f) := by
  obtain ⟨P, hK⟩ := hC
  have hρ : Function.Surjective P.π := P.surj
  let ι : P.K →ₗ[Rᵐᵒᵖ] P.P := Submodule.subtype P.K
  have hιrange : ι.range = P.π.ker := by
    show (Submodule.subtype P.K).range = P.π.ker
    rw [Submodule.range_subtype]
  have hgf : g.comp f = 0 := by
    ext a
    have : f a ∈ g.ker := by rw [← hfg]; exact LinearMap.mem_range_self f a
    simpa using this
  have hπι : P.π.comp ι = 0 := by
    ext k
    exact k.2
  have hinjP : Function.Injective
      (BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) f) :=
    rightFlat_of_projective R (X := P.P) f hf
  have square : (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f).comp
        (BalTensor.map R P.π (LinearMap.id : A →ₗ[R] A))
      = (BalTensor.map R P.π (LinearMap.id : B →ₗ[R] B)).comp
        (BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) f) := by
    rw [← BalTensor.map_comp, ← BalTensor.map_comp]
    simp
  have square2 : (BalTensor.map R ι (LinearMap.id : C →ₗ[R] C)).comp
        (BalTensor.map R (LinearMap.id : P.K →ₗ[Rᵐᵒᵖ] P.K) g)
      = (BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) g).comp
        (BalTensor.map R ι (LinearMap.id : B →ₗ[R] B)) := by
    rw [← BalTensor.map_comp, ← BalTensor.map_comp]
    simp
  have hcompl : (BalTensor.map R P.π (LinearMap.id : A →ₗ[R] A)).comp
        (BalTensor.map R ι (LinearMap.id : A →ₗ[R] A)) = 0 := by
    rw [← BalTensor.map_comp, hπι]
    exact BalTensor.map_zero_left (N := A) (N' := A) (g := LinearMap.id)
  have key : ∀ z : BalTensor R X A,
      BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f z = 0 → z = 0 := by
    intro z hz
    obtain ⟨v, hv⟩ := BalTensor.map_surjective R P.π (LinearMap.id : A →ₗ[R] A) hρ
      (fun a => ⟨a, rfl⟩) z
    have h2 : (BalTensor.map R P.π (LinearMap.id : B →ₗ[R] B))
        ((BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) f) v) = 0 := by
      have hh : (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f)
          ((BalTensor.map R P.π (LinearMap.id : A →ₗ[R] A)) v) = 0 := by
        rw [hv]; exact hz
      rwa [← AddMonoidHom.comp_apply, square, AddMonoidHom.comp_apply] at hh
    have hmem : (BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) f) v ∈
        (BalTensor.map R ι (LinearMap.id : B →ₗ[R] B)).range := by
      rw [show (BalTensor.map R ι (LinearMap.id : B →ₗ[R] B)).range
            = (BalTensor.map R P.π (LinearMap.id : B →ₗ[R] B)).ker from
          range_map_eq_ker_map ι P.π hρ hιrange B, AddMonoidHom.mem_ker]
      exact h2
    obtain ⟨u, hu⟩ := hmem
    have hmapgf : BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) (g.comp f) = 0 := by
      rw [hgf]
      exact BalTensor.map_zero_right (R := R) (N := A) (N' := C)
        (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P)
    have hcompl2 : (BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) g).comp
          (BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) f)
        = BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) (g.comp f) := by
      rw [← BalTensor.map_comp]
      simp
    have hzero : (BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) g)
        ((BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) f) v) = 0 := by
      rw [← AddMonoidHom.comp_apply, hcompl2, hmapgf]
      rfl
    have hKg : (BalTensor.map R (LinearMap.id : P.K →ₗ[Rᵐᵒᵖ] P.K) g) u = 0 := by
      refine hK ?_
      have hιu : (BalTensor.map R ι (LinearMap.id : C →ₗ[R] C))
          ((BalTensor.map R (LinearMap.id : P.K →ₗ[Rᵐᵒᵖ] P.K) g) u) = 0 := by
        rw [← AddMonoidHom.comp_apply, square2, AddMonoidHom.comp_apply, hu]
        exact hzero
      rw [map_zero]
      exact hιu
    have hker2 : (BalTensor.map R (LinearMap.id : P.K →ₗ[Rᵐᵒᵖ] P.K) f).range
        = (BalTensor.map R (LinearMap.id : P.K →ₗ[Rᵐᵒᵖ] P.K) g).ker :=
      range_map_eq_ker_map_right f g hg hfg P.K
    have humem : u ∈ (BalTensor.map R (LinearMap.id : P.K →ₗ[Rᵐᵒᵖ] P.K) f).range := by
      rw [hker2, AddMonoidHom.mem_ker]
      exact hKg
    obtain ⟨u', hu'⟩ := humem
    have hv' : v = (BalTensor.map R ι (LinearMap.id : A →ₗ[R] A)) u' := by
      apply hinjP
      rw [← hu, ← hu']
      rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
        ← BalTensor.map_comp, ← BalTensor.map_comp]
      simp
    rw [← hv, hv', ← AddMonoidHom.comp_apply, hcompl]
    simp
  intro z w hzw
  have h : z - w = 0 := key (z - w) (by rw [map_sub, hzw, sub_self])
  exact sub_eq_zero.mp h

end Work.ORFlatness
