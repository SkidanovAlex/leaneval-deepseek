import Mathlib
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.Tensor
import Submission.Work.ORFlatness.range_map_eq_ker_map
import Submission.Work.ORFlatness.range_map_eq_ker_map_right

open TensorProduct MulOpposite

namespace Work.ORFlatness

universe u

/-- Functoriality of `BalTensor.map` in application form: the composite of
`map R f' g'` with `map R f g` on an element `y` is `map R (f'.comp f) (g'.comp g) y`. -/
private theorem map_apply_map_aux {R : Type u} [Ring R]
    {X X' X'' : Type u} [AddCommGroup X] [Module Rᵐᵒᵖ X]
    [AddCommGroup X'] [Module Rᵐᵒᵖ X'] [AddCommGroup X''] [Module Rᵐᵒᵖ X'']
    {N N' N'' : Type u} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] [AddCommGroup N''] [Module R N'']
    (f' : X' →ₗ[Rᵐᵒᵖ] X'') (g' : N' →ₗ[R] N'')
    (f : X →ₗ[Rᵐᵒᵖ] X') (g : N →ₗ[R] N') (y : BalTensor R X N) :
    BalTensor.map R f' g' (BalTensor.map R f g y) = BalTensor.map R (f'.comp f) (g'.comp g) y := by
  rw [BalTensor.map_comp, AddMonoidHom.comp_apply]

/-- The balanced tensor product of the zero map (in the first variable) with `g` is zero. -/
private theorem map_zero_left_aux {R : Type u} [Ring R]
    {X X' : Type u} [AddCommGroup X] [Module Rᵐᵒᵖ X] [AddCommGroup X'] [Module Rᵐᵒᵖ X']
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (g : N →ₗ[R] N') : BalTensor.map R (0 : X →ₗ[Rᵐᵒᵖ] X') g = 0 := by
  apply BalTensor.ext R
  intro x n
  simp

/-- The balanced tensor product of `f` with the zero map (in the second variable) is zero. -/
private theorem map_zero_right_aux {R : Type u} [Ring R]
    {X X' : Type u} [AddCommGroup X] [Module Rᵐᵒᵖ X] [AddCommGroup X'] [Module Rᵐᵒᵖ X']
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : X →ₗ[Rᵐᵒᵖ] X') : BalTensor.map R f (0 : N →ₗ[R] N') = 0 := by
  apply BalTensor.ext R
  intro x n
  simp

/-- Dimension shifting for `Tor₁` in the **second** variable (mirror of the proved `Work.ORFlatness.tor1Vanishes_of_shortExact`). Let `0 → A →f B →g C → 0` be a short exact sequence of **left** `R`-modules (`g` surjective, `f.range = g.ker`) and let `X` be a **right** `R`-module. If `Tor₁^R(X, B) = 0` (`Work.ORFlatness.Tor1Vanishes R X B`) and the induced map `X ⊗[R] A → X ⊗[R] B` is injective, then `Tor₁^R(X, C) = 0`.

Explicit element chase; no homology functor is needed. `hB` is witnessed by a projective presentation `0 → K → P → X → 0` of `X` (right modules) with `BalTensor.map R P.K.subtype id_B` injective; the SAME presentation witnesses `Tor1Vanishes R X C`: given `z ∈ K ⊗ C` with `(ι ⊗ id_C) z = 0`, lift `z = (id_K ⊗ g) y` (surjectivity of `id_K ⊗ g`), put `w := (ι ⊗ id_B) y ∈ P ⊗ B`; from `(id_P ⊗ g) w = (ι ⊗ id_C) z = 0` and right exactness of the row (`range_map_eq_ker_map_right`) get `w = (id_P ⊗ f) p`, then `(id_X ⊗ f)((π ⊗ id_A) p) = (π ⊗ id_B) w = 0`, so `(π ⊗ id_A) p = 0` by `hA`, i.e. `p ∈ ker(π ⊗ id_A) = range(ι ⊗ id_A)` (right exactness in the first variable, `range_map_eq_ker_map`), so `p = (ι ⊗ id_A) q`; functoriality gives `w = (ι ⊗ id_B)((id_K ⊗ f) q)`, so `y = (id_K ⊗ f) q` by injectivity of `ι ⊗ id_B`, and finally `z = (id_K ⊗ g) y = (id_K ⊗ (g ∘ f)) q = 0`. -/
theorem tor1Vanishes_of_shortExact_right {R : Type u} [Ring R] {A B C : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X] (hB : Work.ORFlatness.Tor1Vanishes R X B)
    (hA : Function.Injective
      (Work.ORFlatness.BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f)) :
    Work.ORFlatness.Tor1Vanishes R X C := by
  obtain ⟨P, hP⟩ := hB
  refine ⟨P, ?_⟩
  -- The key step: an element of `K ⊗ C` killed by `ι ⊗ id_C` is zero.
  have hzero : ∀ z : BalTensor R P.K C,
      BalTensor.map R (Submodule.subtype P.K) (LinearMap.id : C →ₗ[R] C) z = 0 → z = 0 := by
    intro z hz
    -- (1) `id_K ⊗ g` is surjective, so `z = (id_K ⊗ g) y`.
    obtain ⟨y, hy⟩ := BalTensor.map_surjective R (LinearMap.id : P.K →ₗ[Rᵐᵒᵖ] P.K) g
      (fun k => ⟨k, rfl⟩) hg z
    -- `hy : BalTensor.map R (LinearMap.id) g y = z`
    let w : BalTensor R P.P B :=
      BalTensor.map R (Submodule.subtype P.K) (LinearMap.id : B →ₗ[R] B) y
    have hwdef : w = BalTensor.map R (Submodule.subtype P.K) (LinearMap.id : B →ₗ[R] B) y := rfl
    -- (2) `(id_P ⊗ g) w = 0`, because both sides equal `(ι ⊗ g) y`.
    have hgw : BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) g w = 0 := by
      have h1 : BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) g w
          = BalTensor.map R (Submodule.subtype P.K) g y := by
        rw [hwdef, map_apply_map_aux]
        simp only [LinearMap.id_comp, LinearMap.comp_id]
      have h2 : BalTensor.map R (Submodule.subtype P.K) g y
          = BalTensor.map R (Submodule.subtype P.K) (LinearMap.id : C →ₗ[R] C) z := by
        rw [← hy, map_apply_map_aux]
        simp only [LinearMap.id_comp, LinearMap.comp_id]
      rw [h1, h2, hz]
    -- (3) `w` lies in the image of `id_P ⊗ f` by right exactness in the second variable.
    have hwrange : w ∈ (BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) f).range := by
      have hwker : w ∈ (BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) g).ker := by
        rw [AddMonoidHom.mem_ker]; exact hgw
      rwa [← range_map_eq_ker_map_right f g hg hfg P.P] at hwker
    obtain ⟨p, hp⟩ := AddMonoidHom.mem_range.mp hwrange
    have hp' : BalTensor.map R (LinearMap.id : P.P →ₗ[Rᵐᵒᵖ] P.P) f p
        = BalTensor.map R (Submodule.subtype P.K) (LinearMap.id : B →ₗ[R] B) y :=
      hp.trans hwdef
    -- (4) `(id_X ⊗ f) ((π ⊗ id_A) p) = (π ⊗ id_B) w = 0`.
    have hXP : BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f
        (BalTensor.map R P.π (LinearMap.id : A →ₗ[R] A) p) = 0 := by
      have hL : BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f
          (BalTensor.map R P.π (LinearMap.id : A →ₗ[R] A) p)
          = BalTensor.map R P.π f p := by
        rw [map_apply_map_aux]
        simp only [LinearMap.id_comp, LinearMap.comp_id]
      have hR : BalTensor.map R P.π (LinearMap.id : B →ₗ[R] B) w
          = BalTensor.map R P.π f p := by
        rw [hwdef, ← hp']
        rw [map_apply_map_aux]
        simp only [LinearMap.id_comp, LinearMap.comp_id]
      have hR0 : BalTensor.map R P.π (LinearMap.id : B →ₗ[R] B) w = 0 := by
        have h3 : BalTensor.map R P.π (LinearMap.id : B →ₗ[R] B) w
            = BalTensor.map R (P.π.comp (Submodule.subtype P.K))
                (LinearMap.id : B →ₗ[R] B) y := by
          rw [hwdef, map_apply_map_aux]
          simp only [LinearMap.comp_id]
        have hπι : P.π.comp (Submodule.subtype P.K) = 0 := by
          ext k; exact k.2
        rw [h3, hπι, map_zero_left_aux]
        simp
      rw [hL, ← hR, hR0]
    -- (5) By injectivity of `id_X ⊗ f`, `(π ⊗ id_A) p = 0`.
    have hpA : BalTensor.map R P.π (LinearMap.id : A →ₗ[R] A) p = 0 :=
      hA (by simp [hXP])
    -- (6) So `p = (ι ⊗ id_A) q` by right exactness in the first variable.
    have hker : (Submodule.subtype P.K).range = P.π.ker := Submodule.range_subtype P.K
    have hprange : p ∈ (BalTensor.map R (Submodule.subtype P.K) (LinearMap.id : A →ₗ[R] A)).range := by
      rw [range_map_eq_ker_map (Submodule.subtype P.K) P.π P.surj hker A, AddMonoidHom.mem_ker]
      exact hpA
    obtain ⟨q, hq⟩ := AddMonoidHom.mem_range.mp hprange
    -- (7) Functoriality gives `(ι ⊗ id_B) y = (ι ⊗ id_B) ((id_K ⊗ f) q)`, hence `y = (id_K ⊗ f) q`.
    have hwq : BalTensor.map R (Submodule.subtype P.K) (LinearMap.id : B →ₗ[R] B) y
        = BalTensor.map R (Submodule.subtype P.K) (LinearMap.id : B →ₗ[R] B)
            (BalTensor.map R (LinearMap.id : P.K →ₗ[Rᵐᵒᵖ] P.K) f q) := by
      rw [← hp', ← hq, map_apply_map_aux, map_apply_map_aux]
      simp only [LinearMap.id_comp, LinearMap.comp_id]
    have hyq : y = BalTensor.map R (LinearMap.id : P.K →ₗ[Rᵐᵒᵖ] P.K) f q := hP hwq
    -- (8) `z = (id_K ⊗ g) y = (id_K ⊗ (g ∘ f)) q = 0` since `g ∘ f = 0`.
    have hgf : g.comp f = 0 := by
      ext a
      have : f a ∈ g.ker := by rw [← hfg]; exact LinearMap.mem_range_self f a
      simpa using this
    rw [← hy, hyq, map_apply_map_aux, LinearMap.id_comp, hgf, map_zero_right_aux]
    simp
  -- `hzero` upgrades to injectivity of `ι ⊗ id_C`.
  intro z z' h
  have h0 : z - z' = 0 := hzero (z - z') (by rw [map_sub, h, sub_self])
  rwa [sub_eq_zero] at h0

end Work.ORFlatness
