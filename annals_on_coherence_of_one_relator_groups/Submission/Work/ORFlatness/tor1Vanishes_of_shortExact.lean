import Mathlib
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.range_map_eq_ker_map

namespace Work.ORFlatness

universe u

/-- If the map induced by `f : A →ₗ[Rᵐᵒᵖ] X` on balanced tensor products is injective, then
so is the map induced by the inclusion of its range `f.range ↪ X`: writing
`f = f.range.subtype ∘ f.rangeRestrict` and using that `f.rangeRestrict` is surjective
(so that `BalTensor.map R f.rangeRestrict id` is surjective), injectivity of the composite
`BalTensor.map R f.range.subtype id ∘ BalTensor.map R f.rangeRestrict id` forces
injectivity of `BalTensor.map R f.range.subtype id`. -/
theorem injective_map_range_subtype {R : Type u} [Ring R] {A X : Type u}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup X] [Module Rᵐᵒᵖ X]
    (f : A →ₗ[Rᵐᵒᵖ] X) (N : Type u) [AddCommGroup N] [Module R N]
    (hf : Function.Injective (BalTensor.map R f (LinearMap.id : N →ₗ[R] N))) :
    Function.Injective
      (BalTensor.map R (LinearMap.range f).subtype (LinearMap.id : N →ₗ[R] N)) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := BalTensor.map_surjective R f.rangeRestrict (LinearMap.id : N →ₗ[R] N)
    (LinearMap.surjective_rangeRestrict f) (fun n => ⟨n, rfl⟩) x
  obtain ⟨b, rfl⟩ := BalTensor.map_surjective R f.rangeRestrict (LinearMap.id : N →ₗ[R] N)
    (LinearMap.surjective_rangeRestrict f) (fun n => ⟨n, rfl⟩) y
  have hfac : (LinearMap.range f).subtype.comp f.rangeRestrict = f := by ext z; rfl
  have hcomp : (BalTensor.map R (LinearMap.range f).subtype (LinearMap.id : N →ₗ[R] N)).comp
      (BalTensor.map R f.rangeRestrict (LinearMap.id : N →ₗ[R] N))
      = BalTensor.map R f (LinearMap.id : N →ₗ[R] N) := by
    rw [← BalTensor.map_comp, hfac, LinearMap.id_comp]
  have h1 : BalTensor.map R f (LinearMap.id) a = BalTensor.map R f (LinearMap.id) b := by
    rw [← hcomp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
    exact hxy
  rw [hf h1]

/-- Dimension shifting (the key step of the proof of Jaikin-Zapirain--Linton,
Theorem 5.6, in the single two-cell case): if `0 → A →f B →g C → 0` is a short exact
sequence of right `R`-modules (i.e. `g` surjective and `f.range = g.ker`), `N` is a left
`R`-module with `Tor1Vanishes R B N`, and the induced map `A ⊗[R] N → B ⊗[R] N` is
injective, then `Tor1Vanishes R C N`.

Proof sketch: take the witness `P : ProjPres R B` of `hB`, with covering map
`π : P.P →ₗ B` and `K := LinearMap.ker π`, so `K ⊗ N → P.P ⊗ N` is injective.  Put
`Y := π ⁻¹' f.range ⊆ P.P`.  Then `π` restricted to `Y` is surjective onto `A`,
with kernel `K`, and the composite `P.P → B → C` is a surjective map with kernel `Y`;
so `P` (with the same projective module) is a projective presentation of `C` with kernel
`Y`.  One shows `Function.Injective (BalTensor.map R Y.subtype id)`: for `z` in the
kernel, its image in `BalTensor R A N` (via `Y ↠ A`) maps to `0` in `BalTensor R B N`,
hence is `0` by the hypothesis `hA`; by right exactness
(`Work.ORFlatness.range_map_eq_ker_map`, applied to `K → Y → A → 0`, with `g` the
map `Y ↠ A` and `f` the inclusion `K ↪ Y`) the element `z` is the image of some
`w : BalTensor R K N`; since the composite `K → Y → P.P` is the inclusion `K ↪ P.P`,
`w` lies in the kernel of `BalTensor R K N → BalTensor R P.P N`, which is `0` by the
choice of `P`; hence `w = 0` and `z = 0`. -/
theorem tor1Vanishes_of_shortExact {R : Type u} [Ring R] {A B C : Type u}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module Rᵐᵒᵖ B]
    [AddCommGroup C] [Module Rᵐᵒᵖ C]
    (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C) (hg : Function.Surjective g)
    (hfg : f.range = g.ker) (N : Type u) [AddCommGroup N] [Module R N]
    (hB : Work.ORFlatness.Tor1Vanishes R B N)
    (hA : Function.Injective
      (Work.ORFlatness.BalTensor.map R f (LinearMap.id : N →ₗ[R] N))) :
    Work.ORFlatness.Tor1Vanishes R C N := by
  obtain ⟨P, hP⟩ := hB
  -- `map f.range.subtype id` is injective, by `hA` and surjectivity of `f.rangeRestrict`.
  have hA' : Function.Injective
      (BalTensor.map R (LinearMap.range f).subtype (LinearMap.id : N →ₗ[R] N)) :=
    injective_map_range_subtype f N hA
  -- The kernel `Y` of the surjection `P.P → C` obtained by composing `P.π` with `g`.
  let Y : Submodule Rᵐᵒᵖ P.P := LinearMap.ker (g.comp P.π)
  -- `K = ker π` is contained in `Y`.
  have hKY : P.K ≤ Y := by
    intro k hk
    show (g.comp P.π) k = 0
    rw [LinearMap.comp_apply, LinearMap.mem_ker.mp hk, map_zero]
  -- The restriction `ψ : Y → f.range` of `π`, a surjection with kernel `K`.
  let ψ : Y →ₗ[Rᵐᵒᵖ] f.range := P.π.restrict (p := Y) (q := f.range) (fun y hy => by
    have hy' : g (P.π (y : P.P)) = 0 := by
      have := hy
      simpa only [Y, LinearMap.mem_ker, LinearMap.comp_apply] using this
    rw [hfg]
    simpa only [LinearMap.mem_ker] using hy')
  have hsurjψ : Function.Surjective ψ := by
    intro c
    have hgc : g (c : B) = 0 := LinearMap.mem_ker.mp (hfg ▸ c.2)
    obtain ⟨b, hb⟩ := P.surj (c : B)
    have hbY : b ∈ Y := by
      show (g.comp P.π) b = 0
      rw [LinearMap.comp_apply, hb, hgc]
    exact ⟨⟨b, hbY⟩, Subtype.ext (by rw [LinearMap.coe_restrict_apply]; exact hb)⟩
  -- Right exactness of `K → Y → f.range → 0`.
  have hker : (Submodule.inclusion hKY).range = ψ.ker := by
    rw [Submodule.range_inclusion, LinearMap.ker_restrict]
  -- `map Y.subtype id` is injective.
  have hYinj0 : ∀ z : BalTensor R Y N,
      BalTensor.map R Y.subtype (LinearMap.id : N →ₗ[R] N) z = 0 → z = 0 := by
    intro z hz
    have h1 : f.range.subtype.comp ψ = P.π.domRestrict Y :=
      LinearMap.subtype_comp_restrict _
    -- `map ψ id z` is killed by the injection `f.range ⊗ N → B ⊗ N`.
    have hstep : BalTensor.map R (LinearMap.range f).subtype (LinearMap.id : N →ₗ[R] N)
        (BalTensor.map R ψ (LinearMap.id : N →ₗ[R] N) z) = 0 := by
      rw [← AddMonoidHom.comp_apply]
      rw [show (BalTensor.map R (LinearMap.range f).subtype (LinearMap.id : N →ₗ[R] N)).comp
            (BalTensor.map R ψ (LinearMap.id : N →ₗ[R] N))
          = BalTensor.map R (P.π.domRestrict Y) (LinearMap.id : N →ₗ[R] N) from by
        rw [← BalTensor.map_comp, h1, LinearMap.id_comp]]
      rw [show BalTensor.map R (P.π.domRestrict Y) (LinearMap.id : N →ₗ[R] N)
          = (BalTensor.map R P.π (LinearMap.id : N →ₗ[R] N)).comp
              (BalTensor.map R Y.subtype (LinearMap.id : N →ₗ[R] N)) from by
        rw [show P.π.domRestrict Y = P.π.comp Y.subtype from rfl, ← BalTensor.map_comp,
          LinearMap.id_comp]]
      rw [AddMonoidHom.comp_apply, hz, map_zero]
    have hψz : BalTensor.map R ψ (LinearMap.id : N →ₗ[R] N) z = 0 := hA' hstep
    -- Right exactness: `z` comes from `K ⊗ N`.
    have hrex := range_map_eq_ker_map (Submodule.inclusion hKY) ψ hsurjψ hker N
    have hzker : z ∈ (BalTensor.map R ψ (LinearMap.id : N →ₗ[R] N)).ker := by
      rw [AddMonoidHom.mem_ker]; exact hψz
    rw [← hrex] at hzker
    obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp hzker
    -- `Y.subtype ∘ inclusion = K.subtype`, so `map K.subtype id w = 0`.
    have hcompY : (BalTensor.map R Y.subtype (LinearMap.id : N →ₗ[R] N)).comp
        (BalTensor.map R (Submodule.inclusion hKY) (LinearMap.id : N →ₗ[R] N))
        = BalTensor.map R P.K.subtype (LinearMap.id : N →ₗ[R] N) := by
      rw [← BalTensor.map_comp, LinearMap.id_comp, Submodule.subtype_comp_inclusion]
    have hz'' : BalTensor.map R P.K.subtype (LinearMap.id : N →ₗ[R] N) w = 0 := by
      rw [← hcompY, AddMonoidHom.comp_apply, hw]
      exact hz
    have hw0 : w = 0 := hP hz''
    rw [← hw, hw0, map_zero]
  have hYinj : Function.Injective
      (BalTensor.map R (Submodule.subtype Y) (LinearMap.id : N →ₗ[R] N)) := by
    intro z z' h
    have hsub : z - z' = 0 := hYinj0 (z - z') (by rw [map_sub, h, sub_self])
    rwa [sub_eq_zero] at hsub
  -- The same projective module, now presenting `C`.
  refine ⟨{ P := P.P, π := g.comp P.π, surj := ?_ }, ?_⟩
  · intro c
    obtain ⟨b, hb⟩ := hg c
    obtain ⟨p, hp⟩ := P.surj b
    exact ⟨p, by rw [LinearMap.comp_apply, hp, hb]⟩
  · exact hYinj

end Work.ORFlatness
