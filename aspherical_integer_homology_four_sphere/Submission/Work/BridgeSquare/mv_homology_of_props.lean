import Mathlib
import Submission.Work.HomologyMV.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.BridgeSquare

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

/-- The engine of the Mayer–Vietoris computation, stated in the ambient instance normalisation
of `Work.HomologyMV.Basic` (the `ℤ`-module structure on `↥g'.ker` is the restriction of the
ambient one, `Submodule.module`): if `M --f--> N --g--> X --h--> Y --g'--> Z` is exact at `N`,
at `X` and at `Y`, and `f` is surjective, then `X ≅ ker g'`.

This is `Work.HomologyMV.isoKer_of_surjective` (whose statement is phrased in a different,
propositionally equal normalisation of the module structure) re-proved here so that the
resulting equivalence composes with the identifications `hker` without an instance transport. -/
theorem isoKer_of_surjective' {M N X Y Z : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module ℤ M] [Module ℤ N] [Module ℤ X]
    [Module ℤ Y] [Module ℤ Z] (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] X) (h : X →ₗ[ℤ] Y)
    (g' : Y →ₗ[ℤ] Z) (hf : Function.Exact f g) (hg : Function.Exact g h)
    (hh : Function.Exact h g') (hsurj : f.range = ⊤) : Nonempty (X ≃ₗ[ℤ] g'.ker) := by
  rw [LinearMap.exact_iff] at hf hg hh
  -- hf : g.ker = f.range, hg : h.ker = g.range, hh : g'.ker = h.range
  have hg_zero : g = 0 := by
    ext x
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (by rw [hf, hsurj]; trivial)
  have hker : h.ker = ⊥ := by
    rw [hg, hg_zero, LinearMap.range_zero]
  have hinj : Function.Injective h := LinearMap.ker_eq_bot.mp hker
  let H := h.codRestrict g'.ker (fun x => by rw [hh]; exact LinearMap.mem_range_self h x)
  have hbij : Function.Bijective H := by
    constructor
    · intro a b hab
      exact hinj (congrArg Subtype.val hab)
    · intro y
      obtain ⟨x, hx⟩ := (show (y : Y) ∈ h.range by rw [← hh]; exact y.2)
      refine ⟨x, ?_⟩
      apply Subtype.ext
      rw [LinearMap.codRestrict_apply]
      exact hx
  exact ⟨LinearEquiv.ofBijective H hbij⟩

/-- **One degree of the Mayer–Vietoris computation, directly in terms of `L.d`.**  If the
Mayer–Vietoris map `L.d (k,0) : H_k(A ∩ B) → H_k(A) ⊞ H_k(B)` is surjective, then the `X`-slot
in degree `k` is the kernel of the next map `L.d (k-1,0)`. -/
theorem step_iso_direct (L : Work.HomologyMV.MVLES) (k : ℤ) (hk : 1 ≤ k)
    (hsurj : Function.Surjective (L.d (k, 0)).hom) :
    Nonempty (L.H (k, 2) ≅ ModuleCat.of ℤ ↥((L.d (k - 1, 0)).hom.ker)) := by
  obtain ⟨e⟩ := isoKer_of_surjective'
    (L.d (k, 0)).hom (L.d (k, 1)).hom (L.d (k, 2)).hom (L.d (k - 1, 0)).hom
    (L.exact (k, 0)) (L.exact (k, 1)) (L.exact (k, 2))
    (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨e.toModuleIso⟩

/-- **The Mayer–Vietoris computation of `H_*(M̂)`, in the "properties" form** used by the lead:
the hypotheses are surjectivity of the Mayer–Vietoris map `L.d (k,0)` in positive degrees and an
identification of its kernel with `kerModel k` in non-negative degrees, together with the
degree-`0` identification of `H_0(M̂)`.  The conclusion is `H_k(M̂) ≅ Sol k` in every degree `k`,
i.e. `ℤ` for `k = 0, 4` and `0` otherwise.

The identifications `eM`, `eN` of the first two slots with the free models are part of the
interface but are not needed for this computation: the surjectivity and kernel data are already
given directly for the Mayer–Vietoris differential. -/
theorem mv_homology_of_props (L : Work.HomologyMV.MVLES)
    (eM : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelM k ≅ L.H (k, 0)))
    (eN : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelN k ≅ L.H (k, 1)))
    (hsurj : ∀ k : ℤ, 1 ≤ k → Function.Surjective (L.d (k, 0)).hom)
    (hker : ∀ k : ℤ, 0 ≤ k → Nonempty ((L.d (k, 0)).hom.ker ≃ₗ[ℤ] ↥(Work.HomologyMV.kerModel k)))
    (h0 : Nonempty (L.H (0, 2) ≅ Work.HomologyMV.Sol 0)) (k : ℕ) :
    Nonempty (L.H ((k : ℤ), 2) ≅ Work.HomologyMV.Sol k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using h0
  · have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
    obtain ⟨e1⟩ := step_iso_direct L (k : ℤ) hk1 (hsurj (k : ℤ) hk1)
    obtain ⟨e2⟩ := hker ((k : ℤ) - 1) (by omega)
    obtain ⟨e3⟩ := Work.HomologyMV.kerModel_succ_iso_Sol k hk
    exact ⟨e1 ≪≫ e2.toModuleIso ≪≫ e3⟩

end

end Work.BridgeSquare
