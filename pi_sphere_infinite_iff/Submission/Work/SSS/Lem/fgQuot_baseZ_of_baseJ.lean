import Mathlib
import Submission.Work.SSS.baseRowDefs

/-!
# Finiteness of `baseZ ξ m r / baseZ ξ m (r+1)` from that of `baseJ ξ m r / baseJ ξ m (r+1)`

`baseZ ξ m r` is the preimage of `baseJ ξ m r` under the connecting map `k : E¹_{m+1,0} → H_m(F_m)`.
The key point of this file is the elementary linear-algebra fact that the preimage of a finitely
generated quotient is finitely generated: if `Z' ≤ Z` are submodules of `B` and `Z/Z'` is finitely
generated, then for any linear map `f : A → B` the quotient `f⁻¹Z / f⁻¹Z'` is finitely generated.

Indeed the map `f⁻¹Z → Z/Z'`, `x ↦ f x + Z'`, has kernel exactly `f⁻¹Z'`, so `f⁻¹Z / f⁻¹Z'` is
isomorphic to a submodule of `Z/Z'`; over `ℤ` (a Noetherian ring) submodules of finitely generated
modules are finitely generated.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.SSS.Lem

open CategoryTheory CategoryTheory.Limits

/-- If `Z / Z'` is finitely generated, then so is `f ⁻¹' Z / f ⁻¹' Z'` for any linear map `f`
(over a Noetherian ring). -/
lemma fgQuot_comap_of_isNoetherianRing {R A B : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (Z Z' : Submodule R B) (h : Work.SSS.FgQuot Z' Z) :
    Work.SSS.FgQuot (Submodule.comap f Z') (Submodule.comap f Z) := by
  rw [Work.SSS.FgQuot] at h ⊢
  set M : Submodule R A := Submodule.comap f Z with hM
  set K : Submodule R A := Submodule.comap f Z' with hK
  -- The map `M → B/Z'`, `x ↦ f x + Z'`, whose range lies in `Z/Z'`.
  let ψ : M →ₗ[R] B ⧸ Z' := (Submodule.mkQ Z') ∘ₗ (f ∘ₗ M.subtype)
  have hψrange_le : ψ.range ≤ Z.map (Submodule.mkQ Z') := by
    intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact Submodule.mem_map.mpr ⟨f x, x.2, rfl⟩
  -- Hence its range is finitely generated, by Noetherianity of `R`.
  have hψrange : (ψ.range).FG :=
    Submodule.FG.of_le (S := ψ.range) (T := Z.map (Submodule.mkQ Z')) h hψrange_le
  -- The map `M → A/K` exhibiting `M.map K.mkQ`.
  let g : M →ₗ[R] A ⧸ K := (Submodule.mkQ K) ∘ₗ M.subtype
  -- The two maps have the same kernel.
  have hker : ψ.ker = g.ker := by
    ext x
    simp only [LinearMap.mem_ker, ψ, g, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, K, Submodule.mem_comap]
  -- First isomorphism theorem for `ψ`: `M ⧸ ψ.ker` is finitely generated.
  have h1 : (⊤ : Submodule R (M ⧸ ψ.ker)).FG :=
    Submodule.fg_of_linearEquiv (LinearMap.quotKerEquivRange ψ)
      ((Submodule.fg_top ψ.range).mpr hψrange)
  rw [hker] at h1
  -- The range of `g` is `M.map K.mkQ`.
  have hg : g.range = M.map (Submodule.mkQ K) := by
    rw [LinearMap.range_eq_map, Submodule.map_comp, Submodule.map_subtype_top]
  -- Transfer finiteness across the isomorphism `M.map K.mkQ ≃ M ⧸ g.ker`.
  have h2 : (⊤ : Submodule R ↥(M.map (Submodule.mkQ K))).FG :=
    Submodule.fg_of_linearEquiv
      ((LinearEquiv.ofEq _ _ hg).symm.trans (LinearMap.quotKerEquivRange g).symm) h1
  exact (Submodule.fg_top (M.map (Submodule.mkQ K))).mp h2

theorem fgQuot_baseZ_of_baseJ {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C)
    (m r : ℕ) (hr : 1 ≤ r) (h : Work.SSS.FgQuot (Work.SSS.baseJ ξ m (r + 1)) (Work.SSS.baseJ ξ m r)) :
    Work.SSS.FgQuot (Work.SSS.baseZ ξ m (r + 1)) (Work.SSS.baseZ ξ m r) := by
  have key := fgQuot_comap_of_isNoetherianRing (f := (kF ξ m 0).hom) (Work.SSS.baseJ ξ m r)
    (Work.SSS.baseJ ξ m (r + 1)) h
  exact key

end Work.SSS.Lem
