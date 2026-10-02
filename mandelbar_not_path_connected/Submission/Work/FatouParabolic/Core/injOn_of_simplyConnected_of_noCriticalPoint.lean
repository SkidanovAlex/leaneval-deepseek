import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.isOpen_puncturedBasin
import Submission.Work.FatouParabolic.Core.isBounded_puncturedBasin_of_escape
import Submission.Work.FatouParabolic.Basin.mapsTo_puncturedBasin
import Submission.Work.FatouParabolic.Basin.preimage_mem_puncturedBasin
import Submission.Work.FatouParabolic.Core.isLocalHomeomorphOn_of_deriv_ne_zero
import Submission.Work.FatouParabolic.Core.isProperMap_of_escapeBound
import Submission.Work.FatouParabolic.Core.finite_fiber_of_isLocalHomeomorphOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

open Filter
open scoped Topology

/-!
# Injectivity of `F` on the punctured parabolic basin, from simple connectivity

Let `F : ℂ → ℂ` be a holomorphic *surjection* with a fixed point `z₀`, at least doubling the
modulus outside a disc (`BasinEscape F`), whose punctured basin
`Ω = puncturedBasin F z₀ = {z | F^[n] z → z₀ and F^[n] z ≠ z₀ for all n}`
is simply connected and carries no critical point of `F`.  Then `F` is injective on `Ω`.

The proof is the standard "a covering of a simply connected space has one sheet":

* `Ω` is invariant under `F` (`mem_puncturedBasin_of_map_mem` and
  `Basin.mapsTo_puncturedBasin`), i.e. `F ⁻¹' Ω = Ω`;
* `F` is proper (`isProperMap_of_escapeBound`), hence a closed map, and it has no critical point
  on `Ω`, so it is a local homeomorphism there (`isLocalHomeomorphOn_of_deriv_ne_zero`);
* fibres over points of `Ω` are compact (properness) and discrete (local homeomorphism), hence
  finite (`finite_fiber_of_isLocalHomeomorphOn`); so `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`
  makes `F` a covering map on `Ω`;
* restricting to the invariant set `F ⁻¹' Ω = Ω` gives a covering map `↥Ω → ↥Ω` of the simply
  connected space `↥Ω` onto itself, which is injective (`injective_of_isCoveringMap_of_simplyConnected`).
-/

/-- **Invariance of the punctured basin under `F`.**  If `F z₀ = z₀` and `F w` lies in the
punctured basin of `z₀`, then so does `w`: the orbit of `w` is the orbit of `F w` shifted by one
step, and `w` itself cannot be `z₀` (else `F w = z₀`). -/
theorem mem_puncturedBasin_of_map_mem {F : ℂ → ℂ} {z₀ w : ℂ} (hfix : F z₀ = z₀)
    (hw : F w ∈ Work.FatouParabolic.puncturedBasin F z₀) :
    w ∈ Work.FatouParabolic.puncturedBasin F z₀ := by
  rw [Work.FatouParabolic.mem_puncturedBasin] at hw ⊢
  obtain ⟨hne, hconv⟩ := hw
  refine ⟨?_, ?_⟩
  · -- the orbit of `w` never attains `z₀`
    intro n
    cases n with
    | zero =>
      intro h
      simp only [Function.iterate_zero_apply] at h
      exact hne 0 (by rw [Function.iterate_zero_apply, h, hfix])
    | succ k =>
      rw [Function.iterate_succ_apply]
      exact hne k
  · -- the orbit of `w` converges to `z₀`, being the orbit of `F w` shifted by one step
    rw [Work.FatouParabolic.mem_basin] at hconv ⊢
    have he : (fun n : ℕ => (F^[n]) (F w)) = fun n : ℕ => (F^[n + 1]) w := by
      funext n
      rw [Function.iterate_succ_apply]
    rw [he] at hconv
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => (F^[k]) w) 1).mp hconv

/-- **The invariance of the punctured basin, as an equality of sets.** -/
theorem preimage_puncturedBasin_eq {F : ℂ → ℂ} {z₀ : ℂ} (hfix : F z₀ = z₀) :
    F ⁻¹' Work.FatouParabolic.puncturedBasin F z₀ = Work.FatouParabolic.puncturedBasin F z₀ := by
  ext w
  simp only [Set.mem_preimage]
  exact ⟨fun h => mem_puncturedBasin_of_map_mem hfix h,
    fun h => Work.FatouParabolic.Basin.mapsTo_puncturedBasin hfix h⟩

/-- **`F` is a covering map on the punctured basin.**  Holomorphic, proper on `ℂ` (which the
escape bound provides), and a local homeomorphism on `Ω` because `deriv F` does not vanish
there. -/
theorem isCoveringMapOn_puncturedBasin {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : Differentiable ℂ F) (hfix : F z₀ = z₀) (hesc : Work.FatouParabolic.BasinEscape F)
    (hnocrit : ∀ w ∈ Work.FatouParabolic.puncturedBasin F z₀, deriv F w ≠ 0) :
    IsCoveringMapOn F (Work.FatouParabolic.puncturedBasin F z₀) := by
  have hinv := preimage_puncturedBasin_eq (F := F) (z₀ := z₀) hfix
  have hproper : IsProperMap F := isProperMap_of_escapeBound hF.continuous hesc
  have hloc : IsLocalHomeomorphOn F (Work.FatouParabolic.puncturedBasin F z₀) :=
    isLocalHomeomorphOn_of_deriv_ne_zero hF hnocrit
  have hloc' : IsLocalHomeomorphOn F (F ⁻¹' Work.FatouParabolic.puncturedBasin F z₀) := by
    rw [hinv]; exact hloc
  have hfin : ∀ x ∈ Work.FatouParabolic.puncturedBasin F z₀, (F ⁻¹' {x}).Finite :=
    finite_fiber_of_isLocalHomeomorphOn hloc'
      fun x _ => hproper.isCompact_preimage isCompact_singleton
  exact hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hfin hloc'


/-! ## The topological endgame

A covering map `p : E → X` with *path connected* total space `E` and *simply connected* base
`X` is injective: if `p e₁ = p e₂` and `γ` is a path from `e₁` to `e₂`, then `p ∘ γ` is a loop
at `p e₁`, which is null-homotopic because `X` is simply connected.  Lifting that homotopy
relative to the endpoints (starting at `e₁`) shows that `γ` is homotopic relative to the
endpoints to the constant path at `e₁`: indeed the lift of the lifted homotopy at time `1` is a
lift of the constant loop, hence constant, and its endpoint is `e₁` on the one hand and `γ 1 = e₂`
on the other. -/
private theorem injective_of_isCoveringMap_of_simplyConnected' {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (hp : IsCoveringMap p) [SimplyConnectedSpace X]
    [PathConnectedSpace E] : Function.Injective p := by
  intro e₁ e₂ he
  let γ : Path e₁ e₂ := PathConnectedSpace.somePath e₁ e₂
  -- The loop `p ∘ γ` at `p e₁ = p e₂`.
  let P : Path (p e₁) (p e₁) :=
    { toFun := fun t => p (γ t)
      continuous_toFun := hp.continuous.comp γ.continuous
      source' := by rw [γ.source]
      target' := by rw [γ.target]; exact he.symm }
  let Q : Path (p e₁) (p e₁) := Path.refl (p e₁)
  have hPQ := SimplyConnectedSpace.paths_homotopic P Q
  have h₀ : P.toContinuousMap 0 = p e₁ := by
    show p (γ 0) = p e₁
    rw [γ.source]
  have h₁ : Q.toContinuousMap 0 = p e₁ := rfl
  have key := hp.liftPath_apply_one_eq_of_homotopicRel hPQ e₁ h₀ h₁
  have hP : hp.liftPath P.toContinuousMap e₁ h₀ = γ.toContinuousMap :=
    (hp.eq_liftPath_iff' (γ := P.toContinuousMap) (e := e₁) h₀).mpr
      ⟨funext fun t => rfl, γ.source⟩ |>.symm
  have hQ : hp.liftPath Q.toContinuousMap e₁ h₁ = ContinuousMap.const unitInterval e₁ :=
    (hp.eq_liftPath_iff' (γ := Q.toContinuousMap) (e := e₁) h₁).mpr
      ⟨funext fun t => rfl, rfl⟩ |>.symm
  rw [hP, hQ] at key
  simpa [γ.target] using key.symm

theorem injOn_of_simplyConnected_of_noCriticalPoint {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : Differentiable ℂ F) (hfix : F z₀ = z₀) (hsurj : Function.Surjective F)
    (hesc : Work.FatouParabolic.BasinEscape F)
    (hsc : Work.FatouParabolic.ParabolicBasinSimplyConnected F z₀)
    (hnocrit : ∀ w ∈ Work.FatouParabolic.puncturedBasin F z₀, deriv F w ≠ 0) :
    Set.InjOn F (Work.FatouParabolic.puncturedBasin F z₀) := by
  haveI : SimplyConnectedSpace ↥(Work.FatouParabolic.puncturedBasin F z₀) := hsc
  have hinv := preimage_puncturedBasin_eq (F := F) (z₀ := z₀) hfix
  -- `F` is a covering map on the basin, hence so is its restriction to the basin
  have hcov := isCoveringMapOn_puncturedBasin hF hfix hesc hnocrit
  have hcov' : IsCoveringMap ((Work.FatouParabolic.puncturedBasin F z₀).restrictPreimage F) :=
    hcov.isCoveringMap_restrictPreimage
  -- the domain of that covering is `F ⁻¹' Ω = Ω`, which is simply connected
  haveI : PathConnectedSpace ↥(F ⁻¹' Work.FatouParabolic.puncturedBasin F z₀) := by
    rw [hinv]; infer_instance
  intro x hx y hy hxy
  have hx' : F x ∈ Work.FatouParabolic.puncturedBasin F z₀ :=
    Work.FatouParabolic.Basin.mapsTo_puncturedBasin hfix hx
  have hy' : F y ∈ Work.FatouParabolic.puncturedBasin F z₀ :=
    Work.FatouParabolic.Basin.mapsTo_puncturedBasin hfix hy
  have heq : (⟨x, hx'⟩ : ↥(F ⁻¹' Work.FatouParabolic.puncturedBasin F z₀))
      = ⟨y, hy'⟩ :=
    injective_of_isCoveringMap_of_simplyConnected' hcov' (Subtype.ext hxy)
  exact congrArg Subtype.val heq

end Work.FatouParabolic.Core
