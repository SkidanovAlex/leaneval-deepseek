import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.RingTheory.TotallySplit

set_option linter.style.haveILetI false

open scoped BigOperators

noncomputable section

namespace Commons.Lattice.Module

/-- In a free `ℤ`-module of rank `r`, any `r` generators form a basis (are linearly
independent).  Equivalently: a surjective linear map `ℤ^r → M` with `M` free of rank `r`
is injective, because it is an isomorphism after composing with the basis representation. -/
private theorem linearIndependent_of_generating_of_finrank {M : Type*} [AddCommGroup M]
    [Module ℤ M] [Module.Free ℤ M] {r : ℕ} (hr : Module.finrank ℤ M = r)
    (v : Fin r → M) (hspan : ⊤ ≤ Submodule.span ℤ (Set.range v)) :
    LinearIndependent ℤ v := by
  classical
  by_cases h0 : r = 0
  · subst h0
    rw [linearIndependent_iff]
    intro l hl
    apply Finsupp.ext
    intro i
    exact Fin.elim0 i
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    haveI : Module.Finite ℤ M := Module.finite_of_finrank_eq_succ hr
    let b : Module.Basis (Fin (Nat.succ n)) ℤ M := Module.finBasisOfFinrankEq ℤ M hr
    let F : (Fin (Nat.succ n) →₀ ℤ) →ₗ[ℤ] M := Finsupp.linearCombination ℤ v
    have hFrange : LinearMap.range F = ⊤ := by
      rw [Finsupp.range_linearCombination]
      exact le_antisymm le_top hspan
    have hFsurj : Function.Surjective F := LinearMap.range_eq_top.mp hFrange
    let e : M ≃ₗ[ℤ] (Fin (Nat.succ n) →₀ ℤ) := b.repr
    let ψ : (Fin (Nat.succ n) →₀ ℤ) →ₗ[ℤ] (Fin (Nat.succ n) →₀ ℤ) :=
      (e : M →ₗ[ℤ] (Fin (Nat.succ n) →₀ ℤ)).comp F
    have hψsurj : Function.Surjective ψ := by
      intro z
      rcases e.surjective z with ⟨y, hy⟩
      rcases hFsurj y with ⟨l, hl⟩
      refine ⟨l, ?_⟩
      simp [ψ, hl, hy]
    have hψinj : Function.Injective ψ :=
      Module.End.injective_of_surjective ℤ (Fin (Nat.succ n) →₀ ℤ) hψsurj
    have hFinj : Function.Injective F := by
      intro a b hab
      apply hψinj
      simp [ψ, hab]
    rw [linearIndependent_iff]
    intro l hl
    exact hFinj (by simpa using hl)

/-- The main statement. -/
theorem generators_basis_of_finrank {E : Type*} [AddCommGroup E] [Module ℤ E]
    (M : Submodule ℤ E) [Module.Free ℤ M] {r : ℕ} (hr : Module.finrank ℤ M = r)
    (w : Fin r → E) (hw : ∀ i, w i ∈ M)
    (hspan : ∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range w)) :
    LinearIndependent ℤ w := by
  classical
  let v : Fin r → (↥M) := fun i => ⟨w i, hw i⟩
  let F_M : (Fin r →₀ ℤ) →ₗ[ℤ] (↥M) := Finsupp.linearCombination ℤ v
  let F_E : (Fin r →₀ ℤ) →ₗ[ℤ] E := Finsupp.linearCombination ℤ w
  let valH : ↥M →+ E :=
    { toFun := fun x => (x : E)
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  have hterm : ∀ (a : ℤ) (x : ↥M),
      valH ((AddCommGroup.toIntModule ↥M).smul a x) =
        (inferInstance : Module ℤ E).smul a (x : E) := by
    intro a x
    calc
      valH ((AddCommGroup.toIntModule ↥M).smul a x) =
          (((AddCommGroup.toIntModule ↥M).smul a x : ↥M) : E) := rfl
      _ = ((M.module.smul a x : ↥M) : E) := by
          congr 1
          rw [int_smul_eq_zsmul (AddCommGroup.toIntModule ↥M) a x,
              int_smul_eq_zsmul M.module a x]
      _ = (inferInstance : Module ℤ E).smul a (x : E) := Submodule.coe_smul a x
  have hval : ∀ l : Fin r →₀ ℤ, ((F_M l : ↥M) : E) = F_E l := by
    let f : (Fin r →₀ ℤ) →+ E := valH.comp F_M.toAddMonoidHom
    let g : (Fin r →₀ ℤ) →+ E := F_E.toAddMonoidHom
    have hfg : f = g := by
      apply Finsupp.addHom_ext
      intro a b
      change valH ((Finsupp.linearCombination ℤ v) (Finsupp.single a b)) =
        (Finsupp.linearCombination ℤ w) (Finsupp.single a b)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      change valH ((AddCommGroup.toIntModule ↥M).smul b (v a)) =
        (inferInstance : Module ℤ E).smul b (w a)
      simpa [v] using hterm b (v a)
    intro l
    change f l = g l
    exact congrArg (fun h : (Fin r →₀ ℤ) →+ E => h l) hfg
  have hspanM : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro x hx
    rw [← Finsupp.range_linearCombination]
    rw [LinearMap.mem_range]
    have hxE : (x : E) ∈ Submodule.span ℤ (Set.range w) := hspan x.2
    have hxErange : (x : E) ∈ LinearMap.range F_E := by
      change (x : E) ∈ LinearMap.range (Finsupp.linearCombination ℤ w)
      rw [Finsupp.range_linearCombination]
      exact hxE
    rcases hxErange with ⟨l, hl⟩
    refine ⟨l, ?_⟩
    apply Subtype.ext
    rw [hval l, hl]
  have hli : LinearIndependent ℤ v :=
    linearIndependent_of_generating_of_finrank (M := ↥M) hr v hspanM
  rw [linearIndependent_iff]
  intro l hl
  have hlin : ∀ l : Fin r →₀ ℤ, (Finsupp.linearCombination ℤ v) l = 0 → l = 0 :=
    (linearIndependent_iff.mp hli)
  have hFM0 : (Finsupp.linearCombination ℤ v) l = 0 := by
    apply Subtype.ext
    rw [hval l, hl]
    rfl
  exact hlin l hFM0

end Commons.Lattice.Module