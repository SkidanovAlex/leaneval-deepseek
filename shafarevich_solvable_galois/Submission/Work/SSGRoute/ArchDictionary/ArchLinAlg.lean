import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Two linear maps with the same kernel

A finite-dimensional linear-algebra lemma used by the `p = 2` branch of the archimedean
dictionary: if `ρ g : H →ₗ[F] V` have the same kernel and `V` is finite dimensional over a
field `F`, then there is an automorphism `Ψ` of `V` carrying `ρ` to `g`, i.e.
`Ψ (ρ b) = g b` for all `b`.

The proof is the standard one: `ρ` and `g` induce an isomorphism `τ` between their ranges
(`LinearMap.quotKerEquivRange` plus the equality of kernels), and an isomorphism of subspaces of a
finite-dimensional space extends to an automorphism (choose complements; the complements have the
same dimension).
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ArchDictionary

/-- A module over a semiring is finite if it is a finite type. -/
theorem moduleFinite_of_finite {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Finite M] : Module.Finite R M := by
  rw [Module.finite_def, ← Submodule.span_univ]
  exact Submodule.fg_span (Set.finite_univ)

/-- **Extension of an isomorphism of subspaces to an automorphism.** -/
theorem exists_linearEquiv_extend {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Module.Finite F V] (A B : Submodule F V) (τ : A ≃ₗ[F] B) :
    ∃ Ψ : V ≃ₗ[F] V, ∀ a : A, Ψ a = τ a := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl A
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl B
  have hAB : Module.finrank F A = Module.finrank F B := τ.finrank_eq
  have hCAB : Module.finrank F C + Module.finrank F A = Module.finrank F V := by
    have h := (Submodule.prodEquivOfIsCompl A C hC).finrank_eq
    rw [Module.finrank_prod] at h
    omega
  have hDAB : Module.finrank F D + Module.finrank F B = Module.finrank F V := by
    have h := (Submodule.prodEquivOfIsCompl B D hD).finrank_eq
    rw [Module.finrank_prod] at h
    omega
  have hCD : Module.finrank F C = Module.finrank F D := by omega
  let σ : C ≃ₗ[F] D := LinearEquiv.ofFinrankEq C D hCD
  refine ⟨((Submodule.prodEquivOfIsCompl A C hC).symm.trans
    ((τ.prodCongr σ).trans (Submodule.prodEquivOfIsCompl B D hD))), fun a => ?_⟩
  have h1 : (Submodule.prodEquivOfIsCompl A C hC).symm (a : V) = (a, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left A C hC a
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1]
  simp [Submodule.coe_prodEquivOfIsCompl']

/-- **The isomorphism between the ranges induced by two maps with equal kernels.** -/
theorem rangeIso_of_ker_eq {F H V : Type*} [Field F] [AddCommGroup H] [AddCommGroup V]
    [Module F H] [Module F V] (ρ g : H →ₗ[F] V) (hker : ∀ x : H, ρ x = 0 ↔ g x = 0) :
    ∃ τ : (LinearMap.range ρ) ≃ₗ[F] (LinearMap.range g),
      ∀ b : H, τ ⟨ρ b, LinearMap.mem_range_self ρ b⟩ = ⟨g b, LinearMap.mem_range_self g b⟩ := by
  have hker' : LinearMap.ker ρ = LinearMap.ker g := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    exact hker x
  refine ⟨(LinearMap.quotKerEquivRange ρ).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker').trans (LinearMap.quotKerEquivRange g)), fun b => ?_⟩
  refine Subtype.ext ?_
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivRange_symm_apply_image ρ b (LinearMap.mem_range_self ρ b),
    Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk]
  simp

/-- **Two linear maps with the same kernel differ by an automorphism of the target.** -/
theorem exists_linearEquiv_of_ker_eq {F H V : Type*} [Field F] [AddCommGroup H] [AddCommGroup V]
    [Module F H] [Module F V] [Module.Finite F V] (ρ g : H →ₗ[F] V)
    (hker : ∀ x : H, ρ x = 0 ↔ g x = 0) :
    ∃ Ψ : V ≃ₗ[F] V, ∀ b : H, Ψ (ρ b) = g b := by
  obtain ⟨τ, hτ⟩ := rangeIso_of_ker_eq ρ g hker
  obtain ⟨Ψ, hΨ⟩ := exists_linearEquiv_extend (LinearMap.range ρ) (LinearMap.range g) τ
  exact ⟨Ψ, fun b => by
    have h := hΨ ⟨ρ b, LinearMap.mem_range_self ρ b⟩
    rw [hτ b] at h
    exact h⟩

/-- **Two additive maps with the same kernel into a finite-dimensional `ℤ/nℤ`-module differ by an
automorphism of the target.**  Over `ℤ/nℤ` additivity is equivalent to linearity, so this is
`exists_linearEquiv_of_ker_eq` with the module structure on the source produced by
`AddCommGroup.zmodModule`. -/
theorem exists_addEquiv_of_ker_eq (n : ℕ) [Fact n.Prime] {H V : Type*} [AddCommGroup H]
    [AddCommGroup V] [Module (ZMod n) V] [Module.Finite (ZMod n) V] (hH : ∀ x : H, n • x = 0)
    (ρ g : H →+ V) (hker : ∀ x : H, ρ x = 0 ↔ g x = 0) :
    ∃ Ψ : V ≃+ V, ∀ b : H, Ψ (ρ b) = g b := by
  letI : Module (ZMod n) H := AddCommGroup.zmodModule hH
  obtain ⟨Ψ, hΨ⟩ := exists_linearEquiv_of_ker_eq (F := ZMod n)
    (ρ.toZModLinearMap n) (g.toZModLinearMap n) (fun x => by
      rw [AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.coe_toZModLinearMap]
      exact hker x)
  exact ⟨Ψ.toAddEquiv, fun b => hΨ b⟩

end Work.SSGRoute.ArchDictionary
