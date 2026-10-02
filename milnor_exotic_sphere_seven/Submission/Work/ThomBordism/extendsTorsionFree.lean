import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Purity of a free submodule of a torsion-free `ℤ`-module along which all functionals extend

**Mathematics.**  Let `Z` be a torsion-free `ℤ`-module (an abelian group with no torsion) and let
`B ⊆ Z` be a submodule which is *free* as a `ℤ`-module and such that every `ℤ`-linear functional
`B →ₗ[ℤ] ℤ` extends to a functional `Z →ₗ[ℤ] ℤ`.  Then `B` is *pure* in `Z`: if `N • z ∈ B` for a
positive integer `N`, then `z ∈ B`.

**Proof.**  Let `(b i)` be a `ℤ`-basis of `B` and, for each `i`, let `ψ i : Z →ₗ[ℤ] ℤ` be an
extension of the coordinate functional `b.coord i : B →ₗ[ℤ] ℤ` (extensions exist by hypothesis).
Write `bz := N • z ∈ B`; the basis expansion of `bz` reads `bz = ∑ᵢ cᵢ • bᵢ` with
`cᵢ = b.repr bz i`, a finite sum.  Applying the extension `ψ i` to the identity `bz = N • z`
gives `cᵢ = ψ i (N • z) = N * ψ i z`, so `N • z = N • ∑ᵢ (ψ i z) • bᵢ`, and the right-hand side is
`N` times an element of `B`.  Since `Z` is torsion-free, `N` can be cancelled, and `z` is exhibited
as the element `∑ᵢ (ψ i z) • bᵢ ∈ B`.

Note the `ℤ`-action is used throughout in its canonical (`zsmul`) form, matching the instance used
for `hz`; `int_smul_eq_zsmul` bridges it with the action coming from a `Module ℤ` structure.
-/

namespace Work.ThomBordism

/-- A `ℤ`-multiple of a finite sum, for the canonical `zsmul` action of `ℤ` on an `AddCommGroup`. -/
private theorem zsmul_finset_sum {α : Type*} [AddCommGroup α] {γ : Type*} (s : Finset γ) (n : ℤ)
    (f : γ → α) : n • (∑ i ∈ s, f i) = ∑ i ∈ s, n • f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, zsmul_add, ih]

theorem extendsTorsionFree {Z : Type*} [AddCommGroup Z] [Module ℤ Z]
    [Module.IsTorsionFree ℤ Z] (B : Submodule ℤ Z) (hB : Module.Free ℤ ↥B)
    (hext : ∀ φ : B →ₗ[ℤ] ℤ, ∃ ψ : Z →ₗ[ℤ] ℤ, ∀ b : B, ψ (b : Z) = φ b)
    (z : Z) (N : ℕ) (hN : 0 < N) (hz : (N : ℤ) • z ∈ B) : z ∈ B := by
  classical
  have hBinst := hB
  -- a `ℤ`-basis of the free module `B` and the element `N • z` of `B`
  let ι := Module.Free.ChooseBasisIndex ℤ ↥B
  let b : Module.Basis ι ℤ ↥B := Module.Free.chooseBasis ℤ ↥B
  let bz : ↥B := ⟨(N : ℤ) • z, hz⟩
  -- the coordinate functional of the basis, extended to `Z`
  let ψ : ι → (Z →ₗ[ℤ] ℤ) := fun i => Classical.choose (hext (b.coord i))
  have hψ : ∀ (i : ι) (x : ↥B), ψ i (x : Z) = b.coord i x :=
    fun i => Classical.choose_spec (hext (b.coord i))
  -- the basis expansion of `bz`, first in `B` and then, after coercing, in `Z`
  have hexp : bz = ∑ i ∈ (b.repr bz).support, (b.repr bz i) • b i := by
    conv_lhs => rw [← b.linearCombination_repr bz]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hexpZ : (bz : Z) = ∑ i ∈ (b.repr bz).support, (b.repr bz i) • (b i : Z) := by
    have h := congrArg (fun x : ↥B => (x : Z)) hexp
    simpa using h
  -- the coordinate of `bz` in the `i`-th basis direction is `N` times the value `ψ i z`
  have hcoord : ∀ i : ι, b.repr bz i = (N : ℤ) * ψ i z := by
    intro i
    have h1 : b.repr bz i = ψ i (bz : Z) := by
      rw [← Module.Basis.coord_apply b i bz]
      exact (hψ i bz).symm
    rw [h1]
    have h2 : (bz : Z) = (N : ℤ) • z := rfl
    rw [h2, map_zsmul, zsmul_eq_mul]
    simp
  -- the candidate preimage of `z` under multiplication by `N`, an element of `B`
  let W : Z := ∑ i ∈ (b.repr bz).support, (ψ i z) • (b i : Z)
  have hWdef : W = ∑ i ∈ (b.repr bz).support, (ψ i z) • (b i : Z) := rfl
  have hkey : (N : ℤ) • z = (N : ℤ) • W := by
    rw [show (N : ℤ) • z = (bz : Z) from rfl, hexpZ, hWdef, zsmul_finset_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord i, mul_zsmul]
  -- cancellation of `N`, using torsion-freeness of `Z`
  have hAddTors : IsAddTorsionFree Z := IsAddTorsionFree.of_isTorsionFree ℤ Z
  have hne : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hzW : z = W := zsmul_right_injective hne hkey
  -- `W` is a `ℤ`-linear combination of basis vectors of `B`, hence lies in `B`
  rw [hzW, hWdef]
  exact B.toAddSubgroup.sum_mem (fun i _ => (B.toAddSubgroup).zsmul_mem (b i).2 (ψ i z))

end Work.ThomBordism
