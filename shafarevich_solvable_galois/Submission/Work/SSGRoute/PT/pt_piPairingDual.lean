import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators

namespace Work.SSGRoute.PT

/-- **Finite-product duality.**  For a finite index type `F` and finite `𝔽_p`-modules `X i`, `Y i`
paired by non-degenerate `β i`, and any submodule `D ≤ ∏ i, Y i`, every `q ∉ D` is separated from
`D` by an element `x` of the product `∏ i, X i`: `x` annihilates `D` but not `q`
(`∑ i, β i (x i) (· i)` is the product pairing). -/
theorem pt_piPairingDual
    (p : ℕ) [Fact p.Prime]
    {F : Type*} [Fintype F]
    {X Y : F → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module (ZMod p) (X i)]
    [∀ i, Finite (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module (ZMod p) (Y i)]
    [∀ i, Finite (Y i)]
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (hβL : ∀ i, ∀ x : X i, (∀ y : Y i, β i x y = 0) → x = 0)
    (hβR : ∀ i, ∀ y : Y i, (∀ x : X i, β i x y = 0) → y = 0)
    (D : Submodule (ZMod p) (∀ i, Y i)) (q : ∀ i, Y i) (hq : q ∉ D) :
    ∃ x : ∀ i, X i,
      (∀ d ∈ D, ∑ i, β i (x i) (d i) = 0) ∧ (∑ i, β i (x i) (q i) ≠ 0) := by
  classical
  -- The "coordinate" map `x ↦ (fun i => β i (x i))`, landing in the product of the duals of the
  -- `Y i`.
  let Ψ : (∀ i, X i) →ₗ[ZMod p] (∀ i, Y i →ₗ[ZMod p] ZMod p) :=
    LinearMap.pi (fun i => (β i).comp (LinearMap.proj i))
  -- The product pairing `Φ`, obtained from `Ψ` through the canonical linear equivalence
  -- `LinearMap.lsum` between functionals on a finite product and families of functionals.
  let Φ : (∀ i, X i) →ₗ[ZMod p] (∀ i, Y i) →ₗ[ZMod p] ZMod p :=
    (LinearMap.lsum (ZMod p) Y (ZMod p)).toLinearMap.comp Ψ
  have hΦ : ∀ (x : ∀ i, X i) (y : ∀ i, Y i), Φ x y = ∑ i, β i (x i) (y i) := by
    intro x y
    simp [Φ, Ψ, LinearMap.lsum_apply, LinearMap.pi_apply, LinearMap.sum_apply]
  -- Each `β i` is injective on the left, by non-degeneracy.
  have hInjL : ∀ i, Function.Injective ⇑(β i) := by
    intro i
    rw [← LinearMap.ker_eq_bot]
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    exact hβL i x (fun y => by
      have := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y
      simpa using this)
  -- Each `β i` is injective on the right, by non-degeneracy.
  have hInjR : ∀ i, Function.Injective ⇑(β i).flip := by
    intro i
    rw [← LinearMap.ker_eq_bot]
    refine le_antisymm ?_ bot_le
    intro y hy
    rw [Submodule.mem_bot]
    exact hβR i y (fun x => by
      have := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) x
      simpa [LinearMap.flip_apply] using this)
  -- Hence each `β i` is a perfect pairing (finite-dimensional spaces over a field).
  have hpp : ∀ i, (β i).IsPerfPair := fun i =>
    LinearMap.IsPerfPair.of_injective (hInjL i) (hInjR i)
  -- In particular it realises every functional on `Y i`.
  have hbij : ∀ i, Function.Bijective ⇑(β i) := fun i => by
    have := hpp i
    exact LinearMap.IsPerfPair.bijective_left (β i)
  -- Consequently the product pairing `Φ` is surjective onto the dual of `∏ i, Y i`.
  have hsurj : Function.Surjective Φ := by
    intro φ
    -- Decompose `φ` into its coordinate functionals.
    let g : ∀ i, Y i →ₗ[ZMod p] ZMod p := fun i => φ.comp (LinearMap.single (ZMod p) Y i)
    have hg : LinearMap.lsum (ZMod p) Y (ZMod p) g = φ := by
      have hsymm : (LinearMap.lsum (ZMod p) Y (ZMod p)).symm φ = g := by
        funext i
        rfl
      rw [← hsymm, LinearEquiv.apply_symm_apply]
    -- Realise each coordinate functional by an element of `X i`.
    have hx : ∀ i, ∃ x : X i, β i x = g i := fun i => (hbij i).2 (g i)
    choose x hxmem using hx
    refine ⟨x, ?_⟩
    have hΨx : Ψ x = g := by
      funext i
      simp [Ψ, hxmem i]
    show LinearMap.lsum (ZMod p) Y (ZMod p) (Ψ x) = φ
    rw [hΨx, hg]
  -- Separation of points by the dual in the vector space `∏ i, Y i`.
  have hq' : ¬ (∀ φ : Module.Dual (ZMod p) (∀ i, Y i), φ ∈ D.dualAnnihilator → φ q = 0) :=
    fun h => hq ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff D q).mp h)
  push Not at hq'
  obtain ⟨φ, hφmem, hφq⟩ := hq'
  obtain ⟨x, hx⟩ := hsurj φ
  refine ⟨x, ?_, ?_⟩
  · intro d hd
    rw [← hΦ x d, hx]
    exact (Submodule.mem_dualAnnihilator φ).mp hφmem d hd
  · rw [← hΦ x q, hx]
    exact hφq

end Work.SSGRoute.PT
