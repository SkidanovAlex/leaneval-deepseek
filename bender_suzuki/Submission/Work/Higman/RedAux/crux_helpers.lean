import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Work.Higman.RedAux

open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- **Odd-order invariant complement.**  Let `σ` be an `𝔽₂`-linear automorphism of a vector space
`V` with `σ ^ e = 1` for an odd natural number `e`, and let `S ≤ V` be a `σ`-invariant subspace.
Then `S` has a `σ`-invariant complement: there is a subspace `N` with `σ N ⊆ N`, `S ⊔ N = ⊤` and
`S ⊓ N = ⊥`.  (Maschke, via the averaging endomorphism `∑_{k<e} σ^k ∘ π ∘ σ^{-k}`: since `e` is
odd it equals `1` in `𝔽₂`.) -/
theorem odd_compl (σ : V ≃ₗ[ZMod 2] V) {e : ℕ} (he : Odd e) (hσ : σ ^ e = 1)
    (S : Submodule (ZMod 2) V) (hS : ∀ x ∈ S, σ x ∈ S) :
    ∃ N : Submodule (ZMod 2) V, (∀ x ∈ N, σ x ∈ N) ∧ S ⊔ N = ⊤ ∧ S ⊓ N = ⊥ := by
  classical
  have he1 : 1 ≤ e := he.pos
  have hec : (e : ZMod 2) = 1 := by
    obtain ⟨m, hm⟩ := he
    rw [hm]
    push_cast
    rw [show ((2 : ZMod 2)) = 0 from by decide]
    ring
  have hesmul : ∀ x : V, e • x = x := by
    intro x
    have h1 : ((e : ZMod 2)) • x = e • x := Nat.cast_smul_eq_nsmul (ZMod 2) e x
    rw [← h1, hec, one_smul]
  -- `σ ^ k` preserves `S`
  have hSpow : ∀ k : ℕ, ∀ x ∈ S, (σ ^ k) x ∈ S := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [show (σ ^ (k + 1)) = σ * σ ^ k from pow_succ' σ k, LinearEquiv.mul_apply]
      exact hS _ (ih x hx)
  -- `σ.symm` preserves `S`
  have hSsymm : ∀ x ∈ S, σ.symm x ∈ S := by
    intro x hx
    have h1 : σ ((σ ^ (e - 1)) x) = x := by
      rw [← LinearEquiv.mul_apply, ← pow_succ', Nat.sub_add_cancel he1, hσ]
      rfl
    have h2 : σ.symm x = (σ ^ (e - 1)) x := by
      conv_lhs => rw [← h1]
      rw [LinearEquiv.symm_apply_apply]
    rw [h2]
    exact hSpow (e - 1) x hx
  -- `(σ ^ k).symm` preserves `S`
  have hSpowsymm : ∀ k : ℕ, ∀ x ∈ S, ((σ ^ k).symm) x ∈ S := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have h0 : ((σ ^ 0).symm : V ≃ₗ[ZMod 2] V) x = x := by
        apply (σ ^ 0).injective
        rw [LinearEquiv.apply_symm_apply]
        simp
      rw [h0]; exact hx
    | succ k ih =>
      intro x hx
      have h1 : ((σ ^ (k + 1)).symm : V ≃ₗ[ZMod 2] V) x = ((σ ^ k).symm) (σ.symm x) := by
        apply (σ ^ (k + 1)).injective
        rw [LinearEquiv.apply_symm_apply, show (σ ^ (k + 1)) = σ * σ ^ k from pow_succ' σ k,
          LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rw [h1]
      exact ih _ (hSsymm x hx)
  -- a linear retraction onto `S`, and the averaged endomorphism
  obtain ⟨N₀, hN₀⟩ := S.exists_isCompl
  set π : V →ₗ[ZMod 2] V := S.projection N₀ hN₀ with hπdef
  have hπmem : ∀ x, π x ∈ S := fun x => Submodule.projection_apply_mem hN₀ x
  have hπS : ∀ x ∈ S, π x = x := fun x hx => Submodule.projection_apply_of_mem_left hN₀ hx
  set Q : ℕ → V →ₗ[ZMod 2] V :=
    fun k => (σ ^ k).toLinearMap.comp (π.comp (σ ^ k).symm.toLinearMap) with hQdef
  set P : V →ₗ[ZMod 2] V := ∑ k ∈ Finset.range e, Q k with hPdef
  have hPapply : ∀ x, P x = ∑ k ∈ Finset.range e, Q k x := by
    intro x; rw [hPdef, LinearMap.sum_apply]
  have hPmem : ∀ x, P x ∈ S := by
    intro x
    rw [hPapply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    exact hSpow k _ (hπmem _)
  have hQfix : ∀ k, ∀ x ∈ S, Q k x = x := by
    intro k x hx
    change (σ ^ k) (π (((σ ^ k).symm) x)) = x
    rw [hπS _ (hSpowsymm k x hx)]
    simp
  have hPfix : ∀ x ∈ S, P x = x := by
    intro x hx
    rw [hPapply, Finset.sum_congr rfl (fun k _ => hQfix k x hx), Finset.sum_const,
      Finset.card_range]
    exact hesmul x
  -- the cyclic shift `∑_{k<e} Q_{k+1} = ∑_{k<e} Q_k`
  have hQe : Q e = Q 0 := by
    rw [hQdef]
    simp only [hσ, pow_zero]
  have hshift : ∑ k ∈ Finset.range e, Q (k + 1) = ∑ k ∈ Finset.range e, Q k := by
    have h1 : ∑ k ∈ Finset.range (e + 1), Q k = ∑ k ∈ Finset.range e, Q k + Q e :=
      Finset.sum_range_succ Q e
    have h2 : ∑ k ∈ Finset.range (e + 1), Q k = ∑ k ∈ Finset.range e, Q (k + 1) + Q 0 :=
      Finset.sum_range_succ' Q e
    have key : ∑ k ∈ Finset.range e, Q k + Q e = ∑ k ∈ Finset.range e, Q (k + 1) + Q 0 := by
      rw [← h1, ← h2]
    rw [hQe] at key
    exact (add_right_cancel key).symm
  -- `σ (Q k x) = Q (k+1) (σ x)`
  have hstep : ∀ k x, σ (Q k x) = Q (k + 1) (σ x) := by
    intro k x
    show σ ((σ ^ k) (π (((σ ^ k).symm) x))) = (σ ^ (k + 1)) (π (((σ ^ (k + 1)).symm) (σ x)))
    have hB : ((σ ^ (k + 1)).symm : V ≃ₗ[ZMod 2] V) (σ x) = ((σ ^ k).symm) x := by
      apply (σ ^ (k + 1)).injective
      have hl : (σ ^ (k + 1)) (((σ ^ (k + 1)).symm) (σ x)) = σ x :=
        LinearEquiv.apply_symm_apply _ _
      have hr : (σ ^ (k + 1)) (((σ ^ k).symm) x) = σ x := by
        rw [show (σ ^ (k + 1)) = σ * σ ^ k from pow_succ' σ k, LinearEquiv.mul_apply,
          LinearEquiv.apply_symm_apply]
      rw [hl, hr]
    rw [hB]
    rw [← LinearEquiv.mul_apply, ← pow_succ']
  -- `σ` commutes with `P`
  have hcomm : ∀ x, σ (P x) = P (σ x) := by
    intro x
    calc σ (P x) = ∑ k ∈ Finset.range e, σ (Q k x) := by rw [hPapply, map_sum]
      _ = ∑ k ∈ Finset.range e, Q (k + 1) (σ x) := Finset.sum_congr rfl fun k _ => hstep k x
      _ = (∑ k ∈ Finset.range e, Q (k + 1)) (σ x) := (LinearMap.sum_apply _ _ _).symm
      _ = (∑ k ∈ Finset.range e, Q k) (σ x) := by rw [hshift]
      _ = P (σ x) := by rw [hPdef]
  refine ⟨LinearMap.ker P, ?_, ?_, ?_⟩
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hcomm x, hx, map_zero]
  · refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = P x + (x - P x) := by abel
    rw [hx]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hPmem x)) (Submodule.mem_sup_right ?_)
    rw [LinearMap.mem_ker]
    rw [map_sub, hPfix _ (hPmem x)]
    abel
  · refine bot_unique fun x hx => ?_
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hx
    show x = 0
    rw [← hx.2, hPfix x hx.1]

variable {P : Type*} [Group P]

variable {P : Type*} [Group P]

variable {P : Type*} [Group P]

/-- A central factor on the right does not change a commutator. -/
theorem commutator_mul_central_right {z : P} (hz : z ∈ Subgroup.center P) (x a : P) :
    ⁅x, a * z⁆ = ⁅x, a⁆ := by
  have hzy : ∀ y : P, z * y = y * z := fun y => (Subgroup.mem_center_iff.mp hz y).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (a * z) * x⁻¹ * (a * z)⁻¹
      = x * a * (z * x⁻¹) * z⁻¹ * a⁻¹ := by rw [mul_inv_rev]; group
    _ = x * a * (x⁻¹ * z) * z⁻¹ * a⁻¹ := by rw [hzy x⁻¹]
    _ = x * a * x⁻¹ * a⁻¹ := by group

/-- A central factor on the left does not change a commutator. -/
theorem commutator_mul_central_left {z : P} (hz : z ∈ Subgroup.center P) (x a : P) :
    ⁅x * z, a⁆ = ⁅x, a⁆ := by
  have hzy : ∀ y : P, z * y = y * z := fun y => (Subgroup.mem_center_iff.mp hz y).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc x * z * a * (x * z)⁻¹ * a⁻¹
      = x * (z * a) * z⁻¹ * x⁻¹ * a⁻¹ := by rw [mul_inv_rev]; group
    _ = x * (a * z) * z⁻¹ * x⁻¹ * a⁻¹ := by rw [hzy a]
    _ = x * a * x⁻¹ * a⁻¹ := by group

/-- `⁅u * v, a⁆ = ⁅v, a⁆ * ⁅u, a⁆` whenever `⁅v, a⁆` is central. -/
theorem commutator_mul_of_central {u v a : P} (hv : ⁅v, a⁆ ∈ Subgroup.center P) :
    ⁅u * v, a⁆ = ⁅v, a⁆ * ⁅u, a⁆ := by
  have hv' : ∀ y : P, y * ⁅v, a⁆ = ⁅v, a⁆ * y := fun y => (Subgroup.mem_center_iff.mp hv y)
  have hvv : v * a = ⁅v, a⁆ * a * v := by rw [commutatorElement_def]; group
  rw [commutatorElement_def, commutatorElement_def]
  calc u * v * a * (u * v)⁻¹ * a⁻¹
      = u * (v * a) * v⁻¹ * u⁻¹ * a⁻¹ := by rw [mul_inv_rev]; group
    _ = u * (⁅v, a⁆ * a * v) * v⁻¹ * u⁻¹ * a⁻¹ := by rw [hvv]
    _ = u * ⁅v, a⁆ * a * v * v⁻¹ * u⁻¹ * a⁻¹ := by group
    _ = ⁅v, a⁆ * u * a * v * v⁻¹ * u⁻¹ * a⁻¹ := by rw [hv' u]
    _ = ⁅v, a⁆ * (u * a * u⁻¹ * a⁻¹) := by group

/-- The universal identity `(x * y) ^ 2 = x * ⁅y, x⁆ * x * y ^ 2` (valid in every group, since
`⁅y, x⁆ * x = y * x * y⁻¹`). -/
theorem sq_mul_eq (x y : P) : (x * y) ^ 2 = x * ⁅y, x⁆ * x * y ^ 2 := by
  rw [commutatorElement_def, pow_two, pow_two]; group

/-- **The `C₄` square identity.**  If every square of `P` lies in a normal subgroup `Z`, then
every commutator lies in `Z`.  Indeed `(xy)² = x·⁅y,x⁆·x·y²` gives
`⁅y,x⁆ = (x⁻¹·x⁻¹) · (x·((xy)²·(y²)⁻¹)·x⁻¹)` with both factors in `Z`. -/
theorem commutator_mem_of_sq_mem {Z : Subgroup P} (hZn : Z.Normal)
    (hZ : ∀ x : P, x ^ 2 ∈ Z) (x y : P) : ⁅x, y⁆ ∈ Z := by
  have hid : x * ⁅y, x⁆ * x * y ^ 2 = (x * y) ^ 2 := (sq_mul_eq x y).symm
  have hc : ⁅y, x⁆ = x⁻¹ * ((x * y) ^ 2 * (y ^ 2)⁻¹) * x⁻¹ := by
    rw [← hid]; group
  have h2 : ⁅y, x⁆ = (x⁻¹ * x⁻¹) * (x * ((x * y) ^ 2 * (y ^ 2)⁻¹) * x⁻¹) := by
    rw [hc]; group
  have h1 : x⁻¹ * x⁻¹ ∈ Z := by
    have : x⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by rw [pow_two]; group
    rw [this]; exact Subgroup.inv_mem _ (hZ x)
  have h3 : x * ((x * y) ^ 2 * (y ^ 2)⁻¹) * x⁻¹ ∈ Z :=
    hZn.conj_mem _ (Subgroup.mul_mem _ (hZ (x * y)) (Subgroup.inv_mem _ (hZ y))) x
  have hyx : ⁅y, x⁆ ∈ Z := by rw [h2]; exact Subgroup.mul_mem _ h1 h3
  have : ⁅x, y⁆ = ⁅y, x⁆⁻¹ := by rw [← commutatorElement_inv x y]; group
  rw [this]; exact Subgroup.inv_mem _ hyx

end Work.Higman.RedAux
