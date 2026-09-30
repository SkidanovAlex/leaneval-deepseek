import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.Charts

/-- The coefficient at `a` of `∑ m, single (u m) 1` is the number of indices `m` with `u m = a`. -/
private lemma coeff_sum_single {α : Type*} [DecidableEq α] {n : ℕ} (u : Fin n → α) (a : α) :
    (∑ m : Fin n, (Finsupp.single (u m) (1 : ℤ) : α →₀ ℤ)) a
      = ((Finset.univ.filter (fun m => u m = a)).card : ℤ) := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [← Finset.sum_filter, Finset.sum_const]
  simp

theorem sum_single_eq_iff_exists_perm {α : Type u} {n : ℕ} (u v : Fin n → α) :
    (∑ m : Fin n, (Finsupp.single (u m) (1 : ℤ) : α →₀ ℤ)) =
        (∑ m : Fin n, (Finsupp.single (v m) (1 : ℤ) : α →₀ ℤ)) ↔
      ∃ σ : Equiv.Perm (Fin n), ∀ m, v m = u (σ m) := by
  classical
  constructor
  · intro h
    -- The two sums have the same coefficient at every `a`, i.e. the same fibre cardinalities.
    have hc : ∀ a : α, (Finset.univ.filter (fun m => v m = a)).card =
        (Finset.univ.filter (fun m => u m = a)).card := by
      intro a
      have h1 := DFunLike.congr_fun h a
      rw [coeff_sum_single u a, coeff_sum_single v a] at h1
      exact Int.ofNat.inj h1.symm
    -- Match each `v`-fibre bijectively with the corresponding `u`-fibre.
    let e : ∀ a : α, {m : Fin n // v m = a} ≃ {m : Fin n // u m = a} := fun a =>
      Fintype.equivOfCardEq (by
        rw [Fintype.card_subtype, Fintype.card_subtype]
        exact hc a)
    refine ⟨Equiv.ofFiberEquiv e, ?_⟩
    intro m
    exact (Equiv.ofFiberEquiv_map e m).symm
  · rintro ⟨σ, hσ⟩
    have h2 : (∑ m : Fin n, (Finsupp.single (v m) (1 : ℤ) : α →₀ ℤ))
        = ∑ m : Fin n, (Finsupp.single (u (σ m)) (1 : ℤ) : α →₀ ℤ) :=
      Finset.sum_congr rfl (fun m _ => by rw [hσ m])
    rw [h2]
    exact (Equiv.sum_comp σ (fun m => (Finsupp.single (u m) (1 : ℤ) : α →₀ ℤ))).symm

end Work.Charts
