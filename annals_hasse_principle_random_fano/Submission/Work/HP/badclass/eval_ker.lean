import Mathlib
import Submission.Work.HP.badclass.BadDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open MvPolynomial Finset

namespace Work.HP.badclass

/-- For `x` in the torus the functional `a ↦ f_a(x)` is nonzero, so its kernel has `p^{N-1}`
elements. -/
theorem eval_ker (d n p : ℕ) (hp : p.Prime) (x : Fin (n + 1) → ZMod p)
    (hx : ∀ i, x i ≠ 0) :
    ({a : Work.HP.Mon d n → ZMod p | Work.HP.formEvalZMod d n p a x = 0} :
        Set (Work.HP.Mon d n → ZMod p)).ncard = p ^ (Work.HP.NN d n - 1) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set φ : (Work.HP.Mon d n → ZMod p) →ₗ[ZMod p] ZMod p :=
    Fintype.linearCombination (ZMod p)
      (fun m : Work.HP.Mon d n => ∏ j : Fin (n + 1), x j ^ (m.1 j : ℕ)) with hφ
  have hφapp : ∀ a, φ a = Work.HP.formEvalZMod d n p a x := by
    intro a
    rw [hφ, Fintype.linearCombination_apply]
    simp only [smul_eq_mul, Work.HP.formEvalZMod]
  have hdirac : ∀ m : Work.HP.Mon d n,
      φ (Pi.single m 1) = ∏ j : Fin (n + 1), x j ^ (m.1 j : ℕ) := by
    intro m
    rw [hφ, Fintype.linearCombination_apply,
      Finset.sum_eq_single m (f := fun b : Work.HP.Mon d n =>
          (Pi.single m 1 : Work.HP.Mon d n → ZMod p) b • (∏ j : Fin (n + 1), x j ^ (b.1 j : ℕ)))
        (fun b _ hbm => by
          rw [Pi.single_eq_of_ne (show b ≠ m from hbm), zero_smul])
        (fun hm => absurd (Finset.mem_univ m) hm)]
    rw [Pi.single_eq_same, one_smul]
  have hne : φ ≠ 0 := by
    intro h0
    have h1 := hdirac (Work.HP.monE d n 0)
    rw [h0] at h1
    simp only [LinearMap.zero_apply] at h1
    have h2 : (∏ j : Fin (n + 1), x j ^ ((Work.HP.monE d n 0).1 j : ℕ)) ≠ 0 := by
      rw [Finset.prod_eq_single 0
        (f := fun j : Fin (n + 1) => x j ^ ((Work.HP.monE d n 0).1 j : ℕ))
        (fun b _ hb0 => by rw [Work.HP.monE_ne d n 0 b hb0, pow_zero])
        (fun h0 => absurd (Finset.mem_univ 0) h0)]
      rw [Work.HP.monE_self]
      exact pow_ne_zero _ (hx 0)
    exact h2 h1.symm
  have hex : ∃ a, φ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (LinearMap.ext h)
  have hsurj : Function.Surjective φ := by
    obtain ⟨a₀, ha₀⟩ := hex
    intro u
    exact ⟨(u * (φ a₀)⁻¹) • a₀, by
      rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ ha₀, mul_one]⟩
  have hkerNat : Nat.card ↥(LinearMap.ker φ) = p ^ (Work.HP.NN d n - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥(LinearMap.ker φ)), Nat.card_zmod]
    congr 1
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank (ZMod p) ↥(LinearMap.range φ) = 1 := by
      rw [LinearMap.range_eq_top.mpr hsurj]
      have h3 : Module.finrank (ZMod p)
          ↥(⊤ : Submodule (ZMod p) (ZMod p)) = Module.finrank (ZMod p) (ZMod p) :=
        (Submodule.eq_top_iff_finrank_eq (W := ⊤)).mp rfl
      rw [h3, Module.finrank_self]
    have h4 : Module.finrank (ZMod p) (Work.HP.Mon d n → ZMod p) = Work.HP.NN d n :=
      Module.finrank_fintype_fun_eq_card (ZMod p)
    omega
  have hset : ({a : Work.HP.Mon d n → ZMod p | Work.HP.formEvalZMod d n p a x = 0} :
      Set (Work.HP.Mon d n → ZMod p)) = (φ.ker : Set (Work.HP.Mon d n → ZMod p)) := by
    ext a
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker, hφapp]
  rw [hset, Work.HP.ncard_coe_submodule, hkerNat]

end Work.HP.badclass
