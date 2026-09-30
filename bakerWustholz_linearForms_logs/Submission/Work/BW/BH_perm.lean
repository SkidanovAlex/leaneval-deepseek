import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- The determination `lamP` only depends on the *pairs* `(i, log φ (α i))`; permuting the
index set of `α` and the columns of `L` by the same permutation does not change it. -/
lemma lamP_perm {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ) (α : Fin n → K) (v : ℕ)
    (L : Fin n → Fin n → ℤ) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    lamP φ α v (fun j i => L j (π.symm i)) j = lamP φ (fun i => α (π i)) v L j := by
  unfold lamP
  congr 1
  rw [Fintype.sum_equiv π.symm (fun i => (L j (π.symm i) : ℂ) * Complex.log (φ (α i)))
        (fun i => (L j i : ℂ) * Complex.log (φ (α (π i))))]
  intro x
  simp

/-- `BH` is invariant under permuting the `α i` (thereby permuting the columns of `L`): if `BH` holds
for the family `i ↦ α (π i)`, then it holds for `α` with `L` replaced by `fun j i => L j (π.symm i)`. -/
theorem BH_perm {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (v : ℕ) (c : ℝ) (L : Fin n → Fin n → ℤ) (α' : Fin n → K) (σ : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (h : BH φ (fun i => α (π i)) b v c n L α' σ) :
    BH φ α b v c n (fun j i => L j (π.symm i)) α' σ := by
  unfold BH at h ⊢
  obtain ⟨hli, _hb, hexp, hkum, hpos, hmodh, hsum, hprod⟩ := h
  -- The permuted rows of `L` are still `ℚ`-linearly independent: they are the images of the
  -- original rows under the invertible coordinate-permutation `fun x i => x (π.symm i)`.
  have hli' : LinearIndependent ℚ (fun j i => (L j (π.symm i) : ℚ)) := by
    have hrow : (fun j i => (L j (π.symm i) : ℚ)) =
        ⇑(LinearEquiv.funCongrLeft ℚ ℚ π.symm : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)) ∘
          (fun j i => (L j i : ℚ)) := by
      funext j i; rfl
    rw [hrow]
    exact hli.map' _ (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))
  -- `n` independent rows in the `n`-dimensional space `Fin n → ℚ` span everything, so the
  -- saturation condition on `b` is automatic.
  have hspan : Submodule.span ℚ (Set.range fun j i => (L j (π.symm i) : ℚ)) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank' hli' (by
      rw [Fintype.card_fin, Module.finrank_fin_fun])
  have hlam : ∀ j, lamP φ α v (fun j i => L j (π.symm i)) j
      = lamP φ (fun i => α (π i)) v L j := fun j => lamP_perm φ α v L π j
  refine ⟨hli', ?_, ?_, hkum, hpos, ?_, ?_, ?_⟩
  · rw [hspan]; exact Submodule.mem_top
  · intro j; rw [hlam j]; exact hexp j
  · intro j; rw [hlam j]; exact hmodh j
  · intro j
    rw [Fintype.sum_equiv π.symm
        (fun i => |(L j (π.symm i) : ℝ)| * BakerWustholz.modifiedHeight φ (α i))
        (fun i => |(L j i : ℝ)| * BakerWustholz.modifiedHeight φ (α (π i)))
        (by intro x; simp)]
    exact hsum j
  · rw [← Equiv.prod_comp π (fun i => BakerWustholz.modifiedHeight φ (α i))]
    exact hprod

end Work.BW
