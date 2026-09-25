import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.tsum_pi_geometric_prod
import Submission.Commons.Analysis.TSum.summable_mul_multiIndex_geometric

open scoped BigOperators

namespace Commons.NumberTheory.EulerProduct

/-- **Regrouping an infinite sum by the fibres of a map to `ℕ`.**
If `g ∘ F` is summable on `α`, then `∑' c, g (F c)` is the sum over `k` of the
(number of elements of `α` with `F c = k`) times `g k`.  No finiteness of the
fibres is needed: for infinite fibres both sides contribute `0`. -/
theorem tsum_comp_eq_tsum_card_fiber {α : Type*} (F : α → ℕ) (g : ℕ → ℝ)
    (h : Summable (fun c : α => g (F c))) :
    ∑' c : α, g (F c) = ∑' k : ℕ, (Nat.card {c : α // F c = k} : ℝ) * g k := by
  classical
  let e : α ≃ (Σ k : ℕ, {c : α // F c = k}) :=
    { toFun := fun c => ⟨F c, ⟨c, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun c => rfl
      right_inv := by
        rintro ⟨k, ⟨c, hc⟩⟩
        subst hc
        rfl }
  have hsu : Summable (fun p : (Σ k : ℕ, {c : α // F c = k}) => g p.1) :=
    (Equiv.summable_iff (f := fun p : (Σ k : ℕ, {c : α // F c = k}) => g p.1) e).1
      (h.congr (fun c => rfl))
  calc ∑' c : α, g (F c)
      = ∑' p : (Σ k : ℕ, {c : α // F c = k}), g p.1 :=
        Equiv.tsum_eq e (fun p : (Σ k : ℕ, {c : α // F c = k}) => g p.1)
    _ = ∑' k : ℕ, ∑' c : {c : α // F c = k}, g k := Summable.tsum_sigma hsu
    _ = ∑' k : ℕ, (Nat.card {c : α // F c = k} : ℝ) * g k := by
        refine tsum_congr (fun k => ?_)
        rw [tsum_const, nsmul_eq_mul]

/-- **Euler-product identity for weighted compositions.**
For a finite index type `ι`, positive weights `w` and `0 ≤ X < 1`, the generating
function of the number of ways to write `k` as `∑ i, c i * w i` factors as a
product of geometric series. -/
theorem tsum_card_expVec_mul_pow {ι : Type*} [Fintype ι] (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X < 1) :
    (∑' k : ℕ, (Nat.card {c : ι → ℕ // ∑ i, c i * w i = k} : ℝ) * X ^ k) =
      ∏ i, (1 - X ^ (w i))⁻¹ := by
  classical
  have hs0 : ∀ i, 0 ≤ X ^ w i := fun i => pow_nonneg hX0 _
  have hXle : X ≤ 1 := le_of_lt hX1
  have hs1 : ∀ i, X ^ w i < 1 := by
    intro i
    calc X ^ w i ≤ X ^ 1 := pow_le_pow_of_le_one hX0 hXle (hw i)
      _ = X := pow_one X
      _ < 1 := hX1
  have hgeom :=
    Commons.Analysis.SpecialFunctions.tsum_pi_geometric_prod (c := fun i => X ^ w i) hs0 hs1
  have hprod : ∀ e : ι → ℕ, ∏ i, (X ^ w i) ^ e i = X ^ (∑ i, e i * w i) := by
    intro e
    have h1 : ∏ i, (X ^ w i) ^ e i = ∏ i, X ^ (w i * e i) :=
      Finset.prod_congr rfl (fun i _ => (pow_mul X (w i) (e i)).symm)
    rw [h1, Finset.prod_pow_eq_pow_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => Nat.mul_comm (w i) (e i))
  have hsumm : Summable (fun e : ι → ℕ => X ^ (∑ i, e i * w i)) :=
    (Commons.Analysis.TSum.summable_pi_geometric (fun i => X ^ w i) hs0 hs1).congr hprod
  have hfiber := tsum_comp_eq_tsum_card_fiber
    (fun c : ι → ℕ => ∑ i, c i * w i) (fun k => X ^ k) hsumm
  rw [← hgeom]
  rw [← hfiber]
  exact (tsum_congr hprod).symm

end Commons.NumberTheory.EulerProduct
