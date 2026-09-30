import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

theorem sum_le_tsum_tail (σ : ℝ) (hσ : 1 < σ) (S : Finset ℕ) (N : ℕ)
    (hS : ∀ n ∈ S, N ≤ n) :
    ∑ n ∈ S, (n : ℝ) ^ (-σ) ≤ ∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ (-σ) := by
  have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    (Real.summable_nat_rpow).2 (by linarith)
  have hshift : Summable (fun k : ℕ => ((k + N : ℕ) : ℝ) ^ (-σ)) :=
    hsumm.comp_injective (fun a b h => Nat.add_right_cancel h)
  have hInj : Set.InjOn (fun n : ℕ => n - N) ↑S := by
    intro a ha b hb hab
    have ha' : N ≤ a := hS a (by simpa using ha)
    have hb' : N ≤ b := hS b (by simpa using hb)
    have hab' : a - N = b - N := hab
    have h1 : (a - N) + N = (b - N) + N := by rw [hab']
    rwa [Nat.sub_add_cancel ha', Nat.sub_add_cancel hb'] at h1
  have key : ∑ k ∈ S.image (fun n => n - N), ((k + N : ℕ) : ℝ) ^ (-σ)
      = ∑ n ∈ S, (n : ℝ) ^ (-σ) := by
    rw [Finset.sum_image hInj]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Nat.sub_add_cancel (hS x hx)]
  calc ∑ n ∈ S, (n : ℝ) ^ (-σ)
      = ∑ k ∈ S.image (fun n => n - N), ((k + N : ℕ) : ℝ) ^ (-σ) := key.symm
    _ ≤ ∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ (-σ) :=
        Summable.sum_le_tsum _ (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg (k + N)) (-σ)) hshift
    _ = ∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ (-σ) :=
        tsum_congr (fun k => by rw [Nat.add_comm k N])

end Work.BMF.mrlas
