import Mathlib

namespace Work.Holonomy3

/-- Grouping a sum over a finite domain by the fibres of a map `g` into a Fintype:
the sum of `F (g b)` equals the sum over all `p` of the size of the fibre of `p`
times `F p`. -/
lemma sum_comp_fiber {N n : ℕ} (g : Fin n → Fin N) (F : Fin N → ℝ) :
    ∑ b : Fin n, F (g b)
      = ∑ p : Fin N, ((Finset.univ.filter (fun b : Fin n => g b = p)).card : ℝ) * F p := by
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) g (fun b => F (g b))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have h : ∑ x ∈ Finset.univ.filter (fun b : Fin n => g b = p), F (g x)
      = ∑ x ∈ Finset.univ.filter (fun b : Fin n => g b = p), F p := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  rw [h, Finset.sum_const, nsmul_eq_mul]

/-- Double sums of a function of a map are obtained by summing over the fibres,
weighted by the fibre cardinalities. -/
theorem sum_sum_fiber {N n : ℕ} (k : Fin n → Fin N) (X : Fin N → Fin N → ℝ) :
    ∑ a : Fin n, ∑ b : Fin n, X (k a) (k b)
      = ∑ p : Fin N, ∑ q : Fin N,
          ((Finset.univ.filter (fun a : Fin n => k a = p)).card : ℝ) *
          ((Finset.univ.filter (fun a : Fin n => k a = q)).card : ℝ) * X p q := by
  let c : Fin N → ℝ := fun p => ((Finset.univ.filter (fun a : Fin n => k a = p)).card : ℝ)
  show ∑ a : Fin n, ∑ b : Fin n, X (k a) (k b)
      = ∑ p : Fin N, ∑ q : Fin N, c p * c q * X p q
  calc ∑ a : Fin n, ∑ b : Fin n, X (k a) (k b)
      = ∑ a : Fin n, ∑ q : Fin N, c q * X (k a) q :=
        Finset.sum_congr rfl (fun a _ => sum_comp_fiber k (fun q => X (k a) q))
    _ = ∑ q : Fin N, ∑ a : Fin n, c q * X (k a) q := Finset.sum_comm
    _ = ∑ q : Fin N, c q * (∑ a : Fin n, X (k a) q) :=
        Finset.sum_congr rfl
          (fun q _ => (Finset.mul_sum Finset.univ (fun a => X (k a) q) (c q)).symm)
    _ = ∑ q : Fin N, c q * (∑ p : Fin N, c p * X p q) :=
        Finset.sum_congr rfl (fun q _ => by rw [sum_comp_fiber k (fun p => X p q)])
    _ = ∑ q : Fin N, ∑ p : Fin N, c q * (c p * X p q) :=
        Finset.sum_congr rfl
          (fun q _ => Finset.mul_sum Finset.univ (fun p => c p * X p q) (c q))
    _ = ∑ q : Fin N, ∑ p : Fin N, c p * c q * X p q :=
        Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => by ring))
    _ = ∑ p : Fin N, ∑ q : Fin N, c p * c q * X p q := Finset.sum_comm

end Work.Holonomy3
