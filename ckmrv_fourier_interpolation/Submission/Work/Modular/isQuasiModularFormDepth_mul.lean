import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- The index of a pair `(j, j')` in `Fin (d+1) × Fin (d'+1)` as an element of
`Fin (d + d' + 1)`, namely `j + j'`. -/
private def pairIdx {d d' : ℕ} (p : Fin (d+1) × Fin (d'+1)) : Fin (d+d'+1) :=
  ⟨p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩

private lemma pairIdx_coe {d d' : ℕ} (p : Fin (d+1) × Fin (d'+1)) :
    ((pairIdx p : Fin (d+d'+1)) : ℤ) = (p.1 : ℤ) + (p.2 : ℤ) := by
  simp only [pairIdx]; push_cast; ring

/-- Weights add correctly along `pairIdx`. -/
private lemma pairIdx_weight {d d' : ℕ} {k l : ℤ} (p : Fin (d+1) × Fin (d'+1)) :
    ((k - 2*(p.1:ℤ)) + (l - 2*(p.2:ℤ))) = ((k+l) - 2*((pairIdx p : Fin (d+d'+1)):ℤ)) := by
  rw [pairIdx_coe]; ring

/-- The fibre of `pairIdx` over `t`. -/
private def fiber {d d' : ℕ} (t : Fin (d+d'+1)) : Finset (Fin (d+1) × Fin (d'+1)) :=
  Finset.univ.filter (fun p => pairIdx p = t)

/-- Expansion of a product of two finite sums of `E₂`-powers times coefficients. -/
private lemma mul_expansion {d d' : ℕ} (a : Fin (d+1) → ℍ → ℂ) (b : Fin (d'+1) → ℍ → ℂ) :
    (∑ j : Fin (d+1), E2^(j:ℕ) * a j) * (∑ j' : Fin (d'+1), E2^(j':ℕ) * b j')
      = ∑ p : Fin (d+1) × Fin (d'+1), E2^((p.1:ℕ)+(p.2:ℕ)) * (a p.1 * b p.2) := by
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Fintype.sum_prod_type (f := fun p : Fin (d+1) × Fin (d'+1) =>
        E2^((p.1:ℕ)+(p.2:ℕ)) * (a p.1 * b p.2))]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [pow_add]
  ring

theorem isQuasiModularFormDepth_mul {d d' : ℕ} {k l : ℤ} {f g : ℍ → ℂ}
    (hf : IsQuasiModularFormDepth d k f) (hg : IsQuasiModularFormDepth d' l g) :
    IsQuasiModularFormDepth (d + d') (k + l) (f * g) := by
  obtain ⟨m, rfl⟩ := hf
  obtain ⟨n, rfl⟩ := hg
  -- Collect, for each target power `t`, the fibre of pairs `(j, j')` with `j + j' = t`.
  let M : (t : Fin (d+d'+1)) → ModularForm 𝒮ℒ ((k+l) - 2*(t:ℤ)) :=
    fun t => ∑ x : {p // p ∈ fiber t},
      ModularForm.mcast
        ((pairIdx_weight (x.1)).trans (congrArg (fun u : Fin (d+d'+1) => (k+l) - 2*(u:ℤ))
          (Finset.mem_filter.mp x.2).2))
        ((m x.1.1).mul (n x.1.2))
  refine ⟨M, ?_⟩
  have hMt : ∀ t, ⇑(M t) = ∑ p ∈ fiber t, ⇑(m p.1) * ⇑(n p.2) := by
    intro t
    simp only [M, fiber]
    rw [FunLike.coe_sum]
    simp only [ModularForm.coe_mcast, ModularForm.coe_mul]
    rw [← Finset.sum_attach (Finset.univ.filter (fun p => pairIdx p = t))
          (fun p => ⇑(m p.1) * ⇑(n p.2))]
    rw [Finset.attach_eq_univ]
    rfl
  rw [mul_expansion]
  simp only [hMt]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ pairIdx
        (fun p => E2^((p.1:ℕ)+(p.2:ℕ)) * (⇑(m p.1) * ⇑(n p.2)))]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p hp => ?_
  rw [← (Finset.mem_filter.mp hp).2]
  rfl

end Work.Modular
