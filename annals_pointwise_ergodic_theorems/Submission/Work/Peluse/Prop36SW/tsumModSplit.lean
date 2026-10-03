import Mathlib
import Submission.Work.Peluse.Basic

set_option linter.style.haveILetI false

namespace Work.Peluse.Prop36SW

/-- Reindexing a sum over `ℤ` by the negation involution. -/
private lemma tsum_neg_reindex (g : ℤ → ℂ) :
    (∑' b : ℤ, g (-b)) = ∑' z : ℤ, g z := by
  rw [← Equiv.tsum_eq (Equiv.neg ℤ) g]
  simp [Equiv.neg]

/-- A sum over `ℤ` of a function supported in `[-N, N]` splits into the sums over the
residue classes modulo `c`. -/
theorem tsumModSplit {c : ℤ} (hc : c ≠ 0) {v : ℤ → ℂ} {N : ℕ}
    (hv : ∀ x : ℤ, N < x.natAbs → v x = 0) :
    ∑' x : ℤ, v x = ∑ r ∈ Finset.range c.natAbs, ∑' z : ℤ, v (c * z + (r : ℤ)) := by
  have hn : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  haveI : NeZero c.natAbs := ⟨hn⟩
  -- `v` is supported in the finite set `[-N, N]`, hence summable.
  have hsupp : ∀ x ∉ Finset.Icc (-(N : ℤ)) (N : ℤ), v x = 0 := by
    intro x hx
    apply hv
    have h : ((x.natAbs : ℤ) ≤ (N : ℤ)) ↔ -(N : ℤ) ≤ x ∧ x ≤ (N : ℤ) := by
      rw [← Int.abs_eq_natAbs, abs_le]
    have hx' : ¬ ((x.natAbs : ℤ) ≤ (N : ℤ)) := by
      rw [h]; simpa [Finset.mem_Icc] using hx
    exact_mod_cast lt_of_not_ge hx'
  have hvsumm : Summable v := summable_of_ne_finset_zero hsupp
  -- Split `ℤ` into residue classes modulo `c.natAbs`.
  have h1 : ∑' x : ℤ, v x = ∑' p : ℤ × Fin c.natAbs, v ((Int.divModEquiv c.natAbs).symm p) :=
    (Equiv.tsum_eq (Int.divModEquiv c.natAbs).symm v).symm
  have h2 : (fun p : ℤ × Fin c.natAbs => v ((Int.divModEquiv c.natAbs).symm p))
      = fun p : ℤ × Fin c.natAbs => v (p.1 * (c.natAbs : ℤ) + (p.2 : ℤ)) := by
    funext p
    rw [Int.divModEquiv_symm_apply]
  have hsumm : Summable (fun p : ℤ × Fin c.natAbs => v (p.1 * (c.natAbs : ℤ) + (p.2 : ℤ))) := by
    rw [← h2]
    exact (Equiv.summable_iff (Int.divModEquiv c.natAbs).symm).mpr hvsumm
  rw [h1, h2, hsumm.tsum_prod]
  simp only [tsum_fintype]
  -- Interchange the finite sum over residues with the infinite sum over `ℤ`.
  have hstep : ∀ r : Fin c.natAbs, Summable (fun b : ℤ => v (b * (c.natAbs : ℤ) + (r : ℤ))) := by
    intro r
    exact hsumm.comp_injective (i := fun t : ℤ => ((t, r) : ℤ × Fin c.natAbs))
      (fun a b hab => by simpa using congrArg Prod.fst hab)
  rw [Summable.tsum_finsetSum (s := Finset.univ)
        (f := fun (r : Fin c.natAbs) (b : ℤ) => v (b * (c.natAbs : ℤ) + (r : ℤ)))
        (fun r _ => hstep r)]
  -- Identify the sums over `Fin c.natAbs` with the sums over `Finset.range c.natAbs`.
  rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ => ∑' z : ℤ, v (c * z + (r : ℤ))) c.natAbs]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Replace the linear part `c.natAbs · b` by `c · (sign · b)`.
  by_cases hc0 : 0 ≤ c
  · rw [Int.natAbs_of_nonneg hc0]
    refine tsum_congr (fun b => ?_)
    congr 1
    ring
  · have hcabs : ((c.natAbs : ℕ) : ℤ) = -c := by
      rw [← Int.natAbs_neg c]
      exact Int.natAbs_of_nonneg (by linarith)
    rw [hcabs]
    rw [show (∑' b : ℤ, v (b * (-c) + (i : ℤ))) = ∑' b : ℤ, v (c * (-b) + (i : ℤ)) from
      tsum_congr (fun b => by congr 1; ring)]
    exact tsum_neg_reindex (fun z : ℤ => v (c * z + (i : ℤ)))

end Work.Peluse.Prop36SW
