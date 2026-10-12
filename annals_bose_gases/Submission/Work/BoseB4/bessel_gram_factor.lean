import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.bessel_gram_factor`

Let `g : ι → Fin m → ℝ` be a family of vectors whose Gram matrix over `S : Finset ι`
is the identity, `∑_l g s l * g t l = δ_{st}` for `s, t ∈ S`.  Then the matrix
`P = 1 - Σ_{s∈S} |g_s⟩⟨g_s|`, i.e. the orthogonal projection onto the orthogonal
complement of `span{g_s : s ∈ S}` inside `Fin m → ℝ`, is **idempotent**:

`Σ_p P l p * P l' p = P l l'`.

Written out with the `if … then 1 else 0` Kronecker delta, this is the stated
identity.  In the pure index notation of the statement the proof is the direct
expansion of the product of the two brackets, the two linear terms collapsing to
the scalar `Σ_s g s l * g s l'` by the Kronecker delta, and the quadratic term
collapsing to the same scalar by the orthonormality hypothesis `hg`.
-/

namespace Work.BoseB4

theorem bessel_gram_factor {ι : Type*} [DecidableEq ι] {m : ℕ} (g : ι → Fin m → ℝ)
    (S : Finset ι)
    (hg : ∀ s ∈ S, ∀ t ∈ S, (∑ l : Fin m, g s l * g t l) = if s = t then 1 else 0)
    (l l' : Fin m) :
    (∑ p : Fin m, ((if l = p then (1 : ℝ) else 0) - ∑ s ∈ S, g s l * g s p)
        * ((if l' = p then (1 : ℝ) else 0) - ∑ s ∈ S, g s l' * g s p))
      = (if l = l' then (1 : ℝ) else 0) - ∑ s ∈ S, g s l * g s l' := by
  -- Expand the product of the two brackets, term by term.
  have hexp : ∀ p : Fin m,
      ((if l = p then (1 : ℝ) else 0) - ∑ s ∈ S, g s l * g s p)
        * ((if l' = p then (1 : ℝ) else 0) - ∑ s ∈ S, g s l' * g s p)
      = (if l = p then (1 : ℝ) else 0) * (if l' = p then (1 : ℝ) else 0)
        - (if l = p then (1 : ℝ) else 0) * (∑ s ∈ S, g s l' * g s p)
        - (∑ s ∈ S, g s l * g s p) * (if l' = p then (1 : ℝ) else 0)
        + (∑ s ∈ S, g s l * g s p) * (∑ s ∈ S, g s l' * g s p) := fun p => by ring
  -- The four resulting sums: `δ_{ll'}`, and `Σ_s g s l * g s l'` three times.
  have hS1 : (∑ p : Fin m,
        (if l = p then (1 : ℝ) else 0) * (if l' = p then (1 : ℝ) else 0))
      = (if l = l' then (1 : ℝ) else 0) := by
    have h : ∀ p : Fin m, (if l = p then (1 : ℝ) else 0) * (if l' = p then (1 : ℝ) else 0)
        = if l = p then (if l' = p then (1 : ℝ) else 0) else 0 := by
      intro p; by_cases hc : l = p <;> simp [hc]
    simp_rw [h]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    by_cases hl : l = l'
    · subst hl; simp
    · have hl' : ¬ (l' = l) := fun h => hl h.symm
      simp [hl, hl']
  have hS2 : (∑ p : Fin m, (if l = p then (1 : ℝ) else 0) * (∑ s ∈ S, g s l' * g s p))
      = ∑ s ∈ S, g s l * g s l' := by
    have hstep : ∀ p : Fin m, (if l = p then (1 : ℝ) else 0) * (∑ s ∈ S, g s l' * g s p)
        = ∑ s ∈ S, if l = p then g s l' * g s p else 0 := by
      intro p
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases h : l = p <;> simp [h]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    ring
  have hS3 : (∑ p : Fin m, (∑ s ∈ S, g s l * g s p) * (if l' = p then (1 : ℝ) else 0))
      = ∑ s ∈ S, g s l * g s l' := by
    have hstep : ∀ p : Fin m, (∑ s ∈ S, g s l * g s p) * (if l' = p then (1 : ℝ) else 0)
        = ∑ s ∈ S, if l' = p then g s l * g s p else 0 := by
      intro p
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases h : l' = p <;> simp [h]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
  have hS4 : (∑ p : Fin m, (∑ s ∈ S, g s l * g s p) * (∑ t ∈ S, g t l' * g t p))
      = ∑ s ∈ S, g s l * g s l' := by
    have hstep : ∀ p : Fin m, (∑ s ∈ S, g s l * g s p) * (∑ t ∈ S, g t l' * g t p)
        = ∑ s ∈ S, ∑ t ∈ S, (g s l * g s p) * (g t l' * g t p) := by
      intro p
      rw [Finset.sum_mul_sum]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.sum_comm]
    -- the inner double sum over `t ∈ S`, `p : Fin m` collapses via orthonormality
    have hinner : ∀ t ∈ S, (∑ p : Fin m, (g s l * g s p) * (g t l' * g t p))
        = (g s l * g t l') * (if s = t then (1 : ℝ) else 0) := by
      intro t ht
      have hc : ∀ p : Fin m, (g s l * g s p) * (g t l' * g t p)
          = (g s l * g t l') * (g s p * g t p) := fun p => by ring
      simp_rw [hc]
      rw [← Finset.mul_sum]
      rw [hg s hs t ht]
    rw [Finset.sum_congr rfl hinner]
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ hts
      have : ¬ (s = t) := fun h => hts h.symm
      simp [this]
    · intro hS
      exact absurd hs hS
  rw [Finset.sum_congr rfl (fun p _ => hexp p)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hS1, hS2, hS3, hS4]
  ring

end Work.BoseB4
